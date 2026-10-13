/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEvenBoundOdd
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEvenBoundBox
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEvenBoundHessian
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepEvenBoundSlab

/-!
# OneStepEvenBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two-point Taylor estimate at the met face

This module carries the analytic step's residue `(★)`: for a competitor `V` odd
about the met face and harmonic on the **doubled** window, the even part of an
affine competitor is controlled pointwise, on a near-face slab of depth
`delta`, by the affine residual `f = V - ℓ*` at two nearby points plus a
Hessian remainder.

## The mechanism

Write `ρ` for the reflection through the met face `{yᵢ = a}`, `a = (1/2)·3^m`.
The reflection identity `f ∘ ρ + f = -2 e` of `OneStepEvenBoundOdd` is exact but
by itself carries no information: it is an identity.  Harmonicity enters through
a *second-order Taylor comparison* along the normal direction, applied twice:

* to the pair `(y, ρ y)`, whose displacement is `2 s·eᵢ` with `s = a - yᵢ`;
* to the pair `(y, y - delta·eᵢ)`, whose displacement is `-delta·eᵢ`.

The first, combined with the reflection identity, gives
`|e y + f y + s β| ≤ 2 M delta²` where `β` is the (unknown) normal derivative of
`f` at `y`; the second gives `|f(y - delta·eᵢ) - f y + delta β| ≤ M delta²` and
therefore determines `β` up to `M delta`.  Eliminating `β` — legitimate because
`s/delta ∈ (0,1]`, which is exactly why the *deep* comparison point is taken at
the fixed depth `delta` rather than at a depth proportional to `s` — leaves

```text
  |e y| ≤ 2 |f y| + |f (y - delta·eᵢ)| + 3 M delta² .
```

This is the pointwise input the `L²` assembly of `OneStepEvenBoundFinal`
consumes.  Note that no continuity of `V` at the face is used, and no membership
hypothesis beyond `y` in the core slab.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection basisVec)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. Displacements along the normal -/

/-- The normalized seminorm does not see absolute values. -/
theorem normalizedL2On_abs (W : Set (Vec d)) (f : Vec d → ℝ) :
    normalizedL2On W (fun y => |f y|) = normalizedL2On W f := by
  change Real.sqrt (HCPolySupport.volumeAverage W fun y => |f y| ^ 2)
      = Real.sqrt (HCPolySupport.volumeAverage W fun y => f y ^ 2)
  congr 2
  funext y
  rw [sq_abs]

/-- The face reflection displaces a point by twice its distance to the face,
along the normal. -/
theorem coordFaceReflection_sub_self (a : ℝ) (i : Fin d) (y : Vec d) :
    coordFaceReflection a i y - y = (2 * (a - y i)) • (basisVec i : Vec d) := by
  funext j
  by_cases hj : j = i
  · subst hj
    change coordFaceReflection a j y j - y j = 2 * (a - y j) * (basisVec j : Vec d) j
    rw [HCPolySupport.coordFaceReflection_apply_self, HCPolySupport.basisVec_apply,
      ite_eq_left rfl]
    ring
  · change coordFaceReflection a i y j - y j = 2 * (a - y i) * (basisVec i : Vec d) j
    rw [HCPolySupport.coordFaceReflection_apply_ne a i j y hj,
      HCPolySupport.basisVec_apply, ite_eq_right hj]
    ring

/-- Translating by a multiple of a basis vector. -/
theorem sub_smul_basisVec_sub_self (t : ℝ) (i : Fin d) (y : Vec d) :
    (y - t • (basisVec i : Vec d)) - y = (-t) • (basisVec i : Vec d) := by
  funext j
  change (y j - t * (basisVec i : Vec d) j) - y j = (-t) * (basisVec i : Vec d) j
  ring

/-- The `toEuc` image of a normal displacement. -/
theorem toEuc_smul_basisVec (t : ℝ) (i : Fin d) :
    (toEuc : Vec d → EuclideanSpace ℝ (Fin d)) (t • (basisVec i : Vec d))
      = t • EuclideanSpace.single i (1 : ℝ) := by
  rw [map_smul, toEuc_basisVec]

/-- The length of a normal displacement. -/
theorem norm_toEuc_smul_basisVec (t : ℝ) (i : Fin d) :
    ‖(toEuc : Vec d → EuclideanSpace ℝ (Fin d)) (t • (basisVec i : Vec d))‖ = |t| := by
  rw [toEuc_smul_basisVec, norm_smul, PiLp.norm_single, Real.norm_eq_abs]
  norm_num

/-! ## 2. The pointwise estimate on the core slab -/

/-- **The two-point Taylor estimate at a near-face point.**

For `f = V - ℓ*` harmonic on the Taylor box with Hessian bounded by `M`, and `y`
in the core slab of depth `delta` under the met face, comparing `f` at `y` with
its values at the reflected point `ρ y` and at the pushed point `y - delta·eᵢ`
eliminates the unknown normal derivative and prices the even part pointwise. -/
theorem abs_evenAffinePart_le_pointwise {m n : ℤ} {x : Vec d} {i : Fin d} {V : Vec d → ℝ}
    (hVodd : ∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    {c : ℝ} {A : Vec d} {delta M : ℝ} (hdelta : 0 < delta) (hM : 0 ≤ M)
    (hharm : ∀ z ∈ coordBox (taylorLo x m (n - 2) i delta) (taylorHi x m (n - 2) i delta),
      HarmonicAt ((fun y => V y - affineEval (c - vecDot A x) A y)
        ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc z))
    (hMbound : ∀ z ∈ coordBox (taylorLo x m (n - 2) i delta) (taylorHi x m (n - 2) i delta),
      ‖fderiv ℝ (fderiv ℝ ((fun y => V y - affineEval (c - vecDot A x) A y)
        ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))) (toEuc z)‖ ≤ M)
    {y : Vec d} (hy : y ∈ coordBox (slabLo x m (n - 2) i delta) (slabHi x m (n - 2) i))
    (hyD : y - delta • (basisVec i : Vec d)
      ∈ coordBox (taylorLo x m (n - 2) i delta) (taylorHi x m (n - 2) i delta)) :
    |evenAffinePart x m i c A y|
      ≤ 2 * |V y - affineEval (c - vecDot A x) A y|
        + |V (y - delta • (basisVec i : Vec d))
            - affineEval (c - vecDot A x) A (y - delta • (basisVec i : Vec d))|
        + 3 * M * delta ^ 2 := by
  classical
  have hdne : delta ≠ 0 := ne_of_gt hdelta
  set f : Vec d → ℝ := fun z => V z - affineEval (c - vecDot A x) A z with hfdef
  set T : Set (Vec d) :=
    coordBox (taylorLo x m (n - 2) i delta) (taylorHi x m (n - 2) i delta) with hTdef
  have hyT : y ∈ T := coordBox_slab_subset_taylor hdelta hy
  have hrT : coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y ∈ T :=
    reflection_mem_taylor hy hdelta
  set beta : ℝ := fderiv ℝ (f ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc y)
      (EuclideanSpace.single i (1 : ℝ)) with hbetadef
  -- the slab's depth parameter
  have hyi : (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta < y i
      ∧ y i < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    have h := (mem_coordBox_iff.1 hy) i
    rwa [slabLo_self, slabHi_self] at h
  set s : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ m - y i with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith only [hyi.2]
  have hsd : s ≤ delta := by rw [hsdef]; linarith only [hyi.1]
  -- Taylor towards the reflected point
  have htay1 := abs_sub_fderiv_apply_le_of_hessian_bound_vec (V := f) (S := T)
    (convex_coordBox _ _) hharm hMbound hyT hrT
  have hdisp1 : (toEuc : Vec d → EuclideanSpace ℝ (Fin d))
        (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) - toEuc y
      = toEuc ((2 * s) • (basisVec i : Vec d)) := by
    rw [← map_sub, coordFaceReflection_sub_self, hsdef]
  have hnorm1 : ‖(toEuc : Vec d → EuclideanSpace ℝ (Fin d))
        (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) - toEuc y‖ = 2 * s := by
    rw [hdisp1, norm_toEuc_smul_basisVec, abs_of_pos (by linarith only [hs0])]
  have happ1 : fderiv ℝ (f ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc y)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d))
        (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) - toEuc y)
      = 2 * s * beta := by
    rw [hdisp1, toEuc_smul_basisVec, map_smul, hbetadef, smul_eq_mul]
  rw [hnorm1, happ1] at htay1
  -- Taylor towards the pushed point
  have htay2 := abs_sub_fderiv_apply_le_of_hessian_bound_vec (V := f) (S := T)
    (convex_coordBox _ _) hharm hMbound hyT hyD
  have hdisp2 : (toEuc : Vec d → EuclideanSpace ℝ (Fin d))
        (y - delta • (basisVec i : Vec d)) - toEuc y
      = toEuc ((-delta) • (basisVec i : Vec d)) := by
    rw [← map_sub, sub_smul_basisVec_sub_self]
  have hnorm2 : ‖(toEuc : Vec d → EuclideanSpace ℝ (Fin d))
      (y - delta • (basisVec i : Vec d)) - toEuc y‖ = delta := by
    rw [hdisp2, norm_toEuc_smul_basisVec, abs_neg, abs_of_pos hdelta]
  have happ2 : fderiv ℝ (f ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc y)
      ((toEuc : Vec d → EuclideanSpace ℝ (Fin d)) (y - delta • (basisVec i : Vec d))
        - toEuc y) = -delta * beta := by
    rw [hdisp2, toEuc_smul_basisVec, map_smul, hbetadef, smul_eq_mul]
  rw [hnorm2, happ2] at htay2
  -- the reflection identity
  have hrefl : f (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) + f y
      = -2 * evenAffinePart x m i c A y :=
    sub_affineEval_add_reflect hVodd c A y
  -- the two scalar bounds
  have hB1 : |evenAffinePart x m i c A y + f y + s * beta| ≤ 2 * (M * delta ^ 2) := by
    have hsq : M * (2 * s) ^ 2 ≤ 4 * (M * delta ^ 2) := by
      have h2 : (0 : ℝ) ≤ 2 * s := by linarith only [hs0]
      have h3 : 2 * s ≤ 2 * delta := by linarith only [hsd]
      have h1 : (2 * s) ^ 2 ≤ (2 * delta) ^ 2 := pow_le_pow_left₀ h2 h3 2
      have h4 := mul_le_mul_of_nonneg_left h1 hM
      linarith only [h4]
    have hrw : f (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y) - f y - 2 * s * beta
        = -2 * (evenAffinePart x m i c A y + f y + s * beta) := by
      linarith only [hrefl]
    rw [hrw, abs_mul] at htay1
    have habs2 : |(-2 : ℝ)| = 2 := by norm_num
    rw [habs2] at htay1
    linarith only [htay1, hsq]
  have hB2 : |f (y - delta • (basisVec i : Vec d)) - f y + delta * beta|
      ≤ M * delta ^ 2 := by
    rw [show f (y - delta • (basisVec i : Vec d)) - f y - -delta * beta
        = f (y - delta • (basisVec i : Vec d)) - f y + delta * beta by ring] at htay2
    exact htay2
  -- eliminating the unknown normal derivative
  set t : ℝ := s / delta with htdef
  have ht0 : 0 < t := div_pos hs0 hdelta
  have ht1 : t ≤ 1 := by
    rw [htdef, div_le_one hdelta]
    exact hsd
  set P : ℝ := f y with hPdef
  set Q : ℝ := f (y - delta • (basisVec i : Vec d)) with hQdef
  set Rv : ℝ := evenAffinePart x m i c A y with hRvdef
  set u1 : ℝ := Rv + P + s * beta with hu1def
  set u2 : ℝ := t * (Q - P + delta * beta) with hu2def
  have hid : Rv = u1 - P - u2 + t * Q + -(t * P) := by
    rw [hu1def, hu2def, htdef]
    field_simp
    ring
  have hu2b : |u2| ≤ M * delta ^ 2 := by
    rw [hu2def, abs_mul, abs_of_pos ht0]
    have h1 : t * |Q - P + delta * beta| ≤ 1 * |Q - P + delta * beta| :=
      mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
    linarith only [h1, hB2]
  have hMd : 0 ≤ M * delta ^ 2 := by positivity
  have hQ1 : t * Q ≤ |Q| := by
    have h1 : t * Q ≤ t * |Q| := mul_le_mul_of_nonneg_left (le_abs_self Q) ht0.le
    have h2 : t * |Q| ≤ 1 * |Q| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
    linarith only [h1, h2]
  have hQ2 : -|Q| ≤ t * Q := by
    have h1 : t * (-|Q|) ≤ t * Q := mul_le_mul_of_nonneg_left (neg_abs_le Q) ht0.le
    have h2 : t * |Q| ≤ 1 * |Q| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
    linarith only [h1, h2]
  have hP1 : t * P ≤ |P| := by
    have h1 : t * P ≤ t * |P| := mul_le_mul_of_nonneg_left (le_abs_self P) ht0.le
    have h2 : t * |P| ≤ 1 * |P| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
    linarith only [h1, h2]
  have hP2 : -|P| ≤ t * P := by
    have h1 : t * (-|P|) ≤ t * P := mul_le_mul_of_nonneg_left (neg_abs_le P) ht0.le
    have h2 : t * |P| ≤ 1 * |P| := mul_le_mul_of_nonneg_right ht1 (abs_nonneg _)
    linarith only [h1, h2]
  obtain ⟨h1l, h1r⟩ := abs_le.1 hB1
  obtain ⟨h2l, h2r⟩ := abs_le.1 hu2b
  have hPl : -|P| ≤ P := neg_abs_le P
  have hPr : P ≤ |P| := le_abs_self P
  refine abs_le.2 ⟨?_, ?_⟩ <;> rw [hid] <;>
    linarith only [h1l, h1r, h2l, h2r, hQ1, hQ2, hP1, hP2, hPl, hPr, hMd]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
