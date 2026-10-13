/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddClassCornerGeometry

/-!
# OneStepOddClassCornerTaylor

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two-point Taylor elimination, box-generic

The pointwise atom's `(★)` (`OneStepEvenBound.abs_evenAffinePart_le_pointwise`)
is stated on the proved one-met-face slab/Taylor boxes.  The corner pricing
needs the same estimate on the window-hugging corner boxes of
`OneStepOddClassCornerGeometry`, and — for the third application — at an affine
competitor that is *not* a minimizer.

The estimate: for `V` odd about the met upper `i`-face, `f = V − ℓ` the
residual against an arbitrary affine `ℓ = affineEval (c − A·x) A`, harmonic on
`T` with Hessian bound `M` there, and `y` within depth `delta` of the face
with `y`, `ρᵢy`, `y − delta·eᵢ ∈ T`:

```text
  |evenᵢ(ℓ)(y)| ≤ 2|f y| + |f (y − delta·eᵢ)| + 3 M delta² .
```

The reflection identity `f∘ρᵢ + f = −2·evenᵢ(ℓ)` supplies the even part; the
two second-order Taylor steps (towards the reflected and the pushed point)
eliminate the unknown normal derivative.

## References

* Adapted from `OneStepEvenBound.abs_evenAffinePart_le_pointwise` (same
  repository), the boxes abstracted.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory InnerProductSpace
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection basisVec)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-- **The two-point Taylor elimination at a near-face point, box-generic.** The
proved `abs_evenAffinePart_le_pointwise` with the Taylor box abstracted into a
convex `T` and the point memberships as hypotheses. -/
theorem abs_evenAffinePart_le_pointwise_of_mem {m : ℤ} {x : Vec d} {i : Fin d}
    {V : Vec d → ℝ}
    (hVodd : ∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    {c : ℝ} {A : Vec d} {delta M : ℝ} (hdelta : 0 < delta) (hM : 0 ≤ M)
    {T : Set (Vec d)} (hT : Convex ℝ T)
    (hharm : ∀ z ∈ T, HarmonicAt ((fun y => V y - affineEval (c - vecDot A x) A y)
      ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc z))
    (hMbound : ∀ z ∈ T, ‖fderiv ℝ (fderiv ℝ ((fun y => V y
        - affineEval (c - vecDot A x) A y)
      ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d))) (toEuc z)‖ ≤ M)
    {y : Vec d} (hyT : y ∈ T)
    (hrT : coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y ∈ T)
    (hyD : y - delta • (basisVec i : Vec d) ∈ T)
    (hylo : (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta < y i)
    (hyhi : y i < (1 / 2 : ℝ) * (3 : ℝ) ^ m) :
    |evenAffinePart x m i c A y|
      ≤ 2 * |V y - affineEval (c - vecDot A x) A y|
        + |V (y - delta • (basisVec i : Vec d))
            - affineEval (c - vecDot A x) A (y - delta • (basisVec i : Vec d))|
        + 3 * M * delta ^ 2 := by
  classical
  set f : Vec d → ℝ := fun z => V z - affineEval (c - vecDot A x) A z with hfdef
  set beta : ℝ := fderiv ℝ (f ∘ (toEuc.symm : EuclideanSpace ℝ (Fin d) → Vec d)) (toEuc y)
      (EuclideanSpace.single i (1 : ℝ)) with hbetadef
  set s : ℝ := (1 / 2 : ℝ) * (3 : ℝ) ^ m - y i with hsdef
  have hs0 : 0 < s := by rw [hsdef]; linarith only [hyhi]
  have hsd : s ≤ delta := by rw [hsdef]; linarith only [hylo]
  -- Taylor towards the reflected point
  have htay1 := abs_sub_fderiv_apply_le_of_hessian_bound_vec (V := f) (S := T)
    hT hharm hMbound hyT hrT
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
    hT hharm hMbound hyT hyD
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

/-! ## 8. Crude volume lower bounds -/

/-- Any box with all edges at least `delta` has volume at least `delta^d`. -/
theorem volume_toReal_coordBox_ge_of_edges {lo hi : Fin d → ℝ} {delta : ℝ}
    (hdelta : 0 < delta) (hedge : ∀ l, delta ≤ hi l - lo l) :
    delta ^ d ≤ (volume (coordBox lo hi)).toReal := by
  have hle : ∀ l, lo l ≤ hi l := fun l => by linarith only [hedge l, hdelta]
  rw [volume_coordBox_toReal hle]
  calc delta ^ d = ∏ _l : Fin d, delta := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ l : Fin d, (hi l - lo l) :=
        Finset.prod_le_prod₀ (fun _ _ => hdelta.le) (fun l _ => hedge l)

/-- The face slab's edges are all at least `delta`. -/
theorem cornerFaceSlab_edge_ge {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) (l : Fin d) :
    delta ≤ cornerFaceSlabHi x m k i l - cornerFaceSlabLo x m k i delta l := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [cornerFaceSlabHi, cornerFaceSlabLo]
  by_cases hli : l = i
  · rw [ite_eq_left hli, ite_eq_left hli]
    linarith only []
  · rw [ite_eq_right hli, ite_eq_right hli]
    have h := quarter_zpow_lt_hug_edge hx hkm l
    linarith only [h, hdelta16, hw]

/-- The corner slab's edges are all at least `delta`. -/
theorem cornerPairSlab_edge_ge {x : Vec d} {m k : ℤ} {i j : Fin d} {delta : ℝ}
    (hx : x ∈ openCubeSet (originCube d m)) (hkm : k < m)
    (hdelta16 : 16 * delta ≤ (3 : ℝ) ^ k) (l : Fin d) :
    delta ≤ cornerPairSlabHi x m k i j l - cornerPairSlabLo x m k i j delta l := by
  have hw : (0 : ℝ) < (3 : ℝ) ^ k := zpow_pos (by norm_num) _
  rw [cornerPairSlabHi, cornerPairSlabLo]
  by_cases hlij : l = i ∨ l = j
  · rw [ite_eq_left hlij, ite_eq_left hlij]
    linarith only []
  · rw [ite_eq_right hlij, ite_eq_right hlij]
    have h := quarter_zpow_lt_hug_edge hx hkm l
    linarith only [h, hdelta16, hw]

/-! ## 9. Face-depth accessors -/

/-- A point of the face slab is within `delta` of the met face. -/
theorem cornerFaceSlab_depth {x : Vec d} {m k : ℤ} {i : Fin d} {delta : ℝ}
    {y : Vec d}
    (hy : y ∈ coordBox (cornerFaceSlabLo x m k i delta) (cornerFaceSlabHi x m k i)) :
    (1 / 2 : ℝ) * (3 : ℝ) ^ m - delta < y i ∧ y i < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
  have h := (mem_coordBox_iff.1 hy) i
  rw [cornerFaceSlabLo, ite_eq_left rfl, cornerFaceSlabHi, ite_eq_left rfl] at h
  exact h

/-- A point of the corner slab is within `delta` of the `j`-face (and of the
`i`-face). -/
theorem cornerPairSlab_depth {x : Vec d} {m k : ℤ} {i j : Fin d} {delta : ℝ}
    {y : Vec d}
    (hy : y ∈ coordBox (cornerPairSlabLo x m k i j delta)
      (cornerPairSlabHi x m k i j)) :
    ((1 / 2 : ℝ) * (3 : ℝ) ^ m - delta < y i ∧ y i < (1 / 2 : ℝ) * (3 : ℝ) ^ m)
      ∧ ((1 / 2 : ℝ) * (3 : ℝ) ^ m - delta < y j
          ∧ y j < (1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
  have hi' := (mem_coordBox_iff.1 hy) i
  have hj' := (mem_coordBox_iff.1 hy) j
  rw [cornerPairSlabLo, ite_eq_left (Or.inl rfl), cornerPairSlabHi,
    ite_eq_left (Or.inl rfl)] at hi'
  rw [cornerPairSlabLo, ite_eq_left (Or.inr rfl), cornerPairSlabHi,
    ite_eq_left (Or.inr rfl)] at hj'
  exact ⟨hi', hj'⟩

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
