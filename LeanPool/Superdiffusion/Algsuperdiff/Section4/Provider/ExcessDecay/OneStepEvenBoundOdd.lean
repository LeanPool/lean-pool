/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepDatumPriceOdd

/-!
# OneStepEvenBoundOdd

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The odd/even split of a face-odd competitor, and its cost on the doubled window

reduced the boundary branch's odd-class defect to the **even-part bound**

```text
  ‖even part of ℓ*‖_{L²(U₂)} ≤ C(d) · affineExcessRaw U₂ V ,               (★)
```

for `V` harmonic on the doubled window and odd about the met face, and `ℓ*` an
affine minimizer of `V` on `U₂`.  This module proves the algebraic half of
`(★)`: the exact reflection identities the analytic half consumes, and the
resulting `L²` bound for the affine residual on the **doubled** window.

## The three identities

Write `ρ` for the reflection through the met face `{yᵢ = a}`, `a = (1/2)·3^m`,
and split `ℓ* = o + e` into its odd (normal) and even parts of
`OneStepDatumPriceOdd`.  Then, pointwise and with no hypothesis beyond
`V ∘ ρ = -V`:

```text
  o ∘ ρ = -o ,      e ∘ ρ = e ,      (V - ℓ*) ∘ ρ + (V - ℓ*) = -2 e .
```

The third is the identity the near-face slab comparison of `OneStepEvenBound`
runs on; the first two are what make it exact.  Note that `e ∘ ρ = e` is not an
accident of the window: the even part has vanishing `i`-slope
(`evenAffineSlope_apply_self`), so it is constant along the reflection.

## The cost on the doubled window

`V - o` is odd about the met face, so the proved odd bridge
(`OneStepBoundaryOdd.normalizedL2On_oddExtend_le`) prices it on the doubled
window by `2^d` times its cost on `U₂`.  Subtracting the even part back gives

```text
  ‖V - ℓ*‖_{L²(R)} ≤ 2^d (‖V - ℓ*‖_{L²(U₂)} + ‖e‖_{L²(U₂)}) + ‖e‖_{L²(R)} ,
```

which is exactly the input the interior Hessian estimate on the doubled window
needs: the Hessian of `V - ℓ*` at a near-face point is controlled by the
**affine-subtracted** `L²` norm, not by `‖V‖`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay.Schauder

open MeasureTheory
open HCPolySupport (Vec vecDot openCubeSet originCube coordFaceReflection)
open Algsuperdiff.Section4.Support
open Algsuperdiff.Section4.Provider.ExcessDecay

noncomputable section

variable {d : ℕ}

/-! ## 1. The even part is constant along the reflection -/

/-- A slope with vanishing `i`-coordinate does not see the `i`-face
reflection. -/
theorem vecDot_coordFaceReflection_of_apply_eq_zero {g : Vec d} {i : Fin d}
    (hg : g i = 0) (a : ℝ) (y : Vec d) :
    vecDot g (coordFaceReflection a i y) = vecDot g y := by
  classical
  show ∑ j : Fin d, g j * (coordFaceReflection a i y) j = ∑ j : Fin d, g j * y j
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j = i
  · subst hj
    rw [hg, zero_mul, zero_mul]
  · rw [HCPolySupport.coordFaceReflection_apply_ne a i j y hj]

/-- An affine function with vanishing `i`-slope is invariant under the `i`-face
reflection. -/
theorem affineEval_coordFaceReflection_of_slope_zero {c : ℝ} {g : Vec d} {i : Fin d}
    (hg : g i = 0) (a : ℝ) (y : Vec d) :
    affineEval c g (coordFaceReflection a i y) = affineEval c g y := by
  rw [affineEval, affineEval, vecDot_coordFaceReflection_of_apply_eq_zero hg]

/-! ## 2. The two halves of the affine minimizer, as functions -/

/-- The **even part** of the affine datum `(c, A)` at the met upper `i`-face, as
a function on `Vec d`. -/
def evenAffinePart (x : Vec d) (m : ℤ) (i : Fin d) (c : ℝ) (A : Vec d) : Vec d → ℝ :=
  affineEval (evenAffineIntercept x m i c A) (evenAffineSlope i A)

/-- The **odd (normal) part** of the affine datum `(c, A)` at the met upper
`i`-face, as a function on `Vec d`. -/
def oddAffinePart (x : Vec d) (m : ℤ) (i : Fin d) (A : Vec d) : Vec d → ℝ :=
  affineEval (oddAffineIntercept x m i A - vecDot (oddAffineSlope i A) x)
    (oddAffineSlope i A)

/-- The odd part is the normal ramp `Aᵢ (yᵢ - a)`. -/
theorem oddAffinePart_apply (x : Vec d) (m : ℤ) (i : Fin d) (A y : Vec d) :
    oddAffinePart x m i A y = A i * (y i - (1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
  rw [oddAffinePart, ← affineLift_eq_affineEval, affineLift_oddAffineDatum]

/-- **The split**, as an identity of functions. -/
theorem affineEval_eq_oddAffinePart_add_evenAffinePart (x : Vec d) (m : ℤ) (i : Fin d)
    (c : ℝ) (A y : Vec d) :
    affineEval (c - vecDot A x) A y
      = oddAffinePart x m i A y + evenAffinePart x m i c A y :=
  affineEval_split x m i c A y

/-- The odd part is odd about the met face. -/
theorem oddAffinePart_coordFaceReflection (x : Vec d) (m : ℤ) (i : Fin d) (A y : Vec d) :
    oddAffinePart x m i A (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y)
      = -oddAffinePart x m i A y := by
  rw [oddAffinePart_apply, oddAffinePart_apply,
    HCPolySupport.coordFaceReflection_apply_self]
  ring

/-- The even part is even about the met face. -/
theorem evenAffinePart_coordFaceReflection (x : Vec d) (m : ℤ) (i : Fin d) (c : ℝ)
    (A y : Vec d) :
    evenAffinePart x m i c A (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y)
      = evenAffinePart x m i c A y :=
  affineEval_coordFaceReflection_of_slope_zero (evenAffineSlope_apply_self i A) _ y

/-! ## 3. The reflection identity for the affine residual -/

/-- **The reflection identity.**  For a competitor odd about the met face, the
affine residual and its reflection add up to `-2` times the even part — an
exact pointwise identity, with no membership hypothesis. -/
theorem sub_affineEval_add_reflect {x : Vec d} {m : ℤ} {i : Fin d} {V : Vec d → ℝ}
    (hVodd : ∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    (c : ℝ) (A : Vec d) (y : Vec d) :
    (V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y)
        - affineEval (c - vecDot A x) A
            (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y))
      + (V y - affineEval (c - vecDot A x) A y)
      = -2 * evenAffinePart x m i c A y := by
  rw [affineEval_eq_oddAffinePart_add_evenAffinePart x m i c A,
    affineEval_eq_oddAffinePart_add_evenAffinePart x m i c A y,
    oddAffinePart_coordFaceReflection, evenAffinePart_coordFaceReflection, hVodd y]
  ring

/-- **The odd summand.**  Subtracting the odd part of the affine minimizer from a
face-odd competitor leaves a face-odd function. -/
theorem faceOdd_sub_oddAffinePart {x : Vec d} {m : ℤ} {i : Fin d} {V : Vec d → ℝ}
    (hVodd : ∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    (A : Vec d) (z : Vec d) :
    (fun y => V y - oddAffinePart x m i A y)
        (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z)
      = -((fun y => V y - oddAffinePart x m i A y) z) := by
  show V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z)
      - oddAffinePart x m i A (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z)
    = -(V z - oddAffinePart x m i A z)
  rw [hVodd z, oddAffinePart_coordFaceReflection]
  ring

/-! ## 4. The affine residual on the doubled window -/

/-- **The odd bridge for the affine residual.**  For `V` odd about the met face,
the residual `V - ℓ*` on the doubled window is priced by its cost on `U₂`
together with the even part's cost on both windows.

This is the input the interior Hessian estimate consumes: it is the
*affine-subtracted* residual, so no unsubtracted `‖V‖` ever appears. -/
theorem normalizedL2On_reflectedWindow_sub_affineEval_le {m n : ℤ} {x : Vec d}
    (hx : x ∈ openCubeSet (originCube d m)) (hmn : n - 2 < m) {i : Fin d}
    (hup : MeetsUpperFace x m (n - 2) i)
    (hother : ∀ j, j ≠ i → ¬ MeetsUpperFace x m (n - 2) j ∧ ¬ MeetsLowerFace x m (n - 2) j)
    {V : Vec d → ℝ}
    (hVodd : ∀ z, V (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z) = -V z)
    (hVR : MemLp V 2 (volume.restrict (reflectedWindow x m (n - 2)))) (c : ℝ) (A : Vec d) :
    normalizedL2On (reflectedWindow x m (n - 2))
        (fun y => V y - affineEval (c - vecDot A x) A y)
      ≤ 2 ^ d * (normalizedL2On (truncatedWindow x m (n - 2))
              (fun y => V y - affineEval (c - vecDot A x) A y)
            + normalizedL2On (truncatedWindow x m (n - 2)) (evenAffinePart x m i c A))
          + normalizedL2On (reflectedWindow x m (n - 2)) (evenAffinePart x m i c A) := by
  set R : Set (Vec d) := reflectedWindow x m (n - 2) with hRdef
  set U : Set (Vec d) := truncatedWindow x m (n - 2) with hUdef
  set e : Vec d → ℝ := evenAffinePart x m i c A with hedef
  set F : Vec d → ℝ := fun y => V y - oddAffinePart x m i A y with hFdef
  set f : Vec d → ℝ := fun y => V y - affineEval (c - vecDot A x) A y with hfdef
  -- the `L²` data
  have hVU : MemLp V 2 (volume.restrict U) :=
    hVR.mono_measure (Measure.restrict_mono (truncatedWindow_subset_reflectedWindow x m (n - 2))
      le_rfl)
  have heR : MemLp e 2 (volume.restrict R) := by
    rw [hedef, evenAffinePart]
    exact memLp_affineEval_reflectedWindow x m (n - 2) _ _
  have heU : MemLp e 2 (volume.restrict U) := by
    rw [hedef, evenAffinePart]
    exact memLp_affineEval_truncatedWindow x m (n - 2) _ _
  have hFR : MemLp F 2 (volume.restrict R) := by
    rw [hFdef, oddAffinePart]
    exact hVR.sub (memLp_affineEval_reflectedWindow x m (n - 2) _ _)
  have hFU : MemLp F 2 (volume.restrict U) := by
    rw [hFdef, oddAffinePart]
    exact hVU.sub (memLp_affineEval_truncatedWindow x m (n - 2) _ _)
  have hfU : MemLp f 2 (volume.restrict U) := by
    rw [hfdef]
    exact hVU.sub (memLp_affineEval_truncatedWindow x m (n - 2) _ _)
  -- the odd bridge for `F`
  have hFodd : oddExtend x m (n - 2) F =ᵐ[volume] F :=
    oddExtend_ae_eq_self_of_faceOdd_upper hup hother (faceOdd_sub_oddAffinePart hVodd A)
  have hFoddR : oddExtend x m (n - 2) F =ᵐ[volume.restrict R] F :=
    MeasureTheory.ae_restrict_of_ae hFodd
  have hoddFR : MemLp (oddExtend x m (n - 2) F) 2 (volume.restrict R) :=
    hFR.ae_eq hFoddR.symm
  have hRpos : 0 < (volume R).toReal :=
    volume_toReal_reflectedWindow_pos x hx (by omega)
  have hUpos : 0 < (volume U).toReal :=
    volume_toReal_truncatedWindow_pos x hx (by omega)
  have hbridge : normalizedL2On R F ≤ 2 ^ d * normalizedL2On U F := by
    have h := normalizedL2On_oddExtend_le x hmn F hRpos hUpos hoddFR hFU
    rwa [normalizedL2On_congr_ae hFoddR] at h
  -- `F = f + e` on `U`, and `f = F - e` on `R`
  have hFfe : F = fun y => f y + e y := by
    funext y
    show V y - oddAffinePart x m i A y
        = (V y - affineEval (c - vecDot A x) A y) + evenAffinePart x m i c A y
    rw [affineEval_eq_oddAffinePart_add_evenAffinePart x m i c A y]
    ring
  have hfFe : f = fun y => F y + (-e y) := by
    funext y
    show V y - affineEval (c - vecDot A x) A y
        = (V y - oddAffinePart x m i A y) + -evenAffinePart x m i c A y
    rw [affineEval_eq_oddAffinePart_add_evenAffinePart x m i c A y]
    ring
  have hstepU : normalizedL2On U F ≤ normalizedL2On U f + normalizedL2On U e := by
    rw [hFfe]
    exact normalizedL2On_add_le hfU heU
  have hstepR : normalizedL2On R f ≤ normalizedL2On R F + normalizedL2On R e := by
    have hneg : MemLp (fun y => -e y) 2 (volume.restrict R) := heR.neg
    have h := normalizedL2On_add_le (W := R) (f := F) (g := fun y => -e y) hFR hneg
    rw [← hfFe] at h
    refine le_trans h (le_of_eq ?_)
    congr 1
    exact normalizedL2On_neg R e
  have h2d : (0 : ℝ) ≤ 2 ^ d := by positivity
  have hmul : 2 ^ d * normalizedL2On U F
      ≤ 2 ^ d * (normalizedL2On U f + normalizedL2On U e) :=
    mul_le_mul_of_nonneg_left hstepU h2d
  linarith only [hstepR, hbridge, hmul]

end

end Algsuperdiff.Section4.Provider.ExcessDecay.Schauder
