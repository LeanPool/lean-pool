/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.LocalizationFluctuationMeshTransfer

/-!
# GammaTenStripTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The boundary strip of the mesh, for a family of **either sign**

ABK26, Step 2 of `l.approximate.recurrence.formula`,
`e.lower.bound.localization.terms`, `e.recurrence.params`.

## Why the proved transfer is not enough

`LocalizationFluctuationMeshTransfer.cubeFamilyAverage_le_add_sqrt_boundaryFraction`
transfers a grid average from a sub-grid to the full grid at the Cauchy--Schwarz
cost of the missing fraction, but it assumes the family **nonnegative** on the
full grid: its first half replaces `|I|^{-1} sum_J F` by `avsum_J F` using
`inv_anti` on the two cardinalities, a step that reverses for a negative sum.

The Step-2 cell integrand

```
  fluct_R  =  2 mu_field(a_omega; P_z + bfF_z)  -  switch_R(P_z)
```

of `LocalizationFluctuationSelectEndpoint.meshFluctuationCellIntegrand` has **no
sign**: it is a difference of two nonnegative energies.  Its interior-mesh
average is the quantity the interior route of `Closure.GammaTenInterior*`
controls, and the full-mesh average is what
`LocalizationFluctuationSelectEndpoint.fluctuationEnergyAverage` is.  The
transfer between them therefore has to be redone without the sign.

## What is proved

* `cubeFamilyAverage_le_max_add_sqrt_boundaryFraction` --- **the signed boundary
  split**.  For `J subset I` and an arbitrary real family `F`,

  ```
    avsum_I F  <=  max (avsum_J F) 0
                    + sqrt (1 - |J|/|I|) . sqrt (avsum_I F^2) .
  ```

  Two things replace the sign hypothesis: on `J` the ratio `|J|/|I| <= 1` and the
  nonnegativity of `max (.) 0` do the work `inv_anti` used to do, and on the
  strip `I \ J` the Cauchy--Schwarz step is run at `|F|`, whose square is `F^2`.
  The `max` is unavoidable: for `F` constant `-1` and `J` a proper subset the
  bare `avsum_J F` would be `-1` while `avsum_I F` is `-1` too, but the strip
  remainder is nonnegative --- and for `J` empty `avsum_J F = 0`, so the
  right-hand side must be at least `0` before the remainder is added.
* `cubeFamilyAverage_mesoCubeGrid_le_max_interior_add` --- the same at the
  recurrence's own two meshes, with the missing fraction replaced by the
  boundary count `d 3^{g-p}`
  (`LocalizationFluctuationMeshTransfer.one_sub_interior_card_ratio_le`).  This
  is the signed mirror of the proved
  `LocalizationFluctuationMeshTransfer.gridFourthMoment_mesoCubeGrid_le_interior_add`.

## Binders

Finite combinatorics and, in the mesh form, the scale bookkeeping
`K = n + p`, `outer + 1 = n + g`, `g <= p`.  No smallness gate, nothing about the
corrector, the coefficient field or the sample space, and **no sign** on the
family.

## Scope

Internal Provider infrastructure for the Step-2 fluctuation estimate.  There is
no `sorry`, no `admit`, no custom axiom and no `set_option maxHeartbeats`.

## References

* ABK26, `l.approximate.recurrence.formula` Step 2,
  `e.lower.bound.localization.terms`, `e.recurrence.params`.
-/

namespace Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure

open HCPolySupport MeasureTheory
open Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence

noncomputable section

variable {d : ℕ}

/-! ## The signed boundary split -/

/-- **The boundary transfer without a sign hypothesis.**

For any sub-family `J` of `I` and any real family `F`,

```
  avsum_I F  <=  max (avsum_J F) 0  +  sqrt (1 - |J|/|I|) . sqrt (avsum_I F^2) .
```

The interior half uses only `|J| <= |I|` and `0 <= max (avsum_J F) 0`; the strip
half is Cauchy--Schwarz at `|F|`.  Unconditional. -/
theorem cubeFamilyAverage_le_max_add_sqrt_boundaryFraction {I J : Finset (TriadicCube d)}
    (hJI : J ⊆ I) (F : TriadicCube d → ℝ) :
    cubeFamilyAverage I F ≤
      max (cubeFamilyAverage J F) 0 +
        Real.sqrt (1 - (J.card : ℝ) / (I.card : ℝ)) *
          Real.sqrt (cubeFamilyAverage I (fun R => F R ^ 2)) := by
  classical
  rcases Nat.eq_zero_or_pos I.card with hI0 | hIpos
  · have hIempty : I = ∅ := Finset.card_eq_zero.mp hI0
    subst hIempty
    have hJempty : J = ∅ := Finset.subset_empty.mp hJI
    subst hJempty
    simp [cubeFamilyAverage]
  have hN : (0 : ℝ) < (I.card : ℝ) := by exact_mod_cast hIpos
  have hMN : J.card ≤ I.card := Finset.card_le_card hJI
  have hMNR : (J.card : ℝ) ≤ (I.card : ℝ) := by exact_mod_cast hMN
  have hsplit : ∑ R ∈ I, F R = ∑ R ∈ J, F R + ∑ R ∈ I \ J, F R := by
    rw [← Finset.sum_union Finset.disjoint_sdiff]
    congr 1
    exact (Finset.union_sdiff_of_subset hJI).symm
  have hpart1 : ((I.card : ℝ))⁻¹ * ∑ R ∈ J, F R ≤ max (cubeFamilyAverage J F) 0 := by
    rcases Nat.eq_zero_or_pos J.card with hJ0 | hJpos
    · have hJempty : J = ∅ := Finset.card_eq_zero.mp hJ0
      subst hJempty
      simp [cubeFamilyAverage]
    · have hM : (0 : ℝ) < (J.card : ℝ) := by exact_mod_cast hJpos
      have hsumJ : ∑ R ∈ J, F R = (J.card : ℝ) * cubeFamilyAverage J F := by
        show _ = (J.card : ℝ) * (((J.card : ℝ))⁻¹ * ∑ R ∈ J, F R)
        field_simp
      rw [hsumJ]
      have hle1 : (J.card : ℝ) / (I.card : ℝ) ≤ 1 := (div_le_one hN).2 hMNR
      have hmax : cubeFamilyAverage J F ≤ max (cubeFamilyAverage J F) 0 := le_max_left _ _
      have hmax0 : (0 : ℝ) ≤ max (cubeFamilyAverage J F) 0 := le_max_right _ _
      calc ((I.card : ℝ))⁻¹ * ((J.card : ℝ) * cubeFamilyAverage J F)
          = ((J.card : ℝ) / (I.card : ℝ)) * cubeFamilyAverage J F := by
            field_simp
        _ ≤ ((J.card : ℝ) / (I.card : ℝ)) * max (cubeFamilyAverage J F) 0 :=
            mul_le_mul_of_nonneg_left hmax (by positivity)
        _ ≤ 1 * max (cubeFamilyAverage J F) 0 :=
            mul_le_mul_of_nonneg_right hle1 hmax0
        _ = max (cubeFamilyAverage J F) 0 := one_mul _
  have hcard : ((I \ J).card : ℝ) = (I.card : ℝ) - (J.card : ℝ) := by
    rw [Finset.card_sdiff_of_subset hJI]
    push_cast [hMN]
    ring
  have hCS : ∑ R ∈ I \ J, |F R| ≤
      Real.sqrt (((I \ J).card : ℝ)) * Real.sqrt (∑ R ∈ I \ J, |F R| ^ 2) :=
    sum_le_sqrt_card_mul_sqrt_sum_sq _ (fun R => |F R|) fun R _ => abs_nonneg _
  have habs2 : ∑ R ∈ I \ J, |F R| ^ 2 = ∑ R ∈ I \ J, F R ^ 2 :=
    Finset.sum_congr rfl fun R _ => sq_abs _
  have hsq_le : ∑ R ∈ I \ J, F R ^ 2 ≤ ∑ R ∈ I, F R ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset fun R _ _ => sq_nonneg _
  have hsumle : ∑ R ∈ I \ J, F R ≤ ∑ R ∈ I \ J, |F R| :=
    Finset.sum_le_sum fun R _ => le_abs_self _
  have hpart2 : ((I.card : ℝ))⁻¹ * ∑ R ∈ I \ J, F R ≤
      Real.sqrt (1 - (J.card : ℝ) / (I.card : ℝ)) *
        Real.sqrt (cubeFamilyAverage I (fun R => F R ^ 2)) := by
    have hstep : ((I.card : ℝ))⁻¹ * ∑ R ∈ I \ J, F R ≤
        ((I.card : ℝ))⁻¹ *
          (Real.sqrt (((I \ J).card : ℝ)) * Real.sqrt (∑ R ∈ I, F R ^ 2)) := by
      refine mul_le_mul_of_nonneg_left (hsumle.trans (hCS.trans ?_)) (by positivity)
      rw [habs2]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hsq_le) (Real.sqrt_nonneg _)
    refine hstep.trans (le_of_eq ?_)
    unfold cubeFamilyAverage
    rw [hcard, Real.sqrt_mul (by positivity),
      show (1 : ℝ) - (J.card : ℝ) / (I.card : ℝ) =
        ((I.card : ℝ))⁻¹ * ((I.card : ℝ) - (J.card : ℝ)) by field_simp,
      Real.sqrt_mul (by positivity)]
    have hinv : Real.sqrt (((I.card : ℝ))⁻¹) * Real.sqrt (((I.card : ℝ))⁻¹) =
        ((I.card : ℝ))⁻¹ := Real.mul_self_sqrt (by positivity)
    have hrhs : Real.sqrt (((I.card : ℝ))⁻¹) * Real.sqrt ((I.card : ℝ) - (J.card : ℝ)) *
        (Real.sqrt (((I.card : ℝ))⁻¹) * Real.sqrt (∑ R ∈ I, F R ^ 2)) =
        (Real.sqrt (((I.card : ℝ))⁻¹) * Real.sqrt (((I.card : ℝ))⁻¹)) *
          (Real.sqrt ((I.card : ℝ) - (J.card : ℝ)) * Real.sqrt (∑ R ∈ I, F R ^ 2)) := by
      ring
    simp only []
    rw [hrhs, hinv]
  unfold cubeFamilyAverage
  rw [hsplit, mul_add]
  exact add_le_add hpart1 hpart2

/-! ## The signed split at the recurrence's own two meshes -/

/-- **The signed boundary split on the mesh.**

The full-mesh average of an arbitrary real family is below the truncated interior
average plus `sqrt(d 3^{g-p})` times the square root of the full-mesh average of
its square.  The signed mirror of
`LocalizationFluctuationMeshTransfer.gridFourthMoment_mesoCubeGrid_le_interior_add`.

only on the scale bookkeeping. -/
theorem cubeFamilyAverage_mesoCubeGrid_le_max_interior_add (d : ℕ) {K n outer : ℤ}
    {p g : ℕ} (hK : K = n + (p : ℤ)) (houter : outer + 1 = n + (g : ℤ)) (hgp : g ≤ p)
    (F : TriadicCube d → ℝ) :
    cubeFamilyAverage (mesoCubeGrid d K n) F ≤
      max (cubeFamilyAverage (interiorMesoCubeGrid d K n outer) F) 0 +
        Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)) *
          Real.sqrt (cubeFamilyAverage (mesoCubeGrid d K n) (fun R => F R ^ 2)) := by
  have hmain := cubeFamilyAverage_le_max_add_sqrt_boundaryFraction
    (I := mesoCubeGrid d K n) (J := interiorMesoCubeGrid d K n outer)
    interiorMesoCubeGrid_subset F
  have hfrac : Real.sqrt (1 - ((interiorMesoCubeGrid d K n outer).card : ℝ) /
        ((mesoCubeGrid d K n).card : ℝ)) ≤
      Real.sqrt ((d : ℝ) * ((3 : ℝ) ^ g / (3 : ℝ) ^ p)) :=
    Real.sqrt_le_sqrt (one_sub_interior_card_ratio_le d hK houter hgp)
  have hsq : (0 : ℝ) ≤ Real.sqrt (cubeFamilyAverage (mesoCubeGrid d K n)
      (fun R => F R ^ 2)) := Real.sqrt_nonneg _
  have hmul := mul_le_mul_of_nonneg_right hfrac hsq
  linarith [hmain, hmul]

end

end Algsuperdiff.Section3.Provider.Diffusivity.ApproximateRecurrence.Closure
