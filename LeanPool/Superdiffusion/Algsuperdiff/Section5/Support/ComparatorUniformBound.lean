/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Support.LocalizedFinite

/-!
# ComparatorUniformBound

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The comparator is uniformly bounded over the normalized forcing class

On the normalized class the interior Schauder estimate for the comparator reads,
at `Kg = 3^{-n/2}`,

```text
  3^{-n/2} Ksup + KHol ≤ C 3^{-n/2} σ_n⁻¹ ,
```

so `Ksup ≤ C σ_n⁻¹` uniformly in the forcing field, and the supremum bound of
the comparator's Lipschitz representative becomes

```text
  σ_n 3^{-n} ‖v‖_{L^∞(y+□_n)} ≤ σ_n 3^{-n} · d · C σ_n⁻¹ · 3^n / 2 = d C / 2 ,
```

a bound with no dependence on the scale, the centre, the model or the datum.
This discharges the comparator hypothesis of the localized finiteness statements;
the rough-field hypothesis is left explicit, to be discharged by the boundary
Schauder estimate.

## Main results

* `ksup_le_of_normalized_estimate` — the scalar step `Ksup ≤ C σ_n⁻¹`.
* `exists_hasUniformComparatorSupBound` — the comparator hypothesis of the
  localized finiteness statements holds, with an explicit constant.
* `localizedError_comparator_term_le` — the normalized form `d C / 2`.

## References

* ABK26, the comparator of Section 5.1.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open Algsuperdiff.Section4.Support
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. Congruence of the two gauges under a pointwise identity -/

theorem supNormOn_congr {E : Type*} [NormedAddCommGroup E] {U : Set (Vec d)}
    {f h : Vec d → E} (hfh : Set.EqOn f h U) : supNormOn U f = supNormOn U h := by
  refine le_antisymm (supNormOn_le_iff.2 fun x hx => ?_) (supNormOn_le_iff.2 fun x hx => ?_)
  · rw [hfh hx]
    exact le_supNormOn hx
  · rw [← hfh hx]
    exact le_supNormOn hx

/-! ## 2. The scalar step -/

/-- **`Ksup ≤ C σ_n⁻¹` on the normalized class.**  The two powers of three on the
right cancel at `Kg = 3^{-n/2}`, and the nonnegative Hölder constant is dropped
from the left. -/
theorem ksup_le_of_normalized_estimate {C Ksup KHol sigma : ℝ} (n : ℤ) (hKHol : 0 ≤ KHol)
    (hest : Real.rpow 3 (-((1 / 2 : ℝ) * (n : ℝ))) * Ksup + KHol ≤
      C * (Real.rpow 3 ((1 / 2 : ℝ) * (n : ℝ)))⁻¹ *
        (sigma⁻¹ * Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 (-(n : ℝ) / 2))) :
    Ksup ≤ C * sigma⁻¹ := by
  have h3 : (0 : ℝ) < Real.rpow 3 ((1 / 2 : ℝ) * (n : ℝ)) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hcancel : Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 (-(n : ℝ) / 2) = 1 := by
    show (3 : ℝ) ^ ((n : ℝ) / 2) * (3 : ℝ) ^ (-(n : ℝ) / 2) = 1
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      show ((n : ℝ) / 2 + -(n : ℝ) / 2) = 0 by ring, Real.rpow_zero]
  have hneg : Real.rpow 3 (-((1 / 2 : ℝ) * (n : ℝ))) =
      (Real.rpow 3 ((1 / 2 : ℝ) * (n : ℝ)))⁻¹ := by
    show (3 : ℝ) ^ (-((1 / 2 : ℝ) * (n : ℝ))) = ((3 : ℝ) ^ ((1 / 2 : ℝ) * (n : ℝ)))⁻¹
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  rw [hneg] at hest
  have hrw : C * (Real.rpow 3 ((1 / 2 : ℝ) * (n : ℝ)))⁻¹ *
      (sigma⁻¹ * Real.rpow 3 ((n : ℝ) / 2) * Real.rpow 3 (-(n : ℝ) / 2)) =
      (Real.rpow 3 ((1 / 2 : ℝ) * (n : ℝ)))⁻¹ * (C * sigma⁻¹) := by
    rw [mul_assoc, mul_assoc, hcancel]
    ring
  rw [hrw] at hest
  have hmul : (Real.rpow 3 ((1 / 2 : ℝ) * (n : ℝ)))⁻¹ * Ksup ≤
      (Real.rpow 3 ((1 / 2 : ℝ) * (n : ℝ)))⁻¹ * (C * sigma⁻¹) := by linarith
  exact le_of_mul_le_mul_left (by linarith [hmul]) (inv_pos.2 h3)

/-! ## 3. The comparator hypothesis of the localized finiteness statements -/

/-- **The comparator representatives are uniformly bounded on the normalized
class.**  The constant is explicit and depends only on `d`, the universal
Schauder constant, the diffusivity `σ_n` and the scale. -/
theorem exists_hasUniformComparatorSupBound (d : ℕ) (hdim : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (n : ℤ) (y : Vec d),
        HasUniformComparatorSupBound M n y
          ((d : ℝ) * (C * (Annealed.sigmaBar M n : ℝ)⁻¹) * (3 : ℝ) ^ n / 2) := by
  obtain ⟨C, hC, hcomp⟩ := exists_lipschitzRepresentative_comparator d hdim
  refine ⟨C, hC, fun M n y g hg v' hv' vRep' hvRep' => ?_⟩
  obtain ⟨v, vRep, Ksup, KHol, hv, hKsup, hKHol, -, -, hest, hvae, hLip, hsupN, -⟩ :=
    hcomp M n y g (Real.rpow 3 (-(n : ℝ) / 2)) hg
  have hKsupBound : Ksup ≤ C * (Annealed.sigmaBar M n : ℝ)⁻¹ :=
    ksup_le_of_normalized_estimate n hKHol hest
  have hRep : IsCubeRepresentative y n v vRep := ⟨hvae.symm, hLip.continuous.continuousOn⟩
  have hae : v.toFun =ᵐ[volume.restrict (cubeSetAt y n)] v'.toFun :=
    (isDirichletSolutionAt_ae_unique_comparator M n y hv hv').2
  have heq : Set.EqOn vRep vRep' (cubeSetAt y n) :=
    isCubeRepresentative_eqOn hae hRep hvRep'
  rw [← supNormOn_congr heq]
  refine hsupN.trans (ENNReal.ofReal_le_ofReal ?_)
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hdnn : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hstep : (d : ℝ) * Ksup ≤ (d : ℝ) * (C * (Annealed.sigmaBar M n : ℝ)⁻¹) :=
    mul_le_mul_of_nonneg_left hKsupBound hdnn
  have hstep2 : (d : ℝ) * Ksup * (3 : ℝ) ^ n ≤
      (d : ℝ) * (C * (Annealed.sigmaBar M n : ℝ)⁻¹) * (3 : ℝ) ^ n :=
    mul_le_mul_of_nonneg_right hstep h3.le
  linarith

/-! ## 4. The normalized form -/

/-- **The comparator contributes at most `d C / 2` to the localized error.** -/
theorem localizedError_comparator_term_le (d : ℕ) (hdim : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : ABKModel d) (n : ℤ) (y : Vec d) (g : Vec d → Vec d),
        NormalizedForceAt y n g →
        ∀ v : H1Function (cubeSetAt y n),
          IsDirichletSolutionAt
            (fun _ => (Annealed.sigmaBar M n : ℝ) • (1 : Mat d)) y n v g →
          ∀ vRep : Vec d → ℝ, IsCubeRepresentative y n v vRep →
            ENNReal.ofReal ((Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ))) *
                supNormOn (cubeSetAt y n) vRep ≤
              ENNReal.ofReal ((d : ℝ) * C / 2) := by
  obtain ⟨C, hC, hbound⟩ := exists_hasUniformComparatorSupBound d hdim
  refine ⟨C, hC, fun M n y g hg v hv vRep hvRep => ?_⟩
  have hsig : (0 : ℝ) < (Annealed.sigmaBar M n : ℝ) := Provider.Orlicz.sigmaBar_pos M n
  have h3 : (0 : ℝ) < (3 : ℝ) ^ n := zpow_pos (by norm_num) n
  have hrpow : Real.rpow 3 (-(n : ℝ)) = ((3 : ℝ) ^ n)⁻¹ := by
    show (3 : ℝ) ^ (-(n : ℝ)) = ((3 : ℝ) ^ n)⁻¹
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_intCast]
  have hstep := hbound M n y g hg v hv vRep hvRep
  have hnn : (0 : ℝ) ≤ (Annealed.sigmaBar M n : ℝ) * Real.rpow 3 (-(n : ℝ)) :=
    mul_nonneg hsig.le (Real.rpow_nonneg (by norm_num) _)
  refine le_trans (mul_le_mul' le_rfl hstep) ?_
  rw [← ENNReal.ofReal_mul hnn]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hrpow]
  have hexp : (Annealed.sigmaBar M n : ℝ) * ((3 : ℝ) ^ n)⁻¹ *
      ((d : ℝ) * (C * (Annealed.sigmaBar M n : ℝ)⁻¹) * (3 : ℝ) ^ n / 2) =
      (d : ℝ) * C / 2 := by
    field_simp
  rw [hexp]

end

end Algsuperdiff.Section5.Support
