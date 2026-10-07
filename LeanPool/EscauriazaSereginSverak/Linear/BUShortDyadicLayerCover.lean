/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortShiftedCellPartition
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.MeasureTheory.Measure.Interval

/-!
# Coverage by shifted dyadic layers

The shifted layers cover the short normalized time interval, apart from
their measure-zero upper endpoints.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The integer-indexed dyadic scale equals a natural power of one half. -/
theorem bu_short_natural_dyadic_scale (k : ℕ) :
    Foundation.buSmallTimeDyadicScale (k + 1 : ℤ) =
      (1 / 2 : ℝ) ^ (k + 1) := by
  change (2 : ℝ) ^ (-((k : ℤ) + 1)) = (1 / 2 : ℝ) ^ (k + 1)
  have hexp : -((k : ℤ) + 1) = -((k + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [hexp, zpow_neg, zpow_natCast]
  simp [one_div, inv_pow]


/-- The half-open shifted dyadic layers cover the half-open normalized
time interval. -/
theorem bu_short_shifted_ioc_layers_cover :
    (⋃ k : ℕ,
      Ioc (1 / 2 + Foundation.buSmallTimeDyadicScale (k + 1 : ℤ) / 2)
        (1 / 2 + Foundation.buSmallTimeDyadicScale (k + 1 : ℤ))) =
      Ioc (1 / 2 : ℝ) 1 := by
  ext s
  constructor
  · intro hs
    rcases mem_iUnion.mp hs with ⟨k, hk⟩
    let d := Foundation.buSmallTimeDyadicScale (k + 1 : ℤ)
    have hd : 0 < d := Foundation.buSmallTimeDyadicScale_pos _
    have hdle : d ≤ 1 / 2 := by
      dsimp [d]
      rw [bu_short_natural_dyadic_scale]
      have hpow : (1 / 2 : ℝ) ^ k ≤ 1 :=
        pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
      rw [pow_succ]
      nlinarith only [hpow]
    exact ⟨by linarith only [hk.1, hd], by linarith only [hk.2, hdle]⟩
  · intro hs
    have hδ : 0 < s - 1 / 2 := by linarith only [hs.1]
    have hδle : s - 1 / 2 ≤ 1 / 2 := by linarith only [hs.2]
    obtain ⟨n, hnlo, hnhi⟩ :=
      exists_nat_pow_near_of_lt_one hδ
        (by linarith only [hδle])
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)
    cases n with
    | zero =>
      have hlow : (1 / 2 : ℝ) < s - 1 / 2 := by simpa using hnlo
      exact False.elim (by linarith only [hlow, hδle])
    | succ k =>
      refine mem_iUnion.mpr ⟨k, ?_⟩
      rw [bu_short_natural_dyadic_scale]
      have hlow : (1 / 2 : ℝ) ^ (k + 1) / 2 < s - 1 / 2 := by
        simpa [pow_succ, div_eq_mul_inv, mul_comm] using hnlo
      constructor
      · linarith only [hlow]
      · linarith only [hnhi]


/-- The open shifted dyadic layers cover normalized time up to null
endpoints. -/
theorem bu_short_shifted_open_layers_ae :
    (⋃ k : ℕ,
      Ioo (1 / 2 + Foundation.buSmallTimeDyadicScale (k + 1 : ℤ) / 2)
        (1 / 2 + Foundation.buSmallTimeDyadicScale (k + 1 : ℤ))) =ᵐ[volume]
      Ioo (1 / 2 : ℝ) 1 := by
  have heach (k : ℕ) :
      Ioo (1 / 2 + Foundation.buSmallTimeDyadicScale (k + 1 : ℤ) / 2)
          (1 / 2 + Foundation.buSmallTimeDyadicScale (k + 1 : ℤ)) =ᵐ[volume]
        Ioc (1 / 2 + Foundation.buSmallTimeDyadicScale (k + 1 : ℤ) / 2)
          (1 / 2 + Foundation.buSmallTimeDyadicScale (k + 1 : ℤ)) :=
    Ioo_ae_eq_Ioc
  have hunion := (Filter.EventuallyEqSet.countable_iUnion heach)
  rw [bu_short_shifted_ioc_layers_cover] at hunion
  exact hunion.trans Ioo_ae_eq_Ioc.symm

/-- The shifted dyadic space-time layers cover the short normalized
slab up to a null set. -/
theorem bu_short_shifted_parabolic_layers_ae :
    (⋃ k : ℕ,
      (Set.univ ×ˢ Ioo
        (1 / 2 + Foundation.buSmallTimeDyadicScale (k + 1 : ℤ) / 2)
        (1 / 2 + Foundation.buSmallTimeDyadicScale (k + 1 : ℤ)) :
          Set ParabolicPoint)) =ᵐ[volume]
      (Set.univ ×ˢ Ioo (1 / 2 : ℝ) 1 : Set ParabolicPoint) := by
  rw [← Set.prod_iUnion]
  rw [Measure.volume_eq_prod Vec3 ℝ]
  exact Measure.set_prod_ae_eq Filter.EventuallyEq.rfl
    bu_short_shifted_open_layers_ae

end ESS
