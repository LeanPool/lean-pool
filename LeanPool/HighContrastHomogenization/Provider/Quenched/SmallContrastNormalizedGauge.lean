/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Quenched.SmallContrastBurnSplitCarriers

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastNormalizedGauge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The gauge normalization at the frozen witness

The dagger admits the free renormalization `Ψ ↦ max 1 (Ψ/Ψ(1))` at the
SAME growth witness: the tail weakens legally since `Ψ(1) ≥ 1`, the
growth condition transfers unchanged, and admissibility survives the
flooring.  After normalization the gauge's unit value is one, so the
burn-split witness `K'` is polynomial in `K` and the burn depth alone —
no `Ψ(1)` content reaches any scale threshold.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

/-- The normalized gauge. -/
@[expose]
def normalizedGauge (Ψ : ℝ → ℝ) : ℝ → ℝ :=
  fun t => max 1 (Ψ t / Ψ 1)

theorem normalizedGauge_one {Ψ : ℝ → ℝ} (hΨ1 : 0 < Ψ 1) :
    normalizedGauge Ψ 1 = 1 := by
  rw [normalizedGauge, div_self hΨ1.ne', max_self]

/-- **The dagger at the normalized gauge.** -/
theorem coarseEllipticityDagger_normalizedGauge
    {P : Measure (CoeffSpace d)} {g : ℝ}
    {E : BlockMat d} {Ψ : ℝ → ℝ} {K : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S) :
    HCPoly.Frozen.CoarseEllipticityDagger P g E
      (normalizedGauge Ψ) K S := by
  have hΨ1 : (1 : ℝ) ≤ Ψ 1 := hdag.gauge_admissible.2 zero_le_one
  have hΨ10 : (0 : ℝ) < Ψ 1 := lt_of_lt_of_le one_pos hΨ1
  refine ⟨hdag.g_mem, hdag.refBlock_isSymm, hdag.refBlock_posDef,
    ⟨?_, ?_⟩, hdag.one_lt_growthWitness, ?_,
    hdag.source_measurable, hdag.source_nonneg, ?_, hdag.coarse_bound⟩
  · -- monotone on Ici 0
    intro x hx y hy hxy
    rw [normalizedGauge, normalizedGauge]
    refine max_le_max le_rfl ?_
    have hmono := hdag.gauge_admissible.1 hx hy hxy
    rw [div_eq_mul_inv, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right hmono (inv_nonneg.mpr hΨ10.le)
  · -- ≥ 1 on Ici 0
    intro t _
    exact le_max_left _ _
  · -- the growth condition
    intro t ht
    have hgrow := hdag.gauge_growth ht
    have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
    have hK1 : (1 : ℝ) < K := hdag.one_lt_growthWitness
    have htK : t ≤ K * t := by nlinarith only [hK1, ht]
    have hΨt1 : Ψ 1 ≤ Ψ t :=
      hdag.gauge_admissible.1 (Set.mem_Ici.mpr zero_le_one)
        (Set.mem_Ici.mpr ht0) ht
    have hΨt0 : (0 : ℝ) < Ψ t := lt_of_lt_of_le hΨ10 hΨt1
    have hΨKt : Ψ t ≤ Ψ (K * t) :=
      hdag.gauge_admissible.1 (Set.mem_Ici.mpr ht0)
        (Set.mem_Ici.mpr (by nlinarith only [hK1, ht0, ht])) htK
    rw [normalizedGauge, normalizedGauge]
    -- both maxima resolve to the right branch at `t ≥ 1`
    have hbt : (1 : ℝ) ≤ Ψ t / Ψ 1 := by
      rw [le_div_iff₀ hΨ10]
      linarith only [hΨt1]
    have hbKt : (1 : ℝ) ≤ Ψ (K * t) / Ψ 1 := by
      rw [le_div_iff₀ hΨ10]
      have := le_trans hΨt1 hΨKt
      linarith only [this]
    rw [max_eq_right hbt, max_eq_right hbKt]
    have hinv0 : (0 : ℝ) ≤ (Ψ 1)⁻¹ := inv_nonneg.mpr hΨ10.le
    rw [div_eq_mul_inv (Ψ (K * t)), div_eq_mul_inv (Ψ t)]
    calc
      t * (Ψ t * (Ψ 1)⁻¹) = t * Ψ t * (Ψ 1)⁻¹ := by ring
      _ ≤ Ψ (K * t) * (Ψ 1)⁻¹ :=
        mul_le_mul_of_nonneg_right hgrow hinv0
  · -- the tail at the weaker gauge
    intro t ht
    refine le_trans (hdag.source_tail t ht) ?_
    have hΨt0 : (0 : ℝ) < Ψ t := by
      have := hdag.gauge_admissible.2 ht.le
      linarith only [this]
    rw [normalizedGauge]
    have hΨt1' : (1 : ℝ) ≤ Ψ t := hdag.gauge_admissible.2 ht.le
    have hM0 : (0 : ℝ) < max 1 (Ψ t / Ψ 1) :=
      lt_of_lt_of_le one_pos (le_max_left _ _)
    have hMle : max 1 (Ψ t / Ψ 1) ≤ Ψ t := by
      refine max_le hΨt1' ?_
      rw [div_le_iff₀ hΨ10]
      nlinarith only [hΨ1, hΨt1']
    simpa [one_div] using one_div_le_one_div_of_le hM0 hMle

end

end HCPolySupport.HighContrast.Quenched
