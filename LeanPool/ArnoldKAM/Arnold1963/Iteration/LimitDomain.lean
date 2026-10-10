/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Iteration.Construction
public import LeanPool.ArnoldKAM.Arnold1963.Iteration.TotalBudget
public import LeanPool.ArnoldKAM.Arnold1963.Iteration.Measure

/-!
The compact intersection of actual iteration domains, with positive measure and strict loss
bounds obtained from the summable budget.
-/

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped NNReal ENNReal
namespace KamProject.Arnold1963.Iteration.InitialData
variable {n : ℕ} {Ω₀ : Set (ComplexSpace n)} {δ₁ θ₀ Θ₀ ρ₀ : ℝ≥0} {κ D : ℝ}
  (b : InitialParameters n δ₁ θ₀ Θ₀ ρ₀ κ D)
  (h : InitialData n Ω₀ δ₁ θ₀ Θ₀ ρ₀ D)

theorem step_measure (s : ℕ) :
    realVolume (h.actionDomain b s \ h.actionDomain b (s + 1)) ≤
      lossBudget n δ₁ θ₀ Θ₀ κ D s * realVolume h.domain := by
  have hh := Iteration.result_measure_uniform (h.state b s).ar (h.state b s).input
    h.chart b.lower_pos b.delta_quarter h.upper h.typeD
    (b.previousCutoff_ge_one s) (b.cutoff_step_le s)
  apply hh.trans_eq
  change ENNReal.ofReal ((2 * (Θ₀ : ℝ) / θ₀) ^ n) *
    (ENNReal.ofReal (resonanceLossConstant n * D * rawLoss n δ₁ Θ₀ κ s) * realVolume h.domain) = _
  unfold lossBudget actionLossFactor
  rw [show (2 * (Θ₀ : ℝ) / θ₀) ^ n * resonanceLossConstant n * D * rawLoss n δ₁ Θ₀ κ s =
    (2 * (Θ₀ : ℝ) / θ₀) ^ n * (resonanceLossConstant n * D * rawLoss n δ₁ Θ₀ κ s) by ring,
    ENNReal.ofReal_mul (pow_nonneg
      (div_nonneg (mul_nonneg (by norm_num) Θ₀.coe_nonneg) θ₀.coe_nonneg) n), mul_assoc]
  ac_rfl

/-- The intersection of all action domains retained during the iteration. -/
def limitDomain : Set (ComplexSpace n) := ⋂ s, h.actionDomain b s

theorem limit_subset (s : ℕ) : h.limitDomain b ⊆ h.actionDomain b s := iInter_subset _ s

theorem limit_compact : IsCompact (h.limitDomain b) :=
  h.chart.compact.of_isClosed_subset (isClosed_iInter fun s => (h.domain_compact b s).isClosed)
    (h.limit_subset b 0)

theorem limit_loss : realVolume (h.domain \ h.limitDomain b) <
    ENNReal.ofReal κ * realVolume h.domain := by
  exact (limit_positive_of_budget (h.actionDomain b) (lossBudget n δ₁ θ₀ Θ₀ κ D)
    (h.step_measure b) b.lossBudget_tsum_lt (ENNReal.ofReal_lt_one.mpr b.fraction_lt_one)
    h.volume_pos h.volume_finite).1

theorem limit_volume_pos : 0 < realVolume (h.limitDomain b) :=
  (limit_positive_of_budget (h.actionDomain b) (lossBudget n δ₁ θ₀ Θ₀ κ D)
    (h.step_measure b) b.lossBudget_tsum_lt (ENNReal.ofReal_lt_one.mpr b.fraction_lt_one)
    h.volume_pos h.volume_finite).2.1

theorem limit_realSlice_nonempty : (realSlice (h.limitDomain b)).Nonempty :=
  realSlice_nonempty_of_realVolume_pos (h.limit_volume_pos b)

theorem finite_loss (s : ℕ) : realVolume (h.domain \ h.actionDomain b s) <
    ENNReal.ofReal κ * realVolume h.domain :=
  (realVolume_mono (sdiff_subset_sdiff_right (h.limit_subset b s))).trans_lt (h.limit_loss b)

theorem domain_realSlice_nonempty (s : ℕ) : (realSlice (h.actionDomain b s)).Nonempty :=
  (h.limit_realSlice_nonempty b).mono (preimage_mono (h.limit_subset b s))

theorem phase_nonempty (s : ℕ) : (h.phase b s).Nonempty := by
  obtain ⟨x, hx⟩ := h.domain_realSlice_nonempty b s
  refine ⟨(complexify x, 0), hx, ?_⟩
  apply (mem_angleStrip_iff _ _).mpr
  intro j
  simp only [Pi.zero_apply, Complex.zero_im, abs_zero]
  exact (width n ρ₀ δ₁ s).coe_nonneg

theorem limit_volume_gt : ENNReal.ofReal (1 - κ) * realVolume h.domain <
    realVolume (h.limitDomain b) := by
  have hsub : realSlice (h.limitDomain b) ⊆ realSlice h.domain :=
    preimage_mono (h.limit_subset b 0)
  have hfin : realVolume (h.limitDomain b) ≠ ⊤ :=
    ne_top_of_le_ne_top h.volume_finite (realVolume_mono (h.limit_subset b 0))
  have he : realVolume (h.domain \ h.limitDomain b) =
      realVolume h.domain - realVolume (h.limitDomain b) := by
    exact measure_sdiff hsub
      (measurableSet_realSlice_of_isCompact (h.limit_compact b)).nullMeasurableSet hfin
  have hl := h.limit_loss b
  rw [he] at hl
  have hk : ENNReal.ofReal κ * realVolume h.domain ≤ realVolume h.domain := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (ENNReal.ofReal_lt_one.mpr b.fraction_lt_one).le (zero_le : 0 ≤ realVolume h.domain)
  have hh := ENNReal.sub_lt_of_sub_lt hk (Or.inl h.volume_finite) hl
  rw [ENNReal.ofReal_sub 1 b.fraction_pos.le, ENNReal.ofReal_one,
    ENNReal.sub_mul (fun _ _ => h.volume_finite), one_mul]
  exact hh

end KamProject.Arnold1963.Iteration.InitialData
