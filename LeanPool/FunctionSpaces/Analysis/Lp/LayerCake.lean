/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Integral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The layer cake formula in `ℝ≥0∞` and integrals of powers

For every measure `ν`, every almost everywhere measurable `F : α → [0, ∞]` and `p > 0`, the
**layer cake formula** `∫ F^p dν = p ∫_0^∞ ν{F > t} t^(p-1) dt` holds in `[0, ∞]`
(`MeasureTheory.lintegral_rpow_eq_lintegral_meas_lt_mul_ennreal`). Mathlib's
`lintegral_rpow_eq_lintegral_meas_lt_mul` is the version for real `f ≥ 0`. The truncations
`min(F, N)` reduce the formula to it (`MeasureTheory.lintegral_min_natCast_rpow_eq`, with the
level sets `ENNReal.lt_toReal_min_natCast_iff` and the limit `ENNReal.iSup_min_natCast_rpow`),
and monotone convergence gives the limit `N → ∞`.

The **integrals of powers** in `[0, ∞]` that the layer cake method uses:

* `∫_{(0,b)} t^r dt = b^(r+1)/(r+1)` for `b ≥ 0` and `r > -1`
  (`MeasureTheory.lintegral_Ioo_rpow`), and `∫_{(0,∞)} t^r dt = ∞` for every `r`
  (`MeasureTheory.lintegral_Ioi_rpow_eq_top`);
* for every `a ∈ [0, ∞]`, `∫_0^∞ 1_{t < a} t^r dt = a^(r+1)/(r+1)` for `r > -1`
  (`MeasureTheory.lintegral_Ioi_rpow_indicator_lt`) and
  `∫_0^∞ 1_{t ≥ a} t^r dt = a^(r+1)/(-(r+1))` for `r < -1`
  (`MeasureTheory.lintegral_Ioi_rpow_indicator_ge`);
* `∫_0^∞ 1_{t/2 < a} a b t^(p-2) dt = 2^(p-1)/(p-1) a^p b` for `a, b ∈ [0, ∞]` and `p > 1`
  (`MeasureTheory.lintegral_Ioi_indicator_half_lt_mul_rpow`).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal

/-! ### The layer cake formula for `[0, ∞]`-valued functions -/

namespace ENNReal

/-- The level sets of the truncation `min(a, N)`: for `t > 0`, `t < min(a, N)` exactly when
`t < a` and `t < N`. -/
theorem lt_toReal_min_natCast_iff {a : ℝ≥0∞} {N : ℕ} {t : ℝ} (ht : 0 < t) :
    t < (min a N).toReal ↔ ENNReal.ofReal t < a ∧ t < N := by
  have hne : min a (N : ℝ≥0∞) ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _)
  rw [← ENNReal.ofReal_lt_iff_lt_toReal ht.le hne, lt_min_iff,
    ENNReal.ofReal_lt_iff_lt_toReal ht.le (ENNReal.natCast_ne_top N), ENNReal.toReal_natCast]

/-- The truncations `min(a, N)^p` increase to `a^p`. -/
theorem iSup_min_natCast_rpow (a : ℝ≥0∞) {p : ℝ} (hp : 0 < p) :
    ⨆ N : ℕ, min a N ^ p = a ^ p := by
  have h1 : ⨆ N : ℕ, min a (N : ℝ≥0∞) = a := by
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have h2 := (ENNReal.orderIsoRpow p hp).map_iSup fun N : ℕ => min a (N : ℝ≥0∞)
  simp only [ENNReal.orderIsoRpow_apply, h1] at h2
  exact h2.symm

end ENNReal

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The **layer cake formula for the truncation** `min F N`:
`∫ min(F, N)^p dν = p ∫_0^N ν{F > t} t^(p-1) dt`, from Mathlib's real-valued
`lintegral_rpow_eq_lintegral_meas_lt_mul`. -/
theorem lintegral_min_natCast_rpow_eq (ν : Measure α) {F : α → ℝ≥0∞} (hF : AEMeasurable F ν)
    (N : ℕ) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, min (F x) N ^ p ∂ν = ENNReal.ofReal p *
      ∫⁻ t in Ioo (0 : ℝ) N, ν {x | ENNReal.ofReal t < F x} * ENNReal.ofReal (t ^ (p - 1)) := by
  have hf : AEMeasurable (fun x => (min (F x) N).toReal) ν :=
    ENNReal.measurable_toReal.comp_aemeasurable (hF.min aemeasurable_const)
  have h := lintegral_rpow_eq_lintegral_meas_lt_mul ν (ae_of_all _ fun x => ENNReal.toReal_nonneg)
    hf hp
  have hL : ∀ x, ENNReal.ofReal ((min (F x) N).toReal ^ p) = min (F x) N ^ p := fun x => by
    rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hp.le, ENNReal.ofReal_toReal
      (ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (min_le_right _ _))]
  simp_rw [hL] at h
  rw [h]
  congr 1
  rw [← Set.Ioi_inter_Iio, Set.inter_comm, ← Measure.restrict_restrict measurableSet_Iio,
    ← lintegral_indicator measurableSet_Iio]
  refine setLIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
  by_cases htN : t < N
  · rw [Set.indicator_of_mem (show t ∈ Iio (N : ℝ) from htN)]
    congr 2
    ext x
    simp only [mem_ofPred_eq, ENNReal.lt_toReal_min_natCast_iff ht, htN, and_true]
  · rw [Set.indicator_of_notMem (show t ∉ Iio (N : ℝ) from htN)]
    have : {x | t < (min (F x) N).toReal} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, ENNReal.lt_toReal_min_natCast_iff ht, htN, and_false,
        mem_empty_iff_false]
    rw [this, measure_empty, zero_mul]

/-- The **layer cake formula** for `[0, ∞]`-valued functions:
`∫ F^p dν = p ∫_0^∞ ν{F > t} t^(p-1) dt` for every measure `ν`, every almost everywhere
measurable `F : α → [0, ∞]` and `p > 0`. The truncations `min(F, N)` reduce it to Mathlib's
real-valued `lintegral_rpow_eq_lintegral_meas_lt_mul`, and both sides pass to the limit
`N → ∞` by monotone convergence. -/
theorem lintegral_rpow_eq_lintegral_meas_lt_mul_ennreal (ν : Measure α) {F : α → ℝ≥0∞}
    (hF : AEMeasurable F ν) {p : ℝ} (hp : 0 < p) :
    ∫⁻ x, F x ^ p ∂ν = ENNReal.ofReal p *
      ∫⁻ t in Ioi (0 : ℝ), ν {x | ENNReal.ofReal t < F x} * ENNReal.ofReal (t ^ (p - 1)) := by
  have hL : ∫⁻ x, F x ^ p ∂ν = ⨆ N : ℕ, ∫⁻ x, min (F x) N ^ p ∂ν := by
    rw [← lintegral_iSup' (fun N => (hF.min aemeasurable_const).pow_const p)
      (ae_of_all _ fun x N M hNM => ENNReal.rpow_le_rpow
        (min_le_min_left _ (Nat.cast_le.2 hNM)) hp.le)]
    simp_rw [ENNReal.iSup_min_natCast_rpow _ hp]
  have hU : Ioi (0 : ℝ) = ⋃ N : ℕ, Ioo (0 : ℝ) N := by
    ext t
    simp only [mem_Ioi, mem_iUnion, mem_Ioo]
    exact ⟨fun ht => ⟨⌈t⌉₊ + 1, ht, (Nat.le_ceil t).trans_lt (by push_cast; linarith)⟩,
      fun ⟨_, ht, _⟩ => ht⟩
  have hmono : Monotone fun N : ℕ => Ioo (0 : ℝ) N := fun N M hNM =>
    Ioo_subset_Ioo_right (Nat.cast_le.2 hNM)
  rw [hL, hU, setLIntegral_iUnion_of_directed _ hmono.directed_le, ENNReal.mul_iSup]
  simp_rw [lintegral_min_natCast_rpow_eq ν hF _ hp]

/-! ### Integrals of powers -/

/-- `∫_{(0,b)} t^r dt = b^(r+1)/(r+1)` in `[0, ∞]`, for `b ≥ 0` and `r > -1`. -/
theorem lintegral_Ioo_rpow {r : ℝ} (hr : -1 < r) {b : ℝ} (hb : 0 ≤ b) :
    ∫⁻ t in Ioo (0 : ℝ) b, ENNReal.ofReal (t ^ r) =
      ENNReal.ofReal b ^ (r + 1) / ENNReal.ofReal (r + 1) := by
  have hint : IntegrableOn (fun t : ℝ => t ^ r) (Ioc 0 b) :=
    (intervalIntegral.intervalIntegrable_rpow' hr).1
  rw [setLIntegral_congr Ioo_ae_eq_Ioc, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => Real.rpow_nonneg ht.1.le r),
    ← intervalIntegral.integral_of_le hb, integral_rpow (Or.inl hr),
    Real.zero_rpow (by linarith), sub_zero, ENNReal.ofReal_div_of_pos (by linarith),
    ENNReal.ofReal_rpow_of_nonneg hb (by linarith)]

/-- `∫_{(0,∞)} t^r dt = ∞` for every exponent `r`, since `t^r` is not integrable on `(0, ∞)`
(Mathlib's `not_integrableOn_Ioi_rpow`). -/
theorem lintegral_Ioi_rpow_eq_top (r : ℝ) :
    ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ r) = ∞ := by
  by_contra h
  exact not_integrableOn_Ioi_rpow r ((lintegral_ofReal_ne_top_iff_integrable
    (measurable_id.pow_const r).aestronglyMeasurable
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => Real.rpow_nonneg (le_of_lt ht) r)).1 h)

/-- `∫_0^∞ 1_{t < a} t^r dt = a^(r+1)/(r+1)` for every `a ∈ [0, ∞]` and `r > -1`. -/
theorem lintegral_Ioi_rpow_indicator_lt {r : ℝ} (hr : -1 < r) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), {t | ENNReal.ofReal t < a}.indicator (fun t => ENNReal.ofReal (t ^ r)) t
      = a ^ (r + 1) / ENNReal.ofReal (r + 1) := by
  have hm : MeasurableSet {t : ℝ | ENNReal.ofReal t < a} :=
    measurableSet_lt ENNReal.measurable_ofReal measurable_const
  rw [lintegral_indicator hm, Measure.restrict_restrict hm]
  rcases eq_or_ne a ∞ with rfl | ha
  · have hS : {t : ℝ | ENNReal.ofReal t < ∞} ∩ Ioi 0 = Ioi 0 := by
      ext t; simp [ENNReal.ofReal_lt_top]
    rw [hS, lintegral_Ioi_rpow_eq_top, ENNReal.top_rpow_of_pos (by linarith),
      ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
  · have hS : {t : ℝ | ENNReal.ofReal t < a} ∩ Ioi 0 = Ioo 0 a.toReal := by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, (ENNReal.ofReal_lt_iff_lt_toReal h2.le ha).1 h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal h1.le ha).2 h2, h1⟩
    rw [hS, lintegral_Ioo_rpow hr ENNReal.toReal_nonneg, ENNReal.ofReal_toReal ha]

/-- `∫_0^∞ 1_{t ≥ a} t^r dt = a^(r+1)/(-(r+1))` for every `a ∈ [0, ∞]` and `r < -1`, with
`0^(r+1) = ∞` and `∞^(r+1) = 0`. -/
theorem lintegral_Ioi_rpow_indicator_ge {r : ℝ} (hr : r < -1) (a : ℝ≥0∞) :
    ∫⁻ t in Ioi (0 : ℝ), {t | a ≤ ENNReal.ofReal t}.indicator (fun t => ENNReal.ofReal (t ^ r)) t
      = a ^ (r + 1) / ENNReal.ofReal (-(r + 1)) := by
  have hm : MeasurableSet {t : ℝ | a ≤ ENNReal.ofReal t} :=
    measurableSet_le measurable_const ENNReal.measurable_ofReal
  rw [lintegral_indicator hm, Measure.restrict_restrict hm]
  rcases eq_or_ne a 0 with rfl | ha
  · have hS : {t : ℝ | (0 : ℝ≥0∞) ≤ ENNReal.ofReal t} ∩ Ioi 0 = Ioi 0 := by
      ext t; simp
    rw [hS, lintegral_Ioi_rpow_eq_top, ENNReal.zero_rpow_of_neg (by linarith),
      ENNReal.top_div_of_ne_top ENNReal.ofReal_ne_top]
  rcases eq_or_ne a ∞ with rfl | hat
  · have hS : {t : ℝ | ∞ ≤ ENNReal.ofReal t} ∩ Ioi 0 = ∅ := by
      ext t; simp [ENNReal.ofReal_ne_top]
    rw [hS, Measure.restrict_empty, lintegral_zero_measure, ENNReal.top_rpow_of_neg (by linarith),
      ENNReal.zero_div]
  have ha0 : 0 < a.toReal := ENNReal.toReal_pos ha hat
  have hS : {t : ℝ | a ≤ ENNReal.ofReal t} ∩ Ioi 0 = Ici a.toReal := by
    ext t
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ici]
    constructor
    · rintro ⟨h1, h2⟩
      exact (ENNReal.le_ofReal_iff_toReal_le hat h2.le).1 h1
    · intro h
      exact ⟨(ENNReal.le_ofReal_iff_toReal_le hat (ha0.trans_le h).le).2 h, ha0.trans_le h⟩
  have hint : IntegrableOn (fun t : ℝ => t ^ r) (Ioi a.toReal) := integrableOn_Ioi_rpow_of_lt hr ha0
  rw [hS, setLIntegral_congr Ioi_ae_eq_Ici.symm, ← ofReal_integral_eq_lintegral_ofReal hint
    (ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => Real.rpow_nonneg (ha0.trans ht).le r),
    integral_Ioi_rpow_of_lt hr ha0, neg_div, ← div_neg, ENNReal.ofReal_div_of_pos (by linarith),
    ← ENNReal.ofReal_rpow_of_pos ha0, ENNReal.ofReal_toReal hat]

/-- **A power integral below half a level**: for `a, b ∈ [0, ∞]` and `p > 1`,
`∫_0^∞ 1_{t/2 < a} a b t^(p-2) dt = 2^(p-1)/(p-1) a^p b`, by
`MeasureTheory.lintegral_Ioi_rpow_indicator_lt` at the level `2a`. It is the integral in `t` of
the Tonelli step of the weighted strong type of the maximal function. -/
theorem lintegral_Ioi_indicator_half_lt_mul_rpow (a b : ℝ≥0∞) {p : ℝ} (hp : 1 < p) :
    ∫⁻ t in Ioi (0 : ℝ), {t : ℝ | ENNReal.ofReal t / 2 < a}.indicator (fun _ => a * b) t *
        ENNReal.ofReal (t ^ (p - 2)) =
      2 ^ (p - 1) / ENNReal.ofReal (p - 1) * (a ^ p * b) := by
  have hpt : ∀ t : ℝ, {t : ℝ | ENNReal.ofReal t / 2 < a}.indicator (fun _ => a * b) t *
      ENNReal.ofReal (t ^ (p - 2)) = a * b *
      {t : ℝ | ENNReal.ofReal t < 2 * a}.indicator (fun t => ENNReal.ofReal (t ^ (p - 2))) t :=
      fun t => by
    have hiff : ENNReal.ofReal t / 2 < a ↔ ENNReal.ofReal t < 2 * a := by
      rw [ENNReal.div_lt_iff (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top), mul_comm]
    by_cases ht : ENNReal.ofReal t / 2 < a
    · rw [Set.indicator_of_mem (show t ∈ {t : ℝ | ENNReal.ofReal t / 2 < a} from ht),
        Set.indicator_of_mem (show t ∈ {t : ℝ | ENNReal.ofReal t < 2 * a} from hiff.1 ht)]
    · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | ENNReal.ofReal t / 2 < a} from ht),
        Set.indicator_of_notMem (show t ∉ {t : ℝ | ENNReal.ofReal t < 2 * a} from
          fun h => ht (hiff.2 h)), zero_mul, mul_zero]
  have hm : Measurable fun t : ℝ =>
      {t : ℝ | ENNReal.ofReal t < 2 * a}.indicator (fun t => ENNReal.ofReal (t ^ (p - 2))) t :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).indicator
      (measurableSet_lt ENNReal.measurable_ofReal measurable_const)
  simp_rw [hpt]
  rw [lintegral_const_mul _ hm, lintegral_Ioi_rpow_indicator_lt (by linarith),
    show p - 2 + 1 = p - 1 by ring, ENNReal.mul_rpow_of_nonneg _ _ (by linarith),
    show a ^ p = a ^ ((1 : ℝ) + (p - 1)) by rw [add_sub_cancel],
    ENNReal.rpow_add_of_nonneg _ _ zero_le_one (by linarith), ENNReal.rpow_one,
    div_eq_mul_inv, div_eq_mul_inv]
  ring

end MeasureTheory
