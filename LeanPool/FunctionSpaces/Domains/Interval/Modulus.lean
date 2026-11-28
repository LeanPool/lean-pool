/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.Differences
public import LeanPool.FunctionSpaces.Analysis.Differences.DomainModuli
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The modulus of smoothness on an interval

For `f : ℝ → ℂ`, `1 ≤ p ≤ ∞` and an interval `[a, b]`, the **modulus of smoothness of order `r`**
is the modulus on the set `[a, b]` of `Rd.modulusOn` (`Interval.modulus`),

`ω_r(f, t, [a, b])_p = sup_{|h| ≤ t} ‖Δ_h^r(f, ·, [a, b])‖_p
  = sup_{0 ≤ h ≤ t} ‖Δ_h^r f‖_{L_p[a, b - r h]}`   (`Interval.modulus_eq_iSup_nonneg`):

the differences are taken only where all points `x, x + h, …, x + r h` lie in `[a, b]`, and the
steps `h` and `-h` give the same norm.  It
increases in `t`, is subadditive and homogeneous in `f`, satisfies
`ω_r(f, t) ≤ 2^r ‖f‖_{L_p[a,b]}`, vanishes on polynomials of degree `< r`, depends only on
the class of `f` in `L_p[a, b]` (`Interval.modulus_congr_ae`) and is invariant under the
reflection `x ↦ a + b - x` (`Interval.modulus_reflect`).

The same formula defines the modulus for `0 < p < 1`. For `0 < p ≤ 1` the `p`-th power of the
modulus is subadditive and `ω_r(f, t) ≤ 2^(r/p) ‖f‖_{L_p[a,b]}` (`Interval.modulus_add_rpow_le`,
`Interval.modulus_le_of_le_one`), since the `p`-th power of the `L_p` quasi-norm is subadditive.

All norms are `eLpNorm` on the restriction of Lebesgue measure; the functions are measurable
functions on `ℝ`, as the representatives of elements of `L_p` are.
-/

@[expose] public section

open MeasureTheory Set
open Rd (higherDiff measurable_higherDiff)
open scoped ENNReal

namespace Interval

/-- Translation: `‖f(· + c)‖_{L_p[u,v]} = ‖f‖_{L_p[u+c, v+c]}`. -/
theorem eLpNorm_comp_add_Icc {f : ℝ → ℂ} (hf : Measurable f) (p : ℝ≥0∞) (c u v : ℝ) :
    eLpNorm (fun x => f (x + c)) p (volume.restrict (Icc u v)) =
      eLpNorm f p (volume.restrict (Icc (u + c) (v + c))) := by
  have hpre : (fun x => x + c) ⁻¹' Icc (u + c) (v + c) = Icc u v := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hmp : MeasurePreserving (· + c) (volume.restrict (Icc u v))
      (volume.restrict (Icc (u + c) (v + c))) := by
    have := (measurePreserving_add_right volume c).restrict_preimage
      (measurableSet_Icc (a := u + c) (b := v + c))
    rwa [hpre] at this
  exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hmp

/-- Reflection: `‖f(c - ·)‖_{L_p[u,v]} = ‖f‖_{L_p[c-v, c-u]}`. -/
theorem eLpNorm_comp_sub_Icc {f : ℝ → ℂ} (hf : Measurable f) (p : ℝ≥0∞) (c u v : ℝ) :
    eLpNorm (fun x => f (c - x)) p (volume.restrict (Icc u v)) =
      eLpNorm f p (volume.restrict (Icc (c - v) (c - u))) := by
  have hpre : (fun x => c - x) ⁻¹' Icc (c - v) (c - u) = Icc u v := by
    ext x
    simp only [mem_preimage, mem_Icc]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have hmp : MeasurePreserving (fun x => c - x) (volume.restrict (Icc u v))
      (volume.restrict (Icc (c - v) (c - u))) := by
    have := (volume.measurePreserving_sub_left c).restrict_preimage
      (measurableSet_Icc (a := c - v) (b := c - u))
    rwa [hpre] at this
  exact eLpNorm_comp_measurePreserving hf.aestronglyMeasurable hmp

/-- `L_p` norms increase with the interval. -/
theorem eLpNorm_Icc_mono (f : ℝ → ℂ) (p : ℝ≥0∞) {u v u' v' : ℝ} (hu : u' ≤ u) (hv : v ≤ v') :
    eLpNorm f p (volume.restrict (Icc u v)) ≤ eLpNorm f p (volume.restrict (Icc u' v')) :=
  eLpNorm_mono_measure _ (Measure.restrict_mono (Icc_subset_Icc hu hv) le_rfl)

/-- Splitting `[a, c]` at `b`: `‖G‖_{L_p[a,c]} ≤ ‖G‖_{L_p[a,b]} + ‖G‖_{L_p[b,c]}`. -/
theorem eLpNorm_Icc_split {G : ℝ → ℂ} (hG : Measurable G) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hp' : p ≠ ∞) {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    eLpNorm G p (volume.restrict (Icc a c)) ≤
      eLpNorm G p (volume.restrict (Icc a b)) + eLpNorm G p (volume.restrict (Icc b c)) := by
  have hp0 : p ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
  have hq1 : 1 ≤ p.toReal := ENNReal.one_le_toReal_of_one_le hp hp'
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp' hG.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp' hG.aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp' hG.aestronglyMeasurable,
    ← Icc_union_Icc_eq_Icc hab hbc]
  refine le_trans (ENNReal.rpow_le_rpow (lintegral_union_le _ _ _) (by positivity)) ?_
  have := ENNReal.rpow_add_rpow_le_add
    ((∫⁻ x in Icc a b, ‖G x‖ₑ ^ p.toReal) ^ (1 / p.toReal))
    ((∫⁻ x in Icc b c, ‖G x‖ₑ ^ p.toReal) ^ (1 / p.toReal)) hq1
  rwa [← ENNReal.rpow_mul, ← ENNReal.rpow_mul, one_div_mul_cancel (by linarith),
    ENNReal.rpow_one, ENNReal.rpow_one] at this

/-- **Differences in `L_p`**: if `‖f(· + k h)‖_{L_p(μ)} ≤ B` for `k ≤ r`, then
`‖Δ_h^r f‖_{L_p(μ)} ≤ 2^r B`, by the triangle inequality and `∑_k C(r, k) = 2^r`. -/
theorem eLpNorm_higherDiff_le_of_forall {f : ℝ → ℂ} {p : ℝ≥0∞} (hp : 1 ≤ p) {μ : Measure ℝ}
    {r : ℕ} {h : ℝ} {B : ℝ≥0∞}
    (hB : ∀ k ∈ Finset.range (r + 1), eLpNorm (fun x => f (x + k * h)) p μ ≤ B) :
    eLpNorm (higherDiff r h f) p μ ≤ 2 ^ r * B := by
  rw [higherDiff_eq_sum_smul]
  refine (eLpNorm_sum_le hp).trans ?_
  calc ∑ k ∈ Finset.range (r + 1),
        eLpNorm (((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) • fun x => f (x + k * h)) p μ
      ≤ ∑ k ∈ Finset.range (r + 1), (r.choose k : ℝ≥0∞) * B :=
        Finset.sum_le_sum fun k hk => by
          rw [eLpNorm_const_smul, enorm_higherDiff_coeff]
          exact mul_le_mul_right (hB k hk) _
    _ = 2 ^ r * B := by
        rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
        push_cast
        rfl

/-- **Differences in `L_p`, `0 < p ≤ 1`**: if `‖f(· + k h)‖_{L_p(μ)} ≤ B` for `k ≤ r`, then
`‖Δ_h^r f‖_{L_p(μ)} ≤ 2^(r/p) B`. The `p`-th power of the quasi-norm is subadditive
(`MeasureTheory.eLpNorm_add_rpow_le_of_le_one`), `C(r, k)^p ≤ C(r, k)` and `∑_k C(r, k) = 2^r`. -/
theorem eLpNorm_higherDiff_le_of_forall_of_le_one {f : ℝ → ℂ} {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp1 : p ≤ 1) {μ : Measure ℝ} {r : ℕ} {h : ℝ} {B : ℝ≥0∞}
    (hB : ∀ k ∈ Finset.range (r + 1), eLpNorm (fun x => f (x + k * h)) p μ ≤ B) :
    eLpNorm (higherDiff r h f) p μ ≤ 2 ^ ((r : ℝ) / p.toReal) * B := by
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 (ne_top_of_le_ne_top ENNReal.one_ne_top hp1)
  have hq1 : p.toReal ≤ 1 := ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using hp1)
  have hterm : ∀ k ∈ Finset.range (r + 1), eLpNorm (((-1 : ℂ) ^ (r - k) * (r.choose k : ℂ)) •
      fun x => f (x + k * h)) p μ ^ p.toReal ≤ (r.choose k : ℝ≥0∞) * B ^ p.toReal := by
    intro k hk
    have h1 : (1 : ℝ≥0∞) ≤ r.choose k := by
      exact_mod_cast Nat.choose_pos (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))
    have hc : (r.choose k : ℝ≥0∞) ^ p.toReal ≤ r.choose k :=
      (ENNReal.rpow_le_rpow_of_exponent_le h1 hq1).trans_eq (ENNReal.rpow_one _)
    rw [eLpNorm_const_smul, enorm_higherDiff_coeff, ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    exact mul_le_mul' hc (ENNReal.rpow_le_rpow (hB k hk) hq.le)
  have hpow : eLpNorm (higherDiff r h f) p μ ^ p.toReal ≤
      (2 ^ ((r : ℝ) / p.toReal) * B) ^ p.toReal := by
    rw [higherDiff_eq_sum_smul, ENNReal.mul_rpow_of_nonneg _ _ hq.le, ← ENNReal.rpow_mul,
      div_mul_cancel₀ _ hq.ne', ENNReal.rpow_natCast]
    refine (Finset.le_sum_of_subadditive (fun g : ℝ → ℂ => eLpNorm g p μ ^ p.toReal)
      (by simp [ENNReal.zero_rpow_of_pos hq])
      (fun g g' => eLpNorm_add_rpow_le_of_le_one hp0 hp1 g g') _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans_eq ?_
    rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
    push_cast
    rfl
  exact (ENNReal.rpow_le_rpow_iff hq).1 hpow

/-- **Translates on a shorter interval**: for `h ≥ 0` and `k ≤ r`,
`‖f(· + k h)‖_{L_p[a, b - rh]} ≤ ‖f‖_{L_p[a, b]}`, since `[a, b - rh] + kh ⊆ [a, b]`. -/
theorem eLpNorm_comp_add_mul_le {f : ℝ → ℂ} (hf : Measurable f) (p : ℝ≥0∞) {k r : ℕ}
    (hkr : k ≤ r) {h : ℝ} (hh : 0 ≤ h) (a b : ℝ) :
    eLpNorm (fun x => f (x + k * h)) p (volume.restrict (Icc a (b - r * h))) ≤
      eLpNorm f p (volume.restrict (Icc a b)) := by
  have hkr' : (k : ℝ) ≤ r := by exact_mod_cast hkr
  rw [eLpNorm_comp_add_Icc hf]
  exact eLpNorm_Icc_mono f p (by nlinarith) (by nlinarith [mul_le_mul_of_nonneg_right hkr' hh])

/-- **`‖Δ_h^r f‖_{L_p[a, b - rh]} ≤ 2^r ‖f‖_{L_p[a,b]}`** for `h ≥ 0`. -/
theorem eLpNorm_higherDiff_le {f : ℝ → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (a b : ℝ) :
    eLpNorm (higherDiff r h f) p (volume.restrict (Icc a (b - r * h))) ≤
      2 ^ r * eLpNorm f p (volume.restrict (Icc a b)) :=
  eLpNorm_higherDiff_le_of_forall hp fun _ hk =>
    eLpNorm_comp_add_mul_le hf p (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hh a b

/-- **Differences in `L_p`, `p ≤ 1`, on an interval**: for measurable `f` and `h ≥ 0`,
`‖Δ_h^r f‖_{L_p[a, b - rh]} ≤ 2^(r/p) ‖f‖_{L_p[a, b]}`; at `p = 0` the left side is `0`. -/
theorem eLpNorm_higherDiff_le_of_le_one {f : ℝ → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp1 : p ≤ 1)
    (r : ℕ) {h : ℝ} (hh : 0 ≤ h) (a b : ℝ) :
    eLpNorm (higherDiff r h f) p (volume.restrict (Icc a (b - r * h))) ≤
      2 ^ ((r : ℝ) / p.toReal) * eLpNorm f p (volume.restrict (Icc a b)) := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [eLpNorm_exponent_zero (measurable_higherDiff hf r h).aestronglyMeasurable]
  exact eLpNorm_higherDiff_le_of_forall_of_le_one hp0 hp1 fun _ hk =>
    eLpNorm_comp_add_mul_le hf p (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hh a b

/-- For `h ≥ 0`, the points `x` with `x, x + h, …, x + rh ∈ [a, b]` form `[a, b - rh]`. -/
theorem stepSet_Icc_of_nonneg (r : ℕ) {h : ℝ} (hh : 0 ≤ h) (a b : ℝ) :
    Rd.stepSet (Icc a b) r h = Icc a (b - r * h) := by
  ext x
  simp only [Rd.stepSet, mem_ofPred_eq, mem_Icc, smul_eq_mul]
  constructor
  · intro hx
    exact ⟨by simpa using (hx 0 (Nat.zero_le r)).1, by linarith [(hx r le_rfl).2]⟩
  · rintro ⟨hax, hxb⟩ l hl
    have hl' : (l : ℝ) * h ≤ r * h := mul_le_mul_of_nonneg_right (by exact_mod_cast hl) hh
    exact ⟨by linarith [mul_nonneg (Nat.cast_nonneg l) hh], by linarith⟩

/-- For `h ≥ 0`, the restricted difference on `[a, b]` has the norm of `Δ_h^r f` on
`[a, b - rh]`. -/
theorem eLpNorm_indicator_stepSet_Icc (r : ℕ) {h : ℝ} (hh : 0 ≤ h) (p : ℝ≥0∞) (a b : ℝ)
    (f : ℝ → ℂ) :
    eLpNorm ((Rd.stepSet (Icc a b) r h).indicator ((fwdDiff h)^[r] f)) p volume =
      eLpNorm (higherDiff r h f) p (volume.restrict (Icc a (b - r * h))) := by
  rw [stepSet_Icc_of_nonneg r hh,
    eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Icc.nullMeasurableSet]
  rfl

/-- The **modulus of smoothness of order `r`** on `[a, b]` in `L_p`, the modulus on the set
`[a, b]` (`Rd.modulusOn`): `ω_r(f, t, [a, b])_p = sup_{|h| ≤ t} ‖Δ_h^r(f, ·, [a, b])‖_p`, with the
differences taken at the points `x` with `x, x + h, …, x + r h ∈ [a, b]`. -/
noncomputable def modulus (r : ℕ) (p : ℝ≥0∞) (a b : ℝ) (f : ℝ → ℂ) (t : ℝ) : ℝ≥0∞ :=
  Rd.modulusOn volume (Icc a b) r p f t

/-- `‖Δ_h^r f‖_{L_p[a, b - rh]} ≤ ω_r(f, t)` for `0 ≤ h ≤ t`. -/
theorem eLpNorm_higherDiff_le_modulus {r : ℕ} {p : ℝ≥0∞} {a b : ℝ} {f : ℝ → ℂ} {t h : ℝ}
    (hh : h ∈ Icc 0 t) :
    eLpNorm (higherDiff r h f) p (volume.restrict (Icc a (b - r * h))) ≤ modulus r p a b f t := by
  rw [← eLpNorm_indicator_stepSet_Icc r hh.1]
  exact Rd.eLpNorm_indicator_higherDiff_le_modulusOn (by rw [Real.norm_of_nonneg hh.1]; exact hh.2)

/-- **The modulus on an interval through steps `h ≥ 0`**:
`ω_r(f, t, [a, b])_p = sup_{0 ≤ h ≤ t} ‖Δ_h^r f‖_{L_p[a, b - rh]}`, since the step `-h` gives the
norm of the step `h` (`Rd.eLpNorm_indicator_stepSet_neg`). -/
theorem modulus_eq_iSup_nonneg (r : ℕ) (p : ℝ≥0∞) (a b : ℝ) (f : ℝ → ℂ) (t : ℝ) :
    modulus r p a b f t = ⨆ (h : ℝ) (_ : h ∈ Icc 0 t),
      eLpNorm (higherDiff r h f) p (volume.restrict (Icc a (b - r * h))) := by
  refine le_antisymm (iSup₂_le fun h hh => ?_)
    (iSup₂_le fun h hh => eLpNorm_higherDiff_le_modulus hh)
  rcases le_or_gt 0 h with h0 | h0
  · rw [eLpNorm_indicator_stepSet_Icc r h0]
    exact le_iSup₂_of_le h ⟨h0, by rwa [Real.norm_of_nonneg h0] at hh⟩ le_rfl
  · obtain ⟨s, rfl⟩ : ∃ s, h = -s := ⟨-h, (neg_neg h).symm⟩
    have hs : 0 ≤ s := by linarith
    rw [Rd.eLpNorm_indicator_stepSet_neg, eLpNorm_indicator_stepSet_Icc r hs]
    exact le_iSup₂_of_le s ⟨hs, by rwa [norm_neg, Real.norm_of_nonneg hs] at hh⟩ le_rfl

/-- The modulus increases in `t`. -/
theorem modulus_mono (r : ℕ) (p : ℝ≥0∞) (a b : ℝ) (f : ℝ → ℂ) : Monotone (modulus r p a b f) :=
  Rd.modulusOn_mono _ r p f

/-- `ω_r(f, t) ≤ 2^r ‖f‖_{L_p[a,b]}`. -/
theorem modulus_le {f : ℝ → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (a b t : ℝ) :
    modulus r p a b f t ≤ 2 ^ r * eLpNorm f p (volume.restrict (Icc a b)) := by
  rw [modulus_eq_iSup_nonneg]
  exact iSup₂_le fun _ hh => eLpNorm_higherDiff_le hf hp r hh.1 a b

/-- **The modulus is bounded by the quasi-norm for `0 < p ≤ 1`**:
`ω_r(f, t, [a, b])_p ≤ 2^(r/p) ‖f‖_{L_p[a, b]}`. -/
theorem modulus_le_of_le_one {f : ℝ → ℂ} (hf : Measurable f) {p : ℝ≥0∞} (hp1 : p ≤ 1) (r : ℕ)
    (a b t : ℝ) :
    modulus r p a b f t ≤ 2 ^ ((r : ℝ) / p.toReal) * eLpNorm f p (volume.restrict (Icc a b)) := by
  rw [modulus_eq_iSup_nonneg]
  exact iSup₂_le fun _ hh => eLpNorm_higherDiff_le_of_le_one hf hp1 r hh.1 a b

/-- The modulus is subadditive. -/
theorem modulus_add_le {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (a b : ℝ) (f g : ℝ → ℂ) (t : ℝ) :
    modulus r p a b (f + g) t ≤ modulus r p a b f t + modulus r p a b g t :=
  Rd.modulusOn_add_le hp _ r f g t

/-- **The `p`-th power of the modulus is subadditive for `0 < p ≤ 1`**:
`ω_r(f + g, t, [a, b])_p^p ≤ ω_r(f, t, [a, b])_p^p + ω_r(g, t, [a, b])_p^p`, from the same
inequality for the `L_p` quasi-norm of each difference
(`MeasureTheory.eLpNorm_add_rpow_le_of_le_one`). -/
theorem modulus_add_rpow_le {p : ℝ≥0∞} (hp1 : p ≤ 1) (r : ℕ) (a b : ℝ) (f g : ℝ → ℂ) (t : ℝ) :
    modulus r p a b (f + g) t ^ p.toReal ≤
      modulus r p a b f t ^ p.toReal + modulus r p a b g t ^ p.toReal := by
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [ENNReal.toReal_zero, ENNReal.rpow_zero]
    exact le_self_add
  have hq : 0 < p.toReal := ENNReal.toReal_pos hp0 (ne_top_of_le_ne_top ENNReal.one_ne_top hp1)
  set M := modulus r p a b f t ^ p.toReal + modulus r p a b g t ^ p.toReal
  have key : modulus r p a b (f + g) t ≤ M ^ (1 / p.toReal) := by
    refine iSup₂_le fun h hh => ?_
    rw [fwdDiff_iter_add, Set.indicator_add', ← ENNReal.rpow_le_rpow_iff hq, ← ENNReal.rpow_mul,
      one_div_mul_cancel hq.ne', ENNReal.rpow_one]
    exact (eLpNorm_add_rpow_le_of_le_one hp0 hp1 _ _).trans (add_le_add
      (ENNReal.rpow_le_rpow (Rd.eLpNorm_indicator_higherDiff_le_modulusOn hh) hq.le)
      (ENNReal.rpow_le_rpow (Rd.eLpNorm_indicator_higherDiff_le_modulusOn hh) hq.le))
  calc modulus r p a b (f + g) t ^ p.toReal ≤ (M ^ (1 / p.toReal)) ^ p.toReal :=
        ENNReal.rpow_le_rpow key hq.le
    _ = M := by rw [← ENNReal.rpow_mul, one_div_mul_cancel hq.ne', ENNReal.rpow_one]

/-- The modulus is homogeneous. -/
theorem modulus_const_mul (r : ℕ) (p : ℝ≥0∞) (a b : ℝ) (c : ℂ) (f : ℝ → ℂ) (t : ℝ) :
    modulus r p a b (fun x => c * f x) t = ‖c‖ₑ * modulus r p a b f t := by
  simp only [modulus_eq_iSup_nonneg, higherDiff_const_mul, ENNReal.mul_iSup]
  congr 1
  funext h
  congr 1
  funext _
  exact eLpNorm_const_smul c (higherDiff r h f) p _

/-- The modulus vanishes on polynomials of degree `< r`. -/
theorem modulus_polynomial {r : ℕ} {P : Polynomial ℂ} (hP : P ∈ Polynomial.degreeLT ℂ r)
    (p : ℝ≥0∞) (a b t : ℝ) : modulus r p a b (fun x => P.eval (x : ℂ)) t = 0 := by
  simp [modulus_eq_iSup_nonneg, higherDiff_polynomial hP]

/-- **The line has vanishing second modulus**: `ω_2(x ↦ x, t, [0, 1])_p = 0` for every `p` and
`t` (`Interval.modulus_polynomial` with `P = X`, of degree `1 < 2`). -/
theorem modulus_two_id (p : ℝ≥0∞) (t : ℝ) : modulus 2 p 0 1 (fun x => (x : ℂ)) t = 0 := by
  simpa using modulus_polynomial (P := Polynomial.X)
    (Polynomial.mem_degreeLT.2 (Polynomial.degree_X_le.trans_lt (by exact_mod_cast one_lt_two)))
    p 0 1 t

/-- **Differences depend only on the class in `L_p[a, b]`**: for `h ≥ 0`, functions that agree
almost everywhere on `[a, b]` have differences of step `h` with the same `L_p` norm on
`[a, b - rh]`: the norm is that of `Δ_h^r (1_{[a,b]} f)` on the step set
(`Interval.eLpNorm_indicator_stepSet_Icc`, `Rd.indicator_stepSet_higherDiff_indicator`), and the
differences of `1_{[a,b]} f = 1_{[a,b]} g` agree almost everywhere (`Rd.higherDiff_congr_ae`). -/
theorem eLpNorm_higherDiff_congr_ae {f g : ℝ → ℂ} {a b : ℝ}
    (hfg : f =ᵐ[volume.restrict (Icc a b)] g) (r : ℕ) (p : ℝ≥0∞) {h : ℝ} (hh : 0 ≤ h) :
    eLpNorm (higherDiff r h f) p (volume.restrict (Icc a (b - r * h))) =
      eLpNorm (higherDiff r h g) p (volume.restrict (Icc a (b - r * h))) := by
  rw [← eLpNorm_indicator_stepSet_Icc r hh p a b f, ← eLpNorm_indicator_stepSet_Icc r hh p a b g,
    ← Rd.indicator_stepSet_higherDiff_indicator (Icc a b) r h f,
    ← Rd.indicator_stepSet_higherDiff_indicator (Icc a b) r h g]
  rw [ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc] at hfg
  refine eLpNorm_congr_ae ?_
  filter_upwards [Rd.higherDiff_congr_ae hfg r h] with x hx
  by_cases hxU : x ∈ Rd.stepSet (Icc a b) r h
  · rw [Set.indicator_of_mem hxU, Set.indicator_of_mem hxU, hx]
  · rw [Set.indicator_of_notMem hxU, Set.indicator_of_notMem hxU]

/-- **The modulus depends only on the class in `L_p[a, b]`**: functions that agree almost
everywhere on `[a, b]` have the same modulus. -/
theorem modulus_congr_ae {f g : ℝ → ℂ} {a b : ℝ} (hfg : f =ᵐ[volume.restrict (Icc a b)] g)
    (r : ℕ) (p : ℝ≥0∞) (t : ℝ) :
    modulus r p a b f t = modulus r p a b g t := by
  rw [ae_eq_restrict_iff_indicator_ae_eq measurableSet_Icc] at hfg
  exact Rd.modulusOn_congr_ae hfg r p t

/-- **Reflection of a difference**:
`‖Δ_h^r f(a + b - ·)‖_{L_p[a, b - rh]} = ‖Δ_h^r f‖_{L_p[a, b - rh]}`, since
`Δ_h^r f(a + b - ·)(x) = (-1)^r Δ_h^r f(a + b - rh - x)`. -/
theorem eLpNorm_higherDiff_reflect {f : ℝ → ℂ} (hf : Measurable f) (r : ℕ) (p : ℝ≥0∞)
    (a b h : ℝ) :
    eLpNorm (higherDiff r h fun x => f (a + b - x)) p (volume.restrict (Icc a (b - r * h))) =
      eLpNorm (higherDiff r h f) p (volume.restrict (Icc a (b - r * h))) := by
  have hfun : higherDiff r h (fun x => f (a + b - x)) =
      fun x => (-1 : ℂ) ^ r * higherDiff r h f (a + b - r * h - x) := by
    funext x
    rw [higherDiff_reflect]
    congr 2
    ring
  rw [hfun, show (fun x => (-1 : ℂ) ^ r * higherDiff r h f (a + b - r * h - x)) =
      ((-1 : ℂ) ^ r) • fun x => higherDiff r h f (a + b - r * h - x) from rfl, eLpNorm_const_smul,
    eLpNorm_comp_sub_Icc (measurable_higherDiff hf r h)]
  simp only [eNorm_pow, eNorm_neg, eNorm_one, one_pow, one_mul]
  congr 3 <;> ring

/-- **Reflection**: `ω_r(f(a + b - ·), t, [a, b]) = ω_r(f, t, [a, b])`. -/
theorem modulus_reflect {f : ℝ → ℂ} (hf : Measurable f) (r : ℕ) (p : ℝ≥0∞) (a b t : ℝ) :
    modulus r p a b (fun x => f (a + b - x)) t = modulus r p a b f t := by
  simp only [modulus_eq_iSup_nonneg]
  congr 1
  funext h
  congr 1
  funext _
  exact eLpNorm_higherDiff_reflect hf r p a b h

end Interval
