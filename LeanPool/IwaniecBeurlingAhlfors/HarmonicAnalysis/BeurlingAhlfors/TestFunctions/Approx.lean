/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.TestFunctions.Profile
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Smooth approximations of Dragičević's test functions

The test function `f_{2,α} (z) = z² |z|^{−2α} g₂ (|z|)` is approximated by smooth compactly
supported functions, by the standard argument: regularise the singularity at `0`, smooth the
cutoff `g₂` at `1` (where it is only `C¹`), and truncate at infinity. With `t = |z|²`,
`ε_k = δ_k = 1/(k + 1)`, `R_k = k + 2`, `s = Real.smoothTransition` and
`E (t) = exp (−(√t − 1)²)` (`HarmonicAnalysis.BeurlingAhlfors.expCutoff`):

* `A_k (t) = (t + ε_k)^{−α}`, smooth on `t > −ε_k`;
* `G_k (t) = 1 + (E (t) − 1) s ((t − 1)/δ_k)` (`HarmonicAnalysis.BeurlingAhlfors.approxGlue`):
  `1` for `t ≤ 1`, `E (t)` for `t ≥ 1 + δ_k`, smooth;
* `χ_k (t) = s (2 − t/R_k)` (`HarmonicAnalysis.BeurlingAhlfors.approxTrunc`): `1` for `t ≤ R_k`,
  `0` for `t ≥ 2 R_k`;
* `K_k = A_k G_k χ_k` (`HarmonicAnalysis.BeurlingAhlfors.approxProfile`) and
  `φ_k (z) = z² K_k (|z|²)` (`HarmonicAnalysis.BeurlingAhlfors.approxFun`), a Schwartz function
  (`HarmonicAnalysis.BeurlingAhlfors.approxSchwartz`).

## Main results

* `HarmonicAnalysis.BeurlingAhlfors.dzCLM_sq_approxSchwartz_eq`,
  `HarmonicAnalysis.BeurlingAhlfors.dzbarCLM_sq_approxSchwartz_eq`: the derivative formulas
  `∂²φ_k = 2 K_k + 4 t K_k' + t² K_k''` and `∂_zbar²φ_k = z⁴ K_k''`, `t = |z|²`.
* `HarmonicAnalysis.BeurlingAhlfors.tendstoTwo_approxProfile_of_lt_one`,
  `HarmonicAnalysis.BeurlingAhlfors.tendstoTwo_approxProfile_of_one_lt`: the pointwise limits of
  `K_k` and its first two derivatives, `t^{−α}` on `(0, 1)` and `t^{−α} E (t)` on `(1, ∞)`.
* `HarmonicAnalysis.BeurlingAhlfors.norm_approxSchwartz_le_of_lt_one`,
  `HarmonicAnalysis.BeurlingAhlfors.exists_norm_approxSchwartz_le_of_one_lt`: the domination,
  uniform in `k`, by `8 |z|^{−2α}` on the punctured disc and by `C (1 + |z|²)² e^{−(|z| − 1)²}`
  outside it.
-/

@[expose] public section

noncomputable section

open Set Filter Topology
open scoped SchwartzMap ContDiff

namespace HarmonicAnalysis.BeurlingAhlfors

/-! ### The parameters -/

/-- `ε_k = δ_k = 1/(k + 1)`. -/
def approxEps (k : ℕ) : ℝ := 1 / (k + 1)

/-- `R_k = k + 2`. -/
def approxRadius (k : ℕ) : ℝ := k + 2

theorem approxEps_pos (k : ℕ) : 0 < approxEps k := by
  unfold approxEps; positivity

theorem approxEps_le_one (k : ℕ) : approxEps k ≤ 1 := by
  unfold approxEps
  rw [div_le_one (by positivity)]
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem tendsto_approxEps : Tendsto approxEps atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem two_le_approxRadius (k : ℕ) : 2 ≤ approxRadius k := by
  unfold approxRadius
  linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

theorem tendsto_approxRadius : Tendsto approxRadius atTop atTop :=
  tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop

/-! ### The one-variable factors -/

/-- `G_k (t) = 1 + (E (t) − 1) s ((t − 1)/δ_k)`: the cutoff `E`, smoothed at `t = 1`. -/
def approxGlue (k : ℕ) (t : ℝ) : ℝ :=
  1 + (expCutoff t - 1) * Real.smoothTransition ((t - 1) / approxEps k)

/-- `χ_k (t) = s (2 − t/R_k)`: the truncation at infinity. -/
def approxTrunc (k : ℕ) (t : ℝ) : ℝ := Real.smoothTransition (2 - t / approxRadius k)

/-- `K_k (t) = (t + ε_k)^{−α} G_k (t) χ_k (t)`. -/
def approxProfile (α : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (t + approxEps k) ^ (-α) * approxGlue k t * approxTrunc k t

/-- `G_k = 1` on `t ≤ 1`. -/
theorem approxGlue_eq_one (k : ℕ) {t : ℝ} (ht : t ≤ 1) : approxGlue k t = 1 := by
  rw [approxGlue, Real.smoothTransition.zero_of_nonpos
    (div_nonpos_of_nonpos_of_nonneg (by linarith) (approxEps_pos k).le), mul_zero, add_zero]

/-- `G_k = E` on `t ≥ 1 + δ_k`. -/
theorem approxGlue_eq_expCutoff (k : ℕ) {t : ℝ} (ht : 1 + approxEps k ≤ t) :
    approxGlue k t = expCutoff t := by
  rw [approxGlue, Real.smoothTransition.one_of_one_le
    ((le_div_iff₀ (approxEps_pos k)).2 (by linarith)), mul_one]
  ring

/-- `χ_k = 1` on `t ≤ R_k`. -/
theorem approxTrunc_eq_one (k : ℕ) {t : ℝ} (ht : t ≤ approxRadius k) : approxTrunc k t = 1 := by
  have hR : 0 < approxRadius k := by linarith [two_le_approxRadius k]
  exact Real.smoothTransition.one_of_one_le (by linarith [div_le_one_of_le₀ ht hR.le])

/-- `χ_k = 0` on `t ≥ 2 R_k`. -/
theorem approxTrunc_eq_zero (k : ℕ) {t : ℝ} (ht : 2 * approxRadius k ≤ t) :
    approxTrunc k t = 0 := by
  have hR : 0 < approxRadius k := by linarith [two_le_approxRadius k]
  exact Real.smoothTransition.zero_of_nonpos (by linarith [(le_div_iff₀ hR).2 ht])

theorem contDiff_approxGlue (k : ℕ) : ContDiff ℝ ∞ (approxGlue k) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_or_ge t 1 with ht | ht
  · refine (contDiffAt_const (c := (1 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht] with s hs using approxGlue_eq_one k hs.le
  · have hσ : ContDiffAt ℝ ∞ (fun s => Real.smoothTransition ((s - 1) / approxEps k)) t :=
      Real.smoothTransition.contDiffAt.comp t ((contDiffAt_id.sub contDiffAt_const).div_const _)
    exact contDiffAt_const.add
      (((contDiffAt_expCutoff (by linarith)).sub contDiffAt_const).mul hσ)

theorem contDiff_approxTrunc (k : ℕ) : ContDiff ℝ ∞ (approxTrunc k) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.div_const _))

theorem contDiffAt_rpow_add_neg (α c : ℝ) {t : ℝ} (ht : -c < t) :
    ContDiffAt ℝ ∞ (fun s : ℝ => (s + c) ^ (-α)) t :=
  (Real.contDiffAt_rpow_const_of_ne (x := t + c) (p := -α) (by linarith)).comp t
    (contDiffAt_id.add contDiffAt_const)

theorem contDiffAt_approxProfile (α : ℝ) (k : ℕ) {t : ℝ} (ht : -approxEps k < t) :
    ContDiffAt ℝ ∞ (approxProfile α k) t :=
  ((contDiffAt_rpow_add_neg α _ ht).mul (contDiff_approxGlue k).contDiffAt).mul
    (contDiff_approxTrunc k).contDiffAt

/-! ### The approximants -/

/-- `φ_k (z) = z² K_k (|z|²)`. -/
def approxFun (α : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  z ^ 2 * ((approxProfile α k (Complex.normSq z) : ℝ) : ℂ)

theorem contDiff_approxFun (α : ℝ) (k : ℕ) : ContDiff ℝ ∞ (approxFun α k) := by
  have hN : ContDiff ℝ ∞ Complex.normSq := by
    rw [show Complex.normSq = fun z : ℂ => ‖z‖ ^ 2 from funext Complex.normSq_eq_norm_sq]
    exact contDiff_norm_sq ℝ
  rw [contDiff_iff_contDiffAt]
  intro z
  have h1 : ContDiffAt ℝ ∞ (approxProfile α k) (Complex.normSq z) :=
    contDiffAt_approxProfile α k (by linarith [Complex.normSq_nonneg z, approxEps_pos k])
  have h2 : ContDiffAt ℝ ∞ (fun w => ((approxProfile α k (Complex.normSq w) : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (h1.comp z hN.contDiffAt)
  exact (contDiffAt_id.pow 2).mul h2

/-- `φ_k (z) = 0` for `|z|² ≥ 2 R_k`. -/
theorem approxFun_eq_zero (α : ℝ) (k : ℕ) {z : ℂ} (hz : 2 * approxRadius k ≤ Complex.normSq z) :
    approxFun α k z = 0 := by
  rw [approxFun, approxProfile, approxTrunc_eq_zero k hz]
  simp

theorem hasCompactSupport_approxFun (α : ℝ) (k : ℕ) : HasCompactSupport (approxFun α k) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * approxRadius k))
    fun z hz => approxFun_eq_zero α k ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  rw [Complex.normSq_eq_norm_sq]
  have := two_le_approxRadius k
  nlinarith

/-- `φ_k` as a Schwartz function. -/
def approxSchwartz (α : ℝ) (k : ℕ) : 𝓢(ℂ, ℂ) :=
  (hasCompactSupport_approxFun α k).toSchwartzMap (contDiff_approxFun α k)

theorem coe_approxSchwartz (α : ℝ) (k : ℕ) : ⇑(approxSchwartz α k) = approxFun α k := rfl

theorem dzCLM_sq_apply (f : 𝓢(ℂ, ℂ)) (z : ℂ) : (dzCLM ^ 2) f z = dz (dz f) z := by
  rw [coe_dzCLM_pow]
  rfl

theorem dzbarCLM_sq_apply (f : 𝓢(ℂ, ℂ)) (z : ℂ) : (dzbarCLM ^ 2) f z = dzbar (dzbar f) z := by
  rw [coe_dzbarCLM_pow]
  rfl

/-- `∂²φ_k` is the pointwise `∂²` of `z² K_k (|z|²)`. -/
theorem dzCLM_sq_approxSchwartz (α : ℝ) (k : ℕ) (z : ℂ) :
    (dzCLM ^ 2) (approxSchwartz α k) z =
      dz (dz (fun w => w ^ 2 * ((approxProfile α k (Complex.normSq w) : ℝ) : ℂ))) z := by
  rw [dzCLM_sq_apply, coe_approxSchwartz]
  rfl

/-- `∂_zbar²φ_k` is the pointwise `∂_zbar²` of `z² K_k (|z|²)`. -/
theorem dzbarCLM_sq_approxSchwartz (α : ℝ) (k : ℕ) (z : ℂ) :
    (dzbarCLM ^ 2) (approxSchwartz α k) z =
      dzbar (dzbar (fun w => w ^ 2 * ((approxProfile α k (Complex.normSq w) : ℝ) : ℂ))) z := by
  rw [dzbarCLM_sq_apply, coe_approxSchwartz]
  rfl

theorem contDiffAt_two_approxProfile (α : ℝ) (k : ℕ) (z : ℂ) :
    ContDiffAt ℝ 2 (approxProfile α k) (Complex.normSq z) :=
  (contDiffAt_approxProfile α k (by linarith [Complex.normSq_nonneg z, approxEps_pos k])).of_le
    (by norm_num)

/-- The derivative formula for `φ_k`: `∂²φ_k (z) = 2 K_k (t) + 4 t K_k' (t) + t² K_k'' (t)`,
`t = |z|²`. -/
theorem dzCLM_sq_approxSchwartz_eq (α : ℝ) (k : ℕ) (z : ℂ) :
    (dzCLM ^ 2) (approxSchwartz α k) z =
      ((2 * approxProfile α k (Complex.normSq z) +
          4 * Complex.normSq z * deriv (approxProfile α k) (Complex.normSq z) +
          Complex.normSq z ^ 2 * deriv (deriv (approxProfile α k)) (Complex.normSq z) : ℝ) :
        ℂ) := by
  rw [dzCLM_sq_approxSchwartz, dz_dz_sq_mul_ofReal_radial (contDiffAt_two_approxProfile α k z)]

/-- The derivative formula for `φ_k`: `∂_zbar²φ_k (z) = z⁴ K_k'' (|z|²)`. -/
theorem dzbarCLM_sq_approxSchwartz_eq (α : ℝ) (k : ℕ) (z : ℂ) :
    (dzbarCLM ^ 2) (approxSchwartz α k) z =
      z ^ 4 * ((deriv (deriv (approxProfile α k)) (Complex.normSq z) : ℝ) : ℂ) := by
  rw [dzbarCLM_sq_approxSchwartz,
    dzbar_dzbar_sq_mul_ofReal_radial (contDiffAt_two_approxProfile α k z)]

/-! ### The germs of `K_k` -/

/-- On `t < 1`, `K_k = A_k` near `t`. -/
theorem approxProfile_eventuallyEq_of_lt_one (α : ℝ) (k : ℕ) {t : ℝ} (ht : t < 1) :
    approxProfile α k =ᶠ[𝓝 t] fun s => (s + approxEps k) ^ (-α) := by
  filter_upwards [Iio_mem_nhds ht] with s hs
  rw [approxProfile, approxGlue_eq_one k hs.le,
    approxTrunc_eq_one k (by linarith [two_le_approxRadius k, mem_Iio.1 hs]), mul_one, mul_one]

/-- On `1 + δ_k < t < R_k`, `K_k = A_k E` near `t`. -/
theorem approxProfile_eventuallyEq_of_lt (α : ℝ) (k : ℕ) {t : ℝ} (h1 : 1 + approxEps k < t)
    (h2 : t < approxRadius k) :
    approxProfile α k =ᶠ[𝓝 t] fun s => (s + approxEps k) ^ (-α) * expCutoff s := by
  filter_upwards [Ioo_mem_nhds h1 h2] with s hs
  rw [approxProfile, approxGlue_eq_expCutoff k hs.1.le, approxTrunc_eq_one k hs.2.le, mul_one]

/-! ### Pointwise limits -/

/-- On `(0, 1)`, `K_k^{(j)} (t) → (t^{−α})^{(j)}`, `j ≤ 2`. -/
theorem tendstoTwo_approxProfile_of_lt_one (α : ℝ) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    TendstoTwo (approxProfile α) (fun s => s ^ (-α)) t :=
  (tendstoTwo_rpow_add_neg α ht0 tendsto_approxEps).congr
    (Eventually.of_forall fun k => approxProfile_eventuallyEq_of_lt_one α k ht1)

/-- On `(1, ∞)`, `K_k^{(j)} (t) → (t^{−α} E (t))^{(j)}`, `j ≤ 2`. -/
theorem tendstoTwo_approxProfile_of_one_lt (α : ℝ) {t : ℝ} (ht : 1 < t) :
    TendstoTwo (approxProfile α) (fun s => s ^ (-α) * expCutoff s) t := by
  have hA : ∀ k, ContDiffAt ℝ 2 (fun s : ℝ => (s + approxEps k) ^ (-α)) t := fun k =>
    (contDiffAt_rpow_add_neg α _ (by linarith [approxEps_pos k])).of_le (by norm_num)
  have h := (tendstoTwo_rpow_add_neg α (by linarith : (0 : ℝ) < t) tendsto_approxEps).mul_right
    hA (Real.contDiffAt_rpow_const_of_ne (by linarith)) (contDiffAt_expCutoff (by linarith))
  refine h.congr ?_
  have h1 : ∀ᶠ k in atTop, 1 + approxEps k < t :=
    (by simpa using tendsto_approxEps.const_add 1 : Tendsto (fun k => 1 + approxEps k) atTop
      (𝓝 1)).eventually_lt_const ht
  filter_upwards [h1, tendsto_approxRadius.eventually_gt_atTop t] with k hk1 hk2 using
    approxProfile_eventuallyEq_of_lt α k hk1 hk2

/-! ### Domination -/

/-- On `t < 1`, `K_k^{(j)} (t) = A_k^{(j)} (t)`, `j ≤ 2`, explicitly. -/
theorem approxProfile_jet_of_lt_one (α : ℝ) (k : ℕ) {t : ℝ} (ht : t < 1) :
    approxProfile α k t = (t + approxEps k) ^ (-α) ∧
      deriv (approxProfile α k) t = -α * (t + approxEps k) ^ (-α - 1) ∧
      deriv (deriv (approxProfile α k)) t = α * (α + 1) * (t + approxEps k) ^ (-α - 2) := by
  have h := approxProfile_eventuallyEq_of_lt_one α k ht
  refine ⟨h.self_of_nhds, ?_, ?_⟩
  · rw [h.deriv_eq, deriv_rpow_add_neg]
  · rw [h.deriv.deriv_eq, deriv_deriv_rpow_add_neg]

/-- On `(0, 1)`: `|2 K_k + 4 t K_k' + t² K_k''| ≤ 8 t^{−α}` and `t² |K_k''| ≤ 2 t^{−α}`, since
`t / (t + ε_k) ≤ 1` and `(t + ε_k)^{−α} ≤ t^{−α}`. -/
theorem abs_approxProfile_le_of_lt_one {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    |2 * approxProfile α k t + 4 * t * deriv (approxProfile α k) t +
        t ^ 2 * deriv (deriv (approxProfile α k)) t| ≤ 8 * t ^ (-α) ∧
      t ^ 2 * |deriv (deriv (approxProfile α k)) t| ≤ 2 * t ^ (-α) := by
  obtain ⟨h0, h1, h2⟩ := approxProfile_jet_of_lt_one α k ht1
  rw [h0, h1, h2]
  have hε := approxEps_pos k
  obtain ⟨s, hs_def⟩ : ∃ s, s = t + approxEps k := ⟨_, rfl⟩
  rw [← hs_def]
  have hs : 0 < s := by linarith
  have hts : t ≤ s := by linarith
  have hX0 : 0 < s ^ (-α) := Real.rpow_pos_of_pos hs _
  have hXt : s ^ (-α) ≤ t ^ (-α) := Real.rpow_le_rpow_of_nonpos ht0 hts (by linarith)
  have e1 : s ^ (-α - 1) = s ^ (-α) / s := Real.rpow_sub_one hs.ne' _
  have e2 : s ^ (-α - 2) = s ^ (-α) / s ^ 2 := by
    rw [Real.rpow_sub hs, Real.rpow_two]
  rw [e1, e2]
  obtain ⟨r, hr_def⟩ : ∃ r, r = t / s := ⟨_, rfl⟩
  have hr0 : 0 < r := hr_def ▸ div_pos ht0 hs
  have hr1 : r ≤ 1 := hr_def ▸ (div_le_one hs).2 hts
  have eq1 : 2 * s ^ (-α) + 4 * t * (-α * (s ^ (-α) / s)) +
      t ^ 2 * (α * (α + 1) * (s ^ (-α) / s ^ 2)) =
      s ^ (-α) * (2 - 4 * α * r + α * (α + 1) * r ^ 2) := by
    rw [hr_def]; field_simp; ring
  have eq2 : t ^ 2 * |α * (α + 1) * (s ^ (-α) / s ^ 2)| = s ^ (-α) * (α * (α + 1) * r ^ 2) := by
    rw [abs_of_nonneg (by positivity), hr_def]; field_simp
  rw [eq1, eq2, abs_mul, abs_of_pos hX0]
  have har : α * r ≤ 1 := by
    simpa using mul_le_mul hα1.le hr1 hr0.le (zero_le_one : (0 : ℝ) ≤ 1)
  have har2 : α * (α + 1) * r ^ 2 ≤ 2 := by
    have hr2 : r ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hr0.le hr1 2
    have hαplus : α + 1 ≤ 2 := by linarith only [hα1]
    have hαα : α * (α + 1) ≤ 2 := by
      simpa using mul_le_mul hα1.le hαplus
        (by positivity : 0 ≤ α + 1) (zero_le_one : (0 : ℝ) ≤ 1)
    simpa using mul_le_mul hαα hr2 (sq_nonneg r) (by norm_num : (0 : ℝ) ≤ 2)
  have har3 : 0 ≤ α * (α + 1) * r ^ 2 := by positivity
  have hP : |2 - 4 * α * r + α * (α + 1) * r ^ 2| ≤ 8 := by
    rw [abs_le]
    constructor <;> linarith only [har, har2, har3, mul_nonneg hα0.le hr0.le]
  constructor
  · calc _ ≤ t ^ (-α) * 8 := mul_le_mul hXt hP (abs_nonneg _) (Real.rpow_nonneg ht0.le _)
      _ = 8 * t ^ (-α) := mul_comm _ _
  · calc _ ≤ t ^ (-α) * 2 := mul_le_mul hXt har2 har3 (Real.rpow_nonneg ht0.le _)
      _ = 2 * t ^ (-α) := mul_comm _ _

/-- Near the unit circle, `1 ≤ t ≤ 1 + δ_k`: `|G_k|, |G_k'|, |G_k''| ≤ 2 + 3 S`, with `S` a bound
for `s`, `s'`, `s''` (`|E − 1| ≤ δ²`, `|E'| ≤ δ`, `|E''| ≤ 2`). -/
theorem derivBoundTwo_approxGlue_of_le {S : ℝ} (hS1 : 1 ≤ S)
    (hS : ∀ x, DerivBoundTwo Real.smoothTransition x S) (k : ℕ) {t : ℝ} (ht : 1 ≤ t)
    (htδ : t ≤ 1 + approxEps k) : DerivBoundTwo (approxGlue k) t (2 + 3 * S) := by
  obtain ⟨δ, hδ_def⟩ : ∃ δ, δ = approxEps k := ⟨_, rfl⟩
  have hδ : 0 < δ := hδ_def ▸ approxEps_pos k
  have hδ1 : δ ≤ 1 := hδ_def ▸ approxEps_le_one k
  rw [← hδ_def] at htδ
  set σ : ℝ → ℝ := fun s => Real.smoothTransition (δ⁻¹ * s + -δ⁻¹) with hσ_def
  have hG : approxGlue k = fun s => 1 + (expCutoff s - 1) * σ s := by
    funext s
    simp only [approxGlue, σ, ← hδ_def]
    congr 3
    rw [div_eq_inv_mul]
    ring
  have hE2 : ContDiffAt ℝ 2 (fun s => expCutoff s - 1) t :=
    (contDiffAt_expCutoff (by linarith)).sub contDiffAt_const
  have hσ2 : ContDiffAt ℝ 2 σ t :=
    (Real.smoothTransition.contDiff (n := 2)).contDiffAt.comp t
      ((contDiffAt_const.mul contDiffAt_id).add contDiffAt_const)
  have hd : deriv (approxGlue k) = deriv fun s => (expCutoff s - 1) * σ s := by
    rw [hG, deriv_const_add']
  have hd1 : deriv σ t = δ⁻¹ * deriv Real.smoothTransition (δ⁻¹ * t + -δ⁻¹) := by
    rw [hσ_def, deriv_comp_mul_add]
  have hd2 : deriv (deriv σ) t =
      δ⁻¹ ^ 2 * deriv (deriv Real.smoothTransition) (δ⁻¹ * t + -δ⁻¹) := by
    rw [hσ_def, deriv_deriv_comp_mul_add]
  have hσ0 : |σ t| ≤ 1 := by
    rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
  obtain ⟨-, hs1, hs2⟩ := hS (δ⁻¹ * t + -δ⁻¹)
  -- the bounds on `E − 1`, `E'`, `E''`
  have hE0 : |expCutoff t - 1| ≤ δ ^ 2 :=
    (abs_expCutoff_sub_one_le ht).trans (pow_le_pow_left₀ (by linarith) (by linarith) 2)
  have hE0' : |expCutoff t - 1| ≤ 1 := by
    rw [abs_of_nonpos (by linarith [expCutoff_le_one t])]; linarith [expCutoff_pos t]
  have hE1 : |deriv expCutoff t| ≤ δ := (abs_deriv_expCutoff_le ht).trans (by linarith)
  have hE2' : |deriv (deriv expCutoff) t| ≤ 2 :=
    (derivBoundTwo_expCutoff ht).2.2.trans (by linarith [expCutoff_le_one t])
  have hu : 0 < δ⁻¹ := inv_pos.2 hδ
  have huδ : δ⁻¹ * δ = 1 := inv_mul_cancel₀ hδ.ne'
  have k1 : |expCutoff t - 1| * δ⁻¹ ≤ 1 := by
    calc |expCutoff t - 1| * δ⁻¹ ≤ δ ^ 2 * δ⁻¹ := mul_le_mul_of_nonneg_right hE0 hu.le
      _ = δ := by field_simp
      _ ≤ 1 := hδ1
  have k2 : |expCutoff t - 1| * δ⁻¹ ^ 2 ≤ 1 := by
    calc |expCutoff t - 1| * δ⁻¹ ^ 2 ≤ δ ^ 2 * δ⁻¹ ^ 2 :=
          mul_le_mul_of_nonneg_right hE0 (by positivity)
      _ = 1 := by field_simp
  have k3 : |deriv expCutoff t| * δ⁻¹ ≤ 1 := by
    calc |deriv expCutoff t| * δ⁻¹ ≤ δ * δ⁻¹ := mul_le_mul_of_nonneg_right hE1 hu.le
      _ = 1 := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hG]
    refine (abs_add_le _ _).trans ?_
    rw [abs_one, abs_mul]
    have hprod := mul_le_mul hE0' hσ0 (abs_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)
    linarith only [hprod, hS1]
  · rw [hd, deriv_fun_mul (hE2.differentiableAt (by norm_num)) (hσ2.differentiableAt (by norm_num)),
      deriv_sub_const, hd1]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos hu]
    have hfirst : |deriv expCutoff t| * |σ t| ≤ 1 := by
      simpa using (mul_le_mul hE1 hσ0 (abs_nonneg _) hδ.le).trans
        (mul_le_mul_of_nonneg_right hδ1 zero_le_one)
    have hlast := mul_le_mul k1 hs1 (abs_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)
    linarith only [hfirst, hlast, hS1]
  · rw [hd, deriv_deriv_mul hE2 hσ2, deriv_sub_const_fun, hd1, hd2]
    refine (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl |>.trans ?_)
    rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_two, abs_of_pos hu,
      abs_of_pos (by positivity : 0 < δ⁻¹ ^ 2)]
    have hfirst := mul_le_mul hE2' hσ0 (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have hmiddle := mul_le_mul k3 hs1 (abs_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)
    have hlast := mul_le_mul k2 hs2 (abs_nonneg _) (zero_le_one : (0 : ℝ) ≤ 1)
    linarith only [hfirst, hmiddle, hlast]

/-- For `t > 1`, `|G_k^{(j)} (t)| ≤ B E (t)`, `j ≤ 2`, uniformly in `k`. -/
theorem exists_derivBoundTwo_approxGlue :
    ∃ B, ∀ k t, 1 < t → DerivBoundTwo (approxGlue k) t (B * expCutoff t) := by
  obtain ⟨S, hS1, hS⟩ := exists_derivBoundTwo_smoothTransition
  refine ⟨2 + (2 + 3 * S) * Real.exp 1, fun k t ht => ?_⟩
  have hE := expCutoff_pos t
  rcases le_or_gt t (1 + approxEps k) with htδ | htδ
  · refine (derivBoundTwo_approxGlue_of_le hS1 hS k ht.le htδ).mono ?_
    have hE1 : Real.exp (-1) ≤ expCutoff t :=
      exp_neg_one_le_expCutoff ht.le (by linarith [approxEps_le_one k])
    have : 1 ≤ Real.exp 1 * expCutoff t := by
      calc (1 : ℝ) = Real.exp 1 * Real.exp (-1) := by rw [← Real.exp_add]; simp
        _ ≤ Real.exp 1 * expCutoff t := mul_le_mul_of_nonneg_left hE1 (Real.exp_pos 1).le
    nlinarith
  · have h : approxGlue k =ᶠ[𝓝 t] expCutoff := by
      filter_upwards [Ioi_mem_nhds htδ] with s hs using approxGlue_eq_expCutoff k hs.le
    refine ((derivBoundTwo_expCutoff ht.le).congr h).mono ?_
    have : 0 ≤ (2 + 3 * S) * Real.exp 1 * expCutoff t :=
      mul_nonneg (mul_nonneg (by linarith) (Real.exp_pos 1).le) hE.le
    nlinarith

/-- `|χ_k^{(j)}| ≤ S`, `j ≤ 2`, with `S` a bound for `s`, `s'`, `s''` (`R_k ≥ 1`). -/
theorem derivBoundTwo_approxTrunc {S : ℝ} (hS : ∀ x, DerivBoundTwo Real.smoothTransition x S)
    (k : ℕ) (t : ℝ) : DerivBoundTwo (approxTrunc k) t S := by
  have hR : 0 < approxRadius k := by linarith [two_le_approxRadius k]
  have h : approxTrunc k = fun s => Real.smoothTransition (-(approxRadius k)⁻¹ * s + 2) := by
    funext s
    simp only [approxTrunc]
    congr 1
    rw [div_eq_mul_inv]
    ring
  rw [h]
  refine DerivBoundTwo.comp_mul_add ?_ (hS _)
  rw [abs_neg, abs_inv, abs_of_pos hR]
  exact inv_le_one_of_one_le₀ (by linarith [two_le_approxRadius k])

/-- For `t > 1` and `α ∈ [0, 1]`, `|K_k^{(j)} (t)| ≤ B E (t)`, `j ≤ 2`, uniformly in `k`. -/
theorem exists_derivBoundTwo_approxProfile {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ B, ∀ k t, 1 < t → DerivBoundTwo (approxProfile α k) t (B * expCutoff t) := by
  obtain ⟨S, -, hS⟩ := exists_derivBoundTwo_smoothTransition
  obtain ⟨Bg, hBg⟩ := exists_derivBoundTwo_approxGlue
  refine ⟨4 * (4 * 2 * Bg) * S, fun k t ht => ?_⟩
  have hA : DerivBoundTwo (fun s => (s + approxEps k) ^ (-α)) t 2 :=
    DerivBoundTwo.comp_add_const
      (derivBoundTwo_rpow_neg hα0 hα1 (by linarith [approxEps_pos k]))
  have hAc : ContDiffAt ℝ 2 (fun s : ℝ => (s + approxEps k) ^ (-α)) t :=
    (contDiffAt_rpow_add_neg α _ (by linarith [approxEps_pos k])).of_le (by norm_num)
  have hGc : ContDiffAt ℝ 2 (approxGlue k) t :=
    (contDiff_approxGlue k).contDiffAt.of_le (by norm_num)
  have hTc : ContDiffAt ℝ 2 (approxTrunc k) t :=
    (contDiff_approxTrunc k).contDiffAt.of_le (by norm_num)
  have h := (hA.mul hAc hGc (hBg k t ht)).mul (hAc.mul hGc) hTc
    (derivBoundTwo_approxTrunc hS k t)
  exact (show DerivBoundTwo (approxProfile α k) t _ from h).mono (le_of_eq (by ring))

/-- Domination on the punctured unit disc: `|∂²φ_k (z)| ≤ 8 |z|^{−2α}`,
`|∂_zbar²φ_k (z)| ≤ 2 |z|^{−2α}`. -/
theorem norm_approxSchwartz_le_of_lt_one {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) {z : ℂ}
    (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    ‖(dzCLM ^ 2) (approxSchwartz α k) z‖ ≤ 8 * ‖z‖ ^ (-2 * α) ∧
      ‖(dzbarCLM ^ 2) (approxSchwartz α k) z‖ ≤ 2 * ‖z‖ ^ (-2 * α) := by
  have ht0 : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  have ht1 : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hk := contDiffAt_two_approxProfile α k z
  obtain ⟨h1, h2⟩ := abs_approxProfile_le_of_lt_one hα0 hα1 k ht0 ht1
  rw [dzCLM_sq_approxSchwartz, dzbarCLM_sq_approxSchwartz, dz_dz_sq_mul_ofReal_radial hk,
    dzbar_dzbar_sq_mul_ofReal_radial hk, Complex.norm_real, Real.norm_eq_abs, norm_mul,
    norm_pow, Complex.norm_real, Real.norm_eq_abs, ← normSq_rpow_neg]
  refine ⟨h1, ?_⟩
  rwa [show ‖z‖ ^ 4 = Complex.normSq z ^ 2 by rw [Complex.normSq_eq_norm_sq]; ring]

/-- Domination outside the unit disc, for `α ∈ [0, 1]`:
`|∂²φ_k (z)|, |∂_zbar²φ_k (z)| ≤ C (1 + |z|²)² e^{−(|z| − 1)²}`, uniformly in `k`. -/
theorem exists_norm_approxSchwartz_le_of_one_lt {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C, ∀ k z, 1 < ‖z‖ →
      ‖(dzCLM ^ 2) (approxSchwartz α k) z‖ ≤
          C * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) ∧
        ‖(dzbarCLM ^ 2) (approxSchwartz α k) z‖ ≤
          C * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) := by
  obtain ⟨B, hB⟩ := exists_derivBoundTwo_approxProfile hα0 hα1
  refine ⟨2 * B, fun k z hz => ?_⟩
  have ht : 1 < Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith
  have h := norm_dz_dz_sq_mul_ofReal_radial_le (contDiffAt_two_approxProfile α k z)
    (hB k _ ht)
  rw [expCutoff_normSq] at h
  rw [dzCLM_sq_approxSchwartz, dzbarCLM_sq_approxSchwartz]
  constructor
  · exact h.1.trans_eq (by ring)
  · exact h.2.trans_eq (by ring)

end HarmonicAnalysis.BeurlingAhlfors
