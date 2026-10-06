/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-!
# Limits of weighted pairings

Pairings `∫ c_n F_n G_n` converge when `F_n → F` in `L^p`, `G_n → G` in the
conjugate `L^q`, and the weights are bounded by one and converge almost
everywhere; they tend to zero when the weights tend to zero uniformly. These
are the limit passages removing the mollification and cutoff in
`lem:pv-serrin-uniqueness` of the Escauriaza–Seregin–Šverák manuscript. Also recorded: interpolation of `L^p` membership.
-/

public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

noncomputable section

namespace CKN

variable {α : Type} [MeasurableSpace α] {μ : Measure α}

/-- Membership in `L^p` and `L^q` gives membership in `L^r` for `p ≤ r ≤ q`. -/
theorem serrin_memLp_interpolate {E : Type} [NormedAddCommGroup E] {f : α → E}
    {p q r : ℝ≥0∞} (hp0 : p ≠ 0) (hqtop : q ≠ ⊤) (hpr : p ≤ r) (hrq : r ≤ q)
    (hfp : MemLp f p μ) (hfq : MemLp f q μ) : MemLp f r μ := by
  have hr0 : r ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.mpr hp0) hpr).ne'
  have hrtop : r ≠ ⊤ := ne_top_of_le_ne_top hqtop hrq
  have hptop : p ≠ ⊤ := ne_top_of_le_ne_top hrtop hpr
  have hq0 : q ≠ 0 := (lt_of_lt_of_le (pos_iff_ne_zero.mpr hr0) hrq).ne'
  have hm := hfp.aestronglyMeasurable
  have hpr' : p.toReal ≤ r.toReal := ENNReal.toReal_mono hrtop hpr
  have hrq' : r.toReal ≤ q.toReal := ENNReal.toReal_mono hqtop hrq
  have hpfin : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ≠ ⊤ := by
    have h1 := hfp.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hm] at h1
    exact (ENNReal.rpow_lt_top_iff_of_pos (by
      have := ENNReal.toReal_pos hp0 hptop
      positivity)).mp h1 |>.ne
  have hqfin : (∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂μ) ≠ ⊤ := by
    have h1 := hfq.eLpNorm_lt_top
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 hqtop hm] at h1
    exact (ENNReal.rpow_lt_top_iff_of_pos (by
      have := ENNReal.toReal_pos hq0 hqtop
      positivity)).mp h1 |>.ne
  have hpoint (x : α) : ‖f x‖ₑ ^ r.toReal ≤ ‖f x‖ₑ ^ p.toReal + ‖f x‖ₑ ^ q.toReal := by
    rcases le_total ‖f x‖ₑ 1 with h | h
    · exact (ENNReal.rpow_le_rpow_of_exponent_ge h hpr').trans le_self_add
    · exact (ENNReal.rpow_le_rpow_of_exponent_le h hrq').trans le_add_self
  have hrfin : (∫⁻ x, ‖f x‖ₑ ^ r.toReal ∂μ) < ⊤ := by
    calc
      (∫⁻ x, ‖f x‖ₑ ^ r.toReal ∂μ) ≤ ∫⁻ x, (‖f x‖ₑ ^ p.toReal + ‖f x‖ₑ ^ q.toReal) ∂μ :=
        lintegral_mono hpoint
      _ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) + ∫⁻ x, ‖f x‖ₑ ^ q.toReal ∂μ :=
        lintegral_add_left' (hm.enorm.pow_const _) _
      _ < ⊤ := ENNReal.add_lt_top.mpr ⟨hpfin.lt_top, hqfin.lt_top⟩
  rw [memLp_iff, eLpNorm_eq_lintegral_rpow_enorm_toReal hr0 hrtop hm]
  exact ENNReal.rpow_lt_top_of_nonneg (by positivity) hrfin.ne

private theorem serrin_eLpNorm_mul_le {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {F G : α → ℝ} (hF : AEStronglyMeasurable F μ) (hG : AEStronglyMeasurable G μ) :
    (∫⁻ x, ‖F x * G x‖ₑ ∂μ) ≤ eLpNorm F p μ * eLpNorm G q μ := by
  have h := eLpNorm_smul_le_mul_eLpNorm (p := p) (q := q) (r := 1) hF hG
  rw [eLpNorm_one_eq_lintegral_enorm (hF.smul hG)] at h
  simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using h

private theorem serrin_tendsto_mul_bounded {a b : ℕ → ℝ≥0∞} {B : ℝ≥0∞} (hB : B ≠ ⊤)
    (ha : Tendsto a atTop (𝓝 0)) (hb : ∀ᶠ n in atTop, b n ≤ B) :
    Tendsto (fun n => a n * b n) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n => a n * B) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.mul_const ha (Or.inr hB)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h1
    (Eventually.of_forall fun _ => bot_le) ?_
  filter_upwards [hb] with n hn
  exact mul_le_mul_right hn _

private theorem serrin_eLpNorm_bounded {r : ℝ≥0∞} (hr : 1 ≤ r) {G : α → ℝ} {Gs : ℕ → α → ℝ}
    (hGs : ∀ᶠ n in atTop, AEStronglyMeasurable (Gs n) μ)
    (hlim : Tendsto (fun n => eLpNorm (fun x => Gs n x - G x) r μ) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, eLpNorm (Gs n) r μ ≤ 1 + eLpNorm G r μ := by
  have hsmall : ∀ᶠ n in atTop, eLpNorm (fun x => Gs n x - G x) r μ ≤ 1 :=
    (tendsto_order.1 hlim).2 1 one_pos |>.mono fun _ h => h.le
  filter_upwards [hsmall, hGs] with n hn _
  calc
    eLpNorm (Gs n) r μ = eLpNorm (fun x => (Gs n x - G x) + G x) r μ := by
      congr 1
      funext x
      ring
    _ ≤ eLpNorm (fun x => Gs n x - G x) r μ + eLpNorm G r μ :=
      eLpNorm_add_le hr
    _ ≤ 1 + eLpNorm G r μ := by gcongr

/-- Weighted pairings converge under `L^p × L^q` convergence of the factors
and almost everywhere convergence of weights bounded by one. -/
theorem serrin_weighted_pairing_tendsto {p q : ℝ≥0∞} [hpq : ENNReal.HolderTriple p q 1]
    (hq : 1 ≤ q)
    {F G c : α → ℝ} {Fs Gs cs : ℕ → α → ℝ}
    (hF : MemLp F p μ) (hG : MemLp G q μ)
    (hFs : ∀ᶠ n in atTop, AEStronglyMeasurable (Fs n) μ)
    (hGs : ∀ᶠ n in atTop, AEStronglyMeasurable (Gs n) μ)
    (hFlim : Tendsto (fun n => eLpNorm (fun x => Fs n x - F x) p μ) atTop (𝓝 0))
    (hGlim : Tendsto (fun n => eLpNorm (fun x => Gs n x - G x) q μ) atTop (𝓝 0))
    (hcm : ∀ n, AEStronglyMeasurable (cs n) μ) (hcb : ∀ n x, |cs n x| ≤ 1)
    (hcm' : AEStronglyMeasurable c μ) (hcb' : ∀ x, |c x| ≤ 1)
    (hc : ∀ᵐ x ∂μ, Tendsto (fun n => cs n x) atTop (𝓝 (c x))) :
    Tendsto (fun n => ∫ x, cs n x * Fs n x * Gs n x ∂μ) atTop
      (𝓝 (∫ x, c x * F x * G x ∂μ)) := by
  have hFm := hF.aestronglyMeasurable
  have hGm := hG.aestronglyMeasurable
  have hFG : Integrable (fun x => F x * G x) μ := by
    have h := hF.mul (r := 1) hG
    exact (memLp_one_iff_integrable.mp h)
  -- bounded norms of the approximating factors
  have hGbd := serrin_eLpNorm_bounded hq hGs hGlim
  have hGfin : 1 + eLpNorm G q μ ≠ ⊤ := ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
    hG.eLpNorm_ne_top⟩
  -- the three error terms
  have hE1 : Tendsto (fun n => ∫⁻ x, ‖(Fs n x - F x) * Gs n x‖ₑ ∂μ) atTop (𝓝 0) := by
    have hmain := serrin_tendsto_mul_bounded hGfin hFlim hGbd
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmain
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hFs, hGs] with n hFn hGn
    exact serrin_eLpNorm_mul_le (hFn.sub hFm) hGn
  have hE2 : Tendsto (fun n => ∫⁻ x, ‖F x * (Gs n x - G x)‖ₑ ∂μ) atTop (𝓝 0) := by
    have hmain : Tendsto (fun n => eLpNorm F p μ * eLpNorm (fun x => Gs n x - G x) q μ)
        atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.const_mul hGlim (Or.inr hF.eLpNorm_ne_top)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmain
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hGs] with n hGn
    exact serrin_eLpNorm_mul_le hFm (hGn.sub hGm)
  have hE3 : Tendsto (fun n => ∫⁻ x, ‖(cs n x - c x) * (F x * G x)‖ₑ ∂μ) atTop (𝓝 0) := by
    have hlim := tendsto_lintegral_of_dominated_convergence'
      (fun x => 2 * ‖F x * G x‖ₑ)
      (fun n => (((hcm n).sub hcm').mul hFG.aestronglyMeasurable).enorm)
      (fun n => Eventually.of_forall fun x => by
        show ‖(cs n x - c x) * (F x * G x)‖ₑ ≤ 2 * ‖F x * G x‖ₑ
        rw [enorm_mul]
        gcongr
        rw [Real.enorm_eq_ofReal_abs]
        calc
          ENNReal.ofReal |cs n x - c x| ≤ ENNReal.ofReal 2 := by
            apply ENNReal.ofReal_le_ofReal
            calc
              |cs n x - c x| ≤ |cs n x| + |c x| := abs_sub _ _
              _ ≤ 1 + 1 := add_le_add (hcb n x) (hcb' x)
              _ = 2 := by norm_num
          _ = 2 := by simp)
      (by
        rw [lintegral_const_mul' _ _ (by simp)]
        exact ENNReal.mul_ne_top (by simp) hFG.2.ne)
      (by
        filter_upwards [hc] with x hx
        have h1 : Tendsto (fun n => cs n x - c x) atTop (𝓝 0) := by
          simpa using hx.sub_const (c x)
        have h2 := (h1.mul_const (F x * G x)).enorm
        simpa using h2)
    simpa using hlim
  have hFsLp : ∀ᶠ n in atTop, MemLp (Fs n) p μ := by
    have hsmall : ∀ᶠ n in atTop, eLpNorm (fun x => Fs n x - F x) p μ < ⊤ :=
      (tendsto_order.1 hFlim).2 1 one_pos |>.mono fun _ h => h.trans ENNReal.one_lt_top
    filter_upwards [hsmall, hFs] with n hn hm
    have hd : MemLp (fun x => Fs n x - F x) p μ := hn
    have h := hd.add hF
    refine h.congr_norm hm (Eventually.of_forall fun x => ?_)
    simp
  have hGsLp : ∀ᶠ n in atTop, MemLp (Gs n) q μ := by
    have hsmall : ∀ᶠ n in atTop, eLpNorm (fun x => Gs n x - G x) q μ < ⊤ :=
      (tendsto_order.1 hGlim).2 1 one_pos |>.mono fun _ h => h.trans ENNReal.one_lt_top
    filter_upwards [hsmall, hGs] with n hn hm
    have hd : MemLp (fun x => Gs n x - G x) q μ := hn
    have h := hd.add hG
    refine h.congr_norm hm (Eventually.of_forall fun x => ?_)
    simp
  refine tendsto_integral_of_L1 _ ((hcm'.mul hFm).mul hGm) ?_ ?_
  · filter_upwards [hFsLp, hGsLp] with n hFn hGn
    have hprod : Integrable (fun x => Fs n x * Gs n x) μ :=
      memLp_one_iff_integrable.mp (hFn.mul (r := 1) hGn)
    refine (hprod.bdd_mul (c := 1) (hcm n) (Eventually.of_forall fun x => ?_)).congr
      (Eventually.of_forall fun x => by simp only [mul_assoc])
    rw [Real.norm_eq_abs]
    exact hcb n x
  · have hsum := (hE1.add hE2).add hE3
    simp only [add_zero] at hsum
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hFs, hGs] with n hFn hGn
    have hm1 : AEMeasurable (fun x => ‖(Fs n x - F x) * Gs n x‖ₑ) μ :=
      ((hFn.sub hFm).mul hGn).enorm
    have hm2 : AEMeasurable (fun x => ‖F x * (Gs n x - G x)‖ₑ) μ :=
      (hFm.mul (hGn.sub hGm)).enorm
    have hm12 : AEMeasurable
        (fun x => ‖(Fs n x - F x) * Gs n x‖ₑ + ‖F x * (Gs n x - G x)‖ₑ) μ := hm1.add hm2
    rw [← lintegral_add_left' hm1, ← lintegral_add_left' hm12]
    refine lintegral_mono fun x => ?_
    show ‖cs n x * Fs n x * Gs n x - c x * F x * G x‖ₑ ≤ _
    have hid : cs n x * Fs n x * Gs n x - c x * F x * G x =
        cs n x * ((Fs n x - F x) * Gs n x) + cs n x * (F x * (Gs n x - G x)) +
          (cs n x - c x) * (F x * G x) := by ring
    rw [hid]
    have hc1 : ‖cs n x‖ₑ ≤ 1 := by
      rw [Real.enorm_eq_ofReal_abs]
      exact ENNReal.ofReal_le_one.mpr (hcb n x)
    calc
      ‖cs n x * ((Fs n x - F x) * Gs n x) + cs n x * (F x * (Gs n x - G x)) +
          (cs n x - c x) * (F x * G x)‖ₑ ≤
          ‖cs n x * ((Fs n x - F x) * Gs n x)‖ₑ + ‖cs n x * (F x * (Gs n x - G x))‖ₑ +
            ‖(cs n x - c x) * (F x * G x)‖ₑ :=
        (enorm_add_le _ _).trans (add_le_add (enorm_add_le _ _) le_rfl)
      _ ≤ ‖(Fs n x - F x) * Gs n x‖ₑ + ‖F x * (Gs n x - G x)‖ₑ +
            ‖(cs n x - c x) * (F x * G x)‖ₑ := by
        rw [enorm_mul, enorm_mul (cs n x)]
        gcongr
        · exact mul_le_of_le_one_left zero_le hc1
        · exact mul_le_of_le_one_left zero_le hc1

/-- Weighted pairings tend to zero when the weights tend to zero uniformly and
the factors converge in conjugate Lebesgue spaces. -/
theorem serrin_weighted_pairing_tendsto_zero {p q : ℝ≥0∞} [hpq : ENNReal.HolderTriple p q 1]
    (hp : 1 ≤ p) (hq : 1 ≤ q)
    {F G : α → ℝ} {Fs Gs cs : ℕ → α → ℝ}
    (hF : MemLp F p μ) (hG : MemLp G q μ)
    (hFs : ∀ᶠ n in atTop, AEStronglyMeasurable (Fs n) μ)
    (hGs : ∀ᶠ n in atTop, AEStronglyMeasurable (Gs n) μ)
    (hFlim : Tendsto (fun n => eLpNorm (fun x => Fs n x - F x) p μ) atTop (𝓝 0))
    (hGlim : Tendsto (fun n => eLpNorm (fun x => Gs n x - G x) q μ) atTop (𝓝 0))
    {ε : ℕ → ℝ} (hcb : ∀ n x, |cs n x| ≤ ε n) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, cs n x * Fs n x * Gs n x ∂μ) atTop (𝓝 0) := by
  have hFbd := serrin_eLpNorm_bounded hp hFs hFlim
  have hGbd := serrin_eLpNorm_bounded hq hGs hGlim
  set B : ℝ≥0∞ := (1 + eLpNorm F p μ) * (1 + eLpNorm G q μ)
  have hB : B ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hF.eLpNorm_ne_top⟩)
    (ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top, hG.eLpNorm_ne_top⟩)
  have hεE : Tendsto (fun n => ENNReal.ofReal (ε n)) atTop (𝓝 0) := by
    have h := (ENNReal.continuous_ofReal.tendsto 0).comp hε
    simp only [ENNReal.ofReal_zero] at h
    exact h
  have hmain := serrin_tendsto_mul_bounded hB hεE (Eventually.of_forall fun _ => le_rfl)
  have hlint : Tendsto (fun n => ∫⁻ x, ‖cs n x * Fs n x * Gs n x‖ₑ ∂μ) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmain
      (Eventually.of_forall fun _ => bot_le) ?_
    filter_upwards [hFs, hGs, hFbd, hGbd] with n hFn hGn hFb hGb
    calc
      (∫⁻ x, ‖cs n x * Fs n x * Gs n x‖ₑ ∂μ) ≤
          ∫⁻ x, ENNReal.ofReal (ε n) * ‖Fs n x * Gs n x‖ₑ ∂μ := by
        refine lintegral_mono fun x => ?_
        rw [mul_assoc, enorm_mul, Real.enorm_eq_ofReal_abs]
        gcongr
        exact hcb n x
      _ = ENNReal.ofReal (ε n) * ∫⁻ x, ‖Fs n x * Gs n x‖ₑ ∂μ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal (ε n) * (eLpNorm (Fs n) p μ * eLpNorm (Gs n) q μ) := by
        gcongr
        exact serrin_eLpNorm_mul_le hFn hGn
      _ ≤ ENNReal.ofReal (ε n) * B := by
        gcongr
        exact mul_le_mul' hFb hGb
  have hreal : Tendsto (fun n => (∫⁻ x, ‖cs n x * Fs n x * Gs n x‖ₑ ∂μ).toReal) atTop (𝓝 0) := by
    have h := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlint
    simp only [ENNReal.toReal_zero] at h
    exact h
  refine squeeze_zero_norm (fun n => ?_) hreal
  have h := norm_integral_le_lintegral_norm (μ := μ) (fun x => cs n x * Fs n x * Gs n x)
  simpa only [ofReal_norm] using h

end CKN
