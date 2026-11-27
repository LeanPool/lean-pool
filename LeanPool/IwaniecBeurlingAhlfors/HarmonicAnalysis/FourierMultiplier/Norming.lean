/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Geometry.Manifold.SmoothApprox
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The `L^p` norm is normed by Schwartz functions

`HarmonicAnalysis.eLpNorm_le_of_forall_schwartz`: for `1 < p < ∞`, `q = p / (p − 1)` and a
continuous function `h` on a finite-dimensional real normed space with a measure that is finite on
compact sets, if `‖∫ h · (conj g)‖ ≤ A ‖g‖_q` for every Schwartz function `g`, then `‖h‖_p ≤ A`.

The proof is the standard one. The bound passes from Schwartz functions to continuous compactly
supported ones by uniform approximation with a fixed compact support
(`Continuous.exists_contDiff_approx`). It is then tested on `g = χ |h|^{p−2} h`, `χ` a bump
function equal to `1` on a ball: `∫ h (conj g) = ∫ χ |h|^p =: I` and `‖g‖_q^q ≤ I`, so that
`I ≤ A I^{1/q}`, `I^{1/p} ≤ A`, and monotone convergence over the balls concludes.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped SchwartzMap ENNReal ComplexConjugate ContDiff

namespace HarmonicAnalysis

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [IsFiniteMeasureOnCompacts μ]

/-- The bound `‖∫ h · (conj g)‖ ≤ A ‖g‖_q` passes from Schwartz functions `g` to continuous
compactly
supported ones. -/
private theorem norm_integral_mul_conj_le_of_hasCompactSupport {h : V → ℂ} (hh : Continuous h)
    {q : ℝ≥0∞} (hq : 1 ≤ q) (hq' : q ≠ ⊤) {A : ℝ≥0∞} (hA : A ≠ ⊤)
    (H : ∀ g : 𝓢(V, ℂ), ‖∫ x, h x * conj (g x) ∂μ‖ₑ ≤ A * eLpNorm g q μ)
    {g : V → ℂ} (hg : Continuous g) (hgc : HasCompactSupport g) :
    ‖∫ x, h x * conj (g x) ∂μ‖ₑ ≤ A * eLpNorm g q μ := by
  set K := tsupport g
  have hK : IsCompact K := hgc
  have hsupp : Function.support g ⊆ K := subset_tsupport g
  have hφ (j : ℕ) : ∃ φ : V → ℂ, ContDiff ℝ ∞ φ ∧ (∀ x, dist (φ x) (g x) < 1 / (j + 1)) ∧
      Function.support φ ⊆ Function.support g :=
    hg.exists_contDiff_approx ⊤ continuous_const (fun _ => by positivity)
  choose φ hφs hφd hφsupp using hφ
  have hφK (j : ℕ) (x : V) (hx : x ∉ K) : φ j x = 0 :=
    Function.notMem_support.1 fun hx' => hx (hsupp (hφsupp j hx'))
  -- the pairings converge, by dominated convergence
  have hlim : Tendsto (fun j => ∫ x, h x * conj (φ j x) ∂μ) atTop
      (𝓝 (∫ x, h x * conj (g x) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence (K.indicator fun x => ‖h x‖ * (‖g x‖ + 1))
      (fun j => (hh.mul (Complex.continuous_conj.comp (hφs j).continuous)).aestronglyMeasurable)
      ((integrable_indicator_iff hK.measurableSet).2
        ((by fun_prop : Continuous fun x => ‖h x‖ * (‖g x‖ + 1)).continuousOn.integrableOn_compact
          hK))
      (fun j => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => ?_)
    · by_cases hx : x ∈ K
      · rw [Set.indicator_of_mem hx, norm_mul, Complex.norm_conj]
        gcongr
        have h1 : 1 / ((j : ℝ) + 1) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
        have := norm_le_norm_add_norm_sub' (φ j x) (g x)
        rw [← dist_eq_norm] at this
        linarith [hφd j x]
      · simp [Set.indicator_of_notMem hx, hφK j x hx]
    · have hconv : Tendsto (fun j => φ j x) atTop (𝓝 (g x)) :=
        tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg)
          (fun j => (hφd j x).le) tendsto_one_div_add_atTop_nhds_zero_nat)
      exact ((continuous_const.mul Complex.continuous_conj).tendsto (g x)).comp hconv
  -- the norms converge from above
  set c := μ K ^ (1 / q.toReal)
  have hc : c ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hK.measure_lt_top.ne
  have hnorm (j : ℕ) :
      eLpNorm (φ j) q μ ≤ eLpNorm g q μ + ENNReal.ofReal (1 / (j + 1)) * c := by
    calc eLpNorm (φ j) q μ = eLpNorm (g + (φ j - g)) q μ := by rw [add_sub_cancel]
      _ ≤ eLpNorm g q μ + eLpNorm (φ j - g) q μ := eLpNorm_add_le hq
      _ ≤ _ := by
        gcongr
        exact eLpNorm_sub_le_of_dist_bdd μ hq' hK.measurableSet.nullMeasurableSet
          (by positivity) ((hφs j).continuous.sub hg).aestronglyMeasurable
          (fun x => (hφd j x).le) ((hφsupp j).trans hsupp) hsupp
  have hlim' : Tendsto (fun j : ℕ => A * (eLpNorm g q μ + ENNReal.ofReal (1 / (j + 1)) * c))
      atTop (𝓝 (A * eLpNorm g q μ)) := by
    have h1 : Tendsto (fun j : ℕ => ENNReal.ofReal (1 / (j + 1))) atTop (𝓝 0) := by
      simpa using ENNReal.tendsto_ofReal (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa using ENNReal.Tendsto.const_mul
      (tendsto_const_nhds.add (ENNReal.Tendsto.mul_const h1 (Or.inr hc))) (Or.inr hA)
  refine le_of_tendsto_of_tendsto' hlim.eNorm hlim' fun j => ?_
  calc ‖∫ x, h x * conj (φ j x) ∂μ‖ₑ ≤ A * eLpNorm (φ j) q μ :=
        H ((hgc.mono (hφsupp j)).toSchwartzMap (hφs j))
    _ ≤ _ := by gcongr; exact hnorm j

/-- If `J ≤ A J^{1/q}` with `J < ∞` and `1/p + 1/q = 1`, then `J ≤ A^p`. -/
private theorem le_rpow_of_le_mul_rpow {J A : ℝ≥0∞} {p q : ℝ} (hpq : p.HolderConjugate q)
    (hJ : J ≠ ⊤) (h : J ≤ A * J ^ (1 / q)) : J ≤ A ^ p := by
  rcases eq_or_ne J 0 with h0 | h0
  · simp [h0]
  have hsplit : J ^ (1 / p) * J ^ (1 / q) = J := by
    rw [← ENNReal.rpow_add _ _ h0 hJ, hpq.one_div_add_one_div, div_one, ENNReal.rpow_one]
  have hq0 : J ^ (1 / q) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 h0) hJ).ne'
  have hqt : J ^ (1 / q) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hpq.symm.one_div_nonneg hJ
  have : J ^ (1 / p) ≤ A := by
    rw [← ENNReal.mul_le_mul_iff_left hq0 hqt, hsplit]
    exact h
  rwa [one_div, ENNReal.rpow_inv_le_iff hpq.pos] at this

/-- `‖ |z|^{p−2} z ‖ = |z|^{p−1}`. -/
private theorem norm_rpow_sub_two_mul {p : ℝ} (hp : 1 < p) (z : ℂ) :
    ‖((‖z‖ ^ (p - 2) : ℝ) : ℂ) * z‖ = ‖z‖ ^ (p - 1) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rcases eq_or_ne z 0 with rfl | hz
  · simp [Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  · conv_rhs => rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add (norm_pos_iff.2 hz),
      Real.rpow_one]

/-- The function `z ↦ |z|^{p−2} z` is continuous for `1 < p`. -/
private theorem continuous_rpow_sub_two_mul {p : ℝ} (hp : 1 < p) :
    Continuous fun z : ℂ => ((‖z‖ ^ (p - 2) : ℝ) : ℂ) * z := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases eq_or_ne z 0 with rfl | hz
  · have hc : Continuous fun z : ℂ => ‖z‖ ^ (p - 1) :=
      continuous_norm.rpow_const fun _ => Or.inr (by linarith)
    change Tendsto _ (𝓝 0) (𝓝 (((‖(0 : ℂ)‖ ^ (p - 2) : ℝ) : ℂ) * 0))
    rw [mul_zero, tendsto_zero_iff_norm_tendsto_zero]
    simp_rw [norm_rpow_sub_two_mul hp]
    simpa [Real.zero_rpow (by linarith : p - 1 ≠ 0)] using hc.tendsto 0
  · exact (Complex.continuous_ofReal.continuousAt.comp
      ((Real.continuousAt_rpow_const _ _ (Or.inl (norm_ne_zero_iff.2 hz))).comp
        continuous_norm.continuousAt)).mul continuousAt_id

/-- **Norming by Schwartz functions.** Let `1 < p < ∞` and `q = p / (p − 1)`. If `h` is
continuous and `‖∫ h · (conj g)‖ ≤ A ‖g‖_q` for every Schwartz function `g`, then `‖h‖_p ≤ A`. -/
theorem eLpNorm_le_of_forall_schwartz {h : V → ℂ} (hh : Continuous h) {p : ℝ} (hp : 1 < p)
    {A : ℝ≥0∞}
    (H : ∀ g : 𝓢(V, ℂ), ‖∫ x, h x * conj (g x) ∂μ‖ₑ ≤
      A * eLpNorm g (ENNReal.ofReal (p / (p - 1))) μ) :
    eLpNorm h (ENNReal.ofReal p) μ ≤ A := by
  rcases eq_or_ne A ⊤ with rfl | hA
  · exact le_top
  have hpq : p.HolderConjugate (p / (p - 1)) :=
    (Real.holderConjugate_iff_eq_conjExponent hp).2 rfl
  set q := p / (p - 1)
  have hp0 : 0 < p := hpq.pos
  have hq1 : 1 < q := hpq.symm.lt
  have hQ0 : ENNReal.ofReal q ≠ 0 := by simpa using hpq.symm.pos
  have H' (g : V → ℂ) (hg : Continuous g) (hgc : HasCompactSupport g) :
      ‖∫ x, h x * conj (g x) ∂μ‖ₑ ≤ A * eLpNorm g (ENNReal.ofReal q) μ :=
    norm_integral_mul_conj_le_of_hasCompactSupport hh (ENNReal.one_le_ofReal.2 hq1.le)
      ENNReal.ofReal_ne_top hA H hg hgc
  have hcont : Continuous fun x => ‖h x‖ ^ p := hh.norm.rpow_const fun _ => Or.inr hp0.le
  -- the integrals over the balls
  have hball (N : ℕ) : ∫⁻ x, (closedBall (0 : V) (N + 1)).indicator
      (fun x => ‖h x‖ₑ ^ p) x ∂μ ≤ A ^ p := by
    let χ : ContDiffBump (0 : V) := ⟨N + 1, N + 2, by positivity, by linarith⟩
    set g : V → ℂ := fun x => (χ x : ℂ) * (((‖h x‖ ^ (p - 2) : ℝ) : ℂ) * h x)
    have hgc : Continuous g :=
      (Complex.continuous_ofReal.comp χ.continuous).mul
        ((continuous_rpow_sub_two_mul hp).comp hh)
    have hgs : HasCompactSupport g := by
      have : HasCompactSupport ((Complex.ofReal ∘ χ) *
          fun x => ((‖h x‖ ^ (p - 2) : ℝ) : ℂ) * h x) :=
        (χ.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
      exact this
    have hnn (x : V) : 0 ≤ χ x * ‖h x‖ ^ p := mul_nonneg χ.nonneg (by positivity)
    have hint : Integrable (fun x => χ x * ‖h x‖ ^ p) μ :=
      (χ.continuous.mul hcont).integrable_of_hasCompactSupport
        (χ.hasCompactSupport.mul_right (f' := fun x => ‖h x‖ ^ p))
    set J := ∫⁻ x, ENNReal.ofReal (χ x * ‖h x‖ ^ p) ∂μ
    have hpair : ‖∫ x, h x * conj (g x) ∂μ‖ₑ = J := by
      have hpt (x : V) : h x * conj (g x) = ((χ x * ‖h x‖ ^ p : ℝ) : ℂ) := by
        have h2 : ‖h x‖ ^ (p - 2) * ‖h x‖ ^ 2 = ‖h x‖ ^ p := by
          rw [← Real.rpow_natCast, ← Real.rpow_add' (norm_nonneg _) (by norm_num; linarith)]
          norm_num
        calc h x * conj (g x) = (χ x : ℂ) * ((‖h x‖ ^ (p - 2) : ℝ) : ℂ) * (h x * conj (h x)) := by
              simp only [g, map_mul, Complex.conj_ofReal]
              ring
          _ = _ := by
              rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, ← h2, Complex.ofReal_mul,
                Complex.ofReal_mul]
              ring
      simp_rw [hpt, integral_complex_ofReal]
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (integral_nonneg hnn)]
      exact ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ hnn)
    have hJ : J ≠ ⊤ := hpair ▸ eNorm_ne_top
    have hnormg : eLpNorm g (ENNReal.ofReal q) μ ≤ J ^ (1 / q) := by
      rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hQ0 ENNReal.ofReal_ne_top
        hgc.aestronglyMeasurable, ENNReal.toReal_ofReal (by linarith)]
      refine ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by positivity)
      rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by linarith)]
      apply ENNReal.ofReal_le_ofReal
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg χ.nonneg, norm_rpow_sub_two_mul hp,
        Real.mul_rpow χ.nonneg (by positivity), ← Real.rpow_mul (norm_nonneg _),
        hpq.sub_one_mul_conj]
      gcongr
      calc χ x ^ q ≤ χ x ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_ge' χ.nonneg χ.le_one zero_le_one hq1.le
        _ = χ x := Real.rpow_one _
    have hJA : J ≤ A ^ p := le_rpow_of_le_mul_rpow hpq hJ <| by
      calc J = ‖∫ x, h x * conj (g x) ∂μ‖ₑ := hpair.symm
        _ ≤ A * eLpNorm g (ENNReal.ofReal q) μ := H' g hgc hgs
        _ ≤ A * J ^ (1 / q) := by gcongr
    refine le_trans (lintegral_mono fun x => ?_) hJA
    by_cases hx : x ∈ closedBall (0 : V) (N + 1)
    · rw [Set.indicator_of_mem hx, χ.one_of_mem_closedBall hx, one_mul, ← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp0.le]
    · rw [Set.indicator_of_notMem hx]
      exact zero_le
  -- monotone convergence over the balls
  have hmeas : Measurable fun x => ‖h x‖ₑ ^ p := hh.measurable.eNorm.pow_const _
  have hmono : Monotone fun N : ℕ =>
      (closedBall (0 : V) (N + 1)).indicator (fun x => ‖h x‖ₑ ^ p) := by
    intro N M hNM
    exact Set.indicator_le_indicator_of_subset
      (closedBall_subset_closedBall (by gcongr)) (fun _ => zero_le)
  have hsup (x : V) : ‖h x‖ₑ ^ p =
      ⨆ N : ℕ, (closedBall (0 : V) (N + 1)).indicator (fun x => ‖h x‖ₑ ^ p) x := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
    refine le_antisymm (le_iSup_of_le N ?_) (iSup_le fun N => Set.indicator_le_self _ _ x)
    rw [Set.indicator_of_mem (mem_closedBall_zero_iff.2 (by linarith))]
  have hlint : ∫⁻ x, ‖h x‖ₑ ^ p ∂μ ≤ A ^ p := by
    calc ∫⁻ x, ‖h x‖ₑ ^ p ∂μ
        = ∫⁻ x, ⨆ N : ℕ, (closedBall (0 : V) (N + 1)).indicator (fun x => ‖h x‖ₑ ^ p) x ∂μ :=
          lintegral_congr hsup
      _ = ⨆ N : ℕ, ∫⁻ x, (closedBall (0 : V) (N + 1)).indicator (fun x => ‖h x‖ₑ ^ p) x ∂μ :=
          lintegral_iSup (fun N => hmeas.indicator measurableSet_closedBall) hmono
      _ ≤ A ^ p := iSup_le hball
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by simpa using hp0) ENNReal.ofReal_ne_top
    hh.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le, one_div, ENNReal.rpow_inv_le_iff hp0]
  exact hlint

end HarmonicAnalysis
