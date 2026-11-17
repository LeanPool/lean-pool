/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.VectorItoFormula
public import LeanPool.KLS.LevyStochCalc.Brownian.SmoothCutoff
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoLocality
public import LeanPool.KLS.LevyStochCalc.Probability.ExitTime

/-!
# Itô's formula for a twice continuously differentiable function

Multiplying `f` by a smooth box cutoff leaves it, together with its first two derivatives,
unchanged on a cube and makes them bounded and uniformly continuous. Along a path stopped before
it leaves that cube the two functions therefore give the same integrands, and the local property
of the Itô integral transfers the stochastic terms.

## Main statements

* `LevyStochCalc.cutoffFun` — the cut-off function.
* `LevyStochCalc.fderiv_cutoffFun` — its first two derivatives agree with `f`'s on the cube.
* `LevyStochCalc.Brownian.Ito.IsVectorItoVersion.itoFormula_of_contDiff` — Itô's formula for a
  twice continuously differentiable function, with no bound on its derivatives.
-/

@[expose] public section

namespace LevyStochCalc

open scoped Topology

section Cutoff

variable {n : ℕ}

/-- The product of `f` with the smooth box cutoff of radius `k`. -/
noncomputable def cutoffFun (f : (Fin n → ℝ) → ℝ) (k : ℝ) : (Fin n → ℝ) → ℝ :=
  fun z => f z * boxCut k z

theorem contDiff_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    ContDiff ℝ 2 (cutoffFun f k) :=
  hf.mul (contDiff_boxCut (n := n) k)

theorem hasCompactSupport_cutoffFun (f : (Fin n → ℝ) → ℝ) {k : ℝ} (hk : 0 < k) :
    HasCompactSupport (cutoffFun f k) :=
  (hasCompactSupport_boxCut (n := n) hk).mul_left

theorem cutoffFun_eventuallyEq {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : ‖z‖ < 3 * k / 2) : cutoffFun f k =ᶠ[𝓝 z] f := by
  filter_upwards [boxCut_eventuallyEq_one (n := n) hk hz] with w hw
  simp [cutoffFun, hw]

theorem fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : ‖z‖ < 3 * k / 2) : fderiv ℝ (cutoffFun f k) z = fderiv ℝ f z :=
  (cutoffFun_eventuallyEq hk hz).fderiv_eq

theorem fderiv_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : ‖z‖ < 3 * k / 2) :
    fderiv ℝ (fderiv ℝ (cutoffFun f k)) z = fderiv ℝ (fderiv ℝ f) z := by
  have hopen : IsOpen {w : Fin n → ℝ | ‖w‖ < 3 * k / 2} :=
    isOpen_lt continuous_norm continuous_const
  have hev : fderiv ℝ (cutoffFun f k) =ᶠ[𝓝 z] fderiv ℝ f := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact fderiv_cutoffFun hk hw
  exact hev.fderiv_eq

theorem continuous_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Continuous (fderiv ℝ (cutoffFun f k)) :=
  ((contDiff_cutoffFun hf k).fderiv_right (m := 1) (by norm_num)).continuous

theorem continuous_fderiv_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Continuous (fderiv ℝ (fderiv ℝ (cutoffFun f k))) :=
  (((contDiff_cutoffFun hf k).fderiv_right (m := 1) (by norm_num)).fderiv_right
    (m := 0) (by norm_num)).continuous

theorem differentiable_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Differentiable ℝ (cutoffFun f k) :=
  (contDiff_cutoffFun hf k).differentiable (by norm_num)

theorem differentiable_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Differentiable ℝ (fderiv ℝ (cutoffFun f k)) :=
  ((contDiff_cutoffFun hf k).fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)

theorem cutoffFun_eventuallyEq_zero {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : 2 * k < ‖z‖) : cutoffFun f k =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
  have hopen : IsOpen {w : Fin n → ℝ | 2 * k < ‖w‖} :=
    isOpen_lt continuous_const continuous_norm
  filter_upwards [hopen.mem_nhds hz] with w hw
  simp [cutoffFun, boxCut_eq_zero hk hw]

theorem fderiv_cutoffFun_eq_zero {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k) {z : Fin n → ℝ}
    (hz : 2 * k < ‖z‖) : fderiv ℝ (cutoffFun f k) z = 0 := by
  rw [(cutoffFun_eventuallyEq_zero (f := f) hk hz).fderiv_eq]
  simp

theorem fderiv_fderiv_cutoffFun_eq_zero {f : (Fin n → ℝ) → ℝ} {k : ℝ} (hk : 0 < k)
    {z : Fin n → ℝ} (hz : 2 * k < ‖z‖) : fderiv ℝ (fderiv ℝ (cutoffFun f k)) z = 0 := by
  have hopen : IsOpen {w : Fin n → ℝ | 2 * k < ‖w‖} :=
    isOpen_lt continuous_const continuous_norm
  have hev : fderiv ℝ (cutoffFun f k) =ᶠ[𝓝 z] fun _ => (0 : (Fin n → ℝ) →L[ℝ] ℝ) := by
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact fderiv_cutoffFun_eq_zero (f := f) hk hw
  rw [hev.fderiv_eq]
  simp

/-- The coordinates of the first derivative, as a vector. -/
noncomputable def gradVec (g : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) : Fin n → ℝ :=
  fun p => fderiv ℝ g z (Pi.single p 1)

/-- The coordinates of the second derivative, as a vector. -/
noncomputable def hessVec (g : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) : Fin n × Fin n → ℝ :=
  fun pq => fderiv ℝ (fderiv ℝ g) z (Pi.single pq.1 1) (Pi.single pq.2 1)

theorem continuous_gradVec {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Continuous (gradVec (cutoffFun f k)) :=
  continuous_pi fun _ => (continuous_fderiv_cutoffFun hf k).clm_apply continuous_const

theorem continuous_hessVec {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (k : ℝ) :
    Continuous (hessVec (cutoffFun f k)) :=
  continuous_pi fun _ =>
    ((continuous_fderiv_fderiv_cutoffFun hf k).clm_apply continuous_const).clm_apply
      continuous_const

theorem hasCompactSupport_gradVec (f : (Fin n → ℝ) → ℝ) {k : ℝ} (hk : 0 < k) :
    HasCompactSupport (gradVec (cutoffFun f k)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (2 * k)) fun z hz => ?_
  have hz' : 2 * k < ‖z‖ := by
    by_contra hcon
    exact hz (by simpa [Metric.mem_closedBall, dist_eq_norm] using not_lt.mp hcon)
  funext p
  simp [gradVec, fderiv_cutoffFun_eq_zero (f := f) hk hz']

theorem hasCompactSupport_hessVec (f : (Fin n → ℝ) → ℝ) {k : ℝ} (hk : 0 < k) :
    HasCompactSupport (hessVec (cutoffFun f k)) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : Fin n → ℝ) (2 * k)) fun z hz => ?_
  have hz' : 2 * k < ‖z‖ := by
    by_contra hcon
    exact hz (by simpa [Metric.mem_closedBall, dist_eq_norm] using not_lt.mp hcon)
  funext pq
  simp [hessVec, fderiv_fderiv_cutoffFun_eq_zero (f := f) hk hz']

theorem exists_bound_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {k : ℝ}
    (hk : 0 < k) : ∃ K₁ : ℝ, ∀ z, ‖fderiv ℝ (cutoffFun f k) z‖ ≤ K₁ := by
  obtain ⟨M, hM⟩ := (hasCompactSupport_gradVec f hk).exists_bound_of_continuous
    (continuous_gradVec hf k)
  refine ⟨(n : ℝ) * M, fun z => ?_⟩
  refine (norm_le_sum_abs_apply (fderiv ℝ (cutoffFun f k) z)).trans ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      |fderiv ℝ (cutoffFun f k) z (Pi.single p 1)| ≤ M := by
    intro p _
    have := norm_le_pi_norm (gradVec (cutoffFun f k) z) p
    have h2 := hM z
    simp only [gradVec, Real.norm_eq_abs] at this
    linarith
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem exists_bound_fderiv_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {k : ℝ}
    (hk : 0 < k) :
    ∃ K₂ : ℝ, 0 ≤ K₂ ∧ ∀ z, ‖fderiv ℝ (fderiv ℝ (cutoffFun f k)) z‖ ≤ K₂ := by
  obtain ⟨M, hM⟩ := (hasCompactSupport_hessVec f hk).exists_bound_of_continuous
    (continuous_hessVec hf k)
  have hM0 : (0 : ℝ) ≤ M := le_trans (norm_nonneg _) (hM 0)
  refine ⟨(n : ℝ) * ((n : ℝ) * M), by positivity, fun z => ?_⟩
  refine (norm_le_sum_abs_apply₂ (fderiv ℝ (fderiv ℝ (cutoffFun f k)) z)).trans ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      (∑ q, |fderiv ℝ (fderiv ℝ (cutoffFun f k)) z (Pi.single p 1) (Pi.single q 1)|)
        ≤ (n : ℝ) * M := by
    intro p _
    have hq : ∀ q ∈ (Finset.univ : Finset (Fin n)),
        |fderiv ℝ (fderiv ℝ (cutoffFun f k)) z (Pi.single p 1) (Pi.single q 1)| ≤ M := by
      intro q _
      have h1 := norm_le_pi_norm (hessVec (cutoffFun f k) z) (p, q)
      have h2 := hM z
      simp only [hessVec, Real.norm_eq_abs] at h1
      linarith
    refine (Finset.sum_le_sum hq).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem exists_delta_fderiv_fderiv_cutoffFun {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) {k : ℝ}
    (hk : 0 < k) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z w : Fin n → ℝ, ‖z - w‖ < δ →
      ‖fderiv ℝ (fderiv ℝ (cutoffFun f k)) z - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w‖ ≤ ε := by
  have hpos : (0 : ℝ) < ε / ((n : ℝ) * (n : ℝ) + 1) := by positivity
  obtain ⟨δ, hδ0, hδ⟩ := exists_delta_of_hasCompactSupport (continuous_hessVec hf k)
    (hasCompactSupport_hessVec f hk) hpos
  refine ⟨δ, hδ0, fun z w hzw => ?_⟩
  set c : ℝ := ε / ((n : ℝ) * (n : ℝ) + 1) with hc
  have hcnn : (0 : ℝ) ≤ c := hpos.le
  have hcoord : ∀ p q : Fin n,
      |fderiv ℝ (fderiv ℝ (cutoffFun f k)) z (Pi.single p 1) (Pi.single q 1)
        - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w (Pi.single p 1) (Pi.single q 1)| ≤ c := by
    intro p q
    have h1 := norm_le_pi_norm
      (hessVec (cutoffFun f k) z - hessVec (cutoffFun f k) w) (p, q)
    have h2 := hδ z w hzw
    simp only [Pi.sub_apply, hessVec, Real.norm_eq_abs] at h1
    linarith
  have hsub : fderiv ℝ (fderiv ℝ (cutoffFun f k)) z - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w
      = (fderiv ℝ (fderiv ℝ (cutoffFun f k)) z - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w) := rfl
  refine (norm_le_sum_abs_apply₂
    (fderiv ℝ (fderiv ℝ (cutoffFun f k)) z - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w)).trans ?_
  have hterm : ∀ p ∈ (Finset.univ : Finset (Fin n)),
      (∑ q, |(fderiv ℝ (fderiv ℝ (cutoffFun f k)) z
          - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w) (Pi.single p 1) (Pi.single q 1)|)
        ≤ (n : ℝ) * c := by
    intro p _
    have hq : ∀ q ∈ (Finset.univ : Finset (Fin n)),
        |(fderiv ℝ (fderiv ℝ (cutoffFun f k)) z
          - fderiv ℝ (fderiv ℝ (cutoffFun f k)) w) (Pi.single p 1) (Pi.single q 1)| ≤ c := by
      intro q _
      simpa using hcoord p q
    refine (Finset.sum_le_sum hq).trans (le_of_eq ?_)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hc]
  have hd : (0 : ℝ) < (n : ℝ) * (n : ℝ) + 1 := by positivity
  have hrw : (n : ℝ) * ((n : ℝ) * (ε / ((n : ℝ) * (n : ℝ) + 1)))
      = (n : ℝ) * (n : ℝ) * ε / ((n : ℝ) * (n : ℝ) + 1) := by ring
  rw [hrw, div_le_iff₀ hd]
  nlinarith [hε.le]

end Cutoff

namespace Brownian.Ito

open MeasureTheory ProbabilityTheory LevyStochCalc.Brownian.Multidim LevyStochCalc.Probability
open scoped NNReal ENNReal

universe u

section Bounded

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- A pointwise bounded integrand has finite energy on every window. -/
theorem energy_lt_top_of_bounded {K : Ω → ℝ → ℝ} {M : ℝ} (hM : ∀ ω s, |K ω s| ≤ M) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T _hT
  have hpt : ∀ (ω : Ω) (s : ℝ),
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ≤ ((Real.toNNReal M : ℝ≥0) : ℝ≥0∞) ^ 2 := by
    intro ω s
    have h0 : (0 : ℝ) ≤ M := le_trans (abs_nonneg _) (hM ω s)
    have h1 : ‖K ω s‖₊ ≤ Real.toNNReal M := by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal M h0]
      simpa [Real.norm_eq_abs] using hM ω s
    exact pow_le_pow_left' (by exact_mod_cast h1) 2
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ _ω : Ω, ∫⁻ _s in Set.Icc (0 : ℝ) T,
          ((Real.toNNReal M : ℝ≥0) : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω => MeasureTheory.lintegral_mono fun s => hpt ω s
    _ < ⊤ := by
        simp only [MeasureTheory.lintegral_const, MeasureTheory.Measure.restrict_apply_univ,
          Real.volume_Icc, measure_univ, mul_one]
        exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top) ENNReal.ofReal_lt_top

omit [IsProbabilityMeasure P] in
/-- A pointwise bound `|u| ≤ c|v|` squares into a bound on the extended norms. -/
theorem sq_enorm_le_of_abs_le {c : ℝ} (hc : 0 ≤ c) {u v : ℝ} (h : |u| ≤ c * |v|) :
    (‖u‖₊ : ℝ≥0∞) ^ 2 ≤ ENNReal.ofReal (c ^ 2) * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
  have h1 : ‖u‖₊ ≤ Real.toNNReal c * ‖v‖₊ := by
    rw [← NNReal.coe_le_coe]
    push_cast
    rw [Real.coe_toNNReal c hc]
    simpa [Real.norm_eq_abs] using h
  calc (‖u‖₊ : ℝ≥0∞) ^ 2 ≤ ((Real.toNNReal c * ‖v‖₊ : ℝ≥0) : ℝ≥0∞) ^ 2 := by
        exact pow_le_pow_left' (by exact_mod_cast h1) 2
    _ = ENNReal.ofReal (c ^ 2) * (‖v‖₊ : ℝ≥0∞) ^ 2 := by
        rw [ENNReal.coe_mul, mul_pow, ← ENNReal.coe_pow, ← Real.toNNReal_pow hc]
        rfl

omit [IsProbabilityMeasure P] in
/-- The energy of an integrand dominated by a multiple of another one is finite whenever the
dominating integrand's is. -/
theorem energy_lt_top_of_abs_le_mul {K G : Ω → ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hbd : ∀ (ω : Ω) (s : ℝ), |K ω s| ≤ c * |G ω s|)
    (hG : ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T : ℝ, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  calc ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P
      ≤ ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          ENNReal.ofReal (c ^ 2) * (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P :=
        MeasureTheory.lintegral_mono fun ω =>
          MeasureTheory.lintegral_mono fun s => sq_enorm_le_of_abs_le hc (hbd ω s)
    _ = ENNReal.ofReal (c ^ 2) * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
          (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P := by
        simp only [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hG T hT)

end Bounded

section Formula

open LevyStochCalc.Brownian.Multidim

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {n d : ℕ} {W : Multidim.MultidimBrownianMotion P d}
  {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
  {hcoord : ∀ k : Fin d, IsBrownianFiltration (W.W k) ℱ}
  {H : Fin n → Fin d → Ω → ℝ → ℝ}
  {hHm : ∀ p k, Measurable (Function.uncurry (H p k))}
  {hHp : ∀ p k, Probability.ProgressivelyMeasurable ℱ (H p k)}
  {hHs : ∀ (p : Fin n) (k : Fin d) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
    (‖H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤}
  {X₀ : Ω → Fin n → ℝ} {bdrift : Fin n → Ω → ℝ → ℝ} {X : ℝ → Ω → Fin n → ℝ}
  {C : ℝ} (hC0 : 0 ≤ C)
  (hCH : ∀ (p : Fin n) (k : Fin d) (ω : Ω) (s : ℝ), |H p k ω s| ≤ C)

/-- **The localisation step of Itô's formula.** The formula for a `C²` function follows from the
formula for functions with bounded first and second derivatives. -/
theorem IsVectorItoVersion.itoFormula_localise
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T)
    (hbase : ∀ (g : (Fin n → ℝ) → ℝ) (g' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ)
      (g'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ) (K₁ K₂ : ℝ),
      (∀ z, HasFDerivAt g (g' z) z) → (∀ z, HasFDerivAt g' (g'' z) z) →
      (∀ z, ‖g' z‖ ≤ K₁) → 0 ≤ K₂ → (∀ z, ‖g'' z‖ ≤ K₂) →
      Continuous g' → Continuous g'' →
      (∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ z w : Fin n → ℝ, ‖z - w‖ < δ → ‖g'' z - g'' w‖ ≤ ε) →
      ∀ (hmG : ∀ (p : Fin n) (k : Fin d), Measurable (Function.uncurry
          fun ω s => coordDeriv g' p (X s ω) * H p k ω s))
        (hpG : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
          fun ω s => coordDeriv g' p (X s ω) * H p k ω s)
        (hqG : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' →
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
            (‖coordDeriv g' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤),
      (fun ω : Ω => g (X T ω) - g (X 0 ω)) =ᵐ[P] fun ω : Ω =>
        (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv g' p (X s ω) * bdrift p ω s ∂volume)
          + (∑ p : Fin n, ∑ k : Fin d, stochasticIntegralBrownian (W.W k) ℱ (hcoord k)
              (fun ω s => coordDeriv g' p (X s ω) * H p k ω s)
              (hmG p k) (hpG p k) (hqG p k) T ω)
          + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
              coordDeriv₂ g'' p q (X s ω) * ∑ k : Fin d, H p k ω s * H q k ω s ∂volume) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
            (hmg p j) (hpg p j) (hqg p j) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by
  classical
  have hf'eq : f' = fderiv ℝ f := funext fun z => (hf z).fderiv.symm
  have hf''eq : f'' = fderiv ℝ (fderiv ℝ f) := by
    funext z
    have hz := (hf' z).fderiv
    rw [← hf'eq]
    exact hz.symm
  have hstep : ∀ m : ℕ, 0 < m → ∀ᵐ ω ∂P,
      ((T : ℝ) : WithTop ℝ) < Probability.exitTime (fun ω t => X t ω) (m : ℝ) ω →
        f (X T ω) - f (X 0 ω)
          = (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
                (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
                (hmg p j) (hpg p j) (hqg p j) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ f'' p q (X s ω)
                  * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by
    intro m hm0
    have hR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
    set R : ℝ := (m : ℝ) with hRdef
    set g : (Fin n → ℝ) → ℝ := cutoffFun f R with hgdef
    set τ : Ω → WithTop ℝ := Probability.exitTime (fun ω t => X t ω) R with hτdef
    have hadapt : MeasureTheory.Adapted ℱ (fun r ω => X r ω) :=
      fun r => (h.adapted r).measurable
    have hτ : MeasureTheory.IsStoppingTime ℱ τ :=
      Probability.isStoppingTime_exitTime (X := fun ω t => X t ω) hadapt
        (fun ω => h.continuous_path ω) R
    have hR32 : R < 3 * R / 2 := by linarith
    have hg'c : Continuous (fderiv ℝ g) := continuous_fderiv_cutoffFun hfC R
    have hg''c : Continuous (fderiv ℝ (fderiv ℝ g)) := continuous_fderiv_fderiv_cutoffFun hfC R
    have hgf : ∀ z, HasFDerivAt g (fderiv ℝ g z) z :=
      fun z => (differentiable_cutoffFun hfC R z).hasFDerivAt
    have hgf' : ∀ z, HasFDerivAt (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g) z) z :=
      fun z => (differentiable_fderiv_cutoffFun hfC R z).hasFDerivAt
    obtain ⟨K₁, hK₁⟩ := exists_bound_fderiv_cutoffFun hfC hR
    obtain ⟨K₂, hK₂0, hK₂⟩ := exists_bound_fderiv_fderiv_cutoffFun hfC hR
    have hK₁0 : (0 : ℝ) ≤ K₁ := le_trans (norm_nonneg _) (hK₁ 0)
    have hunif : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
        ∀ z w : Fin n → ℝ, ‖z - w‖ < δ →
          ‖fderiv ℝ (fderiv ℝ g) z - fderiv ℝ (fderiv ℝ g) w‖ ≤ ε :=
      fun ε hε => exists_delta_fderiv_fderiv_cutoffFun hfC hR hε
    -- the two families of integrands agree on the cube
    have hd1 : ∀ (p : Fin n) (z : Fin n → ℝ), ‖z‖ < 3 * R / 2 →
        coordDeriv (fderiv ℝ g) p z = coordDeriv f' p z := by
      intro p z hz
      rw [hf'eq]
      unfold coordDeriv
      rw [fderiv_cutoffFun (f := f) hR hz]
    have hd2 : ∀ (p q : Fin n) (z : Fin n → ℝ), ‖z‖ < 3 * R / 2 →
        coordDeriv₂ (fderiv ℝ (fderiv ℝ g)) p q z = coordDeriv₂ f'' p q z := by
      intro p q z hz
      rw [hf''eq]
      unfold coordDeriv₂
      rw [fderiv_fderiv_cutoffFun (f := f) hR hz]
    have hd0 : ∀ z : Fin n → ℝ, ‖z‖ < 3 * R / 2 → g z = f z := by
      intro z hz
      rw [hgdef, cutoffFun, boxCut_eq_one hR hz.le, mul_one]
    -- the cut integrands
    have hmgG : ∀ (p : Fin n) (j : Fin d),
        Measurable (Function.uncurry fun ω s =>
          coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s) :=
      fun p j =>
        (h.measurable_uncurry_comp (continuous_coordDeriv hg'c p).measurable).mul (hHm p j)
    have hpgG : ∀ (p : Fin n) (j : Fin d), Probability.ProgressivelyMeasurable ℱ
        fun ω s => coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s :=
      fun p j => (h.progressivelyMeasurable_comp (continuous_coordDeriv hg'c p)).mul (hHp p j)
    have hqgG : ∀ (p : Fin n) (j : Fin d) (T' : ℝ), 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
      intro p j
      refine energy_lt_top_of_abs_le_mul (c := K₁) hK₁0 (fun ω s => ?_) (hHs p j)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (abs_coordDeriv_le hK₁ p _) (abs_nonneg _)
    have hform := hbase g (fderiv ℝ g) (fderiv ℝ (fderiv ℝ g)) K₁ K₂ hgf hgf' hK₁ hK₂0 hK₂
      hg'c hg''c hunif hmgG hpgG hqgG
    have hSI : ∀ᵐ ω ∂P, ∀ (p : Fin n) (j : Fin d), ((T : ℝ) : WithTop ℝ) ≤ τ ω →
        stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s)
            (hmgG p j) (hpgG p j) (hqgG p j) T ω
          = stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
            (hmg p j) (hpg p j) (hqg p j) T ω := by
      rw [MeasureTheory.ae_all_iff]
      intro p
      rw [MeasureTheory.ae_all_iff]
      intro j
      refine stochasticIntegralBrownian_congr_of_le τ (W.W j) ℱ (hcoord j) hτ
        (hmgG p j) (hpgG p j) (hqgG p j) (hmg p j) (hpg p j) (hqg p j) (fun ω s hs hle => ?_) hT
      have hnorm : ‖X s ω‖ ≤ R :=
        Probability.norm_le_of_le_exitTime (h.continuous_path ω) hs hle
      rw [hd1 p (X s ω) (lt_of_le_of_lt hnorm hR32)]
    filter_upwards [hform, hSI] with ω hω hSIω hlt
    have hball : ∀ s ∈ Set.Icc (0 : ℝ) T, ‖X s ω‖ < R := by
      intro s hs
      by_contra hcon
      have hmem : ∃ u ∈ Set.Icc (0 : ℝ) T, R ≤ ‖X u ω‖ := ⟨s, hs, not_lt.mp hcon⟩
      have := (Probability.exitTime_le_iff (X := fun ω t => X t ω)
        (h.continuous_path ω) R T).2 hmem
      exact absurd this (not_le.mpr hlt)
    have hballs : ∀ s ∈ Set.Ioc (0 : ℝ) T, ‖X s ω‖ < 3 * R / 2 := fun s hs =>
      lt_trans (hball s ⟨hs.1.le, hs.2⟩) hR32
    have hT' : ‖X T ω‖ < 3 * R / 2 :=
      lt_trans (hball T ⟨hT.le, le_rfl⟩) hR32
    have h0' : ‖X 0 ω‖ < 3 * R / 2 :=
      lt_trans (hball 0 ⟨le_rfl, hT.le⟩) hR32
    have hleτ : ((T : ℝ) : WithTop ℝ) ≤ τ ω := le_of_lt hlt
    have e1 : (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv (fderiv ℝ g) p (X s ω) * bdrift p ω s ∂volume)
        = ∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume := by
      refine Finset.sum_congr rfl fun p _ => ?_
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      rw [hd1 p (X s ω) (hballs s hs)]
    have e2 : (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => coordDeriv (fderiv ℝ g) p (X s ω) * H p j ω s)
            (hmgG p j) (hpgG p j) (hqgG p j) T ω)
        = ∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
            (hmg p j) (hpg p j) (hqg p j) T ω :=
      Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun j _ => hSIω p j hleτ
    have e3 : (1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ (fderiv ℝ (fderiv ℝ g)) p q (X s ω)
              * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume)
        = 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω)
              * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by
      refine congrArg (fun x => 1 / 2 * x) ?_
      refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
      rw [hd2 p q (X s ω) (hballs s hs)]
    rw [← hd0 _ hT', ← hd0 _ h0', hω, e1, e2, e3]
  have hall : ∀ᵐ ω ∂P, ∀ m : ℕ, 0 < m →
      ((T : ℝ) : WithTop ℝ) < Probability.exitTime (fun ω t => X t ω) (m : ℝ) ω →
        f (X T ω) - f (X 0 ω)
          = (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
            + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
                (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
                (hmg p j) (hpg p j) (hqg p j) T ω)
            + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
                coordDeriv₂ f'' p q (X s ω)
                  * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume := by
    rw [MeasureTheory.ae_all_iff]
    intro m
    by_cases hm : 0 < m
    · filter_upwards [hstep m hm] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω hcon => absurd hcon hm
  filter_upwards [hall] with ω hω
  obtain ⟨K, hK⟩ := Probability.exists_lt_exitTime (X := fun ω t => X t ω)
    (h.continuous_path ω) hT.le
  exact hω (max K 1) (lt_of_lt_of_le Nat.zero_lt_one (le_max_right K 1))
    (hK (max K 1) (le_max_left K 1))

include hC0 hCH in
/-- **Itô's formula for a twice continuously differentiable function of a vector Itô process.**
No bound is placed on the derivatives of `f`. -/
theorem IsVectorItoVersion.itoFormula_of_contDiff
    (h : IsVectorItoVersion W ℱ hcoord H hHm hHp hHs X₀ bdrift X)
    (hX₀ : ∀ p : Fin n, Measurable fun ω => X₀ ω p)
    (hbm : ∀ p, Measurable (Function.uncurry (bdrift p))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ (p : Fin n) (ω : Ω) (s : ℝ), |bdrift p ω s| ≤ B)
    (hma : ∀ (p q : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => H p k ω s + H q k ω s))
    (hpa : ∀ (p q : Fin n) (k : Fin d),
      Probability.ProgressivelyMeasurable ℱ fun ω s => H p k ω s + H q k ω s)
    (hqa : ∀ (p q : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖H p k ω s + H q k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {f : (Fin n → ℝ) → ℝ} {f' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] ℝ}
    {f'' : (Fin n → ℝ) → (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) →L[ℝ] ℝ}
    (hfC : ContDiff ℝ 2 f)
    (hf : ∀ z, HasFDerivAt f (f' z) z) (hf' : ∀ z, HasFDerivAt f' (f'' z) z)
    (hmg : ∀ (p : Fin n) (k : Fin d),
      Measurable (Function.uncurry fun ω s => coordDeriv f' p (X s ω) * H p k ω s))
    (hpg : ∀ (p : Fin n) (k : Fin d), Probability.ProgressivelyMeasurable ℱ
      fun ω s => coordDeriv f' p (X s ω) * H p k ω s)
    (hqg : ∀ (p : Fin n) (k : Fin d) (T' : ℝ), 0 < T' → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
      (‖coordDeriv f' p (X s ω) * H p k ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {T : ℝ} (hT : 0 < T) :
    (fun ω : Ω => f (X T ω) - f (X 0 ω)) =ᵐ[P] fun ω : Ω =>
      (∑ p : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
          coordDeriv f' p (X s ω) * bdrift p ω s ∂volume)
        + (∑ p : Fin n, ∑ j : Fin d, stochasticIntegralBrownian (W.W j) ℱ (hcoord j)
            (fun ω s => coordDeriv f' p (X s ω) * H p j ω s)
            (hmg p j) (hpg p j) (hqg p j) T ω)
        + 1 / 2 * ∑ p : Fin n, ∑ q : Fin n, ∫ s in Set.Ioc (0 : ℝ) T,
            coordDeriv₂ f'' p q (X s ω) * ∑ j : Fin d, H p j ω s * H q j ω s ∂volume :=
  h.itoFormula_localise hfC hf hf' hmg hpg hqg hT
    (fun _g _g' _g'' _K₁ _K₂ hgf hgf' hK₁ hK₂0 hK₂ _hg'c hg''c hunif hmG hpG hqG =>
      h.itoFormula hC0 hCH hX₀ hbm hB0 hB hma hpa hqa hgf hgf' hK₁ hK₂0 hK₂ hg''c hunif
        hmG hpG hqG hT)

end Formula

end Brownian.Ito


end LevyStochCalc
