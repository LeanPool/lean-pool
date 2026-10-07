/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.BarrierSupport
public import LeanPool.CIVAxisymmetric.Comparison.CommutatorL2
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The energy of `(q_ε - Ψ_σ)_+` and the Grönwall step of `lem:aniso:comparison`

The comparison argument for `eq:aniso:comparison:equation` tests the mollified equation
`eq:aniso:comparison:mollified` against the positive part

`v_ε = (q_ε - Ψ_σ)_+`

of the excess over the linearly growing barrier `eq:aniso:comparison:barrier`, and follows the
energy

`E(τ) = ∫ v_ε(x, τ)² dx`.

This module supplies three groups of facts.

* **Support and integrability.** For `τ ≥ τ₀` the function `v_ε(·, τ)` vanishes wherever
  `‖x‖ ≥ M_∞/σ`, so it is a continuous function with compact support and `E(τ)` is an honest
  integral over `closedBall 0 (M_∞/σ)`. At the initial time `E(τ₀) = 0`, because the barrier
  dominates `M ≥ ‖q(·, τ₀)‖_{L^∞}` there.

* **The two right-hand terms of `eq:aniso:comparison:positive:energy`.** The drift term
  `∫ (div B) v_ε²` is bounded by `Λ E(τ)` whenever `|div B| ≤ Λ`, and the commutator term
  `∫ R_ε v_ε` is bounded by `‖R_ε‖_{L²(B_{R_σ})} √(E(τ))` by Cauchy–Schwarz, the integral over
  `ℝ^m` reducing to one over `closedBall 0 (M_∞/σ)` by the support statement. The commutator
  of `eq:aniso:comparison:mollified` is square integrable on that ball, so the bound is not
  vacuous.

* **Grönwall in integral form.** If a continuous `y ≥ 0` satisfies
  `y(t) ≤ ∫_a^t (Λ y + 2 √y r)` on `[a, b]`, then
  `y(t) ≤ (∫_a^b r²) exp((Λ + 1)(b - a))` there. The proof absorbs `2 √y r ≤ y + r²` and then
  runs the integral-form Grönwall inequality `le_mul_exp_of_le_primitive`, which is proved by
  the fencing theorem applied to `t ↦ (c + Λ ∫_a^t y) exp(-Λ(t - a))`.

The integrated energy inequality itself — the passage from `eq:aniso:comparison:mollified` to
`eq:aniso:comparison:positive:energy` — is not proved here; the last statement consumes it as a
hypothesis in exactly the integrated form that the Grönwall step needs.
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV

/-! ### The excess over the barrier and its energy -/

/-- The positive part `v_ε = (q_ε - Ψ_σ)_+` of the excess of the mollified slice over the
barrier `eq:aniso:comparison:barrier`. -/
@[expose] def comparisonPosPart (m : ℕ) (ε M σ K τ₀ : ℝ) (q : Vec m × ℝ → ℝ) (z : Vec m × ℝ) : ℝ :=
  max (mollifySlice m ε q z - barrier m M σ K τ₀ z) 0

/-- The energy `E(τ) = ∫ v_ε(x, τ)² dx` of `eq:aniso:comparison:positive:energy`. -/
@[expose] def comparisonEnergy (m : ℕ) (ε M σ K τ₀ : ℝ) (q : Vec m × ℝ → ℝ) (τ : ℝ) : ℝ :=
  ∫ x, comparisonPosPart m ε M σ K τ₀ q (x, τ) ^ 2

theorem comparisonPosPart_nonneg {m : ℕ} (ε M σ K τ₀ : ℝ) (q : Vec m × ℝ → ℝ)
    (z : Vec m × ℝ) : 0 ≤ comparisonPosPart m ε M σ K τ₀ q z := le_max_right _ _

/-- Outside a closed ball the norm is at least the radius. -/
theorem le_norm_of_notMem_closedBall {m : ℕ} {R : ℝ} {x : Vec m}
    (hx : x ∉ Metric.closedBall (0 : Vec m) R) : R ≤ ‖x‖ := by
  have h := Metric.mem_closedBall.not.mp hx
  rw [dist_zero_right] at h
  exact le_of_lt (lt_of_not_ge h)

/-! ### Support and integrability -/

/-- For `τ ≥ τ₀` the excess vanishes off the ball of radius `M_∞/σ`: this is the statement
that `v_ε` is compactly supported in `x`, uniformly on `[τ₀, τ₊]`. -/
theorem comparisonPosPart_eq_zero_of_norm_ge {m : ℕ} {ε M σ K τ₀ τ Minf : ℝ} (hε : 0 < ε)
    (hσ : 0 < σ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hτ : τ₀ ≤ τ) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) (x : Vec m) (hx : Minf / σ ≤ ‖x‖) :
    comparisonPosPart m ε M σ K τ₀ q (x, τ) = 0 :=
  posPart_mollifySlice_sub_barrier_eq_zero hε hσ hK hM hτ hmeas hbdd x hx

/-- The excess is continuous in the spatial variable: the mollified slice is smooth and the
barrier is smooth. -/
theorem continuous_comparisonPosPart {m : ℕ} {ε Minf : ℝ} (hε : 0 < ε) (M σ K τ₀ τ : ℝ)
    {q : Vec m × ℝ → ℝ} (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) :
    Continuous fun x : Vec m => comparisonPosPart m ε M σ K τ₀ q (x, τ) := by
  have h1 : Continuous fun x : Vec m => mollifySlice m ε q (x, τ) :=
    (contDiff_mollifySlice hε τ q Minf hmeas hbdd).continuous
  have h2 : Continuous fun x : Vec m => barrier m M σ K τ₀ (x, τ) :=
    (contDiff_barrier M σ K τ₀).continuous.comp (continuous_id.prodMk continuous_const)
  exact (h1.sub h2).max continuous_const

theorem hasCompactSupport_comparisonPosPart {m : ℕ} {ε M σ K τ₀ τ Minf : ℝ} (hε : 0 < ε)
    (hσ : 0 < σ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hτ : τ₀ ≤ τ) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) :
    HasCompactSupport fun x : Vec m => comparisonPosPart m ε M σ K τ₀ q (x, τ) :=
  HasCompactSupport.intro (K := Metric.closedBall (0 : Vec m) (Minf / σ))
    (isCompact_closedBall _ _) fun x hx =>
      comparisonPosPart_eq_zero_of_norm_ge hε hσ hK hM hτ hmeas hbdd x
        (le_norm_of_notMem_closedBall hx)

theorem integrable_sq_comparisonPosPart {m : ℕ} {ε M σ K τ₀ τ Minf : ℝ} (hε : 0 < ε)
    (hσ : 0 < σ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hτ : τ₀ ≤ τ) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) :
    Integrable (fun x : Vec m => comparisonPosPart m ε M σ K τ₀ q (x, τ) ^ 2) volume := by
  have hcs : HasCompactSupport fun x : Vec m => comparisonPosPart m ε M σ K τ₀ q (x, τ) ^ 2 := by
    refine HasCompactSupport.intro (K := Metric.closedBall (0 : Vec m) (Minf / σ))
      (isCompact_closedBall _ _) fun x hx => ?_
    rw [comparisonPosPart_eq_zero_of_norm_ge hε hσ hK hM hτ hmeas hbdd x
      (le_norm_of_notMem_closedBall hx)]
    norm_num
  exact ((continuous_comparisonPosPart hε M σ K τ₀ τ hmeas hbdd).pow
    2).integrable_of_hasCompactSupport hcs

theorem comparisonEnergy_nonneg {m : ℕ} (ε M σ K τ₀ : ℝ) (q : Vec m × ℝ → ℝ) (τ : ℝ) :
    0 ≤ comparisonEnergy m ε M σ K τ₀ q τ :=
  integral_nonneg fun _ => sq_nonneg _

/-- The energy is an integral over the ball of radius `M_∞/σ`. -/
theorem comparisonEnergy_eq_setIntegral_closedBall {m : ℕ} {ε M σ K τ₀ τ Minf : ℝ} (hε : 0 < ε)
    (hσ : 0 < σ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hτ : τ₀ ≤ τ) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) :
    comparisonEnergy m ε M σ K τ₀ q τ
      = ∫ x in Metric.closedBall (0 : Vec m) (Minf / σ),
          comparisonPosPart m ε M σ K τ₀ q (x, τ) ^ 2 := by
  refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
  rw [comparisonPosPart_eq_zero_of_norm_ge hε hσ hK hM hτ hmeas hbdd x
    (le_norm_of_notMem_closedBall hx)]
  norm_num

/-- The energy vanishes at the initial time, because the barrier dominates the bound `M` on
the initial slice there. -/
theorem comparisonEnergy_eq_zero_of_slice_le {m : ℕ} {ε M σ K τ₀ : ℝ} (hε : 0 < ε)
    (hσ : 0 ≤ σ) (hK : 0 ≤ K) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ₀)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ₀)| ≤ M) :
    comparisonEnergy m ε M σ K τ₀ q τ₀ = 0 := by
  have hzero : ∀ x : Vec m, comparisonPosPart m ε M σ K τ₀ q (x, τ₀) ^ 2 = 0 := by
    intro x
    have habs : |mollifySlice m ε q (x, τ₀)| ≤ M := abs_mollifySlice_le hε hmeas hbdd x
    have hle : mollifySlice m ε q (x, τ₀) ≤ M := le_trans (le_abs_self _) habs
    have hbar : M + σ * ‖x‖ ≤ barrier m M σ K τ₀ (x, τ₀) :=
      le_barrier M K τ₀ τ₀ x hσ hK le_rfl
    have hnn : 0 ≤ σ * ‖x‖ := mul_nonneg hσ (norm_nonneg x)
    exact posPart_sq_le_of_le (by linarith only [hle, hbar, hnn])
  simp only [comparisonEnergy, hzero]
  exact integral_zero _ _

/-! ### Elementary inequalities behind the two right-hand terms -/

/-- The absorption inequality `2 √u v ≤ u + v²` for `u ≥ 0`. -/
theorem two_mul_sqrt_mul_le_add_sq {u v : ℝ} (hu : 0 ≤ u) :
    2 * Real.sqrt u * v ≤ u + v ^ 2 := by
  have h : 0 ≤ (Real.sqrt u - v) ^ 2 := sq_nonneg _
  have hs : Real.sqrt u ^ 2 = u := Real.sq_sqrt hu
  nlinarith only [h, hs]

/-- Cauchy–Schwarz in squared form: `(∫ f g)² ≤ (∫ f²)(∫ g²)`. -/
theorem sq_integral_mul_le_mul {α : Type*} [MeasurableSpace α] {μ : Measure α} {f g : α → ℝ}
    (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have hC : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have key : ∀ t : ℝ, 0 ≤ (∫ x, f x ^ 2 ∂μ) + 2 * t * (∫ x, f x * g x ∂μ)
      + t ^ 2 * ∫ x, g x ^ 2 ∂μ := by
    intro t
    have hpt : ∀ x, (f x + t * g x) ^ 2
        = f x ^ 2 + 2 * t * (f x * g x) + t ^ 2 * g x ^ 2 := by
      intro x; ring
    have h1 : Integrable (fun x => 2 * t * (f x * g x)) μ := hfg.const_mul _
    have h2 : Integrable (fun x => t ^ 2 * g x ^ 2) μ := hg.const_mul _
    have e1 : (∫ x, (f x ^ 2 + 2 * t * (f x * g x) + t ^ 2 * g x ^ 2) ∂μ)
        = (∫ x, (f x ^ 2 + 2 * t * (f x * g x)) ∂μ) + ∫ x, t ^ 2 * g x ^ 2 ∂μ :=
      integral_add (hf.add h1) h2
    have e2 : (∫ x, (f x ^ 2 + 2 * t * (f x * g x)) ∂μ)
        = (∫ x, f x ^ 2 ∂μ) + ∫ x, 2 * t * (f x * g x) ∂μ := integral_add hf h1
    have hexp : (∫ x, (f x + t * g x) ^ 2 ∂μ)
        = (∫ x, f x ^ 2 ∂μ) + 2 * t * (∫ x, f x * g x ∂μ) + t ^ 2 * ∫ x, g x ^ 2 ∂μ := by
      rw [integral_congr_ae (Filter.Eventually.of_forall hpt), e1, e2, integral_const_mul,
        integral_const_mul]
    have hnn : 0 ≤ ∫ x, (f x + t * g x) ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
    linarith only [hnn, hexp.le, hexp.ge]
  by_cases hC0 : (∫ x, g x ^ 2 ∂μ) = 0
  · have hB0 : (∫ x, f x * g x ∂μ) = 0 := by
      by_contra hne
      have h := key (-((∫ x, f x ^ 2 ∂μ) + 1) / (2 * ∫ x, f x * g x ∂μ))
      rw [hC0, mul_zero, add_zero] at h
      have hcalc : 2 * (-((∫ x, f x ^ 2 ∂μ) + 1) / (2 * ∫ x, f x * g x ∂μ))
          * (∫ x, f x * g x ∂μ) = -((∫ x, f x ^ 2 ∂μ) + 1) := by
        field_simp
      rw [hcalc] at h
      linarith only [h]
    rw [hB0, hC0]
    norm_num
  · have hCpos : 0 < ∫ x, g x ^ 2 ∂μ := lt_of_le_of_ne hC (Ne.symm hC0)
    have h := key (-(∫ x, f x * g x ∂μ) / ∫ x, g x ^ 2 ∂μ)
    have hmul := mul_le_mul_of_nonneg_left h hCpos.le
    rw [mul_zero] at hmul
    have hid : (∫ x, g x ^ 2 ∂μ) * ((∫ x, f x ^ 2 ∂μ)
        + 2 * (-(∫ x, f x * g x ∂μ) / ∫ x, g x ^ 2 ∂μ) * (∫ x, f x * g x ∂μ)
        + (-(∫ x, f x * g x ∂μ) / ∫ x, g x ^ 2 ∂μ) ^ 2 * ∫ x, g x ^ 2 ∂μ)
        = (∫ x, f x ^ 2 ∂μ) * (∫ x, g x ^ 2 ∂μ) - (∫ x, f x * g x ∂μ) ^ 2 := by
      field_simp
      ring
    rw [hid] at hmul
    linarith only [hmul]

/-- Cauchy–Schwarz: `∫ f g ≤ ‖f‖_{L²} ‖g‖_{L²}`. -/
theorem integral_mul_le_sqrt_mul_sqrt {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ} (hf : Integrable (fun x => f x ^ 2) μ) (hg : Integrable (fun x => g x ^ 2) μ)
    (hfg : Integrable (fun x => f x * g x) μ) :
    (∫ x, f x * g x ∂μ) ≤ Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := by
  have hA : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun _ => sq_nonneg _
  have hsq := sq_integral_mul_le_mul hf hg hfg
  calc (∫ x, f x * g x ∂μ) ≤ |∫ x, f x * g x ∂μ| := le_abs_self _
    _ = Real.sqrt ((∫ x, f x * g x ∂μ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (∫ x, f x ^ 2 ∂μ) * Real.sqrt (∫ x, g x ^ 2 ∂μ) := Real.sqrt_mul hA _

/-- A weight bounded by `Λ` against a square: `∫ w v² ≤ Λ ∫ v²`. -/
theorem integral_bdd_mul_sq_le {α : Type*} [MeasurableSpace α] {μ : Measure α} {w v : α → ℝ}
    {lam : ℝ} (hwm : AEStronglyMeasurable w μ) (hw : ∀ x, |w x| ≤ lam)
    (hv : Integrable (fun x => v x ^ 2) μ) :
    (∫ x, w x * v x ^ 2 ∂μ) ≤ lam * ∫ x, v x ^ 2 ∂μ := by
  have hint : Integrable (fun x => w x * v x ^ 2) μ :=
    hv.bdd_mul hwm (c := lam) (Filter.Eventually.of_forall fun x => by
      simpa [Real.norm_eq_abs] using hw x)
  have hint2 : Integrable (fun x => lam * v x ^ 2) μ := hv.const_mul lam
  have hmono : (∫ x, w x * v x ^ 2 ∂μ) ≤ ∫ x, lam * v x ^ 2 ∂μ := by
    refine integral_mono hint hint2 fun x => ?_
    exact mul_le_mul_of_nonneg_right (le_trans (le_abs_self _) (hw x)) (sq_nonneg _)
  rwa [integral_const_mul] at hmono

/-! ### The two right-hand terms of `eq:aniso:comparison:positive:energy` -/

/-- The drift term of `eq:aniso:comparison:positive:energy`: a weight bounded by `Λ`, such as
`div B` under `eq:aniso:comparison:drift`, contributes at most `Λ E(τ)`. -/
theorem integral_bdd_mul_sq_comparisonPosPart_le {m : ℕ} {ε M σ K τ₀ τ Minf lam : ℝ}
    (hε : 0 < ε) (hσ : 0 < σ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hτ : τ₀ ≤ τ) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) {w : Vec m → ℝ}
    (hwm : AEStronglyMeasurable w volume) (hw : ∀ x, |w x| ≤ lam) :
    (∫ x, w x * comparisonPosPart m ε M σ K τ₀ q (x, τ) ^ 2)
      ≤ lam * comparisonEnergy m ε M σ K τ₀ q τ :=
  integral_bdd_mul_sq_le hwm hw (integrable_sq_comparisonPosPart hε hσ hK hM hτ hmeas hbdd)

/-- The commutator `R_ε` of `eq:aniso:comparison:mollified` is square integrable on every
closed ball: it is a.e. strongly measurable and uniformly bounded, and the ball has finite
measure. -/
theorem integrable_sq_diPernaLionsCommutator {m : ℕ} {ε Mq Rad : ℝ} {Λ : NNReal} (hε : 0 < ε)
    (hM : 0 ≤ Mq) {b : Vec m → Vec m} {divb g : Vec m → ℝ} (hlip : LipschitzWith Λ b)
    (hdivb : ∀ y, |divb y| ≤ Λ) (hdivbm : AEStronglyMeasurable divb volume)
    (hg : ∀ y, |g y| ≤ Mq) (hgm : AEStronglyMeasurable g volume) :
    Integrable (fun x => diPernaLionsCommutator m ε b divb g x ^ 2)
      (volume.restrict (Metric.closedBall (0 : Vec m) Rad)) := by
  have hmeas : AEStronglyMeasurable (fun x => diPernaLionsCommutator m ε b divb g x) volume :=
    aestronglyMeasurable_diPernaLionsCommutator ε hlip.continuous hdivbm hgm
  have hmeas2 : AEStronglyMeasurable
      (fun x => diPernaLionsCommutator m ε b divb g x ^ 2) volume := hmeas.pow 2
  have hfin : volume (Metric.closedBall (0 : Vec m) Rad) ≠ ⊤ :=
    (isCompact_closedBall (0 : Vec m) Rad).measure_ne_top
  refine Measure.integrableOn_of_bounded hfin hmeas2
    (M := ((Λ : ℝ) * Mq * (mollifierGradConst m + 1)) ^ 2) ?_
  filter_upwards with x
  have h := abs_diPernaLionsCommutator_le hε hM hlip hdivb hdivbm hg hgm x
  rw [Real.norm_eq_abs, abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) h 2

/-- The commutator term of `eq:aniso:comparison:positive:energy`: since `v_ε(·, τ)` vanishes off
`closedBall 0 (M_∞/σ)`, Cauchy–Schwarz bounds `∫ R_ε v_ε` by
`‖R_ε‖_{L²(B_{R_σ})} √(E(τ))`. -/
theorem integral_mul_comparisonPosPart_le {m : ℕ} {ε M σ K τ₀ τ Minf : ℝ} (hε : 0 < ε)
    (hσ : 0 < σ) (hK : 0 ≤ K) (hM : 0 ≤ M) (hτ : τ₀ ≤ τ) {q : Vec m × ℝ → ℝ}
    (hmeas : AEStronglyMeasurable (fun y => q (y, τ)) volume)
    (hbdd : ∀ᵐ y ∂volume, |q (y, τ)| ≤ Minf) {rf : Vec m → ℝ}
    (hrm : AEStronglyMeasurable rf (volume.restrict (Metric.closedBall (0 : Vec m) (Minf / σ))))
    (hrsq : Integrable (fun x => rf x ^ 2)
      (volume.restrict (Metric.closedBall (0 : Vec m) (Minf / σ)))) :
    (∫ x, rf x * comparisonPosPart m ε M σ K τ₀ q (x, τ))
      ≤ Real.sqrt (∫ x in Metric.closedBall (0 : Vec m) (Minf / σ), rf x ^ 2)
        * Real.sqrt (comparisonEnergy m ε M σ K τ₀ q τ) := by
  have hrewrite : (∫ x, rf x * comparisonPosPart m ε M σ K τ₀ q (x, τ))
      = ∫ x in Metric.closedBall (0 : Vec m) (Minf / σ),
          rf x * comparisonPosPart m ε M σ K τ₀ q (x, τ) := by
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_).symm
    rw [comparisonPosPart_eq_zero_of_norm_ge hε hσ hK hM hτ hmeas hbdd x
      (le_norm_of_notMem_closedBall hx), mul_zero]
  have hvsq : Integrable (fun x => comparisonPosPart m ε M σ K τ₀ q (x, τ) ^ 2)
      (volume.restrict (Metric.closedBall (0 : Vec m) (Minf / σ))) :=
    (integrable_sq_comparisonPosPart hε hσ hK hM hτ hmeas hbdd).restrict
  have hvm : AEStronglyMeasurable (fun x => comparisonPosPart m ε M σ K τ₀ q (x, τ))
      (volume.restrict (Metric.closedBall (0 : Vec m) (Minf / σ))) :=
    (continuous_comparisonPosPart hε M σ K τ₀ τ hmeas hbdd).aestronglyMeasurable
  have hprod : Integrable (fun x => rf x * comparisonPosPart m ε M σ K τ₀ q (x, τ))
      (volume.restrict (Metric.closedBall (0 : Vec m) (Minf / σ))) := by
    have hdom : Integrable (fun x =>
        (rf x ^ 2 + comparisonPosPart m ε M σ K τ₀ q (x, τ) ^ 2) / 2)
        (volume.restrict (Metric.closedBall (0 : Vec m) (Minf / σ))) :=
      (hrsq.add hvsq).div_const 2
    refine hdom.mono' (hrm.mul hvm) (Filter.Eventually.of_forall fun x => ?_)
    have h1 : 0 ≤ (|rf x| - |comparisonPosPart m ε M σ K τ₀ q (x, τ)|) ^ 2 := sq_nonneg _
    have h2 : |rf x| ^ 2 = rf x ^ 2 := sq_abs _
    have h3 : |comparisonPosPart m ε M σ K τ₀ q (x, τ)| ^ 2
        = comparisonPosPart m ε M σ K τ₀ q (x, τ) ^ 2 := sq_abs _
    rw [Real.norm_eq_abs, abs_mul]
    linarith only [h1, h2, h3]
  rw [hrewrite, comparisonEnergy_eq_setIntegral_closedBall hε hσ hK hM hτ hmeas hbdd]
  exact integral_mul_le_sqrt_mul_sqrt hrsq hvsq hprod

/-! ### Grönwall in integral form -/

/-- Integral-form Grönwall inequality: a continuous `y` on `[a, b]` with
`y(t) ≤ c + Λ ∫_a^t y` obeys `y(t) ≤ c exp(Λ (b - a))`.

The primitive `F(t) = c + Λ ∫_a^t y` is continuous on `[a, b]` and has right derivative
`Λ y(t) ≤ Λ F(t)` there, so `t ↦ F(t) exp(-Λ (t - a))` has nonpositive right derivative and the
fencing theorem `image_le_of_deriv_right_le_deriv_boundary` bounds it by its value `c` at `a`. -/
theorem le_mul_exp_of_le_primitive {y : ℝ → ℝ} {a b c lam : ℝ} (hab : a ≤ b) (hlam : 0 ≤ lam)
    (hc : 0 ≤ c) (hycont : ContinuousOn y (Icc a b))
    (hy : ∀ t ∈ Icc a b, y t ≤ c + lam * ∫ s in a..t, y s) :
    ∀ t ∈ Icc a b, y t ≤ c * Real.exp (lam * (b - a)) := by
  have hyi : IntervalIntegrable y volume a b := hycont.intervalIntegrable_of_Icc hab
  have hprim : ContinuousOn (fun t => ∫ s in a..t, y s) (Icc a b) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hyi left_mem_uIcc
    rwa [uIcc_of_le hab] at h
  have hexpc : Continuous fun t : ℝ => Real.exp (-(lam * (t - a))) :=
    Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const)).neg
  have hPhicont : ContinuousOn
      (fun t => (c + lam * ∫ s in a..t, y s) * Real.exp (-(lam * (t - a)))) (Icc a b) :=
    (continuousOn_const.add (continuousOn_const.mul hprim)).mul hexpc.continuousOn
  have hFderiv : ∀ x ∈ Ico a b,
      HasDerivWithinAt (fun t => c + lam * ∫ s in a..t, y s) (lam * y x) (Ici x) x := by
    intro x hx
    have hxIcc : x ∈ Icc a b := mem_Icc_of_Ico hx
    have hintble : IntervalIntegrable y volume a x :=
      (hycont.mono (Icc_subset_Icc_right hxIcc.2)).intervalIntegrable_of_Icc hxIcc.1
    have hnhd : Icc a b ∈ 𝓝[Ioi x] x := by
      rw [mem_nhdsGT_iff_exists_Ioo_subset' hx.2]
      exact ⟨b, hx.2, fun z hz => ⟨hxIcc.1.trans hz.1.le, hz.2.le⟩⟩
    have hmeasf : StronglyMeasurableAtFilter y (𝓝[Ioi x] x) volume :=
      (hycont.stronglyMeasurableAtFilter_nhdsWithin measurableSet_Icc x).filter_mono
        (nhdsWithin_le_of_mem hnhd)
    have hcw : ContinuousWithinAt y (Ioi x) x :=
      (hycont.continuousWithinAt hxIcc).mono_of_mem_nhdsWithin hnhd
    have hbase : HasDerivWithinAt (fun u => ∫ s in a..u, y s) (y x) (Ici x) x :=
      intervalIntegral.integral_hasDerivWithinAt_right hintble hmeasf hcw
    exact HasDerivWithinAt.const_add c (HasDerivWithinAt.const_mul lam hbase)
  have hexpd : ∀ x : ℝ, HasDerivWithinAt (fun t => Real.exp (-(lam * (t - a))))
      (Real.exp (-(lam * (x - a))) * (-lam)) (Ici x) x := by
    intro x
    have h1 : HasDerivWithinAt (fun t : ℝ => t - a) 1 (Ici x) x :=
      (hasDerivWithinAt_id x (Ici x)).sub_const a
    have h2 : HasDerivWithinAt (fun t : ℝ => lam * (t - a)) (lam * 1) (Ici x) x :=
      HasDerivWithinAt.const_mul lam h1
    have h3 : HasDerivWithinAt (fun t : ℝ => -(lam * (t - a))) (-(lam * 1)) (Ici x) x := h2.neg
    have h4 := h3.exp
    simpa using h4
  have hPhideriv : ∀ x ∈ Ico a b, HasDerivWithinAt
      (fun t => (c + lam * ∫ s in a..t, y s) * Real.exp (-(lam * (t - a))))
      (lam * y x * Real.exp (-(lam * (x - a)))
        + (c + lam * ∫ s in a..x, y s) * (Real.exp (-(lam * (x - a))) * (-lam)))
      (Ici x) x := fun x hx => (hFderiv x hx).mul (hexpd x)
  have hstart : (c + lam * ∫ s in a..a, y s) * Real.exp (-(lam * (a - a))) ≤ c := by
    simp
  have hBderiv : ∀ x ∈ Ico a b, HasDerivWithinAt (fun _ : ℝ => c) 0 (Ici x) x :=
    fun x _ => hasDerivWithinAt_const _ _ _
  have hbound : ∀ x ∈ Ico a b, lam * y x * Real.exp (-(lam * (x - a)))
      + (c + lam * ∫ s in a..x, y s) * (Real.exp (-(lam * (x - a))) * (-lam)) ≤ 0 := by
    intro x hx
    have hyx : y x ≤ c + lam * ∫ s in a..x, y s := hy x (mem_Icc_of_Ico hx)
    have h1 : 0 ≤ (c + lam * ∫ s in a..x, y s) - y x := sub_nonneg.mpr hyx
    have h2 : (0 : ℝ) ≤ Real.exp (-(lam * (x - a))) := (Real.exp_pos _).le
    have h4 : 0 ≤ lam * (Real.exp (-(lam * (x - a))) * ((c + lam * ∫ s in a..x, y s) - y x)) :=
      mul_nonneg hlam (mul_nonneg h2 h1)
    linarith only [h4]
  have hres := image_le_of_deriv_right_le_deriv_boundary hPhicont hPhideriv hstart
    continuousOn_const hBderiv hbound
  intro t ht
  have h1 := hres ht
  have h2 : (c + lam * ∫ s in a..t, y s) ≤ c * Real.exp (lam * (t - a)) := by
    have h := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (lam * (t - a))).le
    rwa [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one] at h
  have h3 : c * Real.exp (lam * (t - a)) ≤ c * Real.exp (lam * (b - a)) := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hc
    exact mul_le_mul_of_nonneg_left (by linarith only [ht.2]) hlam
  exact le_trans (hy t ht) (le_trans h2 h3)

/-- The Grönwall step of `lem:aniso:comparison`, in the form the integrated energy inequality
`eq:aniso:comparison:positive:energy` delivers it: from
`y(t) ≤ ∫_a^t (Λ y + 2 √y r)` on `[a, b]` one gets
`y(t) ≤ (∫_a^b r²) exp((Λ + 1)(b - a))`, so the supremum of `y` is controlled by the squared
`L²` norm of `r`. -/
theorem le_exp_mul_integral_sq_of_le_integral {y r : ℝ → ℝ} {a b lam : ℝ} (hab : a ≤ b)
    (hlam : 0 ≤ lam) (hynn : ∀ t ∈ Icc a b, 0 ≤ y t) (hycont : ContinuousOn y (Icc a b))
    (hrcont : ContinuousOn r (Icc a b))
    (hineq : ∀ t ∈ Icc a b, y t ≤ ∫ s in a..t, (lam * y s + 2 * Real.sqrt (y s) * r s)) :
    ∀ t ∈ Icc a b, y t ≤ (∫ s in a..b, r s ^ 2) * Real.exp ((lam + 1) * (b - a)) := by
  have hlam1 : (0 : ℝ) ≤ lam + 1 := by linarith only [hlam]
  have hGnn : 0 ≤ ∫ s in a..b, r s ^ 2 :=
    intervalIntegral.integral_nonneg hab fun u _ => sq_nonneg _
  refine le_mul_exp_of_le_primitive hab hlam1 hGnn hycont ?_
  intro t ht
  have hat : a ≤ t := ht.1
  have htb : t ≤ b := ht.2
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc_right htb
  have hy_t : ContinuousOn y (Icc a t) := hycont.mono hsub
  have hr_t : ContinuousOn r (Icc a t) := hrcont.mono hsub
  have hyi : IntervalIntegrable y volume a t := hy_t.intervalIntegrable_of_Icc hat
  have hri : IntervalIntegrable (fun s => r s ^ 2) volume a t :=
    (hr_t.pow 2).intervalIntegrable_of_Icc hat
  have hf1 : IntervalIntegrable (fun s => lam * y s + 2 * Real.sqrt (y s) * r s) volume a t :=
    ((continuousOn_const.mul hy_t).add
      ((continuousOn_const.mul (Real.continuous_sqrt.comp_continuousOn hy_t)).mul
        hr_t)).intervalIntegrable_of_Icc hat
  have hf2 : IntervalIntegrable (fun s => (lam + 1) * y s + r s ^ 2) volume a t :=
    ((continuousOn_const.mul hy_t).add (hr_t.pow 2)).intervalIntegrable_of_Icc hat
  have hmono : (∫ s in a..t, (lam * y s + 2 * Real.sqrt (y s) * r s))
      ≤ ∫ s in a..t, ((lam + 1) * y s + r s ^ 2) := by
    refine intervalIntegral.integral_mono_on hat hf1 hf2 fun s hs => ?_
    have h := two_mul_sqrt_mul_le_add_sq (u := y s) (v := r s) (hynn s (hsub hs))
    linarith only [h]
  have hsplit : (∫ s in a..t, ((lam + 1) * y s + r s ^ 2))
      = (lam + 1) * (∫ s in a..t, y s) + ∫ s in a..t, r s ^ 2 := by
    rw [intervalIntegral.integral_add (hyi.const_mul (lam + 1)) hri,
      intervalIntegral.integral_const_mul]
  have hrest : (∫ s in a..t, r s ^ 2) ≤ ∫ s in a..b, r s ^ 2 := by
    have hi2 : IntervalIntegrable (fun s => r s ^ 2) volume t b :=
      ((hrcont.mono (Icc_subset_Icc_left hat)).pow 2).intervalIntegrable_of_Icc htb
    have hadd := intervalIntegral.integral_add_adjacent_intervals hri hi2
    have hnn2 : 0 ≤ ∫ s in t..b, r s ^ 2 :=
      intervalIntegral.integral_nonneg htb fun u _ => sq_nonneg _
    linarith only [hadd, hnn2]
  have h0 := hineq t ht
  linarith only [h0, hmono, hsplit.le, hsplit.ge, hrest]

/-- The Grönwall conclusion for the energy of `eq:aniso:comparison:positive:energy`: once the
integrated energy inequality is available on `[τ₀, τ₊]`, the energy is bounded there by the
squared `L²` norm of the commutator times a constant depending only on `Λ` and `τ₊ - τ₀`. -/
theorem comparisonEnergy_le_exp_mul_integral_sq {m : ℕ} {ε M σ K τ₀ tplus lam : ℝ}
    {q : Vec m × ℝ → ℝ} {r : ℝ → ℝ} (hab : τ₀ ≤ tplus) (hlam : 0 ≤ lam)
    (hcont : ContinuousOn (comparisonEnergy m ε M σ K τ₀ q) (Icc τ₀ tplus))
    (hrcont : ContinuousOn r (Icc τ₀ tplus))
    (hineq : ∀ τ ∈ Icc τ₀ tplus, comparisonEnergy m ε M σ K τ₀ q τ
      ≤ ∫ s in τ₀..τ, (lam * comparisonEnergy m ε M σ K τ₀ q s
          + 2 * Real.sqrt (comparisonEnergy m ε M σ K τ₀ q s) * r s)) :
    ∀ τ ∈ Icc τ₀ tplus, comparisonEnergy m ε M σ K τ₀ q τ
      ≤ (∫ s in τ₀..tplus, r s ^ 2) * Real.exp ((lam + 1) * (tplus - τ₀)) :=
  le_exp_mul_integral_sq_of_le_integral hab hlam
    (fun t _ => comparisonEnergy_nonneg ε M σ K τ₀ q t) hcont hrcont hineq

end CIV
