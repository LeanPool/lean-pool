/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.KLS.BrownianMotion.Gaussian.BrownianMotion
public import LeanPool.MathFin.Probability.Brownian.Wiener.WienerIntegralL2
public import LeanPool.MathFin.Probability.Analysis.IndepIsometryKernel

/-!
# The adapted Itô isometry (the increment-independence cornerstone)

The Wiener integral (`Probability/Brownian/Wiener/WienerIntegralL2.lean`) handles
*deterministic* integrands: there the cross-terms vanish by the BM
covariance `E[(B_t-B_s)(B_v-B_u)] = vol((s,t]∩(u,v])`. That is *not* the
Itô integral. The Itô integral allows a **random, adapted** integrand
`φ`, and the cross-terms vanish for a different, deeper reason: the next
increment `B_{t₁} - B_{t₀}` is *independent of the past* `𝓕_{t₀}` and has mean zero.

This file builds that genuinely-stochastic core **once, against an arbitrary filtration**:
`hF : IsFilteredPreBrownian B 𝓕 μ` (BrownianMotion's class: `B` is `𝓕`-adapted and the
increment `B t - B s` is independent of `𝓕 s`), and "adapted at `t₀`" is Mathlib's
`Measurable[𝓕 t₀]`. The natural filtration is the instance
`IsPreBrownianReal.isFilteredPreBrownian` (`ItoIntegralL2.natFiltration`). The
Poisson isometry (`PoissonCompensatedIsometryAdapted.lean`) is the same argument against
`PoissonRandomMeasure.pastFiltration`, with the independent-scattering field
`indep_of_disjoint_region` in place of `hF.indep`. The one-term facts that follow from independence
(`integral_mul_eq_zero`, `integral_mul_sq`, `memLp_two_mul`) are stated once for both, in
`IndepIsometryKernel`.

## Crux results

* `adapted_indepFun_increment` — an integrand `𝓕_{t₀}`-measurable is
  independent of the forward increment `B_{t₁} - B_{t₀}`.
* `integral_adapted_mul_increment` — **martingale-difference property**:
  `E[φ · (B_{t₁} - B_{t₀})] = 0` for `φ` adapted and integrable. This is
  the discrete statement that the Itô integral is a martingale.
* `integral_adapted_mul_increment_sq` — **isometry kernel**:
  `E[χ · (B_{t₁} - B_{t₀})²] = E[χ] · (t₁ - t₀)` (with the square form
  `integral_adapted_sq_mul_increment_sq` as the `χ = φ²` corollary).

## Coherence with upstream and the Wiener layer

Degenne's `BrownianMotion/StochasticIntegral/` already abstracts the
simple-predictable-integrand objects (`SimpleProcess`, `ElementaryPredictableSet`,
`L2Predictable`) — but proves no *integrand-to-integral* isometry; that is the gap
this file fills. (Since the 2026-07-27 pin bump upstream does prove an isometry,
`SquareIntegrable.toL2Isom` in `StochasticIntegral/SquareIntegrable.lean` — but it
is the other one: the `LinearIsometryEquiv` sending a square-integrable martingale
to its terminal value `X ∞` in `L²`, i.e. the Doob-space isomorphism, not
`‖∫ φ dB‖₂² = ∫ 𝔼[φ²] dt`. The two compose rather than compete, and consuming
`SquareIntegrable` for our `L²`-martingale layer is an open follow-up — see
`docs/archive/upstream-consumption-review-2026-07-27.md`.)
The deterministic second moment `integral_increment_sq` is *consumed* as the diagonal
instance of `WienerIntegralL2.covariance_increment_aux` — the single
shared increment-covariance lemma. Unifying onto the package's
`SimpleProcess`/`L2Predictable` remains deferred to a structural pass of the
simple-process layer.

## Main results

* `adapted_indepFun_increment`: an `𝓕_{t₀}`-measurable integrand is independent of the forward
  increment `B_{t₁} − B_{t₀}`.
* `integral_adapted_mul_increment`: for `φ` adapted to `𝓕_{t₀}`,
  `E[φ · (B_{t₁} − B_{t₀})] = 0`.
* `integral_adapted_sq_mul_increment_sq`: for `φ` adapted to `𝓕_{t₀}`,
  `E[φ² · (B_{t₁} − B_{t₀})²] = E[φ²] · (t₁ − t₀)`.
* `memLp_adapted_mul_increment`: for `φ` adapted to `𝓕_{t₀}` and in `L²`,
  `φ · (B_{t₁} − B_{t₀})` is in `L²`.
* `integral_cross_increment_bilinear_eq_zero`: for adapted integrand families `φ`, `ψ` and
  `j < k`, `E[(φⱼ ΔBⱼ)(ψₖ ΔBₖ)] = 0`.
* `ito_isometry_discrete_bilinear`: `E[(Σₖ φₖ ΔBₖ)(Σₖ ψₖ ΔBₖ)] = Σₖ E[φₖ ψₖ] (t_{k+1} − t_k)`.
* `ito_isometry_discrete`: `E[(Σₖ φₖ ΔBₖ)²] = Σₖ E[φₖ²] (t_{k+1} − t_k)` for adapted `L²`
  integrand families.
* `ito_isometry_brownian_self`: the discrete isometry for `φₖ = B(tₖ)`, with only measurability
  hypotheses.
* `rect_increment_pairing`: for `f` `𝓕_s`-measurable and `g` `𝓕_{s'}`-measurable, both bounded,
  `E[f (B_t − B_s) · g (B_{t'} − B_{s'})] = E[f g] · vol((s,t] ∩ (s',t'])`.

## Tags

Itô isometry, adapted integrand, martingale difference, independent increments, stochastic integral,
Wiener integral, MSC 60H05, MSC 60J65, MSC 60G44
-/

@[expose] public section

namespace MathFin
namespace ItoIsometryAdapted

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {B : ℝ≥0 → Ω → ℝ} {𝓕 : Filtration ℝ≥0 mΩ}

/-! ### Adaptedness of the Brownian coordinates -/

/-- `B u` is `𝓕 t`-measurable for `u ≤ t`: the process is adapted. -/
theorem _root_.ProbabilityTheory.IsFilteredPreBrownian.measurable_eval_of_le
    (hF : IsFilteredPreBrownian B 𝓕 μ) {u t : ℝ≥0} (hu : u ≤ t) : Measurable[𝓕 t] (B u) :=
  ((hF.stronglyAdapted u).mono (𝓕.mono hu)).measurable

/-- Each `B t` is ambient-measurable. -/
theorem _root_.ProbabilityTheory.IsFilteredPreBrownian.measurable_eval
    (hF : IsFilteredPreBrownian B 𝓕 μ) (t : ℝ≥0) : Measurable (B t) :=
  (hF.measurable_eval_of_le le_rfl).mono (𝓕.le t) le_rfl

/-- An integrand `𝓕_{t₀}`-measurable is independent of the forward increment
`B_{t₁} - B_{t₀}` (the filtered-Brownian independence `hF.indep`, read through
`comap φ ≤ 𝓕 t₀`). -/
theorem adapted_indepFun_increment
    (hF : IsFilteredPreBrownian B 𝓕 μ) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : Measurable[𝓕 t₀] φ) :
    IndepFun φ (fun ω ↦ B t₁ ω - B t₀ ω) μ :=
  (IndepFun_iff_Indep _ _ _).2 (indep_of_indep_of_le_left (hF.indep t₀ t₁ ht).symm hφ.comap_le)

/-- **Martingale-difference property of the Itô integral** (discrete form):
for `φ` adapted to `𝓕_{t₀}`, the integrand times the next Brownian increment
has mean zero, `E[φ · (B_{t₁} - B_{t₀})] = 0`. This is the reason the Itô
integral is a martingale — and it holds for *random* `φ`, where the Wiener
(deterministic) covariance argument does not apply. -/
theorem integral_adapted_mul_increment
    (hF : IsFilteredPreBrownian B 𝓕 μ) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : Measurable[𝓕 t₀] φ) :
    ∫ ω, φ ω * (B t₁ ω - B t₀ ω) ∂μ = 0 := by
  refine (adapted_indepFun_increment hF ht hφ).integral_mul_eq_zero
    (hφ.mono (𝓕.le t₀) le_rfl).aestronglyMeasurable
    ((hF.measurable_eval t₁).sub (hF.measurable_eval t₀)).aestronglyMeasurable ?_
  have h := (hF.hasLaw_sub t₁ t₀).integral_eq
  rwa [integral_id_gaussianReal] at h

/-- The forward increment has second moment `E[(B_{t₁} - B_{t₀})²] = t₁ - t₀`: the
diagonal instance of the Wiener-layer increment covariance
`WienerIntegralL2.covariance_increment_aux`. -/
theorem integral_increment_sq (hB : IsPreBrownianReal B μ)
    {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁) :
    ∫ ω, (B t₁ ω - B t₀ ω) ^ 2 ∂μ = (t₁ : ℝ) - t₀ := by
  have : IsProbabilityMeasure μ := hB.isGaussianProcess.isProbabilityMeasure
  have h := WienerIntegralL2.covariance_increment_aux hB t₀ t₁ t₀ t₁ ht ht
  simp only [min_self, max_self] at h
  rw [max_eq_right (sub_nonneg.mpr (NNReal.coe_le_coe.mpr ht))] at h
  rw [← h]
  exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ pow_two (B t₁ ω - B t₀ ω))

/-- **General isometry kernel**: for `χ` adapted to `𝓕_{t₀}`,
`E[χ · (B_{t₁} - B_{t₀})²] = E[χ] · (t₁ - t₀)`. The increment's square is
independent of the past and has mean `t₁ - t₀`. Specialises to
`integral_adapted_sq_mul_increment_sq` (take `χ = φ²`); supplies the *diagonal*
term of the bilinear isometry below (`χ = φₖ · ψₖ`). -/
theorem integral_adapted_mul_increment_sq
    (hF : IsFilteredPreBrownian B 𝓕 μ) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {χ : Ω → ℝ} (hχ : Measurable[𝓕 t₀] χ) :
    ∫ ω, χ ω * (B t₁ ω - B t₀ ω) ^ 2 ∂μ = (∫ ω, χ ω ∂μ) * ((t₁ : ℝ) - t₀) := by
  rw [(adapted_indepFun_increment hF ht hχ).integral_mul_sq
    (hχ.mono (𝓕.le t₀) le_rfl).aestronglyMeasurable
    ((hF.measurable_eval t₁).sub (hF.measurable_eval t₀)).aestronglyMeasurable,
    integral_increment_sq hF.toIsPreBrownianReal ht]

/-- **Isometry kernel** (the diagonal term of the Itô isometry): for `φ`
adapted to `𝓕_{t₀}`, `E[φ² · (B_{t₁} - B_{t₀})²] = E[φ²] · (t₁ - t₀)`. The
`χ = φ²` instance of `integral_adapted_mul_increment_sq`. -/
theorem integral_adapted_sq_mul_increment_sq
    (hF : IsFilteredPreBrownian B 𝓕 μ) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : Measurable[𝓕 t₀] φ) :
    ∫ ω, (φ ω) ^ 2 * (B t₁ ω - B t₀ ω) ^ 2 ∂μ =
      (∫ ω, (φ ω) ^ 2 ∂μ) * ((t₁ : ℝ) - t₀) :=
  integral_adapted_mul_increment_sq hF ht (hφ.pow_const 2)

/-- If `φ` is adapted to `𝓕_{t₀}` and in `L²`, then `φ · (B_{t₁} - B_{t₀})` is
in `L²`: the increment is in `L²` and independent of `φ`, so the product's
square is integrable. This is the `L²`-membership of a single term of an
adapted simple integral. -/
theorem memLp_adapted_mul_increment
    (hF : IsFilteredPreBrownian B 𝓕 μ) {t₀ t₁ : ℝ≥0} (ht : t₀ ≤ t₁)
    {φ : Ω → ℝ} (hφ : Measurable[𝓕 t₀] φ) (hφL2 : MemLp φ 2 μ) :
    MemLp (fun ω ↦ φ ω * (B t₁ ω - B t₀ ω)) 2 μ :=
  (adapted_indepFun_increment hF ht hφ).memLp_two_mul hφL2
    hF.isGaussianProcess.hasGaussianLaw_sub.memLp_two

/-! ### The discrete Itô isometry over a partition -/

/-- **Bilinear cross terms vanish.** For two adapted integrand families `φ`,
`ψ` and `j < k`, `E[(φⱼ·ΔBⱼ)·(ψₖ·ΔBₖ)] = 0`. The factor `φⱼ·ΔBⱼ·ψₖ` is
`𝓕_{tₖ}`-measurable, and `ΔBₖ` is independent of it with mean zero. -/
theorem integral_cross_increment_bilinear_eq_zero
    (hF : IsFilteredPreBrownian B 𝓕 μ) {t : ℕ → ℝ≥0} (hmono : Monotone t)
    {φ ψ : ℕ → Ω → ℝ} (hφ : ∀ n, Measurable[𝓕 (t n)] (φ n))
    (hψ : ∀ n, Measurable[𝓕 (t n)] (ψ n)) {j k : ℕ} (hjk : j < k) :
    ∫ ω, (φ j ω * (B (t (j + 1)) ω - B (t j) ω)) *
          (ψ k ω * (B (t (k + 1)) ω - B (t k) ω)) ∂μ = 0 := by
  have hΦ : Measurable[𝓕 (t k)]
      (fun ω ↦ φ j ω * (B (t (j + 1)) ω - B (t j) ω) * ψ k ω) :=
    (((hφ j).mono (𝓕.mono (hmono hjk.le)) le_rfl).mul
      ((hF.measurable_eval_of_le (hmono hjk)).sub
        (hF.measurable_eval_of_le (hmono hjk.le)))).mul (hψ k)
  have hstep : t k ≤ t (k + 1) := hmono (Nat.le_succ k)
  have h0 := integral_adapted_mul_increment hF hstep hΦ
  rw [show (fun ω ↦ (φ j ω * (B (t (j + 1)) ω - B (t j) ω)) *
        (ψ k ω * (B (t (k + 1)) ω - B (t k) ω)))
      = (fun ω ↦ (φ j ω * (B (t (j + 1)) ω - B (t j) ω) * ψ k ω) *
        (B (t (k + 1)) ω - B (t k) ω)) from by funext ω; ring]
  exact h0

/-- **The bilinear discrete Itô isometry** (the inner-product/polarised form).
For adapted `L²` integrand families `φ`, `ψ` over a partition `t`,

  `E[(Σₖ φₖ·ΔBₖ)·(Σₖ ψₖ·ΔBₖ)] = Σₖ E[φₖ·ψₖ]·(t_{k+1} − t_k)`.

This is the workhorse for the continuous Itô isometry: the inner product of two
adapted simple integrals is the `L²(Ω × [0,T])` inner product of the integrands.
The diagonal terms give the mixed kernel `integral_adapted_mul_increment_sq`;
the off-diagonal terms vanish by `integral_cross_increment_bilinear_eq_zero`. -/
theorem ito_isometry_discrete_bilinear
    (hF : IsFilteredPreBrownian B 𝓕 μ) {N : ℕ} {t : ℕ → ℝ≥0} (hmono : Monotone t)
    {φ ψ : ℕ → Ω → ℝ} (hφ : ∀ n, Measurable[𝓕 (t n)] (φ n))
    (hψ : ∀ n, Measurable[𝓕 (t n)] (ψ n))
    (hφL2 : ∀ n, MemLp (φ n) 2 μ) (hψL2 : ∀ n, MemLp (ψ n) 2 μ) :
    ∫ ω, (∑ k ∈ Finset.range N, φ k ω * (B (t (k + 1)) ω - B (t k) ω)) *
          (∑ k ∈ Finset.range N, ψ k ω * (B (t (k + 1)) ω - B (t k) ω)) ∂μ =
      ∑ k ∈ Finset.range N, (∫ ω, φ k ω * ψ k ω ∂μ) * ((t (k + 1) : ℝ) - t k) := by
  have : IsProbabilityMeasure μ := hF.isGaussianProcess.isProbabilityMeasure
  set a : ℕ → Ω → ℝ := fun k ω ↦ φ k ω * (B (t (k + 1)) ω - B (t k) ω) with ha_def
  set b : ℕ → Ω → ℝ := fun k ω ↦ ψ k ω * (B (t (k + 1)) ω - B (t k) ω) with hb_def
  have ha_L2 : ∀ k, MemLp (a k) 2 μ := fun k ↦
    memLp_adapted_mul_increment hF (hmono (Nat.le_succ k)) (hφ k) (hφL2 k)
  have hb_L2 : ∀ k, MemLp (b k) 2 μ := fun k ↦
    memLp_adapted_mul_increment hF (hmono (Nat.le_succ k)) (hψ k) (hψL2 k)
  have hint : ∀ j k, Integrable (fun ω ↦ a j ω * b k ω) μ := fun j k ↦
    (ha_L2 j).integrable_mul (hb_L2 k)
  -- Diagonal term = mixed variance kernel.
  have hdiag : ∀ k, ∫ ω, a k ω * b k ω ∂μ =
      (∫ ω, φ k ω * ψ k ω ∂μ) * ((t (k + 1) : ℝ) - t k) := by
    intro k
    have hstep : t k ≤ t (k + 1) := hmono (Nat.le_succ k)
    have hχ : Measurable[𝓕 (t k)] (fun ω ↦ φ k ω * ψ k ω) := (hφ k).mul (hψ k)
    rw [show (fun ω ↦ a k ω * b k ω)
          = (fun ω ↦ (φ k ω * ψ k ω) * (B (t (k + 1)) ω - B (t k) ω) ^ 2) from by
            funext ω; simp only [ha_def, hb_def]; ring]
    exact integral_adapted_mul_increment_sq hF hstep hχ
  -- Off-diagonal terms vanish.
  have hcross : ∀ j ∈ Finset.range N, ∀ k ∈ Finset.range N, j ≠ k →
      ∫ ω, a j ω * b k ω ∂μ = 0 := by
    intro j _ k _ hjk
    rcases lt_or_gt_of_ne hjk with h | h
    · exact integral_cross_increment_bilinear_eq_zero hF hmono hφ hψ h
    · rw [show (fun ω ↦ a j ω * b k ω) = (fun ω ↦ b k ω * a j ω) from by funext ω; ring]
      exact integral_cross_increment_bilinear_eq_zero hF hmono hψ hφ h
  calc ∫ ω, (∑ k ∈ Finset.range N, a k ω) * (∑ k ∈ Finset.range N, b k ω) ∂μ
      = ∫ ω, ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, a j ω * b k ω ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
        change (∑ k ∈ Finset.range N, a k ω) * (∑ k ∈ Finset.range N, b k ω)
          = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, a j ω * b k ω
        rw [Finset.sum_mul_sum]
    _ = ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, ∫ ω, a j ω * b k ω ∂μ := by
        rw [integral_finsetSum _ (fun j _ ↦ integrable_finsetSum _ (fun k _ ↦ hint j k))]
        exact Finset.sum_congr rfl
          (fun j _ ↦ integral_finsetSum _ (fun k _ ↦ hint j k))
    _ = ∑ j ∈ Finset.range N, ∫ ω, a j ω * b j ω ∂μ := by
        refine Finset.sum_congr rfl (fun j hj ↦ ?_)
        exact Finset.sum_eq_single j (fun k hk hkj ↦ hcross j hj k hk (Ne.symm hkj))
          (fun hj' ↦ absurd hj hj')
    _ = ∑ k ∈ Finset.range N, (∫ ω, φ k ω * ψ k ω ∂μ) * ((t (k + 1) : ℝ) - t k) :=
        Finset.sum_congr rfl (fun k _ ↦ hdiag k)

/-- **The discrete Itô isometry** (adapted simple integrands):
`E[(Σₖ φₖ·(B_{t_{k+1}} − B_{t_k}))²] = Σₖ E[φₖ²]·(t_{k+1} − t_k)`. The genuine
Itô isometry — the integrand is *random*. It is the `ψ = φ` diagonal of the
inner-product form `ito_isometry_discrete_bilinear` (`x² = x·x`). -/
theorem ito_isometry_discrete
    (hF : IsFilteredPreBrownian B 𝓕 μ) {N : ℕ} {t : ℕ → ℝ≥0} (hmono : Monotone t)
    {φ : ℕ → Ω → ℝ} (hadapt : ∀ n, Measurable[𝓕 (t n)] (φ n))
    (hL2 : ∀ n, MemLp (φ n) 2 μ) :
    ∫ ω, (∑ k ∈ Finset.range N, φ k ω * (B (t (k + 1)) ω - B (t k) ω)) ^ 2 ∂μ =
      ∑ k ∈ Finset.range N, (∫ ω, (φ k ω) ^ 2 ∂μ) * ((t (k + 1) : ℝ) - t k) := by
  simp only [pow_two]
  exact ito_isometry_discrete_bilinear hF hmono hadapt hadapt hL2 hL2

/-- `E[B_s²] = s` (mean zero, variance `s`). -/
theorem integral_eval_sq (hB : IsPreBrownianReal B μ) (hBmeas : ∀ s, Measurable (B s))
    (s : ℝ≥0) :
    ∫ ω, (B s ω) ^ 2 ∂μ = (s : ℝ) := by
  rw [← variance_of_integral_eq_zero (hBmeas s).aemeasurable (hB.integral_eval s)]
  show Var[B s; μ] = (s : ℝ)
  rw [(hB.hasLaw_eval s).variance_eq, variance_id_gaussianReal]

/-- **The discrete `∫₀ᵀ B dB` isometry** — the canonical instance, with *no*
remaining hypotheses beyond measurability. Taking the adapted `L²` integrand
`φₖ = B(tₖ)`,

  `E[(Σₖ B(tₖ)·(B_{t_{k+1}} − B_{t_k}))²] = Σₖ t_k·(t_{k+1} − t_k)`,

the Riemann-sum form of the Itô isometry `E[(∫₀ᵀ B dB)²] = ∫₀ᵀ t dt`. -/
theorem ito_isometry_brownian_self
    (hF : IsFilteredPreBrownian B 𝓕 μ) {N : ℕ} {t : ℕ → ℝ≥0} (hmono : Monotone t) :
    ∫ ω, (∑ k ∈ Finset.range N, B (t k) ω * (B (t (k + 1)) ω - B (t k) ω)) ^ 2 ∂μ =
      ∑ k ∈ Finset.range N, (t k : ℝ) * ((t (k + 1) : ℝ) - t k) := by
  rw [ito_isometry_discrete hF hmono (φ := fun k ↦ B (t k))
    (fun n ↦ hF.measurable_eval_of_le le_rfl)
    (fun n ↦ (hF.isGaussianProcess.hasGaussianLaw_eval (t n)).memLp_two)]
  exact Finset.sum_congr rfl
    (fun k _ ↦ by rw [integral_eval_sq hF.toIsPreBrownianReal hF.measurable_eval])

/-! ### Pairing identity for predictable rectangles

The bridge to the *continuous* Itô integral. For an adapted indicator `f`
(`𝓕_s`-measurable) and `g` (`𝓕_{s'}`-measurable),

  `E[f·(B_t − B_s) · g·(B_{t'} − B_{s'})] = E[f·g] · vol((s,t] ∩ (s',t'])`.

This is the adapted generalisation of `WienerIntegralL2.covariance_increment_aux`
(take `f = g = 1`). It is the inner-product identity that makes the assembly of
predictable simple integrands an isometry into `L²(Ω × [0,T])`. The split-at-the-
later-start argument: the pre-overlap part pairs to zero (martingale difference), and in
the post-overlap part both increments are *forward* of the later start; splitting the longer
at the shorter's end, the cross piece is a martingale difference and the diagonal piece is
the isometry kernel (`integral_adapted_mul_increment_mul_increment`). -/

/-- Integrability of `h · ΔB · ΔB'` for `h` bounded (the products that appear
when splitting the rectangle pairing). -/
lemma integrable_bdd_two_increment (hB : IsPreBrownianReal B μ)
    {h : Ω → ℝ} (hhm : Measurable h)
    {C : ℝ} (hhb : ∀ ω, |h ω| ≤ C) (a b c d : ℝ≥0) :
    Integrable (fun ω ↦ h ω * ((B b ω - B a ω) * (B d ω - B c ω))) μ := by
  have hprod : Integrable (fun ω ↦ (B b ω - B a ω) * (B d ω - B c ω)) μ :=
    (hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two).integrable_mul
      (hB.isGaussianProcess.hasGaussianLaw_sub.memLp_two)
  exact hprod.bdd_mul hhm.aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ by rw [Real.norm_eq_abs]; exact hhb ω)

/-- **Two nested forward increments from one start**: for a bounded `χ` adapted to
`𝓕_a` and `a ≤ b ≤ c`, `E[χ·(B_b − B_a)·(B_c − B_a)] = E[χ]·(b − a)`. Split
`B_c − B_a = (B_c − B_b) + (B_b − B_a)`: the first piece pairs `χ·(B_b − B_a)` (which is
`𝓕_b`-measurable) with a forward increment, a martingale difference; the second is the
isometry kernel. -/
theorem integral_adapted_mul_increment_mul_increment
    (hF : IsFilteredPreBrownian B 𝓕 μ) {a b c : ℝ≥0} (hab : a ≤ b) (hbc : b ≤ c)
    {χ : Ω → ℝ} (hχ : Measurable[𝓕 a] χ) {C : ℝ} (hχb : ∀ ω, |χ ω| ≤ C) :
    ∫ ω, χ ω * ((B b ω - B a ω) * (B c ω - B a ω)) ∂μ = (∫ ω, χ ω ∂μ) * ((b : ℝ) - a) := by
  have hχm : Measurable χ := hχ.mono (𝓕.le a) le_rfl
  have hB' := hF.toIsPreBrownianReal
  have hχb' : Measurable[𝓕 b] (fun ω ↦ χ ω * (B b ω - B a ω)) :=
    (hχ.mono (𝓕.mono hab) le_rfl).mul
      ((hF.measurable_eval_of_le le_rfl).sub (hF.measurable_eval_of_le hab))
  have h1 := integral_adapted_mul_increment hF hbc hχb'
  have h2 := integral_adapted_mul_increment_sq hF hab hχ
  have hsplit : ∀ ω, χ ω * ((B b ω - B a ω) * (B c ω - B a ω))
      = χ ω * (B b ω - B a ω) * (B c ω - B b ω) + χ ω * (B b ω - B a ω) ^ 2 := fun ω ↦ by ring
  simp_rw [hsplit]
  rw [integral_add, h1, h2, zero_add]
  · exact (integrable_bdd_two_increment hB' hχm hχb a b b c).congr
      (Filter.Eventually.of_forall fun ω ↦ by ring)
  · exact (integrable_bdd_two_increment hB' hχm hχb a b a b).congr
      (Filter.Eventually.of_forall fun ω ↦ by ring)

/-- Pairing identity, oriented case `s ≤ s'`. -/
lemma integral_mul_increment_mul_increment_eq_of_le
    (hF : IsFilteredPreBrownian B 𝓕 μ) {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : Measurable[𝓕 s] f) (hg : Measurable[𝓕 s'] g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (_hst : s ≤ t) (hst' : s' ≤ t') (hss' : s ≤ s') :
    ∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ =
      (∫ ω, f ω * g ω ∂μ) * max 0 ((min (t : ℝ) t') - max (s : ℝ) s') := by
  have hB' := hF.toIsPreBrownianReal
  have hfm : Measurable f := hf.mono (𝓕.le s) le_rfl
  have hgm : Measurable g := hg.mono (𝓕.le s') le_rfl
  have hfg : Measurable[𝓕 s'] (fun ω ↦ f ω * g ω) := (hf.mono (𝓕.mono hss') le_rfl).mul hg
  have hfgm : Measurable (fun ω ↦ f ω * g ω) := hfm.mul hgm
  have hfgb : ∀ ω, |f ω * g ω| ≤ Cf * Cg := fun ω ↦ by
    rw [abs_mul]
    exact mul_le_mul (hfb ω) (hgb ω) (abs_nonneg _) (le_trans (abs_nonneg _) (hfb ω))
  have hmaxss' : max (s : ℝ) s' = (s' : ℝ) := max_eq_right (by exact_mod_cast hss')
  rw [hmaxss']
  by_cases htle : t ≤ s'
  · -- Disjoint intervals: the whole pairing is a forward increment with mean zero.
    have hχ : Measurable[𝓕 s'] (fun ω ↦ f ω * (B t ω - B s ω) * g ω) :=
      ((hf.mono (𝓕.mono hss') le_rfl).mul
        ((hF.measurable_eval_of_le htle).sub (hF.measurable_eval_of_le hss'))).mul hg
    have h0 := integral_adapted_mul_increment hF hst' hχ
    have hzero : max (0 : ℝ) ((min (t : ℝ) t') - s') = 0 := by
      refine max_eq_left ?_
      have : (min (t : ℝ) t') ≤ (s' : ℝ) :=
        le_trans (min_le_left _ _) (by exact_mod_cast htle)
      linarith
    rw [hzero, mul_zero, ← h0]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
  · -- Overlapping intervals: split the first increment at the later start `s'`.
    replace htle := not_le.mp htle
    have hT1 : ∫ ω, f ω * g ω * ((B s' ω - B s ω) * (B t' ω - B s' ω)) ∂μ = 0 := by
      have hχ : Measurable[𝓕 s'] (fun ω ↦ f ω * g ω * (B s' ω - B s ω)) :=
        hfg.mul ((hF.measurable_eval_of_le le_rfl).sub (hF.measurable_eval_of_le hss'))
      have h0 := integral_adapted_mul_increment hF hst' hχ
      rw [← h0]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
    have hT2 : ∫ ω, f ω * g ω * ((B t ω - B s' ω) * (B t' ω - B s' ω)) ∂μ
        = (∫ ω, f ω * g ω ∂μ) * (((min t t' : ℝ≥0) : ℝ) - s') := by
      rcases le_total t t' with htt | htt
      · rw [min_eq_left htt]
        exact integral_adapted_mul_increment_mul_increment hF htle.le htt hfg hfgb
      · rw [min_eq_right htt, ← integral_adapted_mul_increment_mul_increment hF hst' htt hfg hfgb]
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
    have hsum : ∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ
        = (∫ ω, f ω * g ω * ((B s' ω - B s ω) * (B t' ω - B s' ω)) ∂μ)
          + ∫ ω, f ω * g ω * ((B t ω - B s' ω) * (B t' ω - B s' ω)) ∂μ := by
      rw [← integral_add (integrable_bdd_two_increment hB' hfgm hfgb s s' s' t')
                         (integrable_bdd_two_increment hB' hfgm hfgb s' t s' t')]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
    have hcoe : ((min t t' : ℝ≥0) : ℝ) = min (t : ℝ) t' := by
      rcases le_total t t' with h | h
      · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
      · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]
    rw [hsum, hT1, hT2, zero_add, hcoe]
    congr 1
    have h1 : (s' : ℝ) ≤ min (t : ℝ) t' :=
      le_min (by exact_mod_cast htle.le) (by exact_mod_cast hst')
    rw [max_eq_right (by linarith)]

/-- **Pairing identity for predictable rectangles.** For adapted bounded
integrands `f` (`𝓕_s`-measurable) and `g` (`𝓕_{s'}`-measurable),

  `E[f·(B_t − B_s) · g·(B_{t'} − B_{s'})] = E[f·g] · vol((s,t] ∩ (s',t'])`,

with `vol((s,t] ∩ (s',t']) = max 0 (min t t' − max s s')`. The adapted
generalisation of the Wiener covariance identity, and the inner-product core of
the continuous Itô isometry. -/
theorem rect_increment_pairing
    (hF : IsFilteredPreBrownian B 𝓕 μ) {f g : Ω → ℝ} {s t s' t' : ℝ≥0}
    (hf : Measurable[𝓕 s] f) (hg : Measurable[𝓕 s'] g)
    {Cf Cg : ℝ} (hfb : ∀ ω, |f ω| ≤ Cf) (hgb : ∀ ω, |g ω| ≤ Cg)
    (hst : s ≤ t) (hst' : s' ≤ t') :
    ∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ =
      (∫ ω, f ω * g ω ∂μ) * max 0 ((min (t : ℝ) t') - max (s : ℝ) s') := by
  rcases le_total s s' with h | h
  · exact integral_mul_increment_mul_increment_eq_of_le hF hf hg hfb hgb hst hst' h
  · rw [show (∫ ω, (f ω * (B t ω - B s ω)) * (g ω * (B t' ω - B s' ω)) ∂μ)
          = ∫ ω, (g ω * (B t' ω - B s' ω)) * (f ω * (B t ω - B s ω)) ∂μ from
        integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring),
        integral_mul_increment_mul_increment_eq_of_le hF hg hf hgb hfb hst' hst h]
    congr 1
    · exact integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ by ring)
    · rw [min_comm (t' : ℝ) t, max_comm (s' : ℝ) s]

end ItoIsometryAdapted
end MathFin
