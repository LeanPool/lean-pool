/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Girsanov.GirsanovSimpleTheta

/-! # Moment bounds for the simple Doléans exponential (the a.e.-subsequence engine feed)

The distributional Girsanov limit (continuous or predictable θ) passes the *simple* exponential
martingale identity to the limit through the a.e.-subsequence set-integral engine
`tendsto_setIntegral_of_subseq_ae_of_sq_bound`, whose hypotheses are: each approximant product
`Dⁿ_u · Zⁿ_T ∈ L²` and a **uniform** second-moment bound `∫ (Dⁿ_u · Zⁿ_T)² ≤ M`. This file supplies
those bounds for **any** bounded, adapted simple integrand — a monotone partition `s : ℕ → ℝ≥0`
covering `[0,T]` with `𝓕_{s i}`-measurable multipliers `c` bounded by `K` — abstractly, so both the
`unifPart`-grid (continuous θ) and the marshalled partition (predictable θ) instantiate the same
estimates rather than re-deriving them.

The two moments the engine's `M` decomposes into (via AM–GM `(x·y)² ≤ ½(x⁴+y⁴)`):

* `quad_integral_simpleDoleans_le` — `∫ (Z_{−c})⁴ ≤ exp(6K²T)`, from
  `(Z_{−c})⁴ = E^{−4c} · exp(6·QV)` with the quadratic variation `QV ≤ K²T`;
* `quad_integral_driftExp_le` — `∫ (D_u)⁴ ≤ exp(4|a|KT)·𝔼[exp(4a·X_u)]`, from the drift bound
  `|simpleDrift| ≤ K·u ≤ K·T` and the Gaussian `4a`-MGF of `X_u`.

The two structural identities behind them, generic in the multiplier scale `r`:

* `simpleStochSum` / `simpleQuadVar` — the discrete Itô sum `∑ cᵢ ΔXᵢ` and discrete quadratic
  variation `∑ cᵢ² Δτᵢ` of the simple integrand;
* `simpleDoleansExp_scaled_eq` — `E^{r·c}_T = exp(r·∑cᵢΔXᵢ − ½r²·∑cᵢ²Δτᵢ)`, the log-linearity that
  turns every `Lᵖ` power into a rescaled Doléans density times an `exp` of the quadratic variation.

## Main definitions

* `simpleStochSum`: the discrete Itô sum `∑_{i<N} cᵢ (X_{s_{i+1}∧T} − X_{s_i∧T})` of a simple
  integrand.
* `simpleQuadVar`: the discrete quadratic variation `∑_{i<N} cᵢ² (s_{i+1}∧T − s_i∧T)`.

## Main results

* `simpleDoleansExp_scaled_eq`: `E^{r·c}_T = exp(r·∑cᵢΔXᵢ − ½r²·∑cᵢ²Δτᵢ)`.
* `simpleQuadVar_le`: `simpleQuadVar ≤ K²·T` for multipliers bounded by `K` on a partition
  covering `[0, T]`.
* `quad_integral_simpleDoleans_le`, `sq_integral_simpleDoleans_le`: `∫ (Z_{−c})⁴ ≤ exp(6K²T)`
  and `∫ (Z_{−c})² ≤ exp(K²T)` for the simple Doléans density.
* `quad_integral_driftExp_le`: `∫ (D_u)⁴ ≤ exp(4|a|KT)·𝔼[exp(4a·X_u)]` for the drift-corrected
  exponential `D_u`.
* `sq_integral_mixedProduct_le`: `∫ (D_u·Z_T)² ≤ ½(exp(4|a|KT)·𝔼[exp(4a·X_u)] + exp(6K²T))`.

## Tags

Girsanov theorem, Doléans exponential, moment bounds, simple integrand, quadratic variation,
fourth moment, MSC 60H05, MSC 60G44
-/

@[expose] public section

namespace MathFin

/- The generic simple-Doléans moment bounds live in their own namespace: their
`simpleDoleansExp_neg_eq` / `simpleDoleansExp_scaled_eq` / `sq_mul_le_half_add_pow4` are the
*partition-generic* forms (they subsume the `unifPart`-grid specializations that
`GirsanovAdaptedTheta` once carried). -/
namespace SimpleDoleansMoments

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ}

/-- **The discrete Itô sum** `∑_{i<N} cᵢ·(X_{s_{i+1}∧T} − X_{s_i∧T})` of a simple integrand — the
stochastic exponent of the simple Doléans density. -/
noncomputable def simpleStochSum (s : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (N : ℕ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N, c i ω * (X (min (s (i + 1)) T) ω - X (min (s i) T) ω)

/-- **The discrete quadratic variation** `∑_{i<N} cᵢ²·(s_{i+1}∧T − s_i∧T)` of a simple integrand —
the drift half of the simple Doléans exponent. -/
noncomputable def simpleQuadVar (s : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (N : ℕ) (T : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N,
    (c i ω) ^ 2 * (NNReal.toReal (min (s (i + 1)) T) - NNReal.toReal (min (s i) T))

/-- **The quadratic variation is bounded by `K²·T`.** Each `cᵢ² ≤ K²` and the clamped cell-lengths
sum to `T` when the partition covers `[0,T]`. -/
lemma simpleQuadVar_le {s : ℕ → ℝ≥0} (hs : Monotone s) (hs0 : s 0 = 0) {c : ℕ → Ω → ℝ} {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (N : ℕ) {T : ℝ≥0} (hNT : T ≤ s N) (ω : Ω) :
    simpleQuadVar (Ω := Ω) s c N T ω ≤ K ^ 2 * (T : ℝ) := by
  rw [simpleQuadVar, ← simpleTau_sum hs0 N hNT, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right ?_ (simpleTau_nonneg hs i T)
  nlinarith [(abs_le.mp (hc_bdd i ω)).1, (abs_le.mp (hc_bdd i ω)).2]

/-- **Log-linearity of the rescaled simple Doléans density.** `E^{r·c}_T = exp(r·∑cᵢΔXᵢ −
½r²·∑cᵢ²Δτᵢ)`: scaling the multiplier by `r` scales the stochastic exponent by `r` and the quadratic
variation by `r²`. The `r = −1` case is the density `Z_{−c}`; `r = −2, −4` power the `L²`/`L⁴`
bounds. -/
lemma simpleDoleansExp_scaled_eq (s : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (r : ℝ) (N : ℕ) (T : ℝ≥0) (ω : Ω) :
    simpleDoleansExp (X := X) s (fun i ω ↦ r * c i ω) N T ω
      = Real.exp (r * simpleStochSum (X := X) s c N T ω
          - 2⁻¹ * r ^ 2 * simpleQuadVar (Ω := Ω) s c N T ω) := by
  rw [simpleDoleansExp_eq_exp_sum]
  congr 1
  rw [simpleStochSum, simpleQuadVar, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ by ring

/-- The density `Z_{−c}` in stochastic-exponent form: `Z_{−c}_T = exp(−∑cᵢΔXᵢ − ½∑cᵢ²Δτᵢ)`, the
`r = −1` specialization of `simpleDoleansExp_scaled_eq`. -/
lemma simpleDoleansExp_neg_eq (s : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (N : ℕ) (T : ℝ≥0) (ω : Ω) :
    simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω
      = Real.exp (-simpleStochSum (X := X) s c N T ω
          - 2⁻¹ * simpleQuadVar (Ω := Ω) s c N T ω) := by
  rw [simpleDoleansExp_eq_exp_sum]
  congr 1
  rw [simpleStochSum, simpleQuadVar, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ ↦ by ring

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  [SigmaFiniteFiltration P 𝓕] [hX : IsFilteredPreBrownian X 𝓕 P]

/-- The adapted, bounded rescaled multiplier `r·c` — the shared side-condition bundle for
`simpleDoleansExp_isMartingale`/`integral_eq_one` at scales `r`. -/
lemma stronglyMeasurable_mul_and_abs_mul_le {s : ℕ → ℝ≥0} {c : ℕ → Ω → ℝ}
    (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (r : ℝ) :
    (∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (fun ω ↦ r * c i ω))
      ∧ (∀ i ω, |r * c i ω| ≤ |r| * K) :=
  ⟨fun i ↦ (hc i).const_mul r, fun i ω ↦ by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hc_bdd i ω) (abs_nonneg r)⟩

include hX in
/-- Measurability of the simple Doléans density `Z_{−c}_T`. -/
lemma measurable_simpleDoleans {s : ℕ → ℝ≥0} (hs : Monotone s) {c : ℕ → Ω → ℝ}
    (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (N : ℕ) (T : ℝ≥0) :
    Measurable (fun ω ↦ simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) :=
  (((simpleDoleansExp_isMartingale (X := X) (P := P) s hs (fun i ω ↦ -(c i ω))
    (fun i ↦ (hc i).neg) (fun i ω ↦ by rw [abs_neg]; exact hc_bdd i ω) N).1 T).mono
      (𝓕.le T)).measurable

include hX in
/-- **Uniform `L⁴` bound on the simple Doléans density.** `∫ (Z_{−c}_T)⁴ ≤ exp(6K²T)`,
partition-free. `(Z_{−c})⁴ = E^{−4c}·exp(6·QV) ≤ exp(6K²T)·E^{−4c}` (`simpleDoleansExp_scaled_eq` at
`r = −1, −4` + `simpleQuadVar_le`), and `E^{−4c}` is a positive unit-mean density. -/
lemma quad_integral_simpleDoleans_le {s : ℕ → ℝ≥0} (hs : Monotone s) (hs0 : s 0 = 0) {c : ℕ → Ω → ℝ}
    (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (N : ℕ) {T : ℝ≥0} (hNT : T ≤ s N) :
    ∫ ω, (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) ^ 4 ∂P
      ≤ Real.exp (6 * K ^ 2 * (T : ℝ)) := by
  obtain ⟨h4m, h4b⟩ := stronglyMeasurable_mul_and_abs_mul_le (𝓕 := 𝓕) hc hc_bdd (-4)
  have hmean : ∫ ω, simpleDoleansExp (X := X) s (fun i ω ↦ (-4 : ℝ) * c i ω) N T ω ∂P = 1 :=
    simpleDoleansExp_integral_eq_one (X := X) s hs _ h4m h4b N T
  have hint4 : Integrable (fun ω ↦ simpleDoleansExp (X := X) s
      (fun i ω ↦ (-4 : ℝ) * c i ω) N T ω) P :=
    (simpleDoleansExp_isMartingale (X := X) (P := P) s hs _ h4m h4b N).integrable T
  have hpt : ∀ ω, (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) ^ 4
      ≤ Real.exp (6 * K ^ 2 * (T : ℝ)) * simpleDoleansExp (X := X) s
          (fun i ω ↦ (-4 : ℝ) * c i ω) N T ω := by
    intro ω
    rw [simpleDoleansExp_neg_eq, simpleDoleansExp_scaled_eq, ← Real.exp_nat_mul, ← Real.exp_add]
    exact Real.exp_le_exp.mpr
        (by push_cast; linarith [simpleQuadVar_le (Ω := Ω) hs hs0 hc_bdd N hNT ω])
  calc ∫ ω, (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) ^ 4 ∂P
      ≤ ∫ ω, Real.exp (6 * K ^ 2 * (T : ℝ)) * simpleDoleansExp (X := X) s
          (fun i ω ↦ (-4 : ℝ) * c i ω) N T ω ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω ↦ by positivity) (hint4.const_mul _)
          (ae_of_all _ hpt)
    _ = Real.exp (6 * K ^ 2 * (T : ℝ)) := by rw [integral_const_mul, hmean, mul_one]

include hX in
/-- **Uniform `L²` bound on the simple Doléans density.** `∫ (Z_{−c}_T)² ≤ exp(K²T)`, partition-free
(the `L²` analogue of `quad_integral_simpleDoleans_le`):
`(Z_{−c})² = E^{−2c}·exp(QV) ≤ exp(K²T)·E^{−2c}` (`simpleDoleansExp_scaled_eq` at `r = −1, −2` +
`simpleQuadVar_le`), and `E^{−2c}` is a positive unit-mean density. This is the `M` the limit
density's Fatou `L²` bound consumes. -/
lemma sq_integral_simpleDoleans_le {s : ℕ → ℝ≥0} (hs : Monotone s) (hs0 : s 0 = 0) {c : ℕ → Ω → ℝ}
    (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (N : ℕ) {T : ℝ≥0} (hNT : T ≤ s N) :
    ∫ ω, (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) ^ 2 ∂P
      ≤ Real.exp (K ^ 2 * (T : ℝ)) := by
  obtain ⟨h2m, h2b⟩ := stronglyMeasurable_mul_and_abs_mul_le (𝓕 := 𝓕) hc hc_bdd (-2)
  have hmean : ∫ ω, simpleDoleansExp (X := X) s (fun i ω ↦ (-2 : ℝ) * c i ω) N T ω ∂P = 1 :=
    simpleDoleansExp_integral_eq_one (X := X) s hs _ h2m h2b N T
  have hint2 : Integrable (fun ω ↦ simpleDoleansExp (X := X) s
      (fun i ω ↦ (-2 : ℝ) * c i ω) N T ω) P :=
    (simpleDoleansExp_isMartingale (X := X) (P := P) s hs _ h2m h2b N).integrable T
  have hpt : ∀ ω, (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) ^ 2
      ≤ Real.exp (K ^ 2 * (T : ℝ)) * simpleDoleansExp (X := X) s
          (fun i ω ↦ (-2 : ℝ) * c i ω) N T ω := by
    intro ω
    rw [simpleDoleansExp_neg_eq, simpleDoleansExp_scaled_eq, pow_two, ← Real.exp_add,
        ← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith [simpleQuadVar_le (Ω := Ω) hs hs0 hc_bdd N hNT ω])
  calc ∫ ω, (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) ^ 2 ∂P
      ≤ ∫ ω, Real.exp (K ^ 2 * (T : ℝ)) * simpleDoleansExp (X := X) s
          (fun i ω ↦ (-2 : ℝ) * c i ω) N T ω ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω ↦ sq_nonneg _) (hint2.const_mul _)
          (ae_of_all _ hpt)
    _ = Real.exp (K ^ 2 * (T : ℝ)) := by rw [integral_const_mul, hmean, mul_one]

include hX in
/-- **The simple Doléans density is in `L²`** (the `MemLp` form of `sq_integral_simpleDoleans_le`),
via the same `E^{−2c}` domination: `(Z_{−c})² ≤ exp(K²T)·E^{−2c}`, integrable. Feeds the predictable
density limit's Fatou `L²` bound as the per-`n` `MemLp` hypothesis. -/
lemma memLp_simpleDoleans_two {s : ℕ → ℝ≥0} (hs : Monotone s) (hs0 : s 0 = 0) {c : ℕ → Ω → ℝ}
    (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (N : ℕ) {T : ℝ≥0} (hNT : T ≤ s N) :
    MemLp (fun ω ↦ simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) 2 P := by
  obtain ⟨h2m, h2b⟩ := stronglyMeasurable_mul_and_abs_mul_le (𝓕 := 𝓕) hc hc_bdd (-2)
  have hZmeas := measurable_simpleDoleans (X := X) (P := P) hs hc hc_bdd N T
  have hint2 : Integrable (fun ω ↦ simpleDoleansExp (X := X) s
      (fun i ω ↦ (-2 : ℝ) * c i ω) N T ω) P :=
    (simpleDoleansExp_isMartingale (X := X) (P := P) s hs _ h2m h2b N).integrable T
  rw [memLp_two_iff_integrable_sq hZmeas.aestronglyMeasurable]
  refine (hint2.const_mul (Real.exp (K ^ 2 * (T : ℝ)))).mono'
    (hZmeas.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_of_nonneg (sq_nonneg _), simpleDoleansExp_neg_eq,
      simpleDoleansExp_scaled_eq, pow_two,
    ← Real.exp_add, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith [simpleQuadVar_le (Ω := Ω) hs hs0 hc_bdd N hNT ω])

include hX in
/-- **Uniform `L⁴`-integrability of the simple Doléans density** (the domination behind
`quad_integral_simpleDoleans_le`): `(Z_{−c})⁴ ≤ exp(6K²T)·E^{−4c}`, an integrable simple density. -/
lemma integrable_simpleDoleans_four {s : ℕ → ℝ≥0} (hs : Monotone s) (hs0 : s 0 = 0) {c : ℕ → Ω → ℝ}
    (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (N : ℕ) {T : ℝ≥0} (hNT : T ≤ s N) :
    Integrable (fun ω ↦ (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) ^ 4) P := by
  obtain ⟨h4m, h4b⟩ := stronglyMeasurable_mul_and_abs_mul_le (𝓕 := 𝓕) hc hc_bdd (-4)
  have hint4 : Integrable (fun ω ↦ simpleDoleansExp (X := X) s
      (fun i ω ↦ (-4 : ℝ) * c i ω) N T ω) P :=
    (simpleDoleansExp_isMartingale (X := X) (P := P) s hs _ h4m h4b N).integrable T
  refine (hint4.const_mul (Real.exp (6 * K ^ 2 * (T : ℝ)))).mono'
    ((measurable_simpleDoleans (X := X) (P := P) hs hc hc_bdd N T).pow_const 4).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  rw [Real.norm_of_nonneg (by positivity), simpleDoleansExp_neg_eq, simpleDoleansExp_scaled_eq,
    ← Real.exp_nat_mul, ← Real.exp_add]
  exact Real.exp_le_exp.mpr
      (by push_cast; linarith [simpleQuadVar_le (Ω := Ω) hs hs0 hc_bdd N hNT ω])

/-! ### The drift-corrected exponential `D_u = exp(a·(X_u + simpleDrift_u) − ½a²u)` -/

include hX in
omit [IsProbabilityMeasure P] [SigmaFiniteFiltration P 𝓕] in
/-- Measurability of the drift-corrected exponential `D_u`. -/
lemma measurable_driftExp {s : ℕ → ℝ≥0} (hs : Monotone s) {c : ℕ → Ω → ℝ}
    (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) (a : ℝ) (N : ℕ) (u : ℝ≥0) :
    Measurable (fun ω ↦ Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)) := by
  have hXu : Measurable (X u) := ((hX.stronglyAdapted u).mono (𝓕.le u)).measurable
  have hsd : Measurable (fun ω ↦ simpleDrift s c N u ω) :=
    ((stronglyMeasurable_simpleDrift hs hc N u).mono (𝓕.le u)).measurable
  fun_prop (disch := first | exact hXu | exact hsd)

include hX in
omit [IsProbabilityMeasure P] [SigmaFiniteFiltration P 𝓕] in
/-- **Uniform `L⁴` bound on the drift-corrected exponentials.**
`∫ (D_u)⁴ ≤ exp(4|a|KT)·𝔼[exp(4a·X_u)]`, `n`-independent
(`(D_u)⁴ = exp(4a·(X_u + drift) − 2a²u) ≤ exp(4|a|KT)·exp(4a·X_u)` since the drift is bounded by
`K·u ≤ K·T` and `−2a²u ≤ 0`). Only the multiplier *bound* is used, not adaptedness. -/
lemma quad_integral_driftExp_le {s : ℕ → ℝ≥0} (hs : Monotone s) (hs0 : s 0 = 0) {c : ℕ → Ω → ℝ}
    {K : ℝ} (hc_bdd : ∀ i ω, |c i ω| ≤ K) (a : ℝ) (N : ℕ) {u T : ℝ≥0} (huT : u ≤ T)
        (hNT : T ≤ s N) :
    ∫ ω, (Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)) ^ 4 ∂P
      ≤ Real.exp (4 * |a| * K * (T : ℝ)) * ∫ ω, Real.exp (4 * a * X u ω) ∂P := by
  have hMGF : Integrable (fun ω ↦ Real.exp (4 * a * X u ω)) P :=
    (hX.hasLaw_eval u).integrable_fun_comp (integrable_exp_mul_gaussianReal (4 * a))
  have hpt : ∀ ω, (Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)) ^ 4
      ≤ Real.exp (4 * |a| * K * (T : ℝ)) * Real.exp (4 * a * X u ω) := by
    intro ω
    have hK0 : (0 : ℝ) ≤ K := (abs_nonneg _).trans (hc_bdd 0 ω)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h4 : a * simpleDrift s c N u ω ≤ |a| * (K * (T : ℝ)) :=
      calc a * simpleDrift s c N u ω ≤ |a * simpleDrift s c N u ω| := le_abs_self _
        _ = |a| * |simpleDrift s c N u ω| := abs_mul _ _
        _ ≤ |a| * (K * (T : ℝ)) := mul_le_mul_of_nonneg_left
            ((simpleDrift_abs_le hs hs0 hc_bdd N (huT.trans hNT) ω).trans
              (mul_le_mul_of_nonneg_left (by exact_mod_cast huT) hK0)) (abs_nonneg a)
    push_cast
    nlinarith [h4, sq_nonneg a, u.coe_nonneg]
  calc ∫ ω, (Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)) ^ 4 ∂P
      ≤ ∫ ω, Real.exp (4 * |a| * K * (T : ℝ)) * Real.exp (4 * a * X u ω) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω ↦ by positivity) (hMGF.const_mul _)
          (ae_of_all _ hpt)
    _ = Real.exp (4 * |a| * K * (T : ℝ)) * ∫ ω,
        Real.exp (4 * a * X u ω) ∂P := integral_const_mul _ _

include hX in
omit [IsProbabilityMeasure P] [SigmaFiniteFiltration P 𝓕] in
/-- **Uniform `L⁴`-integrability of the drift-corrected exponential** (the domination behind
`quad_integral_driftExp_le`): `(D_u)⁴ ≤ exp(4|a|KT)·exp(4a·X_u)`, an integrable Gaussian MGF. -/
lemma integrable_driftExp_four {s : ℕ → ℝ≥0} (hs : Monotone s) (hs0 : s 0 = 0) {c : ℕ → Ω → ℝ}
    (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (a : ℝ) (N : ℕ) {u T : ℝ≥0} (huT : u ≤ T) (hNT : T ≤ s N) :
    Integrable
        (fun ω ↦ (Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)) ^ 4) P := by
  have hMGF : Integrable (fun ω ↦ Real.exp (4 * a * X u ω)) P :=
    (hX.hasLaw_eval u).integrable_fun_comp (integrable_exp_mul_gaussianReal (4 * a))
  refine (hMGF.const_mul (Real.exp (4 * |a| * K * (T : ℝ)))).mono'
    ((measurable_driftExp (X := X) (P := P) hs hc a N u).pow_const 4).aestronglyMeasurable
    (ae_of_all _ fun ω ↦ ?_)
  have hK0 : (0 : ℝ) ≤ K := (abs_nonneg _).trans (hc_bdd 0 ω)
  rw [Real.norm_of_nonneg (by positivity), ← Real.exp_nat_mul, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h4 : a * simpleDrift s c N u ω ≤ |a| * (K * (T : ℝ)) :=
    calc a * simpleDrift s c N u ω ≤ |a * simpleDrift s c N u ω| := le_abs_self _
      _ = |a| * |simpleDrift s c N u ω| := abs_mul _ _
      _ ≤ |a| * (K * (T : ℝ)) := mul_le_mul_of_nonneg_left
          ((simpleDrift_abs_le hs hs0 hc_bdd N (huT.trans hNT) ω).trans
            (mul_le_mul_of_nonneg_left (by exact_mod_cast huT) hK0)) (abs_nonneg a)
  push_cast
  nlinarith [h4, sq_nonneg a, u.coe_nonneg]

/-! ### The mixed-time product `D_u · Z_T`: `L²` membership and uniform second moment -/

/-- Pointwise AM–GM `(x·y)² ≤ ½(x⁴ + y⁴)` — the domination behind the mixed-product `L²` bound. -/
lemma sq_mul_le_half_add_pow4 (x y : ℝ) : (x * y) ^ 2 ≤ 2⁻¹ * (x ^ 4 + y ^ 4) := by
  nlinarith [sq_nonneg (x ^ 2 - y ^ 2), sq_nonneg (x * y)]

include hX in
/-- **The mixed-time product `D_u · Z_T` is in `L²`**, via the AM–GM domination
`(D·Z)² ≤ ½(D⁴ + Z⁴)` and the two `L⁴`-integrabilities. -/
lemma memLp_mixedProduct_two {s : ℕ → ℝ≥0} (hs : Monotone s) (hs0 : s 0 = 0) {c : ℕ → Ω → ℝ}
    (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (a : ℝ) (N : ℕ) {u T : ℝ≥0} (huT : u ≤ T) (hNT : T ≤ s N) :
    MemLp (fun ω ↦ Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)
      * simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) 2 P := by
  have hDmeas := measurable_driftExp (X := X) (P := P) hs hc a N u
  have hZmeas := measurable_simpleDoleans (X := X) (P := P) hs hc hc_bdd N T
  -- `Measurable.mul` concludes in the `Pi` form `g * h`, while the goal's `MemLp`
  -- is about the pointwise lambda; `rw` needs the syntactic form, so pin it here.
  have hDZ : Measurable fun ω ↦
      Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)
        * simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω := hDmeas.mul hZmeas
  rw [memLp_two_iff_integrable_sq hDZ.aestronglyMeasurable]
  refine (((integrable_driftExp_four (X := X) (P := P) hs hs0 hc hc_bdd a N huT hNT).add
    (integrable_simpleDoleans_four (X := X) (P := P) hs hs0 hc hc_bdd N hNT)).const_mul 2⁻¹).mono'
    (hDZ.pow_const 2).aestronglyMeasurable (ae_of_all _ fun ω ↦
      (Real.norm_of_nonneg (sq_nonneg _)).le.trans (sq_mul_le_half_add_pow4 _ _))

include hX in
/-- **Uniform second-moment bound on the mixed-time product**, `n`-independent:
`∫ (D_u·Z_T)² ≤ ½(exp(4|a|KT)·𝔼[exp(4a·X_u)] + exp(6K²T))`. This is the engine's `M`. -/
lemma sq_integral_mixedProduct_le {s : ℕ → ℝ≥0} (hs : Monotone s) (hs0 : s 0 = 0) {c : ℕ → Ω → ℝ}
    (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (a : ℝ) (N : ℕ) {u T : ℝ≥0} (huT : u ≤ T) (hNT : T ≤ s N) :
    ∫ ω, (Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)
      * simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) ^ 2 ∂P
      ≤ 2⁻¹ * (Real.exp (4 * |a| * K * (T : ℝ)) * (∫ ω, Real.exp (4 * a * X u ω) ∂P)
          + Real.exp (6 * K ^ 2 * (T : ℝ))) := by
  have hD4 := integrable_driftExp_four (X := X) (P := P) hs hs0 hc hc_bdd a N huT hNT
  have hZ4 := integrable_simpleDoleans_four (X := X) (P := P) hs hs0 hc hc_bdd N hNT
  calc ∫ ω, (Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)
        * simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) ^ 2 ∂P
      ≤ ∫ ω, 2⁻¹ * ((Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)) ^ 4
          + (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) ^ 4) ∂P :=
        integral_mono_of_nonneg (ae_of_all _ fun ω ↦ sq_nonneg _) ((hD4.add hZ4).const_mul _)
          (ae_of_all _ fun ω ↦ sq_mul_le_half_add_pow4 _ _)
    _ = 2⁻¹ * ((∫ ω, (Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)) ^ 4 ∂P)
          + ∫ ω, (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) ^ 4 ∂P) := by
        rw [integral_const_mul, integral_add hD4 hZ4]
    _ ≤ 2⁻¹ * (Real.exp (4 * |a| * K * (T : ℝ)) * (∫ ω, Real.exp (4 * a * X u ω) ∂P)
          + Real.exp (6 * K ^ 2 * (T : ℝ))) :=
        mul_le_mul_of_nonneg_left (add_le_add
          (quad_integral_driftExp_le (X := X) (P := P) (𝓕 := 𝓕) hs hs0 hc_bdd a N huT hNT)
          (quad_integral_simpleDoleans_le (X := X) (P := P) hs hs0 hc hc_bdd N hNT)) (by norm_num)

end SimpleDoleansMoments

end MathFin
