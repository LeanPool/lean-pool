/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.Girsanov.SimpleDoleansExponential
public import LeanPool.MathFin.Probability.Martingales.EquivMeasure
public import LeanPool.MathFin.Probability.Martingales.ChangeOfMeasure
public import LeanPool.MathFin.Probability.Brownian.ExpMartingaleQBrownian

/-!
# Simple (piecewise-constant adapted) Girsanov — the increments of `B^θ` under `Q`

Route-α, brick α3 (`docs/plans/2026-07-06-girsanov-track-alpha.md`). For a market price of risk
`θ` that is **simple** (piecewise-constant adapted) over a partition `s : ℕ → ℝ≥0` with bounded,
`𝓕_{s i}`-measurable multipliers `c`, the Girsanov density is the simple Doléans exponential
`Z_T = E^{−c}_T` (`simpleDoleansExp s (fun i ↦ −c i) N T`). Under `Q = P.withDensity Z_T`, the
drift-corrected process `B^θ_t = X_t + ∑_i c_i (s_{i+1}∧t − s_i∧t)` starts at `0`, has `N(0,t−s)`
increments, and independent increments (`HasIndepIncrements`) on `[0,T]`, which together fix every
finite-dimensional law of `B^θ` under `Q` on `[0,T]` to that of a standard Brownian motion; path
continuity is not stated. This is the bounded-**adapted**-θ Girsanov for the simple case, strictly
beyond constant θ, on the existing tower with no adapted-integrand Itô formula.

The route is the process-agnostic exponential characterization
`Probability/Brownian/ExpMartingaleQBrownian.isQBrownianMotion_of_expMartingale`: supply the
exponential martingale `exp(a·B^θ − ½a²·)` and read off those three properties, with no
characteristic-function chain re-derived. The two ingredients specific to simple θ are:
* the **spine** (`simple_spine`, `simple_spine_ae`): `E^{−c}·exp(a·B^θ − ½a²·) =ᵐ E^{a−c}`, i.e.
  `Z·D` is again a simple Doléans density (the "tilted density" trick);
* the **mixed-time integrability** (`integrable_expBthetaSimple_mul_density`): `D_u·Z_T ∈ L¹` by an
  `L²` Hölder — `D_u ∈ L²` by the Gaussian MGF of `X_u` with the drift bounded, and `Z_T ∈ L²`
  because `Z_T² = E^{−2c}_T · exp(∑ c_i²Δτ_i)` with `∑ c_i²Δτ_i ≤ K²T`.

## Main definitions

* `simpleDrift`: the piecewise-constant adapted drift `∑_{i<N} cᵢ (s_{i+1}∧t − s_i∧t)` added to `X`
  to form `B^θ_t = X_t + simpleDrift s c N t`.

## Main results

* `MathFin.simpleGirsanovMeasure_isProbabilityMeasure` — `Q = P.withDensity Z_T` is a probability
  measure;
* `MathFin.isExpQMartingale_BthetaSimple` — `B^θ` packaged as exponential-martingale data over
  `[0,T]`;
* `MathFin.Btheta_simple_isQBrownianMotion` — under `Q`, `B^θ` starts at `0`, has `N(0,t−s)`
  increments, and has independent increments on `[0,T]`.

## Tags

Girsanov theorem, change of measure, market price of risk, Doléans exponential,
risk-neutral measure, Brownian motion with drift, simple integrand, MSC 60H30, MSC 60J65, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℝ≥0 → Ω → ℝ}

/-- Every cell factor is `1` at time `0` (both clamped endpoints collapse to `0`). -/
lemma cellExp_zero (a b : ℝ≥0) (c : Ω → ℝ) (ω : Ω) : cellExp (X := X) a b c 0 ω = 1 := by
  rw [cellExp, min_eq_right (zero_le : (0:ℝ≥0) ≤ b), min_eq_right (zero_le : (0:ℝ≥0) ≤ a)]; simp

/-- The simple Doléans exponential is `1` at time `0`. -/
lemma simpleDoleansExp_zero (s : ℕ → ℝ≥0) (d : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    simpleDoleansExp (X := X) s d N 0 ω = 1 := by
  induction N with
  | zero => rfl
  | succ n ih =>
    change simpleDoleansExp (X := X) s d n 0 ω * cellExp (X := X) (s n) (s (n + 1)) (d n) 0 ω = 1
    rw [ih, cellExp_zero, mul_one]

/-- The simple Doléans exponential is strictly positive (a product of exponentials). -/
lemma simpleDoleansExp_pos (s : ℕ → ℝ≥0) (d : ℕ → Ω → ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    0 < simpleDoleansExp (X := X) s d N t ω := by
  induction N with
  | zero => exact one_pos
  | succ n ih =>
    change 0 < simpleDoleansExp (X := X) s d n t ω * cellExp (X := X) (s n) (s (n + 1)) (d n) t ω
    exact mul_pos ih (Real.exp_pos _)

/-- **The simple (piecewise-constant adapted) drift** `∑_{i<N} c_i · (s_{i+1}∧t − s_i∧t)`, clamped
to `[0,t]`: the drift added to `X` to form the simple-θ Girsanov process `B^θ_t = X_t + drift_t`.
Each cell contributes `c_i` times the length of its clamped time-interval. -/
noncomputable def simpleDrift (s : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ i ∈ Finset.range N,
    c i ω * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t))

/-- Each clamped cell-length `s_{i+1}∧t − s_i∧t` is nonnegative (the clamped endpoints are
monotone in the cell index). -/
lemma simpleTau_nonneg {s : ℕ → ℝ≥0} (hs : Monotone s) (i : ℕ) (t : ℝ≥0) :
    0 ≤ NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t) :=
  sub_nonneg.mpr (NNReal.coe_le_coe.mpr (min_le_min (hs (Nat.le_succ i)) le_rfl))

/-- The clamped cell-lengths sum to `t` when the partition covers `[0,t]` (`s_0 = 0`, `t ≤ s_N`). -/
lemma simpleTau_sum {s : ℕ → ℝ≥0} (hs0 : s 0 = 0) (N : ℕ) {t : ℝ≥0} (htN : t ≤ s N) :
    ∑ i ∈ Finset.range N,
        (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) = (t : ℝ) := by
  rw [Finset.sum_range_sub (fun i ↦ NNReal.toReal (min (s i) t)) N, min_eq_right htN, hs0,
    min_eq_left (zero_le : (0 : ℝ≥0) ≤ t)]
  simp

/-- The simple drift is bounded: `|simpleDrift s c N u| ≤ K·u` when `|c_i| ≤ K` and the partition
covers `[0,u]` (`s_0 = 0`, `u ≤ s_N`) — each cell contributes at most `K` times its length, and the
lengths sum to `u`. -/
lemma simpleDrift_abs_le {s : ℕ → ℝ≥0} (hs : Monotone s) (hs0 : s 0 = 0) {c : ℕ → Ω → ℝ} {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (N : ℕ) {u : ℝ≥0} (huN : u ≤ s N) (ω : Ω) :
    |simpleDrift s c N u ω| ≤ K * (u : ℝ) := by
  rw [simpleDrift]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  rw [← simpleTau_sum hs0 N huN, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ ↦ ?_
  rw [abs_mul, abs_of_nonneg (simpleTau_nonneg hs i u)]
  exact mul_le_mul_of_nonneg_right (hc_bdd i ω) (simpleTau_nonneg hs i u)

/-- The simple drift vanishes at time `0` (every clamped cell has zero length). -/
lemma simpleDrift_zero (s : ℕ → ℝ≥0) (c : ℕ → Ω → ℝ) (N : ℕ) (ω : Ω) :
    simpleDrift s c N 0 ω = 0 := by
  rw [simpleDrift]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [min_eq_right (zero_le : (0 : ℝ≥0) ≤ s (i + 1)), min_eq_right (zero_le : (0 : ℝ≥0) ≤ s i)]
  simp

/-- **Log-form of the simple Doléans exponential.** `simpleDoleansExp s d N t = exp(∑_{i<N}
[d_i·(X_{s_{i+1}∧t} − X_{s_i∧t}) − ½ d_i²·(s_{i+1}∧t − s_i∧t)])`: the product of cell exponentials
is a single exponential of a sum, so the Girsanov spine becomes one exponent identity. -/
lemma simpleDoleansExp_eq_exp_sum (s : ℕ → ℝ≥0) (d : ℕ → Ω → ℝ) (N : ℕ) (t : ℝ≥0) (ω : Ω) :
    simpleDoleansExp (X := X) s d N t ω
      = Real.exp (∑ i ∈ Finset.range N,
          (d i ω * (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
            - (d i ω) ^ 2
                * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) / 2)) := by
  induction N with
  | zero => simp [simpleDoleansExp]
  | succ n ih =>
    change simpleDoleansExp (X := X) s d n t ω * cellExp (X := X) (s n) (s (n + 1)) (d n) t ω = _
    rw [ih, cellExp, ← Real.exp_add, Finset.sum_range_succ]

/-- **The simple Girsanov spine.** `Z_t · exp(a·B^θ_t − ½a²t) = exp(a·X_0) · E^{a−c}_t`, where the
density `Z = E^{−c}` and the tilted density `E^{a−c}` are simple Doléans exponentials, and
`B^θ_t = X_t + simpleDrift_t`. This is the "`Z·D` is another exponential density" trick for simple
θ: the per-cell exponents `(−c_i)ΔX_i − ½c_i²Δτ_i` and `a·ΔX_i + a·c_i·Δτ_i − ½a²Δτ_i` combine to
`(a−c_i)ΔX_i − ½(a−c_i)²Δτ_i`, the `a−c` cell. Needs the partition to cover `[0,t]`
(`s_0 = 0`, `t ≤ T ≤ s_N`), so the increments telescope to `X_t − X_0` and `t`. Combined with
`X_0 = 0` a.e. it gives `Z·D =ᵐ E^{a−c}`. -/
lemma simple_spine (s : ℕ → ℝ≥0) (hs0 : s 0 = 0) (c : ℕ → Ω → ℝ) (a : ℝ) (N : ℕ)
    {t T : ℝ≥0} (htT : t ≤ T) (hNT : T ≤ s N) (ω : Ω) :
    simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N t ω
        * Real.exp (a * (X t ω + simpleDrift s c N t ω) - a ^ 2 * (t : ℝ) / 2)
      = Real.exp (a * X 0 ω)
        * simpleDoleansExp (X := X) s (fun i ω ↦ a - c i ω) N t ω := by
  rw [simpleDoleansExp_eq_exp_sum, simpleDoleansExp_eq_exp_sum, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have htN : min (s N) t = t := min_eq_right (htT.trans hNT)
  have h0t : min (s 0) t = 0 := by rw [hs0]; exact min_eq_left (zero_le : (0 : ℝ≥0) ≤ t)
  have hβX : ∑ i ∈ Finset.range N, (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
      = X t ω - X 0 ω := by
    rw [Finset.sum_range_sub (fun i ↦ X (min (s i) t) ω) N, htN, h0t]
  have hβτ : ∑ i ∈ Finset.range N,
      (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) = (t : ℝ) := by
    rw [Finset.sum_range_sub (fun i ↦ NNReal.toReal (min (s i) t)) N, htN, h0t]; simp
  have key :
      (∑ i ∈ Finset.range N,
          ((a - c i ω) * (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
            - (a - c i ω) ^ 2
                * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) / 2))
        - (∑ i ∈ Finset.range N,
          ((-(c i ω)) * (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
            - (-(c i ω)) ^ 2
                * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) / 2))
      = a * (X t ω - X 0 ω) + a * simpleDrift s c N t ω - a ^ 2 * (t : ℝ) / 2 := by
    rw [← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun i _ ↦ show
        ((a - c i ω) * (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
            - (a - c i ω) ^ 2
                * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) / 2)
          - ((-(c i ω)) * (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
            - (-(c i ω)) ^ 2
                * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)) / 2)
        = a * (X (min (s (i + 1)) t) ω - X (min (s i) t) ω)
            + a * (c i ω * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t)))
            - a ^ 2 / 2 * (NNReal.toReal (min (s (i + 1)) t) - NNReal.toReal (min (s i) t))
        from by ring),
      Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, hβX, hβτ]
    simp only [simpleDrift]; ring
  linear_combination -key

variable {P : Measure Ω} [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
  [SigmaFiniteFiltration P 𝓕] [hX : IsFilteredPreBrownian X 𝓕 P]

include hX in
/-- **Unit `P`-mean of the density.** `∫ Z_T dP = 1`: the martingale property equates the mean at
`T` with the mean at `0`, where `Z_0 = 1`. -/
theorem simpleDoleansExp_integral_eq_one (s : ℕ → ℝ≥0) (hs : Monotone s) (d : ℕ → Ω → ℝ)
    (hd : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (d i)) {K : ℝ}
    (hd_bdd : ∀ i ω, |d i ω| ≤ K) (N : ℕ) (T : ℝ≥0) :
    ∫ ω, simpleDoleansExp (X := X) s d N T ω ∂P = 1 := by
  have hmart := simpleDoleansExp_isMartingale (X := X) (P := P) s hs d hd hd_bdd N
  have hmean :=
      hmart.setIntegral_eq (i := 0) (j := T) (zero_le : (0:ℝ≥0) ≤ T) (s := Set.univ)
      MeasurableSet.univ
  simp only [Measure.restrict_univ] at hmean
  calc ∫ ω, simpleDoleansExp (X := X) s d N T ω ∂P
      = ∫ ω, simpleDoleansExp (X := X) s d N 0 ω ∂P := hmean.symm
    _ = ∫ _, (1 : ℝ) ∂P :=
        integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ simpleDoleansExp_zero s d N ω)
    _ = 1 := by simp

include hX in
/-- **The simple Girsanov measure is a probability measure.** `Q = P.withDensity Z_T` with the
positive, unit-mean simple Doléans density `Z_T`. -/
theorem simpleGirsanovMeasure_isProbabilityMeasure (s : ℕ → ℝ≥0) (hs : Monotone s) (d : ℕ → Ω → ℝ)
    (hd : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (d i)) {K : ℝ}
    (hd_bdd : ∀ i ω, |d i ω| ≤ K) (N : ℕ) (T : ℝ≥0) :
    IsProbabilityMeasure
      (P.withDensity fun ω ↦ ENNReal.ofReal (simpleDoleansExp (X := X) s d N T ω)) := by
  have hmart := simpleDoleansExp_isMartingale (X := X) (P := P) s hs d hd hd_bdd N
  exact (isEquivProbMeasure_withDensity P (fun ω ↦ simpleDoleansExp_pos s d N T ω)
    (hmart.integrable T) (simpleDoleansExp_integral_eq_one s hs d hd hd_bdd N T)).isProb

/-- **Adaptedness of the simple drift.** `simpleDrift s c N u` is `𝓕_u`-measurable when the
multipliers are adapted (`c i` is `𝓕_{s i}`-measurable): each cell contributes
`c_i · (s_{i+1}∧u − s_i∧u)`, and either `s_i ≤ u` (so `c_i` is `𝓕_u`-measurable) or `u ≤ s_i`
(so the clamped interval length is `0`). -/
lemma stronglyMeasurable_simpleDrift {s : ℕ → ℝ≥0} (hs : Monotone s) {c : ℕ → Ω → ℝ}
    (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) (N : ℕ) (u : ℝ≥0) :
    StronglyMeasurable[(𝓕 u : MeasurableSpace Ω)] (fun ω ↦ simpleDrift s c N u ω) := by
  have hfun : (fun ω ↦ simpleDrift s c N u ω)
      = ∑ i ∈ Finset.range N,
          (fun ω ↦ c i ω * (NNReal.toReal (min (s (i + 1)) u) - NNReal.toReal (min (s i) u))) := by
    funext ω; simp only [simpleDrift, Finset.sum_apply]
  rw [hfun]
  apply Finset.stronglyMeasurable_sum
  intro i _
  rcases le_total (s i) u with hiu | hui
  · exact ((hc i).mono (𝓕.mono hiu)).mul_const _
  · have hτ : NNReal.toReal (min (s (i + 1)) u) - NNReal.toReal (min (s i) u) = 0 := by
      rw [min_eq_right (hui.trans (hs (Nat.le_succ i))), min_eq_right hui]; ring
    simp only [hτ, mul_zero]
    exact stronglyMeasurable_const

omit [IsProbabilityMeasure P] [SigmaFiniteFiltration P 𝓕] in
include hX in
/-- The pre-Brownian motion starts at `0` a.e.: `X_0` has law `𝒩(0,0) = δ_0`. -/
theorem X0_ae_eq_zero : ∀ᵐ ω ∂P, X 0 ω = 0 := by
  have hmeasX0 : Measurable (X 0) := ((hX.stronglyAdapted 0).mono (𝓕.le 0)).measurable
  have hmap := Measure.map_apply (μ := P) hmeasX0 (measurableSet_singleton (0 : ℝ)).compl
  rw [(hX.hasLaw_eval 0).map_eq, gaussianReal_zero_var,
      Measure.dirac_apply' _ (measurableSet_singleton (0 : ℝ)).compl] at hmap
  have hpre : X 0 ⁻¹' {(0 : ℝ)}ᶜ = {ω | X 0 ω ≠ 0} := by ext ω; simp [Set.mem_preimage]
  rw [hpre] at hmap
  exact ae_iff.mpr (by simpa using hmap.symm)

omit [IsProbabilityMeasure P] [SigmaFiniteFiltration P 𝓕] in
include hX in
/-- **The simple Girsanov spine, a.e. form.** For a partition covering `[0,t]` (`s_0 = 0`,
`t ≤ T ≤ s_N`), the product of the density `Z = E^{−c}` and the drift-corrected exponential
`exp(a·B^θ_t − ½a²t)` is a.e. equal to the tilted simple Doléans exponential `E^{a−c}_t` — because
`X_0 = 0` a.e. `P` kills the `exp(a·X_0)` factor of `simple_spine`. This is the "`Z·D` is another
exponential density" identity that will feed the Bayes change-of-measure engine, exactly as
`Wald(−θ)·Wald(a)` collapses to `Wald(a−θ)` in the constant-θ file. -/
theorem simple_spine_ae (s : ℕ → ℝ≥0) (hs0 : s 0 = 0) (c : ℕ → Ω → ℝ) (a : ℝ) (N : ℕ)
    {t T : ℝ≥0} (htT : t ≤ T) (hNT : T ≤ s N) :
    (fun ω ↦ simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N t ω
        * Real.exp (a * (X t ω + simpleDrift s c N t ω) - a ^ 2 * (t : ℝ) / 2))
      =ᵐ[P] fun ω ↦ simpleDoleansExp (X := X) s (fun i ω ↦ a - c i ω) N t ω := by
  filter_upwards [X0_ae_eq_zero (X := X) (𝓕 := 𝓕)] with ω hω
  rw [simple_spine s hs0 c a N htT hNT ω, hω, mul_zero, Real.exp_zero, one_mul]

include hX in
/-- **Mixed-time integrability for the Bayes engine.** For `u ≤ T ≤ s_N`, the product
`exp(a·B^θ_u − ½a²u) · Z_T` (with density `Z = E^{−c}`) is `P`-integrable. Both factors are in
`L²(P)`: the drift-corrected exponential by the Gaussian MGF of `X_u` (the drift is bounded by
`K·u`), and the density because `Z_T² = E^{−2c}_T · exp(∑ c_i²Δτ_i)` with `∑ c_i²Δτ_i ≤ K²T`, an
integrable martingale times a bounded factor. Hölder (`MemLp.mul`, `L²·L² ⊆ L¹`) closes it. -/
theorem integrable_expBthetaSimple_mul_density (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (c : ℕ → Ω → ℝ) (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i))
    {K : ℝ} (hc_bdd : ∀ i ω, |c i ω| ≤ K) (a : ℝ) (N : ℕ) {u T : ℝ≥0} (huT : u ≤ T)
    (hNT : T ≤ s N) :
    Integrable (fun ω ↦
        Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)
          * simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) P := by
  have hmeasX : ∀ v, Measurable (X v) := fun v ↦ ((hX.stronglyAdapted v).mono (𝓕.le v)).measurable
  have hDsm : StronglyMeasurable[(𝓕 u : MeasurableSpace Ω)]
      (fun ω ↦ Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)) := by
    have hcont : Continuous fun x : ℝ ↦ a * x - a ^ 2 * (u : ℝ) / 2 := by fun_prop
    exact Real.continuous_exp.comp_stronglyMeasurable (hcont.comp_stronglyMeasurable
      ((hX.stronglyAdapted u).add (stronglyMeasurable_simpleDrift hs hc N u)))
  have hDmeas : Measurable
      (fun ω ↦ Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)) :=
    (hDsm.mono (𝓕.le u)).measurable
  -- density multipliers `−c` and `−2c` are adapted and bounded
  have hdneg : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (fun ω ↦ -(c i ω)) :=
    fun i ↦ (hc i).neg
  have hbneg : ∀ i ω, |(-(c i ω))| ≤ K := fun i ω ↦ by rw [abs_neg]; exact hc_bdd i ω
  have hd2 : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (fun ω ↦ -(2 * c i ω)) :=
    fun i ↦ ((hc i).const_mul 2).neg
  have hb2 : ∀ i ω, |(-(2 * c i ω))| ≤ 2 * K := fun i ω ↦ by
    rw [abs_neg, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    exact mul_le_mul_of_nonneg_left (hc_bdd i ω) (by norm_num)
  have hZmeasT : Measurable (fun ω ↦ simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) :=
    (((simpleDoleansExp_isMartingale (X := X) (P := P) s hs _ hdneg hbneg N).1 T).mono
      (𝓕.le T)).measurable
  -- `D_u ∈ L²`: Gaussian MGF of `X_u`, drift bounded
  have hDu2 : MemLp (fun ω ↦
      Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)) 2 P := by
    rw [memLp_two_iff_integrable_sq hDmeas.aestronglyMeasurable]
    refine Integrable.mono'
      (g := fun ω ↦ Real.exp (2 * |a| * K * (T : ℝ)) * Real.exp (2 * a * X u ω))
      (((hX.hasLaw_eval u).integrable_fun_comp
        (integrable_exp_mul_gaussianReal (2 * a))).const_mul _)
      (hDmeas.pow_const 2).aestronglyMeasurable (Filter.Eventually.of_forall fun ω ↦ ?_)
    have hK0 : (0 : ℝ) ≤ K := (abs_nonneg (c 0 ω)).trans (hc_bdd 0 ω)
    have hdrift := simpleDrift_abs_le hs hs0 hc_bdd N (huT.trans hNT) ω
    rw [Real.norm_of_nonneg (sq_nonneg _), pow_two, ← Real.exp_add, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have h1 : a * simpleDrift s c N u ω ≤ |a| * (K * (u : ℝ)) :=
      (le_abs_self _).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hdrift (abs_nonneg a))
    have h2 : |a| * (K * (u : ℝ)) ≤ |a| * (K * (T : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (by exact_mod_cast huT) hK0) (abs_nonneg a)
    simp only [mul_add]
    nlinarith [h1, h2, mul_nonneg (sq_nonneg a) (NNReal.coe_nonneg u)]
  -- `Z_T ∈ L²`: `Z_T² = E^{−2c}_T · exp(∑ c²Δτ) ≤ exp(K²T)·E^{−2c}_T`
  have hZT2 : MemLp (fun ω ↦ simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) 2 P := by
    rw [memLp_two_iff_integrable_sq hZmeasT.aestronglyMeasurable]
    have hZ2c_int : Integrable
        (fun ω ↦ simpleDoleansExp (X := X) s (fun i ω ↦ -(2 * c i ω)) N T ω) P :=
      (simpleDoleansExp_isMartingale (X := X) (P := P) s hs _ hd2 hb2 N).integrable T
    refine Integrable.mono'
      (g := fun ω ↦ Real.exp (K ^ 2 * (T : ℝ))
        * simpleDoleansExp (X := X) s (fun i ω ↦ -(2 * c i ω)) N T ω)
      (hZ2c_int.const_mul _) (hZmeasT.pow_const 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun ω ↦ ?_)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have hZsq_eq : (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) ^ 2
        = simpleDoleansExp (X := X) s (fun i ω ↦ -(2 * c i ω)) N T ω
          * Real.exp (∑ i ∈ Finset.range N, (c i ω) ^ 2
              * (NNReal.toReal (min (s (i + 1)) T) - NNReal.toReal (min (s i) T))) := by
      rw [simpleDoleansExp_eq_exp_sum, simpleDoleansExp_eq_exp_sum, pow_two, ← Real.exp_add,
        ← Real.exp_add]
      congr 1
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun i _ ↦ by ring)
    rw [hZsq_eq]
    have hSumBnd : ∑ i ∈ Finset.range N, (c i ω) ^ 2
        * (NNReal.toReal (min (s (i + 1)) T) - NNReal.toReal (min (s i) T)) ≤ K ^ 2 * (T : ℝ) := by
      rw [← simpleTau_sum hs0 N hNT, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_right ?_ (simpleTau_nonneg hs i T)
      nlinarith [(abs_le.mp (hc_bdd i ω)).1, (abs_le.mp (hc_bdd i ω)).2]
    rw [mul_comm (Real.exp (K ^ 2 * (T : ℝ)))]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hSumBnd)
      (simpleDoleansExp_pos s _ N T ω).le
  exact (memLp_one_iff_integrable.mp (hZT2.mul hDu2)).congr
    (Filter.Eventually.of_forall fun ω ↦ mul_comm _ _)

include hX in
/-- **The simple-θ drift-corrected process, packaged as exponential-martingale data.** For a
partition covering `[0,T]` (`s_0 = 0`, `T ≤ s_N`) with bounded adapted multipliers `c`, the
drift-corrected process `B^θ_u = X_u + simpleDrift_u` is `𝓕`-adapted, starts at `0` a.e. under
`Q = P.withDensity(E^{−c}_T)`, and for every `a` the exponential `exp(a·B^θ − ½a²·)` is a
`Q`-martingale on `[0,T]`. The martingale field feeds the Bayes engine (`Z = E^{−c}` and
`Z·D =ᵐ E^{a−c}`, the α2 martingale): `∫_A D_u dQ = ∫_A Z_u D_u dP` (mixed-time integrability from
`integrable_expBthetaSimple_mul_density`), then `Z_u D_u =ᵐ E^{a−c}_u` (`simple_spine_ae`) turns the
`Q`-martingale identity into the `P`-martingale identity of `E^{a−c}`. -/
theorem isExpQMartingale_BthetaSimple (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (c : ℕ → Ω → ℝ) (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (N : ℕ) {T : ℝ≥0} (hNT : T ≤ s N) :
    IsExpQMartingale
      (P.withDensity fun ω ↦
        ENNReal.ofReal (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω))
      𝓕 (fun u ω ↦ X u ω + simpleDrift s c N u ω) T := by
  have hdneg : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (fun ω ↦ -(c i ω)) :=
    fun i ↦ (hc i).neg
  have hbneg : ∀ i ω, |(-(c i ω))| ≤ K := fun i ω ↦ by rw [abs_neg]; exact hc_bdd i ω
  have hZmart : Martingale (fun u ω ↦ simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N u ω) 𝓕 P :=
    simpleDoleansExp_isMartingale (X := X) s hs _ hdneg hbneg N
  have hZmeasT : Measurable (fun ω ↦ simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω) :=
    ((hZmart.1 T).mono (𝓕.le T)).measurable
  have hZpos : ∀ ω, 0 ≤ simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω :=
    fun ω ↦ (simpleDoleansExp_pos s _ N T ω).le
  refine ⟨fun u ↦ (hX.stronglyAdapted u).add (stronglyMeasurable_simpleDrift hs hc N u), ?_, ?_⟩
  · -- zero start: `X_0 = 0` a.e. `Q` (`Q ≪ P`), `simpleDrift_0 = 0`
    have hQP : (P.withDensity fun ω ↦
        ENNReal.ofReal (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω)) ≪ P :=
      withDensity_absolutelyContinuous _ _
    filter_upwards [hQP.ae_le (X0_ae_eq_zero (X := X) (𝓕 := 𝓕))] with ω hω
    simp [hω, simpleDrift_zero]
  · -- martingale field via the Bayes `[0,T]` change-of-measure engine: `Z = E^{−c}`, the drift-
    -- corrected exponential `D`, and `M = E^{a−c}` with `Z·D =ᵐ M` on `[0,T]` (`simple_spine_ae`).
    intro a s' t' hst' ht'T A hA
    have hEsm : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (fun ω ↦ a - c i ω) :=
      fun i ↦ stronglyMeasurable_const.sub (hc i)
    have hEb : ∀ i ω, |a - c i ω| ≤ |a| + K := fun i ω ↦ by
      rw [abs_le]; obtain ⟨h1, h2⟩ := abs_le.mp (hc_bdd i ω)
      refine ⟨?_, ?_⟩ <;> nlinarith [neg_abs_le a, le_abs_self a]
    have hEmart :
        Martingale (fun u ω ↦ simpleDoleansExp (X := X) s (fun i ω ↦ a - c i ω) N u ω) 𝓕 P :=
      simpleDoleansExp_isMartingale (X := X) s hs _ hEsm hEb N
    have hDsm : ∀ u, StronglyMeasurable[(𝓕 u : MeasurableSpace Ω)]
        (fun ω ↦ Real.exp (a * (X u ω + simpleDrift s c N u ω) - a ^ 2 * (u : ℝ) / 2)) := by
      intro u
      have hcont : Continuous fun x : ℝ ↦ a * x - a ^ 2 * (u : ℝ) / 2 := by fun_prop
      exact Real.continuous_exp.comp_stronglyMeasurable (hcont.comp_stronglyMeasurable
        ((hX.stronglyAdapted u).add (stronglyMeasurable_simpleDrift hs hc N u)))
    exact changeOfMeasure_setIntegral_eq_of_ae_martingale T hZmeasT hZpos hDsm hZmart hEmart
      (fun u huT ↦ simple_spine_ae (𝓕 := 𝓕) s hs0 c a N huT hNT)
      (fun u huT ↦ integrable_expBthetaSimple_mul_density s hs hs0 c hc hc_bdd a N huT hNT)
      hst' ht'T hA

include hX in
/-- **Simple (piecewise-constant adapted) distributional Girsanov: the increments of `B^θ` under
`Q`.** For a partition covering `[0,T]` (`s_0 = 0`, `T ≤ s_N`) and bounded adapted multipliers `c`,
under `Q = P.withDensity(E^{−c}_T)` the drift-corrected process
`B^θ_t = X_t + ∑_i c_i (s_{i+1}∧t − s_i∧t)` has, on `[0,T]`: zero start, Gaussian increments
`N(0,t−s)`, and independent increments (`HasIndepIncrements`), which fix its finite-dimensional laws
on `[0,T]`; path continuity is not stated. One application of the exponential characterization
`isQBrownianMotion_of_expMartingale` to `isExpQMartingale_BthetaSimple` — no characteristic-function
chain re-derived (the whole payoff of the abstraction). This is the general bounded-*adapted*-θ
Girsanov for the simple case, strictly beyond constant θ, on the existing tower — no
adapted-integrand Itô formula. -/
theorem Btheta_simple_isQBrownianMotion (s : ℕ → ℝ≥0) (hs : Monotone s) (hs0 : s 0 = 0)
    (c : ℕ → Ω → ℝ) (hc : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (c i)) {K : ℝ}
    (hc_bdd : ∀ i ω, |c i ω| ≤ K) (N : ℕ) {T : ℝ≥0} (hNT : T ≤ s N) :
    IsBrownianOn (P.withDensity fun ω ↦
      ENNReal.ofReal (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω)) T
      fun t ω ↦ X t ω + simpleDrift s c N t ω := by
  have hdneg : ∀ i, StronglyMeasurable[(𝓕 (s i) : MeasurableSpace Ω)] (fun ω ↦ -(c i ω)) :=
    fun i ↦ (hc i).neg
  have hbneg : ∀ i ω, |(-(c i ω))| ≤ K := fun i ω ↦ by rw [abs_neg]; exact hc_bdd i ω
  have : IsProbabilityMeasure (P.withDensity fun ω ↦
      ENNReal.ofReal (simpleDoleansExp (X := X) s (fun i ω ↦ -(c i ω)) N T ω)) :=
    simpleGirsanovMeasure_isProbabilityMeasure (X := X) (𝓕 := 𝓕) s hs _ hdneg hbneg N T
  exact isQBrownianMotion_of_expMartingale
    (isExpQMartingale_BthetaSimple (X := X) (𝓕 := 𝓕) s hs hs0 c hc hc_bdd N hNT)

end MathFin
