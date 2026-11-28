/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Probability.Distributions.Poisson.Basic

/-!
# Poisson random measure and the compensated increment

A *Poisson random measure* `N` on the time-mark space `[0, ∞) × E` with σ-finite
mark-intensity `ν` is the driving object of Lévy-driven stochastic calculus: `N(·, B)`
is `Poisson`-distributed with mean `ν̂(B)` (`ν̂ := Leb[0,∞) ⊗ ν`), and counts on disjoint
regions are independent. The *compensated* measure `Ñ(B) := N(B) − ν̂(B)` is the mean-zero,
`L²` object one integrates against.

This module provides the object as a hypothesis-bundling structure (its fields are the
Applebaum Def. 2.3.1 properties) plus the two Poisson moment facts the isometry needs —
`𝔼[N(B)] = ν̂(B)` and `𝔼[N(B)²] = ν̂(B)² + ν̂(B)` — hence `𝔼[Ñ(B)] = 0`, `𝔼[Ñ(B)²] = ν̂(B)`.

Mathlib carries the Poisson law (`poissonMeasure`, `integral_poissonMeasure`)
but *not* its mean or variance; we derive them here from the total-mass identity by a single
index shift (`(n+1)·pmf(n+1) = r·pmf(n)`), with no exp-series differentiation.

## Provenance

The `PoissonRandomMeasure` structure's field shape is consulted from
`cgarryZA/LevyStochCalc` (Apache-2.0), itself a faithful rendering of Applebaum Def. 2.3.1;
the isometry developed on top (see `PoissonCompensatedIsometryAdapted` / `…IntegralL2`) is our
own — LevyStochCalc states that isometry as its cited axiom #6, we prove it. References:
Applebaum, *Lévy Processes and Stochastic Calculus*, CUP 2009, Def. 2.3.1 / Thm 4.2.3.

## Main definitions

* `referenceIntensity`: the product measure `Leb[0, ∞) ⊗ ν` on the time-mark space `ℝ × E`.
* `PoissonRandomMeasure`: a family of counting measures `N ω` on `ℝ × E` that are measurable in
  `ω`, with `N(·, B) ∼ Poisson(ν̂ B)` for finite-intensity `B`, and counts on regions disjoint
  from `D` independent of the count on `D`.
* `PoissonRandomMeasure.compensated`: the compensated increment `Ñ(B) = N(B) − ν̂(B)`.
* `poissonMeasureENN`: the Poisson law pushed to `ℝ≥0∞`.

## Main results

* `poissonMeasure_integral_id`, `poissonMeasure_integral_sq`: the Poisson mean `r` and second
  moment `r² + r`.
* `compensated_integral_zero`: `𝔼[Ñ(B)] = 0` for measurable `B` of finite intensity.
* `compensated_integral_sq`: `𝔼[Ñ(B)²] = ν̂(B)` for measurable `B` of finite intensity.
* `memLp_compensated`: `Ñ(D) ∈ L²(P)` for measurable `D` of finite intensity.

## Tags

Poisson random measure, compensated measure, Lévy-driven calculus, mark intensity, Applebaum,
jump measure, MSC 60G55, MSC 60G51
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

/-! ## §1  Moments of the scalar Poisson law (Mathlib gap-fill) -/

/-- The Poisson pmf weight `c_r(n) = e^{-r} · r^n / n!`. Reducible so it folds/unfolds
cheaply against the summand of `integral_poissonMeasure` / `hasSum_one_poissonMeasure`. -/
@[reducible] private noncomputable def pw (r : ℝ≥0) (n : ℕ) : ℝ :=
  Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial

/-- The pmf weights sum to one. -/
private theorem hasSum_pw (r : ℝ≥0) : HasSum (pw r) 1 :=
  hasSum_one_poissonMeasure r

/-- **Shift identity** `(n+1)·c_r(n+1) = r·c_r(n)` — the engine of both moments. -/
private theorem pw_succ_mul (r : ℝ≥0) (n : ℕ) :
    ((n : ℝ) + 1) * pw r (n + 1) = (r : ℝ) * pw r n := by
  change ((n : ℝ) + 1) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (n + 1) / (n + 1).factorial)
      = (r : ℝ) * (Real.exp (-(r : ℝ)) * (r : ℝ) ^ n / n.factorial)
  rw [Nat.factorial_succ]
  have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
  have hf : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  push_cast
  field_simp
  ring

/-- **First moment sum**: `HasSum (fun n => c_r(n)·n) r`. -/
private theorem hasSum_pw_mul_id (r : ℝ≥0) :
    HasSum (fun n => pw r n * (n : ℝ)) (r : ℝ) := by
  have hshift : HasSum (fun n => pw r (n + 1) * ((n : ℝ) + 1)) (r : ℝ) := by
    have hbase : HasSum (fun n => (r : ℝ) * pw r n) (r : ℝ) := by
      simpa using (hasSum_pw r).mul_left (r : ℝ)
    have hfun : (fun n => pw r (n + 1) * ((n : ℝ) + 1)) = (fun n => (r : ℝ) * pw r n) := by
      funext n; rw [mul_comm (pw r (n + 1)) _, pw_succ_mul r n]
    rw [hfun]; exact hbase
  refine (hasSum_nat_add_iff' 1).mp ?_
  simpa using hshift

/-- **Poisson mean**: `∫ n, (n : ℝ) ∂poissonMeasure r = r`. -/
theorem poissonMeasure_integral_id (r : ℝ≥0) :
    ∫ n, (n : ℝ) ∂(poissonMeasure r) = (r : ℝ) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  exact (hasSum_pw_mul_id r).tsum_eq

/-- **Second-moment sum**: `HasSum (fun n => c_r(n)·n²) (r² + r)` — via `n² = n(n-1) + n`,
using the same `(n+1)·c_r(n+1) = r·c_r(n)` shift twice. -/
private theorem hasSum_pw_mul_sq (r : ℝ≥0) :
    HasSum (fun n => pw r n * (n : ℝ) ^ 2) ((r : ℝ) ^ 2 + (r : ℝ)) := by
  have hsum1 : HasSum (fun n => pw r n * (n : ℝ) + pw r n) ((r : ℝ) + 1) := by
    simpa using (hasSum_pw_mul_id r).add (hasSum_pw r)
  have hshift : HasSum (fun n => pw r (n + 1) * ((n : ℝ) + 1) ^ 2) ((r : ℝ) ^ 2 + (r : ℝ)) := by
    have hbase : HasSum (fun n => (r : ℝ) * (pw r n * (n : ℝ) + pw r n))
        ((r : ℝ) ^ 2 + (r : ℝ)) := by
      have := hsum1.mul_left (r : ℝ)
      have hval : (r : ℝ) * ((r : ℝ) + 1) = (r : ℝ) ^ 2 + (r : ℝ) := by ring
      rwa [hval] at this
    have hfun : (fun n => pw r (n + 1) * ((n : ℝ) + 1) ^ 2)
        = (fun n => (r : ℝ) * (pw r n * (n : ℝ) + pw r n)) := by
      funext n
      have hps := pw_succ_mul r n
      have hexp : pw r (n + 1) * ((n : ℝ) + 1) ^ 2
          = ((n : ℝ) + 1) * (((n : ℝ) + 1) * pw r (n + 1)) := by ring
      rw [hexp, hps]; ring
    rw [hfun]; exact hbase
  refine (hasSum_nat_add_iff' 1).mp ?_
  simpa using hshift

/-- **Poisson second moment**: `∫ n, (n : ℝ)^2 ∂poissonMeasure r = r^2 + r`. -/
theorem poissonMeasure_integral_sq (r : ℝ≥0) :
    ∫ n, (n : ℝ) ^ 2 ∂(poissonMeasure r) = (r : ℝ) ^ 2 + (r : ℝ) := by
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  exact (hasSum_pw_mul_sq r).tsum_eq

/-! ## §2  The Poisson random measure and its compensated increment -/

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]

/-- The Poisson law `Poisson(μ)` pushed to `ℝ≥0∞` (via `ℕ ↪ ℝ≥0∞`) — the law of the
extended-real count `N(·, B)`. -/
noncomputable def poissonMeasureENN (μ : ℝ≥0) : Measure ℝ≥0∞ :=
  (poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞))

/-- The reference intensity `Leb[0,∞) ⊗ ν` on the time-mark space `ℝ × E`. -/
noncomputable def referenceIntensity (ν : Measure E) : Measure (ℝ × E) :=
  (volume.restrict (Set.Ici (0 : ℝ))).prod ν

instance (ν : Measure E) [SigmaFinite ν] : SigmaFinite (referenceIntensity ν) :=
  inferInstanceAs (SigmaFinite ((volume.restrict (Set.Ici (0 : ℝ))).prod ν))

/-- **Poisson random measure on `[0,∞) × E`** with σ-finite mark-intensity `ν`, over a
probability space `(Ω, P)`. Its fields are the Applebaum (Def. 2.3.1) properties: each
`N(·, B)` is `Poisson(ν̂(B))`-distributed (`ν̂ = Leb[0,∞) ⊗ ν`), and `N` scatters
independently — the counts on any region disjoint from `D` are independent of `N(·, D)`
(`indep_of_disjoint_region`), which unifies disjoint-box independence with past/future
increment independence. Field shape consulted from `cgarryZA/LevyStochCalc` (cited); the
isometry built on it is our own. -/
structure PoissonRandomMeasure (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [SigmaFinite ν] where
  /-- The `ω`-indexed family of counting measures on the time-mark space `ℝ × E`. -/
  N : Ω → Measure (ℝ × E)
  /-- Each evaluation `ω ↦ N(ω, B)` is measurable. -/
  measurable_eval : ∀ {B : Set (ℝ × E)}, MeasurableSet B → Measurable (fun ω => N ω B)
  /-- `N(·, B)` has `Poisson(ν̂ B)` law under `P`, for finite-intensity `B`. -/
  poisson_law : ∀ {B : Set (ℝ × E)}, MeasurableSet B → referenceIntensity ν B ≠ ⊤ →
    P.map (fun ω => N ω B) = poissonMeasureENN (referenceIntensity ν B).toNNReal
  /-- **Independent scattering** (the defining Poisson-random-measure property, Applebaum
  Def. 2.3.1(2), in its `σ`-algebra form): the counts `N(·, C)` on *all* measurable regions
  `C` disjoint from `D`, jointly, are independent of the count `N(·, D)`. This single field
  drives every cross-term of the Itô–Lévy isometry: it subsumes both count-independence on
  disjoint boxes (take a two-element family) and past/future increment independence (the past
  at `s` lives on `(-∞,s] × E`, disjoint from any future box `(s,t] × A`). -/
  indep_of_disjoint_region : ∀ {D : Set (ℝ × E)}, MeasurableSet D →
    Indep
      (⨆ C ∈ {C : Set (ℝ × E) | Disjoint C D ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N ω C) inferInstance)
      (MeasurableSpace.comap (fun ω => N ω D) inferInstance) P

/-- The **compensated increment** `Ñ(B) := N(B) − ν̂(B)` (a real number for finite-intensity
`B`) — the mean-zero, `L²` object one integrates against. -/
noncomputable def PoissonRandomMeasure.compensated {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] (N : PoissonRandomMeasure P ν)
    (B : Set (ℝ × E)) (ω : Ω) : ℝ :=
  (N.N ω B).toReal - (referenceIntensity ν B).toReal

/-- The compensated increment `Ñ(B)` is measurable. -/
theorem PoissonRandomMeasure.measurable_compensated {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν] (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) : Measurable (N.compensated B) :=
  ((N.measurable_eval hB).ennreal_toReal).sub measurable_const

/-! ### Compensated-increment moments (transport of the scalar moments through `poisson_law`) -/

/-- Integral against `poissonMeasureENN` reduces to a `ℕ`-integral against `poissonMeasure`. -/
private theorem integral_poissonMeasureENN (μ : ℝ≥0) (g : ℝ≥0∞ → ℝ) (hg : Measurable g) :
    ∫ y, g y ∂(poissonMeasureENN μ) = ∫ n : ℕ, g (n : ℝ≥0∞) ∂(poissonMeasure μ) := by
  unfold poissonMeasureENN
  rw [integral_map (by fun_prop) hg.aestronglyMeasurable]

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- Transport `∫ g(N(B)) ∂P` to a Poisson `ℕ`-integral, via the `poisson_law` field. -/
private theorem integral_count_g (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤)
    (g : ℝ≥0∞ → ℝ) (hg : Measurable g) :
    ∫ ω, g (N.N ω B) ∂P
      = ∫ n : ℕ, g (n : ℝ≥0∞) ∂(poissonMeasure (referenceIntensity ν B).toNNReal) := by
  have h1 : ∫ ω, g (N.N ω B) ∂P = ∫ y, g y ∂(P.map (fun ω => N.N ω B)) :=
    (integral_map (N.measurable_eval hB).aemeasurable hg.aestronglyMeasurable).symm
  rw [h1, N.poisson_law hB hfin, integral_poissonMeasureENN _ _ hg]

/-- **Compensated first moment `HasSum`**: `∑' n, c_r(n)·(n − r) = 0`. -/
private theorem hasSum_pw_compensated (r : ℝ≥0) :
    HasSum (fun n => pw r n * ((n : ℝ) - (r : ℝ))) 0 := by
  have h : HasSum (fun n => pw r n * (n : ℝ) - (r : ℝ) * pw r n) ((r : ℝ) - (r : ℝ) * 1) :=
    (hasSum_pw_mul_id r).sub ((hasSum_pw r).mul_left (r : ℝ))
  rw [show (r : ℝ) - (r : ℝ) * 1 = 0 from by ring] at h
  have hfun : (fun n => pw r n * ((n : ℝ) - (r : ℝ)))
      = (fun n => pw r n * (n : ℝ) - (r : ℝ) * pw r n) := by funext n; ring
  rw [hfun]; exact h

/-- **Compensated second moment `HasSum`**: `∑' n, c_r(n)·(n − r)² = r`. -/
private theorem hasSum_pw_compensated_sq (r : ℝ≥0) :
    HasSum (fun n => pw r n * ((n : ℝ) - (r : ℝ)) ^ 2) (r : ℝ) := by
  have h : HasSum
      (fun n => pw r n * (n : ℝ) ^ 2 - 2 * (r : ℝ) * (pw r n * (n : ℝ)) + (r : ℝ) ^ 2 * pw r n)
      ((r : ℝ) ^ 2 + (r : ℝ) - 2 * (r : ℝ) * (r : ℝ) + (r : ℝ) ^ 2 * 1) :=
    ((hasSum_pw_mul_sq r).sub ((hasSum_pw_mul_id r).mul_left (2 * (r : ℝ)))).add
      ((hasSum_pw r).mul_left ((r : ℝ) ^ 2))
  rw [show (r : ℝ) ^ 2 + (r : ℝ) - 2 * (r : ℝ) * (r : ℝ) + (r : ℝ) ^ 2 * 1 = (r : ℝ) from by ring]
    at h
  have hfun : (fun n => pw r n * ((n : ℝ) - (r : ℝ)) ^ 2)
      = (fun n => pw r n * (n : ℝ) ^ 2 - 2 * (r : ℝ) * (pw r n * (n : ℝ)) + (r : ℝ) ^
          2 * pw r n) := by
    funext n; ring
  rw [hfun]; exact h

/-- **Compensated increment is mean-zero**: `𝔼[Ñ(B)] = 0` (finite-intensity `B`). -/
theorem compensated_integral_zero (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    ∫ ω, N.compensated B ω ∂P = 0 := by
  simp only [PoissonRandomMeasure.compensated]
  rw [integral_count_g N hB hfin
        (fun x => x.toReal - (referenceIntensity ν B).toReal) (by fun_prop)]
  simp only [ENNReal.toReal_natCast]
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  exact (hasSum_pw_compensated (referenceIntensity ν B).toNNReal).tsum_eq

/-- **Compensated increment second moment**: `𝔼[Ñ(B)²] = ν̂(B)` (finite-intensity `B`) —
this is the diagonal energy the Itô–Lévy isometry sums. -/
theorem compensated_integral_sq (N : PoissonRandomMeasure P ν) {B : Set (ℝ × E)}
    (hB : MeasurableSet B) (hfin : referenceIntensity ν B ≠ ⊤) :
    ∫ ω, (N.compensated B ω) ^ 2 ∂P = (referenceIntensity ν B).toReal := by
  simp only [PoissonRandomMeasure.compensated]
  rw [integral_count_g N hB hfin
        (fun x => (x.toReal - (referenceIntensity ν B).toReal) ^ 2) (by fun_prop)]
  simp only [ENNReal.toReal_natCast]
  rw [integral_poissonMeasure]
  simp only [smul_eq_mul]
  exact (hasSum_pw_compensated_sq (referenceIntensity ν B).toNNReal).tsum_eq

/-- **The compensated increment is `L²`**: `Ñ(D) ∈ L²(P)` for finite-intensity `D`. Its law is
`Poisson(ν̂ D)` pushed through `n ↦ n − ν̂ D`, whose second moment is finite — concretely
`∑ₙ c_r(n)·(n − r)² = r < ∞` (`hasSum_pw_compensated_sq`). This is the `L²`-membership each
simple-integrand term of the Itô–Lévy isometry needs. -/
theorem memLp_compensated (N : PoissonRandomMeasure P ν) {D : Set (ℝ × E)}
    (hD : MeasurableSet D) (hfin : referenceIntensity ν D ≠ ⊤) :
    MemLp (N.compensated D) 2 P := by
  refine (memLp_two_iff_integrable_sq (N.measurable_compensated hD).aestronglyMeasurable).mpr ?_
  have hrw : (fun ω => (N.compensated D ω) ^ 2)
      = (fun x : ℝ≥0∞ => (x.toReal - (referenceIntensity ν D).toReal) ^ 2) ∘
          (fun ω => N.N ω D) := rfl
  rw [hrw, ← integrable_map_measure (by fun_prop) (N.measurable_eval hD).aemeasurable,
      N.poisson_law hD hfin, poissonMeasureENN,
      integrable_map_measure (by fun_prop) (Measurable.aemeasurable (by fun_prop)),
      integrable_poissonMeasure_iff]
  refine ((hasSum_pw_compensated_sq (referenceIntensity ν D).toNNReal).summable).congr fun n => ?_
  simp only [Function.comp_apply, ENNReal.toReal_natCast, Real.norm_eq_abs]
  rw [abs_of_nonneg (sq_nonneg _)]
  rfl

end MathFin
