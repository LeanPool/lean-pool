/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.Multidim
public import LeanPool.KLS.LevyStochCalc.Brownian.MultidimIto
public import LeanPool.KLS.LevyStochCalc.Poisson.L2Isometry

/-!
# Jump-diffusion process structure

A *jump diffusion* on `ℝⁿ` driven by a `d`-dimensional Brownian motion `W` and
a Poisson random measure `N` (with intensity `dt ⊗ ν` on `[0,T] × E`) is the
solution of the SDE

  `dX_t = μ(t, X_t) dt + σ(t, X_t) dW_t + ∫_E γ(t, X_{t-}, e) Ñ(dt, de)`,

with `X_0 = x_0`. Under Lipschitz `(μ, σ, γ)` the SDE admits a unique càdlàg
adapted solution with `𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞`.

Reference: Applebaum 2009 Ch 6; Ikeda-Watanabe IV.

## Well-posedness

`JumpDiffusion.exists_unique` (Applebaum 6.2.9 / Ikeda-Watanabe IV) is stated
in `Ito/PicardFixedPoint.lean` and forwards to
`Ito.Picard.exists_jumpDiffusion_unique_of_solvesOn` (`Ito/PicardWellPosed.lean`),
proved by Picard iteration in the Bielecki-weighted process space on each
window and by gluing the windows. It asks for
`JumpDiffusionCoeffs.IsRegular` alongside `IsLipschitz`: the Lipschitz
clauses constrain the coefficients only in the state variable, and without
regularity in `s` (and in `e` for `γ`) no `JumpDiffusion` exists at all —
`σ s x = 1 / s` and `σ s x = 1_A s` for non-measurable `A` are Lipschitz
with `L = 0` and defeat the `is_solution` existential for every path map.
See `Ito/PicardSpace.lean`, "The `IsRegular` hypothesis and the `S²` norm".

The `is_solution` field of the `JumpDiffusion` structure is the actual SDE
integral equation (bundled with the hypotheses on `σ(s, X_s)` needed for the
multidim Brownian integral to be defined), so a constant path `X = x₀` does
not satisfy the structure for generic non-zero coefficients.

`is_solution` quantifies over a filtration `ℱ` for which every coordinate of `W`
is a Brownian motion and `N` a Poisson random measure, and asks both coefficient
bundles to be progressive for that one `ℱ`; coupled `(σ, γ)` are therefore in
scope. Such a filtration exists — `LevyStochCalc/Driver/Existence.lean`,
`exists_isBrownianFiltration_and_isPoissonFiltration`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Ito.Setting

universe u v

section Coefficients
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- Coefficient bundle for a jump diffusion: drift `μ`, diffusion `σ`, jump
size `γ`. Lipschitz / measurability hypotheses live on the headline theorem. -/
structure JumpDiffusionCoeffs (n d : ℕ) (E : Type v) where
  /-- The time- and state-dependent drift coefficient. -/
  μ : ℝ → (Fin n → ℝ) → (Fin n → ℝ)
  /-- The time- and state-dependent diffusion coefficient. -/
  σ : ℝ → (Fin n → ℝ) → (Fin n → Fin d → ℝ)
  /-- The time-, state- and mark-dependent jump coefficient. -/
  γ : ℝ → (Fin n → ℝ) → E → (Fin n → ℝ)

/-- Joint Lipschitz hypothesis on the jump-diffusion coefficients
`(μ, σ, γ)`. Required for `JumpDiffusion.exists_unique` (Applebaum 2009
Thm 6.2.9 — without this, Tanaka's example shows uniqueness can fail,
e.g. `dX_t = |X_t|^α dW_t` for `α < 1/2` has infinitely many strong
solutions; cf. Karatzas-Shreve 5.3.2). -/
def JumpDiffusionCoeffs.IsLipschitz {n d : ℕ}
    (coeffs : JumpDiffusionCoeffs n d E) (ν : Measure E) (L : ℝ) : Prop :=
  0 ≤ L ∧
  -- μ uniformly Lipschitz in x:
  (∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
    ‖coeffs.μ s x₁ - coeffs.μ s x₂‖ ≤ L * ‖x₁ - x₂‖) ∧
  -- σ uniformly Lipschitz in x (with the Frobenius / Euclidean norm on matrices):
  (∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
    (∑ i, ∑ j, (coeffs.σ s x₁ i j - coeffs.σ s x₂ i j) ^ 2)
      ≤ L ^ 2 * ‖x₁ - x₂‖ ^ 2) ∧
  -- γ uniformly Lipschitz in x (L²-in-e sense):
  (∀ s : ℝ, ∀ x₁ x₂ : Fin n → ℝ,
    ∫⁻ e, (‖coeffs.γ s x₁ e - coeffs.γ s x₂ e‖₊ : ℝ≥0∞) ^ 2 ∂ν
      ≤ ENNReal.ofReal (L ^ 2 * ‖x₁ - x₂‖ ^ 2))

/-- Regularity of the jump-diffusion coefficients in the time and mark variables: joint
measurability, and square integrability in `s` at a single state.

`JumpDiffusionCoeffs.IsLipschitz` constrains `(μ, σ, γ)` only in the state variable, while the
`is_solution` field of `JumpDiffusion` needs joint measurability, progressive measurability and
`L²` bounds of the integrands along the path. Together with the Lipschitz clauses, the bounds
below give those `L²` bounds along any `L²`-bounded path, since Lipschitz continuity in the
state gives `‖f s x‖ ≤ ‖f s 0‖ + L ‖x‖`. -/
def JumpDiffusionCoeffs.IsRegular {n d : ℕ}
    (coeffs : JumpDiffusionCoeffs n d E) (ν : Measure E) : Prop :=
  Measurable (Function.uncurry coeffs.μ) ∧
  Measurable (Function.uncurry coeffs.σ) ∧
  Measurable (fun p : ℝ × (Fin n → ℝ) × E => coeffs.γ p.1 p.2.1 p.2.2) ∧
  (∀ T : ℝ, 0 < T →
    ∫⁻ s in Set.Icc (0 : ℝ) T, (‖coeffs.μ s 0‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) ∧
  (∀ T : ℝ, 0 < T →
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∑ i, ∑ j,
      (‖coeffs.σ s 0 i j‖₊ : ℝ≥0∞) ^ 2 ∂volume < ⊤) ∧
  (∀ T : ℝ, 0 < T →
    ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖coeffs.γ s 0 e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume < ⊤)

end Coefficients

section Solution
variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- A *jump diffusion* solution.

Fields:
* `X : ℝ → Ω → (Fin n → ℝ)` — the path map.
* `measurable_path` — joint measurability.
* `initial_value` — `X_0 = x_0` a.s.
* `sup_L2` — `𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞` for every `T > 0`.
* `is_solution` — the SDE integral equation: for every `t ≥ 0` and component
  `i`, almost surely (the exceptional set may depend on `t`),
  `X t ω i` equals `x₀ i` plus the drift integral `∫_0^t μ(s, X_s) ds`
  plus the multidim Brownian Itô integral `∫_0^t σ(s, X_s) · dW_s` (row `i`)
  plus the compensated-Poisson integral `∫_0^t ∫_E γ(s, X_s, e) Ñ(ds, de)` (row `i`).
  The Brownian integral requires existence of measurability /
  progressive-measurability / L²-bounds on `(s, ω) ↦ σ(s, X_s)`; these
  are bundled inside the existential. The constant-path witness
  `X t ω = x₀` fails this constraint for generic `(μ, σ, γ)` because
  the integrals don't vanish. -/
structure JumpDiffusion
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {n d : ℕ}
    (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (coeffs : JumpDiffusionCoeffs n d E)
    (x₀ : Fin n → ℝ) where
  /-- The path map. -/
  X : ℝ → Ω → (Fin n → ℝ)
  /-- The path map is jointly measurable in `(t, ω)`. -/
  measurable_path : Measurable (Function.uncurry X)
  /-- Almost-sure initial condition: `X_0 = x_0`. -/
  initial_value : ∀ᵐ ω ∂P, X 0 ω = x₀
  /-- Square-integrable supremum: `𝔼[sup_{t ≤ T} ‖X_t‖²] < ∞` for every `T`. -/
  sup_L2 : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, (⨆ t : Set.Icc (0 : ℝ) T,
      ∑ i, (‖X t.1 ω i‖₊ : ℝ≥0∞) ^ 2) ∂P < ⊤
  /-- Almost-sure càdlàg paths (right-continuous with left limits, a.s.)
  on the SDE time domain `t ≥ 0`.
  Required by the literature jump-diffusion SDE convention: Applebaum 6.2.9 /
  Ikeda-Watanabe IV assume X is càdlàg-adapted so that `X_{s−}` (the left
  limit at s) is well-defined for the integrand evaluation in the
  compensated-Poisson integral. Without this field, `X.X s` and `X_{s−}` are
  silently equal (no left-limit notion), and the SDE equation diverges from
  Applebaum at jump times.

  **Convention note (`X_{s−}` vs `X s`)**: Applebaum 6.2.9 / Ikeda-
  Watanabe IV use `X_{s−}` (the left limit) inside the SDE integrands,
  whereas this structure uses `X s` (point evaluation) below. Two
  separate statements are involved, and only the first is what makes
  the two conventions interchangeable here.

  *`L²`-class identification.* The compensated integral constructed in
  `Poisson/Compensated.lean` depends only on the `P ⊗ ds ⊗ ν`-class of
  its integrand: two admissible integrands equal almost everywhere for
  that measure have almost surely equal integrals
  (`Poisson.Compensated.stochasticIntegral_congr_ae`, from the
  difference isometry). A càdlàg path agrees with its left limits off a
  countable, hence `ds`-null, set
  (`Analysis.ae_eq_leftLim_of_cadlag`), so replacing `X s` by `X_{s−}`
  inside an integrand changes it only on a `P ⊗ ds ⊗ ν`-null set and
  therefore does not change the constructed integral. The same argument
  covers the Lebesgue-`ds` drift integral.

  *Pathwise interpretation.* Identifying that integral with a pathwise
  sum over the jumps of `N` is a different claim: it needs a predictable
  representative of the integrand and the compatibility theorem
  (`Poisson/PathwiseIdentity.lean`, which assumes `MarkedPredictable`;
  predictable modifications exist by
  `Probability.exists_markedPredictable_ae_eq`). Against a *pathwise*
  integral with respect to `N` the two conventions do **not** agree —
  for a counting process, `∫_0^t N_s dN_s − ∫_0^t N_{s−} dN_s = N_t` —
  so the interchangeability above is a statement about the `L²`
  construction, not about pathwise Stieltjes integration. The
  literature prefers `X_{s−}` because it is predictable; the structure's
  `cadlag_paths` field is what makes the left limits exist at all.

  **Quantifier scope**: the time argument is quantified over `t ≥ 0` only —
  the literature scope of the SDE is `[0, ∞)` (the initial condition
  `X 0 = x₀` and the integrals `∫₀^t … ds` only make sense for `t ≥ 0`). -/
  cadlag_paths : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    Filter.Tendsto (fun s => X s ω) (nhdsWithin t (Set.Ioi t)) (nhds (X t ω))
      ∧ ∀ i : Fin n, ∃ L : ℝ,
          Filter.Tendsto (fun s => X s ω i) (nhdsWithin t (Set.Iio t)) (nhds L)
  /-- The SDE integral equation, relative to a filtration `ℱ` for which every coordinate of
  `W` is a Brownian motion and `N` is a Poisson random measure. The filtration, those two
  properties and the per-row integrand hypotheses (joint measurability, progressive
  measurability for `ℱ`, `L²` bounds) are bundled in the existential alongside the equation,
  because the two stochastic integrals need them to be well-typed. Both coefficients are
  progressively measurable for the *same* filtration, so coupled `(σ, γ)` are in scope. -/
  is_solution :
    ∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
      (hℱW : ∀ j : Fin d, LevyStochCalc.Brownian.IsBrownianFiltration (W.W j) ℱ)
      (hℱN : LevyStochCalc.Poisson.IsPoissonFiltration N ℱ)
      (h_σ_meas : ∀ i : Fin n, ∀ j : Fin d,
        Measurable (Function.uncurry (fun ω s => coeffs.σ s (X s ω) i j)))
      (h_σ_progMeas : ∀ i : Fin n, ∀ j : Fin d,
          Probability.ProgressivelyMeasurable ℱ
            (fun ω s => coeffs.σ s (X s ω) i j))
      (h_σ_sq : ∀ i : Fin n, ∀ j : Fin d, ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T',
          (‖coeffs.σ s (X s ω) i j‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
      (h_γ_meas : ∀ i : Fin n,
        Measurable (fun (p : Ω × ℝ × E) =>
          (fun ω' s e => coeffs.γ s (X s ω') e i) p.1 p.2.1 p.2.2))
      (h_γ_progMeas : ∀ i : Fin n,
          Probability.MarkedProgressivelyMeasurable ℱ
            (fun ω' s e => coeffs.γ s (X s ω') e i))
      (h_γ_sq : ∀ i : Fin n, ∀ T' : ℝ, 0 < T' →
        ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T', ∫⁻ e,
          (‖coeffs.γ s (X s ω) e i‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤),
    ∀ t : ℝ, 0 ≤ t → ∀ᵐ ω ∂P, ∀ i : Fin n,
      X t ω i = x₀ i
        + (∫ s in Set.Icc (0 : ℝ) t, coeffs.μ s (X s ω) i)
        + LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion.stochasticIntegral
            W ℱ hℱW
            (fun s ω => coeffs.σ s (X s ω) i)
            (fun j => h_σ_meas i j)
            (fun j => h_σ_progMeas i j)
            (fun j => h_σ_sq i j) t ω
        + LevyStochCalc.Poisson.Compensated.stochasticIntegral N ℱ hℱN
            (fun ω' s e => coeffs.γ s (X s ω') e i)
            (h_γ_meas i) (h_γ_progMeas i) (h_γ_sq i) t ω

/-! **Theorem `JumpDiffusion.exists_unique` is stated in
`LevyStochCalc/Ito/PicardFixedPoint.lean`.**

The literature theorem (Applebaum 6.2.9 / Ikeda-Watanabe IV) is the
output of Picard iteration on the space `S²([0, T]; ℝⁿ)` equipped with
the Bielecki β-norm. The Picard map, its contraction estimate and the
limit of its iterates live in `Ito/Picard.lean`, `Ito/PicardLimit.lean`
and `Ito/PicardContraction.lean`; existence and uniqueness on a window in
`Ito/PicardWindow.lean`; the gluing of the windows in
`Ito/PicardGlobal.lean`; and `Ito/PicardWellPosed.lean` packages the
result as `Ito.Picard.exists_jumpDiffusion_unique_of_solvesOn`. The
theorem in `Ito/PicardFixedPoint.lean` forwards to it through
`picardFixedPoint_jumpDiffusion_exists_unique`. All of these files import
this one for the `JumpDiffusion` structure.

Placing the theorem there avoids an import cycle (Setting → Picard →
PicardFixedPoint → Setting would be a cycle). The qualified name remains
`LevyStochCalc.Ito.Setting.JumpDiffusion.exists_unique` (the theorem
re-opens the namespace explicitly in `PicardFixedPoint.lean`), which is
the name `tools/cited_axioms.md` (entry #12) and `_audit.lean` refer to. -/

end Solution

end LevyStochCalc.Ito.Setting
