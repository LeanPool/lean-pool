/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Backward

/-!
# The main result

Theorem \ref{mainres} of `proof_met.tex`, the semi-invertible Oseledets decomposition, together
with two conclusions the paper does not state: the decomposition is unique, and the fast spaces
are characterised by the backward orbit alone. Every condition and conclusion is written out in
the statement. The three parts are proved separately: `mainres_existence`
(`ProofMet/Existence.lean`), `Cocycle.IsOseledets.backward_characterisation`
(`ProofMet/Backward.lean`) and `Cocycle.IsOseledets.unique` (`ProofMet/Uniqueness.lean`).
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter TopologicalSpace

variable {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]

/-- **Theorem \ref{mainres}: the semi-invertible Oseledets decomposition.** Indexing is from `0`:
`lam i` is the paper's `λ_{i+1}`, `E i` its fast space `E_{i+1}`, `mdim i + 1` its multiplicity
`m_{i+1}`, `Lval` the number `L` of distinct exponents, and `V (l + 1)`, `P (l + 1)` the slow space
`V_{l+2}` and the projection onto it.

1. *Existence.* There are exponents, dimensions, fast spaces, slow spaces and projections with the
   clauses of `mainres_existence`: the exponents are the distinct Lyapunov exponents, `L ≥ 2`
   exactly when `𝓛` is quasicompact, each fast space is measurable, equivariant and grows at
   exactly its exponent, and `X = E_0(ω) ⊕ ⋯ ⊕ E_l(ω) ⊕ V_{l+1}(ω)` with `V_{l+1}(ω) = {λ_ω ≤
   lam (l+1)}`
   and `P_{l+1}` a strongly measurable, tempered projection onto it along the fast spaces.
2. *Backward characterisation.* For `i + 2 ≤ L`, almost surely `E_0(ω) ⊕ ⋯ ⊕ E_i(ω)` is exactly the
   set of `x` with a backward history `x = y₀ ← y₁ ← ⋯`, `𝓛_{σ^{-(n+1)}ω} y_{n+1} = y_n`, decaying
   at rate `lam i`: `‖y_n‖ ≤ e^{-bn}` eventually for every real `b < lam i`.
3. *Uniqueness.* Any other data with all the clauses of (1) has the same `L`, the same exponents and
   dimensions, and almost surely the same fast spaces, slow spaces and projections, at every index
   the clauses constrain (`i + 2 ≤ L`). Nothing is asserted beyond `L`. -/
theorem mainres (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X] [CompleteSpace X]
    [Nontrivial X] :
    ∃ (Lval : ℕ∞) (lam : ℕ → EReal) (mdim : ℕ → ℕ)
      (E : ∀ i : ℕ, Ω → GrassmannianFin X (mdim i + 1))
      (V : ℕ → Ω → Submodule ℝ X) (P : ℕ → Ω → X →L[ℝ] X),
      -- (1) existence
      (1 ≤ Lval ∧
       (∀ i : ℕ, (i : ℕ∞) < Lval → ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam i) ∧
       (∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ Lval ↔ ∀ᵐ ω ∂(R.μ), R.mult i ω ≠ 0) ∧
       ((2 : ℕ∞) ≤ Lval ↔ R.IsQuasicompact) ∧
       -- measurability and temperedness
       (∀ i, Measurable (E i)) ∧
       (∀ i, ∀ x : X, Measurable fun ω => P i ω x) ∧
       (∀ i, R.IsTempered (P i)) ∧
       -- the fast spaces
       (∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ Lval → ∀ᵐ ω ∂(R.μ),
         R.mult i ω = mdim i + 1 ∧
         Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E i ω).1 : Submodule ℝ X)
           = ((E i (R.σ ω)).1 : Submodule ℝ X) ∧
         Tendsto (fun n : ℕ => logEReal
             ‖(R.iterate n ω).comp (((E i ω).1 : Submodule ℝ X)).subtypeL‖ / (n : EReal))
           atTop (nhds (lam i)) ∧
         Tendsto (fun n : ℕ => logEReal
             (growth (R.iterate n ω) ((E i ω).1 : Submodule ℝ X)) / (n : EReal))
           atTop (nhds (lam i))) ∧
       -- the decompositions
       (∀ l : ℕ, ((l + 2 : ℕ) : ℕ∞) ≤ Lval → ∀ᵐ ω ∂(R.μ),
         IsCompl (⨆ i ∈ Finset.range (l + 1), ((E i ω).1 : Submodule ℝ X)) (V (l + 1) ω) ∧
         Submodule.map (R.L ω : X →ₗ[ℝ] X) (V (l + 1) ω) ≤ V (l + 1) (R.σ ω) ∧
         (P (l + 1) ω).comp (P (l + 1) ω) = P (l + 1) ω ∧
         V (l + 1) ω = LinearMap.range ((P (l + 1) ω : X →ₗ[ℝ] X)) ∧
         (∀ x ∈ ⨆ i ∈ Finset.range (l + 1), ((E i ω).1 : Submodule ℝ X), P (l + 1) ω x = 0) ∧
         (V (l + 1) ω : Set X) = {x : X | R.lambdaAt ω x ≤ lam (l + 1)})) ∧
      -- (2) the fast spaces are characterised by the backward orbit
      (∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ Lval → ∀ᵐ ω ∂(R.μ),
        ((⨆ j ∈ Finset.range (i + 1), ((E j ω).1 : Submodule ℝ X) : Submodule ℝ X) : Set X) =
          {x : X | ∃ y : ℕ → X, y 0 = x ∧
            (∀ n : ℕ, R.L ((R.σ.symm : Ω → Ω)^[n + 1] ω) (y (n + 1)) = y n) ∧
            ∀ b : ℝ, (b : EReal) < lam i → ∀ᶠ n : ℕ in atTop, ‖y n‖ ≤ Real.exp (-b * n)}) ∧
      -- (3) uniqueness
      (∀ (Lval' : ℕ∞) (lam' : ℕ → EReal) (mdim' : ℕ → ℕ)
          (E' : ∀ i : ℕ, Ω → GrassmannianFin X (mdim' i + 1))
          (V' : ℕ → Ω → Submodule ℝ X) (P' : ℕ → Ω → X →L[ℝ] X),
        (1 ≤ Lval' ∧
         (∀ i : ℕ, (i : ℕ∞) < Lval' → ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam' i) ∧
         (∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ Lval' ↔ ∀ᵐ ω ∂(R.μ), R.mult i ω ≠ 0) ∧
         ((2 : ℕ∞) ≤ Lval' ↔ R.IsQuasicompact) ∧
         -- measurability and temperedness
         (∀ i, Measurable (E' i)) ∧
         (∀ i, ∀ x : X, Measurable fun ω => P' i ω x) ∧
         (∀ i, R.IsTempered (P' i)) ∧
         -- the fast spaces
         (∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ Lval' → ∀ᵐ ω ∂(R.μ),
           R.mult i ω = mdim' i + 1 ∧
           Submodule.map (R.L ω : X →ₗ[ℝ] X) ((E' i ω).1 : Submodule ℝ X)
             = ((E' i (R.σ ω)).1 : Submodule ℝ X) ∧
           Tendsto (fun n : ℕ => logEReal
               ‖(R.iterate n ω).comp (((E' i ω).1 : Submodule ℝ X)).subtypeL‖ / (n : EReal))
             atTop (nhds (lam' i)) ∧
           Tendsto (fun n : ℕ => logEReal
               (growth (R.iterate n ω) ((E' i ω).1 : Submodule ℝ X)) / (n : EReal))
             atTop (nhds (lam' i))) ∧
         -- the decompositions
         (∀ l : ℕ, ((l + 2 : ℕ) : ℕ∞) ≤ Lval' → ∀ᵐ ω ∂(R.μ),
           IsCompl (⨆ i ∈ Finset.range (l + 1), ((E' i ω).1 : Submodule ℝ X)) (V' (l + 1) ω) ∧
           Submodule.map (R.L ω : X →ₗ[ℝ] X) (V' (l + 1) ω) ≤ V' (l + 1) (R.σ ω) ∧
           (P' (l + 1) ω).comp (P' (l + 1) ω) = P' (l + 1) ω ∧
           V' (l + 1) ω = LinearMap.range ((P' (l + 1) ω : X →ₗ[ℝ] X)) ∧
           (∀ x ∈ ⨆ i ∈ Finset.range (l + 1), ((E' i ω).1 : Submodule ℝ X), P' (l + 1) ω x = 0) ∧
           (V' (l + 1) ω : Set X) = {x : X | R.lambdaAt ω x ≤ lam' (l + 1)})) →
        Lval = Lval' ∧ (∀ i : ℕ, (i : ℕ∞) < Lval → lam i = lam' i) ∧
        ∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ Lval → mdim i = mdim' i ∧ ∀ᵐ ω ∂(R.μ),
          ((E i ω).1 : Submodule ℝ X) = ((E' i ω).1 : Submodule ℝ X) ∧
          V (i + 1) ω = V' (i + 1) ω ∧ P (i + 1) ω = P' (i + 1) ω) := by
  obtain ⟨Lval, lam, mdim, E, V, P, h⟩ := mainres_existence R
  have hO : R.IsOseledets Lval lam mdim E V P := h
  refine ⟨Lval, lam, mdim, E, V, P, h, fun i hi => ?_,
    fun Lval' lam' mdim' E' V' P' h' => Cocycle.IsOseledets.unique R hO h'⟩
  filter_upwards [hO.backward_characterisation R i hi] with ω hω
  exact congrArg (fun S : Submodule ℝ X => (S : Set X)) hω

end MultiplicativeErgodic
