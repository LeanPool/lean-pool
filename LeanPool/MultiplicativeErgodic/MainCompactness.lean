/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Main
public import LeanPool.MultiplicativeErgodic.CompactnessIndex

/-!
# The main result with the compactness criterion

`mainres` states that the decomposition is nontrivial exactly when the cocycle is quasicompact,
`ν < λ₁`. With `nu_eq_compactnessIndex` the index `ν` is the index of compactness `κ`, so the
criterion becomes a comparison of two growth rates of the iterates: `‖𝓛^{(n)}_ω‖`, whose rate is
the top exponent `λ₁`, and `‖𝓛^{(n)}_ω‖_c`, whose rate is `κ`. Since `‖T‖_c ≤ ‖T‖` always,
`κ ≤ λ₁`, and the decomposition is nontrivial exactly when the two rates differ.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter TopologicalSpace

variable {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  [NormedAddCommGroup X] [NormedSpace ℝ X] [MeasurableSpace X]

/-- Quasicompactness is `κ < χ₁`, for the index of compactness `κ`. -/
theorem Cocycle.isQuasicompact_iff_compactnessIndex_lt (R : Cocycle Ω X) [SeparableSpace X]
    [BorelSpace X] (κ : EReal) (hκ : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal (compactSeminorm (R.iterate n ω)) / (n : EReal)) atTop (nhds κ)) :
    R.IsQuasicompact ↔ ∀ᵐ ω ∂(R.μ), κ < R.chi 1 ω := by
  have hν := nu_eq_compactnessIndex R κ hκ
  constructor
  · intro h
    filter_upwards [h, hν] with ω h1 h2
    rwa [h2] at h1
  · intro h
    filter_upwards [h, hν] with ω h1 h2
    rwa [← h2] at h1

/-- **Theorem \ref{mainres}, with the compactness criterion.** The whole of `mainres` —
existence, backward characterisation and uniqueness — with the quasicompactness clause restated,
both for the decomposition and for the competitors in the uniqueness clause: the decomposition
is nontrivial (`L ≥ 2`) exactly when the top Lyapunov exponent `λ₁ = lam 0` differs from the
index of compactness `κ = lim (1/n) log ‖𝓛^{(n)}_ω‖_c`. (Always `κ ≤ λ₁`.) -/
theorem mainres_compactnessIndex (R : Cocycle Ω X) [SeparableSpace X] [BorelSpace X]
    [CompleteSpace X] [Nontrivial X] (κ : EReal)
    (hκ : ∀ᵐ ω ∂(R.μ), Tendsto (fun n : ℕ =>
      logEReal (compactSeminorm (R.iterate n ω)) / (n : EReal)) atTop (nhds κ)) :
    ∃ (Lval : ℕ∞) (lam : ℕ → EReal) (mdim : ℕ → ℕ)
      (E : ∀ i : ℕ, Ω → GrassmannianFin X (mdim i + 1))
      (V : ℕ → Ω → Submodule ℝ X) (P : ℕ → Ω → X →L[ℝ] X),
      -- (1) existence
      (1 ≤ Lval ∧
       (∀ i : ℕ, (i : ℕ∞) < Lval → ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam i) ∧
       (∀ i : ℕ, ((i + 2 : ℕ) : ℕ∞) ≤ Lval ↔ ∀ᵐ ω ∂(R.μ), R.mult i ω ≠ 0) ∧
       ((2 : ℕ∞) ≤ Lval ↔ κ ≠ lam 0) ∧
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
         ((2 : ℕ∞) ≤ Lval' ↔ κ ≠ lam' 0) ∧
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
  obtain ⟨Lval, lam, mdim, E, V, P, ⟨hL1, hlam, hmult, hqc, hrest⟩, hback, huniq⟩ := mainres R
  -- `L ≥ 2` is `κ ≠ λ₁`, for any data whose first exponent is `λ₁`
  have hiff : ∀ l0 : EReal, (∀ᵐ ω ∂(R.μ), R.chi 1 ω = l0) → (R.IsQuasicompact ↔ κ ≠ l0) := by
    intro l0 hl0
    have hκle : κ ≤ l0 := by
      obtain ⟨ω, h1, h2⟩ := ((R.ae_le_chi_of_compactnessIndex hκ 1).and hl0).exists
      rwa [h2] at h1
    rw [R.isQuasicompact_iff_compactnessIndex_lt κ hκ]
    constructor
    · intro h
      obtain ⟨ω, h1, h2⟩ := (h.and hl0).exists
      rw [h2] at h1; exact ne_of_lt h1
    · intro h
      filter_upwards [hl0] with ω hω
      rw [hω]; exact lt_of_le_of_ne hκle h
  have hfirst : ∀ (Lval' : ℕ∞) (lam' : ℕ → EReal), 1 ≤ Lval' →
      (∀ i : ℕ, (i : ℕ∞) < Lval' → ∀ᵐ ω ∂(R.μ), R.lambda i ω = lam' i) →
      ∀ᵐ ω ∂(R.μ), R.chi 1 ω = lam' 0 := by
    intro Lval' lam' h1 hl
    have h0 : ((0 : ℕ) : ℕ∞) < Lval' := lt_of_lt_of_le (by norm_num) h1
    filter_upwards [hl 0 h0] with ω hω
    rw [← hω]; rfl
  refine ⟨Lval, lam, mdim, E, V, P,
    ⟨hL1, hlam, hmult, hqc.trans (hiff _ (hfirst Lval lam hL1 hlam)), hrest⟩, hback, ?_⟩
  rintro Lval' lam' mdim' E' V' P' ⟨h1', hlam', hmult', hqc', hrest'⟩
  exact huniq Lval' lam' mdim' E' V' P'
    ⟨h1', hlam', hmult', hqc'.trans (hiff _ (hfirst Lval' lam' h1' hlam')).symm, hrest'⟩

end MultiplicativeErgodic
