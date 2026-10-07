/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import LeanPool.MicrowaveNetworks.Basic

/-!
# Computing with phase shifters

A network made of phase shifters, interconnected through interconnections and permutation
networks, and connected in series and in parallel, is represented by its transmission
scattering matrix (`Network n`).

## Main definitions

* `interconnection`, `phaseShifter`, `permutationNetwork`: the components.
* `series`, `parallel`: series and parallel connection of two networks.
* `Implementable`: the networks obtainable from the components by series and parallel
  connections.
* `phaseDiagonal`: the diagonal matrix `diag(exp(j φ₁), …, exp(j φₙ))`.
* `permutedPhaseDiagonal`: the product `P_σ diag(exp(j φ₁), …, exp(j φₙ))` of a permutation
  matrix and a diagonal matrix of phases.

## Main results

* `implementable_iff_permutedPhaseDiagonal`: a network is implementable if and only if its
  transmission scattering matrix is a permutation matrix times a diagonal matrix of phases.
-/

public section

namespace MiLAC.PhaseShifters

/-! ## Characterization of implementable networks -/

/-- The permuted diagonal matrix `P_σ diag(exp(j φ₁), …, exp(j φₙ))`. -/
@[expose] noncomputable def permutedPhaseDiagonal {n : ℕ}
    (φ : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) : Network n :=
  σ.toPEquiv.toMatrix *
    Matrix.diagonal (fun i => Complex.exp (φ i * Complex.I))

/-- An entry of a permuted phase diagonal has at most one nonzero value per row. -/
@[simp] lemma permutedPhaseDiagonal_apply {n : ℕ} (φ : Fin n → ℝ)
    (σ : Equiv.Perm (Fin n)) (i j : Fin n) :
    permutedPhaseDiagonal φ σ i j =
      if σ i = j then Complex.exp (φ (σ i) * Complex.I) else 0 := by
  unfold permutedPhaseDiagonal
  rw [PEquiv.toMatrix_toPEquiv_mul]
  rfl

/-! ### Sufficiency -/

/-- A permuted diagonal matrix of phases is implementable (sufficient condition). -/
theorem implementable_if_permutedPhaseDiagonal {n : ℕ}
    (φ : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    Implementable (permutedPhaseDiagonal φ σ) := by
  change Implementable (series (phaseDiagonal φ) (permutationNetwork σ))
  exact Implementable.series
    (implementable_if_phaseDiagonal φ)
    (Implementable.pn σ)

/-! ### Necessity -/

/-- The series of two permuted diagonal matrices is a permuted diagonal matrix. -/
lemma series_permutedPhaseDiagonal
    {n : ℕ} (φ ψ : Fin n → ℝ) (σ τ : Equiv.Perm (Fin n)) :
    ∃ χ : Fin n → ℝ, ∃ ρ : Equiv.Perm (Fin n),
      series (permutedPhaseDiagonal φ σ)
        (permutedPhaseDiagonal ψ τ) =
        permutedPhaseDiagonal χ ρ := by
  refine ⟨fun i => φ i + ψ (σ.symm i), τ.trans σ, ?_⟩
  ext i j
  simp only [series, Matrix.mul_apply, permutedPhaseDiagonal_apply]
  rw [Finset.sum_eq_single (τ i) (fun x _ hx => by simp [Ne.symm hx]) (by simp)]
  by_cases h : σ (τ i) = j
  · subst j
    simp [Equiv.trans_apply, ← Complex.exp_add, add_mul, add_comm]
  · simp [Equiv.trans_apply, h]

/-- The parallel of two permuted diagonal matrices is a permuted diagonal matrix. -/
lemma parallel_permutedPhaseDiagonal
    {n m : ℕ} (φ : Fin n → ℝ) (ψ : Fin m → ℝ)
    (σ : Equiv.Perm (Fin n)) (τ : Equiv.Perm (Fin m)) :
    ∃ χ : Fin (n + m) → ℝ, ∃ ρ : Equiv.Perm (Fin (n + m)),
      parallel (permutedPhaseDiagonal φ σ)
        (permutedPhaseDiagonal ψ τ) =
        permutedPhaseDiagonal χ ρ := by
  refine ⟨Sum.elim φ ψ ∘ finSumFinEquiv.symm,
    finSumFinEquiv.symm.trans ((Equiv.sumCongr σ τ).trans finSumFinEquiv), ?_⟩
  ext i j
  induction i using Fin.addCases <;> induction j using Fin.addCases <;>
    simp [parallel, Matrix.reindex_apply, permutedPhaseDiagonal_apply]

/-- An implementable network is a permuted diagonal matrix of phases (necessary condition). -/
theorem implementable_only_if_permutedPhaseDiagonal {n : ℕ}
    {S : Network n} (hS : Implementable S) :
    ∃ φ : Fin n → ℝ, ∃ σ : Equiv.Perm (Fin n), S = permutedPhaseDiagonal φ σ := by
  induction hS with
  | ps φ =>
    refine ⟨fun _ => φ, Equiv.refl _, ?_⟩
    ext i j
    fin_cases i
    fin_cases j
    simp [permutedPhaseDiagonal, phaseShifter]
  | ic =>
    refine ⟨fun _ => 0, Equiv.refl _, ?_⟩
    rw [interconnection_eq_phaseShifter_zero]
    ext i j
    fin_cases i
    fin_cases j
    simp [permutedPhaseDiagonal, phaseShifter]
  | pn σ =>
    refine ⟨fun _ => 0, σ, ?_⟩
    ext i j
    simp [permutedPhaseDiagonal, permutationNetwork]
  | series _ _ ihA ihB =>
    obtain ⟨φ, σ, rfl⟩ := ihA
    obtain ⟨ψ, τ, rfl⟩ := ihB
    exact series_permutedPhaseDiagonal φ ψ σ τ
  | parallel _ _ ihA ihB =>
    obtain ⟨φ, σ, rfl⟩ := ihA
    obtain ⟨ψ, τ, rfl⟩ := ihB
    exact parallel_permutedPhaseDiagonal φ ψ σ τ

/-! ### Main theorem -/

/-- A network is implementable if and only if it is a permuted diagonal matrix of phases. -/
theorem implementable_iff_permutedPhaseDiagonal {n : ℕ} {S : Network n} :
    Implementable S ↔
    ∃ φ : Fin n → ℝ, ∃ σ : Equiv.Perm (Fin n), S = permutedPhaseDiagonal φ σ := by
  constructor
  · exact implementable_only_if_permutedPhaseDiagonal
  · rintro ⟨φ, σ, rfl⟩
    exact implementable_if_permutedPhaseDiagonal φ σ

end MiLAC.PhaseShifters
