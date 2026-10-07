/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini
-/
module

public import LeanPool.MicrowaveNetworks.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv

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

/-! ## Components -/

/-- A matched network with `n` inputs and `n` outputs, represented by its transmission
scattering matrix. -/
abbrev Network (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- An interconnection, directly connecting an input to an output. -/
def interconnection : Network 1 :=
  1

/-- A phase shifter with phase shift `φ`. -/
noncomputable def phaseShifter (φ : ℝ) : Network 1 :=
  fun _ _ => Complex.exp (φ * Complex.I)

/-- A permutation network, reordering the signals according to `σ`. -/
def permutationNetwork {n : ℕ} (σ : Equiv.Perm (Fin n)) : Network n :=
  σ.toPEquiv.toMatrix

/-- An interconnection is a phase shifter with zero phase. -/
lemma interconnection_eq_phaseShifter_zero :
    interconnection = phaseShifter 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [interconnection, phaseShifter]

/-! ## Series, parallel, and implementable networks -/

/-- The series of two networks, where `A` is followed by `B`. -/
def series {n : ℕ} (A B : Network n) : Network n :=
  B * A

/-- The parallel of two networks. -/
def parallel {n m : ℕ} (A : Network n) (B : Network m) : Network (n + m) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

/-- The ports of the first and of the second network in a parallel are distinct. -/
lemma castAdd_ne_natAdd {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j :=
  MiLAC.castAdd_ne_natAdd i j

/-- The ports of the second and of the first network in a parallel are distinct. -/
lemma natAdd_ne_castAdd {n m : ℕ} (i : Fin m) (j : Fin n) :
    Fin.natAdd n i ≠ Fin.castAdd m j :=
  MiLAC.natAdd_ne_castAdd i j

/-- The upper-left block of a parallel is the first network. -/
@[simp] lemma parallel_castAdd_castAdd {n m : ℕ} (A : Network n) (B : Network m)
    (i j : Fin n) : parallel A B (Fin.castAdd m i) (Fin.castAdd m j) = A i j := by
  simp [parallel, Matrix.reindex_apply]

/-- The upper-right block of a parallel is zero. -/
@[simp] lemma parallel_castAdd_natAdd {n m : ℕ} (A : Network n) (B : Network m)
    (i : Fin n) (j : Fin m) : parallel A B (Fin.castAdd m i) (Fin.natAdd n j) = 0 := by
  simp [parallel, Matrix.reindex_apply]

/-- The lower-left block of a parallel is zero. -/
@[simp] lemma parallel_natAdd_castAdd {n m : ℕ} (A : Network n) (B : Network m)
    (i : Fin m) (j : Fin n) : parallel A B (Fin.natAdd n i) (Fin.castAdd m j) = 0 := by
  simp [parallel, Matrix.reindex_apply]

/-- The lower-right block of a parallel is the second network. -/
@[simp] lemma parallel_natAdd_natAdd {n m : ℕ} (A : Network n) (B : Network m)
    (i j : Fin m) : parallel A B (Fin.natAdd n i) (Fin.natAdd n j) = B i j := by
  simp [parallel, Matrix.reindex_apply]

/-- A network implementable with interconnections, phase shifters, and permutation networks. -/
inductive Implementable : {n : ℕ} → Network n → Prop where
  /-- An interconnection is implementable. -/
  | ic : Implementable interconnection
  /-- A phase shifter is implementable. -/
  | ps (φ : ℝ) : Implementable (phaseShifter φ)
  /-- A permutation network is implementable. -/
  | pn {n : ℕ} (σ : Equiv.Perm (Fin n)) : Implementable (permutationNetwork σ)
  /-- The series of two implementable networks is implementable. -/
  | series {n : ℕ} {A B : Network n} :
      Implementable A → Implementable B → Implementable (series A B)
  /-- The parallel of two implementable networks is implementable. -/
  | parallel {n m : ℕ} {A : Network n} {B : Network m} :
      Implementable A → Implementable B → Implementable (parallel A B)

/-! ## Characterization of implementable networks -/

/-- The diagonal matrix `diag(exp(j φ₁), …, exp(j φₙ))`. -/
noncomputable def phaseDiagonal {n : ℕ}
    (φ : Fin n → ℝ) : Network n :=
  Matrix.diagonal (fun i => Complex.exp (φ i * Complex.I))

/-- The permuted diagonal matrix `P_σ diag(exp(j φ₁), …, exp(j φₙ))`. -/
noncomputable def permutedPhaseDiagonal {n : ℕ}
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

/-- A diagonal matrix of phases is implementable. -/
lemma implementable_if_phaseDiagonal {n : ℕ} (φ : Fin n → ℝ) :
    Implementable (phaseDiagonal φ) := by
  induction n with
  | zero =>
      convert Implementable.pn (Equiv.refl (Fin 0)) using 1
      ext i
      exact Fin.elim0 i
  | succ n ih =>
      have hdecomp : phaseDiagonal φ =
          parallel (phaseDiagonal (fun i => φ (Fin.castAdd 1 i)))
            (phaseShifter (φ (Fin.natAdd n 0))) := by
        ext i j
        induction i using Fin.addCases <;> induction j using Fin.addCases <;>
          simp [phaseDiagonal, phaseShifter, Matrix.diagonal_apply, Fin.fin_one_eq_zero]
      rw [hdecomp]
      exact Implementable.parallel (ih _) (Implementable.ps _)

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
