/-
Copyright (c) 2026 Matteo Nerini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Nerini, Lean Pool contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Matrix.Block
public import Mathlib.Data.Matrix.PEquiv

/-!
# Common microwave network components and composition

Shared matrix definitions and finite-index facts used by both synthesis models. Adapted from
formalizing-analog-computing at commit a89c1e9263658c20a29046f9ed1a8eeb867dd537.
-/

public section

namespace MiLAC

/-- A matched network with `n` inputs and `n` outputs, represented by its transmission
scattering matrix. -/
abbrev Network (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- An interconnection, directly connecting an input to an output. -/
@[expose] def interconnection : Network 1 :=
  1

/-- A phase shifter with phase shift `φ`. -/
@[expose] noncomputable def phaseShifter (φ : ℝ) : Network 1 :=
  fun _ _ => Complex.exp (φ * Complex.I)

/-- A permutation network, reordering the signals according to `σ`. -/
@[expose] def permutationNetwork {n : ℕ} (σ : Equiv.Perm (Fin n)) : Network n :=
  σ.toPEquiv.toMatrix

/-- An interconnection is a phase shifter with zero phase. -/
lemma interconnection_eq_phaseShifter_zero :
    interconnection = phaseShifter 0 := by
  ext i j
  fin_cases i
  fin_cases j
  simp [interconnection, phaseShifter]

/-! ## Series and parallel composition -/

/-- The series of two networks, where `A` is followed by `B`. -/
@[expose] def series {n : ℕ} (A B : Network n) : Network n :=
  B * A

/-- The parallel of two networks. -/
@[expose] def parallel {n m : ℕ} (A : Network n) (B : Network m) : Network (n + m) :=
  Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 B)

/-- The first and second blocks of a parallel network have disjoint ports. -/
@[simp] lemma castAdd_ne_natAdd {n m : ℕ} (i : Fin n) (j : Fin m) :
    Fin.castAdd m i ≠ Fin.natAdd n j :=
  Fin.ne_of_val_ne (Nat.ne_of_lt (Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right n j.val)))

/-- Disjointness of parallel ports with the two blocks interchanged. -/
@[simp] lemma natAdd_ne_castAdd {n m : ℕ} (i : Fin m) (j : Fin n) :
    Fin.natAdd n i ≠ Fin.castAdd m j :=
  (castAdd_ne_natAdd j i).symm

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

/-- The diagonal matrix `diag(exp(j φ₁), …, exp(j φₙ))`. -/
@[expose] noncomputable def phaseDiagonal {n : ℕ}
    (φ : Fin n → ℝ) : Network n :=
  Matrix.diagonal (fun i => Complex.exp (φ i * Complex.I))

/-! ## Phase-only implementations -/

namespace PhaseShifters

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

end PhaseShifters

end MiLAC
