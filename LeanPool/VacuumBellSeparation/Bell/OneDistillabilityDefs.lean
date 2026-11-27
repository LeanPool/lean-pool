/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Bell.BipartiteNormalStateDefs
public import LeanPool.VacuumBellSeparation.Bell.StateExtension
public import LeanPool.VacuumBellSeparation.FreeField.StrongContinuity
public import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap

/-!
Inactive definitions for Verch--Werner, quant-ph/0403089v3, Definitions 3.1
and 5.2. Distillability is defined by genuine CP maps and their positive
two-qubit output; an input negative witness alone is not its definition.
No result about CP construction, output positivity, or normalization is
assumed by these definitions.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Bipartite

open scoped ComplexOrder CStarAlgebra

/-- Qubit algebra defined as `CStarMatrix (Fin 2) (Fin 2) ℂ`. -/
abbrev QubitAlgebra := CStarMatrix (Fin 2) (Fin 2) ℂ
/-- The algebra of complex matrices on the tensor product of two qubit spaces. -/
abbrev TwoQubitAlgebra := CStarMatrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- The actual tensor matrix in the ordered product of the two standard bases. -/
def qubitTensor (X Y : QubitAlgebra) : TwoQubitAlgebra :=
  CStarMatrix.ofMatrix fun i j => X i.1 j.1 * Y i.2 j.2

/-- Transpose the first matrix factor, with no complex conjugation. -/
def partialTransposeLeft (Z : TwoQubitAlgebra) : TwoQubitAlgebra :=
  CStarMatrix.ofMatrix fun i j => Z (j.1, i.2) (i.1, j.2)

/-- Positivity of the partially transposed output functional, not of its input. -/
def TwoQubitPPT (τ : TwoQubitAlgebra →ₚ[ℂ] ℂ) : Prop :=
  ∀ Z : TwoQubitAlgebra, 0 ≤ Z → 0 ≤ τ (partialTransposeLeft Z)

/-- Two qubit trace given by `∑ i, Z i i`. -/
def twoQubitTrace (Z : TwoQubitAlgebra) : ℂ := ∑ i, Z i i

/-- A separate literal density-matrix certificate for a normalized output state. -/
def TwoQubitDensityRealizes (ρ : TwoQubitAlgebra →ₚ[ℂ] ℂ)
    (D : TwoQubitAlgebra) : Prop :=
  0 ≤ D ∧ twoQubitTrace D = 1 ∧ ∀ Z, ρ Z = twoQubitTrace (D * Z)

section GeneralCStarAlgebra

variable {R : Type*} [CStarAlgebra R] [PartialOrder R] [StarOrderedRing R]

/-- C⋆ bipartite commutes given by `∀ a : A, ∀ b : B, (a : R) * (b : R) = (b : R) * (a : R)`. -/
def CStarBipartiteCommutes (A B : StarSubalgebra ℂ R) : Prop :=
  ∀ a : A, ∀ b : B, (a : R) * (b : R) = (b : R) * (a : R)

variable (A B : StarSubalgebra ℂ R)
  [IsClosed (A : Set R)] [IsClosed (B : Set R)]

/-- A genuine positive output functional, specified on the tensor generators. -/
def CStarProductOutput (ω : R →ₚ[ℂ] ℂ)
    (T : QubitAlgebra →CP A) (S : QubitAlgebra →CP B)
    (τ : TwoQubitAlgebra →ₚ[ℂ] ℂ) : Prop :=
  ∀ X Y : QubitAlgebra, τ (qubitTensor X Y) = ω ((T X : R) * (S Y : R))

/-- VW05 Definition 5.2 for actual norm-closed C-star subalgebras.
The existence of the positive tensor-generator extension must be proved.
No subunitality or success-rate normalization is inserted into this definition. -/
def CStarOneDistillable (ω : R →ₚ[ℂ] ℂ) : Prop :=
  ω 1 = 1 ∧ CStarBipartiteCommutes A B ∧
    ∃ T : QubitAlgebra →CP A, ∃ S : QubitAlgebra →CP B,
      ∃ τ : TwoQubitAlgebra →ₚ[ℂ] ℂ,
        CStarProductOutput A B ω T S τ ∧ ¬ TwoQubitPPT τ

/-- The literal k=2 test of Definition 3.1, distinct from distillability. -/
def pptTwoTest (ω : R →ₚ[ℂ] ℂ) (a : Fin 2 → A) (b : Fin 2 → B) : ℂ :=
  ∑ i, ∑ j, ω (((a j : R) * star (a i : R)) *
    (star (b i : R) * (b j : R)))

end GeneralCStarAlgebra

section ConcreteVonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance vnaCarrierClosed (M : VonNeumannAlgebra H) :
    IsClosed (M.toStarSubalgebra : Set (H →L[ℂ] H)) :=
  isClosed_vonNeumannAlgebra M

/-- The actual product observable in the actual jointly generated algebra. -/
def jointProduct (A B : VonNeumannAlgebra H)
    (a : A.toStarSubalgebra) (b : B.toStarSubalgebra) :
    (jointAlgebra A B).toStarSubalgebra :=
  ⟨(a : H →L[ℂ] H) * (b : H →L[ℂ] H),
    (jointAlgebra A B).mul_mem
      (subset_generatedVNA _ (Set.mem_union_left _ a.property))
      (subset_generatedVNA _ (Set.mem_union_right _ b.property))⟩

/-- Joint product output. -/
def JointProductOutput (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ)
    (T : QubitAlgebra →CP A.toStarSubalgebra)
    (S : QubitAlgebra →CP B.toStarSubalgebra)
    (τ : TwoQubitAlgebra →ₚ[ℂ] ℂ) : Prop :=
  ∀ X Y : QubitAlgebra, τ (qubitTensor X Y) = f (jointProduct A B (T X) (S Y))

/-- VW05 one-copy distillability on the original joint VNA.
The state is not extended to an ambient operator algebra. -/
def IsOneDistillable (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ) : Prop :=
  IsStateFunctional (jointAlgebra A B) f ∧ Commuting A B ∧
    ∃ T : QubitAlgebra →CP A.toStarSubalgebra,
      ∃ S : QubitAlgebra →CP B.toStarSubalgebra,
        ∃ τ : TwoQubitAlgebra →ₚ[ℂ] ℂ,
          JointProductOutput A B f T S τ ∧ ¬ TwoQubitPPT τ

/-- A stronger operational certificate: selective CP maps, positive success
probability and their actual normalized NPT output. It is a proof obligation
that every witness to Definition 5.2 can be rescaled into this form. -/
def HasSelectiveOneDistillation (A B : VonNeumannAlgebra H)
    (f : (jointAlgebra A B).toStarSubalgebra → ℂ) : Prop :=
  IsStateFunctional (jointAlgebra A B) f ∧ Commuting A B ∧
    ∃ T : QubitAlgebra →CP A.toStarSubalgebra,
      ∃ S : QubitAlgebra →CP B.toStarSubalgebra,
        ∃ τ ρ : TwoQubitAlgebra →ₚ[ℂ] ℂ, ∃ p : ℝ,
          T 1 ≤ 1 ∧ S 1 ≤ 1 ∧ JointProductOutput A B f T S τ ∧
          τ 1 = (p : ℂ) ∧ 0 < p ∧ p ≤ 1 ∧ ρ 1 = 1 ∧
          (∀ Z, ρ Z = (p : ℂ)⁻¹ * τ Z) ∧ ¬ TwoQubitPPT ρ

end ConcreteVonNeumannAlgebra
end VacuumBellSeparation.Bipartite
