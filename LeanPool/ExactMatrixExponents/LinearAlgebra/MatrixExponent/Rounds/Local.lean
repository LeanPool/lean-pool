/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Packing.Frame

/-!
# The graph interface to local concentration

Each index in `Cell h` identifies an independent block. Host positions
name cells and each station belongs to one cell of one block. The input
has positive arities and integral packets of width `R`. The output
reserves individual host slots for the stations and is padded to units
of width `u` before the beats.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds
open Packing Finset

open scoped Classical in
/-- The data for the input construction, including `V`, `[fv`, `diagram`, `place`, `adj`. -/
structure Input (F : Type) (x y : Wire) (h D T R g : ℕ) (W : ℝ) where
  /-- The type of vertices. -/
  V : Type
  [fv : Fintype V]
  /-- The `Input` component of type `Diagram F x y`. -/
  diagram : Diagram F x y
  /-- The `Input` component of type `diagram.V → V × Cell h`. -/
  place : diagram.V → V × Cell h
  /-- The neighbors of each vertex of type `V → Finset V`. -/
  adj : V → Finset V
  sym : ∀ v z, z ∈ adj v → v ∈ adj z
  degree : ∀ v, (adj v).card ≤ g
  edge : ∀ e, let q := place (diagram.source e)
    let p := place (diagram.target e)
    p.2 = q.2 ∧ (p.1 = q.1 ∨ p.1 ∈ adj q.1)
  loopless : ∀ e, diagram.source e ≠ diagram.target e
  positive : ∀ v, 0 < diagram.arity v
  width : ∀ v w, R ∣ Fintype.card {e // diagram.source e = v ∧ diagram.target e = w}
  /-- The `Input` component of type `diagram.V → Prop`. -/
  mobile : diagram.V → Prop
  ext : ∀ q, ¬mobile (portEnd diagram q)
  occupied : (univ.image place).card * D * T ≤ W
  immobile : Fintype.card {v // ¬mobile v} * D * T ≤ W
  count : ∀ p, Fintype.card {v // place v = p} ≤ 100 * D
  mass : ∀ p, push place (fun v => (diagram.arity v : ℝ)) p ≤ 100 * (D : ℝ) * T
  squares : (∑ v, (diagram.arity v : ℝ) ^ 2) ≤ W * T
  /-- Optional local station and host keys for deterministic numbering. -/
  ranks : Option ((diagram.V → ℕ) × (V → ℕ)) := none

attribute [instance] Input.fv

open scoped Classical in
/-- The data for the local term construction, including `V`, `[fv`, `diagram`, `freeze`,
`frame`. -/
structure LocalTerm (F : Type) (x y : Wire) (h u : ℕ) where
  /-- The type of vertices. -/
  V : Type
  [fv : Fintype V]
  /-- The `LocalTerm` component of type `Diagram F x y`. -/
  diagram : Diagram F x y
  /-- The `LocalTerm` component of type `Freeze diagram`. -/
  freeze : Freeze diagram
  /-- The `LocalTerm` component of type `freeze.Frame V h`. -/
  frame : freeze.Frame V h
  one : Function.Injective frame.place
  width : ∀ v w, u ∣ Fintype.card {e // diagram.source e = v ∧ diagram.target e = w}
  /-- The `LocalTerm` component of type `diagram.V → ℝ`. -/
  charge : diagram.V → ℝ
  cover : ∀ v, diagram.arity v ≤ charge v
  floor : ∀ v, u ≤ charge v

attribute [instance] LocalTerm.fv

variable {F : Type} {x y : Wire} {h D T R g u : ℕ} {W : ℝ}

open scoped Classical in
/-- The graph and arity estimates needed from one summand. Here `D=2^d`
in applications. All implicit constants are bounded by `C`. -/
structure Concentrated (P : Input F x y h D T R g W) (Q : LocalTerm F x y h u)
    (C d ℓ : ℕ) : Prop where
  cells : Fintype.card Q.V ≤ D ^ C * Fintype.card P.V
  coreDegree : ∀ v, (Q.frame.C v).card ≤ C
  fullDegree : ∀ v, (Q.frame.N v).card ≤ D ^ C
  frozenCount : Fintype.card Q.freeze.Fixed * D * T ≤ C * W
  frozenMax : ∀ v : Q.freeze.Fixed, Q.charge v.val ≤ (C : ℝ) * D * T
  frozenSquare : (∑ v : Q.freeze.Fixed, Q.charge v.val ^ 2) ≤ C * W * T
  coreMax : ∀ v : Q.freeze.Core, Q.charge v.val * (D : ℝ) ^ ℓ ≤ T
  coreSum : (∑ v : Q.freeze.Core, Q.charge v.val) ≤ C * W * (1 + (d : ℝ)) ^ 2

open scoped Classical in
/-- The exact expansion and control-index count. Algorithmic locality
of the chosen terms is an additional requirement for realizing the sum. -/
def LocalExpansion [Field F] (P : Input F x y h D T R g W) (u C d ℓ A : ℕ) : Prop :=
  ∃ (I : Type) (_ : Fintype I) (Q : I → LocalTerm F x y h u) (c : I → F),
    Fintype.card I ≤ 2 ^ (A * (1 + Nat.clog 2 (T + 1)) * (univ.image P.place).card) ∧
    (∀ x y, ∑ i, c i * (Q i).diagram.eval x y = P.diagram.eval x y) ∧
    ∀ i, Concentrated P (Q i) C d ℓ

end MatrixMultiplicationAllFields.MatrixExponent.Rounds

namespace MatrixMultiplicationAllFields.MatrixExponent.Rounds
open Filter

/-- Uniform local concentration uses a fixed finite extension for
planting and polynomially many field points for the motions. -/
def LocalLaw (k : Type) [Field k] (ℓ : ℕ) : Prop :=
  ∀ g : ℕ, 0 < g → ∃ C : ℕ, ∀ᶠ d : ℕ in atTop,
    let D := 2 ^ d
    ∃ (A : ℕ) (L : Type) (_ : Field L) (_ : Finite L) (_ : Algebra k L),
      ∀ᶠ T : ℕ in atTop, ∃ R : ℕ, 0 < R ∧ R * D ^ 2 ≤ T ∧
        ∀ (K : Type) (_ : Field K) (_ : Fintype K) (_ : Algebra L K),
          A * (1 + T) ^ A ≤ Fintype.card K → ∀ u : ℕ, 0 < u → u * D ^ C ≤ T →
          ∀ (x y : Wire) (h : ℕ) (W : ℝ) (P : Input K x y h D T R g W), LocalExpansion P u C d ℓ A

end MatrixMultiplicationAllFields.MatrixExponent.Rounds
