/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Diagram.Permute
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Diagram.Wide

/-!
# Bit networks as finite directed multigraphs

Every argument slot belongs either to a named exterior position or to
one end of an internal edge. The two bijections specify this incidence
without requiring a topological order. In particular, loops are allowed.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent

/-- The data for the diagram construction, including `V`, `[fv`, `E`, `[fe`, `table`. -/
structure Diagram (F : Type) (a b : Wire) where
  /-- The type of vertices. -/
  V : Type
  [fv : Fintype V]
  /-- The type of edges. -/
  E : Type
  [fe : Fintype E]
  /-- The local table at each indexed position carried by `Diagram`, with type `V → Table F`. -/
  table : V → Table F
  /-- Names all input-side ports by either a boundary input or an internal edge. -/
  src : (Σ v, slots (table v).1) ≃ slots a ⊕ E
  /-- Names all output-side ports by either a boundary output or an internal edge. -/
  dst : (Σ v, slots (table v).2.1) ≃ slots b ⊕ E

attribute [instance] Diagram.fv Diagram.fe

namespace Diagram
variable {F : Type} {a b : Wire} (G : Diagram F a b)

/-- The quantity computed by `wd (G.table v).1 + wd (G.table v).2.1`. -/
def arity (v : G.V) : ℕ := wd (G.table v).1 + wd (G.table v).2.1
/-- The sum of `(1 + G.arity v)` indexed by `v`. -/
def cost : ℕ := ∑ v, (1 + G.arity v)

/-- The condition `∀ v, G.arity v ≤ 3` on the specified data. -/
def Trivalent : Prop := ∀ v, G.arity v ≤ 3
/-- The condition `∀ v, G.arity v ≤ u ∧ (G.arity v ≤ 3 ∨ G.table v ∈ L)` on the specified data. -/
def Admits (u : ℕ) (L : Set (Table F)) : Prop :=
  ∀ v, G.arity v ≤ u ∧ (G.arity v ≤ 3 ∨ G.table v ∈ L)

/-- The value specified by `(G.src.symm (.inr e)).1`. -/
def source (e : G.E) : G.V := (G.src.symm (.inr e)).1
/-- The value specified by `(G.dst.symm (.inr e)).1`. -/
def target (e : G.E) : G.V := (G.dst.symm (.inr e)).1

/-- Weight of one station before the internal edge bits are summed. -/
def vertex (x : Val a) (y : Val b) (z : G.E → Bool) (v : G.V) : F :=
  (G.table v).2.2
    ((bits (G.table v).1).symm (fun i => Sum.elim (bits a x) z (G.src ⟨v, i⟩)))
    ((bits (G.table v).2.1).symm (fun i => Sum.elim (bits b y) z (G.dst ⟨v, i⟩)))

/-- The eval of type `F` for the given inputs. -/
noncomputable def eval [Field F] (x : Val a) (y : Val b) : F := by
  classical
  exact ∑ z : G.E → Bool, ∏ v, G.vertex x y z v

end Diagram
end MatrixMultiplicationAllFields.MatrixExponent
