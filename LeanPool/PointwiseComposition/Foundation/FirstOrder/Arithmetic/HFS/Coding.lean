/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Arithmetic.HFS.Vec

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace FFL
namespace FirstOrder
namespace Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝐈Σ₁]

/-- The finset Arithmetize Aux construction in `FFL.FirstOrder.Arithmetic`. -/
noncomputable def finsetArithmetizeAux : List V → V
  | [] => ∅
  | x :: xs => insert x (finsetArithmetizeAux xs)

@[simp]
lemma finsetArithmetizeAux_nil : finsetArithmetizeAux ([] : List V) = ∅ :=
  rfl

@[simp]
lemma finsetArithmetizeAux_cons (x : V) (xs) :
    finsetArithmetizeAux (x :: xs) = insert x (finsetArithmetizeAux xs) :=
  rfl

@[simp]
lemma mem_finsetArithmetizeAux_iff {x : V} {s : List V} : x ∈ finsetArithmetizeAux s ↔ x ∈ s :=
  by induction s <;> simp [*]

/-- The arithmetize construction in `Finset`. -/
noncomputable def _root_.PointwiseComposition.Finset.arithmetize (s : Finset V) : V :=
  finsetArithmetizeAux s.toList

@[simp]
lemma mem_finsetArithmetize_iff {x : V} {s : Finset V} :
    x ∈ (PointwiseComposition.Finset.arithmetize s) ↔ x ∈ s := by simp [Finset.arithmetize]

@[simp]
lemma finset_empty_arithmetize : (PointwiseComposition.Finset.arithmetize (∅ : Finset V)) = ∅ :=
  by simp [Finset.arithmetize]

@[simp]
lemma finset_insert_arithmetize (a : V) (s : Finset V) :
    (PointwiseComposition.Finset.arithmetize (insert a s)) =
      insert a (PointwiseComposition.Finset.arithmetize s) :=
  mem_ext <| by intro x; simp

end Arithmetic
end FirstOrder
end FFL

end

end PointwiseComposition
