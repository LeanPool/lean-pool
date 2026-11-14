/-
Copyright (c) 2026 Florian Lengyel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Florian Lengyel
-/
module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.Evaluator.TableLookup
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.EvaluationCongruence
public import LeanPool.PointwiseComposition.CategoricalRiceShapiro.ArithmeticCode.EncodedListEvaluation

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

/-!
# Evaluation of the table-lookup code

This module states two results with different assumptions and different content.

`eval_codeTableLookup_query_congr` assumes no more than `ORingStructure M`.  The
query argument of `codeTableLookup` occurs only inside the Cantor pair that
indexes the table, and every constructor between that occurrence and the whole
code has a valuation-local congruence law.  Composing those laws replaces the
query by an equivalent one.  That statement is local in every respect: one
assignment `v`, one changed argument, and an equivalence quantified only over
the possible query values.  The three remaining arguments are never evaluated
there, and it computes no value of the lookup.

`eval_codeTableLookup_exists_of_values` assumes `𝐏𝐀` and does produce a value:
from values for all four arguments it builds one for the whole lookup, through
the two encoded-list reads and the two subtractions of the option offset.  It
asserts existence only.  The value is not identified with a decoded table entry,
and no list semantics is attached to an arbitrary element of the model.
-/

@[expose] public section

open _root_.Nat Nat Nat.ArithPart₁

namespace CategoricalRiceShapiro
namespace Evaluator

open CategoricalRiceShapiro.ArithmeticCode

open Encodable FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic

open scoped FFL.FirstOrder.Arithmetic

/-- Replacing the query code by one with the same graph at `v` does not change
the graph of the lookup at `v`. -/
theorem eval_codeTableLookup_query_congr {M : Type*} [ORingStructure M] {r : ℕ}
    (dtable dk dq dq' dn : Code r) (z : M) (v : Fin r → M)
    (hquery :
      ∀ x : M, Semiformula.Evalb (x :> v) (code dq) ↔ Semiformula.Evalb (x :> v) (code dq')) :
    Semiformula.Evalb (z :> v) (code (codeTableLookup dtable dk dq dn)) ↔
      Semiformula.Evalb (z :> v) (code (codeTableLookup dtable dk dq' dn)) :=
  by
  have hpair :
    ∀ x : M,
      Semiformula.Evalb (x :> v) (code (codePair dk dq)) ↔
        Semiformula.Evalb (x :> v) (code (codePair dk dq')) :=
    fun x => eval_codePair_congr dk dk dq dq' x v (fun _ => Iff.rfl) hquery
  have hrow :
    ∀ x : M,
      Semiformula.Evalb (x :> v) (code (codeListGetOptional dtable (codePair dk dq))) ↔
        Semiformula.Evalb (x :> v) (code (codeListGetOptional dtable (codePair dk dq'))) :=
    fun x => eval_codeListGetOptional_congr dtable dtable _ _ x v (fun _ => Iff.rfl) hpair
  have hrow' :
    ∀ x : M,
      Semiformula.Evalb (x :> v)
          (code (codeSub (codeListGetOptional dtable (codePair dk dq)) (codeConst 1))) ↔
        Semiformula.Evalb (x :> v)
          (code (codeSub (codeListGetOptional dtable (codePair dk dq')) (codeConst 1))) :=
    fun x => eval_codeSub_congr _ _ _ _ x v hrow (fun _ => Iff.rfl)
  have hentry :
    ∀ x : M,
      Semiformula.Evalb (x :> v)
          (code
            (codeListGetOptional
              (codeSub (codeListGetOptional dtable (codePair dk dq)) (codeConst 1)) dn)) ↔
        Semiformula.Evalb (x :> v)
          (code
            (codeListGetOptional
              (codeSub (codeListGetOptional dtable (codePair dk dq')) (codeConst 1)) dn)) :=
    fun x => eval_codeListGetOptional_congr _ _ dn dn x v hrow' (fun _ => Iff.rfl)
  rw [codeTableLookup_eq, codeTableLookup_eq]
  exact eval_codeSub_congr _ _ _ _ z v hentry (fun _ => Iff.rfl)

/-- The table lookup has a value at any values of its four arguments.

The Cantor pair indexing the table is reached through the public cons
existence theorem: `codeListCons dk dq` is `codeSucc (codePair dk dq)`, so
eliminating `eval_codeSucc_iff` hands back an evaluation of the pair itself
without a separate pairing lemma.  The two encoded-list reads then supply the
optional row and the optional entry, and `eval_codeSub` removes each option
offset.  Only existence is asserted. -/
theorem eval_codeTableLookup_exists_of_values {M : Type*} [ORingStructure M] [M↓[ℒₒᵣ] ⊧* 𝐏𝐀]
    {r : ℕ} (dtable dk dq dn : Code r) (table key query index : M) (v : Fin r → M)
    (htable : Semiformula.Evalb (table :> v) (code dtable))
    (hkey : Semiformula.Evalb (key :> v) (code dk))
    (hquery : Semiformula.Evalb (query :> v) (code dq))
    (hindex : Semiformula.Evalb (index :> v) (code dn)) :
    ∃ z : M, Semiformula.Evalb (z :> v) (code (codeTableLookup dtable dk dq dn)) :=
  by
  let : M↓[ℒₒᵣ] ⊧* 𝐏𝐀⁻ := models_of_subtheory (show M↓[ℒₒᵣ] ⊧* 𝐏𝐀 from inferInstance)
  obtain ⟨c, hc⟩ := eval_codeListCons_exists_of_values dk dq key query v hkey hquery
  obtain ⟨p, hp, -⟩ := (eval_codeSucc_iff (codePair dk dq) c v).mp hc
  obtain ⟨row, hrow⟩ :=
    eval_codeListGetOptional_exists_of_values dtable (codePair dk dq) table p v htable hp
  have hone : Semiformula.Evalb ((1 : M) :> v) (code (codeConst (n := r) 1)) := by
    rw [eval_codeConst_iff]; simp
  obtain ⟨e, he⟩ :=
    eval_codeListGetOptional_exists_of_values _ dn (row - 1) index v
      (eval_codeSub _ _ row 1 v hrow hone) hindex
  refine ⟨e - 1, ?_⟩
  rw [codeTableLookup_eq]
  exact eval_codeSub _ _ e 1 v he hone

end Evaluator
end CategoricalRiceShapiro

end

end PointwiseComposition
