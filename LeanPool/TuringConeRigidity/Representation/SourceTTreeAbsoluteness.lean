/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/SourceTTreeAbsoluteness.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Computability.ArithmeticTreeDescent
public import LeanPool.TuringConeRigidity.SetModels.InternalNaturalRelationReal

/-!
# Source TTree Absoluteness
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.ArithmeticTree
open UniformArithmetic ArithmeticPersistence BoundedSetTheory TransitiveNameModel
open SetModelFunctions SetModelReals SetModelSyntax RelationCollapse
universe u
noncomputable section
attribute [local instance] Classical.propDecidable

theorem sourceContext (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M) : Context M :=
  ⟨hM,hT.pairing,hT.union,hT.powerSet,hT.separation.finitePrefix.bounded,hT.infinity⟩

theorem modelReals_eq (M : ZFSet.{u}) : modelReals M = reals M := rfl

private theorem zero_real_mem {M : ZFSet.{u}} (C : Context M) : (fun _ => false) ∈ reals M := by
  have he : realSet.{u} (fun _ => false) = ∅ := by
    apply ZFSet.ext
    intro x
    simp [realSet]
  change realSet _ ∈ M
  rw [he]
  exact C.nat_mem 0

private theorem relationSet_on (B : Oracle) : On ZFSet.omega.{u} (relationSet B) :=
  fun _ hz => (ZFSet.mem_sep.mp hz).1

theorem Test.illFounded_edges (t : Test) (O : Oracles) (v : ℕ)
    (r : ZFSet.{u}) (hr : ∀ n m, ZFSet.pair (natSet n) (natSet m) ∈ r ↔ t.edgePredicate O v n m)
    (hw : ∃ f : ℕ → ℕ, ∀ n, t.eval O f (Nat.pair v n)) :
    ¬ WellFounded (Rel ZFSet.omega r) := by
  rintro hf
  obtain ⟨f,hf'⟩ := hw
  let nodes : ℕ → ZFSet.{u} := fun n => natSet (Encodable.encode (initialSegment f n))
  have hc : ∀ n, Rel ZFSet.omega r (nodes (n+1)) (nodes n) := by
    intro n
    refine ⟨(mem_omega _).mpr ⟨_,rfl⟩,(hr _ _).mpr ?_⟩
    refine ⟨⟨by simp,?_⟩,⟨by simp,?_⟩,f n,?_⟩
    · simpa only [decodeNode_encode] using
        (show t.accepts O v (initialSegment f (n+1)) from (t.branch_iff O v f).mpr hf' (n+1))
    · simpa only [decodeNode_encode] using
        (show t.accepts O v (initialSegment f n) from (t.branch_iff O v f).mpr hf' n)
    · simp only [decodeNode_encode,prefix_succ]
  exact (wellFounded_iff_isEmpty_descending_chain.mp hf).false ⟨nodes,hc⟩

theorem sourceT_merge_witness (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    (t : Test) (A R : Oracle) (hA : A ∈ reals M) (hR : R ∈ reals M) (v : ℕ)
    (hw : ∃ H : Oracle, ∃ f : ℕ → ℕ, ∀ n, t.eval (parameters A R H) f (Nat.pair v n)) :
    ∃ H ∈ reals M, ∃ f : ℕ → ℕ, ∀ n, t.eval (parameters A R H) f (Nat.pair v n) := by
  let C := sourceContext M hM hT
  let O := parameters A R (fun _ => false)
  have hO : ∀ i, O i ∈ reals M := by
    intro i
    rcases i with _|_|i
    · exact hA
    · exact hR
    · exact zero_real_mem C
  let B : Oracle := fun n => decide (t.mergeReal.edgePredicate O v (left n) (right n))
  have hB : B ∈ reals M := arithmetic_comprehension C (t.mergeReal.edge_arith v) O hO B
    (fun n => by simp [B])
  let r := relationSet.{u} B
  have hr : ∀ n m, ZFSet.pair (natSet n) (natSet m) ∈ r ↔ t.mergeReal.edgePredicate O v n m := by
    intro n m
    simp [r,relationSet_pair,B,left,right]
  have hwf : ¬ WellFounded (Rel ZFSet.omega r) :=
    t.mergeReal.illFounded_edges O v r hr ((t.exists_mergeReal A R v).mp hw)
  obtain ⟨c,G,hG,hGc,hc⟩ := sourceT_natural_descent_real M hM hT
    (relationSet_mem C hB) (relationSet_on B) hwf
  have hGcM : G ∈ reals M := by simpa only [modelReals_eq] using hG
  have he : ∀ n, t.mergeReal.edgePredicate O v (c (n+1)) (c n) := fun n => (hr _ _).mp (hc n)
  refine ⟨Test.realPart (unionRead c),union_real_mem C G hGcM c hGc,Test.witnessPart (unionRead
    c),?_⟩
  intro n
  exact (t.mergeReal_eval A R (unionRead c) (Nat.pair v n)).mp (t.mergeReal.eval_of_descent O v c
    he n)

theorem sourceT_piOneOne_matrix (M : ZFSet.{u}) (hM : Transitive M) (hT : SourceT M)
    {Q : Predicate} (hQ : Arith Q) (A R : Oracle) (hA : A ∈ reals M) (hR : R ∈ reals M) (v : ℕ) :
    (∀ H ∈ reals M, Q (parameters A R H) v) ↔ ∀ H : Oracle, Q (parameters A R H) v := by
  constructor
  · intro h H
    by_contra hnot
    obtain ⟨t,ht⟩ := (arithmetic_tests hQ).2
    obtain ⟨f,hf⟩ := (ht (parameters A R H) v).mp hnot
    obtain ⟨K,hKM,g,hg⟩ := sourceT_merge_witness M hM hT t A R hA hR v ⟨H,f,hf⟩
    exact ((ht (parameters A R K) v).mpr ⟨g,hg⟩) (h K hKM)
  · exact fun h H _ => h H

end
end TuringRigidity.ArithmeticTree

end OAI
