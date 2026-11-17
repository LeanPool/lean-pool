/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalBooleanGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanGeneric

/-!
# Internal Boolean Graph
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalBooleanGraph
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalRegularOrder InternalBooleanSyntax InternalBooleanProjection

def projectFormula (c A U V : ℕ) : Formula :=
  .conj (.subset V c) (.allMem c (.iff (.member 0 (V+1))
    (.allMem (A+1) (.imp (.subset (U+2) 0) (.member 1 0)))))

theorem projectFormula_spec (c A U V : ℕ) (e : ℕ → ZFSet.{0}) :
    (projectFormula c A U V).Eval e ↔ e V = project (e c) (e A) (e U) := by
  simp only [projectFormula,Formula.Eval,Formula.eval_subset,Formula.eval_allMem,
    Formula.eval_iff,Formula.eval_imp,cons_zero,cons_succ]
  have hs (p : ZFSet.{0}) : p ∈ project (e c) (e A) (e U) ↔
      p ∈ e c ∧ ∀ W ∈ e A, e U ⊆ W → p ∈ W := by
    simp only [project,infCode,uppers,ZFSet.mem_sep]
    exact and_congr_right (fun _ => ⟨fun h W hW hUW => h W ⟨hW,hUW⟩,
      fun h W hW => h W hW.1 hW.2⟩)
  constructor
  · rintro ⟨hVc,hV⟩
    exact ZFSet.ext (fun p => (Iff.intro
      (fun h => ⟨hVc h,(hV p (hVc h)).mp h⟩)
      (fun h => (hV p h.1).mpr h.2)).trans (hs p).symm)
  · intro h
    rw [h]
    exact ⟨fun _ hp => ((hs _).mp hp).1,fun p hp => (hs p).trans (and_iff_right hp)⟩

noncomputable def graph (c B A : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod B A).sep (fun z => ∃ U ∈ B, ∃ V ∈ A, z = ZFSet.pair U V ∧ V = project c A U)

theorem pair_graph (c B A U V : ZFSet.{0}) :
    ZFSet.pair U V ∈ graph c B A ↔ U ∈ B ∧ V ∈ A ∧ V = project c A U := by
  rw [graph,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,U',hU,V',hV,he,hp⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hU,hV,hp⟩
  · rintro ⟨hU,hV,hp⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨U,hU,V,hV,rfl⟩,U,hU,V,hV,rfl,hp⟩

theorem graph_mem (M c B A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hB : B ∈ M) (hA : A ∈ M) : graph c B A ∈ M := by
  let e := cons c (cons B (fun _ => A))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _ | _ | i
    · exact hc
    · exact hB
    · exact hA
  have hp := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hB hA
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 2 (.existsMem 4 (.conj (.orderedPair 2 1 0) (projectFormula 3 5 1 0)))) e he hp
  simpa only [graph,Formula.Eval,Formula.eval_orderedPair,projectFormula_spec,
    cons_zero,cons_succ,e] using hs

noncomputable def inclusionOrder (A : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod A A).sep (fun z => ∃ U ∈ A, ∃ V ∈ A, z = ZFSet.pair U V ∧ U ⊆ V)

theorem inclusionOrder_mem (M A : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) : inclusionOrder A ∈ M := by
  have hp := product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded
    hA hA
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.existsMem 2 (.conj (.orderedPair 2 1 0) (.subset 1 0))))
    (fun _ => A) (fun _ => hA) hp
  simpa only [inclusionOrder,Formula.Eval,Formula.eval_orderedPair,Formula.eval_subset,
    cons_zero,cons_succ] using hs

theorem pair_inclusionOrder (A U V : ZFSet.{0}) : ZFSet.pair U V ∈ inclusionOrder A ↔
    U ∈ A ∧ V ∈ A ∧ U ⊆ V := by
  rw [inclusionOrder,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,U',hU,V',hV,he,hp⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hU,hV,hp⟩
  · rintro ⟨hU,hV,hp⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨U,hU,V,hV,rfl⟩,U,hU,V,hV,rfl,hp⟩

end TuringRigidity.InternalBooleanGraph

end OAI
