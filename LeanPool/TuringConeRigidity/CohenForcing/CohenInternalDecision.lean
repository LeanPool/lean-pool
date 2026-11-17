/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenInternalDecision.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenCountedAntichain

/-!
# Cohen Internal Decision
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenInternalDecision
open Set TransitiveNameModel BoundedSetTheory CohenAntichainStages CohenGroundPoset
open CohenCountedAntichain CohenConditionCode CohenSymmetry CohenCoordinates

noncomputable def below (c U : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun q => ∃ p ∈ U, p ⊆ q)

theorem below_mem (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) : below c U ∈ M := by
  let e := cons U (fun _ => c)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact hU
    · exact hc
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.subset 0 1)) e he hc
  simpa only [below,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ,e] using hs

noncomputable def decision (c U E : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun q => (∃ p ∈ E, p ⊆ q) ∨ ∀ p ∈ U, ¬ q ⊆ p)

theorem decision_mem (M c U E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) (hE : E ∈ M) : decision c U E ∈ M := by
  let e := cons U (fun _ => E)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact hU
    · exact hE
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.disj (.existsMem 2 (.subset 0 1)) (.allMem 1 (.neg (.subset 1 0)))) e he hc
  simpa only [decision,Formula.eval_disj,Formula.eval_allMem,Formula.Eval,
    Formula.eval_subset,cons_zero,cons_succ,e] using hs

theorem decision_dense (A U E : ZFSet.{0})
    (hpred : ∀ p ∈ below (conditions A) U, ∃ q ∈ E, Comp (conditions A) p q) :
    ∀ p ∈ conditions A, ∃ q ∈ decision (conditions A) (below (conditions A) U) E, p ⊆ q := by
  classical
  intro p hp
  by_cases h : ∃ r ∈ below (conditions A) U, p ⊆ r
  · obtain ⟨r,hr,hpr⟩ := h
    obtain ⟨a,ha,t,ht,hrt,hat⟩ := hpred r hr
    exact ⟨t,ZFSet.mem_sep.mpr ⟨ht,Or.inl ⟨a,ha,hat⟩⟩,fun z hz => hrt (hpr hz)⟩
  · exact ⟨p,ZFSet.mem_sep.mpr ⟨hp,Or.inr (fun r hr hpr => h ⟨r,hr,hpr⟩)⟩,fun _ h => h⟩

theorem internal_decision_data (M A U : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (hU : U ∈ M) :
    ∃ E ∈ M, E ⊆ below (conditions A) U ∧ Anti (conditions A) E ∧
      (E = ∅ ∨ InternallyCountable M E) ∧
      decision (conditions A) (below (conditions A) U) E ∈ M ∧
      ∀ p ∈ conditions A, ∃ q ∈ decision (conditions A) (below (conditions A) U) E, p ⊆ q := by
  have hc := conditions_mem M A hM hT hA
  have hb := below_mem M _ U hM hT hc hU
  obtain ⟨E,hEM,hEb,hEa,hpred,hct⟩ := internal_counted_antichain M A _ hM hT hA hb
    (fun _ h => (ZFSet.mem_sep.mp h).1)
  exact ⟨E,hEM,hEb,hEa,hct,decision_mem M _ _ E hM hT hc hb hEM,decision_dense A U E hpred⟩

theorem generic_decides (M A U E : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hA : A ∈ M) (hU : U ∈ M) (hE : E ∈ M)
    (hpred : ∀ p ∈ below (conditions A) U, ∃ q ∈ E, Comp (conditions A) p q)
    (G : CountableForcing.GenericFilter (Condition (Conditions A)))
    (hG : ∀ D : Set (Condition (Conditions A)), CohenGroundGeneric.codeSet A D ∈ M →
      CountableForcing.Dense D → ∃ p ∈ G.carrier, p ∈ D) :
    ∃ p ∈ G.carrier, (∃ a ∈ E, a ⊆ graph A p) ∨
      ∀ r ∈ below (conditions A) U, ¬ graph A p ⊆ r := by
  let D : Set (Condition (Conditions A)) :=
    {p | graph A p ∈ decision (conditions A) (below (conditions A) U) E}
  have heq : CohenGroundGeneric.codeSet A D = decision (conditions A) (below (conditions A) U) E
    := by
    apply ZFSet.ext; intro z
    constructor
    · intro hz
      obtain ⟨p,rfl⟩ := ZFSet.mem_range.mp hz
      exact p.property
    · intro hz
      obtain ⟨p,rfl⟩ := (isCondition_iff_graph A z).mp
        ((mem_conditions A z).mp (ZFSet.mem_sep.mp hz).1)
      exact (CohenGroundGeneric.graph_mem_codeSet A D p).mpr hz
  have hc := conditions_mem M A hM hT hA
  have hD : CohenGroundGeneric.codeSet A D ∈ M := heq ▸
    decision_mem M _ _ E hM hT hc (below_mem M _ U hM hT hc hU) hE
  have hdense : CountableForcing.Dense D := by
    intro p
    obtain ⟨q,hq,hpq⟩ := decision_dense A U E hpred (graph A p)
      ((mem_conditions A _).mpr (graph_isCondition A p))
    obtain ⟨q,rfl⟩ := (isCondition_iff_graph A q).mp
      ((mem_conditions A q).mp (ZFSet.mem_sep.mp hq).1)
    exact ⟨q,(graph_subset_iff A q p).mp hpq,hq⟩
  obtain ⟨p,hp,hpD⟩ := hG D hD hdense
  change graph A p ∈ decision (conditions A) (below (conditions A) U) E at hpD
  exact ⟨p,hp,(ZFSet.mem_sep.mp hpD).2⟩

end TuringRigidity.CohenInternalDecision

end OAI
