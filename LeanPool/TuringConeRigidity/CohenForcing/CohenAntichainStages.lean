/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenAntichainStages.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenSizeLevels
public import LeanPool.TuringConeRigidity.CohenForcing.CohenFiniteAntichains
public import LeanPool.TuringConeRigidity.CohenForcing.CohenGroundGeneric

/-!
# Cohen Antichain Stages
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenAntichainStages
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets
open CohenSymmetry CohenCoordinates CohenConditionCode CohenGroundPoset
open CohenGroundGeneric CohenChainCondition CohenNiceNames

def Comp (c p q : ZFSet.{0}) : Prop := ∃ r ∈ c, p ⊆ r ∧ q ⊆ r

def compFormula (c p q : ℕ) : Formula :=
  .existsMem c (.conj (.subset (p+1) 0) (.subset (q+1) 0))

theorem compFormula_spec (c p q : ℕ) (e : ℕ → ZFSet.{0}) :
    (compFormula c p q).Eval e ↔ Comp (e c) (e p) (e q) := by
  simp only [compFormula,Comp,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ]

theorem comp_graph (A : ZFSet.{0}) (p q : Condition (Conditions A)) :
    Comp (conditions A) (graph A p) (graph A q) ↔ Compatible p q := by
  constructor
  · rintro ⟨r,hr,hpr,hqr⟩
    obtain ⟨r,rfl⟩ := (isCondition_iff_graph A r).mp ((mem_conditions A r).mp hr)
    have hrp := (graph_subset_iff A r p).mp hpr
    have hrq := (graph_subset_iff A r q).mp hqr
    intro i a b ha hb
    exact Option.some.inj ((hrp i a ha).symm.trans (hrq i b hb))
  · intro h
    exact ⟨graph A (merge p q),(mem_conditions A _).mpr (graph_isCondition A _),
      (graph_subset_iff A _ p).mpr (merge_le_left p q),
      (graph_subset_iff A _ q).mpr (merge_le_right h)⟩

def Anti (c E : ZFSet.{0}) : Prop :=
  ∀ p ∈ E, ∀ q ∈ E, p ≠ q → ¬ Comp c p q

def antiFormula (c E : ℕ) : Formula := .allMem E (.allMem (E+1)
  (.imp (.neg (.equal 1 0)) (.neg (compFormula (c+2) 1 0))))

theorem antiFormula_spec (c E : ℕ) (e : ℕ → ZFSet.{0}) :
    (antiFormula c E).Eval e ↔ Anti (e c) (e E) := by
  simp only [antiFormula,Anti,Formula.eval_allMem,Formula.eval_imp,
    Formula.Eval,compFormula_spec,cons_zero,cons_succ]

noncomputable def stages (c U : ZFSet.{0}) : ZFSet.{0} :=
  (finiteSubsets U).sep (Anti c)

theorem mem_stages (c U E : ZFSet.{0}) :
    E ∈ stages c U ↔ (E ⊆ U ∧ (E : Set ZFSet.{0}).Finite) ∧ Anti c E := by
  rw [stages,ZFSet.mem_sep,mem_finiteSubsets_iff]

theorem stages_mem (M c U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hU : U ∈ M) : stages c U ∈ M := by
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded (antiFormula 1 0)
    (fun _ => c) (fun _ => hc) (finiteSubsets_mem M U hM hT hU)
  simpa only [antiFormula_spec,cons_zero,cons_succ,stages] using hs

theorem empty_stage (c U : ZFSet.{0}) : (∅ : ZFSet.{0}) ∈ stages c U := by
  apply (mem_stages c U ∅).mpr
  exact ⟨⟨fun _ h => False.elim (ZFSet.notMem_empty _ h),by simp⟩,
    fun _ h => False.elim (ZFSet.notMem_empty _ h)⟩

theorem extend_stage (A U E : ZFSet.{0}) (hU : U ⊆ conditions A)
    (hE : E ∈ stages (conditions A) U) (n : ℕ) :
    ∃ F ∈ stages (conditions A) U, E ⊆ F ∧
      ∀ p ∈ U, CohenSizeLevels.Small n p → ∃ q ∈ F, Comp (conditions A) p q := by
  classical
  obtain ⟨⟨hEU,hEfin⟩,hEa⟩ := (mem_stages _ _ _).mp hE
  let U' : Set (Condition (Conditions A)) := {p | graph A p ∈ U}
  let E' : Set (Condition (Conditions A)) := {p | graph A p ∈ E}
  let V' : Set (Condition (Conditions A)) := {p ∈ U' | CohenSizeLevels.Small n (graph A p)}
  have hE' : Antichain E' := by
    intro p hp q hq hne hc
    exact hEa _ hp _ hq (fun he => hne (graph_injective A he)) ((comp_graph A p q).mpr hc)
  have hE'f : E'.Finite := hEfin.preimage (graph_injective A).injOn
  obtain ⟨F,hFfin,hEF,hFU,hFa,hpred⟩ := CohenFiniteAntichains.finite_extension
    U' V' E' (fun _ h => h.1) (fun p h => show graph A p ∈ U from hEU h) hE' hE'f n
      (fun p hp => Nat.le_of_lt (CohenSizeLevels.small_graph_bound A p n hp.2))
  have hcode : codeSet A F ∈ stages (conditions A) U := by
    apply (mem_stages _ _ _).mpr
    refine ⟨⟨?_,?_⟩,?_⟩
    · intro z hz
      obtain ⟨p,rfl⟩ := ZFSet.mem_range.mp hz
      exact hFU p.property
    · let : Fintype F := hFfin.fintype
      rw [codeSet,ZFSet.coe_range]
      exact Set.finite_range _
    · intro p hp q hq hpq hc
      obtain ⟨p,rfl⟩ := ZFSet.mem_range.mp hp
      obtain ⟨q,rfl⟩ := ZFSet.mem_range.mp hq
      exact hFa p.property q.property (fun he => hpq (congrArg (graph A) he))
        ((comp_graph A p.val q.val).mp hc)
  refine ⟨codeSet A F,hcode,?_,?_⟩
  · intro p hp
    obtain ⟨p,rfl⟩ := (isCondition_iff_graph A p).mp ((mem_conditions A p).mp (hU (hEU hp)))
    exact (graph_mem_codeSet A F p).mpr (hEF hp)
  · intro p hp hsmall
    obtain ⟨p,rfl⟩ := (isCondition_iff_graph A p).mp ((mem_conditions A p).mp (hU hp))
    obtain ⟨q,hq,hpq⟩ := hpred p ⟨hp,hsmall⟩
    exact ⟨graph A q,(graph_mem_codeSet A F q).mpr hq,(comp_graph A p q).mpr hpq⟩

end TuringRigidity.CohenAntichainStages

end OAI
