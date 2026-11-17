/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenAntichainSelector.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalRelationSelection
public import LeanPool.TuringConeRigidity.CohenForcing.CohenCountedAntichain

/-!
# Cohen Antichain Selector
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenAntichainSelector
open TransitiveNameModel BoundedSetTheory CohenAntichainStages CohenGroundPoset
open InternalRelationSelection

/-- An antichain inside `U` that is compatible with every condition in `U`. -/
def Selected (c U E : ZFSet.{0}) : Prop := E ⊆ U ∧ Anti c E ∧
  ∀ p ∈ U, ∃ q ∈ E, Comp c p q

/-- Bounded formula expressing the antichain selection property `Selected`. -/
def selectedFormula (c U E : ℕ) : Formula := .conj (.subset E U)
  (.conj (antiFormula c E)
    (.allMem U (.existsMem (E+1) (compFormula (c+2) 1 0))))

theorem selectedFormula_spec (c U E : ℕ) (e : ℕ → ZFSet.{0}) :
    (selectedFormula c U E).Eval e ↔ Selected (e c) (e U) (e E) := by
  simp only [selectedFormula,Selected,Formula.Eval,Formula.eval_subset,
    antiFormula_spec,Formula.eval_allMem,compFormula_spec,cons_zero,cons_succ]

/-- Set-coded relation between candidate sets and their selected predense antichains. -/
noncomputable def selectionRelation (c Q : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod Q Q).sep (fun z => ∃ U ∈ Q, ∃ E ∈ Q, z = ZFSet.pair U E ∧ Selected c U E)

theorem pair_selectionRelation (c Q U E : ZFSet.{0}) :
    ZFSet.pair U E ∈ selectionRelation c Q ↔ U ∈ Q ∧ E ∈ Q ∧ Selected c U E := by
  simp only [selectionRelation,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,U',hU,E',hE,hp,hsel⟩
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp hp
    exact ⟨hU,hE,hsel⟩
  · rintro ⟨hU,hE,hsel⟩
    exact ⟨ZFSet.mem_prod.mpr ⟨U,hU,E,hE,rfl⟩,U,hU,E,hE,rfl,hsel⟩

theorem selectionRelation_mem (M c Q : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (hQ : Q ∈ M) : selectionRelation c Q ∈ M := by
  let e := cons Q (fun _ => c)
  let φ : Formula := .existsMem 1 (.existsMem 2
    (.conj (.orderedPair 2 1 0) (selectedFormula 4 1 0)))
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact hQ
    · exact hc
  simpa only [selectionRelation,φ,Formula.Eval,Formula.eval_orderedPair,
    selectedFormula_spec,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded φ e he
      (product_mem M hM hT.pairing hT.union hT.powerSet hT.separation.finitePrefix.bounded hQ hQ)

theorem internal_antichain_selector (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) :
    ∃ Q ∈ M, (∀ U, U ∈ Q ↔ U ∈ M ∧ U ⊆ conditions A) ∧
      ∃ T ∈ M, FunctionGraph Q Q T ∧
        ∀ U ∈ Q, ∀ E, ZFSet.pair U E ∈ T → Selected (conditions A) U E := by
  have hc := conditions_mem M A hM hT hA
  obtain ⟨Q,hQM,hQ⟩ := internal_power M hM hT.powerSet hc
  have hr := selectionRelation_mem M (conditions A) Q hM hT hc hQM
  have htotal : ∀ U ∈ Q, ∃ E ∈ Q, ZFSet.pair U E ∈ selectionRelation (conditions A) Q := by
    intro U hU
    obtain ⟨hUM,hUc⟩ := (hQ U).mp hU
    obtain ⟨E,hEM,hEU,hanti,hpred⟩ :=
      CohenInternalAntichain.internal_predense_antichain M A U hM hT hA hUM hUc
    have hEQ := (hQ E).mpr ⟨hEM,fun _ h => hUc (hEU h)⟩
    exact ⟨E,hEQ,(pair_selectionRelation _ _ _ _).mpr ⟨hU,hEQ,hEU,hanti,hpred⟩⟩
  obtain ⟨T,hTM,hfun,hsub⟩ := select_relation M Q Q _ hM hT hQM hQM hr htotal
  exact ⟨Q,hQM,hQ,T,hTM,hfun,fun U _ E hUE => (pair_selectionRelation _ _ _ _).mp (hsub hUE) |>.2.2⟩

theorem internal_antichain_family (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (U : ℕ → ZFSet.{0})
    (hU : ∀ n, U n ∈ M ∧ U n ⊆ conditions A) (hB : orbitGraph U ∈ M) :
    ∃ E : ℕ → ZFSet.{0}, orbitGraph E ∈ M ∧
      ∀ n, E n ∈ M ∧ Selected (conditions A) (U n) (E n) ∧
        (E n = ∅ ∨ InternallyCountable M (E n)) := by
  obtain ⟨Q,hQM,hQ,T,hTM,hfun,hsel⟩ := internal_antichain_selector M A hM hT hA
  have hUQ : ∀ n, U n ∈ Q := fun n => (hQ _).mpr (hU n)
  obtain ⟨E,hE,hval⟩ := map_sequence M Q Q T hM hT hQM hQM hTM hfun U hUQ hB
  refine ⟨E,hE,fun n => ?_⟩
  have hEM := ((hQ _).mp (hval n).1).1
  have hs := hsel (U n) (hUQ n) (E n) (hval n).2
  exact ⟨hEM,hs,CohenCountedAntichain.every_internal_antichain_counted M A (E n) hM hT hA hEM
    (fun _ h => (hU n).2 (hs.1 h)) hs.2.1⟩

end TuringRigidity.CohenAntichainSelector

end OAI
