/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenGroundPoset.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenConditionCode
public import LeanPool.TuringConeRigidity.CohenForcing.CohenChainCondition

/-!
# Cohen Ground Poset
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenGroundPoset
open Set TransitiveNameModel BoundedSetTheory InternalFiniteSubsets CohenConditionCode
open CohenSymmetry CohenCoordinates CohenChainCondition
open InternalCohen (alphabet mem_alphabet)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Bounded formula asserting that a relation is single-valued on the given domain and
alphabet. -/
def singleValuedFormula (A B p : ℕ) : Formula :=
  .allMem A (.allMem (B+1) (.allMem (B+2)
    (.imp (.pairMem 2 1 (p+3)) (.imp (.pairMem 2 0 (p+3)) (.equal 1 0)))))

theorem singleValuedFormula_spec (A B p : ℕ) (e : ℕ → ZFSet.{0}) (hB : e B = alphabet) :
    (singleValuedFormula A B p).Eval e ↔ SingleValued (e A) (e p) := by
  simp only [singleValuedFormula,Formula.eval_allMem,Formula.eval_imp,
    Formula.eval_pairMem,Formula.Eval,cons_zero,cons_succ,hB,SingleValued]

/-- The set of finite Boolean-valued partial functions with coordinates in `A`. -/
noncomputable def conditions (A : ZFSet.{0}) : ZFSet.{0} :=
  (finiteSubsets (ZFSet.prod A alphabet)).sep (SingleValued A)

theorem mem_conditions (A p : ZFSet.{0}) : p ∈ conditions A ↔ IsCondition A p :=
  ZFSet.mem_sep

theorem conditions_mem (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) : conditions A ∈ M := by
  have hB := InternalCohen.alphabet_mem M hM hT
  have hP := product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hA hB
  let e := cons A (fun _ => alphabet)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact hA
    · exact hB
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (singleValuedFormula 1 2 0) e he (finiteSubsets_mem M _ hM hT hP)
  have heq : (finiteSubsets (ZFSet.prod A alphabet)).sep
      (fun p => (singleValuedFormula 1 2 0).Eval (cons p e)) = conditions A := by
    apply ZFSet.ext; intro p
    rw [ZFSet.mem_sep,mem_conditions]
    exact and_congr Iff.rfl (singleValuedFormula_spec 1 2 0 _ rfl)
  exact heq ▸ hs

/-- Encode a finitely supported condition as an element of the set-coded condition poset. -/
noncomputable def encode (A : ZFSet.{0}) (p : Condition (Conditions A)) : Conditions (conditions
  A) :=
  equivShrink (conditions A) ⟨graph A p,(mem_conditions A _).mpr (graph_isCondition A p)⟩

theorem label_encode (A : ZFSet.{0}) (p : Condition (Conditions A)) :
    label (conditions A) (encode A p) = graph A p := by simp [encode,label]

/-- Order isomorphism between finitely supported conditions and their set-coded graphs. -/
noncomputable def conditionEquiv (A : ZFSet.{0}) :
    Condition (Conditions A) ≃o Conditions (conditions A) :=
  { Equiv.ofBijective (encode A) ⟨by
      intro p q h
      have hlabel := congrArg (label (conditions A)) h
      exact graph_injective A (by simpa only [label_encode] using hlabel), by
      intro q
      obtain ⟨p,hp⟩ := (isCondition_iff_graph A _).mp ((mem_conditions A _).mp (label_mem _ q))
      exact ⟨p,label_injective _ (by rw [label_encode]; exact hp)⟩⟩ with
    map_rel_iff' := by
      intro p q
      change label _ (encode A q) ⊆ label _ (encode A p) ↔ _
      rw [label_encode,label_encode,graph_subset_iff] }

theorem poset_internal (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) :
    conditions A ∈ M ∧ InternalCollapse.orderSet (conditions A) ∈ M :=
  ⟨conditions_mem M A hM hT hA,
    InternalCollapse.orderSet_mem M hM hT (conditions_mem M A hM hT hA)⟩

theorem graph_mem_model (M A : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hA : A ∈ M) (p : Condition (Conditions A)) : graph A p ∈ M :=
  hM _ (conditions_mem M A hM hT hA) _ ((mem_conditions A _).mpr (graph_isCondition A p))

theorem antichain_countable (A : ZFSet.{0}) (E : Set (Conditions (conditions A)))
    (hE : E.Pairwise (fun p q => ¬ ∃ r, r ≤ p ∧ r ≤ q)) : E.Countable := by
  let e := conditionEquiv A
  have ha : Antichain (e ⁻¹' E) := by
    intro p hp q hq hpq hc
    apply hE hp hq (fun he => hpq (e.injective he))
    exact ⟨e (merge p q),e.monotone (merge_le_left p q),e.monotone (merge_le_right hc)⟩
  have hh := (CohenChainCondition.antichain_countable _ ha).image e
  have heq : e '' (e ⁻¹' E) = E := Set.image_preimage_eq _ e.surjective
  rwa [heq] at hh

/-- Equivalence between an indexed column coordinate and its set-coded ordered pair. -/
noncomputable def coordinateEquiv (K : ZFSet.{0}) :
    (Conditions K × ℕ) ≃ Conditions (ZFSet.prod K ZFSet.omega) :=
  Equiv.ofBijective (fun i => equivShrink (ZFSet.prod K ZFSet.omega)
    ⟨ZFSet.pair (label K i.1) (natSet i.2),
      ZFSet.mem_prod.mpr ⟨_,label_mem K i.1,_,(mem_omega _).mpr ⟨i.2,rfl⟩,rfl⟩⟩) ⟨by
    intro i j h
    have he := congrArg (label (ZFSet.prod K ZFSet.omega)) h
    simp only [label,Equiv.symm_apply_apply] at he
    obtain ⟨h1,h2⟩ := ZFSet.pair_inj.mp he
    exact Prod.ext (label_injective K h1) (natSet_injective h2),by
    intro q
    obtain ⟨x,hx,y,hy,h⟩ := ZFSet.mem_prod.mp (label_mem _ q)
    obtain ⟨n,rfl⟩ := (mem_omega y).mp hy
    refine ⟨(equivShrink K ⟨x,hx⟩,n),label_injective _ ?_⟩
    simpa [label] using h.symm⟩

/-- Order isomorphism coding many-column Cohen conditions as ground-model sets. -/
noncomputable def manyColumnEquiv (K : ZFSet.{0}) :
    Condition (Conditions K × ℕ) ≃o Conditions (conditions (ZFSet.prod K ZFSet.omega)) :=
  (reindex (coordinateEquiv K)).trans (conditionEquiv _)

theorem manyColumn_internal (M K : ZFSet.{0}) (hM : Transitive M)
    (hT : SourceT M) (hK : K ∈ M) :
    conditions (ZFSet.prod K ZFSet.omega) ∈ M ∧
    InternalCollapse.orderSet (conditions (ZFSet.prod K ZFSet.omega)) ∈ M :=
  poset_internal M _ hM hT (product_mem M hM hT.pairing hT.union hT.powerSet
    hT.separation.finitePrefix.bounded hK (sourceT_omega_mem M hM hT))

end TuringRigidity.CohenGroundPoset

end OAI
