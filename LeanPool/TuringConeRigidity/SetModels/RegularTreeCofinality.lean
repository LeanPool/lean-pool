/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RegularTreeCofinality.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RegularTreeFilter

/-!
# Regular Tree Cofinality
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RegularTreeCofinality
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense RegularTreeFilter
open InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

noncomputable def nodesBelow (B A U : ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun V => ∃ w ∈ conditions, ZFSet.pair w V ∈ A ∧ V ⊆ U)

theorem nodesBelow_mem (M B A U : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hB : B ∈ M) (hA : A ∈ M) (hU : U ∈ M) : nodesBelow B A U ∈ M := by
  let e := cons conditions (cons A (fun _ => U))
  have he : ∀ i, e i ∈ M := by
    intro i; rcases i with _|_|i
    · exact conditions_mem M hM hT
    · exact hA
    · exact hU
  simpa only [nodesBelow,Formula.Eval,Formula.eval_pairMem,Formula.eval_subset,
    cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.pairMem 0 1 3) (.subset 1 4))) e he hB

theorem nodesBelow_decision_dense (c B A U : ZFSet.{0}) (f : List Bool → ZFSet.{0})
    (hf : ∀ s, f s ∈ B ∧ IsCode c (f s) ∧ f s ≠ ∅)
    (hAs : ∀ s V, ZFSet.pair (wordCode s) V ∈ A ↔ V = f s)
    (hden : ∀ V, IsCode c V → V ≠ ∅ → ∃ s, f s ⊆ V)
    (hU : IsCode c U) :
    Dense {p : Conditions c | label c p ∈ ZFSet.sUnion (nodesBelow B A U) ∪ neg c U} := by
  intro p
  obtain ⟨q,hqp,hq⟩ := decision_dense c U hU.1 p
  rcases ZFSet.mem_union.mp hq with hqU|hqN
  · have hb := mem_basicCode c _ (label_mem c q)
    have hb0 : basicCode c (label c q) ≠ ∅ := fun he => ZFSet.notMem_empty _ (he ▸ hb)
    obtain ⟨s,hs⟩ := hden _ (regular_isCode c _) hb0
    obtain ⟨r,hr,hqr⟩ := refines_condition c _ _ (hf s).2.1 (hf s).2.2 hs
    obtain ⟨r,rfl⟩ := label_surjective c ((hf s).2.1.1 hr)
    have hsU : f s ⊆ U := fun _ h =>
      (basicCode_le_iff c _ U (label_mem c q) hU).mpr hqU (hs h)
    exact ⟨r,le_trans hqr hqp,ZFSet.mem_union.mpr (Or.inl (ZFSet.mem_sUnion.mpr
      ⟨f s,ZFSet.mem_sep.mpr ⟨(hf s).1,wordCode s,
        (mem_conditions _).mpr ⟨_,wordCode_function s⟩,(hAs _ _).mpr rfl,hsU⟩,hr⟩))⟩
  · exact ⟨q,hqp,ZFSet.mem_union.mpr (Or.inr hqN)⟩

theorem hit_iff_node (M c B A U : ZFSet.{0}) (f : List Bool → ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hB : B ∈ M) (hA : A ∈ M)
    (hU : U ∈ M) (hUc : IsCode c U)
    (hf : ∀ s, f s ∈ B ∧ IsCode c (f s) ∧ f s ≠ ∅)
    (hAs : ∀ s V, ZFSet.pair (wordCode s) V ∈ A ↔ V = f s)
    (hden : ∀ V, IsCode c V → V ≠ ∅ → ∃ s, f s ⊆ V)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    Hit G U ↔ ∃ s, Hit G (f s) ∧ f s ⊆ U := by
  constructor
  · intro hGU
    have hFM := nodesBelow_mem M B A U hM hT hB hA hU
    obtain ⟨p,hp,hpD⟩ := hG (ZFSet.sUnion (nodesBelow B A U) ∪ neg c U)
      (binary_union_mem M hM hT.pairing hT.union (union_mem M hM hT.union hFM)
        (neg_mem M c U hM hT hc hU))
      (nodesBelow_decision_dense c B A U f hf hAs hden hUc)
    rcases ZFSet.mem_union.mp hpD with hpF|hpN
    · obtain ⟨V,hVF,hpV⟩ := ZFSet.mem_sUnion.mp hpF
      obtain ⟨_,w,hw,hwV,hVU⟩ := ZFSet.mem_sep.mp hVF
      obtain ⟨s,hs⟩ := (prefix_iff_wordCode w).mp ((mem_conditions w).mp hw)
      have hV : V = f s := (hAs s V).mp (hs.symm ▸ hwV)
      exact ⟨s,⟨p,hp,hV ▸ hpV⟩,hV ▸ hVU⟩
    · exact False.elim (hit_neg_excludes c U (code_lower c U hUc) G ⟨p,hp,hpN⟩ hGU)
  · rintro ⟨s,⟨p,hp,hps⟩,hsU⟩
    exact ⟨p,hp,hsU hps⟩

theorem hit_basic_iff (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (G : GenericFilter (Conditions c))
    (hG : AtomicForcing.GroundGeneric M G) (p : Conditions c) :
    Hit G (basicCode c (label c p)) ↔ p ∈ G.carrier := by
  have hpM := hM c hc _ (label_mem c p)
  have hsM := singleton_mem M hM hT.pairing hpM
  have he := hit_regular_iff M c (CohenInternalDecision.below c {label c p}) hM hT hc
    (CohenInternalDecision.below_mem M c _ hM hT hc hsM)
    (fun _ h => (ZFSet.mem_sep.mp h).1) (below_lower c _) G hG
  change Hit G (basicCode c (label c p)) ↔ _ at he
  rw [he]
  constructor
  · rintro ⟨q,hq,hqp⟩
    obtain ⟨_,r,hr,hrq⟩ := ZFSet.mem_sep.mp hqp
    have hrp := ZFSet.mem_singleton.mp hr
    have hqp : label c p ⊆ label c q := hrp ▸ hrq
    exact G.upper hqp hq
  · intro hp
    exact ⟨p,hp,ZFSet.mem_sep.mpr ⟨label_mem c p,label c p,ZFSet.mem_singleton.mpr rfl,
      fun _ h => h⟩⟩

end TuringRigidity.RegularTreeCofinality

end OAI
