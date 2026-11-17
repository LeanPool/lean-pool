/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RegularTreeRecovery.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RegularTreeCofinality
public import LeanPool.TuringConeRigidity.Representation.GenericFilterName

/-!
# Regular Tree Recovery
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RegularTreeRecovery
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense RegularTreeFilter
open RegularTreeCofinality InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- The word conditions whose attached regular-code nodes meet `g`. -/
noncomputable def branchSet (B A g : ZFSet.{0}) : ZFSet.{0} :=
  conditions.sep (fun s => ∃ U ∈ B, ZFSet.pair s U ∈ A ∧ ∃ p ∈ g, p ∈ U)

theorem branchSet_mem (N B A g : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hB : B ∈ N) (hA : A ∈ N) (hg : g ∈ N) : branchSet B A g ∈ N := by
  let e := cons B (cons A (fun _ => g))
  have he : ∀ i, e i ∈ N := by
    intro i
    rcases i with _|_|i
    · exact hB
    · exact hA
    · exact hg
  simpa only [branchSet,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.pairMem 1 0 3) (.existsMem 4 (.member 0 1)))) e he
      (conditions_mem N hN hT)

/-- Conditions whose coded neighborhoods contain a node selected by the branch set `w`. -/
noncomputable def recoverySet (c B A S k w : ZFSet.{0}) : ZFSet.{0} :=
  c.sep (fun p => ∃ U ∈ B, ∃ V ∈ S, ∃ s ∈ w,
    ZFSet.pair s U ∈ A ∧ ZFSet.pair p V ∈ k ∧ U ⊆ V)

theorem recoverySet_mem (N c B A S k w : ZFSet.{0}) (hN : Transitive N) (hT : SourceT N)
    (hc : c ∈ N) (hB : B ∈ N) (hA : A ∈ N) (hS : S ∈ N) (hk : k ∈ N) (hw : w ∈ N) :
    recoverySet c B A S k w ∈ N := by
  let e := cons B (cons S (cons w (cons A (fun _ => k))))
  have he : ∀ i, e i ∈ N := by
    intro i
    rcases i with _ | _ | _ | _ | i
    · exact hB
    · exact hS
    · exact hw
    · exact hA
    · exact hk
  simpa only [recoverySet,Formula.Eval,Formula.eval_pairMem,Formula.eval_subset,
    cons_zero,cons_succ,e] using
    sep_mem N hN hT.separation.finitePrefix.bounded
      (.existsMem 1 (.existsMem 3 (.existsMem 5
        (.conj (.pairMem 0 2 7) (.conj (.pairMem 3 1 8) (.subset 2 1)))))) e he hc

variable (c : ZFSet.{0}) (f : List Bool → ZFSet.{0})
variable (hroot : f [] = c) (hcode : ∀ s, IsCode c (f s))
variable (hm : ∀ s t, s <+: t → f t ⊆ f s)
variable (hd : ∀ a u v : List Bool, ∀ p ∈ f (a ++ [false] ++ u),
  p ∉ f (a ++ [true] ++ v))
variable (G : GenericFilter (Conditions c))

theorem word_mem (s : List Bool) :
    wordCode s ∈ genericFilterSet conditions (pushFilter (RegularTreeFilter.branch c f hroot hcode
      hm hd G)).carrier ↔
      Hit G (f s) := by
  rw [mem_genericFilterSet]
  constructor
  · rintro ⟨p,hp,hps⟩
    have he : p = conditionEquiv ⟨s⟩ := label_injective conditions (hps.trans
      (label_encodeCondition ⟨s⟩).symm)
    subst p
    simpa only [pushFilter,OrderIso.symm_apply_apply,Set.mem_ofPred_eq,RegularTreeFilter.branch]
      using hp
  · intro h
    exact ⟨conditionEquiv ⟨s⟩, by simpa only [pushFilter, OrderIso.symm_apply_apply,
      Set.mem_ofPred_eq, RegularTreeFilter.branch] using h,
      label_encodeCondition ⟨s⟩⟩

theorem branchFilterSet_eq (B A : ZFSet.{0})
    (hfB : ∀ s, f s ∈ B)
    (hAs : ∀ s U, ZFSet.pair (wordCode s) U ∈ A ↔ U = f s) :
    genericFilterSet conditions (pushFilter (RegularTreeFilter.branch c f hroot hcode hm hd
      G)).carrier =
      branchSet B A (genericFilterSet c G.carrier) := by
  apply ZFSet.ext; intro w
  constructor
  · intro hw
    obtain ⟨p,_,he⟩ := (mem_genericFilterSet _ _ w).mp hw
    have hwc : w ∈ conditions := he ▸ label_mem conditions p
    obtain ⟨s,hs⟩ := (prefix_iff_wordCode w).mp ((mem_conditions w).mp hwc)
    have hhit := (word_mem c f hroot hcode hm hd G s).mp (hs.symm ▸ hw)
    obtain ⟨p,hp,hps⟩ := hhit
    exact ZFSet.mem_sep.mpr ⟨hwc,f s,hfB s,hs ▸ (hAs s _).mpr rfl,
      label c p,(mem_genericFilterSet c _ _).mpr ⟨p,hp,rfl⟩,hps⟩
  · intro hw
    obtain ⟨hwc,U,hUB,hwU,p,hpg,hpU⟩ := ZFSet.mem_sep.mp hw
    obtain ⟨s,hs⟩ := (prefix_iff_wordCode w).mp ((mem_conditions w).mp hwc)
    have hU := (hAs s U).mp (hs.symm ▸ hwU)
    obtain ⟨p,hp,rfl⟩ := (mem_genericFilterSet c _ p).mp hpg
    exact hs ▸ (word_mem c f hroot hcode hm hd G s).mpr ⟨p,hp,hU ▸ hpU⟩

theorem originalFilterSet_eq (M B A S k : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M) (hB : B ∈ M) (hA : A ∈ M)
    (hfB : ∀ s, f s ∈ B) (hf0 : ∀ s, f s ≠ ∅)
    (hAs : ∀ s U, ZFSet.pair (wordCode s) U ∈ A ↔ U = f s)
    (hden : ∀ U, IsCode c U → U ≠ ∅ → ∃ s, f s ⊆ U)
    (hSs : ∀ p ∈ c, basicCode c p ∈ S)
    (hks : ∀ p ∈ c, ∀ U, ZFSet.pair p U ∈ k ↔ U = basicCode c p)
    (hG : AtomicForcing.GroundGeneric M G) :
    genericFilterSet c G.carrier = recoverySet c B A S k
      (genericFilterSet conditions (pushFilter (RegularTreeFilter.branch c f hroot hcode hm hd
        G)).carrier) := by
  apply ZFSet.ext; intro p
  constructor
  · intro hp
    obtain ⟨p,hpG,rfl⟩ := (mem_genericFilterSet c _ p).mp hp
    have hhit := (hit_basic_iff M c hM hT hc G hG p).mpr hpG
    obtain ⟨s,hs,hsB⟩ := (hit_iff_node M c B A _ f hM hT hc hB hA
      (basicCode_mem M c _ hM hT hc (label_mem c p)) (regular_isCode c _)
      (fun s => ⟨hfB s,hcode s,hf0 s⟩) hAs hden G hG).mp hhit
    exact ZFSet.mem_sep.mpr ⟨label_mem c p,f s,hfB s,basicCode c (label c p),hSs _ (label_mem c p),
      wordCode s,(word_mem c f hroot hcode hm hd G s).mpr hs,(hAs s _).mpr rfl,
      (hks _ (label_mem c p) _).mpr rfl,hsB⟩
  · intro hp
    obtain ⟨hpc,U,_,V,_,s,hsw,hsU,hpV,hUV⟩ := ZFSet.mem_sep.mp hp
    obtain ⟨p,rfl⟩ := label_surjective c hpc
    have hV := (hks _ (label_mem c p) V).mp hpV
    obtain ⟨q,_,hqs⟩ := (mem_genericFilterSet _ _ s).mp hsw
    have hsc : s ∈ conditions := hqs ▸ label_mem conditions q
    obtain ⟨t,ht⟩ := (prefix_iff_wordCode s).mp ((mem_conditions s).mp hsc)
    have hU := (hAs t U).mp (ht.symm ▸ hsU)
    obtain ⟨r,hr,hrt⟩ := (word_mem c f hroot hcode hm hd G t).mp (ht.symm ▸ hsw)
    have hhit : Hit G (basicCode c (label c p)) := ⟨r,hr,hV ▸ hUV (hU.symm ▸ hrt)⟩
    exact (mem_genericFilterSet c _ _).mpr ⟨p,(hit_basic_iff M c hM hT hc G hG p).mp hhit,rfl⟩

end TuringRigidity.RegularTreeRecovery

end OAI
