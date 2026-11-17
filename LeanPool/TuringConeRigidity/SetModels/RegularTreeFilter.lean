/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/RegularTreeFilter.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.RegularTreeCompatibility
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenFilters
public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanDense

/-!
# Regular Tree Filter
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.RegularTreeFilter
open TransitiveNameModel BoundedSetTheory CountableForcing InternalRegularOperations
open InternalRegularAlgebra InternalBooleanGeneric InternalBooleanDense InternalBooleanSyntax
open InternalCohen
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem refines_condition (c U p : ZFSet.{0}) (hU : IsCode c U) (hU0 : U ≠ ∅)
    (hUp : U ⊆ basicCode c p) : ∃ r ∈ U, p ⊆ r := by
  obtain he|⟨q,hq⟩ := ZFSet.eq_empty_or_nonempty U
  · exact False.elim (hU0 he)
  have hb : q ∈ regular c (CohenInternalDecision.below c {p}) := hUp hq
  obtain ⟨r,hr,hqr⟩ := (mem_regular _ _ _).mp hb |>.2 q (hU.1 hq) (fun _ h => h)
  obtain ⟨hrc,s,hs,hsr⟩ := ZFSet.mem_sep.mp hr
  have hsp := ZFSet.mem_singleton.mp hs
  exact ⟨r,code_lower c U hU q hq r hrc hqr,hsp ▸ hsr⟩

/-- The word-condition filter recording the tree nodes hit by the original condition filter. -/
noncomputable def branch (c : ZFSet.{0}) (f : List Bool → ZFSet.{0})
    (hroot : f [] = c) (hcode : ∀ s, IsCode c (f s))
    (hm : ∀ s t, s <+: t → f t ⊆ f s)
    (hd : ∀ a u v : List Bool, ∀ p ∈ f (a ++ [false] ++ u),
      p ∉ f (a ++ [true] ++ v))
    (G : GenericFilter (Conditions c)) : GenericFilter CohenBorelForcing.Condition where
  carrier := {s | Hit G (f s.word)}
  nonempty := by
    obtain ⟨p,hp⟩ := G.nonempty
    exact ⟨⟨[]⟩,p,hp,hroot.symm ▸ label_mem c p⟩
  upper := by
    intro p q hpq hp
    obtain ⟨r,hr,hrp⟩ := hp
    exact ⟨r,hr,hm q.word p.word hpq hrp⟩
  directed := by
    intro p q hp hq
    obtain ⟨r,hr,hrp⟩ := hp
    obtain ⟨s,hs,hsq⟩ := hq
    obtain ⟨t,_,htr,hts⟩ := G.directed hr hs
    have htp := code_lower c (f p.word) (hcode _) _ hrp _ (label_mem c t) htr
    have htq := code_lower c (f q.word) (hcode _) _ hsq _ (label_mem c t) hts
    rcases RegularTreeCompatibility.comparable_of_overlap f hd _ _ _ htp htq with h|h
    · exact ⟨q,⟨s,hs,hsq⟩,h,le_rfl⟩
    · exact ⟨p,⟨r,hr,hrp⟩,le_rfl,h⟩

/-- The regular codes attached by `A` to word conditions belonging to `D`. -/
noncomputable def nodeFamily (B A D : ZFSet.{0}) : ZFSet.{0} :=
  B.sep (fun U => ∃ w ∈ D, ZFSet.pair w U ∈ A)

theorem nodeFamily_mem (M B A D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hB : B ∈ M) (hA : A ∈ M) (hD : D ∈ M) : nodeFamily B A D ∈ M := by
  simpa only [nodeFamily,Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.pairMem 0 1 3))
      (cons D (fun _ => A)) (by intro i; cases i <;> assumption) hB

theorem nodeFamily_dense (c B A D : ZFSet.{0}) (f : List Bool → ZFSet.{0})
    (hf : ∀ s, f s ∈ B ∧ IsCode c (f s) ∧ f s ≠ ∅)
    (hA : ∀ s U, ZFSet.pair (wordCode s) U ∈ A ↔ U = f s)
    (hm : ∀ s t, s <+: t → f t ⊆ f s)
    (hden : ∀ U, IsCode c U → U ≠ ∅ → ∃ s, f s ⊆ U)
    (hD : Dense {p : CohenBorelForcing.Condition | wordCode p.word ∈ D}) :
    Dense {p : Conditions c | label c p ∈ ZFSet.sUnion (nodeFamily B A D)} := by
  intro p
  have hpB := mem_basicCode c _ (label_mem c p)
  have hp0 : basicCode c (label c p) ≠ ∅ := fun he => ZFSet.notMem_empty _ (he ▸ hpB)
  obtain ⟨s,hs⟩ := hden _ (regular_isCode c _) hp0
  obtain ⟨t,ht,htD⟩ := hD ⟨s⟩
  have htp : f t.word ⊆ basicCode c (label c p) := fun _ h => hs (hm s t.word ht h)
  obtain ⟨r,hr,hpr⟩ := refines_condition c _ _ (hf _).2.1 (hf _).2.2 htp
  obtain ⟨r,rfl⟩ := label_surjective c ((hf _).2.1.1 hr)
  exact ⟨r,hpr,ZFSet.mem_sUnion.mpr ⟨f t.word,
    ZFSet.mem_sep.mpr ⟨(hf _).1,wordCode t.word,htD,(hA _ _).mpr rfl⟩,hr⟩⟩

theorem branch_ground_generic (M c B A : ZFSet.{0}) (f : List Bool → ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hBM : B ∈ M) (hAM : A ∈ M)
    (hAf : FunctionGraph conditions B A)
    (hAs : ∀ s U, ZFSet.pair (wordCode s) U ∈ A ↔ U = f s)
    (hf : ∀ s, f s ∈ B ∧ IsCode c (f s) ∧ f s ≠ ∅)
    (hroot : f [] = c)
    (hm : ∀ s t, s <+: t → f t ⊆ f s)
    (hd : ∀ a u v : List Bool, ∀ p ∈ f (a ++ [false] ++ u),
      p ∉ f (a ++ [true] ++ v))
    (hden : ∀ U, IsCode c U → U ≠ ∅ → ∃ s, f s ⊆ U)
    (G : GenericFilter (Conditions c)) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M
      (pushFilter (branch c f hroot (fun s => (hf s).2.1) hm hd G)) := by
  apply (groundGeneric_iff M _).mpr
  intro D hDM hD
  obtain ⟨p,hp,hpD⟩ := hG (ZFSet.sUnion (nodeFamily B A D))
    (union_mem M hM hT.union (nodeFamily_mem M B A D hM hT hBM hAM hDM))
    (nodeFamily_dense c B A D f hf hAs hm hden hD)
  obtain ⟨U,hUF,hpU⟩ := ZFSet.mem_sUnion.mp hpD
  obtain ⟨_,w,hw,hwU⟩ := ZFSet.mem_sep.mp hUF
  obtain ⟨w',hw',U',_,he⟩ := hAf.1 _ hwU
  have hwc : w ∈ conditions := (ZFSet.pair_inj.mp he).1 ▸ hw'
  obtain ⟨s,hs⟩ := (prefix_iff_wordCode w).mp ((mem_conditions w).mp hwc)
  have hUs : U = f s := (hAs s U).mp (hs.symm ▸ hwU)
  refine ⟨⟨s⟩,?_,hs.symm ▸ hw⟩
  rw [pull_push]
  exact ⟨p,hp,hUs ▸ hpU⟩

end TuringRigidity.RegularTreeFilter

end OAI
