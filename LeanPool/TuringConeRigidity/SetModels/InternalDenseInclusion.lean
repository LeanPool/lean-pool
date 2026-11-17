/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/InternalDenseInclusion.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalCollapseConditions

/-!
# Internal Dense Inclusion
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.InternalDenseInclusion
open TransitiveNameModel BoundedSetTheory CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- Include a condition from a subset poset in the larger set-coded poset. -/
noncomputable def embed (a b : ZFSet.{0}) (hab : a ⊆ b) (p : Conditions a) : Conditions b :=
  equivShrink b ⟨label a p,hab (label_mem a p)⟩

theorem label_embed (a b : ZFSet.{0}) (hab : a ⊆ b) (p : Conditions a) :
    label b (embed a b hab p) = label a p := by simp [embed,label]

theorem embed_le_iff (a b : ZFSet.{0}) (hab : a ⊆ b) (p q : Conditions a) :
    embed a b hab p ≤ embed a b hab q ↔ p ≤ q := by
  change label b (embed a b hab q) ⊆ label b (embed a b hab p) ↔ _
  rw [label_embed,label_embed]; rfl

/-- The set-coded identity graph from `a` into `b`. -/
noncomputable def inclusionGraph (a b : ZFSet.{0}) : ZFSet.{0} :=
  (ZFSet.prod a b).sep (fun z => ∃ p ∈ a, z = ZFSet.pair p p)

theorem pair_inclusionGraph (a b x y : ZFSet.{0}) (hab : a ⊆ b) :
    ZFSet.pair x y ∈ inclusionGraph a b ↔ x ∈ a ∧ y = x := by
  constructor
  · intro h
    obtain ⟨_,p,hp,he⟩ := ZFSet.mem_sep.mp h
    obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
    exact ⟨hp,rfl⟩
  · rintro ⟨hx,hy⟩
    rw [hy]
    exact ZFSet.mem_sep.mpr ⟨ZFSet.pair_mem_prod.mpr ⟨hx,hab hx⟩,x,hx,rfl⟩

theorem inclusionGraph_mem (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) : inclusionGraph a b ∈ M := by
  let e := fun _ : ℕ => a
  simpa only [inclusionGraph,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded (.existsMem 1 (.orderedPair 1 0 0)) e
      (fun _ => ha) (product_mem M hM hT.pairing hT.union hT.powerSet
        hT.separation.finitePrefix.bounded ha hb)

theorem inclusionGraph_function (a b : ZFSet.{0}) (hab : a ⊆ b) :
    FunctionGraph a b (inclusionGraph a b) := by
  refine ⟨fun z hz => ZFSet.mem_prod.mp (ZFSet.mem_sep.mp hz).1,?_⟩
  intro x hx
  exact ⟨x,hab hx,(pair_inclusionGraph a b x x hab).mpr ⟨hx,rfl⟩,
    fun y _ hy => (pair_inclusionGraph a b x y hab).mp hy |>.2⟩

/-- Push a filter along the condition inclusion and take its upward closure. -/
noncomputable def push (a b : ZFSet.{0}) (hab : a ⊆ b) (G : GenericFilter (Conditions a)) :
    GenericFilter (Conditions b) where
  carrier := {q | ∃ p ∈ G.carrier, embed a b hab p ≤ q}
  nonempty := by obtain ⟨p,hp⟩ := G.nonempty; exact ⟨embed a b hab p,p,hp,le_rfl⟩
  upper := by rintro p q hpq ⟨r,hr,hrp⟩; exact ⟨r,hr,hrp.trans hpq⟩
  directed := by
    rintro p q ⟨s,hs,hsp⟩ ⟨t,ht,htq⟩
    obtain ⟨r,hr,hrs,hrt⟩ := G.directed hs ht
    exact ⟨embed a b hab r,⟨r,hr,le_rfl⟩,
      ((embed_le_iff a b hab r s).mpr hrs).trans hsp,
      ((embed_le_iff a b hab r t).mpr hrt).trans htq⟩

theorem embed_mem_push (a b : ZFSet.{0}) (hab : a ⊆ b)
    (G : GenericFilter (Conditions a)) (p : Conditions a) :
    embed a b hab p ∈ (push a b hab G).carrier ↔ p ∈ G.carrier := by
  constructor
  · rintro ⟨q,hq,hqp⟩; exact G.upper ((embed_le_iff a b hab q p).mp hqp) hq
  · intro hp; exact ⟨p,hp,le_rfl⟩

/-- The members of `a` having a weaker condition in the family `D` inside `b`. -/
noncomputable def densePull (a b D : ZFSet.{0}) : ZFSet.{0} :=
  a.sep (fun p => ∃ q ∈ b, q ∈ D ∧ q ⊆ p)

theorem densePull_mem (M a b D : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hD : D ∈ M) : densePull a b D ∈ M := by
  let e := cons b (fun _ => D)
  have he : ∀ i, e i ∈ M := by
    intro i
    cases i
    · exact hb
    · exact hD
  simpa only [densePull,Formula.Eval,Formula.eval_subset,cons_zero,cons_succ,e] using
    sep_mem M hM hT.separation.finitePrefix.bounded
      (.existsMem 1 (.conj (.member 0 3) (.subset 0 1))) e he ha

theorem push_ground_generic (M a b : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (ha : a ∈ M) (hb : b ∈ M) (hab : a ⊆ b)
    (hd : ∀ q ∈ b, ∃ p ∈ a, q ⊆ p)
    (G : GenericFilter (Conditions a)) (hG : AtomicForcing.GroundGeneric M G) :
    AtomicForcing.GroundGeneric M (push a b hab G) := by
  intro D hD hden
  have hpull : Dense {p : Conditions a | label a p ∈ densePull a b D} := by
    intro p
    obtain ⟨q,hqp,hqD⟩ := hden (embed a b hab p)
    obtain ⟨r,hr,hqr⟩ := hd (label b q) (label_mem b q)
    obtain ⟨r,rfl⟩ := label_surjective a hr
    have hpr : label a p ⊆ label a r :=
      fun z hz => hqr (hqp ((label_embed a b hab p).symm ▸ hz))
    exact ⟨r,hpr,ZFSet.mem_sep.mpr ⟨label_mem a r,label b q,label_mem b q,hqD,hqr⟩⟩
  obtain ⟨p,hp,hpD⟩ := hG (densePull a b D) (densePull_mem M a b D hM hT ha hb hD) hpull
  obtain ⟨_,q,hqb,hqD,hqp⟩ := ZFSet.mem_sep.mp hpD
  obtain ⟨q,rfl⟩ := label_surjective b hqb
  exact ⟨q,⟨p,hp,by change label b q ⊆ label b (embed a b hab p); rwa [label_embed]⟩,hqD⟩

end TuringRigidity.InternalDenseInclusion

end OAI
