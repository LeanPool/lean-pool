/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Syntax/BooleanExpressionCertificate.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.InternalBooleanGeneric

/-!
# Boolean Expression Certificate
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.BooleanExpressionCertificate
open TransitiveNameModel BoundedSetTheory InternalRegularOperations InternalRegularAlgebra
open InternalBooleanGeneric CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

/-- One expression-evaluation step: a seed value, a complement, or a supremum of child values. -/
def Step (c B Q S K g t U : ZFSet.{0}) : Prop :=
  (U ∈ S ∧ t = FiniteTerm.tag 0 U) ∨
  (∃ s ∈ K, ∃ V ∈ B, t = FiniteTerm.tag 1 s ∧
    ZFSet.pair s V ∈ g ∧ U = neg c V) ∨
  (∃ T ∈ K, ∃ F ∈ Q, t = FiniteTerm.tag 2 T ∧ U = supCode c F ∧
    (∀ s ∈ T, ∃ V ∈ F, ZFSet.pair s V ∈ g) ∧
    (∀ V ∈ F, ∃ s ∈ T, ZFSet.pair s V ∈ g))

/-- Every pair in `g` has its term and value in the prescribed bounds and satisfies the
evaluation step. -/
def Certificate (c B Q S K g : ZFSet.{0}) : Prop :=
  ∀ z ∈ g, ∃ t ∈ K, ∃ U ∈ B, z = ZFSet.pair t U ∧ Step c B Q S K g t U

theorem Step.mono {c B Q S K L g h t U : ZFSet.{0}}
    (hKL : K ⊆ L) (hgh : g ⊆ h) (hs : Step c B Q S K g t U) :
    Step c B Q S L h t U := by
  rcases hs with hs | hs | hs
  · exact Or.inl hs
  · obtain ⟨s,hs,V,hV,ht,hp,hU⟩ := hs
    exact Or.inr (Or.inl ⟨s,hKL hs,V,hV,ht,hgh hp,hU⟩)
  · obtain ⟨T,hT,F,hF,ht,hU,hTF,hFT⟩ := hs
    exact Or.inr (Or.inr ⟨T,hKL hT,F,hF,ht,hU,
      fun s hs => (hTF s hs).imp (fun V h => ⟨h.1,hgh h.2⟩),
      fun V hV => (hFT V hV).imp (fun s h => ⟨h.1,hgh h.2⟩)⟩)

theorem Certificate.step {c B Q S K g t U : ZFSet.{0}}
    (hg : Certificate c B Q S K g) (hp : ZFSet.pair t U ∈ g) :
    t ∈ K ∧ U ∈ B ∧ Step c B Q S K g t U := by
  obtain ⟨s,hs,V,hV,he,hstep⟩ := hg _ hp
  obtain ⟨rfl,rfl⟩ := ZFSet.pair_inj.mp he
  exact ⟨hs,hV,hstep⟩

theorem Certificate.enlarge {c B Q S K L g : ZFSet.{0}}
    (hg : Certificate c B Q S K g) (hKL : K ⊆ L) : Certificate c B Q S L g := by
  intro z hz
  obtain ⟨t,ht,U,hU,he,hs⟩ := hg z hz
  exact ⟨t,hKL ht,U,hU,he,hs.mono hKL (fun _ h => h)⟩

theorem Certificate.union {c B Q S K g h : ZFSet.{0}}
    (hg : Certificate c B Q S K g) (hh : Certificate c B Q S K h) :
    Certificate c B Q S K (g ∪ h) := by
  intro z hz
  rcases ZFSet.mem_union.mp hz with hz | hz
  · obtain ⟨t,ht,U,hU,he,hs⟩ := hg z hz
    exact ⟨t,ht,U,hU,he,hs.mono (fun _ h => h) (fun _ h => ZFSet.mem_union.mpr (Or.inl h))⟩
  · obtain ⟨t,ht,U,hU,he,hs⟩ := hh z hz
    exact ⟨t,ht,U,hU,he,hs.mono (fun _ h => h) (fun _ h => ZFSet.mem_union.mpr (Or.inr h))⟩

theorem Certificate.insert {c B Q S K g t U : ZFSet.{0}}
    (hg : Certificate c B Q S K g) (ht : t ∈ K) (hU : U ∈ B)
    (hs : Step c B Q S K g t U) :
    Certificate c B Q S K (g ∪ ({ZFSet.pair t U} : ZFSet.{0})) := by
  have hgg : g ⊆ g ∪ ({ZFSet.pair t U} : ZFSet.{0}) :=
    fun _ h => ZFSet.mem_union.mpr (Or.inl h)
  intro z hz
  rcases ZFSet.mem_union.mp hz with hz | hz
  · obtain ⟨s,hs,V,hV,he,hstep⟩ := hg z hz
    exact ⟨s,hs,V,hV,he,hstep.mono (fun _ h => h) hgg⟩
  · have he := ZFSet.mem_singleton.mp hz
    exact ⟨t,ht,U,hU,he,hs.mono (fun _ h => h) hgg⟩

theorem Certificate.induction {c B Q S K g : ZFSet.{0}}
    (hg : Certificate c B Q S K g) (P : ZFSet.{0} → Prop)
    (hseed : ∀ U ∈ S, P U)
    (hneg : ∀ U ∈ B, P U → P (neg c U))
    (hsup : ∀ F ∈ Q, (∀ U ∈ F, P U) → P (supCode c F))
    (t U : ZFSet.{0}) (hp : ZFSet.pair t U ∈ g) : P U := by
  have wf : WellFounded (fun a b : ZFSet.{0} => ZFSet.rank a < ZFSet.rank b) :=
    InvImage.wf ZFSet.rank Ordinal.lt_wf
  induction t using wf.induction generalizing U with
  | h t ih =>
    rcases (hg.step hp).2.2 with hs | hs | hs
    · exact hseed U hs.1
    · obtain ⟨s,_,V,hV,rfl,hchild,rfl⟩ := hs
      exact hneg V hV (ih s (FiniteTerm.pair_rank_right _ _) V hchild)
    · obtain ⟨T,_,F,hF,rfl,rfl,_,hFT⟩ := hs
      apply hsup F hF
      intro V hV
      obtain ⟨s,hs,hp⟩ := hFT V hV
      exact ih s ((ZFSet.rank_lt_of_mem hs).trans (FiniteTerm.pair_rank_right _ _)) V hp

theorem Certificate.generic_agreement (M c B Q S K g : ZFSet.{0})
    (hM : Transitive M) (hT : SourceT M) (hc : c ∈ M)
    (hB : ∀ U, U ∈ B ↔ U ∈ M ∧ IsCode c U)
    (hQ : ∀ F, F ∈ Q ↔ F ∈ M ∧ F ⊆ B)
    (hg : Certificate c B Q S K g)
    (G H : GenericFilter (Conditions c))
    (hG : AtomicForcing.GroundGeneric M G) (hH : AtomicForcing.GroundGeneric M H)
    (hseed : ∀ U ∈ S, Hit G U ↔ Hit H U)
    (t U : ZFSet.{0}) (hp : ZFSet.pair t U ∈ g) : Hit G U ↔ Hit H U := by
  apply hg.induction (fun U => Hit G U ↔ Hit H U) hseed ?_ ?_ t U hp
  · intro V hV ih
    obtain ⟨hVM,hVc⟩ := (hB V).mp hV
    rw [hit_complement_iff M c V hM hT hc hVM hVc G hG,
      hit_complement_iff M c V hM hT hc hVM hVc H hH,ih]
  · intro F hF ih
    obtain ⟨hFM,hFB⟩ := (hQ F).mp hF
    have hFc := fun U hU => ((hB U).mp (hFB hU)).2
    rw [hit_supCode_iff M c F hM hT hc hFM hFc G hG,
      hit_supCode_iff M c F hM hT hc hFM hFc H hH]
    exact exists_congr (fun U => and_congr_right (fun hU => ih U hU))

end TuringRigidity.BooleanExpressionCertificate

end OAI
