/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/TrimmedSumDomains.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedOrderDomains

/-!
# Trimmed Sum Domains
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

noncomputable def trimmedSumDomainSentence : SentenceForm := fromBounded
  (.disj (.existsMem 1 (.orderedPair 1 4 0)) (.existsMem 2 (.orderedPair 1 5 0)))

noncomputable def trimmedSumRelationSentence : SentenceForm :=
  .ex (.ex (fromBounded (.conj (.orderedPair 2 1 0) (sumLessFormula 3 4 5 6 1 0))))

theorem sum_domain_subset_limit (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ) :
    sumDomain a b ⊆ level R γ := by
  intro z hz
  rcases (mem_sumDomain a b z).mp hz with ⟨s,hs,rfl⟩|⟨s,hs,rfl⟩
  · exact orderedPair_mem_level_limit R γ hγ h0 (level_transitive R γ _ ha _ hs)
  · exact orderedPair_mem_level_limit R γ hγ h1 (level_transitive R γ _ hb _ hs)

theorem sum_domain_at_limit_successor (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ) :
    sumDomain a b ∈ level R (γ+1) := by
  let e := cons a (cons b (cons ∅ (fun _ => {∅})))
  have he (i : ℕ) : e i ∈ level R γ := by
    rcases i with _ | _ | _ | i
    · exact ha
    · exact hb
    · exact h0
    · exact h1
  apply defined_set_at_successor R γ trimmedSumDomainSentence e he _
    (sum_domain_subset_limit R γ hγ ha hb h0 h1)
  intro z hz
  rw [trimmedSumDomainSentence,bounded_sat,Formula.absolute _ _ (level_transitive R γ) _
    (fun i => by
      cases i
      · exact hz
      · exact he _)]
  simp only [Formula.eval_disj,Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e,
    mem_sumDomain,leftNode,rightNode]

theorem sum_relation_at_limit_successor (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ)
    (h0 : (∅ : ZFSet.{u}) ∈ level R γ) (h1 : ({∅} : ZFSet.{u}) ∈ level R γ) :
    sumRelation a b ∈ level R (γ+1) := by
  let A := level R γ
  let e := cons a (cons b (cons ∅ (fun _ => {∅})))
  have he (i : ℕ) : e i ∈ A := by
    rcases i with _ | _ | _ | i
    · exact ha
    · exact hb
    · exact h0
    · exact h1
  have hd := sum_domain_subset_limit R γ hγ ha hb h0 h1
  have hsub : sumRelation a b ⊆ A := by
    intro z hz
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp (sumRelation_on a b hz)
    exact orderedPair_mem_level_limit R γ hγ (hd hx) (hd hy)
  apply defined_set_at_successor R γ trimmedSumRelationSentence e he _ hsub
  intro z hz
  change (∃ x ∈ A, ∃ y ∈ A, (fromBounded _).Sat _ (cons y (cons x (cons z e)))) ↔ _
  have hspec (x y : ZFSet.{u}) (hx : x ∈ A) (hy : y ∈ A) :
      (fromBounded (.conj (.orderedPair 2 1 0) (sumLessFormula 3 4 5 6 1 0))).Sat
        (A : Set ZFSet) (cons y (cons x (cons z e))) ↔
          z = ZFSet.pair x y ∧ SumLess a b x y := by
    rw [bounded_sat,Formula.absolute _ A (level_transitive R γ) _ (fun i => by
      rcases i with _ | _ | _ | i
      · exact hy
      · exact hx
      · exact hz
      · exact he i)]
    simp only [Formula.Eval,Formula.eval_orderedPair]
    rw [sumLessFormula_eval _ _ _ _ _ _ _ rfl rfl]
    rfl
  constructor
  · rintro ⟨x,hx,y,hy,h⟩
    obtain ⟨rfl,hless⟩ := (hspec x y hx hy).mp h
    have hkeep := hless
    have hxy : x ∈ sumDomain a b ∧ y ∈ sumDomain a b := by
      rcases hless with ⟨s,hs,t,ht,rfl,rfl,_⟩|⟨s,hs,t,ht,rfl,rfl⟩|⟨s,hs,t,ht,rfl,rfl,_⟩
      · exact ⟨(mem_sumDomain _ _ _).mpr (Or.inl ⟨s,hs,rfl⟩),
          (mem_sumDomain _ _ _).mpr (Or.inl ⟨t,ht,rfl⟩)⟩
      · exact ⟨(mem_sumDomain _ _ _).mpr (Or.inl ⟨s,hs,rfl⟩),
          (mem_sumDomain _ _ _).mpr (Or.inr ⟨t,ht,rfl⟩)⟩
      · exact ⟨(mem_sumDomain _ _ _).mpr (Or.inr ⟨s,hs,rfl⟩),
          (mem_sumDomain _ _ _).mpr (Or.inr ⟨t,ht,rfl⟩)⟩
    exact (pair_mem_sumRelation a b x y).mpr ⟨hxy.1,hxy.2,hkeep⟩
  · intro h
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp (sumRelation_on a b h)
    exact ⟨x,hd hx,y,hd hy,(hspec x y (hd hx) (hd hy)).mpr
      ⟨rfl,((pair_mem_sumRelation a b x y).mp h).2.2⟩⟩

end TuringRigidity.OrdinalArithmetic

end OAI
