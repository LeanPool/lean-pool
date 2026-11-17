/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/TrimmedOrderDomains.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Constructibility.FiniteStageSetBounds
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalProductSets
public import LeanPool.TuringConeRigidity.OrdinalCodes.OrdinalSumSets

/-!
# Trimmed Order Domains
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
universe u

theorem defined_set_at_successor (R : ZFSet.{u}) (γ : Ordinal.{u})
    (p : SentenceForm) (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ level R γ)
    (s : ZFSet.{u}) (hsub : s ⊆ level R γ)
    (hs : ∀ z ∈ level R γ, p.Sat (level R γ : Set ZFSet) (cons z e) ↔ z ∈ s) :
    s ∈ level R (γ+1) := by
  have h := separation_mem_definablePower (level R γ) p e (fun i _ => he i)
  have eq : (level R γ).sep (fun z => p.Sat (level R γ : Set ZFSet) (cons z e)) = s := by
    apply ZFSet.ext; intro z
    rw [ZFSet.mem_sep]
    exact ⟨fun ⟨hz,hp⟩ => (hs z hz).mp hp,fun hz => ⟨hsub hz,(hs z (hsub hz)).mpr hz⟩⟩
  rw [eq] at h
  rwa [level_succ]

noncomputable def trimmedProductDomainSentence : SentenceForm :=
  fromBounded (.existsMem 2 (.existsMem 2 (.orderedPair 2 1 0)))

noncomputable def trimmedProductRelationSentence : SentenceForm :=
  .ex (.ex (fromBounded (.conj (.orderedPair 2 1 0) (productLessFormula 3 4 1 0))))

theorem product_domain_subset_limit (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ) : ZFSet.prod b a ⊆ level R γ := by
  intro z hz
  obtain ⟨s,hs,t,ht,rfl⟩ := ZFSet.mem_prod.mp hz
  exact orderedPair_mem_level_limit R γ hγ
    (level_transitive R γ _ hb _ hs) (level_transitive R γ _ ha _ ht)

theorem product_domain_at_limit_successor (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ) : ZFSet.prod b a ∈ level R (γ+1) := by
  let e := cons a (fun _ => b)
  have he (i : ℕ) : e i ∈ level R γ := by
    cases i
    · exact ha
    · exact hb
  apply defined_set_at_successor R γ trimmedProductDomainSentence e he _
    (product_domain_subset_limit R γ hγ ha hb)
  intro z hz
  rw [trimmedProductDomainSentence,bounded_sat,Formula.absolute _ _ (level_transitive R γ) _
    (fun i => by
      cases i
      · exact hz
      · exact he _)]
  simp only [Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,e,ZFSet.mem_prod]

theorem product_relation_at_limit_successor (R : ZFSet.{u}) (γ : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) {a b : ZFSet.{u}}
    (ha : a ∈ level R γ) (hb : b ∈ level R γ) : productRelation a b ∈ level R (γ+1) := by
  let A := level R γ
  let e := cons a (fun _ => b)
  have he (i : ℕ) : e i ∈ A := by
    cases i
    · exact ha
    · exact hb
  have hd := product_domain_subset_limit R γ hγ ha hb
  have hsub : productRelation a b ⊆ A := by
    intro z hz
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp (productRelation_on a b hz)
    exact orderedPair_mem_level_limit R γ hγ (hd hx) (hd hy)
  apply defined_set_at_successor R γ trimmedProductRelationSentence e he _ hsub
  intro z hz
  change (∃ x ∈ A, ∃ y ∈ A, (fromBounded _).Sat _ (cons y (cons x (cons z e)))) ↔ _
  have hspec (x y : ZFSet.{u}) (hx : x ∈ A) (hy : y ∈ A) :
      (fromBounded (.conj (.orderedPair 2 1 0) (productLessFormula 3 4 1 0))).Sat
        (A : Set ZFSet) (cons y (cons x (cons z e))) ↔
          z = ZFSet.pair x y ∧ ProductLess a b x y := by
    rw [bounded_sat,Formula.absolute _ A (level_transitive R γ) _ (fun i => by
      rcases i with _ | _ | _ | i
      · exact hy
      · exact hx
      · exact hz
      · exact he i)]
    simp only [Formula.Eval,Formula.eval_orderedPair,productLessFormula_eval,cons_zero,cons_succ,e]
  constructor
  · rintro ⟨x,hx,y,hy,h⟩
    obtain ⟨rfl,hless⟩ := (hspec x y hx hy).mp h
    have hkeep := hless
    obtain ⟨s,hs,t,ht,v,hv,w,hw,hx',hy',_⟩ := hless
    exact (pair_mem_productRelation a b x y).mpr
      ⟨ZFSet.mem_prod.mpr ⟨s,hs,t,ht,hx'⟩,ZFSet.mem_prod.mpr ⟨v,hv,w,hw,hy'⟩,hkeep⟩
  · intro h
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp (productRelation_on a b h)
    exact ⟨x,hd hx,y,hd hy,(hspec x y (hd hx) (hd hy)).mpr
      ⟨rfl,((pair_mem_productRelation a b x y).mp h).2.2⟩⟩

end TuringRigidity.OrdinalArithmetic

end OAI
