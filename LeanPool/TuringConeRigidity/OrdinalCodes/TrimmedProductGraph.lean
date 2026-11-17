/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/TrimmedProductGraph.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.TrimmedPresentation
public import LeanPool.TuringConeRigidity.OrdinalCodes.CodeOperationCertificates

/-!
# Trimmed Product Graph
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalCoding
universe u

noncomputable def trimmedProductGraphSentence : SentenceForm :=
  .ex (.ex (.ex (.ex (.ex (.conj
    (fromBounded (.conj (.member 4 7) (.conj (.member 3 6)
      (.conj (.orderedPair 2 4 3) (.orderedPair 5 2 1)))))
    (.conj (ordinalProductAt 0 6 4) (codeSumAt 1 0 3)))))))

theorem trimmedProductGraphSentence_semantics (A : ZFSet.{u}) (hA : Transitive A)
    (e : ℕ → ZFSet.{u}) (he : ∀ i, e i ∈ A) :
    trimmedProductGraphSentence.Sat (A : Set ZFSet) e ↔
      ∃ s ∈ A, ∃ t ∈ A, ∃ x ∈ A, ∃ y ∈ A, ∃ v ∈ A,
        (s ∈ e 2 ∧ t ∈ e 1 ∧ x = ZFSet.pair s t ∧ e 0 = ZFSet.pair x y) ∧
        (ordinalProductAt 0 6 4).Sat (A : Set ZFSet) (cons v (cons y (cons x (cons t (cons s
          e))))) ∧
        (codeSumAt 1 0 3).Sat (A : Set ZFSet) (cons v (cons y (cons x (cons t (cons s e))))) := by
  change (∃ s ∈ A, ∃ t ∈ A, ∃ x ∈ A, ∃ y ∈ A, ∃ v ∈ A, _) ↔ _
  apply exists_congr; intro s; apply and_congr_right; intro hs
  apply exists_congr; intro t; apply and_congr_right; intro ht
  apply exists_congr; intro x; apply and_congr_right; intro hx
  apply exists_congr; intro y; apply and_congr_right; intro hy
  apply exists_congr; intro v; apply and_congr_right; intro hv
  have hE : ∀ i, cons v (cons y (cons x (cons t (cons s e)))) i ∈ A := by
    intro i; rcases i with _|_|_|_|_|i
    · exact hv
    · exact hy
    · exact hx
    · exact ht
    · exact hs
    · exact he i
  rw [SentenceForm.Sat,bounded_sat,Formula.absolute _ A hA _ hE]
  simp only [Formula.Eval,Formula.eval_orderedPair,cons_zero,cons_succ,SentenceForm.Sat]

theorem trimmedProductGraphSentence_spec (R : ZFSet.{u}) (γ a b : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) (hω : ZFSet.omega.{u} ∈ level R γ)
    (ha : a.toZFSet ∈ level R γ) (hb : b.toZFSet ∈ level R γ)
    (hlocal : ∀ s < b, (a * s).toZFSet ∈ level R γ ∧
      ProductCertificates (level R γ) a s ∧ ∀ t < a,
        (a * s + t).toZFSet ∈ level R γ ∧ SumCertificates (level R γ) (a * s) t)
    (z : ZFSet.{u}) (hz : z ∈ level R γ) :
    trimmedProductGraphSentence.Sat (level R γ : Set ZFSet)
      (cons z (cons a.toZFSet (fun _ => b.toZFSet))) ↔
        ∃ x ∈ ZFSet.prod b.toZFSet a.toZFSet, z = ZFSet.pair x (productValue a x) := by
  let A := level R γ
  let e := cons z (cons a.toZFSet (fun _ => b.toZFSet))
  have he (i : ℕ) : e i ∈ A := by
    rcases i with _|_|i
    · exact hz
    · exact ha
    · exact hb
  rw [trimmedProductGraphSentence_semantics A (level_transitive R γ) e he]
  constructor
  · rintro ⟨s,hs,t,ht,x,hx,y,hy,v,hv,⟨hsb,hta,hxdef,hzdef⟩,hp,hq⟩
    change s ∈ b.toZFSet at hsb
    obtain ⟨s,hsb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hsb
    have hsb := Ordinal.toZFSet_mem_toZFSet_iff.mp hsb
    change t ∈ a.toZFSet at hta
    obtain ⟨t,hta,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hta
    have hta := Ordinal.toZFSet_mem_toZFSet_iff.mp hta
    have hE : ∀ i, cons v (cons y (cons x (cons t.toZFSet (cons s.toZFSet e)))) i ∈ A := by
      intro i; rcases i with _|_|_|_|_|i
      · exact hv
      · exact hy
      · exact hx
      · exact ht
      · exact hs
      · exact he i
    have hvdef : v = (a*s).toZFSet := by
      rw [ordinalProductAt,SentenceForm.sat_rename] at hp
      exact productSentence_sound A (level_transitive R γ) _ (fun i => hE _) a s rfl rfl hp
    have hydef : y = (a*s+t).toZFSet :=
      codeSumAt_sound A (level_transitive R γ) 1 0 3 _ hE (a*s) t hvdef rfl hq
    refine ⟨x,ZFSet.mem_prod.mpr ⟨s.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hsb,
      t.toZFSet,Ordinal.toZFSet_mem_toZFSet_iff.mpr hta,hxdef⟩,?_⟩
    change z = ZFSet.pair x y at hzdef
    rw [hzdef,hydef,hxdef,productValue_pair,Ordinal.rank_toZFSet,Ordinal.rank_toZFSet]
  · rintro ⟨x,hxd,hzdef⟩
    obtain ⟨s,hsb,t,hta,rfl⟩ := ZFSet.mem_prod.mp hxd
    change s ∈ b.toZFSet at hsb
    obtain ⟨s,hsb,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hsb
    have hsb := Ordinal.toZFSet_mem_toZFSet_iff.mp hsb
    change t ∈ a.toZFSet at hta
    obtain ⟨t,hta,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hta
    have hta := Ordinal.toZFSet_mem_toZFSet_iff.mp hta
    have hs := level_transitive R γ _ hb _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hsb)
    have ht := level_transitive R γ _ ha _ (Ordinal.toZFSet_mem_toZFSet_iff.mpr hta)
    have hx := orderedPair_mem_level_limit R γ hγ hs ht
    obtain ⟨hv,hp,hrest⟩ := hlocal s hsb
    obtain ⟨hy,hq⟩ := hrest t hta
    let E := cons (a*s).toZFSet (cons (a*s+t).toZFSet
      (cons (ZFSet.pair s.toZFSet t.toZFSet) (cons t.toZFSet (cons s.toZFSet e))))
    have hE (i : ℕ) : E i ∈ A := by
      rcases i with _|_|_|_|_|i
      · exact hv
      · exact hy
      · exact hx
      · exact ht
      · exact hs
      · exact he i
    refine ⟨s.toZFSet,hs,t.toZFSet,ht,_,hx,(a*s+t).toZFSet,hy,(a*s).toZFSet,hv,
      ⟨Ordinal.toZFSet_mem_toZFSet_iff.mpr hsb,Ordinal.toZFSet_mem_toZFSet_iff.mpr
        hta,rfl,?_⟩,?_,?_⟩
    · simpa only [e,cons_zero,productValue_pair,Ordinal.rank_toZFSet] using hzdef
    · exact ordinalProductAt_of_certificates A (level_transitive R γ) 0 6 4 E hE a s rfl rfl hp rfl
    · exact codeSumAt_of_certificates A (level_transitive R γ) hω 1 0 3 E hE (a*s) t rfl rfl hq rfl

theorem product_certificates_at_limit_successor (R : ZFSet.{u}) (γ a b : Ordinal.{u})
    (hγ : Order.IsSuccLimit γ) (hω : ZFSet.omega.{u} ∈ level R γ)
    (ha : a.toZFSet ∈ level R γ) (hb : b.toZFSet ∈ level R γ)
    (hlocal : ∀ s < b, (a * s).toZFSet ∈ level R γ ∧
      ProductCertificates (level R γ) a s ∧ ∀ t < a,
        (a * s + t).toZFSet ∈ level R γ ∧ SumCertificates (level R γ) (a * s) t) :
    ProductCertificates (level R (γ+1)) a b := by
  refine ⟨product_domain_at_limit_successor R γ hγ ha hb,
    product_relation_at_limit_successor R γ hγ ha hb,?_⟩
  apply presentation_graph_at_limit_successor R γ hγ _ _ (a*b) (productValue a)
    (product_domain_subset_limit R γ hγ ha hb) ?_
    (productValue_mem a b) (productValue_surjective a b) (productValue_relation a b)
    trimmedProductGraphSentence (cons a.toZFSet (fun _ => b.toZFSet))
    (fun i => by
      cases i
      · exact ha
      · exact hb)
  · exact trimmedProductGraphSentence_spec R γ a b hγ hω ha hb hlocal
  · intro x hx
    obtain ⟨s,hs,t,ht,rfl⟩ := ZFSet.mem_prod.mp hx
    obtain ⟨s,hs,rfl⟩ := Ordinal.mem_toZFSet_iff.mp hs
    obtain ⟨t,ht,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
    have hs := Ordinal.toZFSet_mem_toZFSet_iff.mp hs
    have ht := Ordinal.toZFSet_mem_toZFSet_iff.mp ht
    simpa only [productValue_pair,Ordinal.rank_toZFSet] using ((hlocal s hs).2.2 t ht).1

end TuringRigidity.OrdinalArithmetic

end OAI
