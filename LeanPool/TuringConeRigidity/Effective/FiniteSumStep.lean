/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/FiniteSumStep.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.FiniteSumDomains
public import LeanPool.TuringConeRigidity.Effective.FiniteSumGraph
public import LeanPool.TuringConeRigidity.SetModels.FinitePresentation

/-!
# Finite Sum Step
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.OrdinalArithmetic
open TransitiveNameModel BoundedSetTheory RelationCollapse ElementaryModel RelativeConstructible
  OrdinalCoding
universe u

theorem sum_certificates_at_add_five (R : ZFSet.{u}) (γ a b : Ordinal.{u})
    (hω : ZFSet.omega.{u} ∈ level R γ)
    (ha : a.toZFSet ∈ level R γ) (hb : b.toZFSet ∈ level R γ)
    (hlocal : ∀ t < b, (a + t).toZFSet ∈ level R γ ∧ SumCertificates (level R γ) a t) :
    SumCertificates (level R (γ+5)) a b := by
  have h0 := level_transitive R γ _ hω _ ZFSet.omega_zero
  have h1 : ({∅} : ZFSet.{u}) ∈ level R γ := by
    have h := level_transitive R γ _ hω _ ((mem_omega _).mpr ⟨1,rfl⟩)
    simpa [natSet] using h
  have h02 : γ ≤ γ+2 := le_self_add
  have h24 : γ+2 ≤ γ+4 := add_le_add le_rfl (by exact_mod_cast (show (2 : ℕ) ≤ 4 by decide) : (2 :
    Ordinal.{u}) ≤ 4)
  have h04 := h02.trans h24
  have hd2 : sumDomain a.toZFSet b.toZFSet ⊆ level R (γ+2) := by
    intro x hx
    rcases (mem_sumDomain _ _ _).mp hx with ⟨t,ht,rfl⟩|⟨t,ht,rfl⟩
    · exact orderedPair_mem_level_add_two R γ h0 (level_transitive R γ _ ha _ ht)
    · exact orderedPair_mem_level_add_two R γ h1 (level_transitive R γ _ hb _ ht)
  have hd4 : sumDomain a.toZFSet b.toZFSet ⊆ level R (γ+4) :=
    fun _ h => level_mono R h24 (hd2 h)
  have hr4 : sumRelation a.toZFSet b.toZFSet ⊆ level R (γ+4) := by
    intro z hz
    obtain ⟨x,hx,y,hy,rfl⟩ := ZFSet.mem_prod.mp (sumRelation_on _ _ hz)
    simpa only [add_assoc,show (2 : Ordinal.{u})+2=4 from by norm_num] using
      orderedPair_mem_level_add_two R (γ+2) (hd2 hx) (hd2 hy)
  have hv (x : ZFSet.{u}) (hx : x ∈ sumDomain a.toZFSet b.toZFSet) :
      sumValue a x ∈ level R γ := by
    rcases (mem_sumDomain _ _ _).mp hx with ⟨t,ht,rfl⟩|⟨t,ht,rfl⟩
    · simpa only [sumValue_left] using level_transitive R γ _ ha _ ht
    · obtain ⟨t,ht,rfl⟩ := Ordinal.mem_toZFSet_iff.mp ht
      simpa only [sumValue_right,Ordinal.rank_toZFSet] using (hlocal t
        (Ordinal.toZFSet_mem_toZFSet_iff.mp ht)).1
  have hpairs (x : ZFSet.{u}) (hx : x ∈ sumDomain a.toZFSet b.toZFSet) :
      ZFSet.pair x (sumValue a x) ∈ level R (γ+4) := by
    simpa only [add_assoc,show (2 : Ordinal.{u})+2=4 from by norm_num] using
      orderedPair_mem_level_add_two R (γ+2) (hd2 hx) (level_mono R h02 (hv x hx))
  have ha4 := level_mono R h04 ha
  have hb4 := level_mono R h04 hb
  have hz4 := level_mono R h04 h0
  have ho4 := level_mono R h04 h1
  have hω4 := level_mono R h04 hω
  have hc4 (t : Ordinal.{u}) (ht : t < b) :
      (a+t).toZFSet ∈ level R (γ+4) ∧ SumCertificates (level R (γ+4)) a t :=
    ⟨level_mono R h04 (hlocal t ht).1,(hlocal t ht).2.mono (level_mono R h04)⟩
  have hd := sum_domain_at_successor_of_subset R (γ+4) ha4 hb4 hz4 ho4 hd4
  have hr := sum_relation_at_successor_of_subset R (γ+4) ha4 hb4 hz4 ho4 hd4 hr4
  have hf := presentation_graph_at_successor_of_pairs R (γ+4) _ _ (a+b) (sumValue a)
    hpairs (sumValue_mem a b) (sumValue_surjective a b) (sumValue_relation a b)
    trimmedSumGraphSentence (cons a.toZFSet (cons b.toZFSet (cons ∅ (fun _ => {∅}))))
    (fun i => by
      rcases i with _|_|_|i
      · exact ha4
      · exact hb4
      · exact hz4
      · exact ho4)
    (sum_graph_spec_with_internal_nodes _ (level_transitive R (γ+4)) a b
      hω4 ha4 hb4 hz4 ho4 hc4 hd4)
  simpa only [SumCertificates, add_assoc, show (4 : Ordinal.{u})+1=5 from by norm_num] using
    And.intro hd (And.intro hr hf)

end TuringRigidity.OrdinalArithmetic

end OAI
