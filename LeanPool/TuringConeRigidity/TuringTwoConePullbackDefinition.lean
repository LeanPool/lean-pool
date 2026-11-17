/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringTwoConePullbackDefinition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringTwoConePullbackProgram
public import LeanPool.TuringConeRigidity.TuringConePullbackDefinition

/-!
# Relative constructibility of the joined inverse relation

Bounded separation from the forward graph, ordinary degree order, and target
base defines x |-> rho^{-1}(b join x). Both bases remain distinct. The bounded
join formula and the weak-model degree-order construction are reused unchanged.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConePullbackDefinition

open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions RelativeConstructible OrdinalCoding
open TwoConeSetGraphs TwoConePullbackProgram
open ConePersistence (Cone)
open ConePullbackDefinition (JoinCode Relation relationFormula eval_relationFormula
  joinCode_iff degreeOrder_mem)

universe u
noncomputable section

theorem relation_iff_graph {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (hb : b ∈ I.carrier) (L : ZFSet.{u})
    (hL : ∀ x ∈ I.carrier, ∀ y ∈ I.carrier,
      ZFSet.pair (degreeSet x) (degreeSet y) ∈ L ↔ x ≤ y) (p : ZFSet.{u}) :
    Relation (idealSet I) L (degreeSet b) (coneGraph ρ) p ↔ p ∈ pullbackGraph ρ hb := by
  constructor
  · rintro ⟨X, hX, Y, hY, rfl, Z, hZ, hpair, hj⟩
    obtain ⟨x, hx, rfl⟩ := (mem_idealSet I X).mp hX
    obtain ⟨y, hy, rfl⟩ := (mem_idealSet I Y).mp hY
    obtain ⟨z, hz, rfl⟩ := (mem_idealSet I Z).mp hZ
    have hj' := (joinCode_iff I L hL hb hx hz).mp hj
    obtain ⟨t, ht⟩ := (mem_coneGraph ρ _).mp hpair
    obtain ⟨hyT, hzT⟩ := ZFSet.pair_inj.mp ht
    have hmap : ρ t = ⟨b ⊔ x, I.join_mem hb hx, le_sup_left⟩ :=
      Subtype.ext ((degreeSet_injective hzT).symm.trans hj')
    have hout : (inverseAt ρ hb ⟨x, hx⟩).val = y := by
      change (ρ.symm ⟨b ⊔ x, I.join_mem hb hx, le_sup_left⟩).val = y
      rw [← hmap, ρ.symm_apply_apply]
      exact (degreeSet_injective hyT).symm
    exact (mem_pullbackGraph ρ hb _).mpr ⟨⟨x, hx⟩, by rw [hout]⟩
  · intro hp
    obtain ⟨x, rfl⟩ := (mem_pullbackGraph ρ hb _).mp hp
    have hz := I.join_mem hb x.property
    have hv : (ρ (inverseAt ρ hb x)).val = b ⊔ x.val :=
      congrArg Subtype.val (ρ.apply_symm_apply _)
    refine ⟨degreeSet x.val, (mem_idealSet I _).mpr ⟨x.val, x.property, rfl⟩,
      degreeSet (inverseAt ρ hb x).val,
      (mem_idealSet I _).mpr ⟨(inverseAt ρ hb x).val, (inverseAt ρ hb x).property.1, rfl⟩,
      rfl, degreeSet (b ⊔ x.val), (mem_idealSet I _).mpr ⟨_, hz, rfl⟩,
      (mem_coneGraph ρ _).mpr ⟨inverseAt ρ hb x, by rw [hv]⟩,
      (joinCode_iff I L hL hb x.property hz).mpr rfl⟩

/-- Internality of the whole joined inverse graph, with no internal Choice. -/
theorem graph_mem (N : ZFSet.{u}) (hN : Transitive N)
    (hP : Pairing N) (hU : BoundedSetTheory.Union N) (hPow : PowerSet N)
    (hS : Separation N) {I : CountableIdeal} {a b : Degree}
    (ρ : Cone I a ≃o Cone I b) (hb : b ∈ I.carrier)
    (L : ZFSet.{u}) (hD : idealSet I ∈ N) (hLM : L ∈ N)
    (hF : coneGraph ρ ∈ N)
    (hL : ∀ x ∈ I.carrier, ∀ y ∈ I.carrier,
      ZFSet.pair (degreeSet x) (degreeSet y) ∈ L ↔ x ≤ y) : pullbackGraph ρ hb ∈ N := by
  have hbN : degreeSet.{u} b ∈ N := hN _ hD _
    ((mem_idealSet I _).mpr ⟨b, hb, rfl⟩)
  let v := cons (idealSet I) (cons L (cons (degreeSet b) (fun _ => coneGraph ρ)))
  have hv : ∀ n, v n ∈ N := by
    intro n
    rcases n with _ | n
    · exact hD
    rcases n with _ | n
    · exact hLM
    rcases n with _ | n
    · exact hbN
    exact hF
  have hs := sep_mem N hN hS (relationFormula 1 2 3 4 0) v hv
    (product_mem N hN hP hU hPow hS hD hD)
  have heq : ZFSet.sep (fun p => (relationFormula 1 2 3 4 0).Eval (cons p v))
      (ZFSet.prod (idealSet I) (idealSet I)) = pullbackGraph ρ hb := by
    apply ZFSet.ext
    intro p
    rw [ZFSet.mem_sep, eval_relationFormula]
    change (p ∈ ZFSet.prod (idealSet I) (idealSet I) ∧
      Relation (idealSet I) L (degreeSet b) (coneGraph ρ) p) ↔ p ∈ pullbackGraph ρ hb
    rw [relation_iff_graph ρ hb L hL]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.mp h).1, h⟩⟩
  exact heq ▸ hs

theorem graph_mem_relativeModel (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) {a b : Degree}
    (ρ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b)
    (hp : TwoConePersistence.Persistent (modelIdeal M hM hT) ρ)
    (ha : a ∈ (modelIdeal M hM hT).carrier) (hb : b ∈ (modelIdeal M hM hT).carrier) :
    pullbackGraph ρ hb ∈ relativeModel M (groundReals M) := by
  let R := groundReals M
  let N := relativeModel M R
  have hR := groundReals_mem M hM hT
  have hRN : R ∈ N := (mem_relativeModel M R R hM hT hR).mpr
    (parameter_in_relativeModel M R hM hT)
  have hr (w : ZFSet.{u}) (hw : w ∈ R) : ∃ B : Oracle, realCode B = w :=
    ⟨decodeReal w, realCode_decodeReal ((mem_groundReals M w).mp hw).2⟩
  have hDN := ground_degreeUniverse_mem_relativeModel M hM hT
  have hLN := degreeOrder_mem N (relativeModel_transitive M R hM)
    (relativeModel_pairing M R hM hT hR) (relativeModel_union M R hM hT hR)
    (relativeModel_power_set M R hM hT hR) (relativeModel_bounded_separation M R hM hT hR)
    (ground_relativeModel_omega M hM hT) R hRN hr hDN
  have hL : ∀ x ∈ (modelIdeal M hM hT).carrier, ∀ y ∈ (modelIdeal M hM hT).carrier,
      ZFSet.pair (degreeSet x) (degreeSet y) ∈ degreeOrder R ↔ x ≤ y := by
    rintro x ⟨A, hA, rfl⟩ y ⟨B, hB, rfl⟩
    exact FullSetForcing.ownDegreeOrder_actual M hM hT R (mem_groundReals M) A hA B hB
  exact graph_mem N (relativeModel_transitive M R hM)
    (relativeModel_pairing M R hM hT hR) (relativeModel_union M R hM hT hR)
    (relativeModel_power_set M R hM hT hR) (relativeModel_bounded_separation M R hM hT hR)
    ρ hb (degreeOrder R) (ground_idealSet_mem_relativeModel M hM hT) hLN
    (TwoConeConstructibleExtension.persistent_modelIdeal_graph_mem_relativeModel
      M hM hT ρ hp ha hb) hL

/-- A one-real definition of this actual total relation on the ordinary ideal. -/
theorem graph_one_real_definition (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) {a b : Degree}
    (ρ : Cone (modelIdeal M hM hT) a ≃o Cone (modelIdeal M hM hT) b)
    (hp : TwoConePersistence.Persistent (modelIdeal M hM hT) ρ)
    (ha : a ∈ (modelIdeal M hM hT).carrier) (hb : b ∈ (modelIdeal M hM hT).carrier) :
    ∃ (δ : Ordinal.{u}) (P : Oracle) (φ : SentenceForm),
      δ.toZFSet ∈ M ∧ P ∈ modelReals M ∧ φ.bound ≤ 2 ∧
      realCode P ∈ level (groundReals M) δ ∧
      pullbackGraph ρ hb = definedSubset (level (groundReals M) δ) φ
        (fun _ : Fin φ.bound => realCode P) := by
  obtain ⟨t, P, hP, hi, ht, hval⟩ :=
    construction_of_relativeModel M hM hT _ (graph_mem_relativeModel M hM hT ρ hp ha hb)
  obtain ⟨φ, hbound, hdef⟩ := t.cofinal_one_real_definition
  obtain ⟨β, _, _, _, hidx, hreal, hset⟩ :=
    hdef M hM hT P hP ht hi 0 (internal_ordinal_zero M hM hT)
  exact ⟨heightDomainIndex (paddedCode t.ordinalVector β), P, φ,
    hidx, hP, hbound, hreal, hval ▸ hset⟩

end
end OAI.TuringRigidity.TwoConePullbackDefinition
