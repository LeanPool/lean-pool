/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConePullbackDefinition.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConePullbackProgram
public import LeanPool.TuringConeRigidity.Constructibility.OneRealConstructionDefinition
public import LeanPool.TuringConeRigidity.Representation.AmbientDegreeActual
public import LeanPool.TuringConeRigidity.TuringConeConstructibleExtension

/-!
# Constructibility of the inverse-join graph

The forward cone graph is already in relative L(R). Its inverse-join graph
is obtained by bounded separation using the internal degree order and the
least-upper-bound definition of a join. This supplies a genuine one-real
level definition for the relation consumed by the oracle-program theorem.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConePullbackDefinition

open TransitiveNameModel BoundedSetTheory ElementaryModel SetDegreeDecoding
open PersistentRestrictions ConePersistence ConeSetGraphs ConePullbackProgram
open RelativeConstructible OrdinalCoding

universe u
noncomputable section

/-- The element `Z` is an upper bound for `A` and `X` under `L` and lies below every common
upper bound in `D`. -/
def JoinCode (D L A X Z : ZFSet.{u}) : Prop :=
  ZFSet.pair A Z ∈ L ∧ ZFSet.pair X Z ∈ L ∧
    ∀ W ∈ D, (ZFSet.pair A W ∈ L ∧ ZFSet.pair X W ∈ L) → ZFSet.pair Z W ∈ L

/-- Bounded formula expressing the coded least-upper-bound property. -/
def joinFormula (d l a x z : ℕ) : Formula :=
  .conj (.pairMem a z l) (.conj (.pairMem x z l)
    (.allMem d (.imp (.conj (.pairMem (a+1) 0 (l+1)) (.pairMem (x+1) 0 (l+1)))
      (.pairMem (z+1) 0 (l+1)))))

@[simp] theorem eval_joinFormula (d l a x z : ℕ) (v : ℕ → ZFSet.{u}) :
    (joinFormula d l a x z).Eval v ↔ JoinCode (v d) (v l) (v a) (v x) (v z) := by
  simp only [joinFormula, Formula.Eval, Formula.eval_pairMem, Formula.eval_allMem,
    Formula.eval_imp, cons_zero, cons_succ, JoinCode]

theorem joinCode_iff (I : CountableIdeal) (L : ZFSet.{u})
    (hL : ∀ x ∈ I.carrier, ∀ y ∈ I.carrier,
      ZFSet.pair (degreeSet x) (degreeSet y) ∈ L ↔ x ≤ y)
    {a x z : Degree} (ha : a ∈ I.carrier) (hx : x ∈ I.carrier) (hz : z ∈ I.carrier) :
    JoinCode (idealSet I) L (degreeSet a) (degreeSet x) (degreeSet z) ↔ z = a ⊔ x := by
  have hs := I.join_mem ha hx
  constructor
  · rintro ⟨haZ, hxZ, hmin⟩
    apply le_antisymm
    · apply (hL z hz (a ⊔ x) hs).mp
      exact hmin _ ((mem_idealSet I _).mpr ⟨a ⊔ x, hs, rfl⟩)
        ⟨(hL a ha _ hs).mpr le_sup_left, (hL x hx _ hs).mpr le_sup_right⟩
    · exact sup_le ((hL a ha z hz).mp haZ) ((hL x hx z hz).mp hxZ)
  · rintro rfl
    refine ⟨(hL a ha _ hs).mpr le_sup_left, (hL x hx _ hs).mpr le_sup_right, ?_⟩
    intro W hW hAW
    obtain ⟨w, hw, rfl⟩ := (mem_idealSet I W).mp hW
    exact (hL _ hs w hw).mpr
      (sup_le ((hL a ha w hw).mp hAW.1) ((hL x hx w hw).mp hAW.2))

/-- The relation pairs `x` with a preimage whose image under `F` is the join of `A` and `x`. -/
def Relation (D L A F p : ZFSet.{u}) : Prop :=
  ∃ x ∈ D, ∃ y ∈ D, p = ZFSet.pair x y ∧
    ∃ z ∈ D, ZFSet.pair y z ∈ F ∧ JoinCode D L A x z

/-- Bounded formula describing the cone-isomorphism pullback through the join with the base. -/
def relationFormula (d l a f p : ℕ) : Formula :=
  .existsMem d (.existsMem (d+1) (.conj (.orderedPair (p+2) 1 0)
    (.existsMem (d+2) (.conj (.pairMem 1 0 (f+3))
      (joinFormula (d+3) (l+3) (a+3) 2 0)))))

@[simp] theorem eval_relationFormula (d l a f p : ℕ) (v : ℕ → ZFSet.{u}) :
    (relationFormula d l a f p).Eval v ↔ Relation (v d) (v l) (v a) (v f) (v p) := by
  simp only [relationFormula, Formula.Eval, Formula.eval_orderedPair,
    Formula.eval_pairMem, eval_joinFormula, cons_zero, cons_succ, Relation]

theorem relation_iff_graph {I : CountableIdeal} {a : Degree} (ρ : I ≃o Cone I a)
    (L : ZFSet.{u})
    (hL : ∀ x ∈ I.carrier, ∀ y ∈ I.carrier,
      ZFSet.pair (degreeSet x) (degreeSet y) ∈ L ↔ x ≤ y) (p : ZFSet.{u}) :
    Relation (idealSet I) L (degreeSet a) (coneGraph ρ) p ↔ p ∈ pullbackGraph ρ := by
  have ha := ConePresentation.base_mem ρ
  constructor
  · rintro ⟨X, hX, Y, hY, rfl, Z, hZ, hpair, hj⟩
    obtain ⟨x, hx, rfl⟩ := (mem_idealSet I X).mp hX
    obtain ⟨y, hy, rfl⟩ := (mem_idealSet I Y).mp hY
    obtain ⟨z, hz, rfl⟩ := (mem_idealSet I Z).mp hZ
    have hj' := (joinCode_iff I L hL ha hx hz).mp hj
    obtain ⟨t, ht⟩ := (mem_coneGraph ρ _).mp hpair
    obtain ⟨hyT, hzT⟩ := ZFSet.pair_inj.mp ht
    have hyt : (⟨y, hy⟩ : I) = t := Subtype.ext (degreeSet_injective hyT)
    have hmap : ρ ⟨y, hy⟩ = ⟨a ⊔ x, I.join_mem ha hx, le_sup_left⟩ := by
      apply Subtype.ext
      rw [hyt]
      exact (degreeSet_injective hzT).symm.trans hj'
    have hout : (inverseAt ρ ⟨x, hx⟩).val = y := by
      change (ρ.symm ⟨a ⊔ x, I.join_mem ha hx, le_sup_left⟩).val = y
      rw [←hmap, ρ.symm_apply_apply]
    exact (mem_pullbackGraph ρ _).mpr ⟨⟨x, hx⟩, by rw [hout]⟩
  · intro hp
    obtain ⟨x, rfl⟩ := (mem_pullbackGraph ρ _).mp hp
    have hz := I.join_mem ha x.property
    have hv : (ρ (inverseAt ρ x)).val = a ⊔ x.val :=
      congrArg Subtype.val (ρ.apply_symm_apply _)
    refine ⟨degreeSet x.val, (mem_idealSet I _).mpr ⟨x.val, x.property, rfl⟩,
      degreeSet (inverseAt ρ x).val,
      (mem_idealSet I _).mpr ⟨(inverseAt ρ x).val, (inverseAt ρ x).property, rfl⟩,
      rfl, degreeSet (a ⊔ x.val), (mem_idealSet I _).mpr ⟨_, hz, rfl⟩,
      (mem_coneGraph ρ _).mpr ⟨inverseAt ρ x, by rw [hv]⟩,
      (joinCode_iff I L hL ha x.property hz).mpr rfl⟩

/-- Bounded separation transforms an internal cone graph into its inverse-
join graph. The surrounding model need not satisfy Choice. -/
theorem graph_mem (N : ZFSet.{u}) (hN : Transitive N)
    (hP : Pairing N) (hU : BoundedSetTheory.Union N) (hPow : PowerSet N)
    (hS : Separation N) {I : CountableIdeal} {a : Degree} (ρ : I ≃o Cone I a)
    (L : ZFSet.{u}) (hD : idealSet I ∈ N) (hLM : L ∈ N)
    (hF : coneGraph ρ ∈ N)
    (hL : ∀ x ∈ I.carrier, ∀ y ∈ I.carrier,
      ZFSet.pair (degreeSet x) (degreeSet y) ∈ L ↔ x ≤ y) : pullbackGraph ρ ∈ N := by
  have ha : degreeSet.{u} a ∈ N := hN _ hD _
    ((mem_idealSet I _).mpr ⟨a, ConePresentation.base_mem ρ, rfl⟩)
  let v := cons (idealSet I) (cons L (cons (degreeSet a) (fun _ => coneGraph ρ)))
  have hv : ∀ n, v n ∈ N := by
    intro n
    rcases n with _ | n
    · exact hD
    rcases n with _ | n
    · exact hLM
    rcases n with _ | n
    · exact ha
    exact hF
  have hs := sep_mem N hN hS (relationFormula 1 2 3 4 0) v hv
    (product_mem N hN hP hU hPow hS hD hD)
  have heq : ZFSet.sep (fun p => (relationFormula 1 2 3 4 0).Eval (cons p v))
      (ZFSet.prod (idealSet I) (idealSet I)) = pullbackGraph ρ := by
    apply ZFSet.ext
    intro p
    rw [ZFSet.mem_sep, eval_relationFormula]
    change (p ∈ ZFSet.prod (idealSet I) (idealSet I) ∧
      Relation (idealSet I) L (degreeSet a) (coneGraph ρ) p) ↔ p ∈ pullbackGraph ρ
    rw [relation_iff_graph ρ L hL]
    exact ⟨And.right, fun h => ⟨(ZFSet.mem_sep.mp h).1, h⟩⟩
  exact heq ▸ hs

/-- The degree-order construction only needs the weak axioms available in
relative L(R); Choice is not needed. -/
theorem degreeOrder_mem (N : ZFSet.{u}) (hN : Transitive N)
    (hP : Pairing N) (hU : BoundedSetTheory.Union N) (hPow : PowerSet N)
    (hS : Separation N) (hω : ZFSet.omega.{u} ∈ N)
    (R : ZFSet.{u}) (_hRM : R ∈ N)
    (hR : ∀ w ∈ R, ∃ B : Oracle, realCode B = w)
    (hD : degreeUniverse R ∈ N) : degreeOrder R ∈ N := by
  exact BoundedSetTheory.internal_degreeOrder_of_degreeUniverse_mem
    N hN hP hU hPow hS hω R hR hD

/-- The actual inverse-join graph belongs to relative L(R), not merely a
pointwise selection of representatives of its values. -/
theorem graph_mem_relativeModel (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) {a : Degree}
    (ρ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a)
    (hp : ConePersistence.Persistent (modelIdeal M hM hT) ρ) :
    pullbackGraph ρ ∈ relativeModel M (groundReals M) := by
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
    ρ (degreeOrder R) (ground_idealSet_mem_relativeModel M hM hT) hLN
    (ConeConstructibleExtension.persistent_modelIdeal_graph_mem_relativeModel M hM hT ρ hp) hL

/-- A one-real level definition of precisely the inverse-join graph. -/
theorem graph_one_real_definition (M : ZFSet.{u}) [Countable (Conditions M)]
    (hM : Transitive M) (hT : SourceT M) {a : Degree}
    (ρ : modelIdeal M hM hT ≃o Cone (modelIdeal M hM hT) a)
    (hp : ConePersistence.Persistent (modelIdeal M hM hT) ρ) :
    ∃ (δ : Ordinal.{u}) (P : Oracle) (φ : SentenceForm),
      δ.toZFSet ∈ M ∧ P ∈ modelReals M ∧ φ.bound ≤ 2 ∧
      realCode P ∈ level (groundReals M) δ ∧
      pullbackGraph ρ = definedSubset (level (groundReals M) δ) φ
        (fun _ : Fin φ.bound => realCode P) := by
  obtain ⟨t, P, hP, hi, ht, hval⟩ :=
    construction_of_relativeModel M hM hT _ (graph_mem_relativeModel M hM hT ρ hp)
  obtain ⟨φ, hbound, hdef⟩ := t.cofinal_one_real_definition
  obtain ⟨β, _, _, _, hidx, hreal, hset⟩ :=
    hdef M hM hT P hP ht hi 0 (internal_ordinal_zero M hM hT)
  exact ⟨heightDomainIndex (paddedCode t.ordinalVector β), P, φ,
    hidx, hP, hbound, hreal, hval ▸ hset⟩

end
end OAI.TuringRigidity.ConePullbackDefinition
