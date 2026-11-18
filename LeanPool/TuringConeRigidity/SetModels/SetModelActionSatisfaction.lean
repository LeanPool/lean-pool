/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/SetModelActionSatisfaction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.SetModels.SetModelIdealSatisfaction
public import LeanPool.TuringConeRigidity.SetModels.SetModelCountability

/-!
# Set Model Action Satisfaction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.SetModelSatisfaction
open BoundedSetTheory TransitiveNameModel SetModelReals SetModelFunctions SetModelSyntax
open SetDegreeDecoding PersistentRestrictions SetModelCountability
universe u
noncomputable section
variable {M : ZFSet.{u}}

/-- Bounded formula expressing a surjective action preserving and reflecting the relation `l`. -/
def actionFormula (f i l : ℕ) : Formula :=
  .conj (ontoFormula f i i)
    (.allMem i (.allMem (i+1) (.allMem (i+2) (.allMem (i+3)
      (.imp (.conj (.pairMem 3 1 (f+4)) (.pairMem 2 0 (f+4)))
        (.iff (.pairMem 3 2 (l+4)) (.pairMem 1 0 (l+4))))))))

/-- A surjective function graph on `i` preserving and reflecting its coded relation. -/
def IsAction (f i l : ZFSet.{u}) : Prop :=
  (FunctionGraph f i i ∧ ∀ y ∈ i, ∃ x ∈ i, ZFSet.pair x y ∈ f) ∧
    ∀ x ∈ i, ∀ y ∈ i, ∀ a ∈ i, ∀ b ∈ i,
      ZFSet.pair x a ∈ f ∧ ZFSet.pair y b ∈ f →
        (ZFSet.pair x y ∈ l ↔ ZFSet.pair a b ∈ l)

@[simp] theorem eval_actionFormula (f i l : ℕ) (e : ℕ → ZFSet.{u}) :
    (actionFormula f i l).Eval e ↔ IsAction (e f) (e i) (e l) := by
  simp only [actionFormula,Formula.Eval,eval_ontoFormula,Formula.eval_allMem,
    Formula.eval_imp,Formula.eval_iff,Formula.eval_pairMem,cons_zero,cons_succ,IsAction]

theorem action_code {I : CountableIdeal} (ρ : I ≃o I) (a b : I) :
    ZFSet.pair (degreeSet.{u} a.val) (degreeSet b.val) ∈ automorphismSet ρ ↔ ρ a = b := by
  rw [mem_automorphismSet]
  constructor
  · rintro ⟨c,he⟩
    obtain ⟨ha,hb⟩ := ZFSet.pair_inj.mp he
    have ha' : a=c := Subtype.ext (degreeSet_injective ha)
    have hb' : b=ρ c := Subtype.ext (degreeSet_injective hb)
    rw [ha',hb']
  · intro h
    exact ⟨a,by rw [h]⟩

theorem action_satisfaction (C : Context M) {L : ZFSet.{u}}
    (hL : ∀ A ∈ reals M, ∀ B ∈ reals M,
      ZFSet.pair (degreeSet (degree A)) (degreeSet (degree B)) ∈ L ↔ Reduces A B)
    {I : CountableIdeal} (hI : idealSet I ∈ M) (ρ : I ≃o I) :
    IsAction (automorphismSet ρ) (idealSet I) L := by
  have hm (a : I) : degreeSet.{u} a.val ∈ M :=
    C.transitive _ hI _ ((mem_idealSet I _).mpr ⟨a.val,a.property,rfl⟩)
  have hi (a : I) : degreeSet.{u} a.val ∈ idealSet I :=
    (mem_idealSet I _).mpr ⟨a.val,a.property,rfl⟩
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · intro z hz
    obtain ⟨a,rfl⟩ := (mem_automorphismSet ρ z).mp hz
    exact ⟨degreeSet a.val,hi a,degreeSet (ρ a).val,hi (ρ a),rfl⟩
  · intro x hx
    obtain ⟨a,ha,rfl⟩ := (mem_idealSet I x).mp hx
    let a' : I := ⟨a,ha⟩
    refine ⟨degreeSet (ρ a').val,hi (ρ a'),(action_code ρ a' (ρ a')).mpr rfl,?_⟩
    intro z hz hxz
    obtain ⟨b,hb,rfl⟩ := (mem_idealSet I z).mp hz
    have hh := (action_code ρ a' ⟨b,hb⟩).mp hxz
    exact congrArg (fun c : I => degreeSet c.val) hh.symm
  · intro y hy
    obtain ⟨b,hb,rfl⟩ := (mem_idealSet I y).mp hy
    let b' : I := ⟨b,hb⟩
    exact ⟨degreeSet (ρ.symm b').val,hi (ρ.symm b'),
      (action_code ρ (ρ.symm b') b').mpr (ρ.apply_symm_apply b')⟩
  · intro x hx y hy a ha b hb hab
    obtain ⟨x,hxc,rfl⟩ := (mem_idealSet I x).mp hx
    obtain ⟨y,hyc,rfl⟩ := (mem_idealSet I y).mp hy
    obtain ⟨a,hac,rfl⟩ := (mem_idealSet I a).mp ha
    obtain ⟨b,hbc,rfl⟩ := (mem_idealSet I b).mp hb
    have hxa := (action_code ρ ⟨x,hxc⟩ ⟨a,hac⟩).mp hab.1
    have hyb := (action_code ρ ⟨y,hyc⟩ ⟨b,hbc⟩).mp hab.2
    rw [order_code C hL (hm ⟨x,hxc⟩) (hm ⟨y,hyc⟩),
      order_code C hL (hm ⟨a,hac⟩) (hm ⟨b,hbc⟩)]
    change (⟨x,hxc⟩ : I) ≤ ⟨y,hyc⟩ ↔ (⟨a,hac⟩ : I) ≤ ⟨b,hbc⟩
    rw [←hxa,←hyb]
    exact ρ.le_iff_le.symm

theorem extends_sets {I J : CountableIdeal} {ρ : I ≃o I} {σ : J ≃o J}
    {hIJ : I.carrier ⊆ J.carrier} (he : Extends hIJ ρ σ) :
    automorphismSet.{u} ρ ⊆ automorphismSet σ := by
  intro z hz
  obtain ⟨a,rfl⟩ := (mem_automorphismSet ρ z).mp hz
  exact (mem_automorphismSet σ _).mpr ⟨⟨a.val,hIJ a.property⟩,by rw [he a]⟩

theorem ideal_subset {I J : CountableIdeal} (h : I.carrier ⊆ J.carrier) :
    idealSet.{u} I ⊆ idealSet J := by
  intro x hx
  obtain ⟨a,ha,rfl⟩ := (mem_idealSet I x).mp hx
  exact (mem_idealSet J _).mpr ⟨a,h ha,rfl⟩

end
end TuringRigidity.SetModelSatisfaction

end OAI
