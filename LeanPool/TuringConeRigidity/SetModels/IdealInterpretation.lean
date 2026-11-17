/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/IdealInterpretation.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Syntax.BoundedDecoding

/-!
# Ideal Interpretation
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.IdealInterpretation
open AntichainParameters SetCoding RelationCoding

structure DegreeIdeal where
  carrier : Set Degree
  nonempty : carrier.Nonempty
  lower : ∀ {x y}, x ≤ y → y ∈ carrier → x ∈ carrier
  join_mem : ∀ {x y}, x ∈ carrier → y ∈ carrier → x ⊔ y ∈ carrier

structure Element (I : DegreeIdeal) where
  val : Degree
  property : val ∈ I.carrier

instance : CoeSort DegreeIdeal Type := ⟨Element⟩

@[ext] theorem Element.ext {I : DegreeIdeal} (x y : I) (h : x.val = y.val) : x = y := by
  cases x; cases y; cases h; rfl

instance (I : DegreeIdeal) : PartialOrder I :=
  PartialOrder.lift Element.val (fun x y h => Element.ext x y h)

instance (I : DegreeIdeal) : SemilatticeSup (Element I) where
  toPartialOrder := inferInstance
  sup x y := ⟨x.val ⊔ y.val,I.join_mem x.property y.property⟩
  le_sup_left := by
    intro x y
    change x.val ≤ x.val ⊔ y.val
    exact le_sup_left
  le_sup_right := by
    intro x y
    change y.val ≤ x.val ⊔ y.val
    exact le_sup_right
  sup_le := by
    intro x y z hx hy
    change x.val ⊔ y.val ≤ z.val
    exact sup_le hx hy

instance (I : DegreeIdeal) : OrderBot (Element I) where
  bot := ⟨⊥,by obtain ⟨x,hx⟩ := I.nonempty; exact I.lower bot_le hx⟩
  bot_le := by
    intro x
    change (⊥ : Degree) ≤ x.val
    exact bot_le

@[simp] theorem coe_sup {I : DegreeIdeal} (x y : I) : (x ⊔ y).val = x.val ⊔ y.val := rfl
@[simp] theorem coe_bot (I : DegreeIdeal) : (⊥ : I).val = (⊥ : Degree) := rfl

theorem coe_finset_sup {I : DegreeIdeal} {α : Type*} (F : Finset α) (f : α → I) :
    (F.sup f).val = F.sup (fun a => (f a).val) := by
  classical
  induction F using Finset.induction_on with
  | empty => rfl
  | @insert a F ha ih => simp only [Finset.sup_insert,coe_sup,ih]

section Formula
variable {α β : Type*} [SemilatticeSup α] [SemilatticeSup β]

def nontrivial (b g₀ g₁ x : α) : Prop :=
  x ≤ b ∧ ∃ z, z ≤ g₀ ⊔ x ∧ z ≤ g₁ ⊔ x ∧ ¬ z ≤ x

def antichain (b g₀ g₁ x : α) : Prop :=
  nontrivial b g₀ g₁ x ∧ ∀ y, nontrivial b g₀ g₁ y → y ≤ x → x ≤ y

theorem map_nontrivial (ρ : α ≃o β) (b g₀ g₁ x : α) :
    nontrivial (ρ b) (ρ g₀) (ρ g₁) (ρ x) ↔ nontrivial b g₀ g₁ x := by
  unfold nontrivial
  simp only [← ρ.map_sup,ρ.le_iff_le]
  constructor
  · rintro ⟨hx,z,h₀,h₁,hn⟩
    obtain ⟨w,rfl⟩ := ρ.surjective z
    exact ⟨hx,w,(ρ.le_iff_le).mp h₀,(ρ.le_iff_le).mp h₁,fun h => hn ((ρ.le_iff_le).mpr h)⟩
  · rintro ⟨hx,z,h₀,h₁,hn⟩
    exact ⟨hx,ρ z,(ρ.le_iff_le).mpr h₀,(ρ.le_iff_le).mpr h₁,fun h => hn ((ρ.le_iff_le).mp h)⟩

theorem map_antichain (ρ : α ≃o β) (b g₀ g₁ x : α) :
    antichain (ρ b) (ρ g₀) (ρ g₁) (ρ x) ↔ antichain b g₀ g₁ x := by
  unfold antichain
  rw [map_nontrivial]
  constructor
  · rintro ⟨hx,hm⟩
    refine ⟨hx,fun y hy hyx => ?_⟩
    exact ρ.le_iff_le.mp (hm (ρ y) ((map_nontrivial ρ _ _ _ _).mpr hy) (ρ.le_iff_le.mpr hyx))
  · rintro ⟨hx,hm⟩
    refine ⟨hx,fun y hy hyx => ?_⟩
    obtain ⟨z,rfl⟩ := ρ.surjective y
    exact ρ.le_iff_le.mpr (hm z ((map_nontrivial ρ _ _ _ _).mp hy) (ρ.le_iff_le.mp hyx))
end Formula

theorem ideal_nontrivial (I : DegreeIdeal) (b g₀ g₁ x : I) :
    nontrivial b g₀ g₁ x ↔ NontrivialCommonLower b.val g₀.val g₁.val x.val := by
  constructor
  · rintro ⟨hx,z,h₀,h₁,hn⟩
    exact ⟨hx,z.val,h₀,h₁,hn⟩
  · rintro ⟨hx,z,h₀,h₁,hn⟩
    exact ⟨hx,⟨z,I.lower h₀ (I.join_mem g₀.property x.property)⟩,h₀,h₁,hn⟩

theorem ideal_antichain (I : DegreeIdeal) (b g₀ g₁ x : I) :
    antichain b g₀ g₁ x ↔ CodedAntichain b.val g₀.val g₁.val x.val := by
  constructor
  · rintro ⟨hx,hm⟩
    refine ⟨(ideal_nontrivial I _ _ _ _).mp hx,fun y hy hyx => ?_⟩
    let y' : I := ⟨y,I.lower hy.1 b.property⟩
    exact hm y' ((ideal_nontrivial I _ _ _ _).mpr hy) hyx
  · rintro ⟨hx,hm⟩
    exact ⟨(ideal_nontrivial I _ _ _ _).mpr hx,fun y hy hyx =>
      hm y.val ((ideal_nontrivial I _ _ _ _).mp hy) hyx⟩

theorem transport_antichain {I J : DegreeIdeal} (ρ : I ≃o J) (b g₀ g₁ x : I) :
    CodedAntichain (ρ b).val (ρ g₀).val (ρ g₁).val (ρ x).val ↔
      CodedAntichain b.val g₀.val g₁.val x.val := by
  rw [← ideal_antichain,← ideal_antichain,map_antichain]

structure ACode (I : DegreeIdeal) where
  bound : I
  left : I
  right : I

def ACode.external {I : DegreeIdeal} (p : ACode I) : AntichainCode :=
  ⟨p.bound.val,p.left.val,p.right.val⟩
def ACode.map {I J : DegreeIdeal} (ρ : I ≃o J) (p : ACode I) : ACode J := ⟨ρ p.bound,ρ p.left,ρ
  p.right⟩

theorem ACode.transport {I J : DegreeIdeal} (ρ : I ≃o J) (p : ACode I) (x : I) :
    (p.map ρ).external.Holds (ρ x).val ↔ p.external.Holds x.val :=
  transport_antichain ρ _ _ _ _

structure SCode (I : DegreeIdeal) where
  bound : I
  tags : ACode I
  decorated : ACode I

def SCode.external {I : DegreeIdeal} (p : SCode I) : SetCode :=
  ⟨p.bound.val,p.tags.external,p.decorated.external⟩
def SCode.map {I J : DegreeIdeal} (ρ : I ≃o J) (p : SCode I) : SCode J :=
  ⟨ρ p.bound,p.tags.map ρ,p.decorated.map ρ⟩

theorem SCode.transport {I J : DegreeIdeal} (ρ : I ≃o J) (p : SCode I) (x c : I) :
    (p.map ρ).external.Graph (ρ x).val (ρ c).val ↔ p.external.Graph x.val c.val := by
  change ((ρ x).val ≤ (ρ p.bound).val ∧ (p.tags.map ρ).external.Holds (ρ c).val ∧
    (p.decorated.map ρ).external.Holds ((ρ x).val ⊔ (ρ c).val)) ↔ _
  rw [← coe_sup,← ρ.map_sup,p.tags.transport ρ c,p.decorated.transport ρ (x ⊔ c)]
  exact and_congr ρ.le_iff_le Iff.rfl

structure RCode (I : DegreeIdeal) (n : ℕ) where
  coordinates : Fin n → SCode I
  tuples : ACode I

def RCode.external {I : DegreeIdeal} {n : ℕ} (p : RCode I n) : RelationCode n :=
  ⟨fun i => (p.coordinates i).external,p.tuples.external⟩
def RCode.map {I J : DegreeIdeal} {n : ℕ} (ρ : I ≃o J) (p : RCode I n) : RCode J n :=
  ⟨fun i => (p.coordinates i).map ρ,p.tuples.map ρ⟩

theorem RCode.internal {I : DegreeIdeal} {n : ℕ} (p : RCode I n) (v : Fin n → I) :
    p.external.Holds (fun i => (v i).val) ↔
      ∃ c : Fin n → I, (∀ i, (p.coordinates i).external.Graph (v i).val (c i).val) ∧
        p.tuples.external.Holds (Finset.univ.sup c).val := by
  constructor
  · rintro ⟨c,hc,ht⟩
    have hm : ∀ i, c i ∈ I.carrier := fun i =>
      I.lower (hc i).2.1.1.1 (p.coordinates i).tags.bound.property
    refine ⟨fun i => ⟨c i,hm i⟩,hc,?_⟩
    simpa only [coe_finset_sup,RCode.external] using ht
  · rintro ⟨c,hc,ht⟩
    exact ⟨fun i => (c i).val,hc,by simpa only [coe_finset_sup,RCode.external] using ht⟩

private theorem map_sup_finset {I J : DegreeIdeal} (ρ : I ≃o J) {α : Type*}
    (F : Finset α) (f : α → I) : ρ (F.sup f) = F.sup (fun a => ρ (f a)) := by
  classical
  induction F using Finset.induction_on with
  | empty => exact ρ.map_bot
  | @insert a F ha ih => simp only [Finset.sup_insert,ρ.map_sup,ih]

theorem RCode.transport {I J : DegreeIdeal} {n : ℕ} (ρ : I ≃o J) (p : RCode I n) (v : Fin n → I) :
    (p.map ρ).external.Holds (fun i => (ρ (v i)).val) ↔ p.external.Holds (fun i => (v i).val) := by
  classical
  rw [(p.map ρ).internal,p.internal]
  constructor
  · rintro ⟨c,hc,ht⟩
    let d := fun i => ρ.symm (c i)
    have hd : ∀ i, ρ (d i) = c i := fun i => ρ.apply_symm_apply _
    refine ⟨d,fun i => ?_,?_⟩
    · exact ((p.coordinates i).transport ρ (v i) (d i)).mp (by simpa only [hd,RCode.map] using hc i)
    · apply (p.tuples.transport ρ (Finset.univ.sup d)).mp
      have he : ρ (Finset.univ.sup d) = Finset.univ.sup c := by
        rw [map_sup_finset]
        simp only [hd]
      simpa only [he,RCode.map] using ht
  · rintro ⟨c,hc,ht⟩
    refine ⟨fun i => ρ (c i),fun i => ((p.coordinates i).transport ρ (v i) (c i)).mpr (hc i),?_⟩
    have hh := (p.tuples.transport ρ (Finset.univ.sup c)).mpr ht
    simpa only [map_sup_finset,RCode.map] using hh

end TuringRigidity.IdealInterpretation

end OAI
