/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringTwoConeIdealCodes.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeIdealCoding
public import LeanPool.TuringConeRigidity.TuringConeRelativeAntichain

/-!
# Bounded relation codes in two ideal cones

Both source and target are principal cones inside ordinary degree ideals.
The ideals need not be equal. Quantifiers are compared with their ambient
cone interpretation using downward closure, and finite joins retain the
appropriate base even at arity zero. No regularity or persistence is assumed.
-/


@[expose] public section

namespace OAI.TuringRigidity.TwoConeIdealCodes

open IdealInterpretation SetCoding RelationCoding BoundedDecoding ConeRelativeCoding
open ArithmeticModelDecoding

abbrev val {I : DegreeIdeal} {a : I} (x : Set.Ici a) : Degree := x.val.val

theorem base_le {I : DegreeIdeal} {a : I} (x : Set.Ici a) : a.val ≤ val x :=
  Set.mem_Ici.mp x.property

def ambient {I : DegreeIdeal} {a : I} (x : Set.Ici a) : Set.Ici a.val :=
  ⟨val x, Set.mem_Ici.mpr (base_le x)⟩

theorem ambient_injective {I : DegreeIdeal} {a : I} :
    Function.Injective (@ambient I a) := by
  intro x y h
  exact Subtype.ext (Element.ext _ _ (congrArg Subtype.val h))

@[simp] theorem val_sup {I : DegreeIdeal} {a : I} (x y : Set.Ici a) :
    val (x ⊔ y) = val x ⊔ val y := rfl

@[simp] theorem val_bot {I : DegreeIdeal} (a : I) :
    val (⊥ : Set.Ici a) = a.val := rfl

theorem val_finset_sup {I : DegreeIdeal} {a : I} {ι : Type*}
    (s : Finset ι) (f : ι → Set.Ici a) :
    val (s.sup f) = a.val ⊔ s.sup (fun i => val (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sup_empty, val_bot, sup_bot_eq]
  | @insert i s hi ih =>
    rw [Finset.sup_insert, val_sup, ih, Finset.sup_insert]
    exact sup_left_comm _ _ _

theorem map_finset_sup {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) {ι : Type*} (s : Finset ι) (f : ι → Set.Ici a) :
    ρ (s.sup f) = s.sup (fun i => ρ (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ρ.map_bot
  | @insert i s hi ih => simp only [Finset.sup_insert, ρ.map_sup, ih]

structure ACode {I : DegreeIdeal} (a : I) where
  bound : Set.Ici a
  left : Set.Ici a
  right : Set.Ici a

def ACode.external {I : DegreeIdeal} {a : I} (p : ACode a) : AntichainCode :=
  ⟨val p.bound, val p.left, val p.right⟩

def ACode.map {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (p : ACode a) : ACode b :=
  ⟨ρ p.bound, ρ p.left, ρ p.right⟩

theorem ACode.above {I : DegreeIdeal} {a : I} (p : ACode a) :
    AntichainAbove p.external a.val := ⟨base_le _, base_le _, base_le _⟩

theorem ACode.transport {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (p : ACode a) (x : Set.Ici a) :
    ConeCoding.Antichain b.val (p.map ρ).external (val (ρ x)) ↔
      ConeCoding.Antichain a.val p.external (val x) :=
  (ConeIdealCoding.antichain_target (ρ p.bound) (ρ p.left) (ρ p.right) (ρ x)).symm.trans
    ((IdealInterpretation.map_antichain ρ _ _ _ _).trans
      (ConeIdealCoding.antichain_target p.bound p.left p.right x))

theorem ACode.map_below {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (p : ACode a) (z : Set.Ici a)
    (hp : AntichainBelow p.external (val z)) :
    AntichainBelow (p.map ρ).external (val (ρ z)) :=
  ⟨ρ.monotone hp.1, ρ.monotone hp.2.1, ρ.monotone hp.2.2⟩

structure SCode {I : DegreeIdeal} (a : I) where
  bound : Set.Ici a
  tags : ACode a
  decorated : ACode a

def SCode.external {I : DegreeIdeal} {a : I} (p : SCode a) : SetCode :=
  ⟨val p.bound, p.tags.external, p.decorated.external⟩

def SCode.map {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (p : SCode a) : SCode b :=
  ⟨ρ p.bound, p.tags.map ρ, p.decorated.map ρ⟩

theorem SCode.above {I : DegreeIdeal} {a : I} (p : SCode a) :
    SetAbove p.external a.val := ⟨base_le _, p.tags.above, p.decorated.above⟩

theorem SCode.transport {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (p : SCode a) (x c : Set.Ici a) :
    ConeCoding.Graph b.val (p.map ρ).external (val (ρ x)) (val (ρ c)) ↔
      ConeCoding.Graph a.val p.external (val x) (val c) := by
  change (b.val ≤ val (ρ x) ∧ val (ρ x) ≤ val (ρ p.bound) ∧
    ConeCoding.Antichain b.val (p.tags.map ρ).external (val (ρ c)) ∧
    ConeCoding.Antichain b.val (p.decorated.map ρ).external
      (val (ρ x) ⊔ val (ρ c))) ↔
    (a.val ≤ val x ∧ val x ≤ val p.bound ∧
    ConeCoding.Antichain a.val p.tags.external (val c) ∧
    ConeCoding.Antichain a.val p.decorated.external (val x ⊔ val c))
  rw [← val_sup, ← ρ.map_sup, p.tags.transport, p.decorated.transport]
  have hle : val (ρ x) ≤ val (ρ p.bound) ↔ val x ≤ val p.bound := ρ.le_iff_le
  simp only [base_le, true_and, hle, val_sup]

theorem SCode.map_below {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (p : SCode a) (z : Set.Ici a)
    (hp : SetBelow p.external (val z)) : SetBelow (p.map ρ).external (val (ρ z)) :=
  ⟨ρ.monotone hp.1, p.tags.map_below ρ z hp.2.1, p.decorated.map_below ρ z hp.2.2⟩

structure RCode {I : DegreeIdeal} (a : I) (n : ℕ) where
  coordinates : Fin n → SCode a
  tuples : ACode a

def RCode.external {I : DegreeIdeal} {a : I} {n : ℕ} (p : RCode a n) : RelationCode n :=
  ⟨fun i => (p.coordinates i).external, p.tuples.external⟩

def RCode.map {I J : DegreeIdeal} {a : I} {b : J} {n : ℕ}
    (ρ : Set.Ici a ≃o Set.Ici b) (p : RCode a n) : RCode b n :=
  ⟨fun i => (p.coordinates i).map ρ, p.tuples.map ρ⟩

theorem RCode.above {I : DegreeIdeal} {a : I} {n : ℕ} (p : RCode a n) :
    RelationAbove p.external a.val := ⟨fun i => (p.coordinates i).above, p.tuples.above⟩

theorem RCode.coordinates_mem {I : DegreeIdeal} {a : I} {n : ℕ}
    (p : RCode a n) {v : Fin n → Degree} (h : ConeCoding.Holds a.val p.external v)
    (i : Fin n) : v i ∈ I.carrier := by
  obtain ⟨c, hc, _⟩ := h
  exact I.lower (hc i).2.1 (p.coordinates i).bound.val.property

theorem RCode.internal {I : DegreeIdeal} {a : I} {n : ℕ}
    (p : RCode a n) (v : Fin n → Set.Ici a) :
    ConeCoding.Holds a.val p.external (fun i => val (v i)) ↔
      ∃ c : Fin n → Set.Ici a,
        (∀ i, ConeCoding.Graph a.val (p.coordinates i).external (val (v i)) (val (c i))) ∧
        ConeCoding.Antichain a.val p.tuples.external (val (Finset.univ.sup c)) := by
  constructor
  · rintro ⟨c, hc, ht⟩
    have hm (i : Fin n) : c i ∈ I.carrier :=
      I.lower (hc i).2.2.1.2.1.1 (p.coordinates i).tags.bound.val.property
    let d : Fin n → Set.Ici a := fun i =>
      ⟨⟨c i, hm i⟩, Set.mem_Ici.mpr (hc i).2.2.1.1⟩
    refine ⟨d, hc, ?_⟩
    simpa only [val_finset_sup, d, RCode.external] using ht
  · rintro ⟨c, hc, ht⟩
    refine ⟨fun i => val (c i), hc, ?_⟩
    simpa only [val_finset_sup, RCode.external] using ht

theorem RCode.transport {I J : DegreeIdeal} {a : I} {b : J} {n : ℕ}
    (ρ : Set.Ici a ≃o Set.Ici b) (p : RCode a n) (v : Fin n → Set.Ici a) :
    ConeCoding.Holds b.val (p.map ρ).external (fun i => val (ρ (v i))) ↔
      ConeCoding.Holds a.val p.external (fun i => val (v i)) := by
  rw [(p.map ρ).internal, p.internal]
  constructor
  · rintro ⟨c, hc, ht⟩
    let d := fun i => ρ.symm (c i)
    have hd (i) : ρ (d i) = c i := ρ.apply_symm_apply _
    refine ⟨d, fun i => ?_, ?_⟩
    · exact ((p.coordinates i).transport ρ (v i) (d i)).mp
        (by simpa only [hd, RCode.map] using hc i)
    · apply (p.tuples.transport ρ (Finset.univ.sup d)).mp
      simpa only [map_finset_sup, hd, RCode.map] using ht
  · rintro ⟨c, hc, ht⟩
    refine ⟨fun i => ρ (c i), fun i => ((p.coordinates i).transport ρ _ _).mpr (hc i), ?_⟩
    have hh := (p.tuples.transport ρ (Finset.univ.sup c)).mpr ht
    simpa only [map_finset_sup, RCode.map] using hh

theorem RCode.transport_one {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (p : RCode a 1) (x : Set.Ici a) :
    ConeCoding.Holds b.val (p.map ρ).external (one (val (ρ x))) ↔
      ConeCoding.Holds a.val p.external (one (val x)) := by
  have h₁ : (fun _ : Fin 1 => val (ρ x)) = one (val (ρ x)) := by funext i; fin_cases i; rfl
  have h₂ : (fun _ : Fin 1 => val x) = one (val x) := by funext i; fin_cases i; rfl
  simpa only [h₁, h₂] using p.transport ρ (fun _ => x)

theorem RCode.transport_two {I J : DegreeIdeal} {a : I} {b : J}
    (ρ : Set.Ici a ≃o Set.Ici b) (p : RCode a 2) (x y : Set.Ici a) :
    ConeCoding.Holds b.val (p.map ρ).external (two (val (ρ x)) (val (ρ y))) ↔
      ConeCoding.Holds a.val p.external (two (val x) (val y)) := by
  have h₁ : (fun i : Fin 2 => val (ρ (![x, y] i))) = two (val (ρ x)) (val (ρ y)) := by
    funext i; fin_cases i <;> rfl
  have h₂ : (fun i : Fin 2 => val (![x, y] i)) = two (val x) (val y) := by
    funext i; fin_cases i <;> rfl
  simpa only [h₁, h₂] using p.transport ρ ![x, y]

theorem RCode.map_below {I J : DegreeIdeal} {a : I} {b : J} {n : ℕ}
    (ρ : Set.Ici a ≃o Set.Ici b) (p : RCode a n) (z : Set.Ici a)
    (hp : RelationBelow p.external (val z)) :
    RelationBelow (p.map ρ).external (val (ρ z)) :=
  ⟨fun i => (p.coordinates i).map_below ρ z (hp.1 i), p.tuples.map_below ρ z hp.2⟩

end OAI.TuringRigidity.TwoConeIdealCodes
