/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/RequestProject/TuringConeIdealBackCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeIdealCoding
public import LeanPool.TuringConeRigidity.TuringConeRelativeAntichain

/-!
# Pulling cone codes back to an ordinary degree ideal

A lower bound on every parameter is part of the input: an arbitrary ambient
code is not automatically a code in the cone. The pullback uses only the
existing forward transport equivalence, after reconstructing its preimage.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeIdealBackCoding

open IdealInterpretation SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding
open ConeRelativeCoding

noncomputable section
variable {I : DegreeIdeal} {a : I}

def targetElement (b : Set.Ici a) (x : Degree) (hlo : a.val ≤ x) (hhi : x ≤ b.val.val) : Set.Ici a
  :=
  ⟨⟨x, I.lower hhi b.val.property⟩, Set.mem_Ici.mpr hlo⟩

def backElement (ρ : I ≃o Set.Ici a) (b : Set.Ici a)
    (x : Degree) (hlo : a.val ≤ x) (hhi : x ≤ b.val.val) : I :=
  ρ.symm (targetElement b x hlo hhi)

@[simp] theorem image_backElement (ρ : I ≃o Set.Ici a) (b : Set.Ici a)
    (x : Degree) (hlo : a.val ≤ x) (hhi : x ≤ b.val.val) :
    ConeIdealCoding.image ρ (backElement ρ b x hlo hhi) = x :=
  congrArg (fun z : Set.Ici a => z.val.val) (ρ.apply_symm_apply _)

theorem backElement_le (ρ : I ≃o Set.Ici a) (b : Set.Ici a)
    (x : Degree) (hlo : a.val ≤ x) (hhi : x ≤ b.val.val) :
    (backElement ρ b x hlo hhi).val ≤ (ρ.symm b).val :=
  show ρ.symm (targetElement b x hlo hhi) ≤ ρ.symm b from ρ.symm.monotone hhi

def backAntichain (ρ : I ≃o Set.Ici a) (b : Set.Ici a) (p : AntichainCode)
    (ha : AntichainAbove p a.val) (hb : AntichainBelow p b.val.val) : ACode I :=
  ⟨backElement ρ b p.bound ha.1 hb.1, backElement ρ b p.left ha.2.1 hb.2.1,
    backElement ρ b p.right ha.2.2 hb.2.2⟩

@[simp] theorem map_backAntichain (ρ : I ≃o Set.Ici a) (b : Set.Ici a) (p : AntichainCode)
    (ha : AntichainAbove p a.val) (hb : AntichainBelow p b.val.val) :
    ConeIdealCoding.mapAntichain ρ (backAntichain ρ b p ha hb) = p := by
  simp only [ConeIdealCoding.mapAntichain, backAntichain, image_backElement]

theorem backAntichain_below (ρ : I ≃o Set.Ici a) (b : Set.Ici a) (p : AntichainCode)
    (ha : AntichainAbove p a.val) (hb : AntichainBelow p b.val.val) :
    AntichainBelow (backAntichain ρ b p ha hb).external (ρ.symm b).val :=
  ⟨backElement_le ρ b p.bound ha.1 hb.1, backElement_le ρ b p.left ha.2.1 hb.2.1,
    backElement_le ρ b p.right ha.2.2 hb.2.2⟩

def backSet (ρ : I ≃o Set.Ici a) (b : Set.Ici a) (p : SetCode)
    (ha : SetAbove p a.val) (hb : SetBelow p b.val.val) : SCode I :=
  ⟨backElement ρ b p.bound ha.1 hb.1,
    backAntichain ρ b p.tags ha.2.1 hb.2.1, backAntichain ρ b p.decorated ha.2.2 hb.2.2⟩

@[simp] theorem map_backSet (ρ : I ≃o Set.Ici a) (b : Set.Ici a) (p : SetCode)
    (ha : SetAbove p a.val) (hb : SetBelow p b.val.val) :
    ConeIdealCoding.mapSet ρ (backSet ρ b p ha hb) = p := by
  simp only [ConeIdealCoding.mapSet, backSet, image_backElement, map_backAntichain]

theorem backSet_below (ρ : I ≃o Set.Ici a) (b : Set.Ici a) (p : SetCode)
    (ha : SetAbove p a.val) (hb : SetBelow p b.val.val) :
    SetBelow (backSet ρ b p ha hb).external (ρ.symm b).val :=
  ⟨backElement_le ρ b p.bound ha.1 hb.1,
    backAntichain_below ρ b p.tags ha.2.1 hb.2.1,
    backAntichain_below ρ b p.decorated ha.2.2 hb.2.2⟩

def backRelation (ρ : I ≃o Set.Ici a) (b : Set.Ici a) {n : ℕ} (p : RelationCode n)
    (ha : RelationAbove p a.val) (hb : RelationBelow p b.val.val) : RCode I n :=
  ⟨fun i => backSet ρ b (p.coordinates i) (ha.1 i) (hb.1 i),
    backAntichain ρ b p.tuples ha.2 hb.2⟩

@[simp] theorem map_backRelation (ρ : I ≃o Set.Ici a) (b : Set.Ici a) {n : ℕ}
    (p : RelationCode n) (ha : RelationAbove p a.val) (hb : RelationBelow p b.val.val) :
    ConeIdealCoding.mapRelation ρ (backRelation ρ b p ha hb) = p := by
  simp only [ConeIdealCoding.mapRelation, backRelation, map_backSet, map_backAntichain]

theorem backRelation_below (ρ : I ≃o Set.Ici a) (b : Set.Ici a) {n : ℕ}
    (p : RelationCode n) (ha : RelationAbove p a.val) (hb : RelationBelow p b.val.val) :
    RelationBelow (backRelation ρ b p ha hb).external (ρ.symm b).val :=
  ⟨fun i => backSet_below ρ b (p.coordinates i) (ha.1 i) (hb.1 i),
    backAntichain_below ρ b p.tuples ha.2 hb.2⟩

theorem map_relation_one (ρ : I ≃o Set.Ici a) (p : RCode I 1) (x : I) :
    ConeCoding.Holds a.val (ConeIdealCoding.mapRelation ρ p) (one (ConeIdealCoding.image ρ x)) ↔
      p.external.Holds (one x.val) := by
  have h₁ : (fun _ : Fin 1 => ConeIdealCoding.image ρ x) = one (ConeIdealCoding.image ρ x) := by
    funext i; fin_cases i; rfl
  have h₂ : (fun _ : Fin 1 => x.val) = one x.val := by
    funext i; fin_cases i; rfl
  simpa only [h₁, h₂] using ConeIdealCoding.map_relation_holds ρ p (fun _ => x)

/-- Backward transport of a bounded unary copy, preserving its actual predicate. -/
theorem transport_copy {U : ℕ → Prop} (ρ : I ≃o Set.Ici a)
    (c : ConeCoding.Copy a.val U) (b : Set.Ici a)
    (haS : RelationAbove c.successor a.val) (haP : RelationAbove c.predicate a.val)
    (hS : RelationBelow c.successor b.val.val) (hP : RelationBelow c.predicate b.val.val) :
    ∃ d : ArithmeticModelDecoding.Copy U,
      RelationBelow d.successor (ρ.symm b).val ∧ RelationBelow d.predicate (ρ.symm b).val := by
  let S := backRelation ρ b c.successor haS hS
  let P := backRelation ρ b c.predicate haP hP
  have hn (n : ℕ) : (c.node n).val ∈ I.carrier := by
    obtain ⟨tags, ht, _⟩ := (c.successor_spec (c.node n) (c.node (n + 1))).mpr ⟨n, rfl, rfl⟩
    exact I.lower ((ht 0).2.1.trans (hS.1 0).1) b.val.property
  let node (n : ℕ) : Set.Ici a :=
    ⟨⟨(c.node n).val, hn n⟩, (c.node n).property⟩
  let up (x : I) : Set.Ici a.val :=
    ⟨ConeIdealCoding.image ρ x, Set.mem_Ici.mpr (ConeIdealCoding.base_le_image ρ x)⟩
  have hup (x : I) (k : ℕ) : up x = c.node k ↔ x = ρ.symm (node k) := by
    constructor
    · intro h
      have hh : ρ x = node k := Subtype.ext (Element.ext _ _ (congrArg Subtype.val h))
      exact (ρ.symm_apply_apply x).symm.trans (congrArg ρ.symm hh)
    · intro h
      subst x
      apply Subtype.ext
      exact congrArg (fun z : Set.Ici a => z.val.val) (ρ.apply_symm_apply (node k))
  have hi : Function.Injective (fun n => (ρ.symm (node n)).val) := by
    intro i j h
    have he : node i = node j := ρ.symm.injective (Element.ext _ _ h)
    exact c.injective (Subtype.ext (congrArg (fun z : Set.Ici a => z.val.val) he))
  have hs (x y : I) : S.external.Holds (two x.val y.val) ↔
      ∃ k, x = ρ.symm (node k) ∧ y = ρ.symm (node (k + 1)) := by
    have hh := ConeIdealCoding.map_relation_two ρ S x y
    simp only [S, map_backRelation] at hh
    rw [← hh]
    change ConeCoding.Holds a.val c.successor (two (up x).val (up y).val) ↔ _
    rw [c.successor_spec]
    exact exists_congr (fun k => and_congr (hup x k) (hup y (k + 1)))
  have hp (x : I) : P.external.Holds (one x.val) ↔
      ∃ k, U k ∧ x = ρ.symm (node k) := by
    have hh := map_relation_one ρ P x
    simp only [P, map_backRelation] at hh
    rw [← hh]
    change ConeCoding.Holds a.val c.predicate (one (up x).val) ↔ _
    rw [c.predicate_spec]
    exact exists_congr (fun k => and_congr_right (fun _ => hup x k))
  have hs' (x y : Degree) : S.external.Holds (two x y) ↔
      ∃ k, x = (ρ.symm (node k)).val ∧ y = (ρ.symm (node (k + 1))).val := by
    constructor
    · intro h
      obtain ⟨k, hk, hl⟩ := (hs ⟨x, S.coordinates_mem h 0⟩ ⟨y, S.coordinates_mem h 1⟩).mp h
      exact ⟨k, congrArg Element.val hk, congrArg Element.val hl⟩
    · rintro ⟨k, rfl, rfl⟩
      exact (hs _ _).mpr ⟨k, rfl, rfl⟩
  have hp' (x : Degree) : P.external.Holds (one x) ↔
      ∃ k, U k ∧ x = (ρ.symm (node k)).val := by
    constructor
    · intro h
      obtain ⟨k, hk, he⟩ := (hp ⟨x, P.coordinates_mem h 0⟩).mp h
      exact ⟨k, hk, congrArg Element.val he⟩
    · rintro ⟨k, hk, rfl⟩
      exact (hp _).mpr ⟨k, hk, rfl⟩
  let d : ArithmeticModelDecoding.Copy U :=
    ⟨fun k => (ρ.symm (node k)).val, hi, S.external, P.external, hs', hp'⟩
  exact ⟨d, backRelation_below ρ b c.successor haS hS,
    backRelation_below ρ b c.predicate haP hP⟩

end
end OAI.TuringRigidity.ConeIdealBackCoding
