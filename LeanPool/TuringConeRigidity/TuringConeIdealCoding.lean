/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeIdealCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeCoding

/-!
# Bounded coding for partial cone isomorphisms

The source is a downward-closed degree ideal `I`; the target is its part above
`a : I`. Neither is assumed to be the full degree structure. Coding predicates
are compared with their ambient interpretations using their parameter bounds.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeIdealCoding

open IdealInterpretation SetCoding RelationCoding BoundedDecoding ArithmeticModelDecoding

variable {I : DegreeIdeal} {a : I}

/-- The underlying degree of an ideal element's image in the principal cone. -/
def image (ρ : I ≃o Set.Ici a) (x : I) : Degree := (ρ x).val.val

theorem base_le_image (ρ : I ≃o Set.Ici a) (x : I) : a.val ≤ image ρ x :=
  Set.mem_Ici.mp (ρ x).property

theorem image_le_iff (ρ : I ≃o Set.Ici a) (x y : I) :
    image ρ x ≤ image ρ y ↔ x ≤ y := ρ.le_iff_le

theorem image_sup (ρ : I ≃o Set.Ici a) (x y : I) :
    image ρ (x ⊔ y) = image ρ x ⊔ image ρ y :=
  congrArg (fun z : Set.Ici a => z.val.val) (ρ.map_sup x y)

theorem image_bot (ρ : I ≃o Set.Ici a) : image ρ ⊥ = a.val :=
  congrArg (fun z : Set.Ici a => z.val.val) ρ.map_bot

theorem image_finset_sup (ρ : I ≃o Set.Ici a) {ι : Type*}
    (s : Finset ι) (f : ι → I) :
    image ρ (s.sup f) = a.val ⊔ s.sup (fun i => image ρ (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty, sup_bot_eq] using image_bot ρ
  | @insert i s hi ih =>
    rw [Finset.sup_insert, image_sup, ih, Finset.sup_insert]
    exact sup_left_comm _ _ _

theorem nontrivial_target (b g₀ g₁ x : Set.Ici a) :
    nontrivial b g₀ g₁ x ↔ AntichainParameters.NontrivialCommonLower
      b.val.val g₀.val.val g₁.val.val x.val.val := by
  constructor
  · rintro ⟨hx, z, h₀, h₁, hn⟩
    exact ⟨hx, z.val.val, h₀, h₁, hn⟩
  · rintro ⟨hx, z, h₀, h₁, hn⟩
    have hax : a.val ≤ x.val.val := Set.mem_Ici.mp x.property
    have h₀' : a.val ⊔ z ≤ g₀.val.val ⊔ x.val.val :=
      sup_le (hax.trans le_sup_right) h₀
    have h₁' : a.val ⊔ z ≤ g₁.val.val ⊔ x.val.val :=
      sup_le (hax.trans le_sup_right) h₁
    let w : I := ⟨a.val ⊔ z, I.lower h₀' (I.join_mem g₀.val.property x.val.property)⟩
    have haw : a ≤ w := by
      change a.val ≤ a.val ⊔ z
      exact le_sup_left
    exact ⟨hx, ⟨w, Set.mem_Ici.mpr haw⟩, h₀', h₁',
      fun h => hn (le_sup_right.trans h)⟩

theorem antichain_target (b g₀ g₁ x : Set.Ici a) :
    antichain b g₀ g₁ x ↔ ConeCoding.Antichain a.val
      ⟨b.val.val, g₀.val.val, g₁.val.val⟩ x.val.val := by
  constructor
  · rintro ⟨hx, hm⟩
    refine ⟨Set.mem_Ici.mp x.property, (nontrivial_target _ _ _ _).mp hx, ?_⟩
    intro y hay hy hyx
    let y' : Set.Ici a := ⟨⟨y, I.lower hy.1 b.val.property⟩, Set.mem_Ici.mpr hay⟩
    exact hm y' ((nontrivial_target _ _ _ _).mpr hy) hyx
  · rintro ⟨_, hx, hm⟩
    exact ⟨(nontrivial_target _ _ _ _).mpr hx, fun y hy hyx =>
      hm y.val.val (Set.mem_Ici.mp y.property)
        ((nontrivial_target _ _ _ _).mp hy) hyx⟩

/-- Transport an ideal-internal antichain code through the cone isomorphism. -/
def mapAntichain (ρ : I ≃o Set.Ici a) (p : ACode I) : AntichainCode :=
  ⟨image ρ p.bound, image ρ p.left, image ρ p.right⟩

theorem map_antichain_holds (ρ : I ≃o Set.Ici a) (p : ACode I) (x : I) :
    ConeCoding.Antichain a.val (mapAntichain ρ p) (image ρ x) ↔ p.external.Holds x.val := by
  exact (antichain_target (ρ p.bound) (ρ p.left) (ρ p.right) (ρ x)).symm.trans
    ((IdealInterpretation.map_antichain ρ _ _ _ _).trans (ideal_antichain I _ _ _ _))

/-- Transport an ideal-internal set code through the cone isomorphism. -/
def mapSet (ρ : I ≃o Set.Ici a) (p : SCode I) : SetCode :=
  ⟨image ρ p.bound, mapAntichain ρ p.tags, mapAntichain ρ p.decorated⟩

theorem map_graph (ρ : I ≃o Set.Ici a) (p : SCode I) (x c : I) :
    ConeCoding.Graph a.val (mapSet ρ p) (image ρ x) (image ρ c) ↔
      p.external.Graph x.val c.val := by
  change (a.val ≤ image ρ x ∧ image ρ x ≤ image ρ p.bound ∧
    ConeCoding.Antichain a.val (mapAntichain ρ p.tags) (image ρ c) ∧
    ConeCoding.Antichain a.val (mapAntichain ρ p.decorated) (image ρ x ⊔ image ρ c)) ↔ _
  rw [← image_sup, map_antichain_holds, map_antichain_holds, image_le_iff]
  exact and_iff_right (base_le_image ρ x)

/-- Transport an ideal-internal relation code through the cone isomorphism. -/
def mapRelation (ρ : I ≃o Set.Ici a) {n : ℕ} (p : RCode I n) : RelationCode n :=
  ⟨fun i => mapSet ρ (p.coordinates i), mapAntichain ρ p.tuples⟩

theorem map_relation_holds (ρ : I ≃o Set.Ici a) {n : ℕ}
    (p : RCode I n) (v : Fin n → I) :
    ConeCoding.Holds a.val (mapRelation ρ p) (fun i => image ρ (v i)) ↔
      p.external.Holds (fun i => (v i).val) := by
  constructor
  · rintro ⟨c, hc, ht⟩
    have hm (i : Fin n) : c i ∈ I.carrier :=
      I.lower (hc i).2.2.1.2.1.1 (ρ (p.coordinates i).tags.bound).val.property
    let d : Fin n → I := fun i =>
      ρ.symm ⟨⟨c i, hm i⟩, Set.mem_Ici.mpr (hc i).2.2.1.1⟩
    have hd (i : Fin n) : image ρ (d i) = c i :=
      congrArg (fun z : Set.Ici a => z.val.val) (ρ.apply_symm_apply _)
    have hs : image ρ (Finset.univ.sup d) = a.val ⊔ Finset.univ.sup c := by
      simpa only [hd] using image_finset_sup ρ Finset.univ d
    apply (p.internal v).mpr
    refine ⟨d, fun i => (map_graph ρ (p.coordinates i) (v i) (d i)).mp ?_, ?_⟩
    · rw [hd]
      exact hc i
    · apply (map_antichain_holds ρ p.tuples _).mp
      rw [hs]
      exact ht
  · intro h
    obtain ⟨c, hc, ht⟩ := (p.internal v).mp h
    refine ⟨fun i => image ρ (c i), fun i => (map_graph ρ _ _ _).mpr (hc i), ?_⟩
    have hh := (map_antichain_holds ρ p.tuples _).mpr ht
    rw [image_finset_sup] at hh
    exact hh

theorem map_relation_two (ρ : I ≃o Set.Ici a) (p : RCode I 2) (x y : I) :
    ConeCoding.Holds a.val (mapRelation ρ p) (two (image ρ x) (image ρ y)) ↔
      p.external.Holds (two x.val y.val) := by
  have h₁ : (fun i : Fin 2 => image ρ (![x, y] i)) = two (image ρ x) (image ρ y) := by
    funext i; fin_cases i <;> rfl
  have h₂ : (fun i : Fin 2 => (![x, y] i).val) = two x.val y.val := by
    funext i; fin_cases i <;> rfl
  simpa only [h₁, h₂] using map_relation_holds ρ p ![x, y]

theorem coordinates_mem (ρ : I ≃o Set.Ici a) {n : ℕ} (p : RCode I n)
    {v : Fin n → Degree} (h : ConeCoding.Holds a.val (mapRelation ρ p) v) (i : Fin n) :
    a.val ≤ v i ∧ v i ∈ I.carrier := by
  obtain ⟨c, hc, _⟩ := h
  exact ⟨(hc i).1, I.lower (hc i).2.1 (ρ (p.coordinates i).bound).val.property⟩

theorem map_antichain_below (ρ : I ≃o Set.Ici a) (p : ACode I) (b : I)
    (hp : AntichainBelow p.external b.val) :
    AntichainBelow (mapAntichain ρ p) (image ρ b) :=
  ⟨(image_le_iff ρ _ _).mpr hp.1, (image_le_iff ρ _ _).mpr hp.2.1,
    (image_le_iff ρ _ _).mpr hp.2.2⟩

theorem map_set_below (ρ : I ≃o Set.Ici a) (p : SCode I) (b : I)
    (hp : SetBelow p.external b.val) : SetBelow (mapSet ρ p) (image ρ b) :=
  ⟨(image_le_iff ρ _ _).mpr hp.1, map_antichain_below ρ _ _ hp.2.1,
    map_antichain_below ρ _ _ hp.2.2⟩

theorem map_relation_below (ρ : I ≃o Set.Ici a) {n : ℕ} (p : RCode I n) (b : I)
    (hp : RelationBelow p.external b.val) : RelationBelow (mapRelation ρ p) (image ρ b) :=
  ⟨fun i => map_set_below ρ _ _ (hp.1 i), map_antichain_below ρ _ _ hp.2⟩

end OAI.TuringRigidity.ConeIdealCoding
