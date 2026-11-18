/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-auto/RequestProject/TuringConeCoding.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
-/

module

public import LeanPool.TuringConeRigidity.TuringConeRigidity
public import LeanPool.TuringConeRigidity.SetModels.IdealInterpretation
public import LeanPool.TuringConeRigidity.Computability.ArithmeticModelDecoding

/-!
# Coding interpreted in a principal Turing cone

An ordinary coded antichain cannot simply be reused after applying a cone
isomorphism: its minimality quantifier must range only over degrees above the
new bottom. This file defines the relative predicates and proves that a cone
isomorphism transports antichain, set, and relation codes with those semantics.
It also transports coded copies of a unary predicate on the natural numbers,
and preserves the bounds on all coding parameters.

The relative antichain predicate has a bounded version, suitable for arithmetic
decoding. Arithmetic complexity bounds and the pointwise inverse bound are
proved in `TuringConeArithmetic` and `TuringConeLocality`. No forcing-extension
theorem or uniform generic representative is asserted here.
-/


@[expose] public section


namespace OAI.TuringRigidity.ConeCoding

open SetCoding RelationCoding AntichainParameters BoundedDecoding
open ArithmeticModelDecoding

/-- The underlying degree-valued map of a cone isomorphism. -/
def image {a : Degree} (e : Degree ≃o Set.Ici a) (x : Degree) : Degree := (e x).val

theorem base_le_image {a : Degree} (e : Degree ≃o Set.Ici a) (x : Degree) :
    a ≤ image e x := Set.mem_Ici.mp (e x).property

theorem image_le_iff {a : Degree} (e : Degree ≃o Set.Ici a) (x y : Degree) :
    image e x ≤ image e y ↔ x ≤ y := e.le_iff_le

theorem image_sup {a : Degree} (e : Degree ≃o Set.Ici a) (x y : Degree) :
    image e (x ⊔ y) = image e x ⊔ image e y := by
  exact congrArg Subtype.val (e.map_sup x y)

/-- The empty join is sent to `a`, not to the ambient bottom. -/
theorem image_finset_sup {a : Degree} (e : Degree ≃o Set.Ici a)
    {ι : Type*} (s : Finset ι) (f : ι → Degree) :
    image e (s.sup f) = a ⊔ s.sup (fun i => image e (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sup_empty, sup_bot_eq, image] using ConeRigidity.map_bot_val e
  | @insert i s hi ih =>
    rw [Finset.sup_insert, image_sup, ih, Finset.sup_insert]
    exact sup_left_comm _ _ _

/-- Above `a`, a witness to nontriviality may be replaced by its join with `a`. -/
theorem nontrivial_ici {a : Degree} (b g₀ g₁ x : Set.Ici a) :
    IdealInterpretation.nontrivial b g₀ g₁ x ↔
      NontrivialCommonLower b.val g₀.val g₁.val x.val := by
  constructor
  · rintro ⟨hx, z, hz₀, hz₁, hn⟩
    exact ⟨hx, z.val, hz₀, hz₁, hn⟩
  · rintro ⟨hx, z, hz₀, hz₁, hn⟩
    refine ⟨hx, ⟨a ⊔ z, Set.mem_Ici.mpr le_sup_left⟩, ?_, ?_, ?_⟩
    · exact sup_le ((Set.mem_Ici.mp x.property).trans le_sup_right) hz₀
    · exact sup_le ((Set.mem_Ici.mp x.property).trans le_sup_right) hz₁
    · intro h
      exact hn (le_sup_right.trans h)

/-- The antichain code interpreted with quantifiers in the cone above `a`. -/
def Antichain (a : Degree) (p : AntichainCode) (x : Degree) : Prop :=
  a ≤ x ∧ NontrivialCommonLower p.bound p.left p.right x ∧
    ∀ y, a ≤ y → NontrivialCommonLower p.bound p.left p.right y → y ≤ x → x ≤ y

theorem antichain_ici {a : Degree} (b g₀ g₁ x : Set.Ici a) :
    IdealInterpretation.antichain b g₀ g₁ x ↔
      Antichain a ⟨b.val, g₀.val, g₁.val⟩ x.val := by
  constructor
  · rintro ⟨hx, hm⟩
    refine ⟨Set.mem_Ici.mp x.property, (nontrivial_ici _ _ _ _).mp hx, ?_⟩
    intro y hay hy hyx
    exact hm ⟨y, Set.mem_Ici.mpr hay⟩ ((nontrivial_ici _ _ _ _).mpr hy) hyx
  · rintro ⟨_, hx, hm⟩
    refine ⟨(nontrivial_ici _ _ _ _).mpr hx, ?_⟩
    intro y hy hyx
    exact hm y.val (Set.mem_Ici.mp y.property) ((nontrivial_ici _ _ _ _).mp hy) hyx

/-- Transport the three antichain parameters through an isomorphism from all degrees to a
principal cone. -/
def mapAntichain {a : Degree} (e : Degree ≃o Set.Ici a) (p : AntichainCode) :
    AntichainCode := ⟨image e p.bound, image e p.left, image e p.right⟩

theorem map_antichain_holds {a : Degree} (e : Degree ≃o Set.Ici a)
    (p : AntichainCode) (x : Degree) :
    Antichain a (mapAntichain e p) (image e x) ↔ p.Holds x :=
  (antichain_ici (e p.bound) (e p.left) (e p.right) (e x)).symm.trans
    (IdealInterpretation.map_antichain e p.bound p.left p.right x)

/-- Both degree variables in a set-code graph now range over the cone. -/
def Graph (a : Degree) (p : SetCode) (x c : Degree) : Prop :=
  a ≤ x ∧ x ≤ p.bound ∧ Antichain a p.tags c ∧ Antichain a p.decorated (x ⊔ c)

/-- Transport the bound and antichain parameters of a set code into the principal cone. -/
def mapSet {a : Degree} (e : Degree ≃o Set.Ici a) (p : SetCode) : SetCode :=
  ⟨image e p.bound, mapAntichain e p.tags, mapAntichain e p.decorated⟩

theorem map_graph {a : Degree} (e : Degree ≃o Set.Ici a) (p : SetCode)
    (x c : Degree) : Graph a (mapSet e p) (image e x) (image e c) ↔ p.Graph x c := by
  change (a ≤ image e x ∧ image e x ≤ image e p.bound ∧
    Antichain a (mapAntichain e p.tags) (image e c) ∧
    Antichain a (mapAntichain e p.decorated) (image e x ⊔ image e c)) ↔ _
  rw [← image_sup, map_antichain_holds, map_antichain_holds, image_le_iff]
  exact and_iff_right (base_le_image e x)

/-- The tuple join includes `a`, also handling arity zero correctly. -/
def Holds {n : ℕ} (a : Degree) (p : RelationCode n) (v : Fin n → Degree) : Prop :=
  ∃ c : Fin n → Degree, (∀ i, Graph a (p.coordinates i) (v i) (c i)) ∧
    Antichain a p.tuples (a ⊔ Finset.univ.sup c)

/-- Transport all coordinate and tuple parameters of a relation code into the principal cone. -/
def mapRelation {a : Degree} (e : Degree ≃o Set.Ici a) {n : ℕ}
    (p : RelationCode n) : RelationCode n :=
  ⟨fun i => mapSet e (p.coordinates i), mapAntichain e p.tuples⟩

theorem map_relation_holds {a : Degree} (e : Degree ≃o Set.Ici a) {n : ℕ}
    (p : RelationCode n) (v : Fin n → Degree) :
    Holds a (mapRelation e p) (fun i => image e (v i)) ↔ p.Holds v := by
  constructor
  · rintro ⟨c, hc, ht⟩
    let d : Fin n → Degree := fun i =>
      e.symm ⟨c i, Set.mem_Ici.mpr (hc i).2.2.1.1⟩
    have hd (i : Fin n) : image e (d i) = c i := by
      exact congrArg Subtype.val (e.apply_symm_apply _)
    have hs : image e (Finset.univ.sup d) = a ⊔ Finset.univ.sup c := by
      simpa only [hd] using image_finset_sup e Finset.univ d
    refine ⟨d, fun i => (map_graph e (p.coordinates i) (v i) (d i)).mp ?_, ?_⟩
    · rw [hd]
      exact hc i
    · apply (map_antichain_holds e p.tuples _).mp
      rw [hs]
      exact ht
  · rintro ⟨c, hc, ht⟩
    refine ⟨fun i => image e (c i), fun i => (map_graph e _ _ _).mpr (hc i), ?_⟩
    have hh := (map_antichain_holds e p.tuples _).mpr ht
    rw [image_finset_sup] at hh
    exact hh

theorem map_relation_one {a : Degree} (e : Degree ≃o Set.Ici a)
    (p : RelationCode 1) (x : Degree) :
    Holds a (mapRelation e p) (one (image e x)) ↔ p.Holds (one x) := by
  have h : (fun i : Fin 1 => image e (one x i)) = one (image e x) := by
    funext i
    fin_cases i
    rfl
  simpa only [h] using map_relation_holds e p (one x)

theorem map_relation_two {a : Degree} (e : Degree ≃o Set.Ici a)
    (p : RelationCode 2) (x y : Degree) :
    Holds a (mapRelation e p) (two (image e x) (image e y)) ↔ p.Holds (two x y) := by
  have h : (fun i : Fin 2 => image e (two x y i)) = two (image e x) (image e y) := by
    funext i
    fin_cases i <;> rfl
  simpa only [h] using map_relation_holds e p (two x y)

theorem map_antichain_below {a : Degree} (e : Degree ≃o Set.Ici a)
    (p : AntichainCode) (b : Degree) (h : AntichainBelow p b) :
    AntichainBelow (mapAntichain e p) (image e b) :=
  ⟨(image_le_iff e _ _).mpr h.1, (image_le_iff e _ _).mpr h.2.1,
    (image_le_iff e _ _).mpr h.2.2⟩

theorem map_set_below {a : Degree} (e : Degree ≃o Set.Ici a)
    (p : SetCode) (b : Degree) (h : SetBelow p b) :
    SetBelow (mapSet e p) (image e b) :=
  ⟨(image_le_iff e _ _).mpr h.1, map_antichain_below e _ _ h.2.1,
    map_antichain_below e _ _ h.2.2⟩

theorem map_relation_below {a : Degree} (e : Degree ≃o Set.Ici a)
    {n : ℕ} (p : RelationCode n) (b : Degree) (h : RelationBelow p b) :
    RelationBelow (mapRelation e p) (image e b) :=
  ⟨fun i => map_set_below e _ _ (h.1 i), map_antichain_below e _ _ h.2⟩

/-- A coded copy whose nodes and quantifiers live in the target cone. -/
structure Copy (a : Degree) (U : ℕ → Prop) where
  /-- The injective sequence of cone elements representing the natural-number nodes. -/
  node : ℕ → Set.Ici a
  injective : Function.Injective node
  /-- The relation code representing successor between the cone nodes. -/
  successor : RelationCode 2
  /-- The relation code representing the distinguished predicate on cone nodes. -/
  predicate : RelationCode 1
  successor_spec : ∀ x y : Set.Ici a,
    Holds a successor (two x.val y.val) ↔ ∃ k, x = node k ∧ y = node (k + 1)
  predicate_spec : ∀ x : Set.Ici a,
    Holds a predicate (one x.val) ↔ ∃ k, U k ∧ x = node k

/-- The coded unary predicate is unchanged, despite the change of bottom. -/
def transportCopy {a : Degree} (e : Degree ≃o Set.Ici a) {U : ℕ → Prop}
    (c : ArithmeticModelDecoding.Copy U) : Copy a U where
  node n := e (c.node n)
  injective := e.injective.comp c.injective
  successor := mapRelation e c.successor
  predicate := mapRelation e c.predicate
  successor_spec := by
    intro x y
    obtain ⟨u, rfl⟩ := e.surjective x
    obtain ⟨v, rfl⟩ := e.surjective y
    change Holds a (mapRelation e c.successor) (two (image e u) (image e v)) ↔
      ∃ k, e u = e (c.node k) ∧ e v = e (c.node (k + 1))
    rw [map_relation_two, c.successor_spec]
    constructor
    · rintro ⟨k, hk, hl⟩
      exact ⟨k, congrArg e hk, congrArg e hl⟩
    · rintro ⟨k, hk, hl⟩
      exact ⟨k, e.injective hk, e.injective hl⟩
  predicate_spec := by
    intro x
    obtain ⟨u, rfl⟩ := e.surjective x
    change Holds a (mapRelation e c.predicate) (one (image e u)) ↔
      ∃ k, U k ∧ e u = e (c.node k)
    rw [map_relation_one, c.predicate_spec]
    constructor
    · rintro ⟨k, hk, he⟩
      exact ⟨k, hk, congrArg e he⟩
    · rintro ⟨k, hk, he⟩
      exact ⟨k, hk, e.injective he⟩

theorem transport_copy_below {a : Degree} (e : Degree ≃o Set.Ici a)
    {U : ℕ → Prop} (c : ArithmeticModelDecoding.Copy U) (b : Degree)
    (hS : RelationBelow c.successor b) (hP : RelationBelow c.predicate b) :
    RelationBelow (transportCopy e c).successor (image e b) ∧
      RelationBelow (transportCopy e c).predicate (image e b) :=
  ⟨map_relation_below e _ _ hS, map_relation_below e _ _ hP⟩

/-- All quantified degrees can be bounded by `y`, retaining the lower bound
`a` in the minimality test. This is the input needed for a relative decoder. -/
def LocalAntichain (a y : Degree) (p : AntichainCode) (x : Degree) : Prop :=
  a ≤ x ∧ LocalNontrivial y p.bound p.left p.right x ∧
    ∀ w, a ≤ w → w ≤ y → LocalNontrivial y p.bound p.left p.right w → w ≤ x → x ≤ w

theorem local_antichain_iff (a y : Degree) (p : AntichainCode)
    (hp : AntichainBelow p y) (x : Degree) :
    LocalAntichain a y p x ↔ Antichain a p x := by
  unfold LocalAntichain Antichain
  simp only [BoundedDecoding.local_nontrivial_iff y p.bound p.left p.right _ hp.1 hp.2.1]
  constructor
  · rintro ⟨hax, hx, hm⟩
    exact ⟨hax, hx, fun w haw hw hle => hm w haw (hw.1.trans hp.1) hw hle⟩
  · rintro ⟨hax, hx, hm⟩
    exact ⟨hax, hx, fun w haw _ hw hle => hm w haw hw hle⟩

end OAI.TuringRigidity.ConeCoding
