/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Foundations.RelationAlgebra.AtomStructure
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.Irreducible

/-!
# Complex algebras and isomorphisms of atom structures

General facts relating atom structures and their complex algebras:

* `LawfulAtomStructure.of_equiv`: lawfulness transports along isomorphisms of atom structures.
* `ComplexAlgebra.congr`: an isomorphism of atom structures induces an isomorphism of complex
  algebras.
* `ComplexAlgebra.exists_equiv_of_relationAlgebraEquiv`: conversely, an isomorphism of complex
  algebras is induced by an isomorphism of atom structures.
* `complexAlgebraEquivOfFinite`: a finite relation algebra is isomorphic to the complex algebra of
  its atom structure.
-/

@[expose] public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra

variable {α β : Type*}

/-- Lawfulness of atom structures transports along an isomorphism of atom structures. -/
theorem LawfulAtomStructure.of_equiv (e : α ≃ β) {A : AtomStructure α} {B : AtomStructure β}
    [LawfulAtomStructure B] (hconv : ∀ a, e (A.conv a) = B.conv (e a))
    (hid : ∀ a, a ∈ A.id ↔ e a ∈ B.id)
    (hcyc : ∀ a b c, (a, b, c) ∈ A.cycles ↔ (e a, e b, e c) ∈ B.cycles) :
    LawfulAtomStructure A where
  assoc := fun {r q p s t} h₁ h₂ => by
    obtain ⟨q', h₃, h₄⟩ := B.assoc ((hcyc _ _ _).mp h₁) ((hcyc _ _ _).mp h₂)
    refine ⟨e.symm q', (hcyc _ _ _).mpr ?_, (hcyc _ _ _).mpr ?_⟩
    · rwa [e.apply_symm_apply]
    · rwa [e.apply_symm_apply]
  id_cycle_right := fun {s r p} hs h =>
    e.injective (B.id_cycle_right ((hid _).mp hs) ((hcyc _ _ _).mp h))
  exists_id_cycle_right := fun r => by
    obtain ⟨s, hs, h⟩ := B.exists_id_cycle_right (e r)
    refine ⟨e.symm s, (hid _).mpr ?_, (hcyc _ _ _).mpr ?_⟩
    · rwa [e.apply_symm_apply]
    · rwa [e.apply_symm_apply]
  cycle_left := fun {r s t} h => (hcyc _ _ _).mpr <| by
    rw [hconv]
    exact B.cycle_left ((hcyc _ _ _).mp h)

namespace ComplexAlgebra

theorem singleton_le_mul_iff {A : AtomStructure α} {a b c : α} :
    ({c} : ComplexAlgebra A) ≤ {a} * {b} ↔ (a, b, c) ∈ A.cycles := by
  simp [mem_mul]

theorem singleton_le_one_iff {A : AtomStructure α} {a : α} :
    ({a} : ComplexAlgebra A) ≤ 1 ↔ a ∈ A.id := by
  simp

/-- An isomorphism of atom structures induces an isomorphism of complex algebras. -/
def congr (e : α ≃ β) {A : AtomStructure α} {B : AtomStructure β}
    [LawfulAtomStructure A] [LawfulAtomStructure B]
    (hconv : ∀ a, e (A.conv a) = B.conv (e a))
    (hcyc : ∀ a b c, (a, b, c) ∈ A.cycles ↔ (e a, e b, e c) ∈ B.cycles) :
    RelationAlgebraEquiv (ComplexAlgebra A) (ComplexAlgebra B) where
  toFun x := ⟨{b | e.symm b ∈ x}⟩
  invFun y := ⟨{a | e a ∈ y}⟩
  left_inv x := by
    ext a
    simp
  right_inv y := by
    ext b
    simp
  map_rel_iff' {x y} := by
    change (⟨{b | e.symm b ∈ x}⟩ : ComplexAlgebra B) ≤ ⟨{b | e.symm b ∈ y}⟩ ↔ x ≤ y
    rw [IsConcreteLE.le_iff, IsConcreteLE.le_iff]
    constructor
    · intro h a ha
      have := @h (e a) (by simpa using ha)
      simpa using this
    · intro h b hb
      exact h hb
  map_mul' x y := by
    ext c
    simp only [mem_mul, mem_mk, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨r, hr, u, hu, h⟩
      refine ⟨e r, by simpa using hr, e u, by simpa using hu, ?_⟩
      simpa using (hcyc _ _ _).mp h
    · rintro ⟨r, hr, u, hu, h⟩
      refine ⟨e.symm r, hr, e.symm u, hu, (hcyc _ _ _).mpr ?_⟩
      simpa using h
  map_star' x := by
    ext c
    simp only [mem_star, mem_mk, Set.mem_ofPred_eq]
    have : e.symm (B.conv c) = A.conv (e.symm c) := by
      rw [Equiv.symm_apply_eq, hconv, Equiv.apply_symm_apply]
    rw [this]

@[simp]
theorem mem_congr_iff (e : α ≃ β) {A : AtomStructure α} {B : AtomStructure β}
    [LawfulAtomStructure A] [LawfulAtomStructure B]
    (hconv : ∀ a, e (A.conv a) = B.conv (e a))
    (hcyc : ∀ a b c, (a, b, c) ∈ A.cycles ↔ (e a, e b, e c) ∈ B.cycles)
    {x : ComplexAlgebra A} {b : β} : b ∈ congr e hconv hcyc x ↔ e.symm b ∈ x := .rfl

/-- An isomorphism of complex algebras is induced by an isomorphism of atom structures. -/
theorem exists_equiv_of_relationAlgebraEquiv {A : AtomStructure α} {B : AtomStructure β}
    [LawfulAtomStructure A] [LawfulAtomStructure B]
    (f : RelationAlgebraEquiv (ComplexAlgebra A) (ComplexAlgebra B)) :
    ∃ e : α ≃ β, (∀ a, f {a} = {e a}) ∧ (∀ a, e (A.conv a) = B.conv (e a)) ∧
      (∀ a, e a ∈ B.id ↔ a ∈ A.id) ∧
      (∀ a b c, (e a, e b, e c) ∈ B.cycles ↔ (a, b, c) ∈ A.cycles) := by
  have hf : ∀ a : α, ∃ b : β, f {a} = {b} := fun a =>
    isAtom_iff.mp (f.isAtom_apply_iff.mpr isAtom_singleton)
  have hg : ∀ b : β, ∃ a : α, f.symm {b} = {a} := fun b =>
    isAtom_iff.mp (f.symm.isAtom_apply_iff.mpr isAtom_singleton)
  choose φ hφ using hf
  choose ψ hψ using hg
  have hψφ : ∀ a, ψ (φ a) = a := fun a => (singleton_inj (A := A)).mp <| by
    rw [← hψ, ← hφ, f.symm_apply_apply]
  have hφψ : ∀ b, φ (ψ b) = b := fun b => (singleton_inj (A := B)).mp <| by
    rw [← hφ, ← hψ, f.apply_symm_apply]
  refine ⟨⟨φ, ψ, hψφ, hφψ⟩, hφ, fun a => (singleton_inj (A := B)).mp ?_, fun a => ?_,
    fun a b c => ?_⟩
  · calc ({φ (A.conv a)} : ComplexAlgebra B) = f {A.conv a} := (hφ _).symm
      _ = f (star {a}) := by rw [star_singleton]
      _ = star (f {a}) := map_star f _
      _ = star {φ a} := by rw [hφ]
      _ = {B.conv (φ a)} := star_singleton
  · change φ a ∈ B.id ↔ a ∈ A.id
    rw [← singleton_le_one_iff, ← hφ a, f.apply_le_one_iff, singleton_le_one_iff]
  · change (φ a, φ b, φ c) ∈ B.cycles ↔ (a, b, c) ∈ A.cycles
    rw [← singleton_le_mul_iff, ← hφ a, ← hφ b, ← hφ c, ← map_mul, map_le_map_iff,
      singleton_le_mul_iff]

end ComplexAlgebra

/-- An atom of a Boolean algebra lies below a finite supremum exactly when it lies below one of
the terms. -/
theorem isAtom_le_finset_sup_iff {α ι : Type*} [BooleanAlgebra α] {a : α} (ha : IsAtom a)
    (t : Finset ι) (f : ι → α) : a ≤ t.sup f ↔ ∃ i ∈ t, a ≤ f i := by
  refine SupPrime.le_finset_sup ⟨fun h => ha.1 (isMin_iff_eq_bot.mp h), fun b c h => ?_⟩
  by_contra hcon
  rw [not_or, ha.not_le_iff_disjoint, ha.not_le_iff_disjoint] at hcon
  exact ha.1 (disjoint_self.mp ((hcon.1.sup_right hcon.2).mono_right h))

section Finite

variable {α : Type*} [RelationAlgebra α] [Finite α]

/-- In a finite relation algebra, every set of atoms is the set of atoms below some element. -/
theorem exists_forall_isAtom_le_iff (S : Set {a : α // IsAtom a}) :
    ∃ x : α, ∀ a : {a : α // IsAtom a}, a.val ≤ x ↔ a ∈ S := by
  classical
  refine ⟨S.toFinite.toFinset.sup Subtype.val, fun a => ?_⟩
  rw [isAtom_le_finset_sup_iff a.property]
  constructor
  · rintro ⟨b, hb, hab⟩
    rw [Set.Finite.mem_toFinset] at hb
    have : a = b := Subtype.ext ((b.property.le_iff_eq a.property.ne_bot).mp hab)
    exact this ▸ hb
  · exact fun ha => ⟨a, S.toFinite.mem_toFinset.mpr ha, le_rfl⟩

variable (α) in
/-- The isomorphism from a finite relation algebra to the complex algebra of its atom structure.
This is the analogue of `complexAlgebraEquiv` that does not require a
`CompleteAtomicRelationAlgebra` instance. -/
noncomputable def complexAlgebraEquivOfFinite :
    RelationAlgebraEquiv α (ComplexAlgebra (atomStructure α)) where
  toFun x := ⟨{a | a.val ≤ x}⟩
  invFun S := Classical.choose (exists_forall_isAtom_le_iff S.carrier)
  left_inv x := by
    have h := Classical.choose_spec
      (exists_forall_isAtom_le_iff {a : {a : α // IsAtom a} | a.val ≤ x})
    change Classical.choose
      (exists_forall_isAtom_le_iff {a : {a : α // IsAtom a} | a.val ≤ x}) = x
    refine le_antisymm ?_ ?_ <;> rw [BooleanAlgebra.le_iff_atom_le_imp] <;> intro a ha hax
    · exact (h ⟨a, ha⟩).mp hax
    · exact (h ⟨a, ha⟩).mpr hax
  right_inv S := by
    ext a
    exact Classical.choose_spec (exists_forall_isAtom_le_iff S.carrier) a
  map_rel_iff' {x y} := by
    rw [BooleanAlgebra.le_iff_atom_le_imp (x := x)]
    exact ⟨fun h a ha hax => @h ⟨a, ha⟩ hax, fun h a hax => h a.val a.property hax⟩
  map_mul' x y := by
    ext p
    rw [ComplexAlgebra.mem_mul]
    constructor
    · intro hp
      obtain ⟨r, hr, hrx, hpr⟩ := exists_atom_le_mul_left p.property hp
      obtain ⟨u, hu, huy, hpu⟩ := exists_atom_le_mul_right p.property hpr
      exact ⟨⟨r, hr⟩, hrx, ⟨u, hu⟩, huy, hpu⟩
    · rintro ⟨r, hr, u, hu, h⟩
      exact h.trans (mul_le_mul' hr hu)
  map_star' x := by
    ext p
    rw [ComplexAlgebra.mem_star]
    exact le_star_iff

theorem complexAlgebraEquivOfFinite_apply (x : α) :
    complexAlgebraEquivOfFinite α x = ⟨{a | a.val ≤ x}⟩ := rfl

end Finite

end FiniteIntegralRelationAlgebras.RelationAlgebra
