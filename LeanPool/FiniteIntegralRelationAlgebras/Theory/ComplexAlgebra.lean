/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Foundations.RelationAlgebra.AtomStructure
public import Mathlib.Data.Fintype.Order
public import Mathlib.Order.Atoms.Finite

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

section Finite

variable {α : Type*} [RelationAlgebra α] [Finite α]

variable (α) in
/-- The isomorphism from a finite relation algebra to the complex algebra of its atom structure.
A finite Boolean algebra supplies the complete atomic structure used by `complexAlgebraEquiv`. -/
noncomputable def complexAlgebraEquivOfFinite :
    RelationAlgebraEquiv α (ComplexAlgebra (atomStructure α)) := by
  letI := Fintype.ofFinite α
  letI : CompleteAtomicRelationAlgebra α :=
    { __ := ‹RelationAlgebra α›
      __ := Fintype.toCompleteAtomicBooleanAlgebra α }
  exact complexAlgebraEquiv

theorem complexAlgebraEquivOfFinite_apply (x : α) :
    complexAlgebraEquivOfFinite α x = ⟨{a | a.val ≤ x}⟩ := rfl

end Finite

end FiniteIntegralRelationAlgebras.RelationAlgebra
