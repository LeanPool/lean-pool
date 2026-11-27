/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Theory.CycleSets
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.End

/-!
# The symmetry group of integral atoms and its action on lawful cycle sets

`IntegralAtom.Aut s n` is the group of permutations of `IntegralAtom (Fin s) (Fin n)` that fix the
identity atom and commute with converse. It acts on the lawful cycle sets by taking images.
-/

@[expose] public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra

namespace IntegralAtom

variable {s n : ℕ}

/-- Permutations of atoms fixing the identity and commuting with converse. -/
def Aut (s n : ℕ) : Subgroup (Equiv.Perm (IntegralAtom (Fin s) (Fin n))) where
  carrier := {σ | σ one = one ∧ ∀ a, σ (conv a) = conv (σ a)}
  mul_mem' {σ τ} hσ hτ := by
    refine ⟨?_, fun a => ?_⟩
    · rw [Equiv.Perm.mul_apply, hτ.1, hσ.1]
    · rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, hτ.2, hσ.2]
  one_mem' := ⟨rfl, fun _ => rfl⟩
  inv_mem' {σ} hσ := by
    refine ⟨?_, fun a => ?_⟩
    · rw [Equiv.Perm.inv_eq_iff_eq, hσ.1]
    · rw [Equiv.Perm.inv_eq_iff_eq, hσ.2]
      exact congrArg conv (σ.apply_symm_apply a).symm

theorem mem_aut_iff {σ : Equiv.Perm (IntegralAtom (Fin s) (Fin n))} :
    σ ∈ Aut s n ↔ σ one = one ∧ ∀ a, σ (conv a) = conv (σ a) := .rfl

namespace Aut

@[simp]
theorem apply_one (σ : Aut s n) : σ.val one = one := σ.property.1

theorem apply_conv (σ : Aut s n) (a : IntegralAtom (Fin s) (Fin n)) :
    σ.val (conv a) = conv (σ.val a) :=
  σ.property.2 a

@[simp]
theorem symm_apply_one (σ : Aut s n) : σ.val.symm one = one := (σ⁻¹).property.1

theorem symm_apply_conv (σ : Aut s n) (a : IntegralAtom (Fin s) (Fin n)) :
    σ.val.symm (conv a) = conv (σ.val.symm a) := (σ⁻¹).property.2 a

@[simp]
theorem apply_eq_one_iff (σ : Aut s n) {a : IntegralAtom (Fin s) (Fin n)} :
    σ.val a = one ↔ a = one := by
  rw [← σ.val.apply_eq_iff_eq (x := a), apply_one]

@[simp]
theorem coe_inv_apply (σ : Aut s n) (a : IntegralAtom (Fin s) (Fin n)) :
    (σ⁻¹).val a = σ.val.symm a := rfl

@[simp]
theorem coe_mul_apply (σ τ : Aut s n) (a : IntegralAtom (Fin s) (Fin n)) :
    (σ * τ).val a = σ.val (τ.val a) := rfl

@[simp]
theorem coe_one_apply (a : IntegralAtom (Fin s) (Fin n)) : (1 : Aut s n).val a = a := rfl

end Aut

/-- The image of a cycle set under a permutation of atoms:
`mapCycles σ T = {(σ a, σ b, σ c) | (a, b, c) ∈ T}`. -/
def mapCycles (σ : Equiv.Perm (IntegralAtom (Fin s) (Fin n))) (T : Set (Cycle (Fin s) (Fin n))) :
    Set (Cycle (Fin s) (Fin n)) :=
  {c | (σ.symm c.1, σ.symm c.2.1, σ.symm c.2.2) ∈ T}

theorem mem_mapCycles {σ : Equiv.Perm (IntegralAtom (Fin s) (Fin n))}
    {T : Set (Cycle (Fin s) (Fin n))}
    {a b c : IntegralAtom (Fin s) (Fin n)} :
    (a, b, c) ∈ mapCycles σ T ↔ (σ.symm a, σ.symm b, σ.symm c) ∈ T := .rfl

@[simp]
theorem apply_mem_mapCycles {σ : Equiv.Perm (IntegralAtom (Fin s) (Fin n))}
    {T : Set (Cycle (Fin s) (Fin n))}
    {a b c : IntegralAtom (Fin s) (Fin n)} : (σ a, σ b, σ c) ∈ mapCycles σ T ↔ (a, b, c) ∈ T := by
  rw [mem_mapCycles, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

theorem IsLawfulCycles.mapCycles {T : Set (Cycle (Fin s) (Fin n))} (h : IsLawfulCycles T)
    {σ : Equiv.Perm (IntegralAtom (Fin s) (Fin n))} (hσ : σ ∈ Aut s n) :
    IsLawfulCycles (mapCycles σ T) := by
  have hone : σ.symm one = one := (Aut s n).inv_mem hσ |>.1
  have hconv : ∀ a, σ.symm (conv a) = conv (σ.symm a) := (Aut s n).inv_mem hσ |>.2
  rw [isLawfulCycles_iff]
  refine ⟨fun r p => ?_, fun r u t hc => ?_, fun r q p u t h₁ h₂ => ?_⟩
  · rw [mem_mapCycles, hone, h.one_right_iff, Equiv.apply_eq_iff_eq]
  · rw [mem_mapCycles, hconv]
    exact h.left_mem hc
  · obtain ⟨q', hq'₁, hq'₂⟩ := h.assoc (mem_mapCycles.mp h₁) (mem_mapCycles.mp h₂)
    refine ⟨σ q', ?_, ?_⟩ <;> rw [mem_mapCycles, Equiv.symm_apply_apply] <;> assumption

/-- `Aut s n` acts on lawful cycle sets by `σ • T = {(σ a, σ b, σ c) | (a, b, c) ∈ T}`. -/
instance : MulAction (Aut s n) {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T} where
  smul σ T := ⟨mapCycles σ.val T.val, T.property.mapCycles σ.property⟩
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

theorem coe_smul (σ : Aut s n) (T : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}) :
    ((σ • T : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}) :
      Set (Cycle (Fin s) (Fin n))) =
      mapCycles σ.val T.val := rfl

/-- Membership in `σ • T`, in terms of the inverse permutation. -/
theorem mem_smul_iff {σ : Aut s n} {T : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}}
    {a b c : IntegralAtom (Fin s) (Fin n)} :
    (a, b, c) ∈ ((σ • T : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}) :
      Set (Cycle (Fin s) (Fin n))) ↔
      (σ.val.symm a, σ.val.symm b, σ.val.symm c) ∈ T.val := .rfl

@[simp]
theorem apply_mem_smul_iff {σ : Aut s n} {T : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}}
    {a b c : IntegralAtom (Fin s) (Fin n)} :
    (σ.val a, σ.val b, σ.val c) ∈ ((σ • T : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}) :
      Set (Cycle (Fin s) (Fin n))) ↔ (a, b, c) ∈ T.val :=
  apply_mem_mapCycles

theorem smul_eq_iff {σ : Aut s n} {T T' : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}} :
    σ • T = T' ↔ ∀ a b c, (σ.val a, σ.val b, σ.val c) ∈ T'.val ↔ (a, b, c) ∈ T.val := by
  constructor
  · rintro rfl a b c
    exact apply_mem_smul_iff
  · intro h
    refine Subtype.ext (Set.ext fun ⟨a, b, c⟩ => ?_)
    rw [mem_smul_iff, ← h, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]

theorem smul_eq_self_iff {σ : Aut s n} {T : {T : Set (Cycle (Fin s) (Fin n)) // IsLawfulCycles T}} :
    σ • T = T ↔ ∀ a b c, (σ.val a, σ.val b, σ.val c) ∈ T.val ↔ (a, b, c) ∈ T.val :=
  smul_eq_iff

end IntegralAtom

end FiniteIntegralRelationAlgebras.RelationAlgebra
