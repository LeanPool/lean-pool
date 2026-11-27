/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Theory.Aut
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# An explicit parametrization of the symmetry group of integral atoms

An element of `IntegralAtom.Aut s n` is determined by a permutation of the `s` symmetric atoms, a
permutation of the `n` pairs of nonsymmetric atoms, and a choice of which pairs to flip. This gives
`IntegralAtom.autEquiv` and the cardinality `s ! * n ! * 2 ^ n` of the group.
-/

@[expose] public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra

namespace IntegralAtom

variable {s n : ℕ}

/-- The map on atoms acting by `π` on symmetric atoms, by `ρ` on nonsymmetric pairs, and flipping
the pairs selected by `ε`. -/
def autFun (π : Fin s → Fin s) (ρ : Fin n → Fin n) (ε : Fin n → Bool) :
    IntegralAtom (Fin s) (Fin n) → IntegralAtom (Fin s) (Fin n)
  | one => one
  | symm i => symm (π i)
  | nsymm i b => nsymm (ρ i) (b ^^ ε i)

@[simp]
theorem autFun_one (π : Fin s → Fin s) (ρ : Fin n → Fin n) (ε : Fin n → Bool) :
    autFun π ρ ε one = one := rfl

@[simp]
theorem autFun_symm (π : Fin s → Fin s) (ρ : Fin n → Fin n) (ε : Fin n → Bool) (i : Fin s) :
    autFun π ρ ε (symm i) = symm (π i) := rfl

@[simp]
theorem autFun_nsymm (π : Fin s → Fin s) (ρ : Fin n → Fin n) (ε : Fin n → Bool) (i : Fin n)
    (b : Bool) : autFun π ρ ε (nsymm i b) = nsymm (ρ i) (b ^^ ε i) := rfl

/-- The element of `Aut s n` determined by a permutation of symmetric atoms, a permutation of
nonsymmetric pairs, and a choice of which pairs to flip. -/
def autOfTriple (p : Equiv.Perm (Fin s) × Equiv.Perm (Fin n) × (Fin n → Bool)) : Aut s n :=
  ⟨{ toFun := autFun p.1 p.2.1 p.2.2
     invFun := autFun p.1.symm p.2.1.symm (p.2.2 ∘ p.2.1.symm)
     left_inv := by rintro (_ | i | ⟨i, b⟩) <;> simp
     right_inv := by rintro (_ | i | ⟨i, b⟩) <;> simp },
    rfl, by rintro (_ | i | ⟨i, b⟩) <;> simp⟩

@[simp]
theorem autOfTriple_apply_one (p : Equiv.Perm (Fin s) × Equiv.Perm (Fin n) × (Fin n → Bool)) :
    (autOfTriple p).val one = one := rfl

@[simp]
theorem autOfTriple_apply_symm (π : Equiv.Perm (Fin s)) (ρ : Equiv.Perm (Fin n))
    (ε : Fin n → Bool) (i : Fin s) : (autOfTriple (π, ρ, ε)).val (symm i) = symm (π i) := rfl

@[simp]
theorem autOfTriple_apply_nsymm (π : Equiv.Perm (Fin s)) (ρ : Equiv.Perm (Fin n))
    (ε : Fin n → Bool) (i : Fin n) (b : Bool) :
    (autOfTriple (π, ρ, ε)).val (nsymm i b) = nsymm (ρ i) (b ^^ ε i) := rfl

theorem autOfTriple_apply (p : Equiv.Perm (Fin s) × Equiv.Perm (Fin n) × (Fin n → Bool))
    (a : IntegralAtom (Fin s) (Fin n)) : (autOfTriple p).val a = autFun p.1 p.2.1 p.2.2 a := rfl

theorem autOfTriple_injective : Function.Injective (autOfTriple (s := s) (n := n)) := by
  rintro ⟨π, ρ, ε⟩ ⟨π', ρ', ε'⟩ h
  have h' : ∀ a, (autOfTriple (π, ρ, ε)).val a = (autOfTriple (π', ρ', ε')).val a :=
    fun a => by rw [h]
  have hπ : π = π' := Equiv.ext fun i => by simpa using h' (symm i)
  have hρε : ∀ i, ρ i = ρ' i ∧ ε i = ε' i := fun i => by simpa using h' (nsymm i false)
  obtain rfl := hπ
  obtain rfl : ρ = ρ' := Equiv.ext fun i => (hρε i).1
  obtain rfl : ε = ε' := funext fun i => (hρε i).2
  rfl

/-- An element of `Aut s n` maps symmetric atoms to symmetric atoms. -/
theorem Aut.exists_apply_symm (τ : Aut s n) (i : Fin s) : ∃ j, τ.val (symm i) = symm j := by
  have hconv := Aut.apply_conv τ (symm i)
  have hne : τ.val (symm i) ≠ one := fun h => by simpa using (Aut.apply_eq_one_iff τ).mp h
  rw [conv_symm] at hconv
  cases h : τ.val (symm i) with
  | one => exact (hne h).elim
  | symm j => exact ⟨j, rfl⟩
  | nsymm j b =>
    rw [h] at hconv
    simp at hconv

/-- An element of `Aut s n` maps nonsymmetric atoms to nonsymmetric atoms. -/
theorem Aut.exists_apply_nsymm (τ : Aut s n) (i : Fin n) (b : Bool) :
    ∃ j c, τ.val (nsymm i b) = nsymm j c := by
  have hconv := Aut.apply_conv τ (nsymm i b)
  have hne : τ.val (conv (nsymm i b)) ≠ τ.val (nsymm i b) := fun h => by
    simpa using τ.val.injective h
  cases h : τ.val (nsymm i b) with
  | one =>
    rw [h] at hconv hne
    exact (hne hconv).elim
  | symm j =>
    rw [h] at hconv hne
    exact (hne hconv).elim
  | nsymm j c => exact ⟨j, c, rfl⟩

theorem autOfTriple_surjective : Function.Surjective (autOfTriple (s := s) (n := n)) := by
  intro σ
  choose π hπ using fun i => Aut.exists_apply_symm σ i
  choose π' hπ' using fun i => Aut.exists_apply_symm σ⁻¹ i
  choose ρ ε hρ using fun i => Aut.exists_apply_nsymm σ i false
  choose ρ' ε' hρ' using fun i => Aut.exists_apply_nsymm σ⁻¹ i false
  have hall : ∀ (τ : Aut s n) (ρ : Fin n → Fin n) (ε : Fin n → Bool),
      (∀ i, τ.val (nsymm i false) = nsymm (ρ i) (ε i)) →
      ∀ i b, τ.val (nsymm i b) = nsymm (ρ i) (b ^^ ε i) := by
    intro τ ρ ε h i b
    cases b
    · simpa using h i
    · have := Aut.apply_conv τ (nsymm i false)
      rw [h] at this
      simpa using this
  have hρ_all := hall σ ρ ε hρ
  have hρ'_all := hall σ⁻¹ ρ' ε' hρ'
  have hπ'π : ∀ i, π' (π i) = i := fun i => symm.inj <| by
    rw [← hπ', ← hπ]
    exact σ.val.symm_apply_apply _
  have hππ' : ∀ i, π (π' i) = i := fun i => symm.inj <| by
    rw [← hπ, ← hπ']
    exact σ.val.apply_symm_apply _
  have hρ'ρ : ∀ i, ρ' (ρ i) = i := fun i => by
    have : (σ⁻¹).val (σ.val (nsymm i false)) = nsymm i false := σ.val.symm_apply_apply _
    rw [hρ_all, hρ'_all] at this
    exact (nsymm.inj this).1
  have hρρ' : ∀ i, ρ (ρ' i) = i := fun i => by
    have : σ.val ((σ⁻¹).val (nsymm i false)) = nsymm i false := σ.val.apply_symm_apply _
    rw [hρ'_all, hρ_all] at this
    exact (nsymm.inj this).1
  refine ⟨(⟨π, π', hπ'π, hππ'⟩, ⟨ρ, ρ', hρ'ρ, hρρ'⟩, ε), Subtype.ext (Equiv.ext ?_)⟩
  rintro (_ | i | ⟨i, b⟩)
  · exact (Aut.apply_one σ).symm
  · exact (hπ i).symm
  · exact (hρ_all i b).symm

/-- `Aut s n` is parametrized by a permutation `π` of the symmetric atoms, a permutation `ρ` of the
nonsymmetric pairs, and a choice `ε` of which pairs to flip. The inverse sends `(π, ρ, ε)` to the
map `one ↦ one`, `symm i ↦ symm (π i)`, `nsymm i b ↦ nsymm (ρ i) (b ^^ ε i)`. -/
noncomputable def autEquiv :
    Aut s n ≃ Equiv.Perm (Fin s) × Equiv.Perm (Fin n) × (Fin n → Bool) :=
  (Equiv.ofBijective autOfTriple ⟨autOfTriple_injective, autOfTriple_surjective⟩).symm

theorem autEquiv_symm_apply (p : Equiv.Perm (Fin s) × Equiv.Perm (Fin n) × (Fin n → Bool)) :
    autEquiv.symm p = autOfTriple p := rfl

@[simp]
theorem autEquiv_symm_apply_one
    (p : Equiv.Perm (Fin s) × Equiv.Perm (Fin n) × (Fin n → Bool)) :
    (autEquiv.symm p).val one = one := rfl

@[simp]
theorem autEquiv_symm_apply_symm (π : Equiv.Perm (Fin s)) (ρ : Equiv.Perm (Fin n))
    (ε : Fin n → Bool) (i : Fin s) : (autEquiv.symm (π, ρ, ε)).val (symm i) = symm (π i) := rfl

@[simp]
theorem autEquiv_symm_apply_nsymm (π : Equiv.Perm (Fin s)) (ρ : Equiv.Perm (Fin n))
    (ε : Fin n → Bool) (i : Fin n) (b : Bool) :
    (autEquiv.symm (π, ρ, ε)).val (nsymm i b) = nsymm (ρ i) (b ^^ ε i) := rfl

theorem autEquiv_symm_apply_apply
    (p : Equiv.Perm (Fin s) × Equiv.Perm (Fin n) × (Fin n → Bool))
    (a : IntegralAtom (Fin s) (Fin n)) :
    (autEquiv.symm p).val a = autFun p.1 p.2.1 p.2.2 a := rfl

/-- The symmetry group of `IntegralAtom (Fin s) (Fin n)` has `s ! * n ! * 2 ^ n` elements. -/
theorem card_aut (s n : ℕ) : Nat.card (Aut s n) = s.factorial * n.factorial * 2 ^ n := by
  rw [Nat.card_congr autEquiv, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_perm, Fintype.card_perm, Fintype.card_fin, Fintype.card_fin, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, mul_assoc]

end IntegralAtom

end FiniteIntegralRelationAlgebras.RelationAlgebra
