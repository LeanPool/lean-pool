/-
Copyright (c) 2026 David Turturean. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
module

-- Adapted for Lean Pool’s module system and pinned Mathlib.

public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Ring.Basic
public import LeanPool.AaronsonAmbainis.DetLow.Basic

/-!
# DetLow: the number of ones of `g` is `2 e_j + b_j(g)`

This is a step of the proof of Lemma 3.6 of the paper.
The ones of `g` split into the upper endpoints `Up g j` of the `j`-edges inside the ones,
the lower endpoints `Dn g j` (in bijection with `Up g j` by flipping `j`), and the points
`Bd g j` whose `j`-neighbour is a zero of `g` (there are `bdry g j` of them).
-/

@[expose] public section

namespace AaronsonAmbainis
namespace DetLow

open Finset MvPolynomial

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- The lower endpoints of the `j`-edges inside the ones of `g`. -/
def Dn (g : Cube ι → Bool) (j : ι) : Finset (Ones g) :=
  univ.filter fun x => x.1 j = false ∧ g (flipSet x.1 {j}) = true

/-- The ones of `g` whose `j`-neighbour is a zero of `g`. -/
def Bd (g : Cube ι → Bool) (j : ι) : Finset (Ones g) :=
  univ.filter fun x => g (flipSet x.1 {j}) = false

theorem mem_Dn {g : Cube ι → Bool} {j : ι} {x : Ones g} :
    x ∈ Dn g j ↔ x.1 j = false ∧ g (flipSet x.1 {j}) = true := by
  simp [Dn]

theorem mem_Bd {g : Cube ι → Bool} {j : ι} {x : Ones g} :
    x ∈ Bd g j ↔ g (flipSet x.1 {j}) = false := by
  simp [Bd]

theorem card_Dn (g : Cube ι → Bool) (j : ι) : (Dn g j).card = (Up g j).card := by
  apply Finset.card_bij
    (fun x hx => (⟨flipSet x.1 {j}, (mem_Dn.mp hx).2⟩ : Ones g))
  · intro x hx
    rw [mem_Up]
    have hx' := mem_Dn.mp hx
    simp [hx'.1, x.2]
  · intro x hx y hy hxy
    have h := congrArg (fun w : Ones g => flipSet w.1 {j}) hxy
    simp only [flipSet_flipSet_singleton] at h
    exact Subtype.ext h
  · intro y hy
    rw [mem_Up] at hy
    refine ⟨⟨flipSet y.1 {j}, hy.2⟩, ?_, ?_⟩
    · rw [mem_Dn]
      simp [hy.1, y.2]
    · exact Subtype.ext (by simp)

theorem card_Bd (g : Cube ι → Bool) (j : ι) : (Bd g j).card = bdry g j := by
  unfold bdry
  apply Finset.card_bij (fun x _ => x.1)
  · intro x hx
    have h := mem_Bd.mp hx
    simp [x.2, h]
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro b hb
    have hb' : g b = true ∧ g (flipSet b {j}) = false := by simpa using hb
    exact ⟨⟨b, hb'.1⟩, mem_Bd.mpr hb'.2, rfl⟩

/-- The number of ones of `g` is `2 e_j + b_j(g)` (proof of Lemma 3.6 of the paper). -/
theorem card_ones_eq (g : Cube ι → Bool) (j : ι) :
    Fintype.card (Ones g) = 2 * (Up g j).card + bdry g j := by
  have h3 : (univ : Finset (Ones g)) = (Up g j ∪ Dn g j) ∪ Bd g j := by
    ext x
    simp only [mem_univ, mem_union, mem_Up, mem_Dn, mem_Bd, true_iff]
    cases h : x.1 j <;> cases h' : g (flipSet x.1 {j}) <;> simp
  have h4 : Disjoint (Up g j) (Dn g j) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have h1 := (mem_Up.mp hx).1
    have h2 := (mem_Dn.mp hx').1
    rw [h1] at h2
    exact Bool.noConfusion h2
  have h5 : Disjoint (Up g j ∪ Dn g j) (Bd g j) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hb := mem_Bd.mp hx'
    rw [Finset.mem_union, mem_Up, mem_Dn] at hx
    rcases hx with hx | hx
    · rw [hx.2] at hb
      exact Bool.noConfusion hb
    · rw [hx.2] at hb
      exact Bool.noConfusion hb
  rw [← Finset.card_univ, h3, Finset.card_union_of_disjoint h5,
    Finset.card_union_of_disjoint h4, card_Dn, card_Bd]
  ring

end DetLow
end AaronsonAmbainis
