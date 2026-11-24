/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import Mathlib.Data.Set.Card
public import Mathlib.Order.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# The two ordered contacts on a long edge

For VII (4.6), page 225, enumerate the contacts along an edge parameter.
Choose contact `μ + 1` from the start and contact `μ + 1` from the end.
Each closed linking interval has `μ + 1` contacts, and the open middle
interval has at least `w`. This finite order count also permits a loop's
two parameter ends to represent the same point of the surface.
-/

public section

namespace GraphMinor.GM07

open Set

private theorem ncard_contacts_Iic {α : Type*} [LinearOrder α] {r : ℕ}
    (f : Fin r ↪o α) (i : Fin r) :
    (range f ∩ Iic (f i)).ncard = i.val + 1 := by
  have heq : range f ∩ Iic (f i) = f '' Iic i := by
    ext x
    constructor
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, f.le_iff_le.mp hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, f.monotone hj⟩
  rw [heq, ncard_image_of_injective _ f.injective]
  simp [← Finset.coe_Iic]

private theorem ncard_contacts_Ici {α : Type*} [LinearOrder α] {r : ℕ}
    (f : Fin r ↪o α) (i : Fin r) :
    (range f ∩ Ici (f i)).ncard = r - i.val := by
  have heq : range f ∩ Ici (f i) = f '' Ici i := by
    ext x
    constructor
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, f.le_iff_le.mp hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, f.monotone hj⟩
  rw [heq, ncard_image_of_injective _ f.injective]
  simp [← Finset.coe_Ici]

private theorem ncard_contacts_Ioo {α : Type*} [LinearOrder α] {r : ℕ}
    (f : Fin r ↪o α) (i j : Fin r) :
    (range f ∩ Ioo (f i) (f j)).ncard = j.val - i.val - 1 := by
  have heq : range f ∩ Ioo (f i) (f j) = f '' Ioo i j := by
    ext x
    constructor
    · rintro ⟨⟨k, rfl⟩, hk⟩
      exact ⟨k, ⟨f.lt_iff_lt.mp hk.1, f.lt_iff_lt.mp hk.2⟩, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨⟨k, rfl⟩, ⟨f.strictMono hk.1, f.strictMono hk.2⟩⟩
  rw [heq, ncard_image_of_injective _ f.injective]
  simp [← Finset.coe_Ioo]

/-- The contact indices `μ + 1` and `r - μ` used to define `W(e)` in
VII (4.6), page 225, with the linking and central contact counts. -/
theorem exists_ordered_contact_cuts {α : Type*} [LinearOrder α]
    {T : Set α} (hT : T.Finite) {μ w : ℕ} (hcard : 2 * μ + w + 2 ≤ T.ncard) :
    ∃ s ∈ T, ∃ t ∈ T, s < t ∧
      (T ∩ Iic s).ncard = μ + 1 ∧ (T ∩ Ici t).ncard = μ + 1 ∧
      w ≤ (T ∩ Ioo s t).ncard := by
  classical
  let r := hT.toFinset.card
  let f : Fin r ↪o α := hT.toFinset.orderEmbOfFin rfl
  have hrange : range f = T := by simp [f]
  have hr : 2 * μ + w + 2 ≤ r := by
    rwa [Set.ncard_eq_toFinset_card T hT] at hcard
  let i : Fin r := ⟨μ, by omega⟩
  let j : Fin r := ⟨r - μ - 1, by omega⟩
  have hij : i < j := by change μ < r - μ - 1; omega
  refine ⟨f i, hrange ▸ mem_range_self i, f j, hrange ▸ mem_range_self j,
    f.strictMono hij, ?_, ?_, ?_⟩
  · rw [← hrange, ncard_contacts_Iic]
  · rw [← hrange, ncard_contacts_Ici]
    dsimp [j]
    omega
  · rw [← hrange, ncard_contacts_Ioo]
    dsimp [i, j]
    omega

end GraphMinor.GM07
