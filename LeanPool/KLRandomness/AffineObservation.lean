/-
Copyright (c) 2026 Bjørn Kjos-Hanssen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bjørn Kjos-Hanssen
-/

-- Modified for Lean Pool.

module

public import LeanPool.KLRandomness.Affine
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Positivity

/-!
# Counting affine constraints after a fixed observation

The observed coordinates form an arbitrary decidable subset of a finite index
set. Extending the unread coordinates by zero defines the remaining-column
linear map. If this map is surjective, every residual syndrome has the same
number of completions. An arbitrary condition on the observed coordinates
can be retained throughout, so earlier disjoint constraints and transcript
conditions can be included in the counting identity.
-/

@[expose] public section

namespace Klr.AffineObservation

variable {ι : Type*}

/-- The values on the observed coordinates. -/
def observedPart (O : Set ι) (x : ι → ZMod 2) : O → ZMod 2 := fun i => x i.val

/-- The values on the unread coordinates. -/
def unreadPart (O : Set ι) (x : ι → ZMod 2) : {i // i ∉ O} → ZMod 2 :=
  fun i => x i.val

/-- Extend an assignment on observed coordinates by zero elsewhere. -/
def extendObserved (O : Set ι) [DecidablePred (· ∈ O)] :
    (O → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) where
  toFun o i := if h : i ∈ O then o ⟨i, h⟩ else 0
  map_add' a b := by ext i; by_cases h : i ∈ O <;> simp [h]
  map_smul' a b := by ext i; by_cases h : i ∈ O <;> simp [h]

/-- Extend an assignment on unread coordinates by zero on the observed coordinates. -/
def extendUnread (O : Set ι) [DecidablePred (· ∈ O)] :
    ({i // i ∉ O} → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) where
  toFun u i := if h : i ∈ O then 0 else u ⟨i, h⟩
  map_add' a b := by ext i; by_cases h : i ∈ O <;> simp [h]
  map_smul' a b := by ext i; by_cases h : i ∈ O <;> simp [h]

/-- Combine observed and unread assignments. -/
def merge (O : Set ι) [DecidablePred (· ∈ O)] (o : O → ZMod 2)
    (u : {i // i ∉ O} → ZMod 2) : ι → ZMod 2 :=
  extendObserved O o + extendUnread O u

@[simp] theorem observedPart_merge (O : Set ι) [DecidablePred (· ∈ O)]
    (o : O → ZMod 2) (u : {i // i ∉ O} → ZMod 2) :
    observedPart O (merge O o u) = o := by
  funext i
  simp [observedPart, merge, extendObserved, extendUnread, i.property]

@[simp] theorem unreadPart_merge (O : Set ι) [DecidablePred (· ∈ O)]
    (o : O → ZMod 2) (u : {i // i ∉ O} → ZMod 2) :
    unreadPart O (merge O o u) = u := by
  funext i
  simp [unreadPart, merge, extendObserved, extendUnread, i.property]

@[simp] theorem merge_parts (O : Set ι) [DecidablePred (· ∈ O)] (x : ι → ZMod 2) :
    merge O (observedPart O x) (unreadPart O x) = x := by
  funext i
  by_cases h : i ∈ O <;>
    simp [merge, observedPart, unreadPart, extendObserved, extendUnread, h]

/-- Splitting all coordinates into the observed and unread parts is a bijection. -/
def splitEquiv (O : Set ι) [DecidablePred (· ∈ O)] :
    (ι → ZMod 2) ≃ (O → ZMod 2) × ({i // i ∉ O} → ZMod 2) where
  toFun x := (observedPart O x, unreadPart O x)
  invFun p := merge O p.1 p.2
  left_inv := merge_parts O
  right_inv p := by simp

/-- The remaining-column map after the coordinates in `O` have been observed. -/
def unreadMap {r : ℕ} (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] :
    ({i // i ∉ O} → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2) :=
  D.comp (extendUnread O)

/-- A background condition that depends only on the observed coordinates. -/
def background (O : Set ι) (P : (O → ZMod 2) → Prop) : Set (ι → ZMod 2) :=
  {x | P (observedPart O x)}

/-- The background condition together with a specified affine syndrome. -/
def joint {r : ℕ} (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) (P : (O → ZMod 2) → Prop) (y : Fin r → ZMod 2) : Set (ι → ZMod 2) :=
  {x | P (observedPart O x) ∧ D x = y}

/-- With the observed part fixed, the only equation left is the residual syndrome equation. -/
def jointEquivSigma {r : ℕ} (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (P : (O → ZMod 2) → Prop)
    (y : Fin r → ZMod 2) :
    joint D O P y ≃ Σ o : {o : O → ZMod 2 // P o},
      Affine.Fiber (unreadMap D O) (y - D (extendObserved O o.val)) where
  toFun x := ⟨⟨observedPart O x.val, x.property.1⟩, ⟨unreadPart O x.val, by
    change D (extendUnread O (unreadPart O x.val)) =
      y - D (extendObserved O (observedPart O x.val))
    apply eq_sub_iff_add_eq.mpr
    rw [← map_add, add_comm]
    change D (merge O (observedPart O x.val) (unreadPart O x.val)) = y
    rw [merge_parts]
    exact x.property.2⟩⟩
  invFun p := ⟨merge O p.1.val p.2.val, by
    constructor
    · simpa using p.1.property
    · dsimp [merge]
      rw [map_add]
      change D (extendObserved O p.1.val) + unreadMap D O p.2.val = y
      rw [p.2.property]
      abel⟩
  left_inv x := by
    apply Subtype.ext
    exact merge_parts O x.val
  right_inv p := by
    rcases p with ⟨⟨o, ho⟩, ⟨u, hu⟩⟩
    apply Sigma.ext (Subtype.ext (observedPart_merge O o u))
    apply (Subtype.heq_iff_coe_eq (fun v => by simp only [observedPart_merge])).mpr
    exact unreadPart_merge O o u

/-- Background assignments are freely parametrized by their unread coordinates. -/
def backgroundEquivProd (O : Set ι) [DecidablePred (· ∈ O)]
    (P : (O → ZMod 2) → Prop) :
    background O P ≃ {o : O → ZMod 2 // P o} × ({i // i ∉ O} → ZMod 2) where
  toFun x := (⟨observedPart O x.val, x.property⟩, unreadPart O x.val)
  invFun p := ⟨merge O p.1.val p.2, by simpa [background] using p.1.property⟩
  left_inv x := by apply Subtype.ext; exact merge_parts O x.val
  right_inv p := by rcases p with ⟨⟨o, ho⟩, u⟩; simp

/-- An assignment vanishing on the observed coordinates is entirely its unread extension. -/
theorem extendUnread_unreadPart_of_observed_zero (O : Set ι)
    [DecidablePred (· ∈ O)] (x : ι → ZMod 2) (hx : observedPart O x = 0) :
    extendUnread O (unreadPart O x) = x := by
  have h := merge_parts O x
  dsimp [merge] at h
  rw [hx, map_zero, zero_add] at h
  exact h

/-- To prove surjectivity of the remaining-column map, it suffices to lift every syndrome
through assignments supported on unread coordinates. This allows a smaller block to be
embedded in a larger finite ambient coordinate set. -/
theorem unreadMap_surjective_of_supported_lift {α : Type*} {r : ℕ}
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (L : α → (ι → ZMod 2))
    (hzero : ∀ a, observedPart O (L a) = 0)
    (hsurj : Function.Surjective (fun a => D (L a))) :
    Function.Surjective (unreadMap D O) := by
  intro y
  obtain ⟨a, ha⟩ := hsurj y
  refine ⟨unreadPart O (L a), ?_⟩
  change D (extendUnread O (unreadPart O (L a))) = y
  rw [extendUnread_unreadPart_of_observed_zero O (L a) (hzero a)]
  exact ha

/-- A surjective remaining-column map has at most as many rows as unread coordinates. -/
theorem unread_rank_le [Fintype ι] {r : ℕ}
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)]
    (hD : Function.Surjective (unreadMap D O)) :
    r ≤ Fintype.card {i // i ∉ O} := by
  simpa using LinearMap.finrank_le_finrank_of_surjective hD

/-- Each admissible observed assignment contributes the same number of completions. -/
theorem card_joint [Fintype ι] {r : ℕ}
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (P : (O → ZMod 2) → Prop)
    (y : Fin r → ZMod 2) (hD : Function.Surjective (unreadMap D O)) :
    Nat.card (joint D O P y) = Nat.card {o : O → ZMod 2 // P o} *
      2 ^ (Fintype.card {i // i ∉ O} - r) := by
  classical
  let : ∀ o : {o : O → ZMod 2 // P o},
      Finite (Affine.Fiber (unreadMap D O) (y - D (extendObserved O o.val))) :=
    fun _ => by unfold Affine.Fiber; infer_instance
  rw [Nat.card_congr (jointEquivSigma D O P y), Nat.card_sigma]
  have hcard (o : {o : O → ZMod 2 // P o}) :
      Nat.card (Affine.Fiber (unreadMap D O) (y - D (extendObserved O o.val))) =
        2 ^ (Fintype.card {i // i ∉ O} - r) := by
    simpa using Affine.card_fiber_of_surjective (unreadMap D O) hD
      (y - D (extendObserved O o.val))
  simp_rw [hcard]
  simp [Nat.card_eq_fintype_card]

/-- The unread coordinates remain unrestricted by a condition on observed values alone. -/
theorem card_background [Fintype ι] (O : Set ι) [DecidablePred (· ∈ O)]
    (P : (O → ZMod 2) → Prop) :
    Nat.card (background O P) = Nat.card {o : O → ZMod 2 // P o} *
      2 ^ Fintype.card {i // i ∉ O} := by
  rw [Nat.card_congr (backgroundEquivProd O P), Nat.card_prod]
  simp [Nat.card_fun, Nat.card_eq_fintype_card]

/-- Imposing any one syndrome keeps exactly a `2⁻ʳ` fraction of every observed-coordinate
background event. The identity remains valid when the background has no assignments. -/
theorem card_joint_mul_pow_eq_card_background [Finite ι] {r : ℕ}
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (P : (O → ZMod 2) → Prop)
    (y : Fin r → ZMod 2) (hD : Function.Surjective (unreadMap D O)) :
    Nat.card (joint D O P y) * 2 ^ r = Nat.card (background O P) := by
  classical
  let _ := Fintype.ofFinite ι
  rw [card_joint D O P y hD, card_background O P, mul_assoc, ← pow_add,
    Nat.sub_add_cancel (unread_rank_le D O hD)]

/-- The assignments extending a specified observation and realizing a syndrome. -/
def observedFiber {r : ℕ} (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) (o : O → ZMod 2) (y : Fin r → ZMod 2) : Set (ι → ZMod 2) :=
  joint D O (fun a => a = o) y

/-- A fixed observation leaves exactly `2^(number of unread coordinates - r)` completions. -/
theorem card_observedFiber [Fintype ι] {r : ℕ}
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (o : O → ZMod 2) (y : Fin r → ZMod 2)
    (hD : Function.Surjective (unreadMap D O)) :
    Nat.card (observedFiber D O o y) = 2 ^ (Fintype.card {i // i ∉ O} - r) := by
  rw [observedFiber, card_joint D O (fun a => a = o) y hD]
  have hcard : Nat.card {a : O → ZMod 2 // a = o} = 1 := Nat.card_unique
  rw [hcard, one_mul]

/-- A fixed observation has one freely chosen bit per unread coordinate. -/
theorem card_fixedObservation [Fintype ι] (O : Set ι) [DecidablePred (· ∈ O)]
    (o : O → ZMod 2) :
    Nat.card (background O (fun a => a = o)) = 2 ^ Fintype.card {i // i ∉ O} := by
  rw [card_background O (fun a => a = o)]
  have hcard : Nat.card {a : O → ZMod 2 // a = o} = 1 := Nat.card_unique
  rw [hcard, one_mul]

/-- Within the extensions of any fixed observation, each syndrome has the same fraction `2⁻ʳ`. -/
theorem observedFiber_fraction [Finite ι] {r : ℕ}
    (D : (ι → ZMod 2) →ₗ[ZMod 2] (Fin r → ZMod 2))
    (O : Set ι) [DecidablePred (· ∈ O)] (o : O → ZMod 2) (y : Fin r → ZMod 2)
    (hD : Function.Surjective (unreadMap D O)) :
    (Nat.card (observedFiber D O o y) : ℚ) /
      Nat.card (background O (fun a => a = o)) = (1 / 2 : ℚ) ^ r := by
  classical
  let _ := Fintype.ofFinite ι
  rw [card_observedFiber D O o y hD, card_fixedObservation O o]
  push_cast
  have hp : (2 : ℚ) ^ Fintype.card {i // i ∉ O} =
      2 ^ (Fintype.card {i // i ∉ O} - r) * 2 ^ r := by
    rw [← pow_add, Nat.sub_add_cancel (unread_rank_le D O hD)]
  rw [hp, div_mul_eq_div_div, div_self (by positivity :
    (2 : ℚ) ^ (Fintype.card {i // i ∉ O} - r) ≠ 0)]
  simp

end Klr.AffineObservation
