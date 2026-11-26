/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.Defs
import LeanPool.GraphMinor.GM09.Basic
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Tactic.Linarith

/-!
# The cyclic order on a finite indexed list

The presentations used in XVI (8.1), Claim (11), need cyclic orders
of the finitely many boundary vertices. Rotation of `Fin n` gives
the basic cyclic permutation. Increasing triples of indices occur
clockwise, including the return from the last index to the first.
-/

public section
namespace GraphMinor.GM16
open Set GraphMinor.GM09

/-- The cyclic permutation that takes each index to the next one. -/
@[expose] noncomputable def finCyclicPerm (n : ℕ) : CyclicPerm (Fin n) where
  bar := univ
  toFun := finRotate n
  finite_bar := finite_univ
  bijOn := (finRotate n).bijective.bijOn_univ
  single_orbit := by
    intro i _ j _
    let : NeZero n := i.neZero
    let k : Fin n := j - i
    refine ⟨k.val, ?_⟩
    rw [← finCycle_eq_finRotate_iterate (k := k)]
    change i + (j - i) = j
    simpa only [add_sub_assoc] using add_sub_cancel_left i j

private theorem finRotate_iterate_val {n : ℕ} (hn : 2 ≤ n) (i : Fin n) (k : ℕ) :
    ((finRotate n)^[k] i).val = (i.val + k) % n := by
  let : NeZero n := i.neZero
  induction k with
  | zero => simp only [Function.iterate_zero, id_eq, Nat.add_zero, Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', finRotate_apply, Fin.val_add, Fin.val_one',
      Nat.mod_eq_of_lt (show 1 < n by omega), ih, Nat.mod_add_mod]
    congr 1

/-- Before wrapping around, rotation has visited no index beyond its
current increasing interval. -/
private theorem finCyclicPerm_firstHit_forward {n : ℕ} {i j k : Fin n}
    (hij : i < j) (hk : k < i ∨ j < k) :
    (finCyclicPerm n).FirstHitIn {i, j, k} i j := by
  have hn : 2 ≤ n := by have := j.isLt; omega
  refine ⟨j.val - i.val, by omega, ?_, Or.inr (Or.inl rfl), ?_⟩
  · apply Fin.ext
    rw [show (finCyclicPerm n).toFun = finRotate n from rfl, finRotate_iterate_val hn]
    have heq : i.val + (j.val - i.val) = j.val := by omega
    rw [heq, Nat.mod_eq_of_lt j.isLt]
  · intro r hr hrlt hmem
    have hval := finRotate_iterate_val hn i r
    have hsmall : i.val + r < n := by have := j.isLt; omega
    rw [Nat.mod_eq_of_lt hsmall] at hval
    change ((finRotate n)^[r] i) ∈ ({i, j, k} : Set (Fin n)) at hmem
    rcases hmem with heq | heq | heq
    · have he := congrArg Fin.val heq
      omega
    · have he := congrArg Fin.val heq
      omega
    · have he := congrArg Fin.val heq
      rcases hk with hk | hk <;> omega

private theorem finCyclicPerm_firstHit_wrap {n : ℕ} {i j k : Fin n}
    (hij : i < j) (hjk : j < k) :
    (finCyclicPerm n).FirstHitIn {i, j, k} k i := by
  have hn : 2 ≤ n := by have := k.isLt; omega
  refine ⟨n - k.val + i.val, by omega, ?_, Or.inl rfl, ?_⟩
  · apply Fin.ext
    rw [show (finCyclicPerm n).toFun = finRotate n from rfl, finRotate_iterate_val hn]
    have heq : k.val + (n - k.val + i.val) = n + i.val := by have := k.isLt; omega
    rw [heq, Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt i.isLt]
    exact Nat.mod_eq_of_lt i.isLt
  · intro r hr hrlt hmem
    have hval := finRotate_iterate_val hn k r
    change ((finRotate n)^[r] k) ∈ ({i, j, k} : Set (Fin n)) at hmem
    by_cases hsmall : k.val + r < n
    · rw [Nat.mod_eq_of_lt hsmall] at hval
      rcases hmem with heq | heq | heq <;> have he := congrArg Fin.val heq <;> omega
    · have hge : n ≤ k.val + r := by omega
      have hrem : k.val + r - n < n := by have := i.isLt; have := k.isLt; omega
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hrem] at hval
      rcases hmem with heq | heq | heq <;> have he := congrArg Fin.val heq <;> omega

private theorem finCyclicPerm_clockwise3_of_increasing {n : ℕ} {i j k : Fin n}
    (hij : i < j) (hjk : j < k) : (finCyclicPerm n).IsClockwise3 i j k := by
  rw [CyclicPerm.isClockwise3_iff]
  have hSet : ({j, k, i} : Set (Fin n)) = {i, j, k} := by
    ext x
    simp only [mem_insert_iff, mem_singleton_iff]
    tauto
  refine ⟨ne_of_lt hij, ne_of_lt (hij.trans hjk), ne_of_lt hjk,
    mem_univ _, mem_univ _, mem_univ _, finCyclicPerm_firstHit_forward hij (Or.inr hjk), ?_,
    finCyclicPerm_firstHit_wrap hij hjk⟩
  simpa only [hSet] using finCyclicPerm_firstHit_forward hjk (Or.inl hij)

/-- Clockwise triples for the finite rotation are precisely the three
cyclic rotations of an increasing triple. -/
theorem finCyclicPerm_clockwise3_iff {n : ℕ} {i j k : Fin n} :
    (finCyclicPerm n).IsClockwise3 i j k ↔
      (i < j ∧ j < k) ∨ (j < k ∧ k < i) ∨ (k < i ∧ i < j) := by
  constructor
  · intro hCW
    have hNe := (CyclicPerm.isClockwise3_iff.mp hCW)
    have hNoRev : ¬ (finCyclicPerm n).IsClockwise3 i k j := by
      intro hRev
      rcases (finCyclicPerm n).isClockwise3_trichotomy (mem_univ i) (mem_univ j) (mem_univ k)
        hNe.1 hNe.2.1 hNe.2.2.1 with h | h
      · exact h.2 hRev
      · exact h.2 hCW
    by_cases h₁ : i < j ∧ j < k
    · exact Or.inl h₁
    by_cases h₂ : j < k ∧ k < i
    · exact Or.inr (Or.inl h₂)
    by_cases h₃ : k < i ∧ i < j
    · exact Or.inr (Or.inr h₃)
    have hRevOrder : (i < k ∧ k < j) ∨ (k < j ∧ j < i) ∨ (j < i ∧ i < k) := by
      have hi := hNe.1
      have hj := hNe.2.1
      have hk := hNe.2.2.1
      omega
    apply False.elim
    apply hNoRev
    rcases hRevOrder with h | h | h
    · exact finCyclicPerm_clockwise3_of_increasing h.1 h.2
    · exact (finCyclicPerm n).isClockwise3_rotate
        ((finCyclicPerm n).isClockwise3_rotate (finCyclicPerm_clockwise3_of_increasing h.1 h.2))
    · exact (finCyclicPerm n).isClockwise3_rotate (finCyclicPerm_clockwise3_of_increasing h.1 h.2)
  · rintro (h | h | h)
    · exact finCyclicPerm_clockwise3_of_increasing h.1 h.2
    · exact (finCyclicPerm n).isClockwise3_rotate
        ((finCyclicPerm n).isClockwise3_rotate (finCyclicPerm_clockwise3_of_increasing h.1 h.2))
    · exact (finCyclicPerm n).isClockwise3_rotate (finCyclicPerm_clockwise3_of_increasing h.1 h.2)

/-- Increasing angles spanning less than one turn realize the finite
rotation as the natural cyclic order of the boundary points. -/
theorem finCyclicPerm_agrees_of_angles {S : Type*} [TopologicalSpace S]
    {F : Set S} (φ : Circle ≃ₜ F) {n : ℕ} (hn : 0 < n)
    (ν : Fin n → S) (τ : Fin n → ℝ) (hτ : StrictMono τ)
    (hTurn : ∀ i, τ i < τ ⟨0, hn⟩ + 2 * Real.pi)
    (hν : ∀ i, (φ (Circle.exp (τ i))).val = ν i) :
    AgreesWithOArcHomeo ν (finCyclicPerm n) F φ := by
  have hBase : ∀ i, τ ⟨0, hn⟩ ≤ τ i := fun i =>
    hτ.monotone (show (⟨0, hn⟩ : Fin n) ≤ i from Nat.zero_le i.val)
  have hWrap : ∀ i j, τ i < τ j + 2 * Real.pi := by
    intro i j
    have hi := hTurn i
    have hj := hBase j
    linarith
  have hPeriod : ∀ t : ℝ, Circle.exp (t + 2 * Real.pi) = Circle.exp t := by
    intro t
    rw [Circle.exp_add, Circle.exp_two_pi, mul_one]
  have hνWrap : ∀ i, (φ (Circle.exp (τ i + 2 * Real.pi))).val = ν i := by
    intro i
    rw [hPeriod]
    exact hν i
  refine ⟨fun i _ => (hν i) ▸ (φ (Circle.exp (τ i))).property, ?_⟩
  intro i j k hCW
  rcases finCyclicPerm_clockwise3_iff.mp hCW with h | h | h
  · exact ⟨τ i, τ j, τ k, hτ h.1, hτ h.2, hWrap k i, hν i, hν j, hν k⟩
  · refine ⟨τ i, τ j + 2 * Real.pi, τ k + 2 * Real.pi,
      hWrap i j, ?_, ?_, hν i, hνWrap j, hνWrap k⟩
    · linarith [hτ h.1]
    · linarith [hτ h.2]
  · refine ⟨τ i, τ j, τ k + 2 * Real.pi, hτ h.2,
      hWrap j k, ?_, hν i, hν j, hνWrap k⟩
    linarith [hτ h.1]

end GraphMinor.GM16
