/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.BellmanArithmetic
public import LeanPool.Egyptian.BellmanFiniteness
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# The first entrance block for an improper rational target

The proof of Lemma 15 cuts at the first positive time for which the reciprocal
remainder exceeds the last denominator. The bounds here are proved in the
paper's unreduced natural-number coordinates.
-/

@[expose] public section

namespace Egyptian.Control

/-- A legal list whose first interior state is reached at its end. -/
inductive Entrance (σ : Convention) : State → List ℕ → Prop
  | last {s x} : Legal σ s x → Interior (step s x) → Entrance σ s [x]
  | more {s x xs} : Legal σ s x → ¬Interior (step s x) →
      Entrance σ (step s x) xs → Entrance σ s (x :: xs)

theorem Entrance.controls {σ s xs} (h : Entrance σ s xs) : Controls σ s xs := by
  induction h with
  | last hx _ => exact ⟨hx, trivial⟩
  | more hx _ _ ih => exact ⟨hx, ih⟩

theorem Entrance.end_inside {σ s xs} (h : Entrance σ s xs) :
    Interior (finish s xs) ∧ 2 ≤ (finish s xs).last := by
  induction h with
  | last hx hi => exact ⟨hi, hx.2.1⟩
  | more _ _ _ ih => exact ih

theorem Entrance.end_small {σ s xs} (h : Entrance σ s xs) :
    (finish s xs).p < (finish s xs).q := by
  obtain ⟨hi, hlast⟩ := h.end_inside
  exact (Nat.le_mul_of_pos_left _ (by omega : 0 < (finish s xs).last)).trans_lt hi

theorem split_first_entrance {σ s xs T} (ht : Terminal σ s xs T)
    (hne : xs ≠ []) :
    ∃ pre suf, xs = pre ++ suf ∧ Entrance σ s pre ∧ Terminal σ (finish s pre) suf T := by
  induction xs generalizing s with
  | nil => contradiction
  | cons x xs ih =>
    have hx := ht.1.1
    have ht' : Terminal σ (step s x) xs T := ⟨ht.1.2, ht.2⟩
    by_cases hi : Interior (step s x)
    · exact ⟨[x],xs,rfl,.last hx hi,ht'⟩
    · have hne' : xs ≠ [] := by
        rintro rfl
        have hstop := ht'.2
        change CanStop (step s x) T at hstop
        apply hi
        unfold Interior
        rw [hstop.2.2, Nat.mul_comm]
        exact Nat.mul_lt_mul_of_pos_left hstop.2.1 (Nat.sub_pos_of_lt hx.1)
      obtain ⟨pre,suf,he,hpre,hsuf⟩ := ih ht' hne'
      exact ⟨x :: pre,suf,by simp [he],.more hx hi hpre,hsuf⟩

/-- Every denominator in an entrance block of length r is strictly below 2^r/λ. -/
theorem Entrance.den_bound {σ s xs} (h : Entrance σ s xs) (d : ℕ) (hd : d ∈ xs) :
    s.p * d < 2 ^ xs.length * s.q := by
  induction h generalizing d with
  | @last s x hx hi =>
    have de : d = x := by simpa using hd
    subst d
    have hxpos : 0 < x := by have := hx.2.1; omega
    change x * (s.p*x-s.q) < s.q*x at hi
    rw [Nat.mul_comm x] at hi
    have drop : s.p*x-s.q < s.q := Nat.lt_of_mul_lt_mul_right hi
    have hlegal := hx.1
    simp only [List.length_singleton, pow_one]
    omega
  | @more s x xs hx hout hxs ih =>
    have hpos : 0 < x := by have := hx.2.1; omega
    have hu : s.q ≤ (step s x).p := by
      unfold Interior at hout
      change ¬x * (step s x).p < s.q*x at hout
      rw [Nat.mul_comm x] at hout
      exact Nat.le_of_mul_le_mul_right (Nat.le_of_not_gt hout) hpos
    have hv : s.p * x ≤ 2 * (step s x).p := by
      have hid := Nat.sub_add_cancel hx.1.le
      change s.q ≤ s.p*x-s.q at hu
      change s.p*x ≤ 2*(s.p*x-s.q)
      omega
    have lift_bound (y : ℕ) (hy : y ∈ xs) : s.p*y < 2^(x::xs).length*s.q := by
      have ht := ih y hy
      change (step s x).p * y < 2^xs.length * (s.q*x) at ht
      apply Nat.lt_of_mul_lt_mul_right (a := x)
      calc
        s.p*y*x = (s.p*x)*y := by ring
        _ ≤ (2*(step s x).p)*y := Nat.mul_le_mul_right y hv
        _ = 2*((step s x).p*y) := by ring
        _ < 2*(2^xs.length*(s.q*x)) := Nat.mul_lt_mul_of_pos_left ht (by decide)
        _ = (2^(x::xs).length*s.q)*x := by simp [pow_succ]; ring
    rcases List.mem_cons.mp hd with rfl | hd'
    · cases xs with
      | nil => cases hxs
      | cons y ys =>
        have hrel : d ≤ y := Convention.rel_le hxs.controls.1.2.2
        exact (Nat.mul_le_mul_left _ hrel).trans_lt (lift_bound y (by simp))
    · exact lift_bound d hd'

theorem Entrance.denominator_lt_pow_length {σ s xs} (he : Entrance σ s xs)
    (hbig : s.q < s.p) {d : ℕ} (hd : d ∈ xs) : d < 2 ^ xs.length := by
  have h := (Nat.mul_le_mul_right d hbig.le).trans_lt (he.den_bound d hd)
  rw [Nat.mul_comm s.q d] at h
  exact Nat.lt_of_mul_lt_mul_right h

theorem Entrance.denominator_product_bound {σ s xs} (he : Entrance σ s xs) (hbig : s.q < s.p) :
    (finish s xs).q ≤ s.q * 2^(xs.length^2) := by
  have hp := xs.prod_le_pow_length (2 ^ xs.length)
    (fun _ hd => (he.denominator_lt_pow_length hbig hd).le)
  rw [← pow_mul, ← sq] at hp
  rw [finish_denominator]
  exact Nat.mul_le_mul_left _ hp

private theorem bounded_lists_finite (M n : ℕ) :
    Set.Finite {xs : List ℕ | xs.length = n ∧ ∀ x ∈ xs, x ≤ M} := by
  induction n with
  | zero =>
    exact (Set.finite_singleton ([] : List ℕ)).subset (fun xs h => by simpa using h.1)
  | succ n ih =>
    have hs := (Set.finite_le_nat M).biUnion' (t := fun x _ =>
      List.cons x '' {xs : List ℕ | xs.length = n ∧ ∀ x ∈ xs, x ≤ M})
      (fun x _ => ih.image _)
    apply hs.subset
    rintro (_ | ⟨x,xs⟩) h
    · simp at h
    · exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr ⟨h.2 _ (by simp),
        xs, ⟨by simpa using h.1, fun d hd => h.2 d (by simp [hd])⟩, rfl⟩⟩

theorem finite_short_entrances (σ : Convention) (s : State) (hbig : s.q < s.p) (M : ℕ) :
    Set.Finite {xs | Entrance σ s xs ∧ xs.length < M} := by
  have hf := (Set.finite_lt_nat M).biUnion' (t := fun n _ =>
    {xs : List ℕ | xs.length = n ∧ ∀ x ∈ xs, x ≤ 2^M})
    (fun n _ => bounded_lists_finite (2^M) n)
  apply hf.subset
  intro xs h
  apply Set.mem_iUnion.mpr
  refine ⟨xs.length, Set.mem_iUnion.mpr ⟨h.2, rfl, ?_⟩⟩
  intro x hx
  exact (h.1.denominator_lt_pow_length hbig hx).le.trans
    (Nat.pow_le_pow_right (by decide) h.2.le)

theorem improper_nonempty {σ s xs T} (ht : Terminal σ s xs T)
    (hbig : s.q < s.p) : xs ≠ [] := by
  rintro rfl
  have hs : CanStop s T := ht.2
  have he := hs.2.2
  have hge : s.p ≤ s.p*T := Nat.le_mul_of_pos_right _ (by have := hs.1; omega)
  omega

end Egyptian.Control
