/-
Copyright (c) 2026 Vjekoslav Kovač, Quanyu Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vjekoslav Kovač, Quanyu Tang
-/

module

public import LeanPool.Egyptian.Bellman
public import Mathlib.Data.Set.Finite.Lattice

/-!
# Finitely many blocks of given length and final numerator

The finiteness step of Kovač–Tang's Bellman attainment lemma, §3.3.
We prove the bound at each recursive call directly in the cleared integer
coordinates, without computing a rational floor.
-/

@[expose] public section

namespace Egyptian.Control

/-- Bound the first denominator of a nonempty block. Reapplying the same
inequality at its successor bounds each subsequent choice. -/
theorem head_bound {σ : Convention} {s : State} {x : ℕ} {xs : List ℕ}
    (hc : Controls σ s (x :: xs)) :
    s.p * x ≤ (x :: xs).length * s.q + (finish s (x :: xs)).p := by
  induction xs generalizing s x with
  | nil =>
    have hl := hc.1.1.le
    change s.p * x ≤ 1 * s.q + (s.p * x - s.q)
    omega
  | cons y ys ih =>
    let d := (finish (step s x) (y :: ys)).p
    have hx : 0 < x := by have := hc.1.2.1; omega
    have hxy : x ≤ y := Convention.rel_le hc.2.1.2.2
    have htail := ih hc.2
    change (s.p * x - s.q) * y ≤ (y :: ys).length * (s.q * x) + d at htail
    have hsmall := (Nat.mul_le_mul_left (s.p * x - s.q) hxy).trans htail
    have hid := congrArg (· * x) (Nat.sub_add_cancel hc.1.1.le)
    have hd : d ≤ d * x := Nat.le_mul_of_pos_right _ hx
    change s.p * x ≤ ((y :: ys).length + 1) * s.q + d
    apply Nat.le_of_mul_le_mul_right (c := x) _ hx
    nlinarith only [hsmall, hid, hd]

/-- An explicit finite tree: when the length and final cleared numerator
are fixed, the set of legal ordered control lists is finite. -/
theorem finite_blocks (σ : Convention) (n d : ℕ) (s : State) (hv : Valid s) :
    Set.Finite {xs : List ℕ | xs.length = n ∧ Controls σ s xs ∧ (finish s xs).p = d} := by
  induction n generalizing s with
  | zero =>
    apply (Set.finite_singleton ([] : List ℕ)).subset
    intro xs h
    simpa using h.1
  | succ n ih =>
    let X : Set ℕ := {x | x ≤ (n+1) * s.q + d ∧ Legal σ s x}
    have hX : X.Finite := (Set.finite_le_nat _).subset (fun _ hx => hx.1)
    have hf := hX.biUnion' (t := fun x _ =>
      List.cons x '' {ys : List ℕ | ys.length = n ∧ Controls σ (step s x) ys ∧
        (finish (step s x) ys).p = d}) (fun x hx =>
        (ih (step s x) (step_valid hv hx.2)).image _)
    apply hf.subset
    intro xs h
    obtain ⟨hlen, hc, hd⟩ := h
    cases xs with
    | nil => simp at hlen
    | cons x xs =>
      have hh := head_bound hc
      rw [hlen, hd] at hh
      have hfirst : x ≤ (n+1) * s.q + d :=
        (Nat.le_mul_of_pos_left x hv.1).trans hh
      exact Set.mem_iUnion.mpr ⟨x, Set.mem_iUnion.mpr
        ⟨⟨hfirst, hc.1⟩, xs, ⟨by simpa using hlen, hc.2, hd⟩, rfl⟩⟩

end Egyptian.Control
