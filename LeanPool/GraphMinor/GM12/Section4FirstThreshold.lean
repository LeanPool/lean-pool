/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

import Mathlib.Data.List.Basic

/-!
# First edges reaching a distance threshold

XII (4.3), claim (2), page 250, takes the first edge of a path
whose distance from the chosen edge reaches a given threshold.
Consecutive path edges have distance at most four. Thus the first
crossing overshoots the threshold by at most three. The list lemma
below records precisely this first-crossing argument, with a bound
on each successive value.
-/

public section

namespace GraphMinor.GM12

/-- The first-crossing argument of XII (4.3), claim (2), page 250.
The initial value is at most the threshold plus three, and each following value increases
by at most four. -/
theorem exists_first_threshold_edge {α : Type*} (value : α → ℕ)
    (i : ℕ) :
    ∀ (l : List α),
      (∀ a, l.head? = some a → value a ≤ i + 3) →
      (∀ (p : List α) a b (q : List α), l = p ++ a :: b :: q →
        value b ≤ value a + 4) →
      (∃ a ∈ l, i ≤ value a) →
      ∃ (p : List α) (a : α) (q : List α), l = p ++ a :: q ∧
        (∀ b ∈ p, value b < i) ∧ i ≤ value a ∧ value a ≤ i + 3 := by
  intro l
  induction l with
  | nil =>
    intro _ _ hex
    obtain ⟨a, ha, _⟩ := hex
    exact False.elim (List.not_mem_nil ha)
  | cons a l ih =>
    intro hhead hstep hex
    by_cases ha : i ≤ value a
    · exact ⟨[], a, l, rfl, by simp, ha, by have h := hhead a rfl; omega⟩
    have halt : value a < i := Nat.lt_of_not_ge ha
    have htail : ∃ b ∈ l, i ≤ value b := by
      obtain ⟨b, hb, hib⟩ := hex
      rcases List.mem_cons.mp hb with rfl | hb
      · exact False.elim (ha hib)
      · exact ⟨b, hb, hib⟩
    -- If the next edge crosses, use its predecessor. Otherwise recurse.
    cases l with
    | nil =>
      obtain ⟨b, hb, _⟩ := htail
      exact False.elim (List.not_mem_nil hb)
    | cons b r =>
      by_cases hb : i ≤ value b
      · refine ⟨[a], b, r, rfl, ?_, hb, ?_⟩
        · intro c hc
          exact (List.mem_singleton.mp hc) ▸ halt
        · have h := hstep [] a b r rfl
          omega
      · have hhead' : ∀ c, (b :: r).head? = some c → value c ≤ i + 3 := by
          intro c hc
          have hbc : b = c := Option.some.inj hc
          subst c
          have h := Nat.lt_of_not_ge hb
          omega
        have hstep' : ∀ (p : List α) c d (q : List α),
            b :: r = p ++ c :: d :: q → value d ≤ value c + 4 := by
          intro p c d q heq
          exact hstep (a :: p) c d q (congrArg (List.cons a) heq)
        obtain ⟨p, c, q, heq, hp, hic, hci⟩ := ih hhead' hstep' htail
        refine ⟨a :: p, c, q, congrArg (List.cons a) heq, ?_, hic, hci⟩
        intro d hd
        rcases List.mem_cons.mp hd with rfl | hd
        · exact halt
        · exact hp d hd

/-- XII (4.3), claim (2), with the initial distance bound four. -/
theorem exists_first_threshold_edge_of_head_le_four {α : Type*} (value : α → ℕ)
    {i : ℕ} (hi : 1 ≤ i) (l : List α)
    (hhead : ∀ a, l.head? = some a → value a ≤ 4)
    (hstep : ∀ (p : List α) a b (q : List α), l = p ++ a :: b :: q →
      value b ≤ value a + 4)
    (hex : ∃ a ∈ l, i ≤ value a) :
    ∃ (p : List α) (a : α) (q : List α), l = p ++ a :: q ∧
      (∀ b ∈ p, value b < i) ∧ i ≤ value a ∧ value a ≤ i + 3 := by
  apply exists_first_threshold_edge value i l
  · intro a ha
    have h := hhead a ha
    omega
  · exact hstep
  · exact hex

/-- XII (4.3), claim (3), page 250: thresholds separated by
`k + 7` yield edges at distance at least `k + 4`. -/
theorem threshold_edges_distance_ge {α : Type*} (d : α → α → ℕ)
    (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    {g f h : α} {i j k : ℕ} (hfi : d g f ≤ i + 3)
    (hhj : j ≤ d g h) (hgap : i + (k + 7) ≤ j) : k + 4 ≤ d f h := by
  have ht := htriangle g f h
  omega

/-- The distance estimate in XII (4.3), claim (4), page 250:
thresholds at most `θ - 5` stay at distance at least two from
the other chosen end edge. -/
theorem threshold_edge_distance_other_end_ge_two {α : Type*} (d : α → α → ℕ)
    (htriangle : ∀ x y z, d x z ≤ d x y + d y z)
    (hsymm : ∀ x y, d x y = d y x)
    {g h f : α} {θ i : ℕ} (hfar : θ ≤ d g h)
    (hfi : d g f ≤ i + 3) (hi : i + 5 ≤ θ) : 2 ≤ d h f := by
  have ht := htriangle g f h
  rw [hsymm f h] at ht
  omega

end GraphMinor.GM12
