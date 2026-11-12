/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.SimpleGridPathBetween

-- [TABLET NODE: SimpleGridPathPointTrichotomy]

/-!
# SimpleGridPathPointTrichotomy

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

lemma SimpleGridPathPointTrichotomy
    (V : Set GaussianInt) (E : Set (Finset GaussianInt))
    (a b x : GaussianInt)
    (hpath : SimpleGridPathBetween V E a b)
    (hincident : ∃ e : Finset GaussianInt, x ∈ e ∧ e ∈ E) :
    x = a ∨ x = b ∨
      ∃ e f : Finset GaussianInt,
        e ≠ f ∧ x ∈ e ∧ x ∈ f ∧ e ∈ E ∧ f ∈ E := by
-- BODY
  rcases hpath with ⟨p, hp, hlen, hhead, hlast, hV, hstep, hE⟩
  rcases hincident with ⟨e, hxe, heE⟩
  rcases (hE e).1 heE with ⟨u, v, l₁, l₂, hraw, heq⟩
  have hxlist : x ∈ p := by
    have hxpair : x ∈ ({u, v} : Finset GaussianInt) := by
      rw [← heq]
      exact hxe
    have hxuv : x = u ∨ x = v := by simpa using hxpair
    rcases hxuv with rfl | rfl
    · rw [hraw]
      simp
    · rw [hraw]
      simp
  have hpne : p ≠ [] := by
    intro hpnil
    have hzero : (2 : Nat) ≤ 0 := by simpa only [hpnil, List.length_nil] using hlen
    omega
  have hfirst : ∀ z : GaussianInt, p.head? = some z → p = z :: p.tail := by
    intro z hz
    cases p with
    | nil => exact False.elim (hpne rfl)
    | cons q r =>
      simp only [List.head?_cons, Option.some.injEq] at hz
      subst q
      rfl
  have split_mem : ∀ (r : List GaussianInt) (z : GaussianInt),
      z ∈ r → ∃ l t, r = l ++ z :: t := by
    intro r z hz
    induction r with
    | nil => simp at hz
    | cons q r ih =>
      simp only [List.mem_cons] at hz
      rcases hz with rfl | hz
      · exact ⟨[], r, rfl⟩
      · rcases ih hz with ⟨l, t, ht⟩
        exact ⟨q :: l, t, by simp [ht, List.cons_append]⟩
  have hxa : x = a ∨ x ≠ a := eq_or_ne x a
  rcases hxa with rfl | hxa
  · exact Or.inl rfl
  have hxb : x = b ∨ x ≠ b := eq_or_ne x b
  rcases hxb with rfl | hxb
  · exact Or.inr (Or.inl rfl)
  rcases split_mem p x hxlist with ⟨l, t, hsplit⟩
  have hl : l ≠ [] := by
    intro hnil
    have hheadx : p.head? = some x := by
      rw [hsplit, hnil]
      simp
    have hhead_eq : x = a := by simpa [hheadx] using hhead
    exact hxa hhead_eq
  have ht : t ≠ [] := by
    intro hnil
    have hlastx : p.getLast? = some x := by
      rw [hsplit, hnil]
      simp
    have hlast_eq : x = b := by simpa [hlastx] using hlast
    exact hxb hlast_eq
  let z := l.getLast hl
  let l₀ := l.dropLast
  have hlt : l₀ ++ [z] = l := by
    exact List.dropLast_append_getLast hl
  obtain ⟨w, t₀, htform⟩ := List.exists_cons_of_ne_nil ht
  have he₁ : ({z, x} : Finset GaussianInt) ∈ E := by
    apply (hE {z, x}).2
    refine ⟨z, x, l₀, w :: t₀, ?_, rfl⟩
    rw [hsplit, ← hlt, htform]
    simp [List.append_assoc]
  have he₂ : ({x, w} : Finset GaussianInt) ∈ E := by
    apply (hE {x, w}).2
    refine ⟨x, w, l, t₀, ?_, rfl⟩
    rw [hsplit, htform]
  refine Or.inr (Or.inr ⟨{z, x}, {x, w}, ?_, by simp, by simp, he₁, he₂⟩)
  intro heq'
  have hzmem : z ∈ ({x, w} : Finset GaussianInt) := by
    rw [← heq']
    simp
  have hzw : z = x ∨ z = w := by simpa using hzmem
  have hznotx : z ≠ x := by
    intro hzx
    have hbad := hp
    rw [hsplit, ← hlt, htform] at hbad
    simp only [List.append_assoc, List.cons_append, List.nil_append, List.nodup_append,
        List.nodup_cons, List.mem_cons, not_or, ne_eq, forall_eq_or_imp] at hbad
    exact hbad.2.1.1.1 hzx
  rcases hzw with hzx | hzw
  · exact hznotx hzx
  · subst w
    have hbad := hp
    rw [hsplit, ← hlt, htform] at hbad
    simp [List.nodup_append] at hbad

end ApollonianSuperharmonic

end
