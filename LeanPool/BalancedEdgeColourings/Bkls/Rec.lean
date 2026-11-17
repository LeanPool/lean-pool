/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Moves
public import LeanPool.BalancedEdgeColourings.Bkls.Theorem1

/-!
# `R`-recolourings

`Rec R c c'`: `c'` is optimal and its counts are those of `c` permuted by a permutation of the
colour sets that keeps sizes and the membership of every colour outside `R` (the effect of any
sequence of the moves of Lemma 2 with both colours in `R`). `rec_two` and `rec_one` are those
moves; `Rec.card_filter`: the number of `m`-piles in a collection defined by sizes and colours
outside `R` does not change.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

open Classical in
/-- A permutation of colour sets keeping sizes and the colours outside `R`. -/
def RPerm (R : Finset (Fin k)) (π : Equiv.Perm (Finset (Fin k))) : Prop :=
  (∀ T, #(π T) = #T) ∧ ∀ T x, x ∉ R → (x ∈ π T ↔ x ∈ T)

open Classical in
theorem RPerm.refl (R : Finset (Fin k)) : RPerm R (Equiv.refl _) :=
  ⟨fun _ => rfl, fun _ _ _ => Iff.rfl⟩

open Classical in
theorem RPerm.trans {R : Finset (Fin k)} {π₁ π₂ : Equiv.Perm (Finset (Fin k))} (h1 : RPerm R π₁)
    (h2 : RPerm R π₂) : RPerm R (π₂.trans π₁) :=
  ⟨fun T => by simp only [Equiv.trans_apply]; rw [h1.1, h2.1],
    fun T x hx => by simp only [Equiv.trans_apply]; rw [h1.2 _ _ hx, h2.2 _ _ hx]⟩

open Classical in
theorem RPerm.of_cases {R : Finset (Fin k)} {a b : Fin k} {π : Equiv.Perm (Finset (Fin k))}
    (ha : a ∈ R) (hb : b ∈ R) (h : ∀ T, π T = T ∨ π T = swapSet a b T) : RPerm R π := by
  refine ⟨fun T => ?_, fun T x hx => ?_⟩
  · rcases h T with e | e <;> rw [e]
    exact card_swapSet a b T
  · rcases h T with e | e <;> rw [e]
    have hxa : x ≠ a := fun e => hx (e ▸ ha)
    have hxb : x ≠ b := fun e => hx (e ▸ hb)
    rw [mem_swapSet, Equiv.swap_apply_of_ne_of_ne hxa hxb]

open Classical in
theorem swap_cases (a b : Fin k) (S T : Finset (Fin k)) :
    Equiv.swap S (swapSet a b S) T = T ∨ Equiv.swap S (swapSet a b S) T = swapSet a b T := by
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · right; rw [h1]
  · right; rw [h2, swapSet_swapSet]
  · left; rfl

open Classical in
/-- `c'` is an `R`-recolouring of `c`. -/
def Rec (R : Finset (Fin k)) (c c' : PEC G (Fin k)) : Prop :=
  IsOptimal c' ∧ ∃ π : Equiv.Perm (Finset (Fin k)), RPerm R π ∧ ∀ T, cnt c' T = cnt c (π T)

variable {R : Finset (Fin k)} {c c' c'' : PEC G (Fin k)} {a b : Fin k}

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem Rec.self (h : IsOptimal c) : Rec R c c := by
  classical
  exact ⟨h, Equiv.refl _, RPerm.refl R, fun _ => rfl⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem Rec.opt (h : Rec R c c') : IsOptimal c' := by
  classical
  exact h.1

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem Rec.trans (h1 : Rec R c c') (h2 : Rec R c' c'') : Rec R c c'' := by
  classical
  obtain ⟨-, π₁, hπ₁, e1⟩ := h1
  obtain ⟨ho, π₂, hπ₂, e2⟩ := h2
  exact ⟨ho, π₂.trans π₁, hπ₁.trans hπ₂, fun T => by rw [e2, e1]; rfl⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Lemma 2, difference two, as a recolouring.** -/
theorem rec_two (hopt : IsOptimal c) (hab : a ≠ b) (ha : a ∈ R) (hb : b ∈ R)
    {S : Finset (Fin k)} (h : cnt c S = cnt c (swapSet a b S) + 2) :
    ∃ c', Rec R c c' ∧ cnt c' S = cnt c (swapSet a b S) ∧ cnt c' (swapSet a b S) = cnt c S ∧
      ∀ X, X ≠ S → X ≠ swapSet a b S → cnt c' X = cnt c X := by
  classical
  obtain ⟨c', ho', e1, e2, e3⟩ := lemma2_two hopt hab h
  refine ⟨c', ⟨ho', Equiv.swap S (swapSet a b S), RPerm.of_cases ha hb (swap_cases a b S),
    fun T => ?_⟩, e1, e2, e3⟩
  rw [Equiv.swap_apply_def]
  split_ifs with h1 h2
  · rw [h1, e1]
  · rw [h2, e2]
  · exact e3 T h1 h2

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Lemma 2, difference one, as a recolouring.** -/
theorem rec_one (hopt : IsOptimal c) (hab : a ≠ b) (ha : a ∈ R) (hb : b ∈ R)
    {S : Finset (Fin k)} (h : cnt c S = cnt c (swapSet a b S) + 1) :
    partner c hab S ≠ S ∧ partner c hab S ≠ swapSet a b S ∧
      swapSet a b (partner c hab S) ≠ S ∧ swapSet a b (partner c hab S) ≠ swapSet a b S ∧
      cnt c (partner c hab S) = cnt c (swapSet a b (partner c hab S)) + 1 ∧
      ∃ c', Rec R c c' ∧ cnt c' S = cnt c (swapSet a b S) ∧
        cnt c' (swapSet a b S) = cnt c S ∧
        cnt c' (partner c hab S) = cnt c (swapSet a b (partner c hab S)) ∧
        cnt c' (swapSet a b (partner c hab S)) = cnt c (partner c hab S) ∧
        ∀ X, X ≠ S → X ≠ swapSet a b S → X ≠ partner c hab S →
          X ≠ swapSet a b (partner c hab S) → cnt c' X = cnt c X := by
  classical
  obtain ⟨n1, n2, n3, n4, hU, c', ho', e1, e2, e3, e4, e5⟩ := lemma2_one' hopt hab h
  refine ⟨n1, n2, n3, n4, hU, c', ⟨ho', (Equiv.swap S (swapSet a b S)).trans
    (Equiv.swap (partner c hab S) (swapSet a b (partner c hab S))),
    (RPerm.of_cases ha hb (swap_cases a b _)).trans (RPerm.of_cases ha hb (swap_cases a b S)),
    fun T => ?_⟩, e1, e2, e3, e4, e5⟩
  set U := partner c hab S
  have hSne : swapSet a b S ≠ S := fun e => by rw [e] at h; omega
  have hUne : swapSet a b U ≠ U := fun e => by rw [e] at hU; omega
  simp only [Equiv.trans_apply]
  by_cases t1 : T = S
  · subst t1
    rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne (Ne.symm n2) (Ne.symm n4), e1]
  by_cases t2 : T = swapSet a b S
  · subst t2
    rw [Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne (Ne.symm n1) (Ne.symm n3), e2]
  rw [Equiv.swap_apply_of_ne_of_ne t1 t2]
  by_cases t3 : T = U
  · subst t3; rw [Equiv.swap_apply_left, e3]
  by_cases t4 : T = swapSet a b U
  · subst t4; rw [Equiv.swap_apply_right, e4]
  rw [Equiv.swap_apply_of_ne_of_ne t3 t4, e5 T t1 t2 t3 t4]

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Pile counts in an `R`-invariant collection are preserved.** -/
theorem Rec.card_filter (h : Rec R c c') (P : Finset (Fin k) → Prop)
    (hP : ∀ T T', #T = #T' → (∀ x, x ∉ R → (x ∈ T ↔ x ∈ T')) → (P T ↔ P T')) (m : ℕ) :
    #(univ.filter fun T => P T ∧ cnt c' T = m) = #(univ.filter fun T => P T ∧ cnt c T = m) := by
  classical
  obtain ⟨-, π, hπ, e⟩ := h
  refine card_bij (fun T _ => π T) (fun T hT => ?_) (fun T _ T' _ h => π.injective h)
    (fun T' hT' => ?_)
  · obtain ⟨hp, hc⟩ := (mem_filter.1 hT).2
    exact mem_filter.2 ⟨mem_univ _, (hP (π T) T (hπ.1 T) (fun x hx => hπ.2 T x hx)).2 hp,
      by rw [← e]; exact hc⟩
  · obtain ⟨hp, hc⟩ := (mem_filter.1 hT').2
    refine ⟨π.symm T', mem_filter.2 ⟨mem_univ _, ?_, ?_⟩, by simp⟩
    · have := (hP (π (π.symm T')) (π.symm T') (hπ.1 _) (fun x hx => hπ.2 _ x hx)).1
      rw [Equiv.apply_symm_apply] at this
      exact this hp
    · rw [e, Equiv.apply_symm_apply]; exact hc
end Bkls

end LeanPool.BalancedEdgeColourings
