/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Lemma2

/-!
# Balister–Kostochka–Li–Schelp 2004, Theorem 1

**Theorem 1.** In any optimal `k`-colouring, `|n_S − n_{S'}| ≤ 2` whenever `|S| = |S'|`.

Induction on `m = |S \ S'|`. In the step, a pair `(P, Q)` at distance `m` with `n_P ≥ n_Q + 3`
behaves rigidly (`pairStep`): exchanging `x ∈ P − Q` and `y ∈ Q − P` gives `n_{P'} = n_P − 1`,
`n_{Q'} = n_Q + 1`, and an optimal colouring in which the pair has moved to `(P', Q')`. Walking the
pair (`walkQ`) shows that a set `S` adjacent to `P` has both `n_S = n_P − 1` and `n_S = n_Q + 1`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

open Classical in
theorem swapSet_eq_insert_erase {x y : Fin k} {P : Finset (Fin k)} (hx : x ∈ P) (hy : y ∉ P) :
    swapSet x y P = insert y (P.erase x) := by
  ext θ
  rw [mem_swapSet, mem_insert, mem_erase]
  by_cases h1 : θ = x
  · subst h1; rw [Equiv.swap_apply_left]
    have : θ ≠ y := fun e => hy (e ▸ hx)
    simp [hy, this]
  by_cases h2 : θ = y
  · subst h2; rw [Equiv.swap_apply_right]; simp [hx]
  rw [Equiv.swap_apply_of_ne_of_ne h1 h2]; simp [h1, h2]

open Classical in
theorem swapSet_comm (x y : Fin k) (P : Finset (Fin k)) : swapSet x y P = swapSet y x P := by
  unfold swapSet; rw [Equiv.swap_comm]

open Classical in
omit [DecidableRel G.Adj] in
/-- The statement of Theorem 1 at distance `m`. -/
def Balanced (G : SimpleGraph V) (k m : ℕ) : Prop :=
  ∀ c : PEC G (Fin k), IsOptimal c → ∀ P Q : Finset (Fin k), #P = #Q → #(P \ Q) = m →
    cnt c P ≤ cnt c Q + 2

variable {c : PEC G (Fin k)}

open Classical in
theorem card_sdiff_symm {P Q : Finset (Fin k)} (h : #P = #Q) : #(Q \ P) = #(P \ Q) := by
  have h1 := card_sdiff_add_card_inter P Q
  have h2 := card_sdiff_add_card_inter Q P
  rw [inter_comm] at h2; omega

open Classical in
theorem erase_insert_facts {x y : Fin k} {P Q : Finset (Fin k)} (hx : x ∈ P) (hxQ : x ∉ Q)
    (hy : y ∈ Q) (hyP : y ∉ P) :
    #((insert y (P.erase x)) \ Q) + 1 = #(P \ Q) ∧ #(P \ insert x (Q.erase y)) + 1 = #(P \ Q) ∧
      #((insert y (P.erase x)) \ insert x (Q.erase y)) = #(P \ Q) := by
  have hxy : x ≠ y := fun e => hyP (e ▸ hx)
  have e1 : (insert y (P.erase x)) \ Q = (P \ Q).erase x := by
    ext θ
    by_cases h1 : θ = x
    · subst h1; simp [hx, hxQ, hxy]
    by_cases h2 : θ = y
    · subst h2; simp [hy, hyP, Ne.symm hxy]
    simp [h1, h2]
  have e2 : P \ insert x (Q.erase y) = (P \ Q).erase x := by
    ext θ
    by_cases h1 : θ = x
    · subst h1; simp [hx, hxQ, hxy]
    by_cases h2 : θ = y
    · subst h2; simp [hy, hyP, Ne.symm hxy]
    simp [h1, h2]
  have e3 : (insert y (P.erase x)) \ insert x (Q.erase y) = insert y ((P \ Q).erase x) := by
    ext θ
    by_cases h1 : θ = x
    · subst h1; simp [hx, hxQ, hxy]
    by_cases h2 : θ = y
    · subst h2; simp [hy, hyP, Ne.symm hxy]
    simp [h1, h2]
  have hxPQ : x ∈ P \ Q := mem_sdiff.2 ⟨hx, hxQ⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [e1, card_erase_add_one hxPQ]
  · rw [e2, card_erase_add_one hxPQ]
  · rw [e3, card_insert_of_notMem (fun h => hyP (mem_sdiff.1 (mem_of_mem_erase h)).1),
      card_erase_add_one hxPQ]

open Classical in
omit [DecidableEq V] in
omit [DecidableRel G.Adj] in
/-- **The pair step.** -/
theorem pairStep {m : ℕ} (ih : Balanced G k (m - 1)) (hopt : IsOptimal c) {P Q : Finset (Fin k)}
    (hcard : #P = #Q) (hm : #(P \ Q) = m) (hm2 : 2 ≤ m) (hbad : cnt c Q + 3 ≤ cnt c P)
    {x y : Fin k} (hx : x ∈ P) (hxQ : x ∉ Q) (hy : y ∈ Q) (hyP : y ∉ P) :
    cnt c (swapSet x y P) + 1 = cnt c P ∧ cnt c (swapSet x y Q) = cnt c Q + 1 ∧
      ∃ c' : PEC G (Fin k), IsOptimal c' ∧ cnt c' (swapSet x y P) = cnt c P ∧
        cnt c' (swapSet x y Q) = cnt c Q ∧
        ∀ T, T ≠ P → T ≠ swapSet x y P → T ≠ Q → T ≠ swapSet x y Q → cnt c' T = cnt c T := by
  classical
  have hxy : x ≠ y := fun e => hyP (e ▸ hx)
  have eP : swapSet x y P = insert y (P.erase x) := swapSet_eq_insert_erase hx hyP
  have eQ : swapSet x y Q = insert x (Q.erase y) := by
    rw [swapSet_comm]; exact swapSet_eq_insert_erase hy hxQ
  obtain ⟨d1, d2, -⟩ := erase_insert_facts hx hxQ hy hyP
  rw [← eP] at d1
  rw [← eQ] at d2
  have hcP' : #(swapSet x y P) = #P := card_swapSet x y P
  have hcQ' : #(swapSet x y Q) = #Q := card_swapSet x y Q
  have hPne : P ≠ Q := fun e => hxQ (e ▸ hx)
  have hP'Q : swapSet x y P ≠ Q := fun e => by rw [e, Finset.sdiff_self, card_empty] at d1; omega
  have ihPQ : ∀ c₀ : PEC G (Fin k), IsOptimal c₀ →
      cnt c₀ (swapSet x y P) ≤ cnt c₀ Q + 2 := fun c₀ h₀ =>
    ih c₀ h₀ _ Q (hcP'.trans hcard) (by omega)
  have ihPQ' : ∀ c₀ : PEC G (Fin k), IsOptimal c₀ → cnt c₀ P ≤ cnt c₀ (swapSet x y Q) + 2 :=
    fun c₀ h₀ => ih c₀ h₀ P _ (hcard.trans hcQ'.symm) (by omega)
  have hb1 := ihPQ c hopt
  have hb2 : cnt c P ≤ cnt c (swapSet x y P) + 2 := lemma2_le hopt x y P
  have hne2 : cnt c P ≠ cnt c (swapSet x y P) + 2 := by
    intro h2
    obtain ⟨c'', hopt'', -, hP'', hrest''⟩ := lemma2_two hopt hxy (S := P) h2
    have := ihPQ c'' hopt''
    rw [hP'', hrest'' Q hPne.symm (Ne.symm hP'Q)] at this
    omega
  have hone : cnt c P = cnt c (swapSet x y P) + 1 := by omega
  obtain ⟨U, hUP, hUP', hiUP, hiUP', hU1, c'', hopt'', -, hP'', hU'', hiU'', hrest''⟩ :=
    lemma2_one hopt hxy (S := P) hone
  have hUeq : U = swapSet x y Q := by
    by_cases h1 : Q = U
    · exfalso
      subst h1
      have := ihPQ' c hopt
      omega
    by_cases h2 : Q = swapSet x y U
    · rw [h2, swapSet_swapSet]
    exfalso
    have := ihPQ c'' hopt''
    rw [hP'', hrest'' Q hPne.symm (Ne.symm hP'Q) h1 h2] at this
    omega
  subst hUeq
  simp only [swapSet_swapSet] at hU1 hU'' hiU''
  refine ⟨by omega, hU1, c'', hopt'', hP'', hU'', fun T h1 h2 h3 h4 =>
    hrest'' T h1 h2 h4 (by rwa [swapSet_swapSet])⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The walk.** -/
theorem walkQ {m : ℕ} (ih : Balanced G k (m - 1)) (hm2 : 2 ≤ m) :
    ∀ j : ℕ, ∀ c : PEC G (Fin k), IsOptimal c → ∀ P Q S : Finset (Fin k), #P = #Q →
      #(P \ Q) = m → cnt c Q + 3 ≤ cnt c P → P ∩ Q ⊆ S → S ⊆ P ∪ Q → #S = #P → S ≠ P →
      (∃ b ∈ S, b ∈ Q ∧ b ∉ P) → #(Q \ S) = j + 1 → cnt c S = cnt c Q + 1 := by
  classical
  intro j
  induction j with
  | zero =>
    intro c hopt P Q S hcard hm hbad hsub1 hsub2 hcS hSP _ hj
    obtain ⟨y, hy⟩ := card_pos.1 (show 0 < #(Q \ S) by omega)
    have hcS' : #(S \ Q) = #(Q \ S) := card_sdiff_symm (hcS.trans hcard).symm
    obtain ⟨x, hx⟩ := card_pos.1 (show 0 < #(S \ Q) by omega)
    obtain ⟨hxS, hxQ⟩ := mem_sdiff.1 hx
    obtain ⟨hyQ, hyS⟩ := mem_sdiff.1 hy
    have hxP : x ∈ P := by
      rcases mem_union.1 (hsub2 hxS) with h | h
      · exact h
      · exact absurd h hxQ
    have hyP : y ∉ P := fun h => hyS (hsub1 (mem_inter.2 ⟨h, hyQ⟩))
    obtain ⟨-, h2, -⟩ := pairStep ih hopt hcard hm hm2 hbad hxP hxQ hyQ hyP
    have hQ'S : swapSet x y Q = S := by
      rw [swapSet_comm, swapSet_eq_insert_erase hyQ hxQ]
      apply eq_of_subset_of_card_le
      · intro θ hθ
        rcases mem_insert.1 hθ with rfl | hθ
        · exact hxS
        · obtain ⟨hθy, hθQ⟩ := mem_erase.1 hθ
          by_contra hθS
          have : #({y, θ} : Finset (Fin k)) ≤ #(Q \ S) :=
            card_le_card fun z hz => by
              rcases mem_insert.1 hz with rfl | hz
              · exact hy
              · rw [mem_singleton.1 hz]; exact mem_sdiff.2 ⟨hθQ, hθS⟩
          rw [card_pair (Ne.symm hθy)] at this; omega
      · rw [card_insert_of_notMem (fun h => hxQ (mem_of_mem_erase h)),
          card_erase_add_one hyQ, hcS, hcard]
    rw [← hQ'S]; exact h2
  | succ j ihj =>
    intro c hopt P Q S hcard hm hbad hsub1 hsub2 hcS hSP hb hj
    obtain ⟨b, hbS, hbQ, hbP⟩ := hb
    obtain ⟨y, hy⟩ := card_pos.1 (show 0 < #(Q \ S) by omega)
    have hcS' : #(S \ Q) = #(Q \ S) := card_sdiff_symm (hcS.trans hcard).symm
    obtain ⟨x, hx⟩ := card_pos.1 (show 0 < #(S \ Q) by omega)
    obtain ⟨hxS, hxQ⟩ := mem_sdiff.1 hx
    obtain ⟨hyQ, hyS⟩ := mem_sdiff.1 hy
    have hxP : x ∈ P := by
      rcases mem_union.1 (hsub2 hxS) with h | h
      · exact h
      · exact absurd h hxQ
    have hyP : y ∉ P := fun h => hyS (hsub1 (mem_inter.2 ⟨h, hyQ⟩))
    have hby : b ≠ y := fun e => hyS (e ▸ hbS)
    obtain ⟨-, -, c', hopt', hP', hQ', hrest'⟩ :=
      pairStep ih hopt hcard hm hm2 hbad hxP hxQ hyQ hyP
    have eP : swapSet x y P = insert y (P.erase x) := swapSet_eq_insert_erase hxP hyP
    have eQ : swapSet x y Q = insert x (Q.erase y) := by
      rw [swapSet_comm]; exact swapSet_eq_insert_erase hyQ hxQ
    obtain ⟨-, -, d3⟩ := erase_insert_facts hxP hxQ hyQ hyP
    have hbP' : b ∉ swapSet x y P := by
      rw [eP, mem_insert, mem_erase, not_or]; exact ⟨hby, fun h => hbP h.2⟩
    have hbQ' : b ∈ swapSet x y Q := by
      rw [eQ]; exact mem_insert_of_mem (mem_erase.2 ⟨hby, hbQ⟩)
    have hQ'S : #(swapSet x y Q \ S) = j + 1 := by
      have : swapSet x y Q \ S = (Q \ S).erase y := by
        rw [eQ]; ext θ; simp only [mem_sdiff, mem_insert, mem_erase]
        constructor
        · rintro ⟨h1 | ⟨h1, h2⟩, h3⟩
          · exact absurd (h1 ▸ hxS) h3
          · exact ⟨h1, h2, h3⟩
        · rintro ⟨h1, h2, h3⟩; exact ⟨Or.inr ⟨h1, h2⟩, h3⟩
      rw [this, card_erase_of_mem hy, hj]; rfl
    have hinter : swapSet x y P ∩ swapSet x y Q ⊆ S := by
      intro θ hθ
      rw [mem_inter, eP, eQ, mem_insert, mem_insert, mem_erase, mem_erase] at hθ
      have hxy : x ≠ y := fun e => hxQ (e ▸ hyQ)
      rcases hθ with ⟨h1 | ⟨h1, h2⟩, h3 | ⟨h3, h4⟩⟩
      · exact absurd (h1.symm.trans h3) (Ne.symm hxy)
      · exact absurd h1 h3
      · exact absurd h3 h1
      · exact hsub1 (mem_inter.2 ⟨h2, h4⟩)
    have hunion : S ⊆ swapSet x y P ∪ swapSet x y Q := by
      intro θ hθ
      rcases mem_union.1 (hsub2 hθ) with h | h
      · by_cases hθx : θ = x
        · rw [eQ, hθx]; exact mem_union_right _ (mem_insert_self _ _)
        · rw [eP]; exact mem_union_left _ (mem_insert_of_mem (mem_erase.2 ⟨hθx, h⟩))
      · by_cases hθy : θ = y
        · exact absurd (hθy ▸ hθ) hyS
        · rw [eQ]; exact mem_union_right _ (mem_insert_of_mem (mem_erase.2 ⟨hθy, h⟩))
    have key := ihj c' hopt' (swapSet x y P) (swapSet x y Q) S
      (by rw [card_swapSet, card_swapSet, hcard]) (by rw [eP, eQ, d3, hm])
      (by rw [hP', hQ']; exact hbad) hinter hunion (by rw [card_swapSet, hcS])
      (fun e => hbP' (e ▸ hbS)) ⟨b, hbS, hbQ', hbP'⟩ hQ'S
    have hSQ : S ≠ Q := fun e => by rw [e, Finset.sdiff_self, card_empty] at hj; omega
    have hSQ' : S ≠ swapSet x y Q := fun e => by
      rw [e, Finset.sdiff_self, card_empty] at hQ'S; omega
    rw [hrest' S hSP (fun e => hbP' (e ▸ hbS)) hSQ hSQ', hQ'] at key
    exact key

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **Balister–Kostochka–Li–Schelp 2004, Theorem 1.** In any optimal `k`-colouring,
`n_S ≤ n_{S'} + 2` whenever `|S| = |S'|`. -/
theorem theorem1 (c : PEC G (Fin k)) (hopt : IsOptimal c) {P Q : Finset (Fin k)}
    (hcard : #P = #Q) : cnt c P ≤ cnt c Q + 2 := by
  classical
  suffices h : ∀ m, Balanced G k m from h _ c hopt P Q hcard rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
    intro c hopt P Q hcard hm
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl | rfl : m = 0 ∨ m = 1 := by omega
      · have hsub : P ⊆ Q := sdiff_eq_empty_iff_subset.1 (card_eq_zero.1 hm)
        have hPQ : P = Q := eq_of_subset_of_card_le hsub (by omega)
        rw [hPQ]; omega
      · obtain ⟨x, hx⟩ := card_eq_one.1 hm
        have hcS : #(Q \ P) = 1 := (card_sdiff_symm hcard).trans hm
        obtain ⟨y, hy⟩ := card_eq_one.1 hcS
        have hxP : x ∈ P \ Q := hx ▸ mem_singleton_self x
        have hyQ : y ∈ Q \ P := hy ▸ mem_singleton_self y
        have hswap : swapSet x y P = Q := by
          rw [swapSet_eq_insert_erase (mem_sdiff.1 hxP).1 (mem_sdiff.1 hyQ).2]
          apply eq_of_subset_of_card_le
          · intro θ hθ
            rcases mem_insert.1 hθ with rfl | hθ
            · exact (mem_sdiff.1 hyQ).1
            · obtain ⟨hθx, hθP⟩ := mem_erase.1 hθ
              by_contra hθQ
              have : θ ∈ P \ Q := mem_sdiff.2 ⟨hθP, hθQ⟩
              rw [hx, mem_singleton] at this; exact hθx this
          · rw [card_insert_of_notMem (fun h => (mem_sdiff.1 hyQ).2 (mem_of_mem_erase h)),
              card_erase_add_one (mem_sdiff.1 hxP).1, hcard]
        have := lemma2_le hopt x y P
        rwa [hswap] at this
    · by_contra hbad
      push Not at hbad
      have ih : Balanced G k (m - 1) := ihm (m - 1) (by omega)
      obtain ⟨x, hx⟩ := card_pos.1 (show 0 < #(P \ Q) by omega)
      have hcS : #(Q \ P) = m := (card_sdiff_symm hcard).trans hm
      obtain ⟨y, hy⟩ := card_pos.1 (show 0 < #(Q \ P) by omega)
      obtain ⟨hxP, hxQ⟩ := mem_sdiff.1 hx
      obtain ⟨hyQ, hyP⟩ := mem_sdiff.1 hy
      obtain ⟨h1, -, -⟩ := pairStep ih hopt hcard hm hm2 (by omega) hxP hxQ hyQ hyP
      have eP : swapSet x y P = insert y (P.erase x) := swapSet_eq_insert_erase hxP hyP
      have hQS : #(Q \ swapSet x y P) = m - 2 + 1 := by
        have : Q \ swapSet x y P = (Q \ P).erase y := by
          rw [eP]; ext θ; simp only [mem_sdiff, mem_insert, mem_erase, not_or, not_and]
          constructor
          · rintro ⟨h1, h2, h3⟩
            exact ⟨h2, h1, fun hθP => h3 (fun e => hxQ (e ▸ h1)) hθP⟩
          · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, fun _ h => h3 h⟩
        rw [this, card_erase_of_mem hy, hcS]; omega
      have h2 := walkQ ih hm2 (m - 2) c hopt P Q (swapSet x y P) hcard hm (by omega)
        (by
          intro θ hθ
          obtain ⟨h1, h2⟩ := mem_inter.1 hθ
          rw [eP]; exact mem_insert_of_mem (mem_erase.2 ⟨fun e => hxQ (e ▸ h2), h1⟩))
        (by
          intro θ hθ
          rw [eP] at hθ
          rcases mem_insert.1 hθ with rfl | hθ
          · exact mem_union_right _ hyQ
          · exact mem_union_left _ (mem_of_mem_erase hθ))
        (card_swapSet x y P)
        (fun e => hyP (by rw [← e, eP]; exact mem_insert_self _ _))
        ⟨y, by rw [eP]; exact mem_insert_self _ _, hyQ, hyP⟩ hQS
      omega
end Bkls

end LeanPool.BalancedEdgeColourings
