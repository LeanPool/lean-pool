/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.L9a

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 9, part (b): the stage engine

`stage_engine`: with room at every degree holding a 2-pile (an empty `S₀ - y + γ` is forced by
counting, or the hypothesis of Lemma 7 holds), all 2-piles can be moved into `[S₋ ∪ {γ}, [k]]` by an
`([k] \ S₋)`-recolouring that keeps the 1-piles of `Up` and of `Out` at each degree.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L9

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
variable {Sm : Finset (Fin k)} {γ : Fin k}

open Classical in
theorem swap_in_up (hγ : γ ∉ Sm) {S0 : Finset (Fin k)} (hS0 : Sm ⊆ S0) (_ : γ ∉ S0) {y : Fin k}
    (hy : y ∈ S0) (hyS : y ∉ Sm) :
    Sm ⊆ swapSet y γ S0 ∧ γ ∈ swapSet y γ S0 ∧ #(swapSet y γ S0) = #S0 := by
  refine ⟨fun z hz => ?_, by rw [mem_swapSet, Equiv.swap_apply_right]; exact hy, card_swapSet _ _ _⟩
  have hzy : z ≠ y := fun e => hyS (e ▸ hz)
  have hzγ : z ≠ γ := fun e => hγ (e ▸ hz)
  rw [mem_swapSet, Equiv.swap_apply_of_ne_of_ne hzy hzγ]; exact hS0 hz

open Classical in
theorem swap_inj {S0 : Finset (Fin k)} (hγS0 : γ ∉ S0) {y y' : Fin k} (hy : y ∈ S0) (_ : y' ∈ S0)
    (h : swapSet y γ S0 = swapSet y' γ S0) : y = y' := by
  by_contra hne
  have h1 : y ∉ swapSet y γ S0 := by rw [mem_swapSet, Equiv.swap_apply_left]; exact hγS0
  have hyγ : y ≠ γ := fun e => hγS0 (e ▸ hy)
  have h2 : y ∈ swapSet y' γ S0 := by
    rw [mem_swapSet, Equiv.swap_apply_of_ne_of_ne hne hyγ]; exact hy
  rw [h] at h1
  exact h1 h2

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem one_palette_room {c' : PEC G (Fin k)} {S0 : Finset (Fin k)}
    (hS0 : Sm ⊆ S0) (hγS0 : γ ∉ S0) (h2 : cnt c' S0 = 2) :
    h1 Sm γ c' (#S0) + 1 ≤
      #(univ.filter fun T : Finset (Fin k) => Sm ⊆ T ∧ γ ∉ T ∧ #T = #S0) := by
  classical
  unfold h1
  have hsub : (univ.filter fun T => (Sm ⊆ T ∧ γ ∉ T ∧ #T = #S0) ∧ cnt c' T = 1) ⊆
      (univ.filter fun T : Finset (Fin k) => Sm ⊆ T ∧ γ ∉ T ∧ #T = #S0).erase S0 := by
    intro T hT
    obtain ⟨h, h'⟩ := (mem_filter.1 hT).2
    exact mem_erase.2 ⟨fun e => by rw [e, h2] at h'; omega, mem_filter.2 ⟨mem_univ _, h⟩⟩
  have := card_le_card hsub
  rw [card_erase_of_mem (mem_filter.2 ⟨mem_univ _, hS0, hγS0, rfl⟩)] at this
  have : 0 < #(univ.filter fun T : Finset (Fin k) => Sm ⊆ T ∧ γ ∉ T ∧ #T = #S0) :=
    card_pos.2 ⟨S0, mem_filter.2 ⟨mem_univ _, hS0, hγS0, rfl⟩⟩
  omega

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The stage engine.** -/
theorem stage_engine (hγ : γ ∉ Sm) {c : PEC G (Fin k)} (hopt : IsOptimal c)
    (hn2 : ∀ T, cnt c T ≤ 2) (hall : ∀ T, cnt c T = 2 → Sm ⊆ T)
    (hroom : ∀ d, 1 ≤ y2 c d →
      h1 Sm γ c d + 1 ≤ #(univ.filter fun T : Finset (Fin k) => Sm ⊆ T ∧ γ ∉ T ∧ #T = d) →
      g1 Sm γ c d + y2 c d < d - #Sm + 1 ∨
      (2 ≤ d - #Sm ∧ (((k - #Sm - 1).choose (d - #Sm - 1) : ℕ) : ℚ) / (((d - #Sm : ℕ) : ℚ) -
          1) - 1 ≤
        (((k - #Sm - 1).choose (d - #Sm - 1) : ℕ) : ℚ) - g1 Sm γ c d - ((y2 c d - 1 : ℕ) : ℚ))) :
    ∃ c', Inv Sm γ c c' ∧ ∀ T, cnt c' T = 2 → Sm ⊆ T ∧ γ ∈ T := by
  classical
  suffices H : ∀ n, ∀ c', Inv Sm γ c c' → bad Sm γ c' = n → ∃ c'', Inv Sm γ c c'' ∧
      bad Sm γ c'' = 0 by
    obtain ⟨c'', hinv, hb⟩ := H _ c ⟨Rec.self hopt, fun _ => rfl, fun _ => rfl⟩ rfl
    refine ⟨c'', hinv, fun T hT => ⟨rec_sub (subset_refl _) hinv.1 hall T hT, ?_⟩⟩
    by_contra hγT
    unfold bad at hb
    rw [card_eq_zero, filter_eq_empty_iff] at hb
    exact hb (mem_univ T) ⟨⟨rec_sub (subset_refl _) hinv.1 hall T hT, hγT⟩, hT⟩
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro c' hinv hbn
  by_cases hn0 : n = 0
  · exact ⟨c', hinv, hbn.trans hn0⟩
  -- a 2-pile still outside
  obtain ⟨S0, hS0m⟩ : (univ.filter fun T => (Sm ⊆ T ∧ γ ∉ T) ∧ cnt c' T = 2).Nonempty := by
    rw [← card_pos]; unfold bad at hbn; omega
  obtain ⟨⟨hS0, hγS0⟩, h2⟩ := (mem_filter.1 hS0m).2
  set d := #S0 with hd
  have hopt' := hinv.1.opt
  have hn2' := rec_cnt_le hinv.1 hn2
  have hy2 : y2 c' d = y2 c d := rec_y2 hinv.1 d
  have hg1 := hinv.2.1 d
  have hh1 := hinv.2.2 d
  -- the hypotheses of `hroom`
  have hy1 : 1 ≤ y2 c d := by
    rw [← hy2]; unfold y2; exact card_pos.2 ⟨S0, mem_filter.2 ⟨mem_univ _, rfl, h2⟩⟩
  have hout : h1 Sm γ c d + 1 ≤
      #(univ.filter fun T : Finset (Fin k) => Sm ⊆ T ∧ γ ∉ T ∧ #T = d) := by
    rw [← hh1]
    exact one_palette_room hS0 hγS0 h2
  -- nonempty squares of `Up` at degree `d`
  have hnon : #(univ.filter fun T => (Sm ⊆ T ∧ γ ∈ T ∧ #T = d) ∧ cnt c' T ≠ 0) + 1 ≤
      g1 Sm γ c d + y2 c d := by
    rw [← hg1, ← hy2]
    unfold g1 y2
    have hsplit := L8.csplit (fun T => (Sm ⊆ T ∧ γ ∈ T ∧ #T = d) ∧ cnt c' T ≠ 0)
      (fun T => cnt c' T = 1)
    have e1 : #(univ.filter fun T => ((Sm ⊆ T ∧ γ ∈ T ∧ #T = d) ∧ cnt c' T ≠ 0) ∧ cnt c' T = 1) =
        #(univ.filter fun T => (Sm ⊆ T ∧ γ ∈ T ∧ #T = d) ∧ cnt c' T = 1) := by
      apply L8.cfilter_congr; intro T; constructor
      · rintro ⟨⟨h, -⟩, h'⟩; exact ⟨h, h'⟩
      · rintro ⟨h, h'⟩; exact ⟨⟨h, by omega⟩, h'⟩
    have e2 : #(univ.filter fun T => ((Sm ⊆ T ∧ γ ∈ T ∧ #T = d) ∧ cnt c' T ≠ 0) ∧
        ¬ cnt c' T = 1) + 1 ≤ #(univ.filter fun T => #T = d ∧ cnt c' T = 2) := by
      have hsub : insert S0 (univ.filter fun T => ((Sm ⊆ T ∧ γ ∈ T ∧ #T = d) ∧ cnt c' T ≠ 0) ∧
          ¬ cnt c' T = 1) ⊆ univ.filter fun T => #T = d ∧ cnt c' T = 2 := by
        intro T hT
        rcases mem_insert.1 hT with rfl | hT
        · exact mem_filter.2 ⟨mem_univ _, rfl, h2⟩
        · obtain ⟨⟨⟨-, -, h3⟩, h4⟩, h5⟩ := (mem_filter.1 hT).2
          have := hn2' T
          exact mem_filter.2 ⟨mem_univ _, h3, by omega⟩
      have := card_le_card hsub
      rwa [card_insert_of_notMem (fun h => hγS0 (mem_filter.1 h).2.1.1.2.1)] at this
    omega
  have hcardSm : #(S0 \ Sm) = d - #Sm := card_sdiff_of_subset hS0
  -- an empty neighbour inside, if one exists, finishes the step
  have hfinish : ∀ c₁ : PEC G (Fin k), Inv Sm γ c c₁ → bad Sm γ c₁ = n → cnt c₁ S0 = 2 →
      (∃ y ∈ S0 \ Sm, cnt c₁ (swapSet y γ S0) = 0) →
      ∃ c'', Inv Sm γ c c'' ∧ bad Sm γ c'' = 0 := by
    intro c₁ hinv₁ hb₁ h2₁ ⟨y, hy, h0⟩
    obtain ⟨hyS0, hyS⟩ := mem_sdiff.1 hy
    obtain ⟨c'', hinv'', hb''⟩ := e1_step hγ hinv₁ hS0 hγS0 h2₁ hyS0 hyS h0
    exact ih _ (by omega) c'' hinv'' rfl
  rcases hroom d hy1 hout with hA | ⟨hs, hB⟩
  · -- case A: by counting, some neighbour is empty
    apply hfinish c' hinv hbn h2
    by_contra hne
    push Not at hne
    have hsub : (S0 \ Sm).image (fun y => swapSet y γ S0) ⊆
        univ.filter fun T => (Sm ⊆ T ∧ γ ∈ T ∧ #T = d) ∧ cnt c' T ≠ 0 := by
      intro T hT
      obtain ⟨y, hy, rfl⟩ := mem_image.1 hT
      obtain ⟨hyS0, hyS⟩ := mem_sdiff.1 hy
      obtain ⟨a1, a2, a3⟩ := swap_in_up hγ hS0 hγS0 hyS0 hyS
      exact mem_filter.2 ⟨mem_univ _, ⟨a1, a2, a3⟩, hne y hy⟩
    have := card_le_card hsub
    rw [card_image_of_injOn (fun y hy y' hy' h => swap_inj hγS0 (mem_sdiff.1 hy).1
      (mem_sdiff.1 hy').1 h), hcardSm] at this
    omega
  · -- case B: Lemma 7 first
    have hcls : #(univ.filter fun T => L7.In7 Sm univ γ S0 T) = (k - #Sm - 1).choose (d - #Sm
        - 1) := by
      have := card_supersets (insert γ Sm) (d := d) (by
        rw [card_insert_of_notMem hγ]; omega)
      rw [card_insert_of_notMem hγ, show k - (#Sm + 1) = k - #Sm - 1 by omega,
        show d - (#Sm + 1) = d - #Sm - 1 by omega] at this
      rw [← this]
      apply L8.cfilter_congr
      intro T
      unfold L7.In7
      constructor
      · rintro ⟨h1', h2', -, h4⟩; exact ⟨insert_subset h2' h1', h4⟩
      · rintro ⟨h1', h4⟩
        exact ⟨(subset_insert _ _).trans h1', h1' (mem_insert_self _ _), subset_univ _, h4⟩
    have hempty : (((k - #Sm - 1).choose (d - #Sm - 1) : ℕ) : ℚ) - g1 Sm γ c d -
        ((y2 c d - 1 : ℕ) : ℚ) ≤ #(univ.filter fun T => L7.In7 Sm univ γ S0 T ∧ cnt c' T = 0) := by
      have hsplit := L8.csplit (fun T => L7.In7 Sm univ γ S0 T) (fun T => cnt c' T = 0)
      have e : #(univ.filter fun T => L7.In7 Sm univ γ S0 T ∧ ¬ cnt c' T = 0) =
          #(univ.filter fun T => (Sm ⊆ T ∧ γ ∈ T ∧ #T = d) ∧ cnt c' T ≠ 0) := by
        apply L8.cfilter_congr; intro T; unfold L7.In7
        constructor
        · rintro ⟨⟨h1', h2', -, h4⟩, h5⟩; exact ⟨⟨h1', h2', h4⟩, h5⟩
        · rintro ⟨⟨h1', h2', h4⟩, h5⟩; exact ⟨⟨h1', h2', subset_univ _, h4⟩, h5⟩
      rw [e, hcls] at hsplit
      have hy' : ((y2 c d - 1 : ℕ) : ℚ) = (y2 c d : ℚ) - 1 := by
        rw [Nat.cast_sub hy1]; simp
      rw [hy']
      have : (((k - #Sm - 1).choose (d - #Sm - 1) : ℕ) : ℚ) =
          #(univ.filter fun T => L7.In7 Sm univ γ S0 T ∧ cnt c' T = 0) +
          #(univ.filter fun T => (Sm ⊆ T ∧ γ ∈ T ∧ #T = d) ∧ cnt c' T ≠ 0) := by
        exact_mod_cast hsplit
      have hn' : (#(univ.filter fun T => (Sm ⊆ T ∧ γ ∈ T ∧ #T = d) ∧ cnt c' T ≠ 0) : ℚ) + 1 ≤
          g1 Sm γ c d + y2 c d := by exact_mod_cast hnon
      linarith
    have hk : #(univ : Finset (Fin k)) = k := by rw [card_univ, Fintype.card_fin]
    have ho : (((#(univ : Finset (Fin k)) - #Sm - 1).choose (#S0 - #Sm - 1) : ℕ) : ℚ) /
        (((#S0 - #Sm : ℕ) : ℚ) - 1) - 1 ≤
        #(univ.filter fun T => L7.In7 Sm univ γ S0 T ∧ cnt c' T = 0) := by
      rw [hk, ← hd]; linarith
    obtain ⟨c₁, hrec₁, h2₁, T, hT7, hTd, hT0⟩ := L7.lemma7 (Sp := univ) hS0 (subset_univ _) hγS0
      (mem_univ _) hs hopt' h2 ho
    have hRc : L7.Rc Sm univ γ ⊆ univ \ Sm := fun x hx => by
      rw [L7.mem_Rc] at hx; exact mem_sdiff.2 ⟨mem_univ _, hx.2.1⟩
    have hRcfix : ∀ x, x ∈ Sm ∨ x = γ → x ∉ L7.Rc Sm univ γ := fun x hx h => by
      rw [L7.mem_Rc] at h; rcases hx with hx | hx
      · exact h.2.1 hx
      · exact h.2.2 hx
    have hinv₁ : Inv Sm γ c c₁ := by
      refine ⟨hinv.1.trans (L8.Rec.mono hrec₁ hRc), fun d' => ?_, fun d' => ?_⟩
      · rw [← hinv.2.1 d']
        have := hrec₁.card_filter (fun T => Sm ⊆ T ∧ γ ∈ T ∧ #T = d') (fun T T' hc h => by
          constructor
          · rintro ⟨a1, a2, a3⟩
            exact ⟨fun z hz => (h z (hRcfix z (Or.inl hz))).1 (a1 hz),
              (h γ (hRcfix γ (Or.inr rfl))).1 a2, hc ▸ a3⟩
          · rintro ⟨a1, a2, a3⟩
            exact ⟨fun z hz => (h z (hRcfix z (Or.inl hz))).2 (a1 hz),
              (h γ (hRcfix γ (Or.inr rfl))).2 a2, hc ▸ a3⟩) 1
        unfold g1; convert this using 3
      · rw [← hinv.2.2 d']
        have := hrec₁.card_filter (fun T => Sm ⊆ T ∧ γ ∉ T ∧ #T = d') (fun T T' hc h => by
          constructor
          · rintro ⟨a1, a2, a3⟩
            exact ⟨fun z hz => (h z (hRcfix z (Or.inl hz))).1 (a1 hz),
              fun h' => a2 ((h γ (hRcfix γ (Or.inr rfl))).2 h'), hc ▸ a3⟩
          · rintro ⟨a1, a2, a3⟩
            exact ⟨fun z hz => (h z (hRcfix z (Or.inl hz))).2 (a1 hz),
              fun h' => a2 ((h γ (hRcfix γ (Or.inr rfl))).1 h'), hc ▸ a3⟩) 1
        unfold h1; convert this using 3
    have hb₁ : bad Sm γ c₁ = n := by
      rw [← hbn]
      have := hrec₁.card_filter (fun T => Sm ⊆ T ∧ γ ∉ T) (fun T T' _ h => by
        constructor
        · rintro ⟨a1, a2⟩
          exact ⟨fun z hz => (h z (hRcfix z (Or.inl hz))).1 (a1 hz),
            fun h' => a2 ((h γ (hRcfix γ (Or.inr rfl))).2 h')⟩
        · rintro ⟨a1, a2⟩
          exact ⟨fun z hz => (h z (hRcfix z (Or.inl hz))).2 (a1 hz),
            fun h' => a2 ((h γ (hRcfix γ (Or.inr rfl))).1 h')⟩) 2
      unfold bad; convert this using 3
    apply hfinish c₁ hinv₁ hb₁ h2₁
    -- `T = S₀ - y + γ`
    obtain ⟨hT1, hTγ, -, hTc⟩ := hT7
    have hγT : γ ∈ T \ S0 := mem_sdiff.2 ⟨hTγ, hγS0⟩
    have hTS : T \ S0 = {γ} := (card_eq_one.1 hTd).elim fun z hz => by
      rw [hz] at hγT ⊢; rw [mem_singleton.1 hγT]
    have hST : #(S0 \ T) = 1 := by rw [card_sdiff_symm hTc, hTd]
    obtain ⟨y, hyST⟩ := card_eq_one.1 hST
    have hy : y ∈ S0 \ T := by rw [hyST]; exact mem_singleton_self _
    obtain ⟨hyS0, hyT⟩ := mem_sdiff.1 hy
    refine ⟨y, mem_sdiff.2 ⟨hyS0, fun h => hyT (hT1 h)⟩, ?_⟩
    have hTeq : swapSet y γ S0 = T := by
      ext z
      rw [mem_swapSet]
      by_cases hzy : z = y
      · subst hzy; rw [Equiv.swap_apply_left]
        exact ⟨fun h => absurd h hγS0, fun h => absurd h hyT⟩
      by_cases hzγ : z = γ
      · subst hzγ; rw [Equiv.swap_apply_right]; exact ⟨fun _ => hTγ, fun _ => hyS0⟩
      rw [Equiv.swap_apply_of_ne_of_ne hzy hzγ]
      constructor
      · intro hz
        by_contra hzT
        have : z ∈ S0 \ T := mem_sdiff.2 ⟨hz, hzT⟩
        rw [hyST, mem_singleton] at this; exact hzy this
      · intro hz
        by_contra hzS
        have : z ∈ T \ S0 := mem_sdiff.2 ⟨hz, hzS⟩
        rw [hTS, mem_singleton] at this; exact hzγ this
    rw [hTeq]; exact hT0
end Bkls.L9

end LeanPool.BalancedEdgeColourings
