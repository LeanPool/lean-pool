/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.L8a

/-!
# Balister–Kostochka–Li–Schelp 2004, Lemma 8, part (b): the matching `J'`

In a colouring with all `n_T ≤ 2`, for colours `a ≠ b`: `InA d T` — `T ∈ [S₋ ∪ {a}, S₊ \ {b}]_d`
holds a 1-pile and `i T` does not; `AV d w` — `w` is the `J`-unmatched vertex of such a pair (it is
unique, `unm_unique`). `g_a - g_b` (1-piles in `[S₋ ∪ {a}, S₊]_d` minus those in
`[S₋ ∪ {b}, S₊]_d`) equals `#AV - #BV` (`gdiff_eq`). `exists_xmatch`: a matching `J'` between the
`AV d` and the `BV d` vertices, maximal for every `d`.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.L8

open LeanPool.Vizing LeanPool.Vizing.PEC SimpleGraph Finset Overfull Balanced Bkls


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}

section Defs

variable (Sm Sp : Finset (Fin k)) (c : PEC G (Fin k)) (a b : Fin k)

open Classical in
/-- A 1-pile on the `a`-side whose partner is not a 1-pile. -/
def InA (d : ℕ) (T : Finset (Fin k)) : Prop :=
  Sm ⊆ T ∧ T ⊆ Sp ∧ a ∈ T ∧ b ∉ T ∧ #T = d ∧ cnt c T = 1 ∧ cnt c (swapSet a b T) ≠ 1

open Classical in
/-- The `J`-unmatched vertex of an `InA` pair. -/
def AV (d : ℕ) (w : V) : Prop :=
  ¬ JMatched c a b w ∧ ∃ T, InA Sm Sp c a b d T ∧ (colSet c w = T ∨ colSet c w = swapSet a b T)

open Classical in
/-- The same on the `b`-side. -/
def BV (d : ℕ) (w : V) : Prop :=
  ¬ JMatched c a b w ∧ ∃ T, InA Sm Sp c b a d T ∧ (colSet c w = T ∨ colSet c w = swapSet a b T)

open Classical in
/-- 1-piles in `[S₋ ∪ {e}, S₊]_d`. -/
noncomputable def g (e : Fin k) (d : ℕ) : ℕ :=
  #(univ.filter fun T => Sm ⊆ T ∧ T ⊆ Sp ∧ e ∈ T ∧ #T = d ∧ cnt c T = 1)

end Defs

variable {Sm Sp : Finset (Fin k)} {c : PEC G (Fin k)} {a b : Fin k}

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem unm_lt {w : V} (h : ¬ JMatched c a b w) :
    cnt c (swapSet a b (colSet c w)) < cnt c (colSet c w) := by
  classical
  have := rank_lt_cnt c w
  unfold JMatched at h
  omega

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem unm_eq {w w' : V} (hw : ¬ JMatched c a b w) (hw' : ¬ JMatched c a b w')
    (he : colSet c w = colSet c w') (h1 : cnt c (colSet c w) = cnt c (swapSet a b (colSet c
        w)) + 1) :
    w = w' := by
  classical
  apply rank_injOn c he
  have r1 := rank_lt_cnt c w
  have r2 := rank_lt_cnt c w'
  unfold JMatched at hw hw'
  rw [← he] at r2 hw'
  omega
open Classical in
theorem swap_mem_a {T : Finset (Fin k)} (hb : b ∉ T) : a ∉ swapSet a b T := by
  rw [mem_swapSet, Equiv.swap_apply_left]; exact hb

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **One `J`-unmatched vertex per pair.** -/
theorem unm_unique (hn2 : ∀ T, cnt c T ≤ 2) {d : ℕ} {T : Finset (Fin k)}
    (hT : InA Sm Sp c a b d T) {w w' : V} (hw : ¬ JMatched c a b w) (hw' : ¬ JMatched c a b w')
    (hc : colSet c w = T ∨ colSet c w = swapSet a b T)
    (hc' : colSet c w' = T ∨ colSet c w' = swapSet a b T) : w = w' := by
  classical
  obtain ⟨-, -, -, -, -, h1, h2⟩ := hT
  have hiT := hn2 (swapSet a b T)
  have l1 := unm_lt hw
  have l2 := unm_lt hw'
  rcases hc with e | e <;> rcases hc' with e' | e'
  · exact unm_eq hw hw' (e.trans e'.symm) (by rw [e] at l1 ⊢; omega)
  · exfalso; rw [e] at l1; rw [e', swapSet_swapSet] at l2; omega
  · exfalso; rw [e, swapSet_swapSet] at l1; rw [e'] at l2; omega
  · exact unm_eq hw hw' (e.trans e'.symm) (by rw [e, swapSet_swapSet] at l1 ⊢; omega)

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem exists_unm {d : ℕ} {T : Finset (Fin k)} (hT : InA Sm Sp c a b d T) :
    ∃ w, ¬ JMatched c a b w ∧ (colSet c w = T ∨ colSet c w = swapSet a b T) := by
  classical
  obtain ⟨-, -, -, -, -, h1, h2⟩ := hT
  by_cases hlt : cnt c (swapSet a b T) < cnt c T
  · exact ⟨startV c a b hlt, startV_unm hlt, Or.inl (startV_spec hlt).1⟩
  · have hlt' : cnt c (swapSet a b (swapSet a b T)) < cnt c (swapSet a b T) := by
      rw [swapSet_swapSet]; omega
    exact ⟨startV c a b hlt', startV_unm hlt', Or.inr (startV_spec hlt').1⟩

open Classical in
/-- The `a`-side set of the pair of `w`. -/
noncomputable def Tof (c : PEC G (Fin k)) (a b : Fin k) (w : V) : Finset (Fin k) :=
  if a ∈ colSet c w then colSet c w else swapSet a b (colSet c w)

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem Tof_eq {d : ℕ} {T : Finset (Fin k)} (hT : InA Sm Sp c a b d T) {w : V}
    (hc : colSet c w = T ∨ colSet c w = swapSet a b T) : Tof c a b w = T := by
  classical
  unfold Tof
  rcases hc with e | e
  · rw [e, ite_eq_left hT.2.2.1]
  · rw [e, ite_eq_right (swap_mem_a hT.2.2.2.1), swapSet_swapSet]

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem card_AV (hn2 : ∀ T, cnt c T ≤ 2) (d : ℕ) :
    #(univ.filter (AV Sm Sp c a b d)) = #(univ.filter (InA Sm Sp c a b d)) := by
  classical
  refine card_bij (fun w _ => Tof c a b w) (fun w hw => ?_) (fun w hw w' hw' h => ?_)
    (fun T hT => ?_)
  · obtain ⟨-, T, hT, hc⟩ := (mem_filter.1 hw).2
    rw [Tof_eq hT hc]; exact mem_filter.2 ⟨mem_univ _, hT⟩
  · obtain ⟨hu, T, hT, hc⟩ := (mem_filter.1 hw).2
    obtain ⟨hu', T', hT', hc'⟩ := (mem_filter.1 hw').2
    rw [Tof_eq hT hc, Tof_eq hT' hc'] at h
    subst h
    exact unm_unique hn2 hT hu hu' hc hc'
  · have hT' := (mem_filter.1 hT).2
    obtain ⟨w, hw, hc⟩ := exists_unm hT'
    exact ⟨w, mem_filter.2 ⟨mem_univ _, hw, T, hT', hc⟩, Tof_eq hT' hc⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem card_BV (hn2 : ∀ T, cnt c T ≤ 2) (d : ℕ) :
    #(univ.filter (BV Sm Sp c a b d)) = #(univ.filter (InA Sm Sp c b a d)) := by
  classical
  have e : univ.filter (BV Sm Sp c a b d) = univ.filter (AV Sm Sp c b a d) := by
    ext w
    simp only [mem_filter, mem_univ, true_and, BV, AV, JMatched, swapSet_comm b a]
  rw [e, card_AV hn2]

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem AV_BV_excl {d d' : ℕ} {w : V} (h1 : AV Sm Sp c a b d w) (h2 : BV Sm Sp c a b d' w) :
    False := by
  classical
  obtain ⟨-, T, hT, hc⟩ := h1
  obtain ⟨-, T', hT', hc'⟩ := h2
  have hT'e : T' = swapSet a b T := by
    have ha' : a ∉ T' := hT'.2.2.2.1
    rcases hc with e | e <;> rcases hc' with e' | e'
    · exact absurd (e' ▸ e ▸ hT.2.2.1) ha'
    · rw [← swapSet_swapSet a b T', ← e', e]
    · rw [← e', e]
    · exfalso
      have : T = T' := by rw [← swapSet_swapSet a b T, ← e, e', swapSet_swapSet]
      exact ha' (this ▸ hT.2.2.1)
  have := hT'.2.2.2.2.2.1
  rw [hT'e] at this
  exact hT.2.2.2.2.2.2 this

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem AV_card {d : ℕ} {w : V} (h : AV Sm Sp c a b d w) : #(colSet c w) = d := by
  classical
  obtain ⟨-, T, hT, hc⟩ := h
  rcases hc with e | e
  · rw [e]; exact hT.2.2.2.2.1
  · rw [e, card_swapSet]; exact hT.2.2.2.2.1

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem BV_card {d : ℕ} {w : V} (h : BV Sm Sp c a b d w) : #(colSet c w) = d := by
  classical
  obtain ⟨-, T, hT, hc⟩ := h
  rcases hc with e | e
  · rw [e]; exact hT.2.2.2.2.1
  · rw [e, card_swapSet]; exact hT.2.2.2.2.1

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem AV_end {d : ℕ} {w : V} (h : AV Sm Sp c a b d w) : IsEnd c a b w := by
  classical
  obtain ⟨-, T, hT, hc⟩ := h
  rcases hc with e | e
  · left; rw [e]; exact ⟨hT.2.2.1, hT.2.2.2.1⟩
  · right; rw [e, mem_swapSet, mem_swapSet, Equiv.swap_apply_right, Equiv.swap_apply_left]
    exact ⟨hT.2.2.1, hT.2.2.2.1⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem BV_end {d : ℕ} {w : V} (h : BV Sm Sp c a b d w) : IsEnd c a b w := by
  classical
  obtain ⟨-, T, hT, hc⟩ := h
  rcases hc with e | e
  · right; rw [e]; exact ⟨hT.2.2.1, hT.2.2.2.1⟩
  · left; rw [e, mem_swapSet, mem_swapSet, Equiv.swap_apply_left, Equiv.swap_apply_right]
    exact ⟨hT.2.2.1, hT.2.2.2.1⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **The matching `J'`.** -/
theorem exists_xmatch :
    ∃ Jx : V → V → Prop, XMatch c a b Jx ∧
      (∀ u v, Jx u v → ∃ d, (AV Sm Sp c a b d u ∧ BV Sm Sp c a b d v) ∨
        (BV Sm Sp c a b d u ∧ AV Sm Sp c a b d v)) ∧
      (∀ d, #(univ.filter (AV Sm Sp c a b d)) ≤ #(univ.filter (BV Sm Sp c a b d)) →
        ∀ u, AV Sm Sp c a b d u → ∃ v, Jx u v) ∧
      (∀ d, #(univ.filter (BV Sm Sp c a b d)) ≤ #(univ.filter (AV Sm Sp c a b d)) →
        ∀ u, BV Sm Sp c a b d u → ∃ v, Jx u v) := by
  classical
  -- for every `d`, subsets of equal size and a bijection
  have hchoice : ∀ d, ∃ A0 B0 : Finset V, A0 ⊆ univ.filter (AV Sm Sp c a b d) ∧
      B0 ⊆ univ.filter (BV Sm Sp c a b d) ∧
      (#(univ.filter (AV Sm Sp c a b d)) ≤ #(univ.filter (BV Sm Sp c a b d)) →
        A0 = univ.filter (AV Sm Sp c a b d)) ∧
      (#(univ.filter (BV Sm Sp c a b d)) ≤ #(univ.filter (AV Sm Sp c a b d)) →
        B0 = univ.filter (BV Sm Sp c a b d)) ∧ #A0 = #B0 := by
    intro d
    set As := univ.filter (AV Sm Sp c a b d)
    set Bs := univ.filter (BV Sm Sp c a b d)
    by_cases hle : #As ≤ #Bs
    · obtain ⟨B0, hB0, hcB⟩ := exists_subset_card_eq hle
      refine ⟨As, B0, subset_refl _, hB0, fun _ => rfl, fun h => ?_, hcB.symm⟩
      exact eq_of_subset_of_card_le hB0 (by omega)
    · obtain ⟨A0, hA0, hcA⟩ := exists_subset_card_eq (le_of_lt (not_le.1 hle))
      exact ⟨A0, Bs, hA0, subset_refl _, fun h => absurd h hle, fun _ => rfl, hcA⟩
  choose A0 B0 hA0 hB0 hA0e hB0e hcard using hchoice
  have he : ∀ d, Fintype.card (A0 d) = Fintype.card (B0 d) := fun d => by
    rw [Fintype.card_coe, Fintype.card_coe, hcard d]
  let e : ∀ d, A0 d ≃ B0 d := fun d => Fintype.equivOfCardEq (he d)
  let Jx : V → V → Prop := fun u v => ∃ d, (∃ hu : u ∈ A0 d, ((e d) ⟨u, hu⟩ : V) = v) ∨
    (∃ hv : v ∈ A0 d, ((e d) ⟨v, hv⟩ : V) = u)
  have hAV : ∀ d u, u ∈ A0 d → AV Sm Sp c a b d u := fun d u hu => (mem_filter.1 (hA0 d hu)).2
  have hBV : ∀ d u, u ∈ B0 d → BV Sm Sp c a b d u := fun d u hu => (mem_filter.1 (hB0 d hu)).2
  have heB : ∀ d (u : A0 d), ((e d) u : V) ∈ B0 d := fun d u => ((e d) u).2
  have hpair : ∀ u v, Jx u v → ∃ d, (AV Sm Sp c a b d u ∧ BV Sm Sp c a b d v) ∨
      (BV Sm Sp c a b d u ∧ AV Sm Sp c a b d v) := by
    rintro u v ⟨d, ⟨hu, rfl⟩ | ⟨hv, rfl⟩⟩
    · exact ⟨d, Or.inl ⟨hAV d u hu, hBV d _ (heB d _)⟩⟩
    · exact ⟨d, Or.inr ⟨hBV d _ (heB d _), hAV d v hv⟩⟩
  refine ⟨Jx, ⟨?_, ?_, ?_⟩, hpair, ?_, ?_⟩
  · rintro u v ⟨d, h | h⟩
    · exact ⟨d, Or.inr h⟩
    · exact ⟨d, Or.inl h⟩
  · rintro u v w ⟨d, ⟨hu, rfl⟩ | ⟨hv, hev⟩⟩ ⟨d', ⟨hu', rfl⟩ | ⟨hw, hew⟩⟩
    · have : d = d' := (AV_card (hAV d u hu)).symm.trans (AV_card (hAV d' u hu'))
      subst this; rfl
    · exfalso
      exact AV_BV_excl (hAV d u hu) (hew ▸ hBV d' _ (heB d' _))
    · exfalso
      exact AV_BV_excl (hAV d' u hu') (hev ▸ hBV d _ (heB d _))
    · have hd : d = d' := (BV_card (hev ▸ hBV d _ (heB d _))).symm.trans
        (BV_card (hew ▸ hBV d' _ (heB d' _)))
      subst hd
      have : (⟨v, hv⟩ : A0 d) = ⟨w, hw⟩ := (e d).injective (Subtype.ext (hev.trans hew.symm))
      exact congrArg Subtype.val this
  · intro u v huv
    obtain ⟨d, h | h⟩ := hpair u v huv
    · exact ⟨AV_end h.1, h.1.1, fun e' => AV_BV_excl h.1 (e' ▸ h.2)⟩
    · exact ⟨BV_end h.1, h.1.1, fun e' => AV_BV_excl h.2 (e' ▸ h.1)⟩
  · intro d hle u hu
    have hu0 : u ∈ A0 d := by rw [hA0e d hle]; exact mem_filter.2 ⟨mem_univ _, hu⟩
    exact ⟨_, d, Or.inl ⟨hu0, rfl⟩⟩
  · intro d hle u hu
    have hu0 : u ∈ B0 d := by rw [hB0e d hle]; exact mem_filter.2 ⟨mem_univ _, hu⟩
    exact ⟨((e d).symm ⟨u, hu0⟩ : V), d, Or.inr ⟨((e d).symm ⟨u, hu0⟩).2, by simp⟩⟩

open Classical in
omit [DecidableEq V] [DecidableRel G.Adj] in
/-- **`g_a - g_b = #AV - #BV`.** -/
theorem gdiff_eq (hn2 : ∀ T, cnt c T ≤ 2) (ha : a ∈ Sp) (hb : b ∈ Sp) (haS : a ∉ Sm)
    (hbS : b ∉ Sm) (_ : a ≠ b) (d : ℕ) :
    (g Sm Sp c a d : ℤ) - g Sm Sp c b d =
      #(univ.filter (AV Sm Sp c a b d)) - #(univ.filter (BV Sm Sp c a b d)) := by
  classical
  rw [card_AV hn2, card_BV hn2]
  -- split by the other colour, then by the partner being a 1-pile
  set C : Finset (Fin k) → Prop := fun T => Sm ⊆ T ∧ T ⊆ Sp ∧ #T = d ∧ cnt c T = 1
  have split : ∀ (x y : Fin k), (g Sm Sp c x d : ℤ) =
      #(univ.filter fun T => C T ∧ x ∈ T ∧ y ∈ T) +
      #(univ.filter fun T => C T ∧ x ∈ T ∧ y ∉ T ∧ cnt c (swapSet x y T) = 1) +
      #(univ.filter fun T => InA Sm Sp c x y d T) := by
    intro x y
    unfold g
    have h1 := card_filter_add_card_filter_not
      (s := univ.filter fun T => Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) (fun T => y ∈ T)
    have h2 := card_filter_add_card_filter_not
      (s := (univ.filter fun T => Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1).filter
        fun T => ¬ y ∈ T) (fun T => cnt c (swapSet x y T) = 1)
    simp only [filter_filter] at h1 h2
    have e1 : (univ.filter fun T => (Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) ∧ y ∈ T) =
        univ.filter fun T => C T ∧ x ∈ T ∧ y ∈ T := by
      ext T; simp only [mem_filter, mem_univ, true_and, C]; tauto
    have e2 : (univ.filter fun T => ((Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) ∧
        ¬ y ∈ T) ∧ cnt c (swapSet x y T) = 1) =
        univ.filter fun T => C T ∧ x ∈ T ∧ y ∉ T ∧ cnt c (swapSet x y T) = 1 := by
      ext T; simp only [mem_filter, mem_univ, true_and, C]; tauto
    have e3 : (univ.filter fun T => ((Sm ⊆ T ∧ T ⊆ Sp ∧ x ∈ T ∧ #T = d ∧ cnt c T = 1) ∧
        ¬ y ∈ T) ∧ ¬ cnt c (swapSet x y T) = 1) = univ.filter fun T => InA Sm Sp c x y d T := by
      ext T; simp only [mem_filter, mem_univ, true_and]; unfold InA; tauto
    rw [e1] at h1; rw [e2, e3] at h2
    omega
  have hboth : (univ.filter fun T => C T ∧ a ∈ T ∧ b ∈ T) =
      univ.filter fun T => C T ∧ b ∈ T ∧ a ∈ T := by
    ext T; simp only [mem_filter, mem_univ, true_and]; tauto
  -- the pairs of 1-piles correspond under `i`
  have hpairs : #(univ.filter fun T => C T ∧ a ∈ T ∧ b ∉ T ∧ cnt c (swapSet a b T) = 1) =
      #(univ.filter fun T => C T ∧ b ∈ T ∧ a ∉ T ∧ cnt c (swapSet b a T) = 1) := by
    refine card_bij (fun T _ => swapSet a b T) (fun T hT => ?_) (fun T _ T' _ h => ?_)
      (fun T hT => ?_)
    · obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩ := (mem_filter.1 hT).2
      refine mem_filter.2 ⟨mem_univ _, ⟨?_, ?_, by rw [card_swapSet]; exact h3, h7⟩, ?_, ?_, ?_⟩
      · intro x hx
        have hxa : x ≠ a := fun e => haS (e ▸ hx)
        have hxb : x ≠ b := fun e => hbS (e ▸ hx)
        rw [mem_swapSet, Equiv.swap_apply_of_ne_of_ne hxa hxb]; exact h1 hx
      · intro x hx
        rw [mem_swapSet] at hx
        by_cases hxa : x = a
        · rw [hxa]; exact ha
        by_cases hxb : x = b
        · rw [hxb]; exact hb
        rw [Equiv.swap_apply_of_ne_of_ne hxa hxb] at hx; exact h2 hx
      · rw [mem_swapSet, Equiv.swap_apply_right]; exact h5
      · exact swap_mem_a h6
      · rw [swapSet_comm, swapSet_swapSet]; exact h4
    · rw [← swapSet_swapSet a b T, h, swapSet_swapSet]
    · obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7⟩ := (mem_filter.1 hT).2
      refine ⟨swapSet a b T, mem_filter.2 ⟨mem_univ _, ⟨?_, ?_, by rw [card_swapSet]; exact h3,
        by rw [swapSet_comm] at h7; exact h7⟩, ?_, ?_, ?_⟩, swapSet_swapSet a b T⟩
      · intro x hx
        have hxa : x ≠ a := fun e => haS (e ▸ hx)
        have hxb : x ≠ b := fun e => hbS (e ▸ hx)
        rw [mem_swapSet, Equiv.swap_apply_of_ne_of_ne hxa hxb]; exact h1 hx
      · intro x hx
        rw [mem_swapSet] at hx
        by_cases hxa : x = a
        · rw [hxa]; exact ha
        by_cases hxb : x = b
        · rw [hxb]; exact hb
        rw [Equiv.swap_apply_of_ne_of_ne hxa hxb] at hx; exact h2 hx
      · rw [mem_swapSet, Equiv.swap_apply_left]; exact h5
      · rw [mem_swapSet, Equiv.swap_apply_right]; exact h6
      · rw [swapSet_swapSet]; exact h4
  have s1 := split a b
  have s2 := split b a
  rw [hboth] at s1
  rw [hpairs] at s1
  linarith
end Bkls.L8

end LeanPool.BalancedEdgeColourings
