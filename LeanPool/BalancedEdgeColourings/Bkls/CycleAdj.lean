/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Cycle3

/-!
# One cycle, with adjacent matched vertices allowed

`cycle_colouring_adj`: as `Cyc.cycle_colouring`, but the internal matching may join adjacent
vertices. Following the article, two adjacent matched vertices `t − 1`, `t` are identified: the
edge `t − 1` between them is removed, the shorter cycle (where the identified vertex is free) is
coloured by induction, and the removed edge gets the third colour. On a triangle every proper
colouring separates all three colour sets, so adjacent pairs impose nothing there.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.Cyc

/-- The third colour. -/
theorem exists_third (a b : Fin 3) : ∃ c, c ≠ a ∧ c ≠ b := by
  by_contra h
  push Not at h
  have h0 := h 0; have h1 := h 1; have h2 := h 2
  omega

private theorem pair_distinct_third {α : Type*} [DecidableEq α] {a b c : α}
    (hca : c ≠ a) (hab : a ≠ b) : ({c, b} : Finset α) ≠ {a, c} := by
  intro e
  have hmem : a ∈ ({c, b} : Finset α) := by rw [e]; simp
  rcases Finset.mem_insert.1 hmem with h | h
  · exact hca h.symm
  · exact hab (Finset.mem_singleton.1 h)

private theorem val_sub_lt_pred {r : ℕ} [NeZero r] (e t : ZMod r)
    (he : e ≠ t - 1) : (e - t).val < r - 1 := by
  by_contra h
  have h1 : (e - t).val = r - 1 := by have := ZMod.val_lt (e - t); omega
  apply he
  have h2 : e - t = -1 := by rw [← cast_pred, ← h1, ZMod.natCast_zmod_val]
  rw [sub_eq_iff_eq_add] at h2
  rw [h2]; ring

private theorem identify_cycle_pair (r : ℕ)
  (ih :
    ∀ m < r,
      ∀ [NeZero m],
        3 ≤ m →
          ∀ (st : ZMod m → VState m),
            (∀ (i : ZMod m) (F : Finset (Fin 3)), st i = VState.ext F → F.card = 2) →
              (∀ (i j : ZMod m), st i = VState.int j → st j = VState.int i ∧ j ≠ i) →
                (Odd m → ∃ i, st i = VState.free) →
                  ¬(m = 6 ∧ ∀ (i : ZMod m), st i = VState.int (i + 3)) →
                    ∃ f,
                      (∀ (i : ZMod m), f i ≠ f (i + 1)) ∧
                        (∀ (i : ZMod m) (F : Finset (Fin 3)), st i = VState.ext F → S f i ≠ F) ∧
                          ∀ (i j : ZMod m), st i = VState.int j → S f i ≠ S f j)
  [NeZero r] (st : ZMod r → VState r)
  (hF : ∀ (i : ZMod r) (F : Finset (Fin 3)), st i = VState.ext F → F.card = 2)
  (hint : ∀ (i j : ZMod r), st i = VState.int j → st j = VState.int i ∧ j ≠ i)
  (t : ZMod r) (ht : st t = VState.int (t - 1))
  (ht' : st (t - 1) = VState.int t) (hr4 : r ≥ 4) :
  ∃ f,
    (∀ (i : ZMod r), f i ≠ f (i + 1)) ∧
      (∀ (i : ZMod r) (F : Finset (Fin 3)), st i = VState.ext F → S f i ≠ F) ∧
        ∀ (i j : ZMod r), st i = VState.int j → S f i ≠ S f j := by
  obtain ⟨r', hr'⟩ : ∃ r', r' = r - 1 := ⟨_, rfl⟩
  have : NeZero r' := ⟨by omega⟩
  let φ : ZMod r' → ZMod r := fun j => t + (j.val : ZMod r)
  let ψ : ZMod r → ZMod r' := fun e => (((e - t).val : ℕ) : ZMod r')
  have hjv : ∀ j : ZMod r', j.val < r - 1 := fun j => by have := ZMod.val_lt j; omega
  have hψφ : ∀ j, ψ (φ j) = j := fun j => by
    change ((((t + (j.val : ZMod r)) - t).val : ℕ) : ZMod r') = j
    rw [add_sub_cancel_left, val_cast_of_lt (show j.val < r by have := hjv j; omega),
      ZMod.natCast_zmod_val]
  have hval : ∀ e : ZMod r, e ≠ t - 1 → (e - t).val < r - 1 :=
    fun e he => val_sub_lt_pred e t he
  have hφψ : ∀ e, e ≠ t - 1 → φ (ψ e) = e := fun e he => by
    change t + ((((((e - t).val : ℕ) : ZMod r')).val : ℕ) : ZMod r) = e
    rw [val_cast_of_lt (show (e - t).val < r' by have := hval e he; omega),
      ZMod.natCast_zmod_val]
    ring
  have hφ0 : φ 0 = t := by simp [φ]
  have hφne : ∀ j : ZMod r', j ≠ 0 → φ j ≠ t ∧ φ j ≠ t - 1 := by
    intro j hj
    constructor
    · intro h
      apply hj
      rw [← hψφ j, h]
      simp [ψ]
    · intro h
      have h1 : ψ (t - 1) = j := by rw [← h, hψφ]
      have h2 : ψ (t - 1) = 0 := by
        change ((((t - 1 - t).val : ℕ)) : ZMod r') = 0
        rw [show t - 1 - t = -1 by ring, ← cast_pred, val_cast_of_lt (by omega),
          show r - 1 = r' by omega, ZMod.natCast_self]
      exact hj (h1 ▸ h2)
  have hψ0 : ∀ e, ψ e = 0 → e = t ∨ e = t - 1 := by
    intro e h
    by_cases he : e = t - 1
    · exact Or.inr he
    · left
      rw [← hφψ e he, h, hφ0]
  -- the states of the shorter cycle
  let mp : VState r → VState r' := fun s =>
    match s with
    | .free => .free
    | .ext F => .ext F
    | .int p => .int (ψ p)
  let st' : ZMod r' → VState r' := fun j => if j = 0 then .free else mp (st (φ j))
  have hst'0 : st' 0 = .free := by simp [st']
  have hst'j : ∀ j, j ≠ 0 → st' j = mp (st (φ j)) := fun j hj => by simp [st', hj]
  -- the partner of a vertex other than `t - 1`, `t` is not `t - 1`, `t`
  have hpart : ∀ i p, st i = .int p → i ≠ t → i ≠ t - 1 → p ≠ t ∧ p ≠ t - 1 := by
    intro i p h hi hi'
    have hp := (hint i p h).1
    constructor
    · intro e; subst e
      rw [ht] at hp
      exact hi' (VState.int.inj hp).symm
    · intro e; subst e
      rw [ht'] at hp
      exact hi (VState.int.inj hp).symm
  obtain ⟨f', hf1, hf2, hf3⟩ := ih r' (by omega) (by omega) st'
    (fun j F h => by
      by_cases hj : j = 0
      · rw [hj, hst'0] at h; cases h
      · rw [hst'j j hj] at h
        cases hs : st (φ j) with
        | free => simp [mp, hs] at h
        | ext F' => simp only [mp, hs] at h; rw [← VState.ext.inj h]; exact hF _ _ hs
        | int p => simp [mp, hs] at h)
    (fun j j' h => by
      by_cases hj : j = 0
      · rw [hj, hst'0] at h; cases h
      · rw [hst'j j hj] at h
        cases hs : st (φ j) with
        | free => simp [mp, hs] at h
        | ext F' => simp [mp, hs] at h
        | int p =>
          simp only [mp, hs] at h
          have hj' := (VState.int.inj h).symm
          obtain ⟨hp1, hp2⟩ := hpart _ _ hs (hφne j hj).1 (hφne j hj).2
          have hφp : φ j' = p := by rw [hj', hφψ p hp2]
          have hj'0 : j' ≠ 0 := fun e => by
            rcases hψ0 p (by rw [← hj', e]) with h' | h'
            · exact hp1 h'
            · exact hp2 h'
          refine ⟨?_, fun e => ?_⟩
          · rw [hst'j j' hj'0, hφp, (hint _ _ hs).1]
            simp only [mp, hψφ]
          · have := (hint _ _ hs).2
            apply this
            rw [← hφp, e])
    (fun _ => ⟨0, hst'0⟩)
    (fun ⟨_, hall⟩ => by
      have := hall 0
      rw [hst'0] at this
      cases this)
  -- the colouring of the original cycle
  obtain ⟨c, hc1, hc2⟩ := exists_third (f' (-1)) (f' 0)
  let f : ZMod r → Fin 3 := fun e => if e = t - 1 then c else f' (ψ e)
  have hft : f (t - 1) = c := by simp [f]
  have hfφ : ∀ j, f (φ j) = f' j := fun j => by
    by_cases hj : j = 0
    · subst hj
      have : φ 0 ≠ t - 1 := by
        rw [hφ0]; intro h
        have : (1 : ZMod r) = 0 := by
          have := congrArg (· - t) h
          simp only [sub_self] at this
          rw [show t - 1 - t = -1 by ring] at this
          exact neg_eq_zero.1 this.symm
        have h1 : ((1 : ℕ) : ZMod r) = 0 := by exact_mod_cast this
        rw [ZMod.natCast_eq_zero_iff] at h1
        have := Nat.le_of_dvd one_pos h1
        omega
      simp only [f, ite_eq_right this, hψφ]
    · simp only [f, ite_eq_right (hφne j hj).2, hψφ]
  have hψm1 : ψ (t - 1 - 1) = -1 := by
    change ((((t - 1 - 1 - t).val : ℕ)) : ZMod r') = -1
    have h2 : t - 1 - 1 - t = ((r - 2 : ℕ) : ZMod r) := by
      have : ((r - 2 : ℕ) : ZMod r) = ((r : ℕ) : ZMod r) - 2 := by
        rw [Nat.cast_sub (by omega)]; norm_num
      rw [this, ZMod.natCast_self]; ring
    rw [h2, val_cast_of_lt (by omega), show r - 2 = r' - 1 by omega, cast_pred]
  have hφm1 : φ (-1) = t - 1 - 1 := by
    rw [← hψm1, hφψ]
    intro h
    have : (1 : ZMod r) = 0 := by
      have := congrArg (· - (t - 1)) h
      simp only [sub_self] at this
      rw [show t - 1 - 1 - (t - 1) = -1 by ring] at this
      exact neg_eq_zero.1 this
    have h1 : ((1 : ℕ) : ZMod r) = 0 := by exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h1
    have := Nat.le_of_dvd one_pos h1
    omega
  have hφsub : ∀ j : ZMod r', j ≠ 0 → φ j - 1 = φ (j - 1) := by
    intro j hj
    change t + (j.val : ZMod r) - 1 = t + ((j - 1).val : ZMod r)
    rw [val_sub_one', ite_eq_right (fun h => hj ((ZMod.val_eq_zero j).1 h)),
      Nat.cast_sub (Nat.one_le_iff_ne_zero.2 (fun h => hj ((ZMod.val_eq_zero j).1 h)))]
    push_cast; ring
  -- every old edge other than `t - 1` comes from a new edge
  have hcover : ∀ e, e ≠ t - 1 → ∃ j, φ j = e := fun e he => ⟨ψ e, hφψ e he⟩
  refine ⟨f, fun e => ?_, fun i F h => ?_, fun i j h => ?_⟩
  · -- proper
    by_cases he : e = t - 1
    · rw [he, hft, sub_add_cancel, ← hφ0, hfφ]; exact hc2
    · by_cases he' : e + 1 = t - 1
      · rw [he', hft]
        have : e = t - 1 - 1 := by rw [← he']; ring
        rw [this, ← hφm1, hfφ]; exact hc1.symm
      · obtain ⟨j, rfl⟩ := hcover e he
        obtain ⟨j', hj'⟩ := hcover _ he'
        rw [← hj', hfφ, hfφ]
        have hjj : j' = j + 1 := by
          have h1 : φ j' - 1 = φ j := by rw [hj']; ring
          by_cases hj'0 : j' = 0
          · subst hj'0
            rw [hφ0] at h1
            exfalso; apply he; rw [← h1]
          · rw [hφsub j' hj'0] at h1
            have := congrArg ψ h1
            rw [hψφ, hψφ] at this
            rw [← this]; ring
        rw [hjj]; exact hf1 j
  · -- external restrictions
    have hit : i ≠ t := fun e => by rw [e, ht] at h; cases h
    have hit' : i ≠ t - 1 := fun e => by rw [e, ht'] at h; cases h
    obtain ⟨j, rfl⟩ := hcover i hit'
    have hj0 : j ≠ 0 := fun e => hit (by rw [e, hφ0])
    have hS : S f (φ j) = S f' j := by
      unfold S; rw [hφsub j hj0, hfφ, hfφ]
    rw [hS]
    apply hf2 j F
    rw [hst'j j hj0, h]
  · -- internal pairs
    have hA : S f t = {c, f' 0} := by unfold S; rw [hft, ← hφ0, hfφ]
    have hB : S f (t - 1) = {f' (-1), c} := by unfold S; rw [hft, ← hφm1, hfφ]
    have hAB : S f t ≠ S f (t - 1) := by
      rw [hA, hB]
      exact pair_distinct_third hc1 (by simpa using hf1 (-1))
    by_cases hit : i = t
    · rw [hit] at h ⊢
      rw [ht] at h
      rw [← VState.int.inj h]
      exact hAB
    by_cases hit' : i = t - 1
    · rw [hit'] at h ⊢
      rw [ht'] at h
      rw [← VState.int.inj h]
      exact fun e => hAB e.symm
    obtain ⟨hp1, hp2⟩ := hpart i j h hit hit'
    obtain ⟨a, rfl⟩ := hcover i hit'
    obtain ⟨b, rfl⟩ := hcover j hp2
    have ha0 : a ≠ 0 := fun e => hit (by rw [e, hφ0])
    have hb0 : b ≠ 0 := fun e => hp1 (by rw [e, hφ0])
    have hSa : S f (φ a) = S f' a := by unfold S; rw [hφsub a ha0, hfφ, hfφ]
    have hSb : S f (φ b) = S f' b := by unfold S; rw [hφsub b hb0, hfφ, hfφ]
    rw [hSa, hSb]
    apply hf3 a b
    rw [hst'j a ha0, h]
    simp only [mp, hψφ]

/-- **One cycle of Lemma 3, adjacent pairs allowed.** -/
theorem cycle_colouring_adj : ∀ (r : ℕ) [NeZero r], 3 ≤ r → ∀ st : ZMod r → VState r,
    (∀ i F, st i = .ext F → F.card = 2) →
    (∀ i j, st i = .int j → st j = .int i ∧ j ≠ i) →
    (Odd r → ∃ i, st i = .free) →
    ¬ (r = 6 ∧ ∀ i, st i = .int (i + 3)) →
    ∃ f : ZMod r → Fin 3, (∀ i, f i ≠ f (i + 1)) ∧
      (∀ i F, st i = .ext F → S f i ≠ F) ∧
      (∀ i j, st i = .int j → S f i ≠ S f j) := by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
  intro _ hr st hF hint hodd h6
  by_cases hadjP : ∃ t, st t = .int (t - 1)
  swap
  · -- no adjacent pairs
    push Not at hadjP
    refine cycle_colouring r hr st hF (fun i j h => ?_) hodd h6
    obtain ⟨h1, h2⟩ := hint i j h
    refine ⟨h1, h2, fun e => ?_, fun e => ?_⟩
    · apply hadjP j; rw [h1, e, add_sub_cancel_right]
    · apply hadjP i; rw [h, e, add_sub_cancel_right]
  obtain ⟨t, ht⟩ := hadjP
  have ht' : st (t - 1) = .int t := by
    have := (hint _ _ ht).1
    exact this
  rcases Nat.lt_or_ge r 4 with hr4 | hr4
  · -- a triangle: drop the internal pairs
    have hr3 : r = 3 := by omega
    subst hr3
    let st' : ZMod 3 → VState 3 := fun i =>
      match st i with
      | .int _ => .free
      | s => s
    have hst'ext : ∀ i F, st' i = .ext F → st i = .ext F := by
      intro i F h
      cases hs : st i with
      | free => simp [st', hs] at h
      | ext F' => simp only [st', hs] at h; rw [h]
      | int j => simp [st', hs] at h
    obtain ⟨f, hf1, hf2, -⟩ := cycle_colouring 3 le_rfl st'
      (fun i F h => hF i F (hst'ext i F h))
      (fun i j h => by
        cases hs : st i with
        | free => simp [st', hs] at h
        | ext F => simp [st', hs] at h
        | int j' => simp [st', hs] at h)
      (fun _ => ⟨t, by simp only [st', ht]⟩)
      (fun h => by omega)
    refine ⟨f, hf1, fun i F h => ?_, fun i j h => ?_⟩
    · exact hf2 i F (by simp only [st', h])
    · -- in a properly coloured triangle all colour sets differ
      have hji := (hint i j h).2
      have hcases' : j = i + 1 ∨ j = i + 2 := by
        have : ∀ a b : ZMod 3, b ≠ a → b = a + 1 ∨ b = a + 2 := by decide
        exact this i j hji
      have hdist : f (i - 1) ≠ f (i + 1) := by
        have h1 := hf1 (i + 1)
        have : ∀ a : ZMod 3, a + 1 + 1 = a - 1 := by decide
        rw [this] at h1
        exact fun e => h1 e.symm
      have hnot : f (i + 1) ∉ S f i := by
        unfold S
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        exact ⟨fun e => hdist e.symm, fun e => hf1 i e.symm⟩
      have hmem : f (i + 1) ∈ S f j := by
        unfold S
        rcases hcases' with rfl | rfl
        · simp
        · rw [show i + 2 - 1 = i + 1 by ring]; simp
      exact fun e => hnot (e ▸ hmem)
  · -- identify the adjacent vertices `t - 1` and `t`
    exact identify_cycle_pair r ih st hF hint t ht ht' hr4

end Bkls.Cyc

end LeanPool.BalancedEdgeColourings
