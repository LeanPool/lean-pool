/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Top.Len


/-!
# M5: Lemma T0 (the partition of a drain)

`startDrain` cuts the children's weights `ws` (total `S`) greedily at half, moves the cut right
past a pair of targets it would separate, and back if that reaches the end (`cutLen`, `shiftR`,
`shiftL`). With every unit (a child, or the two targets of a running drain) of weight at most `U`,
both parts weigh at most `⌊S/2⌋ + U` (`docs/PROOF.md` §4.5.2).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### The greedy cut -/

theorem cutLen_le (ws : List Nat) (b : Nat) : cutLen ws b ≤ ws.length := by
  induction ws generalizing b with
  | nil => simp [cutLen]
  | cons w t ih => unfold cutLen; split <;> simp [ih]

theorem cutLen_sum (ws : List Nat) (b : Nat) : (ws.take (cutLen ws b)).sum ≤ b := by
  induction ws generalizing b with
  | nil => simp [cutLen]
  | cons w t ih =>
    unfold cutLen; split
    · next h => simp only [List.take_succ_cons, List.sum_cons]; have := ih (b - w); omega
    · simp

theorem cutLen_max (ws : List Nat) (b : Nat) (h : cutLen ws b < ws.length) :
    b < (ws.take (cutLen ws b + 1)).sum := by
  induction ws generalizing b with
  | nil => simp at h
  | cons w t ih =>
    unfold cutLen at h ⊢
    split
    · next hw =>
      simp only [List.take_succ_cons, List.sum_cons]
      rw [ite_eq_left hw] at h
      have := ih (b - w) (by simp at h; omega)
      omega
    · next hw => simp; omega

/-! ### The pair shifts -/

/-- Pairs are disjoint: `k - 1, k` and `k, k + 1` are not both pairs. -/
def PairsOK (pr : Nat → Bool) (n : Nat) : Prop :=
  ∀ k, pr k = true → 1 ≤ k ∧ k < n ∧ pr (k + 1) = false

theorem shiftR_eq (pr : Nat → Bool) (n : Nat) (hp : PairsOK pr n) (k f : Nat) (hf : 2 ≤ f) :
    shiftR pr n f k = if 0 < k ∧ k < n ∧ pr k = true then k + 1 else k := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  unfold shiftR
  by_cases h : 0 < k && k < n
  · simp only [h, ite_true]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hk : pr k = true
    · rw [ite_eq_left hk, ite_eq_left ⟨h.1, h.2, hk⟩]
      unfold shiftR
      by_cases h2 : 0 < k + 1 && k + 1 < n
      · simp only [h2, ite_true, (hp k hk).2.2, Bool.false_eq_true, ite_false]
      · simp only [h2, Bool.false_eq_true, ite_false]
    · rw [ite_eq_right hk, ite_eq_right (fun h' => hk h'.2.2)]
  · simp only [h, Bool.false_eq_true, ite_false]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rw [ite_eq_right (fun h' => h ⟨h'.1, h'.2.1⟩)]

theorem shiftL_eq (pr : Nat → Bool) (n : Nat) (hp : PairsOK pr n) (k f : Nat) (hf : 2 ≤ f) :
    shiftL pr f k = if 0 < k ∧ pr k = true then k - 1 else k := by
  obtain ⟨g, rfl⟩ : ∃ g, f = g + 2 := ⟨f - 2, by omega⟩
  by_cases h : 0 < k
  · by_cases hk : pr k = true
    · rw [ite_eq_left ⟨h, hk⟩]
      have e1 : shiftL pr (g + 2) k = shiftL pr (g + 1) (k - 1) := by
        conv_lhs => unfold shiftL
        rw [ite_eq_left h, ite_eq_left hk]
      rw [e1]
      unfold shiftL
      by_cases h2 : k - 1 > 0
      · have : pr (k - 1) = false := by
          by_contra hc; simp only [Bool.not_eq_false] at hc
          have := (hp (k - 1) hc).2.2; rw [show k - 1 + 1 = k by omega, hk] at this; simp at this
        rw [ite_eq_left h2, this]; rfl
      · rw [ite_eq_right h2]
    · rw [ite_eq_right (fun h' => hk h'.2)]
      unfold shiftL; rw [ite_eq_left h, ite_eq_right hk]
  · rw [ite_eq_right (fun h' => h h'.1)]
    unfold shiftL; rw [ite_eq_right h]

/-! ### The cut only asks about pairs inside -/

theorem shiftR_congr {pr pr' : Nat → Bool} {n : Nat} (h : ∀ k, 1 ≤ k → k < n → pr k = pr' k) :
    ∀ f k, shiftR pr n f k = shiftR pr' n f k
  | 0, _ => rfl
  | f + 1, k => by
    unfold shiftR
    by_cases hk : 0 < k ∧ k < n
    · simp only [hk, decide_true, Bool.and_self, ite_true, h k (by omega) hk.2,
      shiftR_congr h f (k + 1)]
    · simp only [Bool.and_eq_true, decide_eq_true_eq, hk, ite_false]

theorem shiftL_congr {pr pr' : Nat → Bool} {n : Nat} (h : ∀ k, 1 ≤ k → k < n → pr k = pr' k) :
    ∀ f k, k < n → shiftL pr f k = shiftL pr' f k
  | 0, _, _ => rfl
  | f + 1, k, hk => by
    unfold shiftL
    by_cases h0 : k > 0
    · rw [ite_eq_left h0, ite_eq_left h0, h k h0 hk, shiftL_congr h f (k - 1) (by omega)]
    · rw [ite_eq_right h0, ite_eq_right h0]

theorem drainCut_congr {ws : List Nat} {pr pr' : Nat → Bool} (hh : Bool)
    (h : ∀ k, 1 ≤ k → k < ws.length → pr k = pr' k) : drainCut ws pr hh = drainCut ws pr' hh := by
  unfold drainCut
  simp only [shiftR_congr h]
  by_cases hn : ws.length = 0
  · simp only [hn]; rfl
  · rw [shiftL_congr h _ _ (by omega)]

/-! ### Lemma T0 -/

theorem sum_take_succ' (ws : List Nat) (m : Nat) (hm : m < ws.length) :
    (ws.take (m + 1)).sum = (ws.take m).sum + ws.getD m 0 := by
  rw [List.sum_take_succ _ _ hm, List.getD_eq_getElem _ _ hm]

theorem sum_take_le (ws : List Nat) {a b : Nat} (h : a ≤ b) : (ws.take a).sum ≤ (ws.take b).sum
  := by
  have : ws.take a = (ws.take b).take a := by rw [List.take_take, Nat.min_eq_left h]
  rw [this]
  exact List.Sublist.sum_le_sum (List.take_sublist _ _) (by simp)

/-- **Lemma T0.** The cut is strictly inside, does not separate a pair, and both parts weigh at
most `⌊S/2⌋ + U`. -/
theorem cutK_spec (ws : List Nat) (pr : Nat → Bool) (hh : Bool) (U : Nat) (hn : 2 ≤ ws.length)
    (hp : PairsOK pr ws.length) (hU1 : ∀ i, i < ws.length → ws.getD i 0 ≤ U)
    (hU2 : ∀ k, pr k = true → ws.getD (k - 1) 0 + ws.getD k 0 ≤ U)
    (hgive : hh = true → ¬ (ws.length = 2 ∧ pr 1 = true)) :
    let k := drainCut ws pr hh
    1 ≤ k ∧ k ≤ ws.length - 1 ∧ (hh = true → pr k = false) ∧
      (ws.take k).sum ≤ ws.sum / 2 + U ∧ ws.sum - (ws.take k).sum ≤ ws.sum / 2 + U := by
  intro k
  set n := ws.length with hnd
  set S := ws.sum with hS
  set c := cutLen (ws.take (n - 1)) (S / 2) with hc
  have hcle : c ≤ n - 1 := by
    have := cutLen_le (ws.take (n - 1)) (S / 2); simp at this; omega
  have hcs : (ws.take c).sum ≤ S / 2 := by
    have := cutLen_sum (ws.take (n - 1)) (S / 2)
    rwa [List.take_take, Nat.min_eq_left hcle] at this
  have hcm : c < n - 1 → S / 2 < (ws.take (c + 1)).sum := by
    intro h
    have := cutLen_max (ws.take (n - 1)) (S / 2) (by simp; omega)
    rwa [List.take_take, Nat.min_eq_left (by omega)] at this
  have hSn : (ws.take n).sum = S := by rw [List.take_of_length_le (le_refl _)]
  -- the bounds for the greedy cut `k0`
  set k0 := max c 1 with hk0
  have hk0b : 1 ≤ k0 ∧ k0 ≤ n - 1 := ⟨le_max_right _ _, max_le hcle (by omega)⟩
  have hk0L : (ws.take k0).sum ≤ S / 2 + U := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · have : k0 = 1 := by rw [hk0, h0]; rfl
      rw [this, show (1 : Nat) = 0 + 1 from rfl, sum_take_succ' ws 0 (by omega), List.take_zero,
        List.sum_nil, Nat.zero_add]
      have := hU1 0 (by omega); omega
    · have : k0 = c := by rw [hk0]; exact max_eq_left h0
      rw [this]; omega
  have hk0R : S - (ws.take k0).sum ≤ S / 2 + U := by
    rcases Nat.lt_or_ge c (n - 1) with hlt | hge
    · have hm := hcm hlt
      rcases Nat.eq_zero_or_pos c with h0 | h0
      · have : k0 = 1 := by rw [hk0, h0]; rfl
        rw [this]; rw [h0, Nat.zero_add] at hm; omega
      · have : k0 = c := by rw [hk0]; exact max_eq_left h0
        rw [this]
        rw [sum_take_succ' ws c (by omega)] at hm
        have := hU1 c (by omega)
        omega
    · have hce : c = n - 1 := by omega
      have : k0 = n - 1 := by rw [hk0, hce]; exact max_eq_left (by omega)
      rw [this]
      have h1 := sum_take_succ' ws (n - 1) (by omega)
      rw [show n - 1 + 1 = n by omega, hSn] at h1
      have := hU1 (n - 1) (by omega)
      omega
  have hk0σ : 1 ≤ c → (ws.take (k0 - 1)).sum ≤ S / 2 := by
    intro h1
    have : k0 = c := by rw [hk0]; exact max_eq_left h1
    rw [this]; exact le_trans (sum_take_le ws (by omega)) hcs
  -- the cut
  cases hh with
  | false =>
    have hk : k = k0 := by simp [k, drainCut, hk0, hc, hnd, hS]
    rw [hk]
    exact ⟨hk0b.1, hk0b.2, fun h => absurd h (by simp), hk0L, hk0R⟩
  | true =>
    have hk1 : shiftR pr n n k0 = if 0 < k0 ∧ k0 < n ∧ pr k0 = true then k0 + 1 else k0 :=
      shiftR_eq pr n hp k0 n hn
    by_cases hpk : pr k0 = true
    · rw [ite_eq_left ⟨by omega, by omega, hpk⟩] at hk1
      by_cases hend : k0 + 1 < n
      · have hk : k = k0 + 1 := by
          simp only [k, drainCut, ← hnd, ← hS, ← hc, ← hk0, ite_true, Bool.true_and]
          rw [hk1, ite_eq_right (by simp; omega)]
        rw [hk]
        refine ⟨by omega, by omega, fun _ => (hp k0 hpk).2.2, ?_, ?_⟩
        · rw [sum_take_succ' ws k0 (by omega)]
          have hpair := hU2 k0 hpk
          have h2 := sum_take_succ' ws (k0 - 1) (by omega)
          rw [show k0 - 1 + 1 = k0 by omega] at h2
          rcases Nat.eq_zero_or_pos c with h0 | h0
          · have : k0 = 1 := by rw [hk0, h0]; rfl
            rw [this] at h2 hpair ⊢
            simp only [Nat.sub_self] at h2 hpair
            rw [List.take_zero, List.sum_nil] at h2
            omega
          · have := hk0σ h0; omega
        · have := sum_take_le ws (show k0 ≤ k0 + 1 by omega); omega
      · have hkn : k0 = n - 1 := by omega
        have hgv := hgive rfl
        have hn3 : 3 ≤ n := by
          by_contra hc3
          apply hgv; refine ⟨by omega, ?_⟩
          rw [show 1 = k0 by omega]; exact hpk
        have hk : k = n - 2 := by
          simp only [k, drainCut, ← hnd, ← hS, ← hc, ← hk0, ite_true, Bool.true_and]
          rw [hk1, ite_eq_left (by simp; omega), shiftL_eq pr n hp (n - 1) n hn,
            ite_eq_left ⟨by omega, by rw [← hkn]; exact hpk⟩]
          omega
        rw [hk]
        have hpn : pr (n - 2) = false := by
          by_contra hc'; simp only [Bool.not_eq_false] at hc'
          have := (hp (n - 2) hc').2.2; rw [show n - 2 + 1 = n - 1 by omega, ← hkn, hpk] at this
          simp at this
        refine ⟨by omega, by omega, fun _ => hpn, ?_, ?_⟩
        · have h1 : 1 ≤ c := by
            by_contra h0
            have : k0 = 1 := by rw [hk0]; simp; omega
            omega
          have := hk0σ h1
          rw [hkn, show n - 1 - 1 = n - 2 by omega] at this
          omega
        · have hpair := hU2 k0 hpk
          rw [hkn, show n - 1 - 1 = n - 2 by omega] at hpair
          have h1 := sum_take_succ' ws (n - 1) (by omega)
          have h2 := sum_take_succ' ws (n - 2) (by omega)
          rw [show n - 1 + 1 = n by omega, hSn] at h1
          rw [show n - 2 + 1 = n - 1 by omega] at h2
          omega
    · rw [ite_eq_right (fun h => hpk h.2.2)] at hk1
      have hk : k = k0 := by
        simp only [k, drainCut, ← hnd, ← hS, ← hc, ← hk0, ite_true, Bool.true_and]
        rw [hk1, ite_eq_right (by simp; omega)]
      rw [hk]
      exact ⟨hk0b.1, hk0b.2, fun _ => by simpa using hpk, hk0L, hk0R⟩

end OrderMaintenance.Proof.Top
