/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
module

public import LeanPool.BalancedEdgeColourings.Bkls.Cycle2
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.Ring

/-!
# Colouring one cycle (Balister–Kostochka–Li–Schelp 2004, Lemma 3, one cycle)

The cycle has vertices `ZMod r`; edge `i` joins `i` and `i + 1`; an edge colouring is
`f : ZMod r → Fin 3`, proper iff `f i ≠ f (i + 1)`; the colour set of vertex `i` is
`S f i = {f (i - 1), f i}`. Each vertex is free, externally restricted (`ext F`, `|F| = 2`: we need
`S f i ≠ F`), or internally matched (`int j`: we need `S f i ≠ S f j`; the matching is an
involution without fixed points and never joins adjacent vertices).

`cycle_colouring`: a colouring exists if `r` is odd only when some vertex is free, and unless
`r = 6` with all six vertices matched to their opposites. The proof (the article's) reduces to the
`ℕ`-indexed cases of `Bkls.Cycle2` after renumbering from a suitable vertex `t` (`transfer`):
* some vertex `t` is not matched, and `t`, `t - 1` are not restricted by the same set: case A;
* otherwise, if some vertex is not matched, all vertices are restricted by the same `F`, `r` is
  even, and alternating `a ∈ F` and `c ∉ F` works (`caseB`);
* otherwise all vertices are matched: let `l` be the least distance of a matched pair; if
  `2 l < r`, start at a pair `t ~ t + l` with `t - 1 ≁ t - 1 + l`; if `2 l = r`, all pairs are
  opposite and `r ≠ 6`: case C.
-/

@[expose] public section

namespace LeanPool.BalancedEdgeColourings

namespace Bkls.Cyc

/-- The state of a vertex of the cycle. -/
inductive VState (r : ℕ) where
  | free : VState r
  | ext (F : Finset (Fin 3)) : VState r
  | int (j : ZMod r) : VState r

/-- The colours at vertex `i`: those of edges `i - 1` and `i`. -/
def S {r : ℕ} (f : ZMod r → Fin 3) (i : ZMod r) : Finset (Fin 3) := {f (i - 1), f i}

variable {r : ℕ} [NeZero r]

/-- The position of `x` counted from `t`. -/
def idx (t x : ZMod r) : ℕ := (x - t).val

/-- A state with partners given by their positions from `t`. -/
def conv (t : ZMod r) : VState r → PState
  | .free => .free
  | .ext F => .ext F
  | .int y => .int (idx t y)

/-- The states renumbered from `t`. -/
def nsOf (t : ZMod r) (st : ZMod r → VState r) (i : ℕ) : PState := conv t (st (t + i))

theorem one_le_r : 1 ≤ r := Nat.one_le_iff_ne_zero.2 (NeZero.ne r)

omit [NeZero r] in
theorem val_cast_of_lt {i : ℕ} (hi : i < r) : ((i : ZMod r)).val = i := by
  classical
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hi]
theorem idx_lt (t x : ZMod r) : idx t x < r := ZMod.val_lt _

omit [NeZero r] in
theorem idx_add (t : ZMod r) {i : ℕ} (hi : i < r) : idx t (t + i) = i := by
  classical
  unfold idx; rw [show t + (i : ZMod r) - t = i by ring]; exact val_cast_of_lt hi
theorem add_idx (t x : ZMod r) : t + (idx t x : ZMod r) = x := by
  unfold idx; rw [ZMod.natCast_zmod_val]; ring

theorem cast_pred : (((r - 1 : ℕ)) : ZMod r) = -1 := by
  have hr := (one_le_r : 1 ≤ r)
  have h : ((r - 1 : ℕ) : ZMod r) + 1 = 0 := by
    rw [show ((r - 1 : ℕ) : ZMod r) + 1 = ((r - 1 + 1 : ℕ) : ZMod r) by push_cast; ring,
      Nat.sub_add_cancel hr, ZMod.natCast_self]
  exact eq_neg_of_add_eq_zero_left h

theorem val_sub_one' (a : ZMod r) : (a - 1).val = if a.val = 0 then r - 1 else a.val - 1 := by
  have hr := (one_le_r : 1 ≤ r)
  split_ifs with h
  · rw [(ZMod.val_eq_zero a).1 h, zero_sub, ← cast_pred, val_cast_of_lt (by omega)]
  · have ha := ZMod.val_lt a
    have : a - 1 = ((a.val - 1 : ℕ) : ZMod r) := by
      rw [Nat.cast_sub (by omega), ZMod.natCast_zmod_val, Nat.cast_one]
    rw [this, val_cast_of_lt (by omega)]

theorem val_add_one' (a : ZMod r) : (a + 1).val = (a.val + 1) % r := by
  have : a + 1 = ((a.val + 1 : ℕ) : ZMod r) := by
    rw [Nat.cast_add, ZMod.natCast_zmod_val, Nat.cast_one]
  rw [this, ZMod.val_natCast]

theorem S_eq (t : ZMod r) (h : ℕ → Fin 3) (x : ZMod r) :
    S (fun y => h (idx t y)) x = cset r h (idx t x) := by
  have hx : idx t (x - 1) = if idx t x = 0 then r - 1 else idx t x - 1 := by
    unfold idx; rw [show x - 1 - t = (x - t) - 1 by ring, val_sub_one']
  change ({h (idx t (x - 1)), h (idx t x)} : Finset (Fin 3)) = cset r h (idx t x)
  unfold cset
  split_ifs with h0
  · rw [hx, ite_eq_left h0, h0]
  · rw [hx, ite_eq_right h0]; rfl

omit [NeZero r] in
theorem conv_int {t : ZMod r} {s : VState r} {j : ℕ} (h : conv t s = .int j) :
    ∃ y, s = .int y ∧ j = idx t y := by
  classical
  cases s with
  | free => cases h
  | ext F => cases h
  | int y => exact ⟨y, rfl, (PState.int.inj h).symm⟩

omit [NeZero r] in
theorem conv_ext {t : ZMod r} {s : VState r} {F : Finset (Fin 3)} (h : conv t s = .ext F) :
    s = .ext F := by
  classical
  cases s with
  | free => cases h
  | ext F' => rw [PState.ext.inj h]
  | int y => cases h

omit [NeZero r] in
theorem nsOf_zero (t : ZMod r) (st : ZMod r → VState r) : nsOf t st 0 = conv t (st t) := by
  classical
  unfold nsOf; rw [Nat.cast_zero, add_zero]
theorem nsOf_last (t : ZMod r) (st : ZMod r → VState r) :
    nsOf t st (r - 1) = conv t (st (t - 1)) := by
  unfold nsOf; rw [cast_pred, ← sub_eq_add_neg]

/-- Renumbering from `t` turns a colouring of `0, …, r - 1` into one of the cycle. -/
theorem transfer (st : ZMod r → VState r) (t : ZMod r) (h : ℕ → Fin 3)
    (hg : NatGood r (nsOf t st) h) :
    ∃ f : ZMod r → Fin 3, (∀ i, f i ≠ f (i + 1)) ∧ (∀ i F, st i = .ext F → S f i ≠ F) ∧
      (∀ i j, st i = .int j → S f i ≠ S f j) := by
  obtain ⟨hprop, hwrap, hext, hint⟩ := hg
  refine ⟨fun y => h (idx t y), fun x => ?_, fun x F hF => ?_, fun x y hxy => ?_⟩
  · change h (idx t x) ≠ h (idx t (x + 1))
    have hi := idx_lt t x
    have : idx t (x + 1) = (idx t x + 1) % r := by
      unfold idx; rw [show x + 1 - t = (x - t) + 1 by ring, val_add_one']
    rw [this]
    rcases Nat.lt_or_ge (idx t x + 1) r with hl | hl
    · rw [Nat.mod_eq_of_lt hl]; exact hprop _ hl
    · rw [show idx t x + 1 = r by omega, Nat.mod_self, show idx t x = r - 1 by omega]
      exact hwrap
  · rw [S_eq t h x]
    apply hext _ F (idx_lt t x)
    change conv t (st (t + (idx t x : ZMod r))) = _
    rw [add_idx, hF]; rfl
  · rw [S_eq t h x, S_eq t h y]
    apply hint _ _ (idx_lt t x)
    change conv t (st (t + (idx t x : ZMod r))) = _
    rw [add_idx, hxy]; rfl

/-- The renumbered matching is symmetric, loopless and joins no adjacent vertices. -/
theorem natSym (st : ZMod r → VState r)
    (hint : ∀ i j, st i = .int j → st j = .int i ∧ j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1)
    (t : ZMod r) : NatSym r (nsOf t st) := by
  intro i j hi hj
  unfold nsOf at hj
  obtain ⟨y, hs, hjy⟩ := conv_int hj
  obtain ⟨h1, h2, h3, h4⟩ := hint _ _ hs
  have hy : y = t + (j : ZMod r) := by rw [hjy, add_idx]
  refine ⟨?_, by rw [hjy]; exact idx_lt t y, ?_, ?_, ?_, ?_, ?_⟩
  · unfold nsOf; rw [← hy, h1]; change PState.int (idx t (t + i)) = _; rw [idx_add t hi]
  · intro e; apply h2; rw [hy, e]
  · intro e; apply h3; rw [hy, e]; push_cast; ring
  · intro e; apply h4; rw [hy, e]; push_cast; ring
  · rintro ⟨e0, e⟩; apply h4; rw [hy, e, e0, cast_pred]; push_cast; ring
  · rintro ⟨e0, e⟩; apply h3; rw [hy, e, e0, cast_pred]; push_cast; ring

theorem exists_not_mem (F : Finset (Fin 3)) (h : F.card = 2) : ∃ a, a ∉ F := by
  by_contra hc
  push Not at hc
  have : F = Finset.univ := Finset.eq_univ_iff_forall.2 hc
  rw [this] at h
  simp at h

omit [NeZero r] in
/-- The colour of edge `t` in case A. -/
theorem choose_a (s0 s1 : VState r) (hF0 : ∀ F, s0 = .ext F → F.card = 2)
    (hF1 : ∀ F, s1 = .ext F → F.card = 2) (hne : ¬ ∃ F, s0 = .ext F ∧ s1 = .ext F) :
    ∃ a : Fin 3, (∀ F, s0 = .ext F → a ∉ F) ∧ (∀ F, s1 = .ext F → a ∈ F) := by
  classical
  by_cases h0 : ∃ F0, s0 = .ext F0 <;> by_cases h1 : ∃ F1, s1 = .ext F1
  · obtain ⟨F0, rfl⟩ := h0
    obtain ⟨F1, rfl⟩ := h1
    have hne' : F0 ≠ F1 := fun e => hne ⟨F0, rfl, by rw [e]⟩
    have hsub : ¬ F1 ⊆ F0 := fun hs =>
      hne' (Finset.eq_of_subset_of_card_le hs (by rw [hF0 F0 rfl, hF1 F1 rfl])).symm
    obtain ⟨a, ha1, ha0⟩ := Finset.not_subset.1 hsub
    exact ⟨a, fun F e => by rw [← VState.ext.inj e]; exact ha0,
      fun F e => by rw [← VState.ext.inj e]; exact ha1⟩
  · obtain ⟨F0, rfl⟩ := h0
    obtain ⟨a, ha⟩ := exists_not_mem F0 (hF0 F0 rfl)
    exact ⟨a, fun F e => by rw [← VState.ext.inj e]; exact ha, fun F e => absurd ⟨F, e⟩ h1⟩
  · obtain ⟨F1, rfl⟩ := h1
    obtain ⟨a, ha⟩ := Finset.card_pos.1 (by rw [hF1 F1 rfl]; omega)
    exact ⟨a, fun F e => absurd ⟨F, e⟩ h0, fun F e => by rw [← VState.ext.inj e]; exact ha⟩
  · exact ⟨0, fun F e => absurd ⟨F, e⟩ h0, fun F e => absurd ⟨F, e⟩ h1⟩

/-- Case B: every vertex restricted by the same set, `r` even. -/
theorem caseB (heven : Even r) (F0 : Finset (Fin 3)) (hc : F0.card = 2)
    (st : ZMod r → VState r) (hall : ∀ x, st x = .ext F0) :
    ∃ f : ZMod r → Fin 3, (∀ i, f i ≠ f (i + 1)) ∧ (∀ i F, st i = .ext F → S f i ≠ F) ∧
      (∀ i j, st i = .int j → S f i ≠ S f j) := by
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (by omega : 0 < F0.card)
  obtain ⟨c, hc'⟩ := exists_not_mem F0 hc
  have hac : a ≠ c := fun e => hc' (e ▸ ha)
  let f : ZMod r → Fin 3 := fun x => if x.val % 2 = 0 then a else c
  have hprop : ∀ x, f x ≠ f (x + 1) := by
    intro x
    have hx := ZMod.val_lt x
    have h1 : (x + 1).val = (x.val + 1) % r := val_add_one' x
    obtain ⟨m, hm⟩ := heven
    simp only [f]
    rcases Nat.lt_or_ge (x.val + 1) r with hl | hl
    · rw [h1, Nat.mod_eq_of_lt hl]
      split_ifs <;> omega
    · rw [h1, show x.val + 1 = r by omega, Nat.mod_self]
      split_ifs <;> omega
  have hv : ∀ x, f x = a ∨ f x = c := fun x => by
    simp only [f]; split_ifs <;> simp
  refine ⟨f, hprop, fun i F hF => ?_, fun i j h => by rw [hall i] at h; cases h⟩
  rw [hall i] at hF
  rw [← VState.ext.inj hF]
  intro e
  have hcS : c ∈ S f i := by
    have hp := hprop (i - 1)
    rw [sub_add_cancel] at hp
    unfold S
    rcases hv (i - 1) with h1 | h1 <;> rcases hv i with h2 | h2
    · exact absurd (h1.trans h2.symm) hp
    · rw [h2]; simp
    · rw [h1]; simp
    · rw [h2]; simp
  rw [e] at hcS
  exact hc' hcS

/-- **One cycle of Lemma 3 (three colours).** -/
theorem cycle_colouring (r : ℕ) [NeZero r] (hr : 3 ≤ r) (st : ZMod r → VState r)
    (hF : ∀ i F, st i = .ext F → F.card = 2)
    (hint : ∀ i j, st i = .int j → st j = .int i ∧ j ≠ i ∧ j ≠ i + 1 ∧ i ≠ j + 1)
    (hodd : Odd r → ∃ i, st i = .free)
    (h6 : ¬ (r = 6 ∧ ∀ i, st i = .int (i + 3))) :
    ∃ f : ZMod r → Fin 3, (∀ i, f i ≠ f (i + 1)) ∧
      (∀ i F, st i = .ext F → S f i ≠ F) ∧
      (∀ i j, st i = .int j → S f i ≠ S f j) := by
  classical
  by_cases hA : ∃ t, (∀ y, st t ≠ .int y) ∧ ¬ ∃ F, st t = .ext F ∧ st (t - 1) = .ext F
  · -- case A
    obtain ⟨t, hti, htF⟩ := hA
    obtain ⟨a, ha0, ha1⟩ := choose_a (st t) (st (t - 1)) (hF t) (hF (t - 1)) htF
    obtain ⟨h, hh⟩ := natCaseA r hr (nsOf t st) (natSym st hint t)
      (fun j e => by
        rw [nsOf_zero] at e
        obtain ⟨y, hy, -⟩ := conv_int e
        exact hti y hy)
      a (fun F e => by rw [nsOf_zero] at e; exact ha0 F (conv_ext e))
      (fun F e => by rw [nsOf_last] at e; exact ha1 F (conv_ext e))
    exact transfer st t h hh
  push Not at hA
  by_cases hB : ∃ t, ∀ y, st t ≠ .int y
  · -- case B
    obtain ⟨t0, ht0⟩ := hB
    obtain ⟨F0, hF0a, -⟩ := hA t0 ht0
    have hall : ∀ k : ℕ, st (t0 - k) = .ext F0 := by
      intro k
      induction k with
      | zero => simpa using hF0a
      | succ k ih =>
        obtain ⟨F, hF1, hF2⟩ := hA (t0 - k) (fun y e => by rw [ih] at e; cases e)
        rw [ih] at hF1
        rw [show t0 - ((k + 1 : ℕ) : ZMod r) = t0 - k - 1 by push_cast; ring,
          VState.ext.inj hF1]
        exact hF2
    have hallx : ∀ x, st x = .ext F0 := fun x => by
      have := hall (t0 - x).val
      rwa [ZMod.natCast_zmod_val, sub_sub_cancel] at this
    have heven : Even r := by
      rcases Nat.even_or_odd r with h | h
      · exact h
      · obtain ⟨i, hi⟩ := hodd h
        rw [hallx i] at hi
        cases hi
    exact caseB heven F0 (hF _ _ (hallx 0)) st hallx
  -- case C: every vertex is matched
  push Not at hB
  have hex : ∃ l : ℕ, ∃ x, st x = .int (x + l) := by
    obtain ⟨y, hy⟩ := hB 0
    exact ⟨y.val, 0, by rw [ZMod.natCast_zmod_val, zero_add]; exact hy⟩
  obtain ⟨x0, hx0⟩ := Nat.find_spec hex
  have hmin0 : ∀ k < Nat.find hex, ∀ x, st x ≠ .int (x + k) :=
    fun k hk x e => Nat.find_min hex hk ⟨x, e⟩
  have hlr : Nat.find hex < r := by
    obtain ⟨y, hy⟩ := hB 0
    have := Nat.find_min' hex (m := y.val) ⟨0, by rw [ZMod.natCast_zmod_val, zero_add]; exact hy⟩
    exact lt_of_le_of_lt this (ZMod.val_lt y)
  generalize Nat.find hex = l at hx0 hmin0 hlr
  have hl2 : 2 ≤ l := by
    by_contra hc
    obtain ⟨-, h2, h3, -⟩ := hint _ _ hx0
    rcases (show l = 0 ∨ l = 1 by omega) with e | e
    · apply h2; rw [e]; simp
    · apply h3; rw [e]; simp
  have hdist : ∀ x (k : ℕ), k < r → st x = .int (x + k) → l ≤ k ∧ l ≤ r - k := by
    intro x k hk e
    refine ⟨Nat.le_of_not_lt fun h => hmin0 k h x e,
      Nat.le_of_not_lt fun h => hmin0 (r - k) h (x + k) ?_⟩
    rw [(hint _ _ e).1]
    congr 1
    rw [Nat.cast_sub hk.le, ZMod.natCast_self]
    ring
  have hl_le : l ≤ r - l := (hdist x0 l hlr hx0).2
  have hmin : ∀ t i j, i < r → nsOf t st i = .int j → i < j → l ≤ j - i ∧ l ≤ r - (j - i) := by
    intro t i j hi e hij
    unfold nsOf at e
    obtain ⟨y, hy, rfl⟩ := conv_int e
    have hj := idx_lt t y
    apply hdist (t + i) _ (by omega)
    rw [hy]
    congr 1
    rw [Nat.cast_sub hij.le]
    exact (add_idx t y).symm.trans (by ring)
  have finish : ∀ t, st t = .int (t + l) → (nsOf t st (l - 1) = .int (r - 1) → l ≠ 3) →
      ∃ f : ZMod r → Fin 3, (∀ i, f i ≠ f (i + 1)) ∧
        (∀ i F, st i = .ext F → S f i ≠ F) ∧ (∀ i j, st i = .int j → S f i ≠ S f j) := by
    intro t ht h3
    have h0 : nsOf t st 0 = .int l := by
      rw [nsOf_zero, ht]; change PState.int (idx t (t + l)) = _; rw [idx_add t hlr]
    obtain ⟨h, hh⟩ := natCaseC r l (nsOf t st) (natSym st hint t)
      (fun i F _ e => by
        unfold nsOf at e
        have := conv_ext e
        obtain ⟨y, hy⟩ := hB (t + i)
        rw [hy] at this
        cases this)
      hl2 (by omega) h0 (hmin t) h3
    exact transfer st t h hh
  by_cases hhalf : 2 * l < r
  · obtain ⟨t, ht, ht'⟩ : ∃ t, st t = .int (t + l) ∧ st (t - 1) ≠ .int (t - 1 + l) := by
      by_contra hc
      push Not at hc
      have hk : ∀ k : ℕ, st (x0 - k) = .int (x0 - k + l) := by
        intro k
        induction k with
        | zero => simpa using hx0
        | succ k ih =>
          have := hc _ ih
          rwa [show x0 - ((k + 1 : ℕ) : ZMod r) = x0 - k - 1 by push_cast; ring]
      have hallx : ∀ x, st x = .int (x + l) := fun x => by
        have := hk (x0 - x).val
        rwa [ZMod.natCast_zmod_val, sub_sub_cancel] at this
      have e1 := (hint _ _ (hallx 0)).1
      rw [hallx (0 + l)] at e1
      have e3 := VState.int.inj e1
      have e2 : ((2 * l : ℕ) : ZMod r) = 0 := by rw [← e3]; push_cast; ring
      rw [ZMod.natCast_eq_zero_iff] at e2
      have := Nat.le_of_dvd (by omega) e2
      omega
    refine finish t ht fun e _ => ?_
    unfold nsOf at e
    obtain ⟨y, hy, hyj⟩ := conv_int e
    have hy' : y = t - 1 := by rw [← add_idx t y, ← hyj, cast_pred]; ring
    rw [hy'] at hy
    apply ht'
    rw [(hint _ _ hy).1]
    congr 1
    rw [Nat.cast_sub (by omega : 1 ≤ l)]
    push_cast
    ring
  · have hrl : r = 2 * l := by omega
    have hl3 : l ≠ 3 := by
      intro e3
      apply h6
      refine ⟨by omega, fun x => ?_⟩
      obtain ⟨y, hy⟩ := hB x
      have hk := hdist x (y - x).val (ZMod.val_lt _)
        (by rw [ZMod.natCast_zmod_val, show x + (y - x) = y by ring]; exact hy)
      have h3 : (y - x).val = 3 := by omega
      rw [hy]
      congr 1
      have := congrArg (fun n : ℕ => (n : ZMod r)) h3
      simp only [ZMod.natCast_zmod_val] at this
      rw [show y = x + (y - x) by ring, this]
      push_cast
      ring
    exact finish x0 hx0 fun _ => hl3

end Bkls.Cyc

end LeanPool.BalancedEdgeColourings
