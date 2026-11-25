/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

import Mathlib.Tactic.Push
public import LeanPool.DynamicMcs.GreedySearch

/-!
# Locality and correctness of single-edge updates

An insertion can first invalidate a choice between the two endpoints. A
deletion can first invalidate only the choice of the later endpoint. Correctness
follows from the legality of the retained prefix and greedy continuation.
-/

@[expose] public section

noncomputable section

namespace DynamicMcs

namespace Greedy
namespace Update
open UGraph

variable {n : ℕ} {G G' : UGraph n}

/-- The endpoint placed earlier in `order` (the candidate's `u` after its
possible swap of the two endpoints). -/
def earlierVert (order : List (Vert n)) (u v : Vert n) : Vert n :=
  if List.idxOf u order ≤ List.idxOf v order then u else v

/-- The vertex at position `laterPos` is exactly `laterVert`. -/
lemma laterVert_get (order : List (Vert n)) (u v : Vert n)
    (h : laterPos order u v < order.length) :
    order.get ⟨laterPos order u v, h⟩ = laterVert order u v := by
  classical
  unfold laterPos laterVert
  by_cases hh : List.idxOf u order ≤ List.idxOf v order
  · simp [hh]
  · have hle : List.idxOf v order ≤ List.idxOf u order := le_of_not_ge hh
    simp [hh, hle]

/-- The later endpoint is one of the two endpoints. -/
lemma laterVert_eq (order : List (Vert n)) (u v : Vert n) :
    laterVert order u v = u ∨ laterVert order u v = v := by
  classical
  unfold laterVert
  by_cases h : List.idxOf u order ≤ List.idxOf v order
  · right; exact ite_eq_left h
  · left; exact ite_eq_right h

/-- The earlier endpoint is one of the two endpoints. -/
lemma earlierVert_eq (order : List (Vert n)) (u v : Vert n) :
    earlierVert order u v = u ∨ earlierVert order u v = v := by
  classical
  unfold earlierVert
  by_cases h : List.idxOf u order ≤ List.idxOf v order
  · left; exact ite_eq_left h
  · right; exact ite_eq_right h

/-- The auxiliary scan reports exactly the first illegal step of the list it
walks: it returns `none` exactly when every choice it walks is legal. -/
lemma firstBreakAux_none (H : UGraph n) (order : List (Vert n)) (k : ℕ)
    (xs : List (Vert n)) :
    firstBreakAux H order k xs = none ↔
      ∀ i (hi : i < xs.length),
        IsMCSNext H (order.take (k + i)).toFinset (xs[i]) := by
  induction xs generalizing k with
  | nil =>
      constructor
      · intro h i hi
        simp at hi
      · intro h
        simp [firstBreakAux]
  | cons x xs ih =>
      constructor
      · intro hnone i hi
        by_cases h : IsMCSNext H (order.take k).toFinset x
        · have heq : firstBreakAux H order k (x :: xs) = firstBreakAux H order (k + 1) xs := by
            simp [firstBreakAux, h]
          rw [heq] at hnone
          have hhall : ∀ j (hj : j < xs.length),
              IsMCSNext H (order.take (k + 1 + j)).toFinset (xs[j]) :=
            (ih (k + 1)).mp hnone
          cases i with
          | zero =>
              simpa using h
          | succ m =>
              have hm : m < xs.length := Nat.succ_lt_succ_iff.mp hi
              have hmt : (x :: xs)[m + 1] = xs[m] := by simp
              have hk : k + (m + 1) = k + 1 + m := by omega
              have hc : order.take (k + (m + 1)) = order.take (k + 1 + m) := by rw [hk]
              rw [hc, hmt]
              exact hhall m hm
        · simp [firstBreakAux, h] at hnone
      · intro hall
        by_cases h : IsMCSNext H (order.take k).toFinset x
        · rw [show firstBreakAux H order k (x :: xs) = firstBreakAux H order (k + 1) xs by
            simp [firstBreakAux, h]]
          exact (ih (k + 1)).mpr (by
            intro j hj
            have hj1 : j + 1 < (x :: xs).length := by
              rw [List.length_cons]
              omega
            have hjlegal := hall (j + 1) hj1
            have hk : k + 1 + j = k + (j + 1) := by omega
            rw [hk]
            simpa using hjlegal)
        · exfalso
          have h0 := hall 0 (by simp)
          exact h h0

/-- If the scan returns `some j`, the returned position is at least the base
`k`. -/
lemma firstBreakAux_some_ge (H : UGraph n) (order : List (Vert n)) (k j : ℕ)
    (xs : List (Vert n)) : firstBreakAux H order k xs = some j → k ≤ j := by
  induction xs generalizing k j with
  | nil =>
      intro hn
      simp [firstBreakAux] at hn
  | cons x xs ih =>
      intro hn
      by_cases hx : IsMCSNext H (order.take k).toFinset x
      · have heq : firstBreakAux H order k (x :: xs) = firstBreakAux H order (k + 1) xs := by
          simp [firstBreakAux, hx]
        have hrec := ih (k + 1) j (heq ▸ hn)
        omega
      · have hteq : firstBreakAux H order k (x :: xs) = some k := by
          simp [firstBreakAux, hx]
        have hj : j = k := by
          rw [hteq] at hn
          exact (Option.some.inj hn).symm
        rw [hj]

/-- Scanning only the first `m` elements reports the same first break as the
full scan, provided that break lies among those `m` positions. -/
lemma firstBreakAux_take (H : UGraph n) (order : List (Vert n)) :
    ∀ (k m : ℕ) (xs : List (Vert n)),
      firstBreakAux H order k (xs.take m) =
        (firstBreakAux H order k xs).filter (fun j => decide (j < k + m)) := by
  intro k m xs
  induction xs generalizing k m with
  | nil => simp [firstBreakAux]
  | cons x xs ih =>
      cases m with
      | zero =>
          cases h : firstBreakAux H order k (x :: xs) with
          | none => simp [firstBreakAux]
          | some j =>
              have hkj := firstBreakAux_some_ge H order k j (x :: xs) h
              have hnot : ¬ j < k := by omega
              simp [firstBreakAux, Option.filter, hnot]
      | succ m =>
          by_cases hx : IsMCSNext H (order.take k).toFinset x
          · simp only [List.take_succ_cons, firstBreakAux, hx, ↓reduceIte]
            rw [ih, show k + (m + 1) = k + 1 + m by omega]
          · simp [List.take_succ_cons, firstBreakAux, Option.filter, hx]

/-- The bounded window probe equals the full-suffix scan filtered to the
window: stopping the scan at `k1` loses nothing. -/
theorem firstBreakWindow_eq_scan (H : UGraph n) (order : List (Vert n)) (k0 k1 : ℕ) :
    firstBreakWindow H order k0 k1 =
      (firstBreak H order k0).filter (fun j => decide (j ≤ k1)) := by
  unfold firstBreakWindow firstBreak
  rw [firstBreakAux_take]
  cases h : firstBreakAux H order k0 (order.drop k0) with
  | none => rfl
  | some j =>
      have := firstBreakAux_some_ge H order k0 j _ h
      simp only [Option.filter, decide_eq_true_eq]
      split_ifs <;> first | rfl | (exfalso; omega)

/-- The auxiliary scan returns `some (k + r)` exactly when the first `r`
choices are legal and the `r`-th is not. -/
lemma firstBreakAux_some (H : UGraph n) (order : List (Vert n)) (k : ℕ)
    (xs : List (Vert n)) (r : ℕ) :
    firstBreakAux H order k xs = some (k + r) ↔
      ∃ (hr : r < xs.length),
        (¬ IsMCSNext H (order.take (k + r)).toFinset (xs[r])) ∧
        ∀ i (hi : i < r),
          IsMCSNext H (order.take (k + i)).toFinset (xs[i]) := by
  induction xs generalizing k r with
  | nil =>
      constructor
      · intro hn
        exfalso
        simp [firstBreakAux] at hn
      · intro h
        rcases h with ⟨hr, _⟩
        simp at hr
  | cons x xs ih =>
      constructor
      · intro hn
        by_cases hx : IsMCSNext H (order.take k).toFinset x
        · -- x legal: the break (if any) is inside xs, index shifts by one
          cases r with
          | zero =>
              exfalso
              have heq : firstBreakAux H order k (x :: xs) = firstBreakAux H order (k + 1) xs := by
                simp [firstBreakAux, hx]
              have hsj : firstBreakAux H order (k + 1) xs = some k := by
                simpa [heq] using hn
              have hg := firstBreakAux_some_ge H order (k + 1) k xs hsj
              omega
          | succ r' =>
              have heq : firstBreakAux H order k (x :: xs) = firstBreakAux H order (k + 1) xs := by
                simp [firstBreakAux, hx]
              have hh : firstBreakAux H order (k + 1) xs = some ((k + 1) + r') := by
                rw [heq] at hn
                have hk' : k + (r' + 1) = (k + 1) + r' := by omega
                simpa [hk'] using hn
              have hrec := (ih (k + 1) r').mp hh
              rcases hrec with ⟨hr, hbad, hprev⟩
              refine ⟨Nat.succ_lt_succ_iff.mpr hr, ?_bad, ?_prev⟩
              · have hk : k + (r' + 1) = (k + 1) + r' := by omega
                rw [hk]
                simpa using hbad
              · intro i hi
                cases i with
                | zero => simpa using hx
                | succ m =>
                    have hm : m < r' := Nat.succ_lt_succ_iff.mp hi
                    have hprev' := hprev m hm
                    have hk : k + (m + 1) = (k + 1) + m := by omega
                    rw [hk]
                    simpa using hprev'
        · -- x illegal: break at position 0, so r = 0
          have hteq : firstBreakAux H order k (x :: xs) = some k := by
            simp [firstBreakAux, hx]
          have hr0 : r = 0 := by
            rw [hteq] at hn
            have hi := (Option.some.inj hn).symm
            omega
          subst r
          refine ⟨by simp, ?_, ?_⟩
          · simpa using hx
          · intro i hi
            omega
      · intro h
        rcases h with ⟨hr, hbad, hprev⟩
        by_cases hx : IsMCSNext H (order.take k).toFinset x
        · -- r > 0 (the first element x is legal), shift index down by one
          have hrpos : 0 < r := by
            by_contra hnot
            have hrle : r ≤ 0 := Nat.not_lt.mp hnot
            have hr0 : r = 0 := Nat.eq_zero_of_le_zero hrle
            subst r
            exact hbad (by simpa using hx)
          have hlen : r - 1 < xs.length := by
            rw [List.length_cons] at hr
            omega
          have hrec' :
              (¬ IsMCSNext H (order.take (k + 1 + (r - 1))).toFinset (xs[r - 1])) ∧
              ∀ i (hi : i < r - 1),
                IsMCSNext H (order.take (k + 1 + i)).toFinset (xs[i]) := by
            constructor
            · have hk : k + 1 + (r - 1) = k + r := by omega
              have hget : (x :: xs)[r] = xs[r - 1] := by
                cases r with
                | zero => omega
                | succ s =>
                    change (x :: xs)[s + 1] = xs[s]
                    exact List.getElem_cons_succ x xs s (by rw [List.length_cons]; omega)
              simpa [hk, hget] using hbad
            · intro i hi
              have hi' : i + 1 < r := by omega
              have hprev' := hprev (i + 1) hi'
              have hget1 : (x :: xs)[i + 1] = xs[i] :=
                List.getElem_cons_succ x xs i (by rw [List.length_cons]; omega)
              have hk : k + 1 + i = k + (i + 1) := by omega
              simpa [hk, hget1] using hprev'
          have hrec : firstBreakAux H order (k + 1) xs = some ((k + 1) + (r - 1)) :=
            (ih (k + 1) (r - 1)).mpr ⟨hlen, hrec'.1, hrec'.2⟩
          calc
            firstBreakAux H order k (x :: xs)
                = firstBreakAux H order (k + 1) xs := by simp [firstBreakAux, hx]
            _ = some ((k + 1) + (r - 1)) := hrec
            _ = some (k + r) := by
                have hkr : (k + 1) + (r - 1) = k + r := by omega
                rw [hkr]
        · -- x illegal: r = 0
          have hr0 : r = 0 := by
            by_contra hnot
            have h0 : 0 < r := Nat.pos_of_ne_zero hnot
            exact hx (by simpa using hprev 0 h0)
          subst r
          simp [firstBreakAux, hx]

/-- Accessing the dropped suffix of an order at index `j` is accessing the
full order at index `k0 + j`. -/
lemma getElem_drop_order (order : List (Vert n)) (k0 j : ℕ) (hj : k0 + j < order.length) :
    (order.drop k0).get ⟨j, by
      have hlen := List.length_drop (l := order) (i := k0)
      omega⟩ = order.get ⟨k0 + j, hj⟩ := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  exact List.getElem_drop (xs := order) (i := k0) (j := j) (h := by
    have hlen := List.length_drop (l := order) (i := k0)
    omega)

/-- The unbounded scan reports exactly the first illegal step. -/
theorem firstBreak_some (H : UGraph n) (order : List (Vert n)) (k0 k : ℕ) :
    firstBreak H order k0 = some k ↔
      (∃ (hk : k < order.length),
        k0 ≤ k ∧ ¬ IsMCSNext H (order.take k).toFinset (order.get ⟨k, hk⟩) ∧
        ∀ (j : ℕ) (hj : j < order.length), k0 ≤ j → j < k →
          IsMCSNext H (order.take j).toFinset (order.get ⟨j, hj⟩)) := by
  classical
  unfold firstBreak
  constructor
  · intro h
    have hk0 : k0 ≤ k := firstBreakAux_some_ge H order k0 k (order.drop k0) h
    have h2 : firstBreakAux H order k0 (order.drop k0) = some (k0 + (k - k0)) := by
      rw [h, Nat.add_sub_cancel' hk0]
    rw [firstBreakAux_some] at h2
    obtain ⟨hr, h1, hall⟩ := h2
    have hlen : k < order.length := by
      rw [List.length_drop] at hr
      omega
    refine ⟨hlen, hk0, ?_, ?_⟩
    · have hget : (order.drop k0)[k - k0] = order.get ⟨k, hlen⟩ := by
        simp [Nat.add_sub_cancel' hk0, List.get_eq_getElem]
      have htake : order.take (k0 + (k - k0)) = order.take k := by
        rw [Nat.add_sub_cancel' hk0]
      rw [← hget, ← htake]
      exact h1
    · intro j hj hjk0 hjk
      have := hall (j - k0) (by omega)
      have hget : (order.drop k0)[j - k0] = order.get ⟨j, hj⟩ := by
        simp [Nat.add_sub_cancel' hjk0, List.get_eq_getElem]
      have htake : order.take (k0 + (j - k0)) = order.take j := by
        rw [Nat.add_sub_cancel' hjk0]
      rw [← hget, ← htake]
      exact this
  · rintro ⟨hk, hk0, h1, hall⟩
    refine ((firstBreakAux_some H order k0 (order.drop k0) (k - k0)).mpr
      ⟨by rw [List.length_drop]; omega, ?_, ?_⟩).trans ?_
    · have hIndex : k - k0 < (order.drop k0).length := by
        rw [List.length_drop]
        omega
      have hget : (order.drop k0)[k - k0]'hIndex = order.get ⟨k, hk⟩ := by
        simp [Nat.add_sub_cancel' hk0, List.get_eq_getElem]
      have htake : order.take (k0 + (k - k0)) = order.take k := by
        rw [Nat.add_sub_cancel' hk0]
      rw [hget, htake]
      exact h1
    · intro i hi
      have hj : k0 + i < order.length := by
        have hlen : (order.drop k0).length = order.length - k0 := List.length_drop (i := k0)
        omega
      have hIndex : i < (order.drop k0).length := by
        rw [List.length_drop]
        omega
      have hx : (order.drop k0)[i]'hIndex = order.get ⟨k0 + i, hj⟩ := by
        simp [List.get_eq_getElem]
      rw [hx]
      exact hall (k0 + i) hj (by omega) (by omega)
    · rw [Nat.add_sub_cancel' hk0]

/-- The unbounded scan finds nothing exactly when every step from `k0` on is
legal. -/
theorem firstBreak_none (H : UGraph n) (order : List (Vert n)) (k0 : ℕ) :
    firstBreak H order k0 = none ↔
      ∀ (j : ℕ) (hj : j < order.length), k0 ≤ j →
        IsMCSNext H (order.take j).toFinset (order.get ⟨j, hj⟩) := by
  classical
  unfold firstBreak
  rw [firstBreakAux_none]
  constructor
  · intro h j hj hjk0
    have hrj : j - k0 < (order.drop k0).length := by
      rw [List.length_drop]; omega
    have := h (j - k0) hrj
    have hget : (order.drop k0)[j - k0] = order.get ⟨j, hj⟩ := by
      simp [Nat.add_sub_cancel' hjk0]
    rw [← hget]
    simpa [Nat.add_sub_cancel' hjk0] using this
  · intro h r hr
    have hj : k0 + r < order.length := by
      have hlen : (order.drop k0).length = order.length - k0 := List.length_drop (i := k0)
      omega
    have hx : (order.drop k0)[r] = order.get ⟨k0 + r, hj⟩ := by
      simp [List.get_eq_getElem]
    rw [hx]
    exact h (k0 + r) hj (by omega)

/-- If the cardinalities of all *unchosen* vertices agree, the MCS-next
predicate transfers across the flip. -/
theorem IsMCSNext_of_eq_neigh_on (chosen : Finset (Vert n)) (w : Vert n)
    (h : ∀ x ∈ (Finset.univ : Finset (Vert n)) \ chosen,
      G.neigh chosen x = G'.neigh chosen x)
    (hnext : IsMCSNext G chosen w) : IsMCSNext G' chosen w := by
  classical
  rcases hnext with ⟨hwU, hwmax, hwmin⟩
  unfold IsMCSNext
  constructor
  · exact hwU
  constructor
  · intro x hx
    have heq_x := h x hx
    have heq_w := h w hwU
    rw [← heq_x]
    rw [← heq_w]
    exact hwmax x hx
  · intro x hx hc
    have heq_x := h x hx
    have heq_w := h w hwU
    have hcw : G.neigh chosen x = G.neigh chosen w := by
      calc G.neigh chosen x = G'.neigh chosen x := by rw [heq_x]
        _ = G'.neigh chosen w := hc
        _ = G.neigh chosen w := by rw [heq_w]
    exact hwmin x hx hcw

/-- On a flip of `{u, v}`, the only ordered pairs whose adjacency may differ
are `(u, v)` and `(v, u)`. -/
lemma flip_pair_ne (hflip : FlipOf G G' u v) (a b : Vert n)
    (h1 : a ≠ u ∨ b ≠ v) (h2 : a ≠ v ∨ b ≠ u) : G'.adj a b ↔ G.adj a b := by
  classical
  rcases hflip with ⟨huv, hflipadj⟩
  constructor
  · intro h
    rcases hflipadj a b with h' | h' | h'
    · exact h'.symm ▸ h
    · rcases h' with ⟨rfl, rfl⟩
      exfalso
      exact h1.elim (fun hu => hu rfl) (fun hv => hv rfl)
    · rcases h' with ⟨rfl, rfl⟩
      exfalso
      exact h2.elim (fun hu => hu rfl) (fun hv => hv rfl)
  · intro h
    rcases hflipadj a b with h' | h' | h'
    · exact h'.symm ▸ h
    · rcases h' with ⟨rfl, rfl⟩
      exfalso
      exact h1.elim (fun hu => hu rfl) (fun hv => hv rfl)
    · rcases h' with ⟨rfl, rfl⟩
      exfalso
      exact h2.elim (fun hu => hu rfl) (fun hv => hv rfl)

/-- On an insertion flip, `G'`-adjacency is `G`-adjacency plus the flipped
pair. -/
lemma adj_flip_ins (hflip : FlipOf G G' u v) (hins : ¬G.adj u v) (hins' : G'.adj u v)
    (a b : Vert n) : G'.adj a b ↔ G.adj a b ∨ (a = u ∧ b = v) ∨ (a = v ∧ b = u) := by
  classical
  rcases hflip with ⟨huv, hflipadj⟩
  constructor
  · intro h
    rcases hflipadj a b with h' | h' | h'
    · left; exact h'.symm ▸ h
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
  · intro h
    rcases h with h' | h' | h'
    · rcases hflipadj a b with heq | hpair | hpair
      · exact heq.symm ▸ h'
      · rcases hpair with ⟨rfl, rfl⟩
        exfalso
        exact hins h'
      · rcases hpair with ⟨rfl, rfl⟩
        exfalso
        exact hins (G.symm h')
    · rcases h' with ⟨rfl, rfl⟩
      exact hins'
    · rcases h' with ⟨rfl, rfl⟩
      exact G'.symm hins'

open Classical in
/-- Alternative form of `neigh`: the cardinality is the size of the
adjacency filter. -/
lemma neigh_alt (H : UGraph n) (s : Finset (Vert n)) (w : Vert n) :
    H.neigh s w = (s.filter (fun y => H.adj w y)).card := by
  classical
  unfold UGraph.neigh
  have hcard : (s.filter (fun y => H.adj w y)).card +
      (s.filter (fun y => ¬ H.adj w y)).card = s.card :=
    Finset.card_filter_add_card_filter_not _
  exact Nat.sub_eq_of_eq_add hcard.symm

/-- On inserting the edge `{u, v}`, for a prefix `s` containing the earlier
endpoint `a` and not the later endpoint `w`: every chosen vertex's
cardinality is unchanged; `w`'s cardinality rises by one; every other
unchosen vertex's cardinality is unchanged. -/
lemma neigh_flip_insert (hflip : FlipOf G G' u v) (hins : ¬G.adj u v) (hins' : G'.adj u v)
    (s : Finset (Vert n)) (a w : Vert n) (ha : a ∈ s) (hw : w ∉ s)
    (haw : a ≠ w) (hae : a = u ∨ a = v) (hwe : w = u ∨ w = v) :
    (∀ x ∈ s, G'.neigh s x = G.neigh s x) ∧
      G'.neigh s w = G.neigh s w + 1 ∧
      (∀ y, y ∉ s → y ≠ w → G'.neigh s y = G.neigh s y) := by
  classical
  -- Generic body for orientation (p ∈ s, q ∉ s), flip of undirected {p, q}
  -- turning (p, q) from absent to present.
  have gen : ∀ (p q : Vert n), FlipOf G G' p q → ¬G.adj p q → G'.adj p q →
      p ∈ s → q ∉ s →
      (∀ x ∈ s, G'.neigh s x = G.neigh s x) ∧
        G'.neigh s q = G.neigh s q + 1 ∧
        (∀ y, y ∉ s → y ≠ q → G'.neigh s y = G.neigh s y) := by
    intro p q hf hp hq hps hqn
    -- Component A: neighbors of already-chosen vertices unchanged.
    have hA : ∀ x ∈ s, G'.neigh s x = G.neigh s x := by
      intro x hx
      rw [neigh_alt, neigh_alt]
      have hfilter : s.filter (fun y => G'.adj x y) = s.filter (fun y => G.adj x y) := by
        apply Finset.filter_congr
        intro y hy
        have h1 : x ≠ p ∨ y ≠ q := Or.inr (fun h => hqn (h ▸ hy))
        have h2 : x ≠ q ∨ y ≠ p := Or.inl (fun h => hqn (h ▸ hx))
        exact flip_pair_ne hf x y h1 h2
      rw [hfilter]
    -- Component B: q's cardinality rises by one.
    have hB : G'.neigh s q = G.neigh s q + 1 := by
      rw [neigh_alt, neigh_alt]
      have hfilter : (s.filter (fun y => G'.adj q y)) =
          insert p (s.filter (fun y => G.adj q y)) := by
        apply Finset.ext
        intro y
        rw [Finset.mem_filter, Finset.mem_insert]
        constructor
        · intro h
          rcases h with ⟨hys, hqy⟩
          rcases (eq_or_ne y p) with hypp | hyp
          · exact Or.inl hypp
          · right
            rw [Finset.mem_filter]
            refine ⟨hys, ?_⟩
            have hyn : y ≠ q := fun h => hqn (h ▸ hys)
            have h1 : q ≠ p ∨ y ≠ q := Or.inr hyn
            have h2 : q ≠ q ∨ y ≠ p := Or.inr hyp
            exact (flip_pair_ne hf q y h1 h2).1 hqy
        · intro h
          rcases h with hypp | hg
          · subst y
            constructor
            · exact hps
            · exact G'.symm hq
          · have hys : y ∈ s := (Finset.mem_filter.mp hg).1
            have hqy : G.adj q y := (Finset.mem_filter.mp hg).2
            constructor
            · exact hys
            · by_cases hyp : y = p
              · exfalso
                have hqp : G.adj q p := by simpa [hyp] using hqy
                exact hp (G.symm hqp)
              · have hyn : y ≠ q := fun h => hqn (h ▸ hys)
                have h1 : q ≠ p ∨ y ≠ q := Or.inr hyn
                have h2 : q ≠ q ∨ y ≠ p := Or.inr hyp
                exact (flip_pair_ne hf q y h1 h2).2 hqy
      rw [hfilter]
      have hpn : p ∉ (s.filter (fun y => G.adj q y)) := by
        intro hpneg
        exact hp (G.symm (Finset.mem_filter.mp hpneg).2)
      rw [Finset.card_insert_of_notMem hpn]
    -- Component C: neighbors of other unchosen vertices unchanged.
    have hC : ∀ y, y ∉ s → y ≠ q → G'.neigh s y = G.neigh s y := by
        intro y hy hyq
        rw [neigh_alt, neigh_alt]
        have hfilter : s.filter (fun x => G'.adj y x) = s.filter (fun x => G.adj y x) := by
          apply Finset.filter_congr
          intro x hx
          have h1 : y ≠ p ∨ x ≠ q := Or.inr (fun h => hqn (h ▸ hx))
          have h2 : y ≠ q ∨ x ≠ p := Or.inl hyq
          exact flip_pair_ne hf y x h1 h2
        rw [hfilter]
    exact ⟨hA, hB, hC⟩
  -- now apply gen in the two orientations
  rcases hae with haa | hav
  · have hwv : w = v := by
      rcases hwe with hwu | hwv
      · exfalso
        exact haw (by rw [haa, hwu])
      · exact hwv
    have hPa : w = v := hwv
    have huins : u ∈ s := by simpa [haa.symm] using ha
    have hvnin : v ∉ s := by simpa [hwv.symm] using hw
    have hmain := gen u v hflip hins hins' huins hvnin
    simpa [hwv] using hmain
  · have hwu : w = u := by
      rcases hwe with hwu | hwv
      · exact hwu
      · exfalso
        exact haw (by rw [hav, hwv])
    have hvins : v ∈ s := by simpa [hav.symm] using ha
    have hunin : u ∉ s := by simpa [hwu.symm] using hw
    -- reorient the flip to (v, u)
    have hflipvu : FlipOf G G' v u := by
      rcases hflip with ⟨huv, hadj⟩
      refine ⟨huv.symm, ?_⟩
      intro x y
      rcases hadj x y with h | hd | hd
      · exact Or.inl h
      · exact Or.inr (Or.inr hd)
      · exact Or.inr (Or.inl hd)
    have hinsvu : ¬G.adj v u := fun hvu => hins (G.symm hvu)
    have hins'vu : G'.adj v u := G'.symm hins'
    have hmain := gen v u hflipvu hinsvu hins'vu hvins hunin
    simpa [hwu] using hmain

/-- When both endpoints of a flipped edge are already chosen, every unchosen
vertex's cardinality is unchanged: the only adjacency difference is `{u, v}`,
and neither endpoint is an unchosen vertex under consideration. -/
lemma neigh_eq_flip_both_chosen (chosen : Finset (Vert n)) (u v : Vert n)
    (hflip : FlipOf G G' u v) (hu : u ∈ chosen) (hv : v ∈ chosen)
    (x : Vert n) (hx : x ∉ chosen) :
    G.neigh chosen x = G'.neigh chosen x := by
  classical
  have hxu : x ≠ u := fun h => hx (h ▸ hu)
  have hxv : x ≠ v := fun h => hx (h ▸ hv)
  rw [neigh_alt, neigh_alt]
  have hfilter : chosen.filter (fun y => G.adj x y) =
      chosen.filter (fun y => G'.adj x y) := by
    apply Finset.filter_congr
    intro y hy
    have h1 : x ≠ u ∨ y ≠ v := Or.inl hxu
    have h2 : x ≠ v ∨ y ≠ u := Or.inl hxv
    exact (flip_pair_ne hflip x y h1 h2).symm
  rw [hfilter]

/-- If a vertex `x` is a legal MCS pick on `G`, and on `G'` only `w`'s
cardinality went down (all other unchosen vertices' cardinalities agree), then
`x` is still a legal MCS pick on `G'`, provided `x ≠ w`. -/
lemma IsMCSNext_of_drop (chosen : Finset (Vert n)) (w x : Vert n)
    (hneigh : ∀ y, y ∈ (Finset.univ : Finset (Vert n)) \ chosen → y ≠ w →
      G.neigh chosen y = G'.neigh chosen y)
    (hwle : G'.neigh chosen w ≤ G.neigh chosen w)
    (hnext : IsMCSNext G chosen x) (hxw : x ≠ w) : IsMCSNext G' chosen x := by
  classical
  rcases hnext with ⟨hxU, hxmax, hxmin⟩
  have hxG' : G'.neigh chosen x = G.neigh chosen x :=
    (hneigh x hxU hxw).symm
  unfold IsMCSNext
  constructor
  · exact hxU
  constructor
  · -- max cardinality on G'
    intro y hy
    by_cases hyw : y = w
    · subst y
      calc G'.neigh chosen w ≤ G.neigh chosen w := hwle
        _ ≤ G.neigh chosen x := hxmax w hy
        _ = G'.neigh chosen x := hxG'.symm
    · have hxmaxy : G.neigh chosen y ≤ G.neigh chosen x := hxmax y hy
      calc G'.neigh chosen y = G.neigh chosen y := (hneigh y hy hyw).symm
        _ ≤ G.neigh chosen x := hxmaxy
        _ = G'.neigh chosen x := hxG'.symm
  · -- least-index tiebreak on G'
    intro y hy hc'
    by_cases hyw : y = w
    · subst y
      -- w ties x on G': show they tie on G too, then use hxmin.
      have hGeq : G.neigh chosen w = G.neigh chosen x := by
        apply le_antisymm
        · exact hxmax w hy
        · have : G'.neigh chosen w = G.neigh chosen x := by
            rwa [hxG'] at hc'
          calc G.neigh chosen x = G'.neigh chosen w := this.symm
            _ ≤ G.neigh chosen w := hwle
      exact hxmin w hy hGeq
    · have hGeq : G.neigh chosen y = G.neigh chosen x := by
        calc G.neigh chosen y = G'.neigh chosen y := hneigh y hy hyw
          _ = G'.neigh chosen x := by exact hc'
          _ = G.neigh chosen x := hxG'
      exact hxmin y hy hGeq

/-- On deleting the edge `{u, v}`, for a prefix `s` containing the earlier
endpoint `a` and not the later endpoint `w`: every chosen vertex's
cardinality is unchanged; `w`'s cardinality drops by one; every other
unchosen vertex's cardinality is unchanged. -/
lemma neigh_flip_delete (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬G'.adj u v)
    (s : Finset (Vert n)) (a w : Vert n) (ha : a ∈ s) (hw : w ∉ s)
    (haw : a ≠ w) (hae : a = u ∨ a = v) (hwe : w = u ∨ w = v) :
    (∀ x ∈ s, G'.neigh s x = G.neigh s x) ∧
      G'.neigh s w + 1 = G.neigh s w ∧
      (∀ y, y ∉ s → y ≠ w → G.neigh s y = G'.neigh s y) := by
  classical
  have hflip_rev : FlipOf G' G u v := by
    rcases hflip with ⟨huv, hadj⟩
    refine ⟨huv, ?_⟩
    intro x y
    rcases hadj x y with h | hd | hd
    · left; exact h.symm
    · exact Or.inr (Or.inl hd)
    · exact Or.inr (Or.inr hd)
  have himp := neigh_flip_insert hflip_rev hdel' hdel s a w ha hw haw hae hwe
  rcases himp with ⟨hA, hB, hC⟩
  constructor
  · intro x hx
    exact (hA x hx).symm
  constructor
  · exact hB.symm
  · exact hC

/-! ## Window soundness (proved in later stages) -/

/-- Both endpoints of a flip lie in `order.take i` as soon as `i` exceeds
their later position. -/
lemma bothend_in_take_of_lt_laterPos (order : List (Vert n)) (u v : Vert n)
    (hmu : u ∈ order) (hmv : v ∈ order) {i : ℕ} (hi : laterPos order u v < i) :
    u ∈ order.take i ∧ v ∈ order.take i := by
  classical
  unfold laterPos at hi
  constructor
  · apply (List.mem_take_iff_idxOf_lt hmu).mpr
    exact lt_of_le_of_lt (Nat.le_max_left _ _) hi
  · apply (List.mem_take_iff_idxOf_lt hmv).mpr
    exact lt_of_le_of_lt (Nat.le_max_right _ _) hi

/-- Steps strictly after the later endpoint are legal on `G'` after any
flip: both endpoints lie in the prefix, so no unchosen vertex's
cardinality changes. -/
theorem legal_after_laterPos (order : List (Vert n)) (u v : Vert n)
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order)
    (i : ℕ) (hi : i < order.length) (hgt : laterPos order u v < i) :
    IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩) := by
  classical
  let chosen := (order.take i).toFinset
  have hmu : u ∈ order := mem_of_IsMCSOrdering order hvalid u
  have hmv : v ∈ order := mem_of_IsMCSOrdering order hvalid v
  have hboth := bothend_in_take_of_lt_laterPos order u v hmu hmv hgt
  have huC : u ∈ chosen := List.mem_toFinset.mpr hboth.1
  have hvC : v ∈ chosen := List.mem_toFinset.mpr hboth.2
  have hnextG : IsMCSNext G chosen (order.get ⟨i, hi⟩) := hvalid.2.2 i hi
  have hneigh : ∀ x, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
      G.neigh chosen x = G'.neigh chosen x := by
    intro x hx
    exact neigh_eq_flip_both_chosen chosen u v hflip huC hvC x (Finset.mem_sdiff.mp hx).2
  change IsMCSNext G' chosen (order.get ⟨i, hi⟩)
  exact IsMCSNext_of_eq_neigh_on chosen (order.get ⟨i, hi⟩) hneigh hnextG

/-- The earlier endpoint sits exactly at position `earlierPos` in the order. -/
lemma earlierVert_get (order : List (Vert n)) (u v : Vert n) (hmem : u ∈ order)
    (hmem' : v ∈ order) :
    order.get ⟨earlierPos order u v, by
      have h1 := List.idxOf_lt_length_of_mem hmem
      have h2 := List.idxOf_lt_length_of_mem hmem'
      unfold earlierPos
      omega⟩ = earlierVert order u v := by
  classical
  unfold earlierPos earlierVert
  by_cases h : List.idxOf u order ≤ List.idxOf v order
  · have hle : List.idxOf u order ≤ List.idxOf v order := h
    simp [ite_eq_left h, Nat.min_eq_left h]
  · have hle : List.idxOf v order ≤ List.idxOf u order := le_of_not_ge h
    simp [ite_eq_right h, Nat.min_eq_right hle]

/-- The earlier and later endpoints are distinct vertices. -/
lemma earlier_ne_later (order : List (Vert n)) (u v : Vert n)
    (huv : u ≠ v) :
    earlierVert order u v ≠ laterVert order u v := by
  classical
  by_cases hle : List.idxOf u order ≤ List.idxOf v order
  · -- earlier = u, later = v
    have hu : earlierVert order u v = u := by
      unfold earlierVert; rw [ite_eq_left hle]
    have hv : laterVert order u v = v := by
      unfold laterVert; rw [ite_eq_left hle]
    rw [hu, hv]
    exact huv
  · have hge : List.idxOf v order ≤ List.idxOf u order := le_of_not_ge hle
    have hu : laterVert order u v = u := by
      unfold laterVert; rw [ite_eq_right hle]
    have hv : earlierVert order u v = v := by
      unfold earlierVert; rw [ite_eq_right hle]
    rw [hv, hu]
    exact huv.symm

/-- The earlier position is strictly less than the later position (when
`u ≠ v`, both present and the order is a permutation). -/
lemma earlierPos_lt_laterPos (order : List (Vert n)) (u v : Vert n)
    (huv : u ≠ v) (hmu : u ∈ order) (hmv : v ∈ order) :
    earlierPos order u v < laterPos order u v := by
  classical
  unfold earlierPos laterPos
  by_cases hle : List.idxOf u order ≤ List.idxOf v order
  · -- min = idxOf u, max = idxOf v; need idxOf u < idxOf v
    have hu : List.idxOf u order < List.idxOf v order := by
      refine lt_of_le_of_ne hle ?_
      intro h
      exact huv ((List.idxOf_inj (y := v) hmu).mp h)
    rwa [Nat.min_eq_left hle, Nat.max_eq_right hle]
  · have hge : List.idxOf v order ≤ List.idxOf u order := le_of_not_ge hle
    have hv : List.idxOf v order < List.idxOf u order := by
      refine lt_of_le_of_ne hge ?_
      intro h
      have hvu : v = u := (List.idxOf_inj (y := u) hmv).mp h
      exact huv hvu.symm
    rwa [Nat.min_eq_right hge, Nat.max_eq_left hge]

/-- The position of the later endpoint in the order is exactly `laterPos`. -/
lemma idxOf_laterVert (order : List (Vert n)) (u v : Vert n) :
    List.idxOf (laterVert order u v) order = laterPos order u v := by
  classical
  unfold laterPos laterVert
  by_cases hle : List.idxOf u order ≤ List.idxOf v order
  · rw [ite_eq_left hle, Nat.max_eq_right hle]
  · have hge : List.idxOf v order ≤ List.idxOf u order := le_of_not_ge hle
    rw [ite_eq_right hle, Nat.max_eq_left hge]

/-- The position of the earlier endpoint in the order is exactly
`earlierPos`. -/
lemma idxOf_earlierVert (order : List (Vert n)) (u v : Vert n) :
    List.idxOf (earlierVert order u v) order = earlierPos order u v := by
  classical
  unfold earlierPos earlierVert
  by_cases hle : List.idxOf u order ≤ List.idxOf v order
  · rw [ite_eq_left hle, Nat.min_eq_left hle]
  · have hge : List.idxOf v order ≤ List.idxOf u order := le_of_not_ge hle
    rw [ite_eq_right hle, Nat.min_eq_right hge]

/-- Deletion, middle steps: for a deletion flip, a step strictly between the
endpoints stays legal on `G'`. -/
theorem legal_middle_delete (order : List (Vert n)) (u v : Vert n)
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬G'.adj u v)
    (hvalid : IsMCSOrdering G order)
    (i : ℕ) (hi : i < order.length)
    (hgt : earlierPos order u v < i) (hlt : i < laterPos order u v) :
    IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩) := by
  classical
  let chosen := (order.take i).toFinset
  let w := laterVert order u v
  let a := earlierVert order u v
  let x := order.get ⟨i, hi⟩
  have huv := hflip.1
  have hmu : u ∈ order := mem_of_IsMCSOrdering order hvalid u
  have hmv : v ∈ order := mem_of_IsMCSOrdering order hvalid v
  have hae : a = u ∨ a = v := earlierVert_eq order u v
  have hwe : w = u ∨ w = v := laterVert_eq order u v
  have haw : a ≠ w := earlier_ne_later order u v huv
  have hw_mem_order : w ∈ order := by
    rcases hwe with h1 | h2
    · rw [h1]; exact hmu
    · rw [h2]; exact hmv
  have ha_mem_order : a ∈ order := by
    rcases hae with h1 | h2
    · rw [h1]; exact hmu
    · rw [h2]; exact hmv
  -- a is chosen: idxOf a = earlierPos < i
  have haC : a ∈ chosen := by
    have hmem : a ∈ order.take i := by
      rw [List.mem_take_iff_idxOf_lt ha_mem_order, idxOf_earlierVert]
      exact hgt
    exact List.mem_toFinset.mpr hmem
  -- w is not chosen: idxOf w = laterPos ≥ i
  have hwN : w ∉ chosen := by
    rw [List.mem_toFinset]
    intro hwmem
    have hwi : List.idxOf w order < i :=
      (List.mem_take_iff_idxOf_lt hw_mem_order).mp hwmem
    have hlater : List.idxOf w order = laterPos order u v := idxOf_laterVert order u v
    rw [hlater] at hwi
    omega
  -- order[i] ≠ w: x has position i, w has position laterPos > i
  have hxw : x ≠ w := by
    intro hxw
    have hx_pos : List.idxOf x order = i := by
      change List.idxOf (order.get ⟨i, hi⟩) order = i
      exact List.get_idxOf hvalid.1 ⟨i, hi⟩
    rw [hxw, idxOf_laterVert] at hx_pos
    omega
  have hneigh_del := neigh_flip_delete hflip hdel hdel' chosen a w haC hwN haw hae hwe
  have hw_drop : G'.neigh chosen w + 1 = G.neigh chosen w := hneigh_del.2.1
  have hC : ∀ y, y ∉ chosen → y ≠ w → G.neigh chosen y = G'.neigh chosen y := hneigh_del.2.2
  -- pre-digest for IsMCSNext_of_drop
  have hneigh' : ∀ y, y ∈ (Finset.univ : Finset (Vert n)) \ chosen → y ≠ w →
      G.neigh chosen y = G'.neigh chosen y := by
    intro y hy hyw
    exact hC y (Finset.mem_sdiff.mp hy).2 hyw
  have hwle : G'.neigh chosen w ≤ G.neigh chosen w := by omega
  have hnextG : IsMCSNext G chosen x := hvalid.2.2 i hi
  change IsMCSNext G' chosen x
  exact IsMCSNext_of_drop chosen w x hneigh' hwle hnextG hxw

/-- If `w` is unchosen and has strictly larger cardinality than every other
unchosen vertex, then `w` is the legal MCS pick: the strict maximum settles
both the maximality and the tie-break clause. -/
lemma IsMCSNext_of_unique_max (H : UGraph n) (chosen : Finset (Vert n)) (w : Vert n)
    (hwU : w ∈ (Finset.univ : Finset (Vert n)) \ chosen)
    (hstrict : ∀ x, x ∈ (Finset.univ : Finset (Vert n)) \ chosen → x ≠ w →
      H.neigh chosen x < H.neigh chosen w) :
    IsMCSNext H chosen w := by
  classical
  unfold IsMCSNext
  constructor
  · exact hwU
  constructor
  · intro x hx
    by_cases hxw : x = w
    · subst x; omega
    · exact (hstrict x hx hxw).le
  · intro x hx hc
    by_cases hxw : x = w
    · subst x; exact le_refl w
    · have hlt := hstrict x hx hxw
      rw [hc] at hlt
      omega

/-- Insertion probe correctness: inside the insertion window `(pu, pv]`, the
old choice at step `k` is illegal on `G'` exactly when the later endpoint
beats it on `G'`: strictly larger cardinality, or equal cardinality with
smaller id.  (This is the arithmetic condition the candidate's `_first_break`
evaluates.) -/
theorem insert_break_iff (order : List (Vert n)) (u v : Vert n)
    (hflip : FlipOf G G' u v) (hins : ¬G.adj u v) (hins' : G'.adj u v)
    (hvalid : IsMCSOrdering G order)
    (k : ℕ) (hk : k < order.length)
    (hgt : earlierPos order u v < k) (hle : k ≤ laterPos order u v) :
    ¬ IsMCSNext G' (order.take k).toFinset (order.get ⟨k, hk⟩) ↔
      let w := laterVert order u v
      let c := G'.neigh (order.take k).toFinset (order.get ⟨k, hk⟩)
      let d := G'.neigh (order.take k).toFinset w
      d > c ∨ (d = c ∧ w < order.get ⟨k, hk⟩) := by
  classical
  let chosen := (order.take k).toFinset
  let x := order.get ⟨k, hk⟩
  let w := laterVert order u v
  have huv := hflip.1
  have hmu : u ∈ order := mem_of_IsMCSOrdering order hvalid u
  have hmv : v ∈ order := mem_of_IsMCSOrdering order hvalid v
  have hwe : w = u ∨ w = v := laterVert_eq order u v
  have hw_mem_order : w ∈ order := by
    rcases hwe with h1 | h2
    · rw [h1]; exact hmu
    · rw [h2]; exact hmv
  have hidx_w : List.idxOf w order = laterPos order u v := idxOf_laterVert order u v
  -- the later endpoint is not yet chosen at step k
  have hwN : w ∉ chosen := by
    rw [List.mem_toFinset]
    intro hwmem
    have hwi : List.idxOf w order < k :=
      (List.mem_take_iff_idxOf_lt hw_mem_order).mp hwmem
    rw [hidx_w] at hwi
    omega
  have hwU : w ∈ (Finset.univ : Finset (Vert n)) \ chosen :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwN⟩
  -- the old choice x is unchosen, and legal on G
  have hxN : x ∉ chosen := by
    rw [List.mem_toFinset]
    intro hxmem
    have hxi : List.idxOf x order < k :=
      (List.mem_take_iff_idxOf_lt (List.get_mem order ⟨k, hk⟩)).mp hxmem
    have hxpos : List.idxOf x order = k := List.get_idxOf hvalid.1 ⟨k, hk⟩
    rw [hxpos] at hxi
    omega
  have hxU : x ∈ (Finset.univ : Finset (Vert n)) \ chosen :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxN⟩
  have hnextG : IsMCSNext G chosen x := hvalid.2.2 k hk
  obtain ⟨_, hxmax, hxmin⟩ := hnextG
  -- the earlier endpoint is chosen at step k: idxOf a = earlierPos < k
  have haC : earlierVert order u v ∈ chosen := by
    have ham : earlierVert order u v ∈ order := by
      rcases earlierVert_eq order u v with h1 | h2
      · rw [h1]; exact hmu
      · rw [h2]; exact hmv
    have hmem : earlierVert order u v ∈ order.take k := by
      rw [List.mem_take_iff_idxOf_lt ham, idxOf_earlierVert]
      exact hgt
    exact List.mem_toFinset.mpr hmem
  -- the flip cardinality analysis on the prefix `chosen`
  have hAw := neigh_flip_insert hflip hins hins' chosen (earlierVert order u v) w
    haC hwN (earlier_ne_later order u v huv)
    (earlierVert_eq order u v) hwe
  -- w's cardinality rises by one on G'
  have hB : G'.neigh chosen w = G.neigh chosen w + 1 := hAw.2.1
  -- every other unchosen vertex's cardinality is unchanged on G'
  have hC : ∀ y, y ∉ chosen → y ≠ w → G'.neigh chosen y = G.neigh chosen y := hAw.2.2
  have hxC : ∀ y, y ∈ (Finset.univ : Finset (Vert n)) \ chosen → y ≠ w →
      G'.neigh chosen y = G.neigh chosen y := by
    intro y hy hyw
    exact hC y (Finset.mem_sdiff.mp hy).2 hyw
  constructor
  · intro hnot
    by_cases hxw : x = w
    · -- if x = w, the flip makes w a strict max on G', contradicting hnot
      have hwNext : IsMCSNext G' chosen w :=
        IsMCSNext_of_unique_max G' chosen w hwU (by
          intro y hy hyw
          have hGy := hxC y hy hyw
          have hmax' : G.neigh chosen y ≤ G.neigh chosen w := by
            rw [← hxw]
            exact hxmax y hy
          rw [hGy, hB]
          omega)
      have hxNext : IsMCSNext G' chosen x := by rw [hxw]; exact hwNext
      exfalso
      exact hnot hxNext
    · -- x ≠ w: on G' the cardinality of x is unchanged
      have hxG : G'.neigh chosen x = G.neigh chosen x := hxC x hxU hxw
      -- ¬IsMCSNext G' chosen x, with x unchosen, yields a witness y beating x
      have hsplit : (∃ y, y ∈ (Finset.univ : Finset (Vert n)) \ chosen ∧
            G'.neigh chosen x < G'.neigh chosen y) ∨
          (∃ y, y ∈ (Finset.univ : Finset (Vert n)) \ chosen ∧
            G'.neigh chosen y = G'.neigh chosen x ∧ y < x) := by
        by_cases hmax' : ∀ y, y ∈ (Finset.univ : Finset (Vert n)) \ chosen →
            G'.neigh chosen y ≤ G'.neigh chosen x
        · right
          have hCnot : ¬∀ y, y ∈ (Finset.univ : Finset (Vert n)) \ chosen →
              G'.neigh chosen y = G'.neigh chosen x → x ≤ y := by
            intro hmin'
            exact hnot ⟨hxU, hmax', hmin'⟩
          push Not at hCnot
          obtain ⟨y, hyU, heq, hge⟩ := hCnot
          exact ⟨y, hyU, heq, hge⟩
        · left
          push Not at hmax'
          obtain ⟨y, hyU, hge⟩ := hmax'
          exact ⟨y, hyU, hge⟩
      cases hsplit with
      | inl hex =>
          obtain ⟨y, hyU, hgt⟩ := hex
          -- y must be w: every other unchosen vertex keeps its G-cardinality
          have hyw : y = w := by
            by_contra hyn
            have hyG := hxC y hyU hyn
            rw [hxG, hyG] at hgt
            have hle := hxmax y hyU
            omega
          subst y
          exact Or.inl hgt
      | inr hex =>
          obtain ⟨y, hyU, heq, hlt⟩ := hex
          have hyw : y = w := by
            by_contra hyn
            have hyG := hxC y hyU hyn
            rw [hxG, hyG] at heq
            have hle := hxmin y hyU heq
            exact lt_irrefl y (lt_of_lt_of_le hlt hle)
          subst y
          exact Or.inr ⟨heq, hlt⟩
  · intro hdis
    -- whichever disjunct holds, x fails the G' MCS test via the witness w
    refine fun hnextG' => ?_
    obtain ⟨_, hmax', hmin'⟩ := hnextG'
    cases hdis with
    | inl hdg =>
        exact lt_irrefl _ (lt_of_lt_of_le hdg (hmax' w hwU))
    | inr heq =>
        exact lt_irrefl w (lt_of_lt_of_le heq.2 (hmin' w hwU heq.1))

/-- Deletion probe correctness: the candidate's probe fires exactly when
step `pv` (whose choice is the later endpoint) is illegal on `G'`. -/
theorem deletionBreaks_true_iff (order : List (Vert n)) (u v : Vert n) :
    deletionBreaks G' order u v = true ↔
      ¬ IsMCSNext G' (order.take (laterPos order u v)).toFinset
        (laterVert order u v) := by
  classical
  unfold deletionBreaks UGraph.isFalse
  by_cases h : IsMCSNext G' (order.take (laterPos order u v)).toFinset
    (laterVert order u v)
  · simp [h]
  · simp [h]

/-! ## Recombination (proved in later stages) -/

/-- An ordering whose every step is legal on `G'` is a valid MCS ordering of
`G'` (nodup and length are inherited from validity on `G`). -/
theorem ordering_of_steps_legal (order : List (Vert n))
    (hvalid : IsMCSOrdering G order)
    (hsteps : ∀ i (hi : i < order.length),
      IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩)) :
    IsMCSOrdering G' order := by
  exact ⟨hvalid.1, hvalid.2.1, hsteps⟩

/-- Regreeding from a legal prefix yields a valid MCS ordering. -/
theorem update_from_prefix (order : List (Vert n)) (k : ℕ)
    (hvalid : IsMCSOrdering G order)
    (hsteps : ∀ i (hi : i < order.length), i < k →
      IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩)) :
    IsMCSOrdering G' (greedySuffix G' (order.take k)) := by
  classical
  rcases hvalid with ⟨hnodup, hlen, hstep⟩
  refine greedySuffix_valid G' (order.take k) ?N ?S
  · exact hnodup.take
  · intro i hi
    have hi_lt_len : i < order.length := by
      have : (order.take k).length = min k order.length := by simp
      omega
    have hi_lt_k : i < k := by
      have : (order.take k).length = min k order.length := by simp
      omega
    have htake : (order.take k).take i = order.take i := by
      rw [List.take_take, Nat.min_eq_left (le_of_lt hi_lt_k)]
    have hget : (order.take k).get ⟨i, hi⟩ = order.get ⟨i, hi_lt_len⟩ := by
      exact List.getElem_take
    rw [htake, hget]
    exact hsteps i hi_lt_len hi_lt_k

/-- Regreeding from a full prefix is the identity. -/
theorem greedySuffix_full (H : UGraph n) (order : List (Vert n))
    (h : order.toFinset = (Finset.univ : Finset (Vert n))) :
    greedySuffix H order = order := by
  classical
  unfold greedySuffix mcsRemainder
  rw [h]
  simp [mcsLoop]

/-! ## Main theorems -/

/-- A valid MCS ordering is a permutation of all vertices. -/
lemma order_toFinset_univ (order : List (Vert n))
    (hvalid : IsMCSOrdering G order) :
    order.toFinset = (Finset.univ : Finset (Vert n)) := by
  classical
  refine Finset.eq_univ_of_forall (fun x => ?_)
  exact List.mem_toFinset.mpr (mem_of_IsMCSOrdering order hvalid x)

/-- `insert_edge` preserves the invariant: for every finite graphs `G`, `G'`
differing only by the inserted edge `{u, v}`, and every valid MCS ordering
`order` of `G`, the updated ordering is a valid MCS ordering of `G'`. -/
theorem insert_update_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (insertUpdate G' order u v) := by
  classical
  unfold insertUpdate
  -- Expose the `let` binding so the window result can be rewritten.
  change G'.IsMCSOrdering
    (let k := Option.getD (firstBreakWindow G' order
      (earlierPos order u v + 1) (laterPos order u v)) order.length;
      G'.greedySuffix (List.take k order))
  -- Window bounds of the probe: k0 = earlierPos + 1, k1 = laterPos.
  by_cases hk0 : firstBreak G' order (earlierPos order u v + 1) = none
  · -- No break at or after the earlier endpoint: keep the whole order.
    have hfull : Option.getD (firstBreakWindow G' order
        (earlierPos order u v + 1) (laterPos order u v)) order.length =
        order.length := by
      rw [firstBreakWindow_eq_scan]
      rw [hk0]
      simp
    rw [hfull]
    change G'.IsMCSOrdering (G'.greedySuffix (List.take order.length order))
    rw [List.take_length]
    rw [greedySuffix_full G' order (order_toFinset_univ order hvalid)]
    refine ordering_of_steps_legal order hvalid ?_
    intro i hi
    by_cases hi0 : i ≤ earlierPos order u v
    · exact prefix_preserved order u v hflip hvalid i hi0 hi
    · have hgeo : earlierPos order u v + 1 ≤ i := by omega
      exact (firstBreak_none G' order (earlierPos order u v + 1)).mp hk0 i hi hgeo
  · -- The scan finds a first break k.
    obtain ⟨k, hk⟩ :=
      (Option.ne_none_iff_exists (o := firstBreak G' order (earlierPos order u v + 1))).mp hk0
    have hk' : firstBreak G' order (earlierPos order u v + 1) = some k := hk.symm
    -- Tightness: the first break cannot lie past the later endpoint,
    -- because every step after `laterPos` is legal on `G'` for any flip.
    have htight : k ≤ laterPos order u v := by
      rcases (firstBreak_some G' order (earlierPos order u v + 1) k).mp hk'
        with ⟨hklen, _, hbad, _⟩
      by_contra hgt
      have hgt' : laterPos order u v < k := by omega
      exact hbad (legal_after_laterPos order u v hflip hvalid k hklen hgt')
    have hkd : Option.getD (firstBreakWindow G' order
        (earlierPos order u v + 1) (laterPos order u v)) order.length = k := by
      rw [firstBreakWindow_eq_scan]
      rw [hk']
      simp [Option.filter, htight]
    rw [hkd]
    change G'.IsMCSOrdering (G'.greedySuffix (List.take k order))
    refine update_from_prefix order k hvalid ?_
    intro i hi hi_lt_k
    by_cases hi0 : i ≤ earlierPos order u v
    · exact prefix_preserved order u v hflip hvalid i hi0 hi
    · have hgeo : earlierPos order u v + 1 ≤ i := by omega
      rcases (firstBreak_some G' order (earlierPos order u v + 1) k).mp hk'
        with ⟨_, _, _, hall⟩
      exact hall i hi hgeo hi_lt_k

/-- `delete_edge` preserves the invariant: for every finite graphs `G`, `G'`
differing only by the deleted edge `{u, v}`, and every valid MCS ordering
`order` of `G`, the updated ordering is a valid MCS ordering of `G'`. -/
theorem delete_update_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (deleteUpdate G' order u v) := by
  classical
  unfold deleteUpdate
  by_cases hb : deletionBreaks G' order u v = true
  · -- probe fires: regreedy from laterPos
    rw [ite_eq_left (by simpa [deletionBreaks] using hb)]
    refine update_from_prefix order (laterPos order u v) hvalid ?_
    intro i hi hi_lt
    by_cases hi0 : i ≤ earlierPos order u v
    · exact prefix_preserved order u v hflip hvalid i hi0 hi
    · -- i is a middle step: earlierPos < i < laterPos
      have hgt : earlierPos order u v < i := by omega
      exact legal_middle_delete order u v hflip hdel hdel' hvalid i hi hgt hi_lt
  · -- probe does not fire: keep the whole order, every step legal on G'
    rw [ite_eq_right (by simpa [deletionBreaks] using hb)]
    refine ordering_of_steps_legal order hvalid ?_
    intro i hi
    by_cases hi0 : i ≤ earlierPos order u v
    · exact prefix_preserved order u v hflip hvalid i hi0 hi
    · -- i > earlierPos: either middle (earlierPos < i < laterPos) or the later
      -- step (i = laterPos) or after (i > laterPos)
      have hgt0 : earlierPos order u v < i := by omega
      by_cases hlteq : i ≤ laterPos order u v
      · by_cases heq : i = laterPos order u v
        · -- step laterPos: ending `order.get i = laterVert`; the probe did not
          -- fire, so this step is legal on G'
          have positionBound : laterPos order u v < order.length := heq ▸ hi
          have hchoose := laterVert_get order u v positionBound
          -- deletionBreaks G' order u v = false: the pick is legal
          have hpop : deletionBreaks G' order u v = true ↔
              ¬ IsMCSNext G' (order.take (laterPos order u v)).toFinset
                (laterVert order u v) := deletionBreaks_true_iff order u v
          have hlegal : IsMCSNext G' (order.take (laterPos order u v)).toFinset
              (laterVert order u v) := by
            by_contra hn
            exact hb (hpop.mpr hn)
          subst heq
          rw [hchoose]
          exact hlegal
        · -- middle step
          have hlt : i < laterPos order u v := lt_of_le_of_ne hlteq heq
          exact legal_middle_delete order u v hflip hdel hdel' hvalid i hi hgt0 hlt
      · -- i > laterPos
        have hgt : laterPos order u v < i := lt_of_not_ge hlteq
        exact legal_after_laterPos order u v hflip hvalid i hi hgt

end Update
end Greedy
end DynamicMcs
