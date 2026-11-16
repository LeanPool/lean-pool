/-
Copyright (c) 2026 Denis Firsov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Denis Firsov
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.OrderMaintenance.Proof.Cost.TopIface


/-!
# M5: views of the top structure

The top structure (`OrderMaintenance/Model/Top.lean`, `docs/PROOF.md` §2.6) as the proofs see it:
* `nd s v`: node `v`; `pp s c j`: level `j` of chunk `c`'s stored path (`pp s c 0 = c`);
* `anc s c h`: the live ancestor of chunk `c` at height `h`, along `lpar` and `livePar`;
* `tw s cl u`: the true weight of `u`, the number of chunks of `cl` below it in the live tree;
* `rng s cl u`: the range of `u`, the chunks whose path passes through `u`;
* `tagF s c`: the tag that the labels along `c`'s path spell (`β`-bit digits).

And list facts: `Before l a b` (`a` strictly before `b` in `l`), and `GapsGe β B ls` (the labels
`ls`, with sentinels `-1` and `2^β`, have all gaps at least `B`).
-/


@[expose] public section

namespace OrderMaintenance.Proof.Top

open OrderMaintenance.Model OrderMaintenance.Proof
/-! ### The fields the top structure reads -/

/-- The top structure's part of a core: everything its code reads, with the chunk tags. -/
structure TS where
  P : Params
  nodes : Array Node
  path : Array (Array Nat)
  cin : Array (List Nat)
  lpar : Array Nat
  tag : Nat → Nat

def ts (s : Core) : TS :=
  ⟨s.P, s.nodes, s.path, s.cin, s.lpar, fun c => (s.C.getX c).tag⟩

/-- `TopSame` keeps the top structure's part. -/
theorem _root_.OrderMaintenance.Proof.TopSame.ts {s s' : Core} (h : TopSame s s') : ts s' = ts s
  := by
  obtain ⟨⟨h1, h2, h3, h4, -, -, -, -⟩, -, hl, hP⟩ := h
  unfold OrderMaintenance.Proof.Top.ts
  rw [h1, h2, h3, h4, hP]
  congr 1
  funext c; exact (hl c).2.2

/-! ### Views -/

section views
variable (s : TS)

def nd (v : Nat) : Node := s.nodes.getX v
def pth (c j : Nat) : Nat := (s.path.getX c).getX j
def lpr (c : Nat) : Nat := s.lpar.getX c
def cinT (c : Nat) : List Nat := s.cin.getX c
def ht (v : Nat) : Nat := (nd s v).height

/-- The tables holding entry `e` of height `h` (`h = 0`: a chunk). -/
def tabs (h e : Nat) : List Nat := if h = 0 then cinT s e else (nd s e).inTables

/-- Level `j` of chunk `c`'s path; level 0 is `c` itself. -/
def pp (c j : Nat) : Nat := if j = 0 then c else pth s c j

/-- The live ancestor of chunk `c` at height `h`. -/
def anc (c : Nat) : Nat → Nat
  | 0 => c
  | 1 => lpr s c
  | h + 2 => (nd s (anc c (h + 1))).livePar

def isN (v : Nat) : Prop := v ≠ NIL ∧ v < s.nodes.size ∧ (nd s v).alive = true
def liveN (v : Nat) : Prop := isN s v ∧ (nd s v).draining = false
def ghostN (v : Nat) : Prop := isN s v ∧ (nd s v).draining = true

instance (v : Nat) : Decidable (isN s v) := by unfold isN; infer_instance
instance (v : Nat) : Decidable (liveN s v) := by unfold liveN; infer_instance
instance (v : Nat) : Decidable (ghostN s v) := by unfold ghostN; infer_instance

def order (X : Nat) : List Nat := (nd s X).order
def labs (X : Nat) : List Nat := (nd s X).table.map (·.2)
def lab (X e : Nat) : Option Nat := (nd s X).lab? e

/-- The live parent of entry `e` of height `h`; for a ghost, that of its targets. -/
def par (h e : Nat) : Nat :=
  if h = 0 then lpr s e
  else if (nd s e).draining then (nd s (nd s e).t1).livePar else (nd s e).livePar

/-- The ghost whose target `p` is (`NIL` if none). -/
def srcOf (p : Nat) : Nat := (nd s p).overflowOf

/-- The true weight of `u`: chunks of `cl` below `u` in the live tree. -/
def tw (cl : List Nat) (u : Nat) : Nat := (cl.filter fun c => anc s c (ht s u) = u).length

/-- The range of `u`: chunks of `cl` whose path passes through `u`. -/
def rng (cl : List Nat) (u : Nat) : List Nat := cl.filter fun c => pp s c (ht s u) = u

/-- Digit `j ≥ 1` of `c`'s tag: the label of `p_{j-1}(c)` in the table of `p_j(c)`. -/
def digit (c j : Nat) : Nat := ((nd s (pp s c j)).lab? (pp s c (j - 1))).getD 0

/-- The lowest `k` digits of `c`'s tag. -/
def tagUp (c : Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => tagUp c k + digit s c (k + 1) * 2 ^ (k * s.P.beta)

/-- The tag that `c`'s path spells. -/
def tagF (c : Nat) : Nat := tagUp s c s.P.H

end views

/-! ### Strict order in a list -/

/-- `a` is strictly before `b` in `l`. -/
def Before (l : List Nat) (a b : Nat) : Prop := [a, b].Sublist l

theorem Before.mono {l l' : List Nat} {a b : Nat} (h : Before l a b) (hl : l.Sublist l') :
    Before l' a b := List.Sublist.trans h hl

theorem Before.mem_left {l : List Nat} {a b : Nat} (h : Before l a b) : a ∈ l :=
  h.subset (by simp)

theorem Before.mem_right {l : List Nat} {a b : Nat} (h : Before l a b) : b ∈ l :=
  h.subset (by simp)

theorem Before.ne {l : List Nat} {a b : Nat} (h : Before l a b) (hl : l.Nodup) : a ≠ b := by
  intro e; subst e
  have := List.Nodup.sublist h hl
  simp at this

theorem before_cons {x : Nat} {t : List Nat} {a b : Nat} :
    Before (x :: t) a b ↔ Before t a b ∨ (a = x ∧ b ∈ t) := by
  unfold Before
  rw [List.sublist_cons_iff]
  constructor
  · rintro (h | ⟨r, hr, h⟩)
    · exact Or.inl h
    · simp only [List.cons.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact Or.inr ⟨rfl, List.singleton_sublist.mp h⟩
  · rintro (h | ⟨rfl, h⟩)
    · exact Or.inl h
    · exact Or.inr ⟨[b], rfl, List.singleton_sublist.mpr h⟩

theorem Before.trans {l : List Nat} {a b c : Nat} (h1 : Before l a b) (h2 : Before l b c)
    (hl : l.Nodup) : Before l a c := by
  induction l with
  | nil => exact absurd h1.mem_left (by simp)
  | cons x t ih =>
    have hx : x ∉ t := (List.nodup_cons.mp hl).1
    rw [before_cons] at h1 h2 ⊢
    rcases h1 with h1 | ⟨rfl, hb⟩
    · rcases h2 with h2 | ⟨rfl, hc⟩
      · exact Or.inl (ih h1 h2 (List.nodup_cons.mp hl).2)
      · exact absurd h1.mem_right hx
    · rcases h2 with h2 | ⟨rfl, hc⟩
      · exact Or.inr ⟨rfl, h2.mem_right⟩
      · exact absurd hb hx

/-- Two distinct members of a list are in one order or the other. -/
theorem before_total {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    Before l a b ∨ Before l b a := by
  induction l with
  | nil => simp at ha
  | cons x t ih =>
    unfold Before
    rcases List.mem_cons.mp ha with rfl | ha'
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact absurd rfl hab
      · left; exact List.cons_sublist_cons.mpr (List.singleton_sublist.mpr hb')
    · rcases List.mem_cons.mp hb with rfl | hb'
      · right; exact List.cons_sublist_cons.mpr (List.singleton_sublist.mpr ha')
      · rcases ih ha' hb' with h | h
        · left; exact h.cons x
        · right; exact h.cons x

/-- In a nodup list, the order of two members is asymmetric. -/
theorem Before.asymm {l : List Nat} {a b : Nat} (h : Before l a b) (hl : l.Nodup) :
    ¬ Before l b a := fun h' => (h.trans h' hl).ne hl rfl

/-- Order in a sublist of a nodup list is the order in the list. -/
theorem before_of_sublist {l o : List Nat} {a b : Nat} (hs : l.Sublist o) (ho : o.Nodup)
    (ha : a ∈ l) (hb : b ∈ l) (h : Before o a b) : Before l a b := by
  have hab : a ≠ b := h.ne ho
  rcases before_total ha hb hab with h' | h'
  · exact h'
  · exact absurd (h'.mono hs) (h.asymm ho)

theorem before_append_left {l1 l2 : List Nat} {a b : Nat} (h : Before l1 a b) :
    Before (l1 ++ l2) a b := h.mono (List.sublist_append_left _ _)

theorem before_append_right {l1 l2 : List Nat} {a b : Nat} (h : Before l2 a b) :
    Before (l1 ++ l2) a b := h.mono (List.sublist_append_right _ _)

theorem before_append_mem {l1 l2 : List Nat} {a b : Nat} (ha : a ∈ l1) (hb : b ∈ l2) :
    Before (l1 ++ l2) a b := by
  unfold Before
  have : [a, b] = [a] ++ [b] := rfl
  rw [this]
  exact List.Sublist.append (List.singleton_sublist.mpr ha) (List.singleton_sublist.mpr hb)

/-- `a` before `b` in `l1 ++ b :: l2`, for `a ∈ l1`. -/
theorem before_split {l1 l2 : List Nat} {a b : Nat} (ha : a ∈ l1) :
    Before (l1 ++ b :: l2) a b := before_append_mem ha (by simp)

/-- What is before `b` in a nodup list `l1 ++ b :: l2` is in `l1`. -/
theorem mem_of_before_split {l1 l2 : List Nat} {a b : Nat} (hl : (l1 ++ b :: l2).Nodup)
    (h : Before (l1 ++ b :: l2) a b) : a ∈ l1 := by
  have hab := h.ne hl
  have ha := h.mem_left
  rcases List.mem_append.mp ha with h1 | h2
  · exact h1
  · rcases List.mem_cons.mp h2 with rfl | h3
    · exact absurd rfl hab
    · have hba : Before (l1 ++ b :: l2) b a := by
        have : l1 ++ b :: l2 = (l1 ++ [b]) ++ l2 := by simp
        rw [this]; exact before_append_mem (by simp) h3
      exact absurd hba (h.asymm hl)

/-! ### Gaps between labels -/

/-- The labels `ls` (in table order), with sentinels `-1` and `2^β` (shifted by one: `0` and
`2^β + 1`), have all gaps at least `B`. -/
def GapsGe (β B : Nat) (ls : List Nat) : Prop :=
  (0 :: ls.map (· + 1) ++ [2 ^ β + 1]).IsChain fun a b => a + B ≤ b

/-! ### Tags -/

theorem tagUp_lt {s : TS} {c : Nat} (k : Nat)
    (hd : ∀ j, 1 ≤ j → j ≤ k → digit s c j < 2 ^ s.P.beta) :
    tagUp s c k < 2 ^ (k * s.P.beta) := by
  induction k with
  | zero => simp [tagUp]
  | succ k ih =>
    unfold tagUp
    have h1 := ih (fun j hj1 hj2 => hd j hj1 (by omega))
    have h2 := hd (k + 1) (by omega) le_rfl
    have hpow : 2 ^ ((k + 1) * s.P.beta) = 2 ^ s.P.beta * 2 ^ (k * s.P.beta) := by
      rw [← pow_add]; congr 1; ring
    rw [hpow]
    have : digit s c (k + 1) * 2 ^ (k * s.P.beta) + 2 ^ (k * s.P.beta) ≤
        2 ^ s.P.beta * 2 ^ (k * s.P.beta) := by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ h2
    omega

/-- Digit comparison: digits agree above level `j`, digit `j` is smaller, all digits fit. -/
theorem tagUp_lt_of_digit {s s' : TS} {c d : Nat} (hβ : s'.P.beta = s.P.beta) {j : Nat}
    (hj : 1 ≤ j) (hdc : ∀ i, 1 ≤ i → i ≤ j → digit s c i < 2 ^ s.P.beta)
    (hlt : digit s c j < digit s' d j) :
    ∀ k, j ≤ k → (∀ i, j < i → i ≤ k → digit s c i = digit s' d i) → tagUp s c k < tagUp s' d k
      := by
  intro k hk heq
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · have := ih (by omega) (fun i hi1 hi2 => heq i hi1 (by omega))
      unfold tagUp
      rw [heq (k + 1) h le_rfl, hβ]
      omega
    · have hjk : j = k + 1 := by omega
      subst hjk
      unfold tagUp
      have h1 := tagUp_lt (s := s) (c := c) k (fun i hi1 hi2 => hdc i hi1 (by omega))
      rw [hβ]
      have : (digit s c (k + 1) + 1) * 2 ^ (k * s.P.beta) ≤ digit s' d (k + 1) * 2 ^ (k *
        s.P.beta) :=
        Nat.mul_le_mul_right _ hlt
      rw [Nat.add_mul, one_mul] at this
      omega

/-- Two shifted digits, combined with `|||`, are added. -/
theorem lor_shift_eq_add {pv vb h β : Nat} (hvb : vb < 2 ^ β) (h1 : 1 ≤ h) :
    (pv <<< (h * β)) ||| (vb <<< ((h - 1) * β)) = pv * 2 ^ (h * β) + vb * 2 ^ ((h - 1) * β) := by
  have hlt : vb <<< ((h - 1) * β) < 2 ^ (h * β) := by
    rw [Nat.shiftLeft_eq]
    have : h * β = β + (h - 1) * β := by
      obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
      simp; ring
    rw [this, pow_add]
    exact Nat.mul_lt_mul_of_pos_right hvb (by positivity)
  rw [← Nat.shiftLeft_add_eq_or_of_lt hlt, Nat.shiftLeft_eq, Nat.shiftLeft_eq]

theorem tagUp_congr {s s' : TS} {c c' : Nat} (hβ : s'.P.beta = s.P.beta) :
    ∀ k, (∀ i, 1 ≤ i → i ≤ k → digit s' c' i = digit s c i) → tagUp s' c' k = tagUp s c k
  | 0, _ => rfl
  | k + 1, h => by
    unfold tagUp
    rw [tagUp_congr hβ k (fun i h1 h2 => h i h1 (by omega)), h (k + 1) (by omega) le_rfl, hβ]

theorem tagUp_succ (s : TS) (c k : Nat) :
    tagUp s c (k + 1) = tagUp s c k + digit s c (k + 1) * 2 ^ (k * s.P.beta) := rfl

theorem tagUp_mono (s : TS) (c m : Nat) : ∀ k, m ≤ k → tagUp s c m ≤ tagUp s c k
  | 0, hk => by rw [show m = 0 by omega]
  | k + 1, hk => by
    rcases Nat.eq_or_lt_of_le hk with e | hlt
    · rw [e]
    · have := tagUp_mono s c m k (by omega)
      rw [tagUp_succ]; omega

theorem tagUp_high {s s' : TS} {c c' : Nat} (hβ : s'.P.beta = s.P.beta) (m : Nat) :
    ∀ k, m ≤ k → (∀ i, m < i → i ≤ k → digit s' c' i = digit s c i) →
      tagUp s' c' k + tagUp s c m = tagUp s c k + tagUp s' c' m
  | 0, hk, _ => by rw [show m = 0 by omega]; omega
  | k + 1, hk, h => by
    rcases Nat.eq_or_lt_of_le hk with e | hlt
    · rw [e]; omega
    · have := tagUp_high hβ m k (by omega) (fun i h1 h2 => h i h1 (by omega))
      rw [tagUp_succ, tagUp_succ, h (k + 1) (by omega) le_rfl, hβ]
      omega

/-- Two consecutive digits `h`, `h+1` replaced: the arithmetic of `drainStep`'s tag update. -/
theorem tagUp_replace2 {s s' : TS} {c c' : Nat} (hβ : s'.P.beta = s.P.beta) {h k : Nat}
    (h1 : 1 ≤ h) (hk : h + 1 ≤ k)
    (heq : ∀ i, 1 ≤ i → i ≤ k → i ≠ h → i ≠ h + 1 → digit s' c' i = digit s c i) :
    digit s c (h + 1) * 2 ^ (h * s.P.beta) + digit s c h * 2 ^ ((h - 1) * s.P.beta) ≤ tagUp s c k ∧
    tagUp s' c' k = tagUp s c k -
        (digit s c (h + 1) * 2 ^ (h * s.P.beta) + digit s c h * 2 ^ ((h - 1) * s.P.beta)) +
      (digit s' c' (h + 1) * 2 ^ (h * s.P.beta) + digit s' c' h * 2 ^ ((h - 1) * s.P.beta)) := by
  obtain ⟨g, rfl⟩ : ∃ g, h = g + 1 := ⟨h - 1, by omega⟩
  have hlow := tagUp_congr (c := c) (c' := c') hβ g (fun i h1 h2 => heq i h1 (by omega) (by
    omega) (by omega))
  have hhi := tagUp_high (c := c) (c' := c') hβ (g + 2) k (by omega)
    (fun i h1 h2 => heq i (by omega) h2 (by omega) (by omega))
  have e1 : tagUp s c (g + 2) = tagUp s c g + digit s c (g + 1) * 2 ^ (g * s.P.beta) +
      digit s c (g + 2) * 2 ^ ((g + 1) * s.P.beta) := rfl
  have e2 : tagUp s' c' (g + 2) = tagUp s' c' g + digit s' c' (g + 1) * 2 ^ (g * s'.P.beta) +
      digit s' c' (g + 2) * 2 ^ ((g + 1) * s'.P.beta) := rfl
  rw [hβ] at e2
  simp only [Nat.add_sub_cancel] at *
  have hk2 : tagUp s c (g + 2) ≤ tagUp s c k := tagUp_mono s c _ k (by omega)
  simp only [show g + 1 + 1 = g + 2 from rfl] at *
  constructor
  · omega
  · omega

end OrderMaintenance.Proof.Top
