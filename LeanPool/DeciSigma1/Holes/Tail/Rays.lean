/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

import Mathlib.Algebra.Order.BigOperators.Group.Finset

public import LeanPool.DeciSigma1.Arithmetic.DifferenceConstraints
public import LeanPool.DeciSigma1.Words.Basic
public import LeanPool.DeciSigma1.Words.SuffixChains
import Mathlib.Order.SuccPred.Nat
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Tactic.Ring.RingNF

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Closed factors and rays

Tools for replacing a rejected tail by a periodic continuation. A factor `x[c, c')` is repeated
by `pumpFactor x c c' L`: `x[0, c)` followed by the first `L` letters of `x[c, c')^ω`. The
repetition must create no new comparison with the target words, which is guaranteed when the two
cuts `c` and `c'` have the same finite summary.

The summary is the *suffix node*. The *suffix dictionary* of the targets at window `B`
(`suffixDictionary`) consists of the empty word and the nonempty factors of the suffixes of
length `B` of the targets; for `m` targets it has at most `m B (B + 1) / 2 + 1` words. The suffix
node of a word (`suffixNode`) is its longest suffix in the dictionary, together with the state of
the run before that suffix. Suffix nodes form a deterministic automaton (`suffixNode_snoc`), and
for `N` states there are at most `suffixNodeBound m N B` of them, whatever the alphabet. Two cuts
`c < c'` with the same suffix node bound a *closed* factor (`NodeClosedAt`); among the cuts
`u, u + s, u + 2 s, …` a closed factor of length at least `s` occurs early
(`exists_nodeClosedAt_of_spaced_cuts`). Along the pumped word, letters, states and suffix nodes
repeat with period `c' - c` from `c` on. If no occurrence of the suffix of length `B` of a target
ends in `(c, c']`, every comparison of the pumped word with the target is a comparison of `x`
with the target (`comparison_of_pumpFactor`). Pumping a closed factor after the first rejected
cut keeps the coordinate eligible with the same first rejected cut and makes its endpoint
immortal (`pumpFactor_eligible`).

Long periodic suffixes give closed factors directly, through the *window state* of a cut at
window `B`: the state of the run `B` letters before the cut together with those `B` letters
(`windowState`). Equal window states (`ClosedAt`) make the letters of the pumped word periodic
from `c - B` on, and give equal suffix nodes for every dictionary of words of length at most `B`
(`ClosedAt.nodeClosedAt`).

The second part treats rays as continuations. The state along a ray (`rayState`) repeats after
a computable horizon (`ray_state_reduce`), and `repeatFactorRay` is the ray of a factor.
To choose the lengths of several ray prefixes at once, the admitted comparisons between
distinct rays give constraints `L j ≥ L i + (b - a + 1)` (`raySystem`); a solution makes the
prefixes free of admitted comparisons (`ray_prefix_hole`).

## Main declarations

- `suffixDictionary`, `suffixNode`, `suffixNode_snoc`: suffix dictionaries and the suffix-node
  automaton.
- `NodeClosedAt`, `factorLengthBound`, `exists_nodeClosedAt_of_spaced_cuts`: closed factors.
- `windowState`, `ClosedAt`, `ClosedAt.nodeClosedAt`: factors closed at a window.
- `NoSuffixOccurrenceEndsBetween`: no occurrence of a suffix of a target ends inside a factor.
- `pumpFactor`, `comparison_of_pumpFactor`, `pumpFactor_eligible`: pumping a closed factor.
- `rayState`, `ray_state_reduce`, `repeatFactorRay`: runs along rays.
- `raySystem`, `ray_prefix_hole`: the difference system of ray lengths.
-/

@[expose] public section


namespace DeciSigma1.Holes.Tail

open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table

variable {α S : Type} {k : ℕ}

/-! ## Prefixes of suffixes and suffixes of prefixes -/

theorem prefix_drop_iff {u x : List α} {a : ℕ} (ha : a ≤ x.length) :
    u <+: x.drop a ↔ a + u.length ≤ x.length ∧ ∀ j < u.length, x[a + j]? = u[j]? := by
  rw [List.prefix_iff_eq_take]
  constructor
  · intro h
    have hl : u.length ≤ (x.drop a).length := by
      rw [h]; simp only [List.length_take]; exact min_le_right _ _
    refine ⟨by simp at hl; omega, fun j hj => ?_⟩
    rw [congrArg (fun l => l[j]?) h, List.getElem?_take_of_lt hj, List.getElem?_drop]
  · rintro ⟨hl, h⟩
    apply List.ext_getElem?
    intro j
    by_cases hj : j < u.length
    · rw [List.getElem?_take_of_lt hj, List.getElem?_drop, h j hj]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

theorem suffix_take_iff {u x : List α} {e : ℕ} (he : e ≤ x.length) :
    u <:+ x.take e ↔ u.length ≤ e ∧ ∀ j < u.length, x[e - u.length + j]? = u[j]? := by
  rw [List.suffix_iff_eq_drop]
  simp only [List.length_take, min_eq_left he]
  constructor
  · intro h
    have hl : u.length ≤ e := by
      have := congrArg List.length h
      simp only [List.length_drop, List.length_take, min_eq_left he] at this
      omega
    refine ⟨hl, fun j hj => ?_⟩
    rw [congrArg (fun l => l[j]?) h, List.getElem?_drop, List.getElem?_take_of_lt (by omega)]
  · rintro ⟨hl, h⟩
    apply List.ext_getElem?
    intro j
    by_cases hj : j < u.length
    · rw [List.getElem?_drop, List.getElem?_take_of_lt (by omega), h j hj]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

theorem getElem?_suffixOfLength (t : List α) (B j : ℕ) :
    (Words.suffixOfLength t B)[j]? = t[t.length - B + j]? := by
  simp [Words.suffixOfLength, List.getElem?_drop]

/-- Comparing suffixes after appending one letter to each word. -/
theorem snoc_suffix_snoc_iff {u w : List α} {a b : α} :
    u ++ [b] <:+ w ++ [a] ↔ u <:+ w ∧ b = a := by
  constructor
  · rintro ⟨r, hr⟩
    rw [← List.append_assoc] at hr
    obtain ⟨h1, h2⟩ := List.append_inj' hr rfl
    exact ⟨⟨r, h1⟩, by simpa using h2⟩
  · rintro ⟨⟨r, rfl⟩, rfl⟩
    exact ⟨r, by simp⟩

/-- A word is its prefix before a suffix, followed by that suffix. -/
theorem take_append_suffix {s w : List α} (h : s <:+ w) :
    w.take (w.length - s.length) ++ s = w := by
  conv_rhs => rw [← List.take_append_drop (w.length - s.length) w]
  rw [← List.suffix_iff_eq_drop.mp h]

/-! ## Window states and pumped factors -/

/-- The window state of cut `c` at window `b`: the state before the last `b` letters before `c`,
and those letters (the whole prefix if `c < b`). -/
def windowState (T : Table α S k) (q0 : S) (x : List α) (b c : ℕ) : S × List α :=
  (runFrom T.step q0 (x.take (c - b)), (x.take c).drop (c - b))

/-- The factor `x[c, c')` is closed at window `B`: the cuts `B ≤ c < c'` have the same window
state. -/
def ClosedAt (T : Table α S k) (q0 : S) (x : List α) (B c c' : ℕ) : Prop :=
  B ≤ c ∧ c < c' ∧ c' ≤ x.length ∧ windowState T q0 x B c = windowState T q0 x B c'

/-- No occurrence in `x` of the suffix of length `B` of `t` ends in `(c, c']`. -/
def NoSuffixOccurrenceEndsBetween [DecidableEq α] (x t : List α) (B c c' : ℕ) : Prop :=
  ∀ e ∈ Words.occurrences x t B, e ≤ c ∨ c' < e

/-- The factor `τ = x[c, c')` pumped: `x[0, c)` followed by the first `L` letters of `τ^ω`. -/
def pumpFactor (x : List α) (c c' L : ℕ) : List α :=
  x.take c ++ (pow ((x.drop c).take (c' - c)) (L + 1)).take L

theorem NoSuffixOccurrenceEndsBetween.mono [DecidableEq α] {x t : List α} {b B c c' : ℕ}
    (h : NoSuffixOccurrenceEndsBetween x t b c c')
    (hb : b ≤ B) : NoSuffixOccurrenceEndsBetween x t B c c' :=
  fun e he => h e (Words.occurrences_antitone hb he)

/-! ## Suffix dictionaries -/

section Dictionary

variable [DecidableEq α]

/-- The nonempty factors of `w`. -/
def nonemptyFactors (w : List α) : Finset (List α) :=
  (Finset.range w.length).biUnion fun i =>
    (Finset.range (w.length - i)).image fun j => (w.drop i).take (j + 1)

theorem mem_nonemptyFactors {u w : List α} : u ∈ nonemptyFactors w ↔ u ≠ [] ∧ u <:+: w := by
  simp only [nonemptyFactors, Finset.mem_biUnion, Finset.mem_range, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, j, hj, rfl⟩
    refine ⟨?_, (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix⟩
    rw [← List.length_pos_iff, List.length_take, List.length_drop]
    omega
  · rintro ⟨hne, s, t, rfl⟩
    have hu := List.length_pos_iff.mpr hne
    refine ⟨s.length, by simp; omega, u.length - 1, by simp; omega, ?_⟩
    rw [show u.length - 1 + 1 = u.length by omega, List.append_assoc, List.drop_left,
      List.take_left]

/-- A word of length `n` has at most `n (n + 1) / 2` nonempty factors. -/
theorem card_nonemptyFactors_le (w : List α) :
    (nonemptyFactors w).card ≤ w.length * (w.length + 1) / 2 := by
  have hsum : ∀ n : ℕ, (∑ i ∈ Finset.range n, (n - i)) * 2 = n * (n + 1) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ', Nat.add_mul]
      have : ∑ i ∈ Finset.range n, (n + 1 - (i + 1)) = ∑ i ∈ Finset.range n, (n - i) :=
        Finset.sum_congr rfl fun i _ => by omega
      rw [this, ih, Nat.sub_zero]
      ring
  calc (nonemptyFactors w).card
      ≤ ∑ i ∈ Finset.range w.length, ((Finset.range (w.length - i)).image
          fun j => (w.drop i).take (j + 1)).card := Finset.card_biUnion_le
    _ ≤ ∑ i ∈ Finset.range w.length, (w.length - i) :=
        Finset.sum_le_sum fun i _ => Finset.card_image_le.trans (by simp)
    _ = w.length * (w.length + 1) / 2 := by have := hsum w.length; omega

/-- The suffix dictionary of the targets `ts` at window `B`: the empty word and the nonempty
factors of the suffixes of length `B` of the targets (of the whole target if it is shorter). -/
def suffixDictionary (ts : List (List α)) (B : ℕ) : Finset (List α) :=
  insert [] (ts.toFinset.biUnion fun t => nonemptyFactors (Words.suffixOfLength t B))

variable {ts : List (List α)} {B : ℕ}

theorem mem_suffixDictionary {u : List α} :
    u ∈ suffixDictionary ts B ↔ u = [] ∨ ∃ t ∈ ts, u <:+: Words.suffixOfLength t B := by
  simp only [suffixDictionary, Finset.mem_insert, Finset.mem_biUnion, List.mem_toFinset,
    mem_nonemptyFactors]
  constructor
  · rintro (h | ⟨t, ht, -, h⟩)
    exacts [.inl h, .inr ⟨t, ht, h⟩]
  · rintro (h | ⟨t, ht, h⟩)
    · exact .inl h
    · by_cases hu : u = []
      exacts [.inl hu, .inr ⟨t, ht, hu, h⟩]

theorem nil_mem_suffixDictionary : ([] : List α) ∈ suffixDictionary ts B :=
  Finset.mem_insert_self _ _

theorem length_le_of_mem_suffixDictionary {u : List α} (h : u ∈ suffixDictionary ts B) :
    u.length ≤ B := by
  rcases mem_suffixDictionary.mp h with rfl | ⟨t, -, h⟩
  · simp
  · have := h.length_le
    simp only [Words.length_suffixOfLength] at this
    omega

/-- The suffix dictionary is closed under factors. -/
theorem mem_suffixDictionary_of_infix {u v : List α} (hv : v ∈ suffixDictionary ts B)
    (hu : u <:+: v) : u ∈ suffixDictionary ts B := by
  rcases mem_suffixDictionary.mp hv with rfl | ⟨t, ht, h⟩
  · exact mem_suffixDictionary.mpr (.inl (List.infix_nil.mp hu))
  · exact mem_suffixDictionary.mpr (.inr ⟨t, ht, hu.trans h⟩)

/-- The suffixes of length at most `B` of a target lie in the suffix dictionary. -/
theorem mem_suffixDictionary_of_suffix {t p : List α} (ht : t ∈ ts) (hp : p <:+ t)
    (hpB : p.length ≤ B) : p ∈ suffixDictionary ts B := by
  have hpt := hp.length_le
  refine mem_suffixDictionary.mpr (.inr ⟨t, ht, (List.suffix_of_suffix_length_le hp
    (List.drop_suffix _ _) ?_).isInfix⟩)
  simp only [List.length_drop]
  omega

/-- The suffix dictionary of `m` targets at window `B` has at most `m B (B + 1) / 2 + 1`
words. -/
theorem card_suffixDictionary_le (ts : List (List α)) (B : ℕ) :
    (suffixDictionary ts B).card ≤ ts.length * (B * (B + 1) / 2) + 1 := by
  refine (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ?_ 1)
  have hB : ∀ t : List α, (Words.suffixOfLength t B).length ≤ B := fun t => by simp
  calc _ ≤ ∑ t ∈ ts.toFinset, (nonemptyFactors (Words.suffixOfLength t B)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _t ∈ ts.toFinset, B * (B + 1) / 2 := Finset.sum_le_sum fun t _ =>
        (card_nonemptyFactors_le _).trans (Nat.div_le_div_right
          (Nat.mul_le_mul (hB t) (Nat.add_le_add_right (hB t) 1)))
    _ = ts.toFinset.card * (B * (B + 1) / 2) := by simp
    _ ≤ ts.length * (B * (B + 1) / 2) := Nat.mul_le_mul_right _ (List.toFinset_card_le ts)

end Dictionary

/-! ## Suffix nodes -/

section Nodes

variable [DecidableEq α] {D : Finset (List α)}

/-- The longest suffix of `w` that lies in the dictionary `D`, or the empty word if there is
none. -/
def dictSuffix (D : Finset (List α)) : List α → List α
  | [] => []
  | a :: w => if a :: w ∈ D then a :: w else dictSuffix D w

theorem dictSuffix_suffix (D : Finset (List α)) : ∀ w : List α, dictSuffix D w <:+ w
  | [] => List.suffix_refl _
  | a :: w => by
    rw [dictSuffix]
    split_ifs
    · exact List.suffix_refl _
    · exact (dictSuffix_suffix D w).trans (List.suffix_cons _ _)

theorem dictSuffix_mem (hD : [] ∈ D) : ∀ w : List α, dictSuffix D w ∈ D
  | [] => hD
  | a :: w => by
    rw [dictSuffix]
    split_ifs with h
    exacts [h, dictSuffix_mem hD w]

theorem length_le_length_dictSuffix : ∀ {w s : List α}, s <:+ w → s ∈ D →
    s.length ≤ (dictSuffix D w).length
  | [], s, hs, _ => by rw [List.suffix_nil.mp hs]; simp
  | a :: w, s, hs, hsD => by
    rw [dictSuffix]
    split_ifs with h
    · exact hs.length_le
    · rcases List.suffix_cons_iff.mp hs with rfl | hs
      · exact absurd hsD h
      · exact length_le_length_dictSuffix hs hsD

/-- Every suffix of `w` in `D` is a suffix of `dictSuffix D w`. -/
theorem suffix_dictSuffix {w s : List α} (hs : s <:+ w) (hsD : s ∈ D) : s <:+ dictSuffix D w :=
  List.suffix_of_suffix_length_le hs (dictSuffix_suffix D w) (length_le_length_dictSuffix hs hsD)

/-- A longest suffix of `w` in `D` is `dictSuffix D w`. -/
theorem dictSuffix_eq (hD : [] ∈ D) {w s : List α} (hs : s <:+ w) (hsD : s ∈ D)
    (hmax : ∀ r, r <:+ w → r ∈ D → r.length ≤ s.length) : dictSuffix D w = s := by
  have h1 := hmax _ (dictSuffix_suffix D w) (dictSuffix_mem hD w)
  have h2 := length_le_length_dictSuffix (D := D) hs hsD
  exact ((suffix_dictSuffix hs hsD).eq_of_length (by omega)).symm

/-- If `D` contains the empty word and is closed under prefixes, the longest suffix in `D` after
one more letter `a` is the longest suffix in `D` of `dictSuffix D w ++ [a]`. -/
theorem dictSuffix_snoc (hD : [] ∈ D) (hpre : ∀ u a, u ++ [a] ∈ D → u ∈ D) (w : List α)
    (a : α) : dictSuffix D (w ++ [a]) = dictSuffix D (dictSuffix D w ++ [a]) := by
  apply dictSuffix_eq hD ((dictSuffix_suffix D _).trans
    (snoc_suffix_snoc_iff.mpr ⟨dictSuffix_suffix D w, rfl⟩)) (dictSuffix_mem hD _)
  intro r hr hrD
  rcases List.eq_nil_or_concat r with rfl | ⟨r0, b, rfl⟩
  · simp
  · rw [List.concat_eq_append] at hr hrD ⊢
    obtain ⟨hr0, rfl⟩ := snoc_suffix_snoc_iff.mp hr
    exact length_le_length_dictSuffix
      (snoc_suffix_snoc_iff.mpr ⟨suffix_dictSuffix hr0 (hpre r0 _ hrD), rfl⟩) hrD

/-- The suffix node of `w` for the dictionary `D`: the longest suffix of `w` in `D`, and the state
of the run of `T` from `q0` before that suffix. -/
def suffixNode (T : Table α S k) (q0 : S) (D : Finset (List α)) (w : List α) : List α × S :=
  (dictSuffix D w, runFrom T.step q0 (w.take (w.length - (dictSuffix D w).length)))

/-- One step of the suffix-node automaton: the node after the letter `a`, from the node `n`. -/
def suffixNodeStep (T : Table α S k) (D : Finset (List α)) (n : List α × S) (a : α) :
    List α × S :=
  (dictSuffix D (n.1 ++ [a]),
    runFrom T.step n.2 ((n.1 ++ [a]).take (n.1.length + 1 - (dictSuffix D (n.1 ++ [a])).length)))

/-- The suffix nodes form a deterministic automaton: the node after one more letter is computed
from the node before, if `D` contains the empty word and is closed under prefixes. -/
theorem suffixNode_snoc (T : Table α S k) (q0 : S) (hD : [] ∈ D)
    (hpre : ∀ u a, u ++ [a] ∈ D → u ∈ D) (w : List α) (a : α) :
    suffixNode T q0 D (w ++ [a]) = suffixNodeStep T D (suffixNode T q0 D w) a := by
  have hsnoc := dictSuffix_snoc hD hpre w a
  simp only [suffixNode, suffixNodeStep, ← hsnoc]
  refine Prod.ext rfl ?_
  simp only
  have hs := dictSuffix_suffix D w
  have hsw := hs.length_le
  have h2 : (dictSuffix D (w ++ [a])).length ≤ (dictSuffix D w).length + 1 := by
    rw [hsnoc]; simpa using (dictSuffix_suffix D (dictSuffix D w ++ [a])).length_le
  generalize dictSuffix D (w ++ [a]) = s' at h2 ⊢
  generalize dictSuffix D w = s at hs hsw h2 ⊢
  have e : w ++ [a] = w.take (w.length - s.length) ++ (s ++ [a]) := by
    rw [← List.append_assoc, take_append_suffix hs]
  rw [← runFrom_append, e, List.take_append, List.take_of_length_le (by simp; omega)]
  congr 3
  simp
  omega

/-- The state after `w` is read from its suffix node. -/
theorem runFrom_eq_suffixNode (T : Table α S k) (q0 : S) (D : Finset (List α)) (w : List α) :
    runFrom T.step q0 w = runFrom T.step (suffixNode T q0 D w).2 (suffixNode T q0 D w).1 := by
  simp only [suffixNode]
  rw [← runFrom_append, take_append_suffix (dictSuffix_suffix D w)]

/-- A suffix `p ∈ D` of `w` is a suffix of the word of the suffix node of `w`, and the state before
it is read from the node. -/
theorem suffixNode_suffix (T : Table α S k) (q0 : S) {w p : List α} (hp : p <:+ w)
    (hpD : p ∈ D) :
    p <:+ (suffixNode T q0 D w).1 ∧
      runFrom T.step q0 (w.take (w.length - p.length)) =
        runFrom T.step (suffixNode T q0 D w).2
          ((suffixNode T q0 D w).1.take ((suffixNode T q0 D w).1.length - p.length)) := by
  have hps := suffix_dictSuffix hp hpD
  refine ⟨hps, ?_⟩
  simp only [suffixNode]
  have hpl := hps.length_le
  have hs := dictSuffix_suffix D w
  have hsw := hs.length_le
  generalize dictSuffix D w = s at hs hsw hpl ⊢
  have e : w = w.take (w.length - s.length) ++ s := (take_append_suffix hs).symm
  rw [← runFrom_append]
  conv_lhs => rw [e]
  rw [List.take_append, List.take_of_length_le (by simp; omega)]
  congr 3
  simp
  omega

/-- Two words with the same suffix node have the same suffixes in `D`, with the same states before
them. -/
theorem suffix_of_suffixNode_eq (T : Table α S k) (q0 : S) {w w' p : List α}
    (he : suffixNode T q0 D w = suffixNode T q0 D w') (hp : p <:+ w) (hpD : p ∈ D) :
    p <:+ w' ∧ runFrom T.step q0 (w'.take (w'.length - p.length)) =
      runFrom T.step q0 (w.take (w.length - p.length)) := by
  obtain ⟨h1, h2⟩ := suffixNode_suffix T q0 hp hpD
  rw [he] at h1 h2
  have hp' : p <:+ w' := h1.trans (dictSuffix_suffix D w')
  exact ⟨hp', (suffixNode_suffix T q0 hp' hpD).2.trans h2.symm⟩

/-- The factor `x[c, c')` is closed for the dictionary `D`: the cuts `c < c'` have the same suffix
node. -/
def NodeClosedAt (T : Table α S k) (q0 : S) (D : Finset (List α)) (x : List α) (c c' : ℕ) :
    Prop :=
  c < c' ∧ c' ≤ x.length ∧ suffixNode T q0 D (x.take c) = suffixNode T q0 D (x.take c')

variable {T : Table α S k} {q0 : S} {x : List α} {B c c' : ℕ}

/-- The cuts of a closed factor have the same state. -/
theorem NodeClosedAt.state (hcl : NodeClosedAt T q0 D x c c') :
    runFrom T.step q0 (x.take c) = runFrom T.step q0 (x.take c') := by
  rw [runFrom_eq_suffixNode T q0 D (x.take c), runFrom_eq_suffixNode T q0 D (x.take c'),
    hcl.2.2]

/-- For a dictionary of words of length at most `|v|`, the suffix node of `u ++ v` depends only on
the state after `u` and on `v`. -/
theorem suffixNode_append (T : Table α S k) (q0 : S) (hD : [] ∈ D) {u v : List α}
    (hB : ∀ r ∈ D, r.length ≤ v.length) :
    suffixNode T q0 D (u ++ v) = (dictSuffix D v, runFrom T.step (runFrom T.step q0 u)
      (v.take (v.length - (dictSuffix D v).length))) := by
  have hdv : dictSuffix D (u ++ v) = dictSuffix D v := by
    apply dictSuffix_eq hD ((dictSuffix_suffix D v).trans (List.suffix_append _ _))
      (dictSuffix_mem hD v)
    intro r hr hrD
    exact length_le_length_dictSuffix
      (List.suffix_of_suffix_length_le hr (List.suffix_append _ _) (hB r hrD)) hrD
  simp only [suffixNode, hdv]
  have := (dictSuffix_suffix D v).length_le
  rw [← runFrom_append, List.take_append, List.take_of_length_le (by simp; omega)]
  congr 3
  simp
  omega

/-- A factor closed at window `B` is closed for every dictionary of words of length at most `B`
that contains the empty word. -/
theorem ClosedAt.nodeClosedAt (hcl : ClosedAt T q0 x B c c') (hD : [] ∈ D)
    (hB : ∀ r ∈ D, r.length ≤ B) : NodeClosedAt T q0 D x c c' := by
  obtain ⟨hBc, hcc, hc', hw⟩ := hcl
  refine ⟨hcc, hc', ?_⟩
  have hsplit : ∀ e, x.take e = x.take (e - B) ++ (x.take e).drop (e - B) := fun e => by
    conv_lhs => rw [← List.take_append_drop (e - B) (x.take e)]
    rw [List.take_take, min_eq_left (Nat.sub_le _ _)]
  have hlen : ∀ e, B ≤ e → e ≤ x.length → ((x.take e).drop (e - B)).length = B := fun e h1 h2 => by
    simp; omega
  rw [hsplit c, hsplit c', suffixNode_append T q0 hD (by rw [hlen c hBc (by omega)]; exact hB),
    suffixNode_append T q0 hD (by rw [hlen c' (by omega) hc']; exact hB)]
  simp only [windowState, Prod.mk.injEq] at hw
  rw [hw.1, hw.2]

/-- A bound `N (m B (B + 1) / 2 + 1)` on the number of suffix nodes for the dictionary of `m`
targets at window `B`, with `N` states. -/
def suffixNodeBound (m N B : ℕ) : ℕ := N * (m * (B * (B + 1) / 2) + 1)

/-- A bound `(B + 1) · suffixNodeBound m N B` on the length of a closed factor found among cuts
spaced `B + 1` apart. -/
def factorLengthBound (m N B : ℕ) : ℕ := (B + 1) * suffixNodeBound m N B

theorem factorLengthBound_mono (m N : ℕ) : Monotone (factorLengthBound m N) := by
  intro B B' h
  have h1 : B * (B + 1) / 2 ≤ B' * (B' + 1) / 2 :=
    Nat.div_le_div_right (Nat.mul_le_mul h (by omega))
  exact Nat.mul_le_mul (by omega)
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left _ h1) 1))

/-- Among the cuts `u, u + s, …, u + V s` of `x`, where `V = |D| · N` and `[] ∈ D`, two have the
same suffix node; they bound a closed factor of length at least `s`. -/
theorem exists_nodeClosedAt_of_spaced_cuts [Fintype S] (T : Table α S k) (q0 : S) (hD : [] ∈ D)
    (x : List α) {s u : ℕ} (hs : 0 < s) (hu : u + s * (D.card * Fintype.card S) ≤ x.length) :
    ∃ c c', u ≤ c ∧ c' ≤ u + s * (D.card * Fintype.card S) ∧ s ≤ c' - c ∧
      NodeClosedAt T q0 D x c c' := by
  set V := D.card * Fintype.card S
  have hmaps : ∀ j ∈ Finset.range (V + 1),
      suffixNode T q0 D (x.take (u + j * s)) ∈ D ×ˢ (Finset.univ : Finset S) := fun j _ =>
    Finset.mem_product.mpr ⟨dictSuffix_mem hD _, Finset.mem_univ _⟩
  have hcard : (D ×ˢ (Finset.univ : Finset S)).card < (Finset.range (V + 1)).card := by
    rw [Finset.card_product, Finset.card_univ, Finset.card_range]; omega
  obtain ⟨j₁, hj₁, j₂, hj₂, hne, he⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard hmaps
  rw [Finset.mem_range] at hj₁ hj₂
  have key : ∀ i j, i < j → j < V + 1 →
      suffixNode T q0 D (x.take (u + i * s)) = suffixNode T q0 D (x.take (u + j * s)) →
      ∃ c c', u ≤ c ∧ c' ≤ u + s * V ∧ s ≤ c' - c ∧ NodeClosedAt T q0 D x c c' := by
    intro i j hij hj heq
    have h1 : (i + 1) * s ≤ j * s := Nat.mul_le_mul_right s hij
    have h2 : j * s ≤ V * s := Nat.mul_le_mul_right s (by omega)
    rw [Nat.add_mul, Nat.one_mul] at h1
    rw [Nat.mul_comm s V] at hu ⊢
    exact ⟨u + i * s, u + j * s, by omega, by omega, by omega, by omega, by omega, heq⟩
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · exact key j₁ j₂ h hj₂ he
  · exact key j₂ j₁ h hj₁ he.symm

end Nodes

/-! ## Structure of a pumped factor -/

section PumpFactor

variable {x : List α} {c c' L : ℕ}

theorem length_loop (hc' : c' ≤ x.length) :
    ((x.drop c).take (c' - c)).length = c' - c := by simp; omega

theorem loop_ne_nil (hcc : c < c') (hc' : c' ≤ x.length) : (x.drop c).take (c' - c) ≠ [] := by
  intro h; have := congrArg List.length h; rw [length_loop hc'] at this; simp at this; omega

theorem length_pow_loop (hc' : c' ≤ x.length) (n : ℕ) :
    (pow ((x.drop c).take (c' - c)) n).length = n * (c' - c) := by
  rw [Words.length_pow, length_loop hc']

theorem le_length_pow_loop (hcc : c < c') (hc' : c' ≤ x.length) (L : ℕ) :
    L + 1 ≤ (pow ((x.drop c).take (c' - c)) (L + 1)).length := by
  rw [length_pow_loop hc']; exact Nat.le_mul_of_pos_right _ (by omega)

theorem length_pumpFactor (hcc : c < c') (hc' : c' ≤ x.length) :
    (pumpFactor x c c' L).length = c + L := by
  have := le_length_pow_loop hcc hc' L
  simp only [pumpFactor, List.length_append, List.length_take]
  omega

/-- The letters of the periodic part of a pumped factor. -/
theorem getElem?_pumpFactor_ge (hcc : c < c') (hc' : c' ≤ x.length) {p : ℕ} (hc : c ≤ p)
    (hp : p < c + L) : (pumpFactor x c c' L)[p]? = x[c + (p - c) % (c' - c)]? := by
  have hlen := le_length_pow_loop hcc hc' L
  unfold pumpFactor
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, min_eq_left (by omega : c ≤ x.length)]
  rw [List.getElem?_take_of_lt (by omega), Words.getElem?_pow
    (loop_ne_nil hcc hc') (by omega), length_loop hc',
    List.getElem?_take_of_lt (Nat.mod_lt _ (by omega)), List.getElem?_drop]

theorem getElem?_pumpFactor_of_lt (hcc : c < c') (hc' : c' ≤ x.length) (hL : c' - c ≤ L) {p : ℕ}
    (hp : p < c') : (pumpFactor x c c' L)[p]? = x[p]? := by
  by_cases hpc : p < c
  · unfold pumpFactor
    rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hpc]
  · rw [getElem?_pumpFactor_ge hcc hc' (by omega) (by omega), Nat.mod_eq_of_lt (by omega)]
    congr 1; omega

theorem getElem?_stay_period (hcc : c < c') (hc' : c' ≤ x.length) {p : ℕ} (hc : c ≤ p)
    (hp : p + (c' - c) < c + L) :
    (pumpFactor x c c' L)[p + (c' - c)]? = (pumpFactor x c c' L)[p]? := by
  rw [getElem?_pumpFactor_ge hcc hc' (by omega) hp, getElem?_pumpFactor_ge hcc hc' hc (by omega)]
  congr 2
  rw [show p + (c' - c) - c = p - c + (c' - c) by omega, Nat.add_mod_right]

theorem pumpFactor_take (hcc : c < c') (hc' : c' ≤ x.length) (hL : c' - c ≤ L) {p : ℕ}
    (hp : p ≤ c') :
    (pumpFactor x c c' L).take p = x.take p := by
  apply List.ext_getElem?
  intro j
  by_cases hj : j < p
  · rw [List.getElem?_take_of_lt hj, List.getElem?_take_of_lt hj,
      getElem?_pumpFactor_of_lt hcc hc' hL (by omega)]
  · rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-- Pumping to a greater length extends the shorter pumped word. -/
theorem pumpFactor_prefix (hcc : c < c') (hc' : c' ≤ x.length) {L L' : ℕ} (h : L ≤ L') :
    pumpFactor x c c' L <+: pumpFactor x c c' L' := by
  unfold pumpFactor
  rw [List.prefix_append_right_inj]
  have hlen := le_length_pow_loop hcc hc' L
  have e1 : pow ((x.drop c).take (c' - c)) (L' + 1) =
      pow ((x.drop c).take (c' - c)) (L + 1) ++ pow ((x.drop c).take (c' - c)) (L' - L) := by
    rw [← Words.pow_add]; congr 1; omega
  have e2 : (pow ((x.drop c).take (c' - c)) (L + 1)).take L =
      ((pow ((x.drop c).take (c' - c)) (L' + 1)).take L').take L := by
    rw [List.take_take, min_eq_left h, e1, List.take_append_of_le_length (by omega)]
  rw [e2]
  exact List.take_prefix _ _

end PumpFactor

/-! ## Pumping a closed factor -/

theorem take_succ_eq_append {w : List α} {p : ℕ} (h : p < w.length) :
    w.take (p + 1) = w.take p ++ [w[p]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some]

section Closed

variable {T : Table α S k} {q0 : S} {x : List α} {B c c' L : ℕ}

theorem ClosedAt.window (hcl : ClosedAt T q0 x B c c') {j : ℕ} (hj : j < B) :
    x[c - B + j]? = x[c' - B + j]? := by
  obtain ⟨hB, hcc, hc', hn⟩ := hcl
  have h2 := congrArg (fun n => n.2[j]?) hn
  simp only [windowState, List.getElem?_drop, List.getElem?_take] at h2
  rwa [ite_eq_left (by omega), ite_eq_left (by omega)] at h2

/-- The letters of the pumped factor repeat with period `c' - c` from `c - B` on. -/
theorem pumpFactor_letter_period (hcl : ClosedAt T q0 x B c c') (hL : c' - c ≤ L) {p : ℕ}
    (hp : c - B ≤ p) (hpL : p + (c' - c) < c + L) :
    (pumpFactor x c c' L)[p]? = (pumpFactor x c c' L)[p + (c' - c)]? := by
  have ⟨hB, hcc, hc', _⟩ := hcl
  by_cases hpc : p < c
  · rw [getElem?_pumpFactor_of_lt hcc hc' hL (by omega),
      getElem?_pumpFactor_of_lt hcc hc' hL (by omega)]
    have := hcl.window (j := p - (c - B)) (by omega)
    rwa [show c - B + (p - (c - B)) = p by omega,
      show c' - B + (p - (c - B)) = p + (c' - c) by omega] at this
  · exact (getElem?_stay_period hcc hc' (by omega) hpL).symm

/-- A function `F` of words that is updated letter by letter, `F (w ++ [a]) = G (F w) a`, and
takes the same value on the prefixes of length `c < c'` repeats with period `c' - c` from `c` on
along the pumped factor. -/
theorem pumpFactor_period_of_snoc {β : Type*} (F : List α → β) (G : β → α → β)
    (hF : ∀ w a, F (w ++ [a]) = G (F w) a) (hcc : c < c') (hc' : c' ≤ x.length)
    (hFc : F (x.take c) = F (x.take c')) (hL : c' - c ≤ L) {p : ℕ} (hp : c ≤ p)
    (hpL : p + (c' - c) ≤ c + L) :
    F ((pumpFactor x c c' L).take (p + (c' - c))) = F ((pumpFactor x c c' L).take p) := by
  have hlen := length_pumpFactor (L := L) hcc hc'
  induction p, hp using Nat.le_induction with
  | base =>
    rw [show c + (c' - c) = c' by omega, pumpFactor_take hcc hc' hL le_rfl,
      pumpFactor_take hcc hc' hL hcc.le]
    exact hFc.symm
  | succ p hp ih =>
    have hlet := getElem?_stay_period hcc hc' hp (by omega : p + (c' - c) < c + L)
    rw [List.getElem?_eq_getElem (by omega), List.getElem?_eq_getElem (by omega),
      Option.some_inj] at hlet
    rw [show p + 1 + (c' - c) = p + (c' - c) + 1 by omega, take_succ_eq_append (by omega),
      take_succ_eq_append (by omega), hF, hF, ih (by omega), hlet]

/-- Under the hypotheses of `pumpFactor_period_of_snoc`, the value of `F` on every prefix of the
pumped factor is its value on a prefix of `x` of length at most `c'`, and longer than `c` if the
prefix of the pumped factor is. -/
theorem pumpFactor_reduce_of_snoc {β : Type*} (F : List α → β) (G : β → α → β)
    (hF : ∀ w a, F (w ++ [a]) = G (F w) a) (hcc : c < c') (hc' : c' ≤ x.length)
    (hFc : F (x.take c) = F (x.take c')) (hL : c' - c ≤ L) :
    ∀ p ≤ c + L, ∃ p' ≤ c', (c < p → c < p') ∧
      F ((pumpFactor x c c' L).take p) = F (x.take p') := by
  intro p
  induction p using Nat.strong_induction_on with
  | _ p ih =>
    intro hp
    by_cases h1 : p ≤ c'
    · exact ⟨p, h1, id, by rw [pumpFactor_take hcc hc' hL h1]⟩
    · have hst := pumpFactor_period_of_snoc F G hF hcc hc' hFc hL (p := p - (c' - c)) (by omega)
        (by omega)
      rw [show p - (c' - c) + (c' - c) = p by omega] at hst
      obtain ⟨p', hp', hc, he⟩ := ih (p - (c' - c)) (by omega) (by omega)
      exact ⟨p', hp', fun _ => hc (by omega), hst.trans he⟩

end Closed

/-! ## Comparisons with a target -/

/-- If `x[c, c')` is closed for the suffix dictionary of the targets `ts` at window `B`, and no
occurrence of the suffix of length `B` of the target `t ∈ ts` ends in `(c, c']`, every comparison
of the pumped factor with `t`, read from any state `qt`, is a comparison of `x` with `t`. Empty
targets are included. -/
theorem comparison_of_pumpFactor [DecidableEq α] [DecidableEq S] {T : Table α S k} {q0 qt : S}
    {x t : List α} {ts : List (List α)} {B c c' L : ℕ}
    (hcl : NodeClosedAt T q0 (suffixDictionary ts B) x c c') (ht : t ∈ ts)
    (hfree : NoSuffixOccurrenceEndsBetween x t B c c') (hL : c' - c ≤ L) :
    T.pathChannel q0 (pumpFactor x c c' L) qt t ⊆ T.pathChannel q0 x qt t := by
  intro pq hpq
  rw [mem_pathChannel] at hpq ⊢
  obtain ⟨a, ha, b, hb, hpre, rfl⟩ := hpq
  have ⟨hcc, hc', hnode⟩ := hcl
  have hlen := length_pumpFactor (L := L) hcc hc'
  set y := pumpFactor x c c' L with hy
  set ℓ := t.length - b with hℓ
  have hu : (t.drop b).length = ℓ := by simp [hℓ]
  have hpre' := (prefix_drop_iff ha).mp hpre
  rw [hu] at hpre'
  by_cases h1 : a + ℓ ≤ c'
  · -- the occurrence ends at or before `c'`, where the pumped factor agrees with `x`
    refine ⟨a, by omega, b, hb, ?_, by rw [hy, pumpFactor_take hcc hc' hL (by omega)]⟩
    rw [prefix_drop_iff (by omega), hu]
    refine ⟨by omega, fun j hj => ?_⟩
    rw [← hpre'.2 j hj, hy, getElem?_pumpFactor_of_lt hcc hc' hL (by omega)]
  -- the occurrence ends at `a + ℓ > c'`, with the suffix node of a cut `e ∈ (c, c']` of `x`
  have hD : [] ∈ suffixDictionary ts B := nil_mem_suffixDictionary
  have hpreD : ∀ u (a : α), u ++ [a] ∈ suffixDictionary ts B → u ∈ suffixDictionary ts B :=
    fun u _ h => mem_suffixDictionary_of_infix h (List.prefix_append _ _).isInfix
  obtain ⟨e, he, hce, hen⟩ := pumpFactor_reduce_of_snoc (suffixNode T q0 (suffixDictionary ts B))
    (suffixNodeStep T (suffixDictionary ts B)) (suffixNode_snoc T q0 hD hpreD) hcc hc' hnode hL
    (a + ℓ) (by omega)
  have hce' := hce (by omega)
  have hsuf : t.drop b <:+ y.take (a + ℓ) := by
    rw [suffix_take_iff (by omega), hu]
    refine ⟨by omega, fun j hj => ?_⟩
    rw [show a + ℓ - ℓ + j = a + j by omega, hpre'.2 j hj]
  by_cases h2 : ℓ ≤ B
  · -- the compared suffix lies in the dictionary: it ends at `e` with the same state before it
    obtain ⟨hpx, hst⟩ := suffix_of_suffixNode_eq T q0 hen hsuf
      (mem_suffixDictionary_of_suffix ht (List.drop_suffix b t) (by omega))
    simp only [List.length_take, hu, List.take_take] at hst
    rw [min_eq_left (by omega : e ≤ x.length), min_eq_left (by omega : a + ℓ ≤ y.length),
      min_eq_left (by omega : e - ℓ ≤ e), min_eq_left (by omega : a + ℓ - ℓ ≤ a + ℓ),
      show a + ℓ - ℓ = a by omega] at hst
    rw [suffix_take_iff (by omega), hu] at hpx
    refine ⟨e - ℓ, by omega, b, hb, ?_, by rw [hst]⟩
    rw [prefix_drop_iff (by omega), hu]
    exact ⟨by omega, fun j hj => hpx.2 j hj⟩
  · -- the suffix of length `B` of the target would end inside `(c, c']`
    exfalso
    have hBt : B ≤ t.length := by omega
    have hv : Words.suffixOfLength t B <:+ y.take (a + ℓ) :=
      (List.suffix_of_suffix_length_le (List.drop_suffix _ t) (List.drop_suffix b t)
        (by simp; omega)).trans hsuf
    obtain ⟨hvx, -⟩ := suffix_of_suffixNode_eq T q0 hen hv
      (mem_suffixDictionary_of_suffix ht (List.drop_suffix _ t) (by simp))
    have hocc : e ∈ Words.occurrences x t B :=
      Words.mem_occurrences.mpr ⟨by omega, hBt, hvx⟩
    rcases hfree _ hocc with h | h <;> omega

/-- If `x[c, c')`, with `h = c' - c`, is closed at a window `B' ≥ B + h` and
`suffixReturnGap t B > h`, then no occurrence of the suffix of length `B'` of `t` ends in
`(c, c']`. -/
theorem noSuffixOccurrenceEndsBetween_of_closedAt_of_suffixReturnGap_gt [DecidableEq α]
    {T : Table α S k} {q0 : S}
    {x t : List α} {B B' c c' : ℕ}
    (hcl : ClosedAt T q0 x B' c c') (hB : B + (c' - c) ≤ B')
    (hD : ∀ h,
        Words.suffixReturnGap t B = some h → c' - c <
            h) : NoSuffixOccurrenceEndsBetween x t B' c c' := by
  intro e he
  by_contra hcon
  push Not at hcon
  have ⟨hB', hcc, hc', _⟩ := hcl
  rw [Words.mem_occurrences] at he
  obtain ⟨hex, hBt, hocc⟩ := he
  have hlen' : (Words.suffixOfLength t B').length = B' := by simp [hBt]
  rw [suffix_take_iff hex, hlen'] at hocc
  obtain ⟨hBe, hocc⟩ := hocc
  set h := c' - c with hh
  -- `v_B(t)` occurs in `t` ending at distance `h` from its end
  have hocc2 : Words.suffixOfLength t B <:+ t.take (t.length - h) := by
    rw [suffix_take_iff (by omega)]
    simp only [Words.length_suffixOfLength, min_eq_left (by omega : B ≤ t.length)]
    refine ⟨by omega, fun j hj => ?_⟩
    have e1 := hocc (B' - h - B + j) (by omega)
    have e2 := hocc (B' - B + j) (by omega)
    have e3 := hcl.window (j := e - h - B + j - (c - B')) (by omega)
    rw [getElem?_suffixOfLength] at e1 e2
    rw [getElem?_suffixOfLength]
    have i1 : t.length - h - B + j = t.length - B' + (B' - h - B + j) := by omega
    have i2 : t.length - B + j = t.length - B' + (B' - B + j) := by omega
    rw [i1, i2, ← e1, ← e2]
    have i3 : e - B' + (B' - h - B + j) = c - B' + (e - h - B + j - (c - B')) := by omega
    have i4 : e - B' + (B' - B + j) = c' - B' + (e - h - B + j - (c - B')) := by omega
    rw [i3, i4]
    exact e3
  obtain ⟨h0, hD0, hle⟩ := Words.suffixReturnGap_le_of_occ (by omega) (by omega) (by omega) hocc2
  have := hD h0 hD0
  omega

/-! ## Pumping after the first rejected cut -/

/-- Replacing an eligible word by a pumped closed factor after its first rejected cut gives an
eligible word with an immortal endpoint and the same first rejected cut. -/
theorem pumpFactor_eligible [DecidableEq α] (M : StructuralReader α S k)
    {W W' : Fin k → List α} {i : Fin k} {D : Finset (List α)} {c c' L : ℕ} (hW : M.Eligible W i)
    (hcl : NodeClosedAt M.toTable (M.start i) D (W i) c c') (hJ : M.firstRejection W i ≤ c)
    (hL : c' - c ≤ L) (hW' : W' i = pumpFactor (W i) c c' L) :
    M.Eligible W' i ∧ M.Immortal (M.endState W' i) ∧ M.firstRejection W' i =
        M.firstRejection W i := by
  classical
  have ⟨hcc, hc', _⟩ := hcl
  have hlen := length_pumpFactor (L := L) hcc hc'
  have hred : ∀ L', c' - c ≤ L' → ∀ p ≤ c + L', ∃ p' ≤ c', (c < p → c < p') ∧
      runFrom M.step (M.start i) ((pumpFactor (W i) c c' L').take p) =
        runFrom M.step (M.start i) ((W i).take p') := fun L' hL' =>
    pumpFactor_reduce_of_snoc (runFrom M.step (M.start i)) M.step (runFrom_snoc M.step _) hcc
      hc' hcl.state hL'
  have hq : ∀ a, M.runPrefix W' i a =
      runFrom M.step (M.start i) ((pumpFactor (W i) c c' L).take a) := by
    intro a; simp only [Table.runPrefix, hW']
  have hlive : ∀ L', c' - c ≤ L' → ∀ p ≤ c + L',
      runFrom M.step (M.start i) ((pumpFactor (W i) c c' L').take p) ≠ M.dead := by
    intro L' hL' p hp
    obtain ⟨p', hp', _, he⟩ := hred L' hL' p hp
    rw [he]
    exact hW.1 p' (by omega)
  have helig : M.Eligible W' i := by
    refine ⟨fun a ha => ?_, ?_⟩
    · rw [hq]; rw [hW', hlen] at ha; exact hlive L hL a ha
    · simp only [Table.endState, hq, hW', hlen]
      obtain ⟨p', hp', hc, he⟩ := hred L hL (c + L) le_rfl
      rw [he]
      exact StructuralReader.rejected_of_firstRejection_le hW (by have := hc (by omega); omega)
          (by omega)
  refine ⟨helig, ?_, ?_⟩
  · -- continue along longer pumped words
    intro n
    have hpre := pumpFactor_prefix (x := W i) (L := L) (L' := L + n) hcc hc' (by omega)
    have hlen' := length_pumpFactor (x := W i) (L := L + n) hcc hc'
    refine ⟨(pumpFactor (W i) c c' (L + n)).drop (c + L), by rw [List.length_drop, hlen']; omega,
      fun a ha => ?_⟩
    have hz : (pumpFactor (W i) c c' (L + n)).take (c + L) = pumpFactor (W i) c c' L := by
      obtain ⟨r, hr⟩ := hpre
      rw [← hr, List.take_left' hlen]
    have hend : M.endState W' i = runFrom M.step (M.start i) (pumpFactor (W i) c c' L) := by
      simp only [Table.endState, hq, hW', List.take_length]
    rw [hend, ← runFrom_append, ← hz, ← List.take_add]
    exact hlive (L + n) (by omega) _ (by omega)
  · apply StructuralReader.firstRejection_eq_of_rejected helig
    · rw [hq, pumpFactor_take hcc hc' hL (by omega)]
      exact (StructuralReader.firstRejection_spec hW).2.1
    · intro a' ha'
      rw [hq, pumpFactor_take hcc hc' hL (by omega)]
      exact (StructuralReader.firstRejection_spec hW).2.2 a' ha'

open DeciSigma1.Arithmetic DeciSigma1.Words DeciSigma1.Automata

variable {ι : Type}

/-! ## Runs along rays -/

section Runs

variable (M : StructuralReader α S k)

/-- The state at cut `a` of the run along the ray `Ω` from `q`. -/
def rayState (q : S) (Ω : Ray α) (a : ℕ) : S := runFrom M.step q (streamPrefix Ω.stream a)

variable {M}

theorem rayState_add (q : S) (Ω : Ray α) (x t : ℕ) :
    rayState M q Ω (x + t) =
        runFrom M.step (rayState M q Ω x) (streamPrefix (fun i => Ω.stream (x + i)) t) := by
  simp only [rayState]
  rw [streamPrefix_add, runFrom_append]

/-- A state loop along a stretch whose text repeats loops forever. -/
theorem rayState_loop (q : S) (Ω : Ray α) {x d : ℕ}
    (hxd : rayState M q Ω (x + d) = rayState M q Ω x)
    (hshift : ∀ s, Ω.stream (x + d + s) = Ω.stream (x + s)) :
    ∀ m t, rayState M q Ω (x + t + m * d) = rayState M q Ω (x + t) := by
  have hf : (fun i => Ω.stream (x + d + i)) = fun i => Ω.stream (x + i) := funext hshift
  have hloop : ∀ t, rayState M q Ω (x + d + t) = rayState M q Ω (x + t) := by
    intro t
    rw [rayState_add q Ω (x + d) t, hxd, hf, ← rayState_add]
  intro m
  induction m with
  | zero => intro t; simp
  | succ m ih =>
    intro t
    rw [show x + t + (m + 1) * d = x + d + (t + m * d) by ring, hloop, ← Nat.add_assoc, ih]

variable [DecidableEq α] [Fintype S]

/-- The horizon `onset + N · period`: every pair of a state and a phase that occurs after the onset
occurs before the horizon. -/
def rayHorizon (S : Type) [Fintype S] (Ω : Ray α) : ℕ := Ω.onset + Fintype.card S * Ω.period

/-- Every cut of a ray has a cut at or before it and below the horizon with the same state and
the same infinite suffix. -/
theorem ray_state_reduce (q : S) (Ω : Ray α) (a : ℕ) :
    ∃ a', a' ≤ a ∧ a' < rayHorizon S Ω ∧ rayState M q Ω a' = rayState M q Ω a ∧
      ∀ t, Ω.stream (a' + t) = Ω.stream (a + t) := by
  classical
  by_cases hlt : a < rayHorizon S Ω
  · exact ⟨a, le_rfl, hlt, rfl, fun _ => rfl⟩
  unfold rayHorizon at hlt ⊢
  have hν : 0 < Ω.period := Ray.period_pos
  have hper : PeriodicFrom Ω.stream Ω.onset Ω.period := (Ray.leastStreamPeriod_shift le_rfl).2.1
  -- pigeonhole on (state, phase) over the cuts `A, …, A + N ν`
  let f : Fin (Fintype.card S * Ω.period + 1) → S × Fin Ω.period := fun m =>
    (rayState M q Ω (Ω.onset + m), ⟨m % Ω.period, Nat.mod_lt _ hν⟩)
  have hcard : Fintype.card (S × Fin Ω.period) <
      Fintype.card (Fin (Fintype.card S * Ω.period + 1)) := by
    simp [Fintype.card_prod]
  obtain ⟨m₁, m₂, hne, he⟩ := Fintype.exists_ne_map_eq_of_card_lt f hcard
  obtain ⟨x, d, hxA, hd, hxd, hdν, hst⟩ : ∃ x d, Ω.onset ≤ x ∧ 0 < d ∧
      x + d ≤ Ω.onset + Fintype.card S * Ω.period ∧ Ω.period ∣ d ∧
      rayState M q Ω (x + d) = rayState M q Ω x := by
    have hs := congrArg Prod.fst he
    have hp := congrArg (fun z => (z.2 : ℕ)) he
    simp only [f] at hs hp
    rcases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with h | h
    · refine ⟨Ω.onset + m₁, m₂ - m₁, by omega, by omega, by have := m₂.isLt; omega,
        (Nat.modEq_iff_dvd' h.le).mp hp, ?_⟩
      rw [show Ω.onset + m₁ + (m₂ - m₁) = Ω.onset + m₂ by omega]; exact hs.symm
    · refine ⟨Ω.onset + m₂, m₁ - m₂, by omega, by omega, by have := m₁.isLt; omega,
        (Nat.modEq_iff_dvd' h.le).mp hp.symm, ?_⟩
      rw [show Ω.onset + m₂ + (m₁ - m₂) = Ω.onset + m₁ by omega]; exact hs
  obtain ⟨c, rfl⟩ := hdν
  have hshift : ∀ s, Ω.stream (x + Ω.period * c + s) = Ω.stream (x + s) := by
    intro s
    have := hper.add_mul (x - Ω.onset + s) c
    rw [show Ω.onset + (x - Ω.onset + s) + c * Ω.period = x + Ω.period * c + s by
      rw [show Ω.onset + (x - Ω.onset + s) = x + s by omega]; ring,
      show Ω.onset + (x - Ω.onset + s) = x + s by omega] at this
    exact this
  have hloop := rayState_loop q Ω hst hshift
  have hdiv := Nat.mod_add_div (a - x) (Ω.period * c)
  have hmodlt := Nat.mod_lt (a - x) hd
  refine ⟨x + (a - x) % (Ω.period * c), by omega, by omega, ?_, ?_⟩
  · have := hloop ((a - x) / (Ω.period * c)) ((a - x) % (Ω.period * c))
    rw [this.symm]
    congr 1
    rw [mul_comm ((a - x) / (Ω.period * c))]; omega
  · intro t
    have key :=
        hper.add_mul (x - Ω.onset + (a - x) % (Ω.period * c) + t) (c * ((a - x) / (Ω.period * c)))
    rw [show Ω.onset + (x - Ω.onset + (a - x) % (Ω.period * c) + t) = x + (a - x) %
        (Ω.period * c) + t by
      omega] at key
    rw [← key]
    congr 1
    rw [show c * ((a - x) / (Ω.period * c)) * Ω.period = Ω.period * c * ((a - x) /
        (Ω.period * c)) by ring]
    omega

end Runs

/-! ## The ray of a closed factor -/

/-- The ray `x[:c] τ^ω` of a closed factor `τ = x[c:c']`. -/
def repeatFactorRay (x : List α) (c c' : ℕ) (hcc : c < c') (hc' : c' ≤ x.length) : Ray α :=
  ⟨x.take c, (x.drop c).take (c' - c), loop_ne_nil hcc hc'⟩

/-- The prefixes of the ray of a closed factor are the pumped factors. -/
theorem streamPrefix_repeatFactorRay {x : List α} {c c' : ℕ} (hcc : c < c') (hc' : c' ≤ x.length)
    (L : ℕ) : streamPrefix (repeatFactorRay x c c' hcc hc').stream (c + L) =
        pumpFactor x c c' L := by
  have h := Ray.streamPrefix_stream (Ω := repeatFactorRay x c c' hcc hc') L
  simp only [repeatFactorRay, List.length_take, min_eq_left (by omega : c ≤ x.length)] at h
  exact h

/-- The onset of the ray of a factor `x[c, c')` is at most `c`. -/
theorem onset_repeatFactorRay_le [DecidableEq α] {x : List α} {c c' : ℕ} (hcc : c < c')
    (hc' : c' ≤ x.length) : (repeatFactorRay x c c' hcc hc').onset ≤ c :=
  Ray.onset_le_stem.trans (by simp [repeatFactorRay])

theorem period_repeatFactorRay_le [DecidableEq α] {x : List α} {c c' : ℕ} (hcc : c < c')
    (hc' : c' ≤ x.length) : (repeatFactorRay x c c' hcc hc').period ≤ c' - c := by
  have :=
      Nat.le_of_dvd (Ray.loop_length_pos _) (Ray.period_dvd (Ω := repeatFactorRay x c c' hcc hc'))
  simpa [repeatFactorRay, length_loop hc'] using this

/-! ## The ray difference system -/

section System

variable [DecidableEq α] [Fintype S] (M : StructuralReader α S k) [Fintype ι] [DecidableEq ι]

/-- The largest onset of the rays. -/
def maxOnset (Ω : ι → Ray α) : ℕ := Finset.univ.sup fun i => (Ω i).onset

/-- The largest period of the rays. -/
def maxPeriod (Ω : ι → Ray α) : ℕ := Finset.univ.sup fun i => (Ω i).period

/-- The constraints `L j ≥ L i + (b - a + 1)` for distinct rays `i ≠ j`, host cuts `a` below the
horizon and target cuts `b ≤ J j` with an admitted state pair and equal infinite suffixes. -/
def rayEdges (st : ι → S) (Ω : ι → Ray α) (J : ι → ℕ) : Finset (ι × ι × ℤ) :=
  Finset.univ.biUnion fun i => Finset.univ.biUnion fun j =>
    if i = j then ∅ else
      (((Finset.range (rayHorizon S (Ω i))) ×ˢ (Finset.range (J j + 1))).filter
        (fun ab => M.admitted (rayState M (st i) (Ω i) ab.1) (rayState M (st j) (Ω j) ab.2) = true ∧
          ∀ t, (Ω i).stream (ab.1 + t) = (Ω j).stream (ab.2 + t))).image
        (fun ab => (i, j, (ab.2 : ℤ) - ab.1 + 1))

/-- The difference system of the ray lengths, from the constraints `rayEdges`. -/
def raySystem (st : ι → S) (Ω : ι → Ray α) (J : ι → ℕ) : DifferenceSystem ι :=
  DifferenceSystem.ofFinset (rayEdges M st Ω J)

variable {M}

theorem sat_raySys_iff {st : ι → S} {Ω : ι → Ray α} {J : ι → ℕ} {x : ι → ℤ} :
    (raySystem M st Ω J).Sat x ↔ ∀ i j, i ≠ j → ∀ a < rayHorizon S (Ω i), ∀ b ≤ J j,
      M.admitted (rayState M (st i) (Ω i) a) (rayState M (st j) (Ω j) b) = true →
      (∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t)) → x i + ((b : ℤ) - a + 1) ≤ x j := by
  rw [raySystem, DifferenceSystem.sat_ofFinset_iff]
  constructor
  · intro h i j hij a ha b hb hadm heq
    apply h (i, j, (b : ℤ) - a + 1)
    simp only [rayEdges, Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨i, j, ?_⟩
    rw [ite_eq_right hij, Finset.mem_image]
    exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
      ⟨Finset.mem_range.mpr ha, Finset.mem_range.mpr (by omega)⟩, hadm, heq⟩, rfl⟩
  · intro h e he
    simp only [rayEdges, Finset.mem_biUnion, Finset.mem_univ, true_and] at he
    obtain ⟨i, j, he⟩ := he
    split_ifs at he with hij
    · simp at he
    · obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨hab, hadm, heq⟩ := Finset.mem_filter.mp hab
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      exact h i j hij a (Finset.mem_range.mp ha) b (by have := Finset.mem_range.mp hb; omega)
        hadm heq

omit [DecidableEq ι] in
theorem onset_le_maxOnset (Ω : ι → Ray α) (i : ι) : (Ω i).onset ≤ maxOnset Ω :=
  Finset.le_sup (f := fun i => (Ω i).onset) (Finset.mem_univ i)

omit [DecidableEq ι] in
theorem period_le_maxPeriod (Ω : ι → Ray α) (i : ι) : (Ω i).period ≤ maxPeriod Ω :=
  Finset.le_sup (f := fun i => (Ω i).period) (Finset.mem_univ i)

omit [Fintype S] [Fintype ι] [DecidableEq ι] in
/-- A comparison among ray prefixes, read as cuts and states of the rays. -/
theorem mem_pathChannel_rays [DecidableEq S] {st : ι → S} {Ω : ι → Ray α} {L : ι → ℕ} {i j : ι}
    {pq : S × S} :
    pq ∈ M.pathChannel (st i) (streamPrefix (Ω i).stream (L i)) (st j)
        (streamPrefix (Ω j).stream (L j)) ↔
      ∃ a ≤ L i, ∃ b ≤ L j, L j - b ≤ L i - a ∧
        (∀ t < L j - b, (Ω j).stream (b + t) = (Ω i).stream (a + t)) ∧
        pq = (rayState M (st i) (Ω i) a, rayState M (st j) (Ω j) b) := by
  rw [Table.mem_pathChannel]
  simp only [length_streamPrefix, take_streamPrefix]
  constructor
  · rintro ⟨a, ha, b, hb, hpre, rfl⟩
    rw [drop_streamPrefix_prefix_iff _ _ hb ha] at hpre
    exact ⟨a, ha, b, hb, hpre.1, hpre.2, by simp [rayState, min_eq_left ha, min_eq_left hb]⟩
  · rintro ⟨a, ha, b, hb, h1, h2, rfl⟩
    refine ⟨a, ha, b, hb, (drop_streamPrefix_prefix_iff _ _ hb ha).mpr ⟨h1, h2⟩, ?_⟩
    simp [rayState, min_eq_left ha, min_eq_left hb]

/-- Suppose every target cut of an admitted pair is at most `J`,
`L j > J j + maxOnset + 2 · maxPeriod`, no admitted comparison of a ray with itself with `a ≤ b`
has equal infinite suffixes, and `L` solves the ray system. Then the prefixes of length `L` carry
no admitted comparison, between any two rays or a ray and itself. -/
theorem ray_prefix_hole [DecidableEq S] (st : ι → S) (Ω : ι → Ray α) (J L : ι → ℕ)
    (hK : ∀ j b p, b ≤ L j → M.admitted p (rayState M (st j) (Ω j) b) = true → b ≤ J j)
    (hlong : ∀ j, J j + maxOnset Ω + 2 * maxPeriod Ω < L j)
    (hself : ∀ i a b, b ≤ J i → a ≤ b →
      M.admitted (rayState M (st i) (Ω i) a) (rayState M (st i) (Ω i) b) = true →
      ¬ ∀ t, (Ω i).stream (a + t) = (Ω i).stream (b + t))
    (hsat : (raySystem M st Ω J).Sat (fun i => (L i : ℤ))) :
    ∀ i j, ∀ pq ∈ M.pathChannel (st i) (streamPrefix (Ω i).stream (L i)) (st j)
      (streamPrefix (Ω j).stream (L j)), M.admitted pq.1 pq.2 = false := by
  intro i j pq hpq
  rw [mem_pathChannel_rays] at hpq
  obtain ⟨a, ha, b, hb, hlen, hagree, rfl⟩ := hpq
  by_contra hadm
  rw [Bool.not_eq_false] at hadm
  have hbJ := hK j b _ hb hadm
  -- the long agreement is an equality of infinite suffixes
  have hinf : ∀ t, (Ω i).stream (a + t) = (Ω j).stream (b + t) := by
    apply Ray.stream_suffix_eq_of_prefix_eq
    intro t ht
    have h1 := onset_le_maxOnset Ω i
    have h2 := onset_le_maxOnset Ω j
    have h3 := period_le_maxPeriod Ω i
    have h4 := period_le_maxPeriod Ω j
    have h5 := hlong j
    exact (hagree t (by omega)).symm
  by_cases hij : i = j
  · subst hij
    exact hself i a b hbJ (by omega) hadm hinf
  · -- reduce the host cut below the horizon
    obtain ⟨a', ha', hha', hst, hsuf⟩ := ray_state_reduce (M := M) (st i) (Ω i) a
    have := (sat_raySys_iff.mp hsat) i j hij a' hha' b hbJ (by rw [hst]; exact hadm)
      (fun t => (hsuf t).trans (hinf t))
    omega

end System

end DeciSigma1.Holes.Tail
