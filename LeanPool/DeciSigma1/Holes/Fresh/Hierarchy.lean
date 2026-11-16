/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

import Mathlib.Algebra.Order.BigOperators.Group.Finset

public import LeanPool.DeciSigma1.Readers.Basic
import Mathlib.Order.SuccPred.Nat
import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # The marker hierarchy of a tuple

The bound on minimal fresh tuples deletes repeated blocks from a fresh tuple `W`. The blocks
come from a hierarchy of *markers*, words built from `W` itself. At level `1` the coordinates
with a nonempty word are active, and the marker of each is the last letter of its word; empty
words are never active. An *anchor* of level `t` in a text is a cut at which an active marker of
level `t` ends; the anchors cut a text into level-`t` blocks. A coordinate stays active at level
`t + 1` if its word has an anchor before its end, and its marker of level `t + 1` is the suffix
of its word that starts where the longest marker ending at the last such anchor starts. Every
marker is a suffix of its word, and a marker of level `t + 1` has exactly two level-`t` anchors:
the end of the marker it starts with, and its own end (`contextAnchors_marker_succ`).

The active markers of one level form a factor antichain: none is a proper factor of another
(`marker_eq_of_infix`). Hence an occurrence of an active marker inside an occurrence of another
one, in any text, is the same occurrence (`marker_occurrences_eq_of_nested`), and anchors are
determined by a bounded neighborhood of the cut.

For a tuple of fresh words, suffixes of one word starting at different cuts carry different
states when one is a prefix of the other. So a fixed text has fewer than `N` nonempty suffixes of
one word as prefixes (`card_prefixComparingCuts_le`). This bounds the number of levels by
`k (N - 1)` (`topLevel_le`) and the number of level-`t` anchors inside an occurrence of a marker
of level `t + 1` by `k (N - 1) + 1` (`card_anchors_inside_marker_le`).

## Main declarations

- `Level`, `level`, `active`, `marker`: the levels of the hierarchy, their active coordinates
  and markers.
- `contextAnchors`, `anchors`: the anchors of a text and of a coordinate.
- `marker_eq_of_infix`, `marker_occurrences_eq_of_nested`: active markers of one level form a
  factor antichain.
- `contextAnchors_marker_succ`, `marker_occurrences_in_next_marker`: a marker of level `t + 1`
  consists of two blocks of level `t`.
- `topLevel`, `topLevel_le`: the highest level, at most `k (N - 1)` for fresh tuples.
- `card_anchors_inside_marker_le`, `card_anchors_Ioc_marker_le`: the number of anchors inside a
  marker of the next level.
-/

@[expose] public section


namespace DeciSigma1.Holes.Fresh

open DeciSigma1.Readers
open Finset

variable {α : Type} {k : ℕ}

/-! ## Occurrences in words -/

section Occurrences

variable {x u v : List α}

/-- `u` ends at the cut `e ≤ |x|` of `x` iff it occurs at position `e - |u|`. -/
theorem suffix_take_iff {e : ℕ} (he : e ≤ x.length) :
    u <:+ x.take e ↔ u.length ≤ e ∧ u <+: x.drop (e - u.length) := by
  have hte : (x.take e).length = e := by simp [Nat.min_eq_left he]
  constructor
  · rintro ⟨s, hs⟩
    have hsl : s.length + u.length = e := by rw [← hte, ← hs, List.length_append]
    refine ⟨by omega, x.drop e, ?_⟩
    have hx : x = s ++ (u ++ x.drop e) := by
      rw [← List.append_assoc, hs, List.take_append_drop]
    rw [show e - u.length = s.length by omega]
    conv_rhs => rw [hx]
    rw [List.drop_left]
  · rintro ⟨hl, r, hr⟩
    refine ⟨x.take (e - u.length), ?_⟩
    have : x.take e = x.take (e - u.length) ++ (x.drop (e - u.length)).take u.length := by
      rw [← List.take_add, Nat.sub_add_cancel hl]
    rw [this, ← hr, List.take_left]

/-- An occurrence of `v` inside an occurrence of `u` in the same word makes `v` a factor of `u`. -/
theorem infix_of_occ {i j : ℕ} (hu : u <+: x.drop i) (hv : v <+: x.drop j) (hij : i ≤ j)
    (hlen : j + v.length ≤ i + u.length) : v <:+: u := by
  obtain ⟨r, hr⟩ := hu
  have hd : x.drop j = u.drop (j - i) ++ r := by
    rw [show j = i + (j - i) by omega, ← List.drop_drop, ← hr,
      List.drop_append_of_le_length (by omega), Nat.add_sub_cancel_left]
  rw [hd] at hv
  have h1 : v <+: u.drop (j - i) :=
    List.prefix_of_prefix_length_le hv (List.prefix_append _ _) (by simp; omega)
  exact List.infix_iff_prefix_suffix.mpr ⟨_, h1, List.drop_suffix _ _⟩

/-- The cut `i + |u|` after an occurrence at `i`. -/
theorem take_occ {i : ℕ} (hu : u <+: x.drop i) : x.take (i + u.length) = x.take i ++ u := by
  rw [List.take_add, ← List.prefix_iff_eq_take.mp hu]

/-- A word that occurs at position `i` ends at the cut `i + |u|`. -/
theorem suffix_take_of_occ {i : ℕ} (hu : u <+: x.drop i) : u <:+ x.take (i + u.length) := by
  rw [take_occ hu]; exact List.suffix_append _ _

/-- A nonempty word occurring at position `i` fits into the word. -/
theorem occ_le_length {i : ℕ} (hu : u <+: x.drop i) (hne : u ≠ []) :
    i + u.length ≤ x.length := by
  have h1 := hu.length_le
  have h2 : 0 < u.length := List.length_pos_iff.mpr hne
  simp only [List.length_drop] at h1
  omega

/-- Two suffixes of one word, the shorter is a suffix of the longer. -/
theorem suffix_of_suffix_of_le {w : List α} (hu : u <:+ w) (hv : v <:+ w)
    (h : u.length ≤ v.length) : u <:+ v := List.suffix_of_suffix_length_le hu hv h

/-- A suffix `u` of a word is the drop at `|w| - |u|`, hence occurs there. -/
theorem occ_of_suffix {w : List α} (hu : u <:+ w) : u <+: w.drop (w.length - u.length) := by
  rw [← List.suffix_iff_eq_drop.mp hu]

end Occurrences

/-! ## Levels -/

/-- One level of the hierarchy: the active words and their markers. Markers of inactive
words are never used. -/
structure Level (α : Type) (k : ℕ) where
  /-- Coordinates participating in this level. -/
  active : Finset (Fin k)
  /-- Distinguishing word assigned to each participating coordinate. -/
  marker : Fin k → List α

namespace Level

variable [DecidableEq α] (L : Level α k)

/-- Cuts `e ≤ |u|` of a text `u` at which an active marker of `L` ends. -/
def markerEndCuts (u : List α) : Finset ℕ :=
  (range (u.length + 1)).filter (fun e => ∃ m ∈ L.active, L.marker m <:+ u.take e)

/-- The last cut `< |x|` at which an active marker ends (`0` if there is none). -/
def lastInteriorCut (x : List α) : ℕ := ((L.markerEndCuts x).filter (· < x.length)).sup id

/-- Length of the longest active marker ending at the cut `e` of `x`. -/
def blockLengthAt (x : List α) (e : ℕ) : ℕ :=
  (L.active.filter (fun m => L.marker m <:+ x.take e)).sup (fun m => (L.marker m).length)

/-- The next level: a word stays active if it has an anchor before its end, and its next marker
starts where the longest marker ending at its last such anchor starts. -/
def next (W : Fin k → List α) : Level α k where
  active := L.active.filter (fun l => ∃ e ∈ L.markerEndCuts (W l), e < (W l).length)
  marker l := (W l).drop (L.lastInteriorCut (W l) - L.blockLengthAt (W l) (L.lastInteriorCut (W l)))

variable {L}

theorem mem_markerEndCuts {u : List α} {e : ℕ} :
    e ∈ L.markerEndCuts u ↔ e ≤ u.length ∧ ∃ m ∈ L.active, L.marker m <:+ u.take e := by
  simp [markerEndCuts]

/-- The active markers of the level are nonempty, and none is a proper factor of another. -/
def FactorAntichain (L : Level α k) : Prop :=
  (∀ m ∈ L.active, L.marker m ≠ []) ∧
    ∀ m ∈ L.active, ∀ m' ∈ L.active, L.marker m <:+: L.marker m' → L.marker m = L.marker m'

/-- Every active marker is a suffix of its own word. -/
def MarkersAreSuffixes (L : Level α k) (W : Fin k → List α) :
    Prop := ∀ m ∈ L.active, L.marker m <:+ W m

omit [DecidableEq α] in
/-- Two active markers ending at one cut are equal. -/
theorem FactorAntichain.eq_of_suffix (hA : L.FactorAntichain) {m m' : Fin k} (hm : m ∈ L.active)
    (hm' : m' ∈ L.active)
    {u : List α} (h : L.marker m <:+ u) (h' : L.marker m' <:+ u) : L.marker m = L.marker m' := by
  rcases List.suffix_or_suffix_of_suffix h h' with h1 | h1
  · exact hA.2 m hm m' hm' h1.isInfix
  · exact (hA.2 m' hm' m hm h1.isInfix).symm

theorem lastInteriorCut_spec {x : List α} (h : ∃ e ∈ L.markerEndCuts x, e < x.length) :
    L.lastInteriorCut x ∈ L.markerEndCuts x ∧ L.lastInteriorCut x < x.length ∧
      ∀ e ∈ L.markerEndCuts x, e < x.length → e ≤ L.lastInteriorCut x := by
  have hne : ((L.markerEndCuts x).filter (· < x.length)).Nonempty := by
    obtain ⟨e, he, hlt⟩ := h
    exact ⟨e, mem_filter.mpr ⟨he, hlt⟩⟩
  obtain ⟨e0, he0, hsup⟩ := exists_mem_eq_sup _ hne id
  rw [mem_filter] at he0
  refine ⟨?_, ?_, ?_⟩
  · simp only [lastInteriorCut, hsup, id]; exact he0.1
  · simp only [lastInteriorCut, hsup, id]; exact he0.2
  · intro e he hlt
    exact le_sup (f := id) (mem_filter.mpr ⟨he, hlt⟩)

theorem blockLengthAt_spec {x : List α} {e : ℕ} (he : e ∈ L.markerEndCuts x) :
    ∃ m ∈ L.active, L.marker m <:+ x.take e ∧ L.blockLengthAt x e = (L.marker m).length := by
  have hne : (L.active.filter (fun m => L.marker m <:+ x.take e)).Nonempty := by
    obtain ⟨-, m, hm, hs⟩ := mem_markerEndCuts.mp he
    exact ⟨m, mem_filter.mpr ⟨hm, hs⟩⟩
  obtain ⟨m, hm, hsup⟩ := exists_mem_eq_sup _ hne (fun m => (L.marker m).length)
  rw [mem_filter] at hm
  exact ⟨m, hm.1, hm.2, hsup⟩

theorem next_active {W : Fin k → List α} {l : Fin k} :
    l ∈ (L.next W).active ↔ l ∈ L.active ∧ ∃ e ∈ L.markerEndCuts (W l), e < (W l).length := by
  simp [next]

theorem next_active_subset (W : Fin k → List α) : (L.next W).active ⊆ L.active := filter_subset _ _

/-- The next marker is the marker ending at the last anchor before the end, followed by the rest
of the word. -/
theorem next_spec {W : Fin k → List α} {l : Fin k} (hl : l ∈ (L.next W).active) :
    ∃ m ∈ L.active, L.marker m <:+ (W l).take (L.lastInteriorCut (W l)) ∧
      L.blockLengthAt (W l) (L.lastInteriorCut (W l)) = (L.marker m).length ∧
      (L.marker m).length ≤ L.lastInteriorCut (W l) ∧
      (L.next W).marker l = (W l).drop (L.lastInteriorCut (W l) - (L.marker m).length) ∧
      (L.next W).marker l = L.marker m ++ (W l).drop (L.lastInteriorCut (W l)) := by
  obtain ⟨-, hex⟩ := next_active.mp hl
  obtain ⟨he, hlt, -⟩ := lastInteriorCut_spec hex
  obtain ⟨m, hm, hs, hlen⟩ := blockLengthAt_spec he
  have hle : L.lastInteriorCut (W l) ≤ (W l).length := hlt.le
  obtain ⟨hl1, hocc⟩ := (suffix_take_iff hle).mp hs
  have hmk : (L.next W).marker l = (W l).drop (L.lastInteriorCut (W l) - (L.marker m).length) := by
    simp only [next, hlen]
  refine ⟨m, hm, hs, hlen, hl1, hmk, ?_⟩
  rw [hmk]
  obtain ⟨r, hr⟩ := hocc
  have hd := congrArg (List.drop (L.marker m).length) hr
  rw [List.drop_left, List.drop_drop, Nat.sub_add_cancel hl1] at hd
  rw [← hr, hd]

/-- The next marker starts strictly before the current marker of the same word. -/
theorem next_start_lt (hA : L.FactorAntichain) {W : Fin k → List α} (hS : L.MarkersAreSuffixes W)
    {l : Fin k}
    (hl : l ∈ (L.next W).active) :
    L.lastInteriorCut (W l) - L.blockLengthAt (W l) (L.lastInteriorCut (W l)) < (W l).length -
        (L.marker l).length := by
  obtain ⟨m, hm, hs, hlen, hl1, -, -⟩ := next_spec hl
  obtain ⟨hlact, hex⟩ := next_active.mp hl
  obtain ⟨-, hlt, -⟩ := lastInteriorCut_spec hex
  have hle : L.lastInteriorCut (W l) ≤ (W l).length := hlt.le
  have hτ := ((suffix_take_iff hle).mp hs).2
  have hσ := occ_of_suffix (hS l hlact)
  have hσl := (hS l hlact).length_le
  rw [hlen]
  by_contra hcon
  have hinf : L.marker m <:+: L.marker l := infix_of_occ hσ hτ (by omega) (by omega)
  have heq := hA.2 m hm l hlact hinf
  have : (L.marker m).length = (L.marker l).length := by rw [heq]
  omega

/-- The current marker of an active word is a proper suffix of its next marker. -/
theorem next_suffix (hA : L.FactorAntichain) {W : Fin k → List α} (hS : L.MarkersAreSuffixes W)
    {l : Fin k}
    (hl : l ∈ (L.next W).active) :
    L.marker l <:+ (L.next W).marker l ∧ (L.marker l).length < ((L.next W).marker l).length := by
  have hns := next_start_lt hA hS hl
  have hσl := (hS l (next_active_subset W hl)).length_le
  have hlen : (L.marker l).length < ((L.next W).marker l).length := by
    simp only [next, List.length_drop]; omega
  exact
      ⟨suffix_of_suffix_of_le (hS l (next_active_subset W hl)) (List.drop_suffix _ _) hlen.le, hlen⟩

/-- The factor antichain property passes to the next level. -/
theorem next_anti (hA : L.FactorAntichain) {W : Fin k → List α} (hS : L.MarkersAreSuffixes W) :
    (L.next W).FactorAntichain := by
  refine ⟨fun l hl => ?_, fun g hg m hm h => ?_⟩
  · obtain ⟨_, -, -, -, -, -, hcat⟩ := next_spec hl
    obtain ⟨-, hex⟩ := next_active.mp hl
    obtain ⟨-, hlt, -⟩ := lastInteriorCut_spec hex
    rw [hcat]
    intro hnil
    have := congrArg List.length hnil
    simp at this
    omega
  · obtain ⟨g', hg', -, -, hlg, -, hcatg⟩ := next_spec hg
    obtain ⟨-, hexg⟩ := next_active.mp hg
    obtain ⟨-, hltg, -⟩ := lastInteriorCut_spec hexg
    obtain ⟨m', hm', -, -, hlm, hmkm, hcatm⟩ := next_spec hm
    obtain ⟨-, hexm⟩ := next_active.mp hm
    obtain ⟨-, hltm, hmaxm⟩ := lastInteriorCut_spec hexm
    obtain ⟨s, r, hsr⟩ := h
    have hO : (L.next W).marker g <+:
        (W m).drop (L.lastInteriorCut (W m) - (L.marker m').length + s.length) := by
      rw [← List.drop_drop, ← hmkm, ← hsr, List.append_assoc, List.drop_left]
      exact List.prefix_append _ _
    have hτgO : L.marker g' <+:
        (W m).drop (L.lastInteriorCut (W m) - (L.marker m').length + s.length) := by
      refine List.IsPrefix.trans ?_ hO
      rw [hcatg]; exact List.prefix_append _ _
    have hτm : L.marker m' <+: (W m).drop (L.lastInteriorCut (W m) - (L.marker m').length) := by
      rw [← hmkm, hcatm]; exact List.prefix_append _ _
    have hlenσg : ((L.next W).marker g).length =
        (L.marker g').length + ((W g).length - L.lastInteriorCut (W g)) := by
      rw [hcatg]; simp
    have hσgne : (L.next W).marker g ≠ [] := by
      intro hnil; have := congrArg List.length hnil; simp only [List.length_nil] at this; omega
    have hOle := occ_le_length hO hσgne
    have hβends : L.lastInteriorCut (W m) - (L.marker m').length + s.length + (L.marker g').length ∈
        L.markerEndCuts (W m) :=
      mem_markerEndCuts.mpr ⟨by omega, g', hg', suffix_take_of_occ hτgO⟩
    have hβle := hmaxm _ hβends (by omega)
    have hinf : L.marker g' <:+: L.marker m' := infix_of_occ hτm hτgO (by omega) (by omega)
    have heqτ := hA.2 g' hg' m' hm' hinf
    have hlenτ : (L.marker g').length = (L.marker m').length := by rw [heqτ]
    have hs0 : s.length = 0 := by omega
    have hsuf : L.marker g <:+ (L.next W).marker g := (next_suffix hA hS hg).1
    have hend : L.lastInteriorCut (W m) - (L.marker m').length + s.length +
        ((L.next W).marker g).length ∈
        L.markerEndCuts (W m) :=
      mem_markerEndCuts.mpr ⟨hOle, g, next_active_subset W hg, hsuf.trans (suffix_take_of_occ hO)⟩
    have hendeq : L.lastInteriorCut (W m) - (L.marker m').length + s.length +
        ((L.next W).marker g).length = (W m).length := by
      by_contra hne
      have := hmaxm _ hend (by omega)
      omega
    have hlenσm : ((L.next W).marker m).length = (W m).length -
        (L.lastInteriorCut (W m) - (L.marker m').length) := by
      rw [hmkm, List.length_drop]
    exact List.IsInfix.eq_of_length ⟨s, r, hsr⟩ (by omega)

/-- Read as a text, a next marker has exactly two anchors: the end of the marker it starts with
and its own end. -/
theorem next_markerEndCuts_eq (hA : L.FactorAntichain) {W : Fin k → List α}
    (hS : L.MarkersAreSuffixes W)
    {l : Fin k}
    (hl : l ∈ (L.next W).active) :
    ∃ m ∈ L.active, L.marker m <+: (L.next W).marker l ∧
      (L.marker m).length < ((L.next W).marker l).length ∧
      L.markerEndCuts ((L.next W).marker l) =
          {(L.marker m).length, ((L.next W).marker l).length} := by
  obtain ⟨m, hm, -, -, hlm, hmk, hcat⟩ := next_spec hl
  obtain ⟨hlact, hex⟩ := next_active.mp hl
  obtain ⟨-, hlt, hmax⟩ := lastInteriorCut_spec hex
  have hpre : L.marker m <+: (L.next W).marker l := by rw [hcat]; exact List.prefix_append _ _
  have hτocc : L.marker m <+: (W l).drop (L.lastInteriorCut (W l) - (L.marker m).length) := by
    rw [← hmk]; exact hpre
  have hσlen : ((L.next W).marker l).length =
      (W l).length - (L.lastInteriorCut (W l) - (L.marker m).length) := by
    rw [hmk, List.length_drop]
  have hτlt : (L.marker m).length < ((L.next W).marker l).length := by
    rw [hcat, List.length_append, List.length_drop]; omega
  refine ⟨m, hm, hpre, hτlt, ?_⟩
  ext p
  simp only [mem_insert, mem_singleton, mem_markerEndCuts]
  constructor
  · rintro ⟨hp, h, hh, hsuf⟩
    have htake : (W l).take (L.lastInteriorCut (W l) - (L.marker m).length + p) =
        (W l).take (L.lastInteriorCut (W l) - (L.marker m).length) ++
            ((L.next W).marker l).take p := by
      rw [List.take_add, hmk]
    have hsufx : L.marker h <:+ (W l).take (L.lastInteriorCut (W l) - (L.marker m).length + p) := by
      rw [htake]; exact hsuf.trans (List.suffix_append _ _)
    have hpe : L.lastInteriorCut (W l) - (L.marker m).length + p ∈ L.markerEndCuts (W l) :=
      mem_markerEndCuts.mpr ⟨by omega, h, hh, hsufx⟩
    rcases Nat.lt_or_ge (L.lastInteriorCut (W l) - (L.marker m).length + p)
        (W l).length with hlt' | hge
    · have hle := hmax _ hpe hlt'
      rcases lt_or_eq_of_le hle with hlt2 | heq
      · exfalso
        have hptake : p ≤ ((L.next W).marker l).length := hp
        obtain ⟨hhl, hocc⟩ := (suffix_take_iff hptake).mp hsuf
        have hocc' : L.marker h <+: (W l).drop
            (L.lastInteriorCut (W l) - (L.marker m).length + (p - (L.marker h).length)) := by
          rw [← List.drop_drop, ← hmk]; exact hocc
        have hinf : L.marker h <:+: L.marker m := infix_of_occ hτocc hocc' (by omega) (by omega)
        have heq := hA.2 h hh m hm hinf
        have : (L.marker h).length = (L.marker m).length := by rw [heq]
        omega
      · left; omega
    · right; omega
  · rintro (rfl | rfl)
    · refine ⟨hpre.length_le, m, hm, ?_⟩
      rw [← List.prefix_iff_eq_take.mp hpre]
    · refine ⟨le_rfl, l, hlact, ?_⟩
      rw [List.take_length]; exact (next_suffix hA hS hl).1

end Level

/-! ## The hierarchy of a tuple -/

variable [DecidableEq α]

/-- The hierarchy of a tuple. Level `0` is a placeholder without markers (its anchors are all
cuts, see `contextAnchors`). At levels `0` and `1` the active coordinates are those with a
nonempty word, and the marker of level `1` is the last letter of the word. -/
def level (W : Fin k → List α) : ℕ → Level α k
  | 0 => ⟨univ.filter (fun l => W l ≠ []), fun _ => []⟩
  | 1 => ⟨univ.filter (fun l => W l ≠ []), fun l => (W l).drop ((W l).length - 1)⟩
  | t + 2 => (level W (t + 1)).next W

/-- Active coordinates at level `t`; at levels `0` and `1`, those with a nonempty word. -/
def active (W : Fin k → List α) (t : ℕ) : Finset (Fin k) := (level W t).active

/-- The markers of level `t`; only those of active coordinates are used. -/
def marker (W : Fin k → List α) (t : ℕ) : Fin k → List α := (level W t).marker

/-- Level-`t` anchors of an arbitrary text: all cuts `≥ 1` at level `0`; for `t ≥ 1`, the cuts
at which an active level-`t` marker ends (word ends are not added). -/
def contextAnchors (W : Fin k → List α) : ℕ → List α → Finset ℕ
  | 0, u => Icc 1 u.length
  | t + 1, u => (level W (t + 1)).markerEndCuts u

/-- Level-`t` anchors of a coordinate: its context anchors and its end. -/
def anchors (W : Fin k → List α) (t : ℕ) (l : Fin k) : Finset ℕ :=
  insert (W l).length (contextAnchors W t (W l))

/-- The top level: the least `t` with no active coordinate at level `t + 1`. The search is
capped at `totalLength W`; the cap never binds (`topLevel_spec`). -/
def topLevel (W : Fin k → List α) : ℕ :=
  Nat.find (⟨totalLength W, Or.inr le_rfl⟩ : ∃ t, active W (t + 1) = ∅ ∨ totalLength W ≤ t)

section Basic

variable (W : Fin k → List α)

/-- The coordinates active at level `0` are those with a nonempty word. -/
@[simp] theorem mem_active_zero {l : Fin k} : l ∈ active W 0 ↔ W l ≠ [] := by
  simp [active, level]

/-- The coordinates active at level `1` are those with a nonempty word. -/
@[simp] theorem mem_active_one {l : Fin k} : l ∈ active W 1 ↔ W l ≠ [] := by
  simp [active, level]

@[simp] theorem marker_zero (l : Fin k) : marker W 0 l = [] := rfl

theorem marker_one (l : Fin k) : marker W 1 l = (W l).drop ((W l).length - 1) := rfl

theorem level_succ_succ (t : ℕ) : level W (t + 2) = (level W (t + 1)).next W := rfl

theorem contextAnchors_succ (t : ℕ) (u : List α) :
    contextAnchors W (t + 1) u = (level W (t + 1)).markerEndCuts u :=
  rfl

theorem mem_contextAnchors_succ {t : ℕ} {u : List α} {e : ℕ} :
    e ∈ contextAnchors W (t + 1) u ↔
      e ≤ u.length ∧ ∃ m ∈ active W (t + 1), marker W (t + 1) m <:+ u.take e :=
  Level.mem_markerEndCuts

/-- Every marker is a suffix of its own word. -/
theorem marker_suffix (t : ℕ) (l : Fin k) : marker W t l <:+ W l := by
  rcases t with _ | _ | t
  · exact List.nil_suffix
  · exact List.drop_suffix _ _
  · exact List.drop_suffix _ _

theorem markers_are_suffixes (t : ℕ) :
    (level W t).MarkersAreSuffixes W := fun m _ => marker_suffix W t m

theorem active_succ_subset (t : ℕ) : active W (t + 1) ⊆ active W t := by
  rcases t with _ | t
  · exact subset_refl _
  · exact Level.next_active_subset W

theorem active_anti {s t : ℕ} (h : s ≤ t) : active W t ⊆ active W s := by
  induction h with
  | refl => exact subset_refl _
  | step _ ih => exact (active_succ_subset W _).trans ih

/-- The word of an active coordinate is nonempty. -/
theorem ne_nil_of_mem_active {t : ℕ} {l : Fin k} (hl : l ∈ active W t) : W l ≠ [] :=
  (mem_active_zero W).mp (active_anti W (Nat.zero_le t) hl)

/-- A coordinate stays active iff it has an internal anchor. -/
theorem mem_active_succ_succ {t : ℕ} {l : Fin k} :
    l ∈ active W (t + 2) ↔
      l ∈ active W (t + 1) ∧ ∃ e ∈ anchors W (t + 1) l, e < (W l).length := by
  simp only [active, level_succ_succ, Level.next_active, anchors, mem_insert, contextAnchors_succ]
  constructor
  · rintro ⟨h1, e, he, hlt⟩; exact ⟨h1, e, Or.inr he, hlt⟩
  · rintro ⟨h1, e, he | he, hlt⟩
    · omega
    · exact ⟨h1, e, he, hlt⟩

end Basic

section Antichain

variable {W : Fin k → List α}

/-- The marker of a nonempty word at level `1` is a single letter. -/
theorem length_marker_one {l : Fin k} (hl : l ∈ active W 1) : (marker W 1 l).length = 1 := by
  have := List.length_pos_iff.mpr ((mem_active_one W).mp hl)
  rw [marker_one, List.length_drop]; omega

theorem level_one_anti : (level W 1).FactorAntichain := by
  refine ⟨fun l hl h => ?_, fun m hm m' hm' h =>
    h.eq_of_length ((length_marker_one hm).trans (length_marker_one hm').symm)⟩
  have := length_marker_one hl
  rw [show marker W 1 l = [] from h] at this
  simp at this

/-- Every level `t + 1` of the hierarchy of a tuple is a factor antichain. -/
theorem level_anti : ∀ t, (level W (t + 1)).FactorAntichain
  | 0 => level_one_anti
  | t + 1 => Level.next_anti (level_anti t) (markers_are_suffixes W (t + 1))

/-- Active markers of one level are never proper factors of each other. -/
theorem marker_eq_of_infix (t : ℕ) (m m' : Fin k) (hm : m ∈ active W t)
    (hm' : m' ∈ active W t) : marker W t m <:+: marker W t m' → marker W t m = marker W t m' := by
  rcases t with _ | t
  · intro _; rfl
  · exact (level_anti t).2 m hm m' hm'

theorem marker_ne_nil {t : ℕ} (ht : 1 ≤ t) {m : Fin k}
    (hm : m ∈ active W t) : marker W t m ≠ [] := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact (level_anti t).1 m hm

/-- Markers of one level ending at one cut have the same text. -/
theorem marker_eq_of_suffix {t : ℕ} {m m' : Fin k}
    (hm : m ∈ active W t) (hm' : m' ∈ active W t) {u : List α} (h : marker W t m <:+ u)
    (h' : marker W t m' <:+ u) : marker W t m = marker W t m' := by
  rcases t with _ | t
  · rfl
  · exact Level.FactorAntichain.eq_of_suffix (level_anti t) hm hm' h h'

/-- Each next marker has the current marker of its word as a proper suffix. -/
theorem marker_suffix_succ {t : ℕ} {l : Fin k}
    (hl : l ∈ active W (t + 1)) : marker W t l <:+ marker W (t + 1) l := by
  rcases t with _ | t
  · exact List.nil_suffix
  · exact (Level.next_suffix (level_anti t) (markers_are_suffixes W (t + 1)) hl).1

/-- The marker of a coordinate that stays active grows strictly. -/
theorem marker_grows {t : ℕ} {l : Fin k} (hl : l ∈ active W (t + 1)) :
    (marker W t l).length < (marker W (t + 1) l).length := by
  rcases t with _ | t
  · rw [length_marker_one hl]; exact Nat.one_pos
  · exact (Level.next_suffix (level_anti t) (markers_are_suffixes W (t + 1)) hl).2

theorem le_length_marker {t : ℕ} {l : Fin k} (hl : l ∈ active W t) :
    t ≤ (marker W t l).length := by
  induction t with
  | zero => exact Nat.zero_le _
  | succ t ih =>
    have := ih (active_succ_subset W t hl)
    have := marker_grows hl
    omega

theorem active_eq_empty_of_totalLength_lt {t : ℕ} (h : totalLength W < t) :
    active W t = ∅ := by
  rw [eq_empty_iff_forall_notMem]
  intro l hl
  have h1 := le_length_marker hl
  have h2 := (marker_suffix W t l).length_le
  have h3 := length_le_totalLength W l
  omega

/-- Read as a text, a marker of level `t + 1` has exactly two anchors of level `t`: the end of
the level-`t` marker it starts with, and its own end. -/
theorem contextAnchors_marker_succ {t : ℕ} (ht : 1 ≤ t) {l : Fin k} (hl : l ∈ active W (t + 1)) :
    ∃ m ∈ active W t, marker W t m <+: marker W (t + 1) l ∧
      (marker W t m).length < (marker W (t + 1) l).length ∧
      contextAnchors W t (marker W (t + 1) l) =
        {(marker W t m).length, (marker W (t + 1) l).length} := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact Level.next_markerEndCuts_eq (level_anti t) (markers_are_suffixes W (t + 1)) hl

/-- The complete occurrences of level-`t` markers in a marker of level `t + 1` are exactly one
prefix occurrence and one suffix occurrence. -/
theorem marker_occurrences_in_next_marker {t : ℕ} (ht : 1 ≤ t) {l : Fin k}
    (hl : l ∈ active W (t + 1)) :
    (∃ m ∈ active W t, marker W t m <+: marker W (t + 1) l) ∧
      marker W t l <:+ marker W (t + 1) l ∧
      ∀ h ∈ active W t, ∀ i, marker W t h <+: (marker W (t + 1) l).drop i →
        i = 0 ∨ i + (marker W t h).length = (marker W (t + 1) l).length := by
  obtain ⟨m, hm, hpre, -, hset⟩ := contextAnchors_marker_succ ht hl
  refine ⟨⟨m, hm, hpre⟩, marker_suffix_succ hl, fun h hh i hocc => ?_⟩
  have hhne := marker_ne_nil ht hh
  have hle := occ_le_length hocc hhne
  have hmem : i + (marker W t h).length ∈ contextAnchors W t (marker W (t + 1) l) := by
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    exact Level.mem_markerEndCuts.mpr ⟨hle, h, hh, suffix_take_of_occ hocc⟩
  rw [hset, mem_insert, mem_singleton] at hmem
  rcases hmem with h1 | h1
  · left
    have hs1 : marker W t h <:+ (marker W (t + 1) l).take (marker W t m).length := by
      rw [← h1]; exact suffix_take_of_occ hocc
    rw [← List.prefix_iff_eq_take.mp hpre] at hs1
    have heq := marker_eq_of_suffix hh hm hs1 List.suffix_rfl
    have : (marker W t h).length = (marker W t m).length := by rw [heq]
    omega
  · right; exact h1

/-- Anchors of level `t + 1` are anchors of level `t`, in every context. -/
theorem contextAnchors_succ_subset (t : ℕ) (u : List α) :
    contextAnchors W (t + 1) u ⊆ contextAnchors W t u := by
  intro e he
  rw [mem_contextAnchors_succ] at he
  obtain ⟨hle, m, hm, hs⟩ := he
  rcases t with _ | t
  · have h1 : 1 ≤ (marker W (0 + 1) m).length :=
      List.length_pos_iff.mpr (marker_ne_nil le_rfl hm)
    have h2 := hs.length_le
    simp only [List.length_take] at h2
    simp only [contextAnchors, mem_Icc]
    omega
  · rw [mem_contextAnchors_succ]
    exact ⟨hle, m, active_succ_subset W _ hm, (marker_suffix_succ hm).trans hs⟩

theorem anchors_succ_subset (t : ℕ) (l : Fin k) :
    anchors W (t + 1) l ⊆ anchors W t l :=
  insert_subset_insert _ (contextAnchors_succ_subset t _)

/-- A coordinate that is not active at level `t + 1` is a single level-`t` block. -/
theorem anchors_eq_singleton {t : ℕ} (ht : 1 ≤ t) {l : Fin k}
    (hl : l ∉ active W (t + 1)) : anchors W t l = {(W l).length} := by
  induction t with
  | zero => omega
  | succ t ih =>
    apply le_antisymm _ (singleton_subset_iff.mpr (mem_insert_self _ _))
    by_cases hl' : l ∈ active W (t + 1)
    · intro e he
      rw [mem_singleton]
      by_contra hne'
      have hle : e ≤ (W l).length := by
        rcases mem_insert.mp he with rfl | he
        · exact le_rfl
        · rcases t with _ | t
          · exact (Level.mem_markerEndCuts.mp he).1
          · exact (Level.mem_markerEndCuts.mp he).1
      rcases t with _ | t
      · exact hl (Level.next_active.mpr ⟨hl', e, (mem_insert.mp he).resolve_left hne', by omega⟩)
      · exact hl ((mem_active_succ_succ W).mpr ⟨hl', e, he, by omega⟩)
    · rcases t with _ | t
      · intro e he
        have hnil : W l = [] := not_not.mp (fun h => hl' ((mem_active_one W).mpr h))
        rcases mem_insert.mp he with rfl | he
        · exact mem_singleton_self _
        · have := (Level.mem_markerEndCuts.mp he).1
          rw [hnil] at this ⊢
          exact mem_singleton.mpr (by simpa using this)
      · rw [← ih (by omega) hl']
        exact anchors_succ_subset _ l

end Antichain

section Locality

variable {W : Fin k → List α}

/-- An occurrence of an active level-`t` marker inside an occurrence of another one, in any
text, is the same occurrence of the same marker text. -/
theorem marker_occurrences_eq_of_nested {t : ℕ} {m m' : Fin k}
    (hm : m ∈ active W t) (hm' : m' ∈ active W t) {u : List α} {i j : ℕ}
    (h : marker W t m <+: u.drop i) (h' : marker W t m' <+: u.drop j) (hij : i ≤ j)
    (hlen : j + (marker W t m').length ≤ i + (marker W t m).length) :
    i = j ∧ marker W t m' = marker W t m := by
  have heq := marker_eq_of_infix t m' m hm' hm (infix_of_occ h h' hij hlen)
  have : (marker W t m').length = (marker W t m).length := by rw [heq]
  exact ⟨by omega, heq⟩

/-- Anchors of a text are anchors of every extension of it to the right. -/
theorem contextAnchors_append_left {t : ℕ} {u v : List α} {e : ℕ} (h : e ∈ contextAnchors W t u) :
    e ∈ contextAnchors W t (u ++ v) := by
  rcases t with _ | t
  · simp only [contextAnchors, mem_Icc, List.length_append] at h ⊢; omega
  · obtain ⟨he, m, hm, hs⟩ := (mem_contextAnchors_succ W).mp h
    refine (mem_contextAnchors_succ W).mpr ⟨by simp; omega, m, hm, ?_⟩
    rwa [List.take_append_of_le_length he]

/-- Anchors at cuts inside a prefix are anchors of that prefix. -/
theorem mem_contextAnchors_append_left {t : ℕ} {u v : List α} {e : ℕ} (he : e ≤ u.length) :
    e ∈ contextAnchors W t (u ++ v) ↔ e ∈ contextAnchors W t u := by
  refine ⟨fun h => ?_, contextAnchors_append_left⟩
  rcases t with _ | t
  · simp only [contextAnchors, mem_Icc, List.length_append] at h ⊢; omega
  · obtain ⟨-, m, hm, hs⟩ := (mem_contextAnchors_succ W).mp h
    rw [List.take_append_of_le_length he] at hs
    exact (mem_contextAnchors_succ W).mpr ⟨he, m, hm, hs⟩

/-- Anchors of a text are anchors of every extension of it to the left, shifted. -/
theorem contextAnchors_append_right {t : ℕ} {u v : List α} {e : ℕ} (h : e ∈ contextAnchors W t v) :
    u.length + e ∈ contextAnchors W t (u ++ v) := by
  rcases t with _ | t
  · simp only [contextAnchors, mem_Icc, List.length_append] at h ⊢; omega
  · obtain ⟨he, m, hm, hs⟩ := (mem_contextAnchors_succ W).mp h
    refine (mem_contextAnchors_succ W).mpr ⟨by simp; omega, m, hm, ?_⟩
    rw [List.take_length_add_append]
    exact hs.trans (List.suffix_append _ _)

/-- An anchor of `u ++ v` beyond `|u|` whose marker lies inside `v` is an anchor of `v`. -/
theorem contextAnchors_of_append_right {t : ℕ} (ht : 1 ≤ t) {u v : List α} {e : ℕ} {m : Fin k}
    (hm : m ∈ active W t) (hs : marker W t m <:+ (u ++ v).take (u.length + e))
    (he : e ≤ v.length) (hin : (marker W t m).length ≤ e) : e ∈ contextAnchors W t v := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  rw [List.take_length_add_append] at hs
  refine (mem_contextAnchors_succ W).mpr ⟨he, m, hm, ?_⟩
  exact List.suffix_of_suffix_length_le hs (List.suffix_append _ _) (by simp; omega)

end Locality

section Top

variable {W : Fin k → List α}

/-- `topLevel W` is the least `t` with no active coordinate at level `t + 1`. -/
theorem topLevel_spec :
    active W (topLevel W + 1) = ∅ ∧ ∀ t < topLevel W, active W (t + 1) ≠ ∅ := by
  refine ⟨?_, fun t ht h => ?_⟩
  · rcases Nat.find_spec
      (⟨totalLength W, Or.inr le_rfl⟩ : ∃ t, active W (t + 1) = ∅ ∨ totalLength W ≤ t)
      with h | h
    · exact h
    · exact active_eq_empty_of_totalLength_lt (by unfold topLevel; omega)
  · exact Nat.find_min _ ht (Or.inl h)

theorem active_nonempty_of_le_topLevel {t : ℕ} (ht : 1 ≤ t) (h : t ≤ topLevel W) :
    (active W t).Nonempty := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact nonempty_iff_ne_empty.mpr (topLevel_spec.2 t (by omega))

end Top

/-! ## Fresh tuples: the number of levels and of anchors -/

section Fresh

open DeciSigma1.Readers.Table

variable {S : Type} [Fintype S] [DecidableEq S]

/-- Start positions `b < |W j|` whose (nonempty) suffix of `W j` is a prefix of `z`. -/
def suffixOccurrenceCuts (W : Fin k → List α) (j : Fin k) (z : List α) : Finset ℕ :=
  (range (W j).length).filter (fun b => (W j).drop b <+: z)

theorem mem_suffixOccurrenceCuts {W : Fin k → List α} {j : Fin k} {z : List α} {b : ℕ} :
    b ∈ suffixOccurrenceCuts W j z ↔ b < (W j).length ∧ (W j).drop b <+: z := by
  simp [suffixOccurrenceCuts]

/-- A fixed text has at most `N - 1` nonempty suffixes of a fresh word as prefixes: their
starting cuts carry distinct live states. -/
theorem card_prefixComparingCuts_le {T : Table α S k} {W : Fin k → List α} {j : Fin k}
    (hj : T.Fresh W j)
    (txt : List α) :
    ((range (W j).length).filter (fun b => (W j).drop b <+: txt)).card ≤ Fintype.card S - 1 := by
  have hfr := fresh_iff.mp hj
  have key : ∀ b d, b ∈ suffixOccurrenceCuts W j txt → d ∈ suffixOccurrenceCuts W j txt → b < d →
      T.runPrefix W j b ≠ T.runPrefix W j d := by
    intro b d hb hd hlt hq
    rw [mem_suffixOccurrenceCuts] at hb hd
    have hpre : (W j).drop d <+: (W j).drop b :=
      List.prefix_of_prefix_length_le hd.2 hb.2 (by simp only [List.length_drop]; omega)
    have hrun : T.runPrefix W j (b + ((W j).length - d)) = T.endState W j := by
      rw [runPrefix_add, show (W j).length - d = ((W j).drop d).length by simp,
        ← List.prefix_iff_eq_take.mp hpre, hq, runFrom_runPrefix_drop]
    exact hfr _ (by omega) hrun
  have hinj : Set.InjOn (T.runPrefix W j) (suffixOccurrenceCuts W j txt) := by
    intro b hb d hd hq
    by_contra hbd
    rcases Nat.lt_or_gt_of_ne hbd with hlt | hlt
    · exact key b d hb hd hlt hq
    · exact key d b hd hb hlt hq.symm
  have hmaps : (suffixOccurrenceCuts W j txt).image (T.runPrefix W j) ⊆
      univ.erase (T.endState W j) := by
    intro q hq
    obtain ⟨b, hb, rfl⟩ := mem_image.mp hq
    exact mem_erase.mpr ⟨hfr b (mem_suffixOccurrenceCuts.mp hb).1, mem_univ _⟩
  calc (suffixOccurrenceCuts W j txt).card =
      ((suffixOccurrenceCuts W j txt).image (T.runPrefix W j)).card :=
        (card_image_of_injOn hinj).symm
    _ ≤ (univ.erase (T.endState W j)).card := card_le_card hmaps
    _ = Fintype.card S - 1 := by rw [card_erase_of_mem (mem_univ _), card_univ]

theorem card_suffixOccurrenceCuts_le {T : Table α S k} {W : Fin k → List α} (hfr : ∀ i, T.Fresh W i)
    (j : Fin k) (z : List α) : (suffixOccurrenceCuts W j z).card ≤ Fintype.card S - 1 :=
  card_prefixComparingCuts_le (hfr j) z

/-- A family of positions, each read as a nonempty suffix of a coordinate word that is a
prefix of `z`, has at most `k (N - 1)` members. -/
theorem card_le_of_subset_biUnion {T : Table α S k} {W : Fin k → List α}
    (hfr : ∀ i, T.Fresh W i) (z : List α) (f : Fin k → ℕ → ℕ) {P : Finset ℕ}
    (hP : P ⊆ univ.biUnion (fun j => (suffixOccurrenceCuts W j z).image (f j))) :
    P.card ≤ k * (Fintype.card S - 1) := by
  calc P.card ≤ (univ.biUnion (fun j => (suffixOccurrenceCuts W j z).image (f j))).card :=
      card_le_card hP
    _ ≤ ∑ j, ((suffixOccurrenceCuts W j z).image (f j)).card := card_biUnion_le
    _ ≤ ∑ _j : Fin k, (Fintype.card S - 1) :=
        sum_le_sum (fun j _ => card_image_le.trans (card_suffixOccurrenceCuts_le hfr j z))
    _ = k * (Fintype.card S - 1) := by simp

/-! ## The number of levels -/

/-- Prefix lengths `p ≥ 1` of `z` whose prefix is a suffix of some coordinate word. -/
def prefixOccurrenceCuts (W : Fin k → List α) (z : List α) : Finset ℕ :=
  (Icc 1 z.length).filter (fun p => ∃ j, z.take p <:+ W j)

theorem card_prefixOccurrenceCuts_le {T : Table α S k} {W : Fin k → List α} (hfr : ∀ i, T.Fresh W i)
    (z : List α) : (prefixOccurrenceCuts W z).card ≤ k * (Fintype.card S - 1) := by
  refine card_le_of_subset_biUnion hfr z (fun j b => (W j).length - b) ?_
  intro p hp
  simp only [prefixOccurrenceCuts, mem_filter, mem_Icc] at hp
  obtain ⟨⟨hp1, hp2⟩, j, hj⟩ := hp
  have hlen : (z.take p).length = p := by simp; omega
  have hpj : p ≤ (W j).length := hlen ▸ hj.length_le
  have hdrop : (W j).drop ((W j).length - p) = z.take p := by
    rw [List.suffix_iff_eq_drop.mp hj, hlen]
  simp only [mem_biUnion, mem_univ, true_and, mem_image]
  refine ⟨j, (W j).length - p, mem_suffixOccurrenceCuts.mpr ⟨by omega, ?_⟩, by omega⟩
  rw [hdrop]; exact List.take_prefix _ _

theorem le_card_prefixOccurrenceCuts {W : Fin k → List α} {t : ℕ} (ht : 1 ≤ t) :
    ∀ l ∈ active W t, t ≤ (prefixOccurrenceCuts W (marker W t l)).card := by
  induction t, ht using Nat.le_induction with
  | base =>
    intro l hl
    have hlen : (marker W 1 l).length = 1 := length_marker_one hl
    have h1 : 1 ∈ prefixOccurrenceCuts W (marker W 1 l) := by
      simp only [prefixOccurrenceCuts, mem_filter, mem_Icc, hlen]
      refine ⟨⟨le_rfl, le_rfl⟩, l, ?_⟩
      rw [List.take_of_length_le (by omega)]
      exact marker_suffix W 1 l
    exact card_pos.mpr ⟨1, h1⟩
  | succ t ht ih =>
    intro l hl
    obtain ⟨m, hm, hpre, hlt, -⟩ := contextAnchors_marker_succ ht hl
    have hsub : insert (marker W (t + 1) l).length (prefixOccurrenceCuts W (marker W t m)) ⊆
        prefixOccurrenceCuts W (marker W (t + 1) l) := by
      intro p hp
      simp only [prefixOccurrenceCuts, mem_insert, mem_filter, mem_Icc] at hp ⊢
      rcases hp with rfl | ⟨⟨hp1, hp2⟩, j, hj⟩
      · refine ⟨⟨by omega, le_rfl⟩, l, ?_⟩
        rw [List.take_length]; exact marker_suffix W (t + 1) l
      · refine ⟨⟨hp1, by omega⟩, j, ?_⟩
        rw [List.prefix_iff_eq_take.mp hpre, List.take_take, Nat.min_eq_left hp2] at hj
        exact hj
    have hnot : (marker W (t + 1) l).length ∉ prefixOccurrenceCuts W (marker W t m) := by
      simp only [prefixOccurrenceCuts, mem_filter, mem_Icc]; omega
    have := card_le_card hsub
    rw [card_insert_of_notMem hnot] at this
    have := ih m hm
    omega

/-- The hierarchy of a fresh tuple has at most `k (N - 1)` levels. -/
theorem topLevel_le {T : Table α S k} {W : Fin k → List α} (hfr : ∀ i, T.Fresh W i) :
    topLevel W ≤ k * (Fintype.card S - 1) := by
  rcases Nat.eq_zero_or_pos (topLevel W) with h0 | hpos
  · omega
  · obtain ⟨l, hl⟩ := active_nonempty_of_le_topLevel (W := W) hpos le_rfl
    exact (le_card_prefixOccurrenceCuts hpos l hl).trans (card_prefixOccurrenceCuts_le hfr _)

/-! ## Anchors inside a marker of the next level -/

/-- In a fresh tuple, an occurrence of a marker of level `t + 1` in any text has at most
`k (N - 1) + 1` anchors of level `t` strictly inside. -/
theorem card_anchors_inside_marker_le {T : Table α S k} {W : Fin k → List α}
    (hfr : ∀ i, T.Fresh W i) (t : ℕ) {l : Fin k} (hl : l ∈ active W (t + 1))
    (ctx : List α) {a : ℕ} (hocc : marker W (t + 1) l <+: ctx.drop a) :
    ((contextAnchors W t ctx).filter
        (fun p => a < p ∧ p < a + (marker W (t + 1) l).length)).card ≤
      k * (Fintype.card S - 1) + 1 := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have hlen : (marker W (0 + 1) l).length = 1 := length_marker_one hl
    rw [hlen, filter_false_of_mem (fun p _ => by omega), card_empty]
    exact Nat.zero_le _
  obtain ⟨m, hm, hpre, hlt, hset⟩ := contextAnchors_marker_succ ht hl
  set σ := marker W (t + 1) l with hσ
  have hsub : (contextAnchors W t ctx).filter (fun p => a < p ∧ p < a + σ.length) ⊆
      insert (a + (marker W t m).length)
        (univ.biUnion (fun j => (suffixOccurrenceCuts W j σ).image (fun b => a +
            ((W j).length - b)))) := by
    intro p hp
    rw [mem_filter] at hp
    obtain ⟨hpa, hap, hpσ⟩ := hp
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    obtain ⟨hpc, h, hh, hsuf⟩ := (mem_contextAnchors_succ W).mp hpa
    have hσle := occ_le_length hocc (marker_ne_nil (by omega) hl)
    have htake : ctx.take p = ctx.take a ++ σ.take (p - a) := by
      have h1 : (ctx.drop a).take (p - a) = σ.take (p - a) := by
        rw [List.prefix_iff_eq_take.mp hocc, List.take_take, Nat.min_eq_left (by omega)]
      rw [← h1, ← List.take_add, Nat.add_sub_cancel' hap.le]
    have hlenp : (σ.take (p - a)).length = p - a := by simp; omega
    rw [htake] at hsuf
    rcases le_or_gt (marker W (t' + 1) h).length (p - a) with hle | hgt
    · -- the marker lies inside the occurrence
      have hin : marker W (t' + 1) h <:+ σ.take (p - a) :=
        List.suffix_of_suffix_length_le hsuf (List.suffix_append _ _) (by omega)
      have hmem : p - a ∈ contextAnchors W (t' + 1) σ :=
        (mem_contextAnchors_succ W).mpr ⟨by omega, h, hh, hin⟩
      rw [hset, mem_insert, mem_singleton] at hmem
      rcases hmem with h1 | h1
      · exact mem_insert.mpr (Or.inl (by omega))
      · omega
    · -- the marker sticks out of the left end of the occurrence
      have hout : σ.take (p - a) <:+ marker W (t' + 1) h :=
        List.suffix_of_suffix_length_le (List.suffix_append _ _) hsuf (by omega)
      have hw : σ.take (p - a) <:+ W h := hout.trans (marker_suffix W _ h)
      have hpw : p - a ≤ (W h).length := hlenp ▸ hw.length_le
      have hdrop : (W h).drop ((W h).length - (p - a)) = σ.take (p - a) := by
        rw [List.suffix_iff_eq_drop.mp hw, hlenp]
      refine mem_insert_of_mem ?_
      simp only [mem_biUnion, mem_univ, true_and, mem_image]
      refine ⟨h, (W h).length - (p - a), mem_suffixOccurrenceCuts.mpr ⟨by omega, ?_⟩, by omega⟩
      rw [hdrop]; exact List.take_prefix _ _
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (univ.biUnion (fun j => (suffixOccurrenceCuts W j σ).image (fun b => a +
        ((W j).length - b)))).card + 1 :=
        card_insert_le _ _
    _ ≤ k * (Fintype.card S - 1) + 1 := by
        have := card_le_of_subset_biUnion hfr σ (fun j b => a + ((W j).length - b))
          (subset_refl _)
        omega

/-- The same bound counting the right end: at most `k (N - 1) + 2` anchors of level `t` in the
half-open window `(a, a + |σ|]` of an occurrence of `σ` at `a`. -/
theorem card_anchors_Ioc_marker_le {T : Table α S k} {W : Fin k → List α}
    (hfr : ∀ i, T.Fresh W i) (t : ℕ) {l : Fin k} (hl : l ∈ active W (t + 1))
    (ctx : List α) {a : ℕ} (hocc : marker W (t + 1) l <+: ctx.drop a) :
    ((contextAnchors W t ctx).filter
        (fun p => a < p ∧ p ≤ a + (marker W (t + 1) l).length)).card ≤
      k * (Fintype.card S - 1) + 2 := by
  have hsub : (contextAnchors W t ctx).filter
        (fun p => a < p ∧ p ≤ a + (marker W (t + 1) l).length) ⊆
      insert (a + (marker W (t + 1) l).length) ((contextAnchors W t ctx).filter
        (fun p => a < p ∧ p < a + (marker W (t + 1) l).length)) := by
    intro p hp
    rw [mem_filter] at hp
    rw [mem_insert, mem_filter]
    rcases lt_or_eq_of_le hp.2.2 with h | h
    · exact Or.inr ⟨hp.1, hp.2.1, h⟩
    · exact Or.inl h
  have := card_anchors_inside_marker_le hfr t hl ctx hocc
  have := card_le_card hsub
  have := card_insert_le (a + (marker W (t + 1) l).length) ((contextAnchors W t ctx).filter
        (fun p => a < p ∧ p < a + (marker W (t + 1) l).length))
  omega

end Fresh

end DeciSigma1.Holes.Fresh
