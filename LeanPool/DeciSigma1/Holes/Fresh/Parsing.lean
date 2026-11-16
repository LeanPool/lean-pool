/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Fresh.Hierarchy
import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Pow
public import Mathlib.Algebra.GroupWithZero.Nat

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Parses of blocks and the reverse trie

Fix a level `t ≥ 1` of the marker hierarchy of a tuple `W`. The anchors of level `t + 1` cut
each nonempty word into *upper blocks*, and the anchors of level `t` cut every upper block into
*lower blocks*; an empty word has no blocks. An upper occurrence `(l, s, e)` is the upper block
of word `l` between the cuts `s` and `e` (`upperOccurrences`). Its parse is the list of its
lower blocks (`upperParse`), and `depthCut` is the cut that lies `d` lower blocks to the left
of its end.

The parses of all upper occurrences, read from the right, form a trie. An `Edge` of this trie
joins two consecutive nodes `a < b` on the path of one parse. The upper occurrences that
traverse the edge (`Edge.TraversedBy`) are those whose parses end with the same `b` lower blocks;
the deletion of `Holes.Fresh.Deletion` removes one stretch of these blocks from all of them at
once.

Parsing is local (`relativeAnchors_eq`): in any left context, the lower anchors of a text `z`
are the anchors of `z` alone together with the ends of markers that start to the left of `z`.
The anchors of `z` alone lie after all such ends (`not_inside_le_crossBoundaryMarkerEnds`), and
the ends lie in a set of at most `k (N - 1)` cuts that does not depend on the context
(`crossBoundaryMarkerEnds_subset_prefixOccurrenceCuts`).

## Main declarations

- `commonPrefixLength`, `commonSuffixLength`: longest common prefixes and suffixes of lists.
- `depthCutAt`, `anchorCount`: cuts read from the right end of a parse.
- `upperOccurrences`, `upperParse`, `upperParses`, `depthCut`: upper blocks and their parses.
- `trieNodes`, `Edge`, `Edge.TraversedBy`: the reverse trie of parses and its edges.
- `relativeAnchors`, `crossBoundaryMarkerEnds`, `relativeAnchors_eq`: anchors of a text in a
  context.
-/

@[expose] public section


namespace DeciSigma1.Holes.Fresh

open Finset

/-! ## Longest common prefix and suffix of lists -/

section Lcp

variable {β : Type} [DecidableEq β]

/-- The length of the longest common prefix. -/
def commonPrefixLength : List β → List β → ℕ
  | a :: A, b :: B => if a = b then commonPrefixLength A B + 1 else 0
  | _, _ => 0

theorem le_commonPrefixLength_iff {A B : List β} {d : ℕ} :
    d ≤ commonPrefixLength A B ↔ d ≤ A.length ∧ d ≤ B.length ∧ A.take d = B.take d := by
  induction A generalizing B d with
  | nil => cases d <;> simp [commonPrefixLength]
  | cons a A ih =>
    cases B with
    | nil => cases d <;> simp [commonPrefixLength]
    | cons b B =>
      cases d with
      | zero => simp
      | succ d =>
        simp only [commonPrefixLength]
        split_ifs with hab
        · subst hab
          simp only [List.length_cons, List.take_succ_cons, List.cons.injEq, true_and,
            Nat.add_le_add_iff_right]
          exact ih
        · simp [hab]

theorem commonPrefixLength_le_left (A B : List β) :
    commonPrefixLength A B ≤ A.length := (le_commonPrefixLength_iff.mp le_rfl).1

theorem commonPrefixLength_le_right (A B : List β) :
    commonPrefixLength A B ≤ B.length := (le_commonPrefixLength_iff.mp le_rfl).2.1

theorem take_commonPrefixLength (A B : List β) :
    A.take (commonPrefixLength A B) = B.take (commonPrefixLength A B) :=
  (le_commonPrefixLength_iff.mp le_rfl).2.2

theorem commonPrefixLength_comm (A B : List β) : commonPrefixLength A B = commonPrefixLength B A :=
  le_antisymm
    (le_commonPrefixLength_iff.mpr ⟨commonPrefixLength_le_right A B, commonPrefixLength_le_left A B,
        (take_commonPrefixLength A B).symm⟩)
    (le_commonPrefixLength_iff.mpr ⟨commonPrefixLength_le_right B A, commonPrefixLength_le_left B A,
        (take_commonPrefixLength B A).symm⟩)

theorem commonPrefixLength_self (A : List β) : commonPrefixLength A A = A.length :=
  le_antisymm (commonPrefixLength_le_left A A) (le_commonPrefixLength_iff.mpr ⟨le_rfl, le_rfl, rfl⟩)

/-- Ultrametric inequality for common prefixes. -/
theorem min_le_commonPrefixLength (A B C : List β) :
    min (commonPrefixLength A B) (commonPrefixLength B C) ≤ commonPrefixLength A C := by
  obtain ⟨h1, h2, h3⟩ :=
      le_commonPrefixLength_iff.mp (min_le_left (commonPrefixLength A B) (commonPrefixLength B C))
  obtain ⟨h4, h5, h6⟩ :=
      le_commonPrefixLength_iff.mp (min_le_right (commonPrefixLength A B) (commonPrefixLength B C))
  exact le_commonPrefixLength_iff.mpr ⟨h1, h5, h3.trans h6⟩

/-- The length of the longest common suffix, counted in list entries. -/
def commonSuffixLength (Z Y : List β) : ℕ := commonPrefixLength Z.reverse Y.reverse

theorem commonSuffixLength_comm (Z Y : List β) :
    commonSuffixLength Z Y = commonSuffixLength Y Z := commonPrefixLength_comm _ _

theorem commonSuffixLength_le_left (Z Y : List β) : commonSuffixLength Z Y ≤ Z.length := by
  unfold commonSuffixLength; simpa using commonPrefixLength_le_left Z.reverse Y.reverse

theorem commonSuffixLength_self (Z : List β) :
    commonSuffixLength Z Z = Z.length := by simp [commonSuffixLength, commonPrefixLength_self]

theorem min_le_commonSuffixLength (A B C : List β) :
    min (commonSuffixLength A B) (commonSuffixLength B C) ≤ commonSuffixLength A C :=
  min_le_commonPrefixLength _ _ _

end Lcp

/-! ## Cuts read from the right -/

section Cuts

/-- The largest element of `A` below `p` (`0` if there is none). -/
def previousAnchor (A : Finset ℕ) (p : ℕ) : ℕ := (A.filter (· < p)).sup id

/-- Cuts of a parse read from its right end `e`: `depthCutAt A e 0 = e`, then previous anchors. -/
def depthCutAt (A : Finset ℕ) (e : ℕ) : ℕ → ℕ
  | 0 => e
  | d + 1 => previousAnchor A (depthCutAt A e d)

/-- The number of elements of `A` in `(s, e]`. -/
def anchorCount (A : Finset ℕ) (s e : ℕ) : ℕ := (A.filter (fun p => s < p ∧ p ≤ e)).card

variable {A : Finset ℕ}

theorem le_previousAnchor {p q : ℕ} (hq : q ∈ A) (hqp : q < p) : q ≤ previousAnchor A p :=
  le_sup (f := id) (mem_filter.mpr ⟨hq, hqp⟩)

theorem previousAnchor_le {p s : ℕ} (h : ∀ q ∈ A, q < p → q ≤ s) : previousAnchor A p ≤ s :=
  Finset.sup_le fun q hq => h q (mem_filter.mp hq).1 (mem_filter.mp hq).2

theorem previousAnchor_spec {p : ℕ} (h : ∃ q ∈ A, q < p) :
    previousAnchor A p ∈ A ∧ previousAnchor A p < p := by
  have hne : (A.filter (· < p)).Nonempty := by
    obtain ⟨q, hq, hqp⟩ := h; exact ⟨q, mem_filter.mpr ⟨hq, hqp⟩⟩
  obtain ⟨q, hq, hsup⟩ := exists_mem_eq_sup _ hne id
  rw [mem_filter] at hq
  simp only [previousAnchor, hsup, id]
  exact hq

theorem anchorCount_split {s p e : ℕ} (h1 : s ≤ p) (h2 : p ≤ e) :
    anchorCount A s e = anchorCount A s p + anchorCount A p e := by
  unfold anchorCount
  rw [← card_union_of_disjoint]
  · congr 1
    ext q
    by_cases hq : q ∈ A
    · simp only [mem_filter, mem_union, hq, true_and]; omega
    · simp [hq]
  · rw [disjoint_left]
    intro q hq hq'
    simp only [mem_filter] at hq hq'
    omega

theorem anchorCount_anti {p q e : ℕ} (h : q ≤ p) : anchorCount A p e ≤ anchorCount A q e :=
  card_le_card fun r hr => by
    simp only [mem_filter] at hr ⊢; exact ⟨hr.1, by omega, hr.2.2⟩

theorem anchorCount_self (s : ℕ) : anchorCount A s s = 0 := by
  unfold anchorCount
  rw [card_eq_zero, filter_eq_empty_iff]
  intro q _; omega

/-- The cuts read from the right enumerate the elements of `A` in `(s, e]`, then reach `s`. -/
theorem depthCutAt_spec {s e : ℕ} (hse : s < e) (he : e ∈ A) (hs : s = 0 ∨ s ∈ A) :
    (∀ d < anchorCount A s e, depthCutAt A e d ∈ A ∧ s < depthCutAt A e d ∧ depthCutAt A e d ≤ e ∧
      anchorCount A (depthCutAt A e d) e = d) ∧ depthCutAt A e (anchorCount A s e) = s := by
  have hn : 1 ≤ anchorCount A s e := card_pos.mpr ⟨e, mem_filter.mpr ⟨he, hse, le_rfl⟩⟩
  have main : ∀ d < anchorCount A s e, depthCutAt A e d ∈ A ∧ s < depthCutAt A e d ∧
      depthCutAt A e d ≤ e ∧
      anchorCount A (depthCutAt A e d) e = d := by
    intro d
    induction d with
    | zero => intro _; exact ⟨he, hse, le_rfl, anchorCount_self e⟩
    | succ d ih =>
      intro hd
      obtain ⟨hpA, hsp, hpe, hcnt⟩ := ih (by omega)
      set p := depthCutAt A e d with hp
      have hsplit := anchorCount_split (A := A) hsp.le hpe
      have hsp2 : 2 ≤ anchorCount A s p := by omega
      -- an element of `A` strictly between `s` and `p`
      have hex : ∃ q ∈ A, s < q ∧ q < p := by
        by_contra hno
        simp only [not_exists, not_and, not_lt] at hno
        have : anchorCount A s p ≤ 1 := by
          unfold anchorCount
          rw [card_le_one]
          intro a ha b hb
          simp only [mem_filter] at ha hb
          have ha' : a = p := by
            by_contra hne; exact absurd (hno a ha.1 ha.2.1) (by omega)
          have hb' : b = p := by
            by_contra hne; exact absurd (hno b hb.1 hb.2.1) (by omega)
          rw [ha', hb']
        omega
      obtain ⟨q, hqA, hsq, hqp⟩ := hex
      obtain ⟨hprA, hprp⟩ := previousAnchor_spec ⟨q, hqA, hqp⟩
      have hqpr := le_previousAnchor hqA hqp
      change previousAnchor A p ∈ A ∧ s < previousAnchor A p ∧ previousAnchor A p ≤ e ∧
          anchorCount A (previousAnchor A p) e = d + 1
      refine ⟨hprA, by omega, by omega, ?_⟩
      rw [anchorCount_split (A := A) hprp.le hpe, hcnt]
      have : anchorCount A (previousAnchor A p) p = 1 := by
        unfold anchorCount
        rw [card_eq_one]
        refine ⟨p, ?_⟩
        ext r
        simp only [mem_filter, mem_singleton]
        constructor
        · rintro ⟨hr, h1, h2⟩
          by_contra hne
          have := le_previousAnchor hr (show r < p by omega)
          omega
        · rintro rfl; exact ⟨hpA, hprp, le_rfl⟩
      omega
  refine ⟨main, ?_⟩
  obtain ⟨n, hn'⟩ : ∃ n, anchorCount A s e = n + 1 := ⟨anchorCount A s e - 1, by omega⟩
  rw [hn']
  obtain ⟨hpA, hsp, hpe, hcnt⟩ := main n (by omega)
  change previousAnchor A (depthCutAt A e n) = s
  have hsplit := anchorCount_split (A := A) hsp.le hpe
  have h1 : anchorCount A s (depthCutAt A e n) = 1 := by omega
  have hno : ∀ q ∈ A, q < depthCutAt A e n → q ≤ s := by
    intro q hq hqp
    by_contra hqs
    have : 2 ≤ anchorCount A s (depthCutAt A e n) := by
      unfold anchorCount
      have hsub : ({q, depthCutAt A e n} : Finset ℕ) ⊆
          A.filter (fun p => s < p ∧ p ≤ depthCutAt A e n) := by
        intro r hr
        simp only [mem_insert, mem_singleton] at hr
        rcases hr with rfl | rfl
        · exact mem_filter.mpr ⟨hq, by omega, hqp.le⟩
        · exact mem_filter.mpr ⟨hpA, hsp, le_rfl⟩
      have := card_le_card hsub
      rw [card_pair (by omega)] at this
      exact this
    omega
  apply le_antisymm (previousAnchor_le hno)
  rcases hs with hs0 | hsA
  · omega
  · exact le_previousAnchor hsA hsp

end Cuts

/-! ## Upper occurrences and their parses -/

section Upper

variable {α : Type} [DecidableEq α] {k : ℕ}

/-- A context anchor is a cut of its text. -/
theorem contextAnchors_le_length {W : Fin k → List α} {t : ℕ} {u : List α} {e : ℕ}
    (h : e ∈ contextAnchors W t u) : e ≤ u.length := by
  rcases t with _ | t
  · simp only [contextAnchors, mem_Icc] at h; omega
  · exact ((mem_contextAnchors_succ W).mp h).1

/-- No context anchor lies at the cut `0`. -/
theorem contextAnchors_pos {W : Fin k → List α} {t : ℕ} {u : List α} {e : ℕ}
    (h : e ∈ contextAnchors W t u) : 1 ≤ e := by
  rcases t with _ | t
  · simp only [contextAnchors, mem_Icc] at h; omega
  · obtain ⟨-, m, hm, hs⟩ := (mem_contextAnchors_succ W).mp h
    have h1 := List.length_pos_iff.mpr (marker_ne_nil (by omega) hm)
    have h2 := hs.length_le
    simp only [List.length_take] at h2
    omega

/-- Anchors of a coordinate are cuts of its word. -/
theorem le_length_of_mem_anchors {W : Fin k → List α} {t : ℕ} {l : Fin k} {p : ℕ}
    (hp : p ∈ anchors W t l) : p ≤ (W l).length := by
  rcases mem_insert.mp hp with rfl | hp
  · exact le_rfl
  · exact contextAnchors_le_length hp

/-- The anchors of a nonempty word are cuts `1 ≤ p ≤ |W l|`. -/
theorem anchors_bounds {W : Fin k → List α} {t : ℕ} {l : Fin k} (hl : W l ≠ []) {p : ℕ}
    (hp : p ∈ anchors W t l) : 1 ≤ p ∧ p ≤ (W l).length := by
  refine ⟨?_, le_length_of_mem_anchors hp⟩
  rcases mem_insert.mp hp with rfl | hp
  · exact List.length_pos_iff.mpr hl
  · exact contextAnchors_pos hp

/-- The start of the upper (level-`t + 1`) block of word `l` that ends at the upper anchor `e`. -/
def upperOccurrenceStart (W : Fin k → List α) (t : ℕ) (l : Fin k) (e : ℕ) : ℕ :=
  previousAnchor (anchors W (t + 1) l) e

/-- The upper occurrences `(l, s, e)`: the upper (level-`t + 1`) blocks of all nonempty words.
An empty word has no blocks. -/
def upperOccurrences (W : Fin k → List α) (t : ℕ) : Finset (Fin k × ℕ × ℕ) :=
  (univ.filter fun l => W l ≠ []).biUnion fun l =>
    (anchors W (t + 1) l).image fun e => (l, upperOccurrenceStart W t l e, e)

theorem mem_upperOcc {W : Fin k → List α} {t : ℕ} {o : Fin k × ℕ × ℕ} :
    o ∈ upperOccurrences W t ↔ W o.1 ≠ [] ∧ o.2.2 ∈ anchors W (t + 1) o.1 ∧ o.2.1 =
        upperOccurrenceStart W t o.1 o.2.2 := by
  obtain ⟨l, s, e⟩ := o
  simp only [upperOccurrences, mem_biUnion, mem_filter, mem_univ, true_and, mem_image,
    Prod.mk.injEq]
  constructor
  · rintro ⟨l', hl', e', he', rfl, rfl, rfl⟩; exact ⟨hl', he', rfl⟩
  · rintro ⟨hl, he, rfl⟩; exact ⟨l, hl, e, he, rfl, rfl, rfl⟩

/-- The word of an upper occurrence is nonempty. -/
theorem ne_nil_of_mem_upperOccurrences {W : Fin k → List α} {t : ℕ} {o : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) : W o.1 ≠ [] := (mem_upperOcc.mp ho).1

/-- The number of lower (level-`t`) blocks of an upper occurrence. -/
def lowerBlockCount (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) : ℕ :=
  anchorCount (anchors W t o.1) o.2.1 o.2.2

/-- The cut at depth `d` of an upper occurrence: `d` lower blocks to the left of its end. -/
def depthCut (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) (d : ℕ) : ℕ :=
  depthCutAt (anchors W t o.1) o.2.2 d

/-- The level-`t` parse of an upper occurrence, read from the right. -/
def reversedBlocks (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) : List (List α) :=
  (List.range (lowerBlockCount W t o)).map fun d =>
    ((W o.1).drop (depthCut W t o (d + 1))).take (depthCut W t o d - depthCut W t o (d + 1))

/-- The level-`t` parse of an upper occurrence: the list of its lower blocks. -/
def upperParse (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) : List (List α) :=
  (reversedBlocks W t o).reverse

/-- The parses of all upper occurrences. -/
def upperParses (W : Fin k → List α) (t : ℕ) : Finset (List (List α)) :=
  (upperOccurrences W t).image (upperParse W t)

/-- Basic facts on an upper occurrence `(l, s, e)`: `s < e ≤ |W l|`, `e` is a lower anchor,
`s` is `0` or a lower anchor, and no upper anchor lies strictly between `s` and `e`. -/
theorem upperOcc_spec {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) :
    o.2.1 < o.2.2 ∧ o.2.2 ≤ (W o.1).length ∧ o.2.2 ∈ anchors W t o.1 ∧
      (o.2.1 = 0 ∨ o.2.1 ∈ anchors W t o.1) ∧
      ∀ p ∈ anchors W (t + 1) o.1, ¬ (o.2.1 < p ∧ p < o.2.2) := by
  obtain ⟨hl, he, hs⟩ := mem_upperOcc.mp ho
  obtain ⟨he1, he2⟩ := anchors_bounds hl he
  have hsub := anchors_succ_subset (W := W) t o.1
  rw [hs]
  refine ⟨?_, he2, hsub he, ?_, ?_⟩
  · by_cases hex : ∃ q ∈ anchors W (t + 1) o.1, q < o.2.2
    · exact (previousAnchor_spec hex).2
    · have : upperOccurrenceStart W t o.1 o.2.2 ≤ 0 :=
        previousAnchor_le (fun q hq hqe => absurd ⟨q, hq, hqe⟩ hex)
      omega
  · by_cases hex : ∃ q ∈ anchors W (t + 1) o.1, q < o.2.2
    · exact Or.inr (hsub (previousAnchor_spec hex).1)
    · left
      have : upperOccurrenceStart W t o.1 o.2.2 ≤ 0 :=
          previousAnchor_le (fun q hq hqe => absurd ⟨q, hq, hqe⟩ hex)
      omega
  · rintro p hp ⟨h1, h2⟩
    have := le_previousAnchor hp h2
    unfold upperOccurrenceStart at h1
    omega

/-- The depth cuts of an upper occurrence enumerate its lower anchors. -/
theorem depthCut_spec {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) :
    (∀ d < lowerBlockCount W t o, depthCut W t o d ∈ anchors W t o.1 ∧ o.2.1 < depthCut W t o d ∧
      depthCut W t o d ≤ o.2.2 ∧ anchorCount (anchors W t o.1) (depthCut W t o d) o.2.2 = d) ∧
      depthCut W t o (lowerBlockCount W t o) = o.2.1 := by
  obtain ⟨hse, -, he, hs, -⟩ := upperOcc_spec ho
  exact depthCutAt_spec hse he hs

theorem depthCut_lt {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d : ℕ} (hd : d < lowerBlockCount W t o) :
    depthCut W t o (d + 1) < depthCut W t o d := by
  obtain ⟨hall, hlast⟩ := depthCut_spec ho
  obtain ⟨-, hs, -, hcnt⟩ := hall d hd
  by_cases h : d + 1 < lowerBlockCount W t o
  · obtain ⟨-, -, -, hcnt'⟩ := hall (d + 1) h
    by_contra hge
    have := anchorCount_anti (A := anchors W t o.1) (e := o.2.2) (not_lt.mp hge)
    omega
  · have hd' : d + 1 = lowerBlockCount W t o := by omega
    rw [hd', hlast]
    exact hs

@[simp] theorem length_reversedBlocks (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) :
    (reversedBlocks W t o).length = lowerBlockCount W t o := by simp [reversedBlocks]

@[simp] theorem length_upperSeq (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) :
    (upperParse W t o).length = lowerBlockCount W t o := by simp [upperParse]

theorem getElem_reversedBlocks (W : Fin k → List α) (t : ℕ) (o : Fin k × ℕ × ℕ) {d : ℕ}
    (hd : d < (reversedBlocks W t o).length) :
    (reversedBlocks W t o)[d] =
      ((W o.1).drop (depthCut W t o (d + 1))).take (depthCut W t o d - depthCut W t o (d + 1)) := by
  simp [reversedBlocks]

theorem length_getElem_reversedBlocks {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d : ℕ}
        (hd : d < (reversedBlocks W t o).length) :
    (reversedBlocks W t o)[d].length = depthCut W t o d - depthCut W t o (d + 1) := by
  rw [getElem_reversedBlocks]
  rw [length_reversedBlocks] at hd
  have h1 := ((depthCut_spec ho).1 d hd).2.2.1
  have h2 := (upperOcc_spec ho).2.1
  have h3 := depthCut_lt ho hd
  simp only [List.length_take, List.length_drop]
  omega

theorem depthCut_lt_of_lt {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d d' : ℕ} (hdd : d < d')
    (hd' : d' ≤ lowerBlockCount W t o) : depthCut W t o d' < depthCut W t o d := by
  induction d', hdd using Nat.le_induction with
  | base => exact depthCut_lt ho (by omega)
  | succ d' hdd ih =>
    exact (depthCut_lt ho (by omega)).trans (ih (by omega))

/-- An upper occurrence is determined by its word and its end. -/
theorem upperOcc_ext {W : Fin k → List α} {t : ℕ} {o o' : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) (ho' : o' ∈ upperOccurrences W t) (h1 : o.1 = o'.1)
        (h2 : o.2.2 = o'.2.2) :
    o = o' := by
  have hs := (mem_upperOcc.mp ho).2.2
  have hs' := (mem_upperOcc.mp ho').2.2
  obtain ⟨l, s, e⟩ := o
  obtain ⟨l', s', e'⟩ := o'
  simp only at h1 h2 hs hs'
  subst h1 h2
  rw [hs, hs']

/-- Upper occurrences of one word are disjoint: an earlier one ends before the next starts. -/
theorem upperOccurrences_le_start {W : Fin k → List α} {t : ℕ} {o o' : Fin k × ℕ × ℕ}
    (ho : o ∈ upperOccurrences W t) (ho' : o' ∈ upperOccurrences W t) (h1 : o.1 = o'.1)
    (h2 : o.2.2 < o'.2.2) : o.2.2 ≤ o'.2.1 := by
  rw [(mem_upperOcc.mp ho').2.2, upperOccurrenceStart, ← h1]
  exact le_previousAnchor (mem_upperOcc.mp ho).2.1 h2

/-- The total length, in letters, of the first `d` words of a list of words. -/
def firstBlocksLength {β : Type} (Z : List (List β)) (d : ℕ) : ℕ := ((Z.take d).map List.length).sum

/-- The cut at depth `d` is the end minus the total length of the last `d` lower blocks. -/
theorem depthCut_add_baseLen {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d : ℕ} (hd : d ≤ lowerBlockCount W t o) :
    depthCut W t o d + firstBlocksLength (reversedBlocks W t o) d = o.2.2 := by
  induction d with
  | zero => simp [firstBlocksLength, depthCut, depthCutAt]
  | succ d ih =>
    have hd' : d < (reversedBlocks W t o).length := by simp; omega
    have h1 := ih (by omega)
    have hlen := length_getElem_reversedBlocks ho hd'
    have hlt := depthCut_lt ho (by omega : d < lowerBlockCount W t o)
    have : firstBlocksLength (reversedBlocks W t o) (d + 1) =
        firstBlocksLength (reversedBlocks W t o) d +
        (reversedBlocks W t o)[d].length := by
      simp only
          [firstBlocksLength, List.take_add_one, List.getElem?_eq_getElem hd', Option.toList_some,
        List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero]
    omega

/-! ## The reverse trie -/

/-- The nodes of the reverse trie on the path of the parse `Z`: the root `0`, the leaf `|Z|`,
and the lengths of the common suffixes of `Z` with the parses of all upper occurrences. -/
def trieNodes (W : Fin k → List α) (t : ℕ) (Z : List (List α)) : Finset ℕ :=
  insert 0 (insert Z.length ((upperParses W t).image (commonSuffixLength Z)))

/-- An edge of the reverse trie: two consecutive nodes `startDepth < endDepth` on the path of
the parse `blocks`. -/
structure Edge (W : Fin k → List α) (t : ℕ) where
  /-- Common blocks parsed along this edge. -/
  blocks : List (List α)
  blocks_mem : blocks ∈ upperParses W t
  /-- Initial trie cut of the parsed block interval. -/
  startDepth : ℕ
  /-- Final trie cut of the parsed block interval. -/
  endDepth : ℕ
  endDepth_mem : endDepth ∈ trieNodes W t blocks
  startDepth_lt_endDepth : startDepth < endDepth
  no_interior_node : ∀ c ∈ trieNodes W t blocks, ¬ (startDepth < c ∧ c < endDepth)

/-- An upper occurrence traverses the edge if its parse ends with the same `endDepth` lower
blocks as the parse of the edge. -/
def Edge.TraversedBy {W : Fin k → List α} {t : ℕ} (e : Edge W t) (o : Fin k × ℕ × ℕ) : Prop :=
  e.endDepth ≤ commonSuffixLength (upperParse W t o) e.blocks

instance {W : Fin k → List α} {t : ℕ} (e : Edge W t) (o : Fin k × ℕ × ℕ) :
    Decidable (e.TraversedBy o) := inferInstanceAs (Decidable (_ ≤ _))

theorem commonSuffixLength_mem_trieNodes {W : Fin k → List α} {t : ℕ} (Z : List (List α))
    {Y : List (List α)} (hY : Y ∈ upperParses W t) : commonSuffixLength Z Y ∈ trieNodes W t Z :=
  mem_insert_of_mem (mem_insert_of_mem (mem_image_of_mem _ hY))

theorem le_length_of_mem_trieNodes {W : Fin k → List α} {t : ℕ} {Z : List (List α)} {c : ℕ}
    (hc : c ∈ trieNodes W t Z) : c ≤ Z.length := by
  simp only [trieNodes, mem_insert, mem_image] at hc
  rcases hc with rfl | rfl | ⟨Y, -, rfl⟩
  · exact Nat.zero_le _
  · exact le_rfl
  · exact commonSuffixLength_le_left _ _

namespace Edge

variable {W : Fin k → List α} {t : ℕ} (e : Edge W t)

theorem endDepth_le_length :
    e.endDepth ≤ e.blocks.length := le_length_of_mem_trieNodes e.endDepth_mem

/-- A parse whose common suffix with the parse of the edge is shorter than `endDepth` has common
suffix at most `startDepth`: no trie node lies strictly inside an edge. -/
theorem commonSuffixLength_le_startDepth {Y : List (List α)} (hY : Y ∈ upperParses W t)
    (h : commonSuffixLength e.blocks Y < e.endDepth) :
    commonSuffixLength e.blocks Y ≤ e.startDepth := by
  by_contra h'
  exact e.no_interior_node _ (commonSuffixLength_mem_trieNodes e.blocks hY) ⟨by omega, h⟩

theorem through_iff {o : Fin k × ℕ × ℕ} :
    e.TraversedBy o ↔ e.endDepth ≤ lowerBlockCount W t o ∧ (reversedBlocks W t o).take e.endDepth =
        e.blocks.reverse.take e.endDepth := by
  unfold TraversedBy commonSuffixLength upperParse
  rw [List.reverse_reverse, le_commonPrefixLength_iff]
  have := e.endDepth_le_length
  simp only [length_reversedBlocks, List.length_reverse]
  constructor
  · rintro ⟨h1, -, h3⟩; exact ⟨h1, h3⟩
  · rintro ⟨h1, h3⟩; exact ⟨h1, this, h3⟩

/-- Some upper occurrence has the parse of the edge, and it traverses the edge. -/
theorem exists_through :
    ∃ o ∈ upperOccurrences W t, upperParse W t o = e.blocks ∧ e.TraversedBy o := by
  obtain ⟨o, ho, hZ⟩ := mem_image.mp e.blocks_mem
  refine ⟨o, ho, hZ, ?_⟩
  unfold TraversedBy
  rw [hZ, commonSuffixLength_self]
  exact e.endDepth_le_length

/-- An occurrence that traverses the edge has the same last `endDepth` lower block lengths as the
parse of the edge. -/
theorem firstBlocksLength_eq {o : Fin k × ℕ × ℕ} (h : e.TraversedBy o) {d : ℕ}
    (hd : d ≤ e.endDepth) :
    firstBlocksLength (reversedBlocks W t o) d = firstBlocksLength e.blocks.reverse d := by
  have h2 := (e.through_iff.mp h).2
  unfold firstBlocksLength
  rw [show (reversedBlocks W t o).take d = ((reversedBlocks W t o).take e.endDepth).take d by
      rw [List.take_take, Nat.min_eq_left hd],
    show e.blocks.reverse.take d = (e.blocks.reverse.take e.endDepth).take d by
      rw [List.take_take, Nat.min_eq_left hd], h2]

/-- For an occurrence that traverses the edge, the cut at depth `d ≤ endDepth` is its end minus a
length that depends only on the edge. -/
theorem depthCut_through {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (h : e.TraversedBy o) {d : ℕ} (hd : d ≤ e.endDepth) :
    depthCut W t o d + firstBlocksLength e.blocks.reverse d = o.2.2 := by
  rw [← e.firstBlocksLength_eq h hd]
  exact depthCut_add_baseLen ho (hd.trans (e.through_iff.mp h).1)

end Edge

end Upper

/-! ## Locality of parsing -/

section Locality

variable {α : Type} [DecidableEq α] {k : ℕ} {W : Fin k → List α}

/-- Lower (level-`t`) anchors of a text `z` read in the left context `u`, as positions in
`(0, |z|]` relative to the left cut of `z`. -/
def relativeAnchors (W : Fin k → List α) (t : ℕ) (u z : List α) : Finset ℕ :=
  (Icc 1 z.length).filter (fun p => u.length + p ∈ contextAnchors W t (u ++ z))

/-- The positions of `z` at which an active level-`t` marker ends that starts strictly to the
left of `z`, in the context `u`. -/
def crossBoundaryMarkerEnds (W : Fin k → List α) (t : ℕ) (u z : List α) : Finset ℕ :=
  (Icc 1 z.length).filter (fun p => ∃ m ∈ active W t,
    marker W t m <:+ (u ++ z).take (u.length + p) ∧ p < (marker W t m).length)

/-- In any context, the lower anchors of `z` are the anchors of `z` alone, which do not depend
on the context, and the ends of markers that start to the left of `z`. -/
theorem relativeAnchors_eq {t : ℕ} (ht : 1 ≤ t) (u z : List α) :
    relativeAnchors W t u z = contextAnchors W t z ∪ crossBoundaryMarkerEnds W t u z := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  ext p
  simp only [relativeAnchors, crossBoundaryMarkerEnds, mem_union, mem_filter, mem_Icc]
  constructor
  · rintro ⟨⟨hp1, hp2⟩, hp⟩
    obtain ⟨-, m, hm, hs⟩ := (mem_contextAnchors_succ W).mp hp
    by_cases hin : (marker W (t + 1) m).length ≤ p
    · exact Or.inl (contextAnchors_of_append_right ht hm hs hp2 hin)
    · exact Or.inr ⟨⟨hp1, hp2⟩, m, hm, hs, by omega⟩
  · rintro (hp | ⟨⟨hp1, hp2⟩, m, hm, hs, -⟩)
    · obtain ⟨hle, m, hm, hs⟩ := (mem_contextAnchors_succ W).mp hp
      have h1 := List.length_pos_iff.mpr (marker_ne_nil ht hm)
      have h2 := hs.length_le
      simp only [List.length_take] at h2
      exact ⟨⟨by omega, hle⟩, contextAnchors_append_right hp⟩
    · refine ⟨⟨hp1, hp2⟩, (mem_contextAnchors_succ W).mpr ⟨by simp; omega, m, hm, hs⟩⟩

/-- No anchor of `z` alone lies at or before the end of a marker that starts to the left of `z`:
its marker would occur strictly inside the other marker, against the factor antichain
property. -/
theorem not_inside_le_crossBoundaryMarkerEnds {t : ℕ} (ht : 1 ≤ t) {u z : List α}
    {p q : ℕ} (hp : p ∈ crossBoundaryMarkerEnds W t u z) (hq : q ∈ contextAnchors W t z)
        (hqp : q ≤ p) : False := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  simp only [crossBoundaryMarkerEnds, mem_filter, mem_Icc] at hp
  obtain ⟨⟨-, hpz⟩, ν, hν, hsν, hlν⟩ := hp
  obtain ⟨hqz, μ, hμ, hsμ⟩ := (mem_contextAnchors_succ W).mp hq
  have hlen : (u ++ z).length = u.length + z.length := by simp
  obtain ⟨hlν', hoν⟩ := (suffix_take_iff (by omega)).mp hsν
  have hsμ' : marker W (t + 1) μ <:+ (u ++ z).take (u.length + q) := by
    rw [List.take_length_add_append]; exact hsμ.trans (List.suffix_append _ _)
  obtain ⟨hlμ, hoμ⟩ := (suffix_take_iff (by omega)).mp hsμ'
  have hlμq : (marker W (t + 1) μ).length ≤ q := by
    have := hsμ.length_le; simp only [List.length_take] at this; omega
  obtain ⟨heq, -⟩ := marker_occurrences_eq_of_nested hν hμ hoν hoμ (by omega) (by omega)
  omega

/-- In every context, the ends of markers that start to the left of `z` lie in the set of
lengths of prefixes of `z` that are nonempty suffixes of coordinate words
(`prefixOccurrenceCuts W z`, which has at most `k (N - 1)` elements for fresh tuples). -/
theorem crossBoundaryMarkerEnds_subset_prefixOccurrenceCuts {t : ℕ} (u z : List α) :
    crossBoundaryMarkerEnds W t u z ⊆ prefixOccurrenceCuts W z := by
  intro p hp
  simp only [crossBoundaryMarkerEnds, mem_filter, mem_Icc] at hp
  obtain ⟨⟨hp1, hp2⟩, m, -, hs, hlt⟩ := hp
  rw [List.take_length_add_append] at hs
  have hout : z.take p <:+ marker W t m :=
    List.suffix_of_suffix_length_le (List.suffix_append _ _) hs (by simp; omega)
  simp only [prefixOccurrenceCuts, mem_filter, mem_Icc]
  exact ⟨⟨hp1, hp2⟩, m, hout.trans (marker_suffix W t m)⟩

end Locality

end DeciSigma1.Holes.Fresh
