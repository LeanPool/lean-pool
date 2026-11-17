/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

import Mathlib.Algebra.Order.BigOperators.Group.Finset

public import LeanPool.DeciSigma1.Holes.Fresh.Parsing
public import LeanPool.DeciSigma1.Words.Deletion
import Mathlib.Data.Finset.Max

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Block deletion

A `BlockDeletion` is the shortening step of the bound on minimal fresh tuples. It consists of an
edge `(a, b)` of the reverse trie of parses at level `t` and two depths `a + M ≤ i < j ≤ b - M`,
with `M = deletionMargin k N`, such that in every upper occurrence that traverses the edge the cuts
at depths `j` and `i` carry the same `label`. The label of a cut records which markers of levels
`1, …, t` end there (`lowerLevelTypes`) and the state of the run before the longest of them, so
equal labels give equal states at the two cuts. The deletion removes the text between these two cuts
from every traversing occurrence (`BlockDeletion.apply`). All removed texts have the same length
(`deletionLength`), and each starts and ends in the same state, so the edited runs pass through
states of the original runs (`BlockDeletion.runPrefix_apply`). The deletion of positions, its cut
map `retainedCount` and the greatest preimage `greatestPreimage` of a cut of the edited text are
those of `Words.Deletion`.

This module proves the properties of a block deletion other than the inclusion of channels:
the edited tuple is shorter, has the same endpoints, visits only states that the original
visits, stays fresh, and keeps the anchors of the original words at the images of the retained
cuts (`contextAnchors_apply`). With channel inclusion, proved in
`Holes.Fresh.ChannelPreservation`, a block deletion is a fresh domination
(`BlockDeletion.freshDominates_of_channel`).

## Main declarations

- `ValidDeletionSite`, `contextAnchors_deleteSite`: one deletion site and the anchors after it
  is removed.
- `sitePositions`, `StrictlySeparated`, `Retained`, `contextAnchors_deleteSites`: deletion of
  several sites with `Words.deletePositions`, and the anchors of the edited text.
- `deletionMargin`, `lowerLevelTypes`, `label`: the labels of cuts.
- `BlockDeletion`, `BlockDeletion.apply`, `BlockDeletion.runPrefix_apply`: block deletions, the
  edited tuple and its states.
- `BlockDeletion.freshDominates_of_channel`: a block deletion with smaller channels is a fresh
  domination.
-/

@[expose] public section


namespace DeciSigma1.Holes.Fresh

open DeciSigma1.Readers DeciSigma1.Words
open Finset

variable {α : Type} [DecidableEq α] {k : ℕ}

/-! ## Small list and marker facts -/

omit [DecidableEq α] in
theorem prefix_drop_of_occ {x u v : List α} {i j : ℕ} (hu : u <+: x.drop i)
    (hv : v <+: x.drop j) (hij : i ≤ j) (hlen : j + v.length ≤ i + u.length) :
    v <+: u.drop (j - i) := by
  obtain ⟨r, hr⟩ := hu
  have hd : x.drop j = u.drop (j - i) ++ r := by
    rw [show j = i + (j - i) by omega, ← List.drop_drop, ← hr,
      List.drop_append_of_le_length (by omega), Nat.add_sub_cancel_left]
  rw [hd] at hv
  exact List.prefix_of_prefix_length_le hv (List.prefix_append _ _) (by simp; omega)

omit [DecidableEq α] in
theorem suffix_append_right {a b : List α} (h : a <:+ b) (c : List α) : a ++ c <:+ b ++ c := by
  obtain ⟨p, rfl⟩ := h; exact ⟨p, by simp⟩

theorem marker_suffix_of_le {W : Fin k → List α} {r t : ℕ} (hrt : r ≤ t)
    {m : Fin k} (hm : m ∈ active W t) : marker W r m <:+ marker W t m := by
  induction t, hrt using Nat.le_induction with
  | base => exact List.suffix_refl _
  | succ t _ ih =>
    exact (ih (active_succ_subset W t hm)).trans (marker_suffix_succ hm)

/-- An occurrence of a level-`r` marker (`1 ≤ r ≤ t + 1`) that strictly crosses a cut `p` at
which a level-`t` marker `τ` ends has at most `|τ|` letters to the left of `p`: otherwise `τ`,
or its level-`r` suffix, would occur strictly inside it, against the factor antichain
property. -/
theorem crossing_length_le {W : Fin k → List α} {t r : ℕ} (ht : 1 ≤ t)
    (hr : r ≤ t + 1) {m m0 : Fin k} (hm : m ∈ active W r) (hm0 : m0 ∈ active W t)
    {u : List α} {p e : ℕ} (hτ : marker W t m0 <:+ u.take p) (hμ : marker W r m <:+ u.take e)
    (hpe : p < e) (he : e ≤ u.length) :
    (marker W r m).length ≤ (e - p) + (marker W t m0).length := by
  by_contra hcon
  have hpu : p ≤ u.length := by omega
  obtain ⟨hμl, hμo⟩ := (suffix_take_iff he).mp hμ
  obtain ⟨hτl, hτo⟩ := (suffix_take_iff hpu).mp hτ
  rcases Nat.lt_or_ge r (t + 1) with hrt | hrt
  · -- r ≤ t: the level-`r` suffix of `τ` sits strictly inside the occurrence
    have hrt' : r ≤ t := by omega
    have hm0r : m0 ∈ active W r := active_anti W hrt' hm0
    have hsuf : marker W r m0 <:+ u.take p := (marker_suffix_of_le hrt' hm0).trans hτ
    have hsl := (marker_suffix_of_le hrt' hm0).length_le
    obtain ⟨-, hro⟩ := (suffix_take_iff hpu).mp hsuf
    obtain ⟨heq, -⟩ := marker_occurrences_eq_of_nested hm hm0r hμo hro (by omega) (by omega)
    omega
  · -- r = t + 1: `τ` is a complete internal occurrence, against
    -- `marker_occurrences_in_next_marker`
    have hr' : r = t + 1 := by omega
    subst hr'
    have hin := prefix_drop_of_occ hμo hτo (by omega) (by omega)
    rcases (marker_occurrences_in_next_marker ht hm).2.2 m0 hm0 _ hin with h | h <;> omega

/-! ## Deleting one site -/

section OneSite

variable {W : Fin k → List α}

/-- Conditions on one deletion site `[c, c + δ)` of a text `x` at level `t`, for the markers of
`W`: a level-`t` marker ends at `c`, the same markers of each level `1, …, t` end at `c` and at
`c + δ`, and no marker of level `t + 1` ends at `c + δ`. The conditions depend only on
`x.take (c + δ)`. -/
structure ValidDeletionSite (W : Fin k → List α) (t : ℕ) (x : List α) (c δ : ℕ) : Prop where
  le_len : c + δ ≤ x.length
  anchor : 1 ≤ t → ∃ m ∈ active W t, marker W t m <:+ x.take c
  types : ∀ r, 1 ≤ r → r ≤ t → ∀ m ∈ active W r,
    (marker W r m <:+ x.take c ↔ marker W r m <:+ x.take (c + δ))
  no_upper_marker : ∀ m ∈ active W (t + 1), ¬ marker W (t + 1) m <:+ x.take (c + δ)

theorem ValidDeletionSite.of_take {t : ℕ} {x x' : List α} {c δ p : ℕ}
    (h : ValidDeletionSite W t x c δ)
    (hx : x'.take p = x.take p) (hp : c + δ ≤ p) (hlen : c + δ ≤ x'.length) :
    ValidDeletionSite W t x' c δ := by
  have e1 : x'.take c = x.take c := by
    rw [show c = min c p by omega, ← List.take_take, hx, List.take_take]
  have e2 : x'.take (c + δ) = x.take (c + δ) := by
    rw [show c + δ = min (c + δ) p by omega, ← List.take_take, hx, List.take_take]
  exact ⟨hlen, by rw [e1]; exact h.anchor, by rw [e1, e2]; exact h.types,
    by rw [e2]; exact h.no_upper_marker⟩

omit [DecidableEq α] in
theorem take_deleteSite_of_le {x : List α} {c δ e : ℕ} (hc : c ≤ x.length) (he : e ≤ c) :
    (x.take c ++ x.drop (c + δ)).take e = x.take e := by
  rw [List.take_append_of_le_length (by simp; omega), List.take_take, Nat.min_eq_left he]

omit [DecidableEq α] in
theorem take_deleteSite_of_ge {x : List α} {c δ e : ℕ} (hc : c ≤ x.length) (he : c ≤ e) :
    (x.take c ++ x.drop (c + δ)).take e = x.take c ++ (x.drop (c + δ)).take (e - c) := by
  rw [List.take_append, List.take_of_length_le (by simp; omega)]
  simp only [List.length_take, Nat.min_eq_left hc]

omit [DecidableEq α] in
theorem take_add_delta {x : List α} {c δ e : ℕ} (he : c ≤ e) :
    x.take (e + δ) = x.take (c + δ) ++ (x.drop (c + δ)).take (e - c) := by
  rw [← List.take_add]; congr 1; omega

omit [DecidableEq α] in
theorem length_deleteSite {x : List α} {c δ : ℕ} (h : c + δ ≤ x.length) :
    (x.take c ++ x.drop (c + δ)).length = x.length - δ := by
  simp; omega

/-- After deleting a valid site, the level-`r` anchors (`1 ≤ r ≤ t + 1`) of the edited text,
for the markers of `W`, are exactly the images of the original ones: cuts `≤ c` stay and cuts
`≥ c + δ` move left by `δ`. -/
theorem contextAnchors_deleteSite {t : ℕ} {x : List α} {c δ : ℕ}
    (hS : ValidDeletionSite W t x c δ) {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ t + 1) (e : ℕ) :
    e ∈ contextAnchors W r (x.take c ++ x.drop (c + δ)) ↔
      (e ≤ c ∧ e ∈ contextAnchors W r x) ∨ (c ≤ e ∧ e + δ ∈ contextAnchors W r x) := by
  obtain ⟨r, rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hcx : c + δ ≤ x.length := hS.le_len
  have hlen := length_deleteSite (x := x) hcx
  simp only [mem_contextAnchors_succ]
  constructor
  · rintro ⟨heL, m, hm, hs⟩
    by_cases hec : e ≤ c
    · left
      rw [take_deleteSite_of_le (by omega) hec] at hs
      exact ⟨hec, by omega, m, hm, hs⟩
    · right
      refine ⟨by omega, by omega, m, hm, ?_⟩
      rw [take_deleteSite_of_ge (by omega) (by omega)] at hs
      rw [take_add_delta (by omega : c ≤ e)]
      set R := (x.drop (c + δ)).take (e - c) with hR
      have hRl : R.length = e - c := by simp [hR]; omega
      by_cases hμR : (marker W (r + 1) m).length ≤ e - c
      · exact (List.suffix_of_suffix_length_le hs (List.suffix_append _ _) (by omega)).trans
          (List.suffix_append _ _)
      · rcases Nat.eq_zero_or_pos t with rfl | ht
        · have : r = 0 := by omega
          subst this
          have : (marker W (0 + 1) m).length = 1 := length_marker_one hm
          omega
        obtain ⟨m0, hm0, hτ⟩ := hS.anchor ht
        have hτ'' : marker W t m0 <:+ (x.take c ++ x.drop (c + δ)).take c := by
          rwa [take_deleteSite_of_le (by omega) le_rfl]
        have hs' : marker W (r + 1) m <:+ (x.take c ++ x.drop (c + δ)).take e := by
          rwa [take_deleteSite_of_ge (by omega) (by omega)]
        have hcr := crossing_length_le ht hr hm hm0 hτ'' hs' (by omega) (by omega)
        have h1 : marker W (r + 1) m <:+ marker W t m0 ++ R :=
          List.suffix_of_suffix_length_le hs (suffix_append_right hτ R) (by simp; omega)
        have hτ2 := ((hS.types t ht le_rfl m0 hm0).mp hτ)
        exact h1.trans (suffix_append_right hτ2 R)
  · rintro (⟨hec, heL, m, hm, hs⟩ | ⟨hce, heL, m, hm, hs⟩)
    · refine ⟨by omega, m, hm, ?_⟩
      rwa [take_deleteSite_of_le (by omega) hec]
    · refine ⟨by omega, m, hm, ?_⟩
      rw [take_deleteSite_of_ge (by omega) hce]
      rw [take_add_delta hce] at hs
      set R := (x.drop (c + δ)).take (e - c) with hR
      have hRl : R.length = e - c := by simp [hR]; omega
      by_cases hμR : (marker W (r + 1) m).length ≤ e - c
      · exact (List.suffix_of_suffix_length_le hs (List.suffix_append _ _) (by omega)).trans
          (List.suffix_append _ _)
      · rcases Nat.eq_or_lt_of_le hce with hceq | hcl
        · -- the marker ends exactly at the right cut `c + δ`
          subst hceq
          have hR0 : R = [] := by simp [hR]
          rw [hR0, List.append_nil] at hs ⊢
          rcases Nat.lt_or_ge (r + 1) (t + 1) with hrt | hrt
          · exact (hS.types (r + 1) (by omega) (by omega) m hm).mpr hs
          · have : r = t := by omega
            subst this
            exact absurd hs (hS.no_upper_marker m hm)
        · rcases Nat.eq_zero_or_pos t with rfl | ht
          · have : r = 0 := by omega
            subst this
            have : (marker W (0 + 1) m).length = 1 := length_marker_one hm
            omega
          obtain ⟨m0, hm0, hτ⟩ := hS.anchor ht
          have hτ2 := ((hS.types t ht le_rfl m0 hm0).mp hτ)
          have hs' : marker W (r + 1) m <:+ x.take (e + δ) := by
            rw [take_add_delta hce]; exact hs
          have hcr := crossing_length_le ht hr hm hm0 hτ2 hs' (by omega) (by omega)
          have h1 : marker W (r + 1) m <:+ marker W t m0 ++ R :=
            List.suffix_of_suffix_length_le hs (suffix_append_right hτ2 R) (by simp; omega)
          exact h1.trans (suffix_append_right hτ R)

end OneSite

/-! ## Deleting several sites -/

section SeveralSites

variable {W : Fin k → List α}

/-- The positions deleted by the sites `[c, c + δ)` with `c ∈ cs`. -/
def sitePositions (δ : ℕ) (cs : Finset ℕ) : Finset ℕ := cs.biUnion fun c => Finset.Ico c (c + δ)

/-- Sites of length `δ` with a retained position between any two of them. -/
def StrictlySeparated (δ : ℕ) (cs : Finset ℕ) : Prop := ∀ c ∈ cs, ∀ c' ∈ cs, c < c' → c + δ < c'

/-- An original cut that is not strictly inside a deleted interval. -/
def Retained (δ : ℕ) (cs : Finset ℕ) (p : ℕ) : Prop := ∀ c ∈ cs, ¬ (c < p ∧ p < c + δ)

variable {δ : ℕ} {cs : Finset ℕ}

theorem mem_sitePositions {p : ℕ} : p ∈ sitePositions δ cs ↔ ∃ c ∈ cs, c ≤ p ∧ p < c + δ := by
  simp [sitePositions]

theorem sitePositions_insert (c : ℕ) (cs : Finset ℕ) :
    sitePositions δ (insert c cs) = sitePositions δ cs ∪ Finset.Ico c (c + δ) := by
  rw [sitePositions, Finset.biUnion_insert, Finset.union_comm]; rfl

/-- After deleting separated valid sites, the level-`r` anchors (`1 ≤ r ≤ t + 1`) of the edited
text, for the markers of `W`, are exactly the images under the cut map of the original anchors
outside the deleted open intervals. -/
theorem contextAnchors_deleteSites {t r : ℕ} (hr1 : 1 ≤ r)
    (hr : r ≤ t + 1) (cs : Finset ℕ) : ∀ {x : List α}, StrictlySeparated δ cs →
    (∀ c ∈ cs, ValidDeletionSite W t x c δ) → ∀ e,
      e ∈ contextAnchors W r (deletePositions x (sitePositions δ cs)) ↔
        ∃ p ∈ contextAnchors W r x, Retained δ cs p ∧ retainedCount (sitePositions δ cs) p = e := by
  induction cs using Finset.induction_on_max with
  | empty =>
    intro x _ _ e
    simp only [sitePositions, Finset.biUnion_empty, deletePositions_empty, retainedCount_empty,
      Retained, Finset.notMem_empty, false_imp_iff, implies_true, true_and, exists_eq_right]
  | insert c cs hmax ih =>
    intro x hsep hok e
    have hc := hok c (mem_insert_self ..)
    have hcx := hc.le_len
    have hlt : ∀ c2 ∈ cs, c2 + δ < c := fun c2 h2 =>
      hsep c2 (mem_insert_of_mem h2) c (mem_insert_self ..) (hmax c2 h2)
    have hD : ∀ p ∈ sitePositions δ cs, p < c := fun p hp => by
      obtain ⟨c2, h2, -, h3⟩ := mem_sitePositions.mp hp
      have := hlt c2 h2; omega
    have hok' : ∀ c2 ∈ cs, ValidDeletionSite W t (x.take c ++ x.drop (c + δ)) c2 δ := by
      intro c2 hc2
      have h2 := hlt c2 hc2
      refine (hok c2 (mem_insert_of_mem hc2)).of_take (p := c)
        (take_deleteSite_of_le (by omega) le_rfl) h2.le ?_
      rw [length_deleteSite hcx]; omega
    rw [sitePositions_insert, deletePositions_union_Ico x hD (by omega),
      ih (fun a ha b hb => hsep a (mem_insert_of_mem ha) b (mem_insert_of_mem hb)) hok' e]
    constructor
    · rintro ⟨p', hp', hret, hk⟩
      rcases (contextAnchors_deleteSite hc hr1 hr p').mp hp' with ⟨hpc, hpx⟩ | ⟨hcp, hpx⟩
      · refine ⟨p', hpx, fun c2 hc2 => ?_, by rwa [retainedCount_union_Ico_of_le hpc]⟩
        rcases mem_insert.mp hc2 with rfl | hc2
        · omega
        · exact hret c2 hc2
      · refine ⟨p' + δ, hpx, fun c2 hc2 => ?_, ?_⟩
        · rcases mem_insert.mp hc2 with rfl | hc2
          · omega
          · have := hlt c2 hc2; omega
        · rwa [retainedCount_union_Ico_of_ge hD (by omega), Nat.add_sub_cancel]
    · rintro ⟨p, hp, hret, hk⟩
      have hretc := hret c (mem_insert_self ..)
      by_cases h : p ≤ c
      · exact ⟨p, (contextAnchors_deleteSite hc hr1 hr p).mpr (Or.inl ⟨h, hp⟩),
          fun c2 hc2 => hret c2 (mem_insert_of_mem hc2),
          by rwa [← retainedCount_union_Ico_of_le h]⟩
      · refine ⟨p - δ, (contextAnchors_deleteSite hc hr1 hr _).mpr
          (Or.inr ⟨by omega, by rwa [Nat.sub_add_cancel (by omega)]⟩), ?_,
          by rwa [← retainedCount_union_Ico_of_ge hD (by omega)]⟩
        intro c2 hc2 ⟨h1, h2⟩
        have := hlt c2 hc2; omega

/-- A maximal interval of deleted positions is a site. -/
theorem mem_sites_of_maximal_interval (hs : StrictlySeparated δ cs) {j c : ℕ} (hjc : j < c)
    (hD : ∀ p, j ≤ p → p < c → p ∈ sitePositions δ cs)
    (hj : j = 0 ∨ j - 1 ∉ sitePositions δ cs) (hc : c ∉ sitePositions δ cs) :
    j ∈ cs ∧ c = j + δ := by
  obtain ⟨c₀, hc₀, h1, h2⟩ := mem_sitePositions.mp (hD (c - 1) (by omega) (by omega))
  have hce : c = c₀ + δ := by
    by_contra hne
    exact hc (mem_sitePositions.mpr ⟨c₀, hc₀, by omega, by omega⟩)
  have hje : j = c₀ := by
    rcases lt_trichotomy j c₀ with h | h | h
    · obtain ⟨c₁, hc₁, h3, h4⟩ := mem_sitePositions.mp (hD (c₀ - 1) (by omega) (by omega))
      have := hs c₁ hc₁ c₀ hc₀ (by omega)
      omega
    · exact h
    · rcases hj with h0 | h0
      · omega
      · exact absurd (mem_sitePositions.mpr ⟨c₀, hc₀, by omega, by omega⟩) h0
  exact ⟨hje ▸ hc₀, by omega⟩

variable {S : Type}

omit [DecidableEq α] in
/-- If every deleted text starts and ends in the same state, the state of the edited text at a
cut is the state of the original text at the greatest preimage of the cut. -/
theorem runFrom_deleteSites (T : Table α S k) (q0 : S) {x : List α} (hs : StrictlySeparated δ cs)
    (hst : ∀ c ∈ cs, c + δ < x.length ∧
      runFrom T.step q0 (x.take c) = runFrom T.step q0 (x.take (c + δ)))
    (a : ℕ) :
    runFrom T.step q0 ((deletePositions x (sitePositions δ cs)).take a) =
      runFrom T.step q0 (x.take (greatestPreimage (sitePositions δ cs) a)) := by
  refine runFrom_take_deletePositions T q0 x (fun j c hjc _ hD hj hc => ?_) (fun h => ?_) a
  · obtain ⟨hjs, rfl⟩ := mem_sites_of_maximal_interval hs hjc hD hj hc
    exact (hst j hjs).2
  · obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp h
    have := (hst c hc).1; omega

end SeveralSites

/-! ## Labels -/

section Label

variable {S : Type} [DecidableEq S]

/-- The margin between the deleted depths and the ends of a trie edge: `k (n - 1) + 2` bounds
the anchors in a window of a marker of the next level (`card_anchors_Ioc_marker_le`), and
`2 k n + 3` leaves room for the windows on both sides of the deleted text. -/
def deletionMargin (k n : ℕ) : ℕ := (k * (n - 1) + 2) + 2 * k * n + 3

/-- The level-`r` marker texts that end at the cut `c` of `u`. -/
def markerTypes (W : Fin k → List α) (r : ℕ) (u : List α) (c : ℕ) : Finset (List α) :=
  ((active W r).filter (fun m => marker W r m <:+ u.take c)).image (marker W r)

/-- The marker texts ending at the cut, at each level `1, …, t`. -/
def lowerLevelTypes (W : Fin k → List α) (t : ℕ) (u : List α) (c : ℕ) : Fin t → Finset (List α) :=
  fun r => markerTypes W (r.1 + 1) u c

/-- The length of the longest marker of level at most `t` that ends at the cut. -/
def windowLength (W : Fin k → List α) (t : ℕ) (u : List α) (c : ℕ) : ℕ :=
  univ.sup fun r : Fin t => (lowerLevelTypes W t u c r).sup List.length

/-- The label of the cut `c` of word `l`: the marker texts of levels `1, …, t` ending at the cut,
and the state `windowLength` letters to the left of the cut. -/
def label (T : Table α S k) (W : Fin k → List α) (t : ℕ) (l : Fin k) (c : ℕ) :
    (Fin t → Finset (List α)) × S :=
  (lowerLevelTypes W t (W l) c, T.runPrefix W l (c - windowLength W t (W l) c))

theorem mem_markerTypes {W : Fin k → List α} {r : ℕ} {u : List α} {c : ℕ} {τ : List α} :
    τ ∈ markerTypes W r u c ↔ ∃ m ∈ active W r, marker W r m <:+ u.take c ∧ marker W r m = τ := by
  simp only [markerTypes, mem_image, mem_filter, and_assoc]

/-- Equal marker texts in the labels mean that the same markers of levels `1, …, t` end at the
two cuts. -/
theorem types_iff_of_lowerLevelTypes {W : Fin k → List α} {t : ℕ} {u : List α} {c c' : ℕ}
    (h : lowerLevelTypes W t u c = lowerLevelTypes W t u c') {r : ℕ} (hr1 : 1 ≤ r)
        (hr : r ≤ t) {m : Fin k}
    (hm : m ∈ active W r) : marker W r m <:+ u.take c ↔ marker W r m <:+ u.take c' := by
  have hrr : markerTypes W r u c = markerTypes W r u c' := by
    have := congrFun h ⟨r - 1, by omega⟩
    simpa [lowerLevelTypes, Nat.sub_add_cancel hr1] using this
  constructor
  · intro hs
    obtain ⟨m', -, hs', he⟩ := mem_markerTypes.mp (hrr ▸ mem_markerTypes.mpr ⟨m, hm, hs, rfl⟩)
    rwa [he] at hs'
  · intro hs
    obtain ⟨m', -, hs', he⟩ := mem_markerTypes.mp (hrr.symm ▸ mem_markerTypes.mpr ⟨m, hm, hs, rfl⟩)
    rwa [he] at hs'

omit [DecidableEq S] in
/-- Equal labels give equal states at the two cuts: the marker texts fix the last
`windowLength` letters before each cut, and the second component fixes the state before them. -/
theorem runPrefix_eq_of_label (T : Table α S k) {W : Fin k → List α} {t : ℕ} {l : Fin k}
    {c c' : ℕ} (hc : c ≤ (W l).length) (hc' : c' ≤ (W l).length)
    (h : label T W t l c = label T W t l c') : T.runPrefix W l c = T.runPrefix W l c' := by
  simp only [label, Prod.mk.injEq] at h
  obtain ⟨hL, hq⟩ := h
  have hw : windowLength W t (W l) c = windowLength W t (W l) c' := by simp only [windowLength, hL]
  rw [← hw] at hq
  set w := windowLength W t (W l) c with hwdef
  rcases Nat.eq_zero_or_pos w with hw0 | hwpos
  · rw [hw0] at hq; simpa using hq
  · -- a marker text of length `w` ends at both cuts
    have hne1 : (univ : Finset (Fin t)).Nonempty := by
      by_contra hem
      rw [not_nonempty_iff_eq_empty] at hem
      simp [hwdef, windowLength, hem] at hwpos
    obtain ⟨r, -, hr⟩ :=
        exists_mem_eq_sup _ hne1 (fun r : Fin t => (lowerLevelTypes W t (W l) c r).sup List.length)
    have hne2 : (lowerLevelTypes W t (W l) c r).Nonempty := by
      by_contra hem
      rw [not_nonempty_iff_eq_empty] at hem
      have : w = 0 := by rw [hwdef, windowLength, hr, hem, sup_empty]; rfl
      omega
    obtain ⟨τ, hτ, hτl⟩ := exists_mem_eq_sup _ hne2 List.length
    have hτw : τ.length = w := by rw [hwdef, windowLength, hr, hτl]
    have hτ' : τ ∈ lowerLevelTypes W t (W l) c' r := hL ▸ hτ
    obtain ⟨m1, -, hs1, rfl⟩ := mem_markerTypes.mp hτ
    obtain ⟨m2, -, hs2, he2⟩ := mem_markerTypes.mp hτ'
    rw [he2] at hs2
    obtain ⟨hl1, ho1⟩ := (suffix_take_iff hc).mp hs1
    obtain ⟨hl2, ho2⟩ := (suffix_take_iff hc').mp hs2
    have e1 := take_occ ho1
    have e2 := take_occ ho2
    rw [Nat.sub_add_cancel hl1] at e1
    rw [Nat.sub_add_cancel hl2] at e2
    simp only [Table.runPrefix]
    rw [e1, e2, runFrom_append, runFrom_append, hτw]
    simp only [Table.runPrefix] at hq
    rw [hq]

end Label

/-! ## Block deletions -/

variable {S : Type} [Fintype S]

/-- A block deletion at level `t`: an edge `(a, b)` of the reverse trie of parses and depths
`i = minDepth` and `j = maxDepth` with `a + M ≤ i < j ≤ b - M`, where `M = deletionMargin k N`,
such that the cuts at depths `j` and `i` carry equal labels in every upper occurrence that
traverses the edge. Depths count lower blocks from the right, so the cut at depth `j` lies to the
left of the cut at depth `i`. -/
structure BlockDeletion (T : Table α S k) (W : Fin k → List α) (t : ℕ) where
  /-- Parse edge containing the blocks to delete. -/
  edge : Edge W t
  /-- First cut of the deleted block interval. -/
  minDepth : ℕ
  /-- Last cut of the deleted block interval. -/
  maxDepth : ℕ
  left_margin : edge.startDepth + deletionMargin k (Fintype.card S) ≤ minDepth
  minDepth_lt_maxDepth : minDepth < maxDepth
  right_margin : maxDepth + deletionMargin k (Fintype.card S) ≤ edge.endDepth
  labels_eq : ∀ o ∈ upperOccurrences W t, edge.TraversedBy o →
    label T W t o.1 (depthCut W t o maxDepth) = label T W t o.1 (depthCut W t o minDepth)

namespace BlockDeletion

variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)

/-- The length of the deleted text, the same in every upper occurrence that traverses the edge. -/
def deletionLength :
    ℕ := firstBlocksLength m.edge.blocks.reverse m.maxDepth -
        firstBlocksLength m.edge.blocks.reverse m.minDepth

/-- The upper occurrences of word `l` that traverse the edge. -/
def traversingOccurrences (l : Fin k) : Finset (Fin k × ℕ × ℕ) :=
  (upperOccurrences W t).filter (fun o => o.1 = l ∧ m.edge.TraversedBy o)

/-- The left cuts, at depth `j`, of the deletion sites of word `l`. -/
def sites (l : Fin k) :
    Finset ℕ := (m.traversingOccurrences l).image (fun o => depthCut W t o m.maxDepth)

/-- The edited tuple: delete `[depthCut o j, depthCut o i)` from every upper occurrence `o` that
traverses the edge. -/
def apply : Fin k → List α :=
  fun l => deletePositions (W l) (sitePositions m.deletionLength (m.sites l))

theorem one_le_minDepth :
    1 ≤ m.minDepth := by have := m.left_margin; unfold deletionMargin at this; omega

theorem maxDepth_lt_endDepth :
    m.maxDepth <
        m.edge.endDepth := by have := m.right_margin; unfold deletionMargin at this; omega

theorem mem_throughOcc {l : Fin k} {o : Fin k × ℕ × ℕ} :
    o ∈ m.traversingOccurrences l ↔ o ∈ upperOccurrences W t ∧ o.1 = l ∧ m.edge.TraversedBy o := by
  simp [traversingOccurrences]

/-- In a traversing occurrence `(l, s, e)`, the deletion site lies strictly inside the upper
block, its two cuts are lower anchors, and the deleted text has length `deletionLength`. -/
theorem site_spec {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : m.edge.TraversedBy o) :
    o.2.1 < depthCut W t o m.maxDepth ∧ depthCut W t o m.maxDepth < depthCut W t o m.minDepth ∧
      depthCut W t o m.minDepth < o.2.2 ∧ o.2.2 ≤ (W o.1).length ∧
      depthCut W t o m.maxDepth + m.deletionLength = depthCut W t o m.minDepth ∧
      depthCut W t o m.maxDepth ∈ anchors W t o.1 ∧ depthCut W t o m.minDepth ∈
          anchors W t o.1 := by
  have hbn := (m.edge.through_iff.mp hth).1
  have hjn : m.maxDepth < lowerBlockCount W t o := lt_of_lt_of_le m.maxDepth_lt_endDepth hbn
  have hin : m.minDepth < lowerBlockCount W t o := by have := m.minDepth_lt_maxDepth; omega
  obtain ⟨hall, -⟩ := depthCut_spec ho
  obtain ⟨hjA, hjs, -, -⟩ := hall m.maxDepth hjn
  obtain ⟨hiA, -, -, -⟩ := hall m.minDepth hin
  have hji := depthCut_lt_of_lt ho m.minDepth_lt_maxDepth hjn.le
  have hie : depthCut W t o m.minDepth < o.2.2 :=
    depthCut_lt_of_lt ho (show 0 < m.minDepth from m.one_le_minDepth) hin.le
  have hj' := m.edge.depthCut_through ho hth m.maxDepth_lt_endDepth.le
  have hi' := m.edge.depthCut_through ho hth (d := m.minDepth)
    (by have := m.minDepth_lt_maxDepth; have := m.maxDepth_lt_endDepth; omega)
  have hE := (upperOcc_spec ho).2.1
  refine ⟨hjs, hji, hie, hE, ?_, hjA, hiA⟩
  unfold deletionLength
  omega

theorem delta_pos : 0 < m.deletionLength := by
  obtain ⟨o, ho, -, hth⟩ := m.edge.exists_through
  have := m.site_spec ho hth
  omega

theorem mem_sites {l : Fin k} {c : ℕ} :
    c ∈ m.sites l ↔ ∃ o ∈ upperOccurrences W t, o.1 = l ∧ m.edge.TraversedBy o ∧
        depthCut W t o m.maxDepth =
        c := by
  simp only [sites, mem_image, mem_throughOcc]
  constructor
  · rintro ⟨o, ⟨ho, hl, hth⟩, rfl⟩; exact ⟨o, ho, hl, hth, rfl⟩
  · rintro ⟨o, ho, hl, hth, rfl⟩; exact ⟨o, ⟨ho, hl, hth⟩, rfl⟩

/-- Two deletion sites of one word lie in different upper blocks, so the earlier site ends
strictly before the later one starts. -/
theorem sites_separated {l : Fin k} {c c' : ℕ} (hc : c ∈ m.sites l)
    (hc' : c' ∈ m.sites l) (hlt : c < c') : c + m.deletionLength < c' := by
  obtain ⟨o, ho, hl, hth, rfl⟩ := m.mem_sites.mp hc
  obtain ⟨o', ho', hl', hth', rfl⟩ := m.mem_sites.mp hc'
  have s1 := m.site_spec ho hth
  have s2 := m.site_spec ho' hth'
  rcases lt_trichotomy o.2.2 o'.2.2 with h | h | h
  · have := upperOccurrences_le_start ho ho' (hl.trans hl'.symm) h
    omega
  · have := upperOcc_ext ho ho' (hl.trans hl'.symm) h
    subst this; omega
  · have := upperOccurrences_le_start ho' ho (hl'.trans hl.symm) h
    omega

theorem strictlySeparated (l : Fin k) :
    StrictlySeparated m.deletionLength (m.sites l) :=
  fun _ hc _ hc' h => m.sites_separated hc hc' h

/-- Every site satisfies the hypotheses of `contextAnchors_deleteSite` and is a loop of the run. -/
theorem site_valid {l : Fin k} {c : ℕ} (hc : c ∈ m.sites l) :
    ValidDeletionSite W t (W l) c m.deletionLength ∧ c + m.deletionLength < (W l).length ∧
      runFrom T.step (T.start l) ((W l).take c) =
          runFrom T.step (T.start l) ((W l).take (c + m.deletionLength)) := by
  obtain ⟨o, ho, rfl, hth, rfl⟩ := m.mem_sites.mp hc
  obtain ⟨hsj, hji, hie, hE, hd, hjA, hiA⟩ := m.site_spec ho hth
  rw [hd]
  have hlab := m.labels_eq o ho hth
  have hnotup := (upperOcc_spec ho).2.2.2.2
  refine ⟨⟨by omega, ?_, ?_, ?_⟩, by omega, ?_⟩
  · intro ht
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    have hmem : depthCut W (t' + 1) o m.maxDepth ∈ contextAnchors W (t' + 1) (W o.1) := by
      rcases mem_insert.mp hjA with h | h
      · omega
      · exact h
    obtain ⟨-, m0, hm0, hs⟩ := (mem_contextAnchors_succ W).mp hmem
    exact ⟨m0, hm0, hs⟩
  · intro r hr1 hr mm hmm
    simp only [label, Prod.mk.injEq] at hlab
    rw [hd]
    exact types_iff_of_lowerLevelTypes hlab.1 hr1 hr hmm
  · intro mm hmm hs
    rw [hd] at hs
    have hmem : depthCut W t o m.minDepth ∈ anchors W (t + 1) o.1 :=
      mem_insert_of_mem ((mem_contextAnchors_succ W).mpr ⟨by omega, mm, hmm, hs⟩)
    exact hnotup _ hmem ⟨by omega, hie⟩
  · exact runPrefix_eq_of_label T (by omega) (by omega) hlab

theorem length_not_mem_sitePositions (l : Fin k) :
    (W l).length ∉ sitePositions m.deletionLength (m.sites l) := by
  intro h
  obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp h
  have := (m.site_valid hc).2.1
  omega

/-- The state of an edited word at a cut is the state of the original word at the greatest
preimage of the cut. -/
theorem runPrefix_apply (l : Fin k) (a : ℕ) :
    T.runPrefix m.apply l a =
      T.runPrefix W l (greatestPreimage (sitePositions m.deletionLength (m.sites l)) a) :=
  runFrom_deleteSites T (T.start l) (m.strictlySeparated l)
    (fun _ hc => ⟨(m.site_valid hc).2.1, (m.site_valid hc).2.2⟩) a

/-- The edited tuple has the same endpoints. -/
theorem endState_apply (l : Fin k) :
    T.endState m.apply l = T.endState W l := by
  simp only [Table.endState]
  rw [m.runPrefix_apply, apply, greatestPreimage_length _ (m.length_not_mem_sitePositions l)]

/-- The edited tuple visits only states that the original visits. -/
theorem visitedStates_subset [DecidableEq S] (l : Fin k) :
    T.visitedStates m.apply l ⊆ T.visitedStates W l := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Table.mem_visitedStates.mp hq
  rw [m.runPrefix_apply]
  exact Table.runPrefix_mem_visitedStates W l
    (greatestPreimage_le_length _ (m.length_not_mem_sitePositions l) ha)

theorem properVisitedStates_subset [DecidableEq S] (l : Fin k) :
    T.properVisitedStates m.apply l ⊆ T.properVisitedStates W l := by
  intro q hq
  obtain ⟨a, ha, rfl⟩ := Table.mem_properVisitedStates.mp hq
  rw [m.runPrefix_apply]
  exact Table.mem_properVisitedStates.mpr ⟨_, greatestPreimage_lt_length _ ha, rfl⟩

/-- The edited tuple is fresh. -/
theorem fresh_apply [DecidableEq S] (hfr : ∀ i, T.Fresh W i) (l : Fin k) :
    T.Fresh m.apply l := by
  intro h
  rw [m.endState_apply l] at h
  exact hfr l (m.properVisitedStates_subset l h)

/-- The edited tuple is shorter. -/
theorem totalLength_apply_lt : totalLength m.apply < totalLength W := by
  obtain ⟨o, ho, -, hth⟩ := m.edge.exists_through
  have hsite : depthCut W t o m.maxDepth ∈ m.sites o.1 := m.mem_sites.mpr ⟨o, ho, rfl, hth, rfl⟩
  have hd := m.delta_pos
  unfold totalLength
  apply Finset.sum_lt_sum
  · intro l _
    rw [apply, length_deletePositions]
    exact retainedCount_le _
  · refine ⟨o.1, mem_univ _, ?_⟩
    rw [apply, length_deletePositions]
    exact retainedCount_lt_of_mem
      (mem_sitePositions.mpr ⟨_, hsite, le_rfl, by omega⟩)
      (by have := (m.site_valid hsite).2.1; omega)

/-- For the markers of `W`, the level-`r` anchors (`1 ≤ r ≤ t + 1`) of an edited word are exactly
the images under the cut map of the original anchors that are not deleted. -/
theorem contextAnchors_apply {r : ℕ} (hr1 : 1 ≤ r) (hr : r ≤ t + 1) (l : Fin k) (e' : ℕ) :
    e' ∈ contextAnchors W r (m.apply l) ↔
      ∃ p ∈ contextAnchors W r (W l), Retained m.deletionLength (m.sites l) p ∧
        retainedCount (sitePositions m.deletionLength (m.sites l)) p = e' :=
  contextAnchors_deleteSites hr1 hr _ (m.strictlySeparated l)
    (fun _ hc => (m.site_valid hc).1) e'

/-- A block deletion whose edited tuple has smaller channels is a fresh domination. -/
theorem freshDominates_of_channel [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    (hch : ∀ i j, T.channel m.apply i j ⊆ T.channel W i j) : FreshDominates T m.apply W :=
  ⟨⟨m.endState_apply, m.visitedStates_subset, hch⟩, m.fresh_apply hfr⟩

end BlockDeletion

end DeciSigma1.Holes.Fresh
