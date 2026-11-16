/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Fresh.DeletionCoordinates
import Mathlib.Order.SuccPred.Nat
import Mathlib.Data.Finset.Max

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Transport of channel pairs through a block deletion

A pair in a channel of the edited tuple compares, at cuts `a` and `b`, a suffix of a host word
with a suffix of a target word. To show that it lies in the original channel, the comparison is
moved back to the original words. The deleted texts sit at a fixed depth in every upper
occurrence that traverses the edge of the deletion. The main step is that a text of
`upperCutLength` letters that ends at the end of a traversing occurrence forces every other
upper occurrence ending with the same text to traverse the edge as well
(`traversedBy_of_text_eq`). Hence a junction inside one of the compared texts is
matched by a junction at the same position in the other (`transfer`), and the comparison of
edited texts is a comparison of original texts read at the corresponding cuts.

## Main declarations

- `BlockDeletion.upperCutLength`, `BlockDeletion.deletedText`: the length of the text after a
  deletion site in a traversing occurrence, and the deleted text.
- `BlockDeletion.endMarker`: the marker that ends a traversing occurrence lies within its
  last `minDepth` lower blocks.
- `BlockDeletion.traversedBy_of_text_eq`: a text ending at the end of a traversing
  occurrence determines traversal.
- `BlockDeletion.transfer`: junctions are matched across a comparison.
-/

@[expose] public section


namespace DeciSigma1.Holes.Fresh

open DeciSigma1.Readers DeciSigma1.Words
open Finset

/-! ## Deletion sites, junctions and windows -/

section Sites

variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]

namespace BlockDeletion

variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)

/-- The total length of the last `minDepth` lower blocks of a traversing occurrence: the length
of the text between a deletion site and the end of the occurrence. -/
def upperCutLength : ℕ := firstBlocksLength m.edge.blocks.reverse m.minDepth

/-- The deleted text, common to all sites: the lower blocks of depths
`minDepth, …, maxDepth - 1`. -/
def deletedText :
    List α := (((m.edge.blocks.reverse.take m.maxDepth).drop m.minDepth).reverse).flatten

theorem minDepth_le_endDepth :
    m.minDepth ≤
        m.edge.endDepth := by have := m.minDepth_lt_maxDepth; have := m.maxDepth_lt_endDepth;
                              omega

theorem upperCutLength_spec {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : m.edge.TraversedBy o) :
    depthCut W t o m.minDepth + m.upperCutLength = o.2.2 ∧ depthCut W t o m.maxDepth +
        m.deletionLength +
        m.upperCutLength = o.2.2 ∧
      0 < m.upperCutLength := by
  have h1 := m.edge.depthCut_through ho hth m.minDepth_le_endDepth
  have h2 := m.site_spec ho hth
  refine ⟨h1, by unfold upperCutLength; omega, by unfold upperCutLength; omega⟩

theorem site_occ {l : Fin k} {c : ℕ} (hc : c ∈ m.sites l) :
    ∃ o ∈ upperOccurrences W t, o.1 = l ∧ m.edge.TraversedBy o ∧ depthCut W t o m.maxDepth = c :=
  m.mem_sites.mp hc

theorem site_text {l : Fin k} {c : ℕ} (hc : c ∈ m.sites l) :
    c + m.deletionLength < (W l).length ∧ ((W l).drop c).take m.deletionLength = m.deletedText := by
  refine ⟨(m.site_valid hc).2.1, ?_⟩
  obtain ⟨o, ho, rfl, hth, rfl⟩ := m.site_occ hc
  have hsp := m.site_spec ho hth
  have hbn := (m.edge.through_iff.mp hth)
  have hjn : m.maxDepth ≤ lowerBlockCount W t o := by have := m.maxDepth_lt_endDepth; omega
  have ht := text_depthCut ho m.minDepth_lt_maxDepth.le hjn
  rw [show depthCut W t o m.minDepth - depthCut W t o m.maxDepth = m.deletionLength
      by omega] at ht
  rw [ht, deletedText]
  congr 3
  rw [show (reversedBlocks W t o).take m.maxDepth =
      ((reversedBlocks W t o).take m.edge.endDepth).take m.maxDepth by
      rw [List.take_take, Nat.min_eq_left m.maxDepth_lt_endDepth.le], hbn.2, List.take_take,
    Nat.min_eq_left m.maxDepth_lt_endDepth.le]

/-- Of two sites of one word, the upper block of the earlier one ends before that of the later one
starts. -/
theorem site_order {o o' : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (ho' : o' ∈ upperOccurrences W t) (hth : m.edge.TraversedBy o) (hth' : m.edge.TraversedBy o')
        (hl : o.1 = o'.1)
    (hlt : depthCut W t o m.maxDepth < depthCut W t o' m.maxDepth) : o.2.2 ≤ o'.2.1 := by
  have s1 := m.site_spec ho hth
  have s2 := m.site_spec ho' hth'
  rcases lt_trichotomy o.2.2 o'.2.2 with h | h | h
  · exact upperOccurrences_le_start ho ho' hl h
  · have := upperOcc_ext ho ho' hl h; subst this; omega
  · have := upperOccurrences_le_start ho' ho hl.symm h; omega

/-- A word with an upper occurrence that traverses the edge is active at level `t + 1`. -/
theorem active_of_through {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : m.edge.TraversedBy o) : o.1 ∈ active W (t + 1) := by
  have hbn := (m.edge.through_iff.mp hth).1
  have h2 : 1 <
      lowerBlockCount W t o := by have := m.maxDepth_lt_endDepth; have := m.one_le_minDepth;
                                  have := m.minDepth_lt_maxDepth; omega
  obtain ⟨hall, -⟩ := depthCut_spec ho
  obtain ⟨hA, -, -, -⟩ := hall 1 h2
  have hlt : depthCut W t o 1 < depthCut W t o 0 := depthCut_lt ho (d := 0) (by omega)
  have hE := (upperOcc_spec ho).2.1
  have hd0 : depthCut W t o 0 = o.2.2 := rfl
  rcases t with _ | t
  · exact (mem_active_one W).mpr (ne_nil_of_mem_upperOccurrences ho)
  · by_cases hact : o.1 ∈ active W (t + 1)
    · exact (mem_active_succ_succ W).mpr ⟨hact, _, hA, by omega⟩
    · exfalso
      rcases t with _ | t
      · exact hact ((mem_active_one W).mpr (ne_nil_of_mem_upperOccurrences ho))
      · have hsing := anchors_eq_singleton (t := t + 1) (by omega) hact
        have := anchors_succ_subset (t + 1) o.1 hA
        rw [hsing, mem_singleton] at this
        omega

theorem active_t_of_through {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    (hth : m.edge.TraversedBy o) : o.1 ∈ active W t :=
  active_succ_subset W t (m.active_of_through ho hth)

/-- A set that contains the cuts at depths `0, …, D` of an upper occurrence has at least `D + 1`
elements. -/
theorem card_depthCuts {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    {D : ℕ} (hD : D ≤ lowerBlockCount W t o) {X : Finset ℕ} (hX : ∀ d ≤ D, depthCut W t o d ∈ X) :
    D + 1 ≤ X.card := by
  have hinj : Set.InjOn (depthCut W t o) (range (D + 1)) := by
    intro d hd d' hd' he
    simp only [coe_range, Set.mem_Iio] at hd hd'
    by_contra hne'
    rcases Nat.lt_or_gt_of_ne hne' with h | h
    · exact absurd he (depthCut_lt_of_lt ho h (by omega)).ne'
    · exact absurd he (depthCut_lt_of_lt ho h (by omega)).ne
  calc D + 1 = ((range (D + 1)).image (depthCut W t o)).card := by
        rw [card_image_of_injOn hinj, card_range]
    _ ≤ X.card := card_le_card (fun p hp => by
        obtain ⟨d, hd, rfl⟩ := mem_image.mp hp
        exact hX d (by simp at hd; omega))

theorem depthCut_anti {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t)
    {d d' : ℕ} (h : d ≤ d') (hd' : d' ≤ lowerBlockCount W t o) : depthCut W t o d' ≤
        depthCut W t o d := by
  rcases Nat.eq_or_lt_of_le h with h | h
  · rw [h]
  · exact (depthCut_lt_of_lt ho h hd').le

theorem deletionMargin_gt
    (hlt : m.edge.startDepth + deletionMargin k (Fintype.card S) ≤ m.minDepth) :
    k * (Fintype.card S - 1) + 4 + m.edge.startDepth < m.minDepth := by
  unfold deletionMargin at hlt; omega

/-- The marker of level `t + 1` that ends a traversing occurrence lies within its last
`minDepth` lower blocks, by the bound on anchors inside a marker and the deletion margin. -/
theorem endMarker [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) (hth : m.edge.TraversedBy o) :
    ∃ g ∈ active W (t + 1), marker W (t + 1) g <:+ (W o.1).take o.2.2 ∧
      (marker W (t + 1) g).length ≤ m.upperCutLength := by
  have hact := m.active_of_through ho hth
  have hE := (mem_upperOcc.mp ho).2.1
  rw [anchors_eq_contextAnchors hact] at hE
  obtain ⟨-, g, hg, hs⟩ := (mem_contextAnchors_succ W).mp hE
  refine ⟨g, hg, hs, Nat.le_of_not_lt fun hlong => ?_⟩
  have hEl := (upperOcc_spec ho).2.1
  obtain ⟨hl1, hocc⟩ := (suffix_take_iff hEl).mp hs
  have hsp := card_anchors_Ioc_marker_le hfr t hg (W o.1) hocc
  have hnt := m.upperCutLength_spec ho hth
  have hbn := (m.edge.through_iff.mp hth).1
  have hin : m.minDepth ≤ lowerBlockCount W t o := by have := m.minDepth_le_endDepth; omega
  have hctx := anchors_eq_contextAnchors (m.active_t_of_through ho hth)
  have := card_depthCuts ho hin (X := (contextAnchors W t (W o.1)).filter
    (fun p => o.2.2 - (marker W (t + 1) g).length < p ∧
      p ≤ o.2.2 - (marker W (t + 1) g).length + (marker W (t + 1) g).length)) (by
    intro d hd
    rw [mem_filter, ← hctx]
    have h1 := depthCut_anti ho hd hin
    have h2 := depthCut_anti ho (Nat.zero_le d) (hd.trans hin)
    obtain ⟨hall, -⟩ := depthCut_spec ho
    have := m.minDepth_lt_maxDepth; have := m.maxDepth_lt_endDepth
    exact ⟨(hall d (by omega)).1, by rw [show depthCut W t o 0 = o.2.2 from rfl] at h2; omega,
      by rw [show depthCut W t o 0 = o.2.2 from rfl] at h2; omega⟩)
  have := m.deletionMargin_gt m.left_margin
  omega

/-- Upper anchors are not cuts of a site: sites lie strictly inside upper blocks. -/
theorem anchor_ne_site {l : Fin k} {p c : ℕ}
    (hp : p ∈ anchors W (t + 1) l) (hc : c ∈ m.sites l) : p ≠ c ∧ p ≠ c + m.deletionLength := by
  obtain ⟨o, ho, rfl, hth, rfl⟩ := m.site_occ hc
  have hsp := m.site_spec ho hth
  have hno := (upperOcc_spec ho).2.2.2.2 p hp
  constructor <;> rintro rfl <;> exact hno ⟨by omega, by omega⟩

/-- At the junction `J` of a site `c`, the greatest preimage is `c + δ`, the next
`upperCutLength` letters are original text up to the end of the upper block, and no other
junction of the word lies in `(J, J + upperCutLength)`. -/
theorem junction_window {l : Fin k} {c : ℕ} (hc : c ∈ m.sites l) :
    greatestPreimage (sitePositions m.deletionLength (m.sites l))
        (retainedCount (sitePositions m.deletionLength (m.sites l)) c) = c + m.deletionLength ∧
    (∀ J', IsJunction m.deletionLength (m.sites l) J' →
      J' ≤ retainedCount (sitePositions m.deletionLength (m.sites l)) c ∨
        retainedCount (sitePositions m.deletionLength (m.sites l)) c + m.upperCutLength ≤ J') ∧
    retainedCount (sitePositions m.deletionLength (m.sites l)) c + m.upperCutLength ≤
      (m.apply l).length ∧
    ((m.apply l).drop (retainedCount (sitePositions m.deletionLength (m.sites l)) c)).take
        m.upperCutLength =
      ((W l).drop (c + m.deletionLength)).take m.upperCutLength := by
  have hδ := m.delta_pos
  have hs := m.strictlySeparated l
  set cs := m.sites l with hcs
  obtain ⟨o, ho, hol, hth, hoc⟩ := m.site_occ hc
  have hnt := m.upperCutLength_spec ho hth
  rw [hoc] at hnt
  have hEl := (upperOcc_spec ho).2.1
  rw [hol] at hEl
  -- every other site is left of `c` or right of the end of its upper block
  have hother : ∀ c' ∈ cs, c' < c ∨ c' = c ∨ o.2.2 < c' := by
    intro c' hc'
    rcases lt_trichotomy c' c with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · right; right
      obtain ⟨o', ho', hol', hth', hoc'⟩ := m.site_occ hc'
      have := m.site_order ho ho' hth hth' (hol.trans hol'.symm) (by rw [hoc, hoc']; exact h)
      have := m.site_spec ho' hth'
      omega
  have hretE : Retained m.deletionLength cs o.2.2 := by
    intro c' hc' ⟨h1, h2⟩
    rcases hother c' hc' with h | h | h
    · have := hs.lt hc' hc h; omega
    · omega
    · omega
  have hretc' : Retained m.deletionLength cs (c + m.deletionLength) := by
    intro c' hc' ⟨h1, h2⟩
    rcases hother c' hc' with h | h | h
    · have := hs.lt hc' hc h; omega
    · omega
    · omega
  have hkE : retainedCount (sitePositions m.deletionLength cs) o.2.2 =
      retainedCount (sitePositions m.deletionLength cs) c + m.upperCutLength := by
    rw [retainedCount_dist hretc' (q := o.2.2) (by omega) (fun c' hc' ⟨h1, h2⟩ => by
      rcases hother c' hc' with h | h | h <;> omega), retainedCount_site_right hc]
    congr 1; omega
  have j2 := greatestPreimage_site hs hc
  have hsep : ∀ J', IsJunction m.deletionLength cs J' →
      J' ≤ retainedCount (sitePositions m.deletionLength cs) c ∨
        retainedCount (sitePositions m.deletionLength cs) c + m.upperCutLength ≤ J' := by
    rintro J' ⟨c', hc', rfl⟩
    rcases hother c' hc' with h | h | h
    · exact Or.inl (retainedCount_mono h.le)
    · exact Or.inl (by rw [h])
    · exact Or.inr (hkE ▸ retainedCount_mono h.le)
  refine ⟨j2, hsep, ?_, ?_⟩
  · rw [← hkE, BlockDeletion.apply, length_deletePositions]
    exact retainedCount_mono hEl
  · rw [← j2]
    refine take_drop_deleteSites _ (fun J' hJ' ⟨h1, h2⟩ => ?_)
    rcases hsep J' hJ' with h | h <;> omega

private theorem anchorCount_min_eq_card (Q : Finset ℕ) (hQ : Q.Nonempty) {n : ℕ}
    (hQle : ∀ q ∈ Q, q ≤ n) : anchorCount Q (Q.min' hQ) n + 1 = Q.card := by
  have hqmQ := Q.min'_mem hQ
  have hf : Q.filter (fun q => Q.min' hQ < q ∧ q ≤ n) = Q.erase (Q.min' hQ) := by
    ext q
    simp only [mem_filter, mem_erase]
    constructor
    · rintro ⟨hq, h1, -⟩; exact ⟨by omega, hq⟩
    · rintro ⟨h1, hq⟩
      exact ⟨hq, lt_of_le_of_ne (Q.min'_le q hq) (Ne.symm h1), hQle q hq⟩
  rw [anchorCount, hf, card_erase_of_mem hqmQ]
  have := card_pos.mpr hQ
  omega

private theorem reversedBlocks_take_eq_of_depthCuts
    {W : Fin k → List α} {t : ℕ} {o₁ o₂ : Fin k × ℕ × ℕ}
    {Q : Finset ℕ} {qm n c₁ c₂ D : ℕ} {z : List α}
    (hqmQ : qm ∈ Q) (hnQ : n ∈ Q) (hqmn : qm ≤ n) (hDdef : D = anchorCount Q qm n)
    (hnlow₁ : D ≤ lowerBlockCount W t o₁) (hnlow₂ : D ≤ lowerBlockCount W t o₂)
    (hdc₁ : ∀ d ≤ D, depthCut W t o₁ d = c₁ + depthCutAt Q n d)
    (hdc₂ : ∀ d ≤ D, depthCut W t o₂ d = c₂ + depthCutAt Q n d)
    (hz₁ : ((W o₁.1).drop c₁).take n = z) (hz₂ : ((W o₂.1).drop c₂).take n = z) :
    (reversedBlocks W t o₁).take D = (reversedBlocks W t o₂).take D := by
  have hr : ∀ d < D, depthCutAt Q n (d + 1) < depthCutAt Q n d ∧ depthCutAt Q n d ≤ n := by
    intro d hd
    have hlt : qm < n := by
      rcases Nat.eq_or_lt_of_le hqmn with h | h
      · rw [hDdef, h, anchorCount_self] at hd; omega
      · exact h
    obtain ⟨hall, -⟩ := depthCutAt_spec hlt hnQ (Or.inr hqmQ)
    obtain ⟨hrQ, hlr, hrn, -⟩ := hall d (by omega)
    exact ⟨(previousAnchor_spec ⟨qm, hqmQ, hlr⟩).2, hrn⟩
  apply List.ext_getElem
  · simp only [List.length_take, length_reversedBlocks]; omega
  · intro d h1 h2
    have hd : d < D := by simp only [List.length_take, length_reversedBlocks] at h1; omega
    obtain ⟨hlt, hle⟩ := hr d hd
    simp only [List.getElem_take, getElem_reversedBlocks]
    rw [hdc₁ d hd.le, hdc₁ (d + 1) hd, hdc₂ d hd.le, hdc₂ (d + 1) hd,
      Nat.add_sub_add_left, Nat.add_sub_add_left,
      segment_eq hz₁ hlt.le hle, segment_eq hz₂ hlt.le hle]

/-- Let `o₁` be a traversing occurrence and `z` its last `upperCutLength` letters. If `z` also
ends at an upper anchor `p₂` of a word `l₂`, then the upper occurrence of `l₂` ending at `p₂`
traverses the edge too: its parse agrees with that of `o₁` on at least
`minDepth - k (N - 1) - 1 > startDepth` lower blocks, the anchors of `z` alone, which do not
depend on the context; and the length of its common suffix with the parse of the edge is a trie
node, hence at least `endDepth`. This is a statement about the original tuple. -/
theorem traversedBy_of_text_eq [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {o₁ : Fin k × ℕ × ℕ} (ho₁ : o₁ ∈ upperOccurrences W t) (hth : m.edge.TraversedBy o₁)
    {l₂ : Fin k} {p₂ : ℕ} (hp₂ : p₂ ∈ anchors W (t + 1) l₂) (hn : m.upperCutLength ≤ p₂)
    (hz : ((W l₂).drop (p₂ - m.upperCutLength)).take m.upperCutLength =
      ((W o₁.1).drop (o₁.2.2 - m.upperCutLength)).take m.upperCutLength) :
    m.edge.TraversedBy (l₂, upperOccurrenceStart W t l₂ p₂, p₂) := by
  obtain ⟨hnt1, -, hnpos⟩ := m.upperCutLength_spec ho₁ hth
  have hE₁ := (upperOcc_spec ho₁).2.1
  have hbn := (m.edge.through_iff.mp hth).1
  have hin : m.minDepth <
      lowerBlockCount W t o₁ := by have := m.minDepth_lt_maxDepth;
                                   have := m.maxDepth_lt_endDepth; omega
  obtain ⟨hall₁, -⟩ := depthCut_spec ho₁
  have hs₁c : o₁.2.1 < depthCut W t o₁ m.minDepth := (hall₁ m.minDepth hin).2.1
  have hcnt : anchorCount (anchors W t o₁.1) (depthCut W t o₁ m.minDepth) o₁.2.2 = m.minDepth :=
    (hall₁ m.minDepth hin).2.2.2
  have hp₂len : p₂ ≤ (W l₂).length := le_length_of_mem_anchors hp₂
  have hl₂ : W l₂ ≠ [] := List.ne_nil_of_length_pos (by omega)
  have hmg := m.deletionMargin_gt m.left_margin
  set n := m.upperCutLength with hndef
  set E₁ := o₁.2.2 with hE₁def
  set c₁ := E₁ - n with hc₁def
  have hc₁ : depthCut W t o₁ m.minDepth = c₁ := by omega
  rw [hc₁] at hs₁c hcnt
  set z := ((W o₁.1).drop c₁).take n with hzdef
  have hzlen : z.length = n := by simp [hzdef]; omega
  set u₁ := (W o₁.1).take c₁ with hu₁def
  set u₂ := (W l₂).take (p₂ - n) with hu₂def
  have hact₁ := m.active_t_of_through ho₁ hth
  have hanc₁ := anchors_eq_contextAnchors hact₁
  set Q := contextAnchors W t z with hQ
  have hrel : ∀ u, relativeAnchors W t u z = Q ∪ crossBoundaryMarkerEnds W t u z :=
      fun u => relativeAnchors_eq_union t u z
  have hQle : ∀ q ∈ Q, q ≤ n := fun q hq => hzlen ▸ contextAnchors_le_length hq
  have hA₁ : ∀ q, 1 ≤ q → q ≤ n →
      (c₁ + q ∈ anchors W t o₁.1 ↔ q ∈ Q ∪ crossBoundaryMarkerEnds W t u₁ z) := by
    intro q h1 h2
    rw [← hrel, mem_relAnchors_iff rfl (by omega) h1 h2, hanc₁]
  have hA₂ : ∀ q, 1 ≤ q → q < n →
      (p₂ - n + q ∈ anchors W t l₂ ↔ q ∈ Q ∪ crossBoundaryMarkerEnds W t u₂ z) := by
    intro q h1 h2
    rw [← hrel, mem_relAnchors_iff hz (by omega) h1 h2.le]
    exact
        ⟨fun h => mem_contextAnchors_of_mem_anchors_of_lt_length h (by omega),
            fun h => mem_insert_of_mem h⟩
  -- counting: at least `i - k (N - 1)` inside anchors
  have hcardSO : (crossBoundaryMarkerEnds W t u₁ z).card ≤ k * (Fintype.card S - 1) :=
    (card_le_card (crossBoundaryMarkerEnds_subset_prefixOccurrenceCuts u₁ z)).trans
        (card_prefixOccurrenceCuts_le hfr z)
  have hcardQ : m.minDepth ≤ Q.card + k * (Fintype.card S - 1) := by
    have hsub : (anchors W t o₁.1).filter (fun p => c₁ < p ∧ p ≤ E₁) ⊆
        (Q ∪ crossBoundaryMarkerEnds W t u₁ z).image (c₁ + ·) := by
      intro p hp
      rw [mem_filter] at hp
      rw [mem_image]
      refine ⟨p - c₁, (hA₁ (p - c₁) (by omega) (by omega)).mp ?_, by omega⟩
      rw [Nat.add_sub_cancel' (by omega)]; exact hp.1
    have h1 := card_le_card hsub
    have h2 := card_image_le (s := Q ∪ crossBoundaryMarkerEnds W t u₁ z) (f := (c₁ + ·))
    have h3 := card_union_le Q (crossBoundaryMarkerEnds W t u₁ z)
    unfold anchorCount at hcnt
    omega
  have hnQ : n ∈ Q := by
    have hE : c₁ + n ∈ anchors W t o₁.1 := by
      rw [show c₁ + n = E₁ by omega]; exact (upperOcc_spec ho₁).2.2.1
    rcases mem_union.mp ((hA₁ n hnpos le_rfl).mp hE) with h | h
    · exact h
    · exfalso
      have hQe : Q = ∅ := by
        rw [eq_empty_iff_forall_notMem]
        intro q hq
        have := crossBoundaryMarkerEnds_lt_inside h hq
        have := hQle q hq
        omega
      rw [hQe, card_empty] at hcardQ
      omega
  have hQne : Q.Nonempty := ⟨n, hnQ⟩
  set qm := Q.min' hQne with hqmdef
  have hqmQ : qm ∈ Q := Q.min'_mem hQne
  have hqm_le : ∀ q ∈ Q, qm ≤ q := fun q hq => Q.min'_le q hq
  have hqm1 : 1 ≤ qm := contextAnchors_pos hqmQ
  have hqmn : qm ≤ n := hqm_le n hnQ
  -- from the first inside anchor on, the anchors in `z` are those of `z` alone
  have hcross : ∀ u q, qm ≤ q → (q ∈ Q ∪ crossBoundaryMarkerEnds W t u z ↔ q ∈ Q) := by
    refine fun u q h1 => ⟨fun h => (mem_union.mp h).elim id fun h => ?_, mem_union_left _⟩
    have := crossBoundaryMarkerEnds_lt_inside h hqmQ
    omega
  have hag₁ : ∀ q, qm ≤ q → q ≤ n → (c₁ + q ∈ anchors W t o₁.1 ↔ q ∈ Q) := fun q h1 h2 => by
    rw [hA₁ q (by omega) h2, hcross _ q h1]
  have hag₂ : ∀ q, qm ≤ q → q ≤ n → (p₂ - n + q ∈ anchors W t l₂ ↔ q ∈ Q) := by
    intro q h1 h2
    rcases Nat.lt_or_ge q n with hlt | hge
    · rw [hA₂ q (by omega) hlt, hcross _ q h1]
    · have hq : q = n := by omega
      rw [hq, Nat.sub_add_cancel hn]
      exact ⟨fun _ => hnQ, fun _ => anchors_succ_subset t l₂ hp₂⟩
  set D := anchorCount Q qm n with hDdef
  have hdc₁ : ∀ d ≤ D, depthCut W t o₁ d = c₁ + depthCutAt Q n d := by
    intro d hd
    have := depthCutAt_shift hag₁ hqmQ hnQ hqmn d hd
    rw [show c₁ + n = E₁ by omega] at this
    exact this
  have hdc₂ : ∀ d ≤ D, depthCutAt (anchors W t l₂) p₂ d = p₂ - n + depthCutAt Q n d := by
    intro d hd
    have := depthCutAt_shift hag₂ hqmQ hnQ hqmn d hd
    rwa [Nat.sub_add_cancel hn] at this
  have hD : D + 1 = Q.card := anchorCount_min_eq_card Q hQne hQle
  -- the target's upper boundary is at or before the first inside anchor
  have hz' : ((W l₂).drop (p₂ - n)).take n = z := hz
  have hs₂ : upperOccurrenceStart W t l₂ p₂ ≤ p₂ - n + qm := by
    by_contra! hcon
    have hex : ∃ q ∈ anchors W (t + 1) l₂, q < p₂ := by
      by_contra hno
      have : upperOccurrenceStart W t l₂ p₂ ≤ 0 :=
        previousAnchor_le (fun q hq hqp => absurd ⟨q, hq, hqp⟩ hno)
      omega
    obtain ⟨hs₂A, hs₂p⟩ : upperOccurrenceStart W t l₂ p₂ ∈ anchors W (t + 1) l₂ ∧
        upperOccurrenceStart W t l₂ p₂ < p₂ := previousAnchor_spec hex
    have hs₂ctx := mem_contextAnchors_of_mem_anchors_of_lt_length hs₂A (by omega)
    obtain ⟨-, g, hg, hσ⟩ := (mem_contextAnchors_succ W).mp hs₂ctx
    set s₂ := upperOccurrenceStart W t l₂ p₂ with hs₂def
    have hσ' : marker W (t + 1) g <:+ (W l₂).take s₂ := hσ
    set d₂ := s₂ - (p₂ - n) with hd₂def
    have htk₂ : (W l₂).take s₂ = u₂ ++ z.take d₂ := by
      rw [show s₂ = (p₂ - n) + d₂ by omega, List.take_add, ← hz', List.take_take,
        Nat.min_eq_left (by omega)]
    obtain ⟨hσl, hσo⟩ := (suffix_take_iff (by omega)).mp hσ'
    rcases Nat.lt_or_ge d₂ (marker W (t + 1) g).length with hlong | hshort
    · -- the upper marker starts left of `z`: the factor antichain property bounds the anchors
      have ht : 1 ≤ t := by
        by_contra ht0
        have h0 : t = 0 := by omega
        have h1 : (marker W (t + 1) g).length = 1 := by
          rw [h0] at hg ⊢; exact length_marker_one hg
        omega
      have hge : ∀ q ∈ Q, d₂ ≤ q := by
        intro q hq
        by_contra hql
        have hql' : q < d₂ := Nat.lt_of_not_le hql
        obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
        obtain ⟨hqz, h, hh, hμ⟩ := (mem_contextAnchors_succ W).mp hq
        have hμl : (marker W (t' + 1) h).length ≤ q := by
          have := hμ.length_le; simp only [List.length_take] at this; omega
        have hμ₂ : marker W (t' + 1) h <:+ (W l₂).take (p₂ - n + q) := by
          rw [List.take_add, show ((W l₂).drop (p₂ - n)).take q = z.take q by
            rw [← hz', List.take_take, Nat.min_eq_left (by omega)]]
          exact hμ.trans (List.suffix_append _ _)
        obtain ⟨-, hμo⟩ := (suffix_take_iff (by omega)).mp hμ₂
        have hin' := prefix_drop_of_occ hσo hμo (by omega) (by omega)
        rcases (marker_occurrences_in_next_marker (by omega) hg).2.2 h hh _ hin' with
          h1 | h1 <;> omega
      have := hge qm hqmQ
      omega
    · -- the upper marker is inside `z`: an upper anchor strictly inside `o₁`
      have hσz : marker W (t + 1) g <:+ z.take d₂ := by
        rw [htk₂] at hσ'
        exact List.suffix_of_suffix_length_le hσ' (List.suffix_append _ _) (by simp; omega)
      have hσ₁ : marker W (t + 1) g <:+ (W o₁.1).take (c₁ + d₂) := by
        rw [List.take_add, show ((W o₁.1).drop c₁).take d₂ = z.take d₂ by
          rw [hzdef, List.take_take, Nat.min_eq_left (by omega)]]
        exact hσz.trans (List.suffix_append _ _)
      have hanc : c₁ + d₂ ∈ anchors W (t + 1) o₁.1 :=
        mem_insert_of_mem ((mem_contextAnchors_succ W).mpr ⟨by omega, g, hg, hσ₁⟩)
      exact (upperOcc_spec ho₁).2.2.2.2 _ hanc ⟨by omega, by omega⟩
  have ho₂ : (l₂, upperOccurrenceStart W t l₂ p₂, p₂) ∈ upperOccurrences W t :=
      mem_upperOcc.mpr ⟨hl₂, hp₂, rfl⟩
  have hnlow₂ : D ≤ lowerBlockCount W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂) := by
    have h1 := anchorCount_shift (A := anchors W t l₂) hag₂
    rw [Nat.sub_add_cancel hn] at h1
    have h2 := anchorCount_anti (A := anchors W t l₂) (e := p₂) hs₂
    change D ≤ anchorCount (anchors W t l₂) (upperOccurrenceStart W t l₂ p₂) p₂
    omega
  have hnlow₁ : D ≤ lowerBlockCount W t o₁ := by
    have h1 := anchorCount_shift (A := anchors W t o₁.1) hag₁
    rw [show c₁ + n = E₁ by omega] at h1
    have h2 := anchorCount_anti (A := anchors W t o₁.1) (e := E₁) (show o₁.2.1 ≤ c₁ + qm by omega)
    change D ≤ anchorCount (anchors W t o₁.1) o₁.2.1 E₁
    omega
  have htake : (reversedBlocks W t o₁).take D =
      (reversedBlocks W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂)).take D :=
    reversedBlocks_take_eq_of_depthCuts hqmQ hnQ hqmn hDdef hnlow₁ hnlow₂
      hdc₁ hdc₂ hzdef.symm hz'
  have hlcs : D ≤
      commonSuffixLength (upperParse W t o₁)
          (upperParse W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂)) := by
    unfold commonSuffixLength upperParse
    rw [List.reverse_reverse, List.reverse_reverse, le_commonPrefixLength_iff]
    simp only [length_reversedBlocks]
    exact ⟨hnlow₁, hnlow₂, htake⟩
  have hDa : m.edge.startDepth < D := by omega
  have hb₁ : m.edge.endDepth ≤ commonSuffixLength (upperParse W t o₁) m.edge.blocks := hth
  have hmin :=
      min_le_commonSuffixLength m.edge.blocks (upperParse W t o₁)
          (upperParse W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂))
  rw [commonSuffixLength_comm m.edge.blocks (upperParse W t o₁)] at hmin
  have hlow : m.edge.startDepth <
      commonSuffixLength m.edge.blocks (upperParse W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂)) :=
    lt_of_lt_of_le (lt_min (by have := m.edge.startDepth_lt_endDepth; omega) (by omega)) hmin
  unfold Edge.TraversedBy
  by_contra hcon
  have hY : upperParse W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂) ∈ upperParses W t :=
      mem_image_of_mem _ ho₂
  have := m.edge.commonSuffixLength_le_startDepth hY (by rw [commonSuffixLength_comm]; omega)
  omega

/-- Let `u₁` be a junction of word `l₁`, and let the edited word `l₂` have the same text of
`upperCutLength` letters from `u₂`, with no junction strictly inside. Then `u₂` is a junction of
`l₂`. -/
theorem transfer [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {l₁ l₂ : Fin k} {u₁ u₂ : ℕ} (hJ : IsJunction m.deletionLength (m.sites l₁) u₁)
    (htext : ((m.apply l₁).drop u₁).take m.upperCutLength =
        ((m.apply l₂).drop u₂).take m.upperCutLength)
    (hfree : ∀ J,
        IsJunction m.deletionLength (m.sites l₂) J → ¬ (u₂ < J ∧ J < u₂ + m.upperCutLength))
    (hlen : u₂ + m.upperCutLength ≤ (m.apply l₂).length) :
    IsJunction m.deletionLength (m.sites l₂) u₂ := by
  obtain ⟨c₁, hc₁, rfl⟩ := hJ
  obtain ⟨o₁, ho₁, hol₁, hth₁, hoc₁⟩ := m.site_occ hc₁
  obtain ⟨-, -, -, hwin₁⟩ := m.junction_window hc₁
  obtain ⟨hnt1, hnt2, hnpos⟩ := m.upperCutLength_spec ho₁ hth₁
  obtain ⟨g, hg, hσE, hσl⟩ := m.endMarker hfr ho₁ hth₁
  rw [hoc₁] at hnt2
  have hE₁ := (upperOcc_spec ho₁).2.1
  rw [hol₁] at hE₁ hσE
  have hσz : marker W (t + 1) g <:+
      ((W l₁).drop (c₁ + m.deletionLength)).take m.upperCutLength := by
    have hcat : (W l₁).take o₁.2.2 =
        (W l₁).take (c₁ + m.deletionLength) ++
            ((W l₁).drop (c₁ + m.deletionLength)).take m.upperCutLength := by
      rw [← List.take_add]; congr 1; omega
    rw [hcat] at hσE
    exact List.suffix_of_suffix_length_le hσE (List.suffix_append _ _) (by simp; omega)
  have hσU : marker W (t + 1) g <:+ (m.apply l₂).take (u₂ + m.upperCutLength) := by
    rw [List.take_add, ← htext, hwin₁]
    exact hσz.trans (List.suffix_append _ _)
  have hanc : u₂ + m.upperCutLength ∈ contextAnchors W (t + 1) (m.apply l₂) :=
    (mem_contextAnchors_succ W).mpr ⟨hlen, g, hg, hσU⟩
  obtain ⟨p₂, hp₂, hret, hkp⟩ :=
      (m.contextAnchors_apply (r := t + 1) (by omega) le_rfl l₂ _).mp hanc
  have hp₂A : p₂ ∈ anchors W (t + 1) l₂ := mem_insert_of_mem hp₂
  have hs := m.strictlySeparated l₂
  have hδ := m.delta_pos
  have hka : greatestPreimage (sitePositions m.deletionLength (m.sites l₂)) u₂ + m.upperCutLength =
      p₂ :=
    greatestPreimage_add_eq hnpos hfree hret (fun c hc => (m.anchor_ne_site hp₂A hc).2) hkp
  have hwin₂ : ((m.apply l₂).drop u₂).take m.upperCutLength =
      ((W l₂).drop (greatestPreimage (sitePositions m.deletionLength (m.sites l₂)) u₂)).take
        m.upperCutLength :=
    take_drop_deleteSites _ hfree
  have hz₂ : ((W l₂).drop (p₂ - m.upperCutLength)).take m.upperCutLength =
      ((W o₁.1).drop (o₁.2.2 - m.upperCutLength)).take m.upperCutLength := by
    rw [show p₂ - m.upperCutLength =
          greatestPreimage (sitePositions m.deletionLength (m.sites l₂)) u₂ by omega,
        ← hwin₂,
        ← htext, hwin₁,
      hol₁, show o₁.2.2 - m.upperCutLength = c₁ + m.deletionLength by omega]
  have hthr := m.traversedBy_of_text_eq hfr ho₁ hth₁ hp₂A (by omega) hz₂
  have hl₂ : W l₂ ≠ [] :=
    List.ne_nil_of_length_pos (by have := le_length_of_mem_anchors hp₂A; omega)
  have ho₂ : (l₂, upperOccurrenceStart W t l₂ p₂, p₂) ∈ upperOccurrences W t :=
      mem_upperOcc.mpr ⟨hl₂, hp₂A, rfl⟩
  obtain ⟨-, hn2', -⟩ := m.upperCutLength_spec ho₂ hthr
  have hE2 : (l₂, upperOccurrenceStart W t l₂ p₂, p₂).2.2 = p₂ := rfl
  rw [hE2] at hn2'
  have hc₂ : depthCut W t (l₂, upperOccurrenceStart W t l₂ p₂, p₂) m.maxDepth ∈ m.sites l₂ :=
    m.mem_sites.mpr ⟨_, ho₂, rfl, hthr, rfl⟩
  refine ⟨_, hc₂, ?_⟩
  rw [← retainedCount_site_right hc₂, show depthCut W t (l₂, upperOccurrenceStart W t l₂ p₂,
      p₂) m.maxDepth + m.deletionLength =
    greatestPreimage (sitePositions m.deletionLength (m.sites l₂)) u₂ by omega]
  exact retainedCount_greatestPreimage u₂

/-- Two junctions of one word are at least `upperCutLength` apart. -/
theorem junction_sep {l : Fin k} {u u' : ℕ} (hu : IsJunction m.deletionLength (m.sites l) u)
        (hu' : IsJunction m.deletionLength (m.sites l) u')
        (hlt : u < u') :
    u + m.upperCutLength ≤ u' := by
  obtain ⟨c, hc, rfl⟩ := hu
  rcases (m.junction_window hc).2.1 u' hu' with h | h
  · omega
  · exact h

end BlockDeletion

end Sites

end DeciSigma1.Holes.Fresh
