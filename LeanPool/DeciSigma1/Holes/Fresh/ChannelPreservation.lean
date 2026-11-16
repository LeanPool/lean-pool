/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Fresh.ChannelTransport

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Block deletions preserve channels

A channel pair of the edited tuple compares suffixes of two edited words. If no junction lies
strictly inside the comparison, or if the junctions inside correspond on both sides
(`BlockDeletion.matching`), the pair is a pair of the original channel by `prefix_of_matched`.
The remaining case is a comparison whose end lies strictly inside the upper block of a host
junction (`BlockDeletion.channel_pair_lifts_of_right_endpoint`): then the target suffix is
original text near the end of its word, and the equal labels at the two cuts of the deletion
give the same window of text and states before both cuts.

Thus every channel of the edited tuple is contained in the original channel
(`BlockDeletion.channel`), and block deletions on fresh tuples are fresh dominations
(`BlockDeletion.freshDominates`).

## Main declarations

- `BlockDeletion.matching`: junctions inside a comparison correspond.
- `BlockDeletion.channel_pair_lifts_of_right_endpoint`: comparisons ending inside the upper
  block of a junction.
- `BlockDeletion.channel`: every channel of the edited tuple is contained in the original one.
- `BlockDeletion.freshDominates`: block deletions are fresh dominations.
-/

@[expose] public section


namespace DeciSigma1.Holes.Fresh

open DeciSigma1.Readers DeciSigma1.Words
open Finset

/-! ## Junctions and windows -/

section Sites

variable {α : Type} [DecidableEq α] {k : ℕ} {S : Type} [Fintype S]

namespace BlockDeletion

variable {T : Table α S k} {W : Fin k → List α} {t : ℕ} (m : BlockDeletion T W t)

/-- In a comparison of edited texts in which every host junction strictly inside has the rest
of its upper block inside the comparison, the host and target junctions strictly inside
correspond. The proof is an induction on the rightmost junction. -/
theorem matching [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {i j : Fin k} {a b L : ℕ} (hL : (m.apply j).length = b + L)
    (hpre : (m.apply j).drop b <+: (m.apply i).drop a)
    (hB : ∀ d,
        0 < d → d < L → IsJunction m.deletionLength (m.sites i)
            (a + d) → d + m.upperCutLength ≤ L) :
    ∀ d, 0 < d → d < L →
      (IsJunction m.deletionLength (m.sites i) (a + d) ↔ IsJunction m.deletionLength
          (m.sites j) (b + d)) := by
  obtain ⟨r, hr⟩ := hpre
  have hxa : ∀ d, 0 < d → d < L → a + L ≤ (m.apply i).length := by
    intro d h1 h2
    have := congrArg List.length hr
    simp only [List.length_append, List.length_drop] at this
    omega
  have htext : ∀ d, d + m.upperCutLength ≤ L →
      ((m.apply i).drop (a + d)).take m.upperCutLength =
          ((m.apply j).drop (b + d)).take m.upperCutLength := by
    intro d hd
    rw [← List.drop_drop, ← List.drop_drop, ← hr, List.drop_append_of_le_length (by simp; omega),
      List.take_append_of_le_length (by simp; omega)]
  suffices H : ∀ e d, L - d = e → 0 < d → d < L →
      (IsJunction m.deletionLength (m.sites i) (a + d) ↔ IsJunction m.deletionLength
          (m.sites j) (b + d)) from
    fun d h1 h2 => H _ d rfl h1 h2
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
  intro d he hd0 hdL
  have IH : ∀ d', d < d' → d' < L →
      (IsJunction m.deletionLength (m.sites i) (a + d') ↔ IsJunction m.deletionLength
          (m.sites j) (b + d')) :=
    fun d' h1 h2 => ih (L - d') (by omega) d' rfl (by omega) h2
  constructor
  · intro hJ
    have hdn := hB d hd0 hdL hJ
    refine m.transfer hfr hJ (htext d hdn) ?_ (by omega)
    rintro J hJ' ⟨h1, h2⟩
    have h3 := (IH (J - b) (by omega) (by omega)).mpr (by rwa [Nat.add_sub_cancel' (by omega)])
    have := m.junction_sep hJ h3 (by omega)
    omega
  · intro hJ
    have hdn : d + m.upperCutLength ≤ L := by
      obtain ⟨c, hc, hce⟩ := hJ
      have := (m.junction_window hc).2.2.1
      omega
    refine m.transfer hfr hJ (htext d hdn).symm ?_ (by have := hxa d hd0 hdL; omega)
    rintro J hJ' ⟨h1, h2⟩
    have h3 := (IH (J - a) (by omega) (by omega)).mp (by rwa [Nat.add_sub_cancel' (by omega)])
    have := m.junction_sep hJ h3 (by omega)
    omega

/-! ## Comparisons ending inside the upper block of a junction -/

/-- A word that is not active at level `t + 1` has no deletion site and is not edited. -/
theorem apply_of_inactive {l : Fin k} (hl : l ∉ active W (t + 1)) :
    m.sites l = ∅ ∧ m.apply l = W l := by
  have h : m.sites l = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro c hc
    obtain ⟨o, ho, hol, hth, -⟩ := m.site_occ hc
    exact hl (hol ▸ m.active_of_through ho hth)
  refine ⟨h, ?_⟩
  rw [BlockDeletion.apply, h]
  exact deletePositions_empty _

/-- No deletion site meets the last marker of level `t + 1` of its word, by the bound on anchors
inside a marker and the deletion margin. -/
theorem terminal [DecidableEq S] (hfr : ∀ i, T.Fresh W i) {l : Fin k}
    (hl : l ∈ active W (t + 1)) {c : ℕ} (hc : c ∈ m.sites l) :
    c + m.deletionLength + (marker W (t + 1) l).length ≤ (W l).length := by
  obtain ⟨o, ho, rfl, hth, hoc⟩ := m.site_occ hc
  have hsp := m.site_spec ho hth
  rw [hoc] at hsp
  refine Nat.le_of_not_lt fun hcon => ?_
  have hσ := marker_suffix W (t + 1) o.1
  have hocc : marker W (t + 1) o.1 <+:
      (W o.1).drop ((W o.1).length - (marker W (t + 1) o.1).length) := occ_of_suffix hσ
  have hspan := card_anchors_Ioc_marker_le hfr t hl (W o.1) hocc
  have hσl := hσ.length_le
  have hin : m.minDepth ≤
      lowerBlockCount W t o := by have := m.minDepth_le_endDepth;
                                  have := (m.edge.through_iff.mp hth).1; omega
  have hin' : m.minDepth < lowerBlockCount W t o := by
    have := m.minDepth_lt_maxDepth; have := m.maxDepth_lt_endDepth; have :=
        (m.edge.through_iff.mp hth).1; omega
  have hctx := anchors_eq_contextAnchors (active_succ_subset W t hl)
  have hdi : depthCut W t o m.minDepth = c + m.deletionLength := by omega
  have := card_depthCuts ho hin (X := (contextAnchors W t (W o.1)).filter
    (fun p => (W o.1).length - (marker W (t + 1) o.1).length < p ∧
      p ≤ (W o.1).length - (marker W (t + 1) o.1).length + (marker W (t + 1) o.1).length)) (by
    intro d hd
    rw [mem_filter, ← hctx]
    have h1 := depthCut_anti ho hd hin
    have h2 := depthCut_anti ho (Nat.zero_le d) (hd.trans hin)
    obtain ⟨hall, -⟩ := depthCut_spec ho
    rw [show depthCut W t o 0 = o.2.2 from rfl] at h2
    refine ⟨(hall d (by omega)).1, by omega, by omega⟩)
  have := m.deletionMargin_gt m.left_margin
  omega

theorem contextAnchors_anti {s t' : ℕ} (h : s ≤ t') (u : List α) :
    contextAnchors W t' u ⊆ contextAnchors W s u := by
  induction h with
  | refl => exact subset_refl _
  | step _ ih => exact (contextAnchors_succ_subset _ u).trans ih

theorem le_windowLength {r : ℕ} (hr1 : 1 ≤ r) (hrt : r ≤ t) {g : Fin k} (hg : g ∈ active W r)
    {u : List α} {c : ℕ} (hs : marker W r g <:+ u.take c) :
    (marker W r g).length ≤ windowLength W t u c := by
  have hmem : marker W r g ∈ lowerLevelTypes W t u c ⟨r - 1, by omega⟩ := by
    simp only [lowerLevelTypes, Nat.sub_add_cancel hr1]
    exact mem_markerTypes.mpr ⟨g, hg, hs, rfl⟩
  exact (le_sup (f := List.length) hmem).trans
    (le_sup (f := fun r : Fin t => (lowerLevelTypes W t u c r).sup List.length) (mem_univ _))

theorem windowLength_spec {u : List α} {c : ℕ} (hw : 0 < windowLength W t u c) :
    ∃ r, 1 ≤ r ∧ r ≤ t ∧ ∃ g ∈ active W r, marker W r g <:+ u.take c ∧
      (marker W r g).length = windowLength W t u c := by
  have hne1 : (univ : Finset (Fin t)).Nonempty := by
    by_contra hem
    rw [not_nonempty_iff_eq_empty] at hem
    simp [windowLength, hem] at hw
  obtain ⟨r, -, hr⟩ := exists_mem_eq_sup _ hne1
    (fun r : Fin t => (lowerLevelTypes W t u c r).sup List.length)
  have hne2 : (lowerLevelTypes W t u c r).Nonempty := by
    by_contra hem
    rw [not_nonempty_iff_eq_empty] at hem
    have : windowLength W t u c = 0 := by rw [windowLength, hr, hem, sup_empty]; rfl
    omega
  obtain ⟨τ, hτ, hτl⟩ := exists_mem_eq_sup _ hne2 List.length
  obtain ⟨g, hg, hs, rfl⟩ := mem_markerTypes.mp hτ
  exact ⟨r.1 + 1, by omega, by omega, g, hg, hs, by rw [windowLength, hr, hτl]⟩

omit [DecidableEq α] [Fintype S] in
/-- A text ending at a cut, read back from the cut. -/
theorem take_of_suffix_take {x τ : List α} {c : ℕ} (hc : c ≤ x.length) (hs : τ <:+ x.take c)
    {e : ℕ} (he : e ≤ τ.length) :
    x.take (c - e) = x.take (c - τ.length) ++ τ.take (τ.length - e) ∧
      (x.drop (c - e)).take e = τ.drop (τ.length - e) := by
  obtain ⟨s', hs'⟩ := hs
  have hτc : τ.length ≤ c := by
    have := congrArg List.length hs'; simp at this; omega
  have hs'l : s'.length = c - τ.length := by
    have := congrArg List.length hs'; simp at this; omega
  have hpre : x.take (c - τ.length) = s' := by
    rw [show x.take (c - τ.length) = (x.take c).take (c - τ.length) by
      rw [List.take_take, Nat.min_eq_left (by omega)], ← hs', List.take_left' hs'l]
  have hcat : x.take c = x.take (c - τ.length) ++ τ := by rw [hpre, hs']
  have hl1 : (x.take (c - τ.length)).length = c - τ.length := by simp; omega
  constructor
  · rw [show x.take (c - e) = (x.take c).take (c - e) by
      rw [List.take_take, Nat.min_eq_left (by omega)], hcat, List.take_append,
      List.take_of_length_le (by omega), hl1]
    congr 2; omega
  · rw [show (x.drop (c - e)).take e = (x.take c).drop (c - e) by
      rw [List.drop_take]; congr 1; omega, hcat, List.drop_append,
      List.drop_of_length_le (by omega), List.nil_append, hl1]
    congr 1; omega

omit [Fintype S] in
/-- Equal labels at two cuts give the same text and the same states on the last
`windowLength` letters before both cuts. -/
theorem label_window {l : Fin k} {c c' : ℕ} (hc : c ≤ (W l).length) (hc' : c' ≤ (W l).length)
    (h : label T W t l c = label T W t l c') {e : ℕ} (he : e ≤ windowLength W t (W l) c) :
    e ≤ c ∧ e ≤ c' ∧ ((W l).drop (c - e)).take e = ((W l).drop (c' - e)).take e ∧
      T.runPrefix W l (c - e) = T.runPrefix W l (c' - e) := by
  have h' := h
  simp only [label, Prod.mk.injEq] at h'
  obtain ⟨hL, hq⟩ := h'
  have hw : windowLength W t (W l) c = windowLength W t (W l) c' := by simp only [windowLength, hL]
  rw [← hw] at hq
  rcases Nat.eq_zero_or_pos (windowLength W t (W l) c) with hw0 | hwpos
  · have he0 : e = 0 := by omega
    subst he0
    exact ⟨Nat.zero_le _, Nat.zero_le _, by simp, by simpa using runPrefix_eq_of_label T hc hc' h⟩
  obtain ⟨r, hr1, hrt, g, hg, hs, hlen⟩ := windowLength_spec hwpos
  have hmem : marker W r g ∈ lowerLevelTypes W t (W l) c' ⟨r - 1, by omega⟩ := by
    rw [← hL]
    simp only [lowerLevelTypes, Nat.sub_add_cancel hr1]
    exact mem_markerTypes.mpr ⟨g, hg, hs, rfl⟩
  simp only [lowerLevelTypes, Nat.sub_add_cancel hr1] at hmem
  obtain ⟨g', -, hs', he'⟩ := mem_markerTypes.mp hmem
  rw [he'] at hs'
  have hcl := hs.length_le
  have hcl' := hs'.length_le
  simp only [List.length_take] at hcl hcl'
  obtain ⟨t1, d1⟩ := take_of_suffix_take hc hs (e := e) (by omega)
  obtain ⟨t2, d2⟩ := take_of_suffix_take hc' hs' (e := e) (by omega)
  refine ⟨by omega, by omega, by rw [d1, d2], ?_⟩
  simp only [Table.runPrefix]
  rw [t1, t2, runFrom_append, runFrom_append]
  simp only [Table.runPrefix] at hq
  rw [hlen, hq]

/-- The label window of a deletion site meets no other site of its word. -/
theorem compatible_window [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {l : Fin k} {c c₂ : ℕ} (hc : c ∈ m.sites l) (hc₂ : c₂ ∈ m.sites l) (hlt : c₂ < c) :
    c₂ + m.deletionLength + windowLength W t (W l) c ≤ c := by
  have hs := m.strictlySeparated l
  have hsep := hs.lt hc₂ hc hlt
  rcases Nat.eq_zero_or_pos (windowLength W t (W l) c) with hw0 | hwpos
  · omega
  obtain ⟨r, hr1, hrt, g, hg, hμ, hlen⟩ := windowLength_spec hwpos
  refine Nat.le_of_not_lt fun hcon => ?_
  obtain ⟨o, ho, hol, hth, hoc⟩ := m.site_occ hc
  obtain ⟨o₂, ho₂, hol₂, hth₂, hoc₂⟩ := m.site_occ hc₂
  have hord := m.site_order ho₂ ho hth₂ hth (hol₂.trans hol.symm) (by rw [hoc, hoc₂]; exact hlt)
  have hsp := m.site_spec ho hth
  have hsp₂ := m.site_spec ho₂ hth₂
  rw [hoc] at hsp
  rw [hoc₂] at hsp₂
  have hcW : c ≤ (W l).length := by rw [← hol]; omega
  obtain ⟨hl1, hocc⟩ := (suffix_take_iff hcW).mp hμ
  obtain ⟨r', rfl⟩ : ∃ r', r = r' + 1 := ⟨r - 1, by omega⟩
  have hspan := card_anchors_inside_marker_le hfr r' hg (W l) hocc
  have hin : m.minDepth ≤ lowerBlockCount W t o₂ := by
    have := m.minDepth_le_endDepth; have := (m.edge.through_iff.mp hth₂).1; omega
  have hin' : m.minDepth < lowerBlockCount W t o₂ := by
    have := m.minDepth_lt_maxDepth; have := m.maxDepth_lt_endDepth; have :=
        (m.edge.through_iff.mp hth₂).1; omega
  have hdi : depthCut W t o₂ m.minDepth = c₂ + m.deletionLength := by omega
  have := card_depthCuts ho₂ hin (X := (contextAnchors W r' (W l)).filter
    (fun p => c - (marker W (r' + 1) g).length < p ∧
      p < c - (marker W (r' + 1) g).length + (marker W (r' + 1) g).length)) (by
    intro d hd
    rw [mem_filter]
    have h1 := depthCut_anti ho₂ hd hin
    have h2 := depthCut_anti ho₂ (Nat.zero_le d) (hd.trans hin)
    rw [show depthCut W t o₂ 0 = o₂.2.2 from rfl] at h2
    obtain ⟨hall, -⟩ := depthCut_spec ho₂
    have hA := (hall d (by omega)).1
    have hEl := (upperOcc_spec ho₂).2.1
    rw [hol₂] at hA hEl
    refine
        ⟨contextAnchors_anti (by omega) _ (mem_contextAnchors_of_mem_anchors_of_lt_length hA
            (by omega)), by omega,
      by omega⟩)
  have := m.deletionMargin_gt m.left_margin
  omega

/-- No junction of a word lies in the `windowLength` letters before the junction of a site: an
earlier site ends before the label window, and a later site has a later junction. -/
theorem junction_not_in_labelWindow [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {l : Fin k} {c J' : ℕ} (hc : c ∈ m.sites l)
    (hJ' : IsJunction m.deletionLength (m.sites l) J')
    (h1 : retainedCount (sitePositions m.deletionLength (m.sites l)) c -
      windowLength W t (W l) c < J')
    (h2 : J' < retainedCount (sitePositions m.deletionLength (m.sites l)) c) : False := by
  obtain ⟨c₂, hc₂, rfl⟩ := hJ'
  have hs := m.strictlySeparated l
  have hδ := m.delta_pos
  rcases lt_trichotomy c₂ c with hlt | rfl | hgt
  · -- the sites before `c` end before its label window, which is therefore retained text
    have hwin : ∀ c₃ ∈ m.sites l, c₃ < c →
        c₃ + m.deletionLength + windowLength W t (W l) c ≤ c :=
      fun c₃ hc₃ h => m.compatible_window hfr hc hc₃ h
    have hret : Retained m.deletionLength (m.sites l) (c - windowLength W t (W l) c) := by
      intro c₃ hc₃ ⟨h3, h4⟩
      rcases lt_trichotomy c₃ c with h5 | rfl | h5
      · have := hwin c₃ hc₃ h5; omega
      · omega
      · have := hs.lt hc hc₃ h5; omega
    have := hwin c₂ hc₂ hlt
    have hk1 := retainedCount_mono (D := sitePositions m.deletionLength (m.sites l))
      (show c₂ ≤ c - windowLength W t (W l) c by omega)
    have hk2 := retainedCount_dist hret (q := c) (by omega) fun c₃ hc₃ ⟨h3, h4⟩ => by
      rcases lt_trichotomy c₃ c with h5 | rfl | h5
      · have := hwin c₃ hc₃ h5; omega
      · omega
      · omega
    omega
  · omega
  · -- a later site has a later junction
    have := retainedCount_mono (D := sitePositions m.deletionLength (m.sites l)) hgt.le
    have hne' : retainedCount (sitePositions m.deletionLength (m.sites l)) c₂ ≠
        retainedCount (sitePositions m.deletionLength (m.sites l)) c := by
      intro he
      have k1 := greatestPreimage_site hs hc
      have k2 := greatestPreimage_site hs hc₂
      rw [he] at k2
      omega
    omega

/-- The edited text of a word ends with its original terminal window: past the last site, the
cut map is a shift. -/
theorem tail_window {l : Fin k} {P : ℕ}
    (hP : ∀ c ∈ m.sites l, c + m.deletionLength + P ≤ (W l).length) (hPl : P ≤ (W l).length)
    {b' : ℕ} (hb1 : (m.apply l).length - P ≤ b') (hb2 : b' ≤ (m.apply l).length) :
    (m.apply l).drop b' = (W l).drop ((W l).length - ((m.apply l).length - b')) ∧
      greatestPreimage (sitePositions m.deletionLength (m.sites l)) b' = (W l).length -
          ((m.apply l).length - b') := by
  have hδ := m.delta_pos
  have hret0 : Retained m.deletionLength (m.sites l) ((W l).length - P) := by
    intro c hc ⟨h1, h2⟩; have := hP c hc; omega
  have hdist : ∀ q, (W l).length - P ≤ q → q ≤ (W l).length →
      retainedCount (sitePositions m.deletionLength (m.sites l)) q =
        retainedCount (sitePositions m.deletionLength (m.sites l)) ((W l).length - P) +
          (q - ((W l).length - P)) := by
    intro q h1 h2
    exact retainedCount_dist hret0 h1 (fun c hc ⟨h3, h4⟩ => by have := hP c hc; omega)
  have hk0 := hdist (W l).length (by omega) le_rfl
  rw [← length_deletePositions, ← BlockDeletion.apply] at hk0
  set p := (W l).length - ((m.apply l).length - b')
  have hp1 : (W l).length - P ≤ p := by omega
  have hkp : retainedCount (sitePositions m.deletionLength (m.sites l)) p = b' := by
    rw [hdist p hp1 (by omega)]; omega
  have hpn : p ∉ sitePositions m.deletionLength (m.sites l) := by
    intro hm
    obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp hm
    have := hP c hc
    have := (m.site_text hc).1
    omega
  have hkR : greatestPreimage (sitePositions m.deletionLength (m.sites l)) b' = p := by
    rw [← hkp]; exact greatestPreimage_retainedCount hpn
  refine ⟨?_, hkR⟩
  have hfree : ∀ J, IsJunction m.deletionLength (m.sites l) J →
      ¬ (b' < J ∧ J < b' + ((m.apply l).length - b')) := by
    rintro J ⟨c, hc, rfl⟩ ⟨h1, -⟩
    have h3 := retainedCount_mono (D := sitePositions m.deletionLength (m.sites l))
      (show c ≤ (W l).length - P by have := hP c hc; omega)
    have h4 := hdist ((W l).length - P) le_rfl (by omega)
    omega
  have hw : ((m.apply l).drop b').take ((m.apply l).length - b') =
      ((W l).drop (greatestPreimage (sitePositions m.deletionLength (m.sites l)) b')).take
        ((m.apply l).length - b') := take_drop_deleteSites _ hfree
  rw [hkR, List.take_of_length_le (by simp), List.take_of_length_le (by simp; omega)] at hw
  exact hw

/-- A comparison whose end lies strictly inside the upper block of a host junction gives a pair
of the original channel. The target suffix is original text in the last marker of its word, the
comparison starts at most `windowLength` letters left of the junction, by the factor antichain
property, and the equal label window before the right cut of the deletion gives the original
pair. -/
theorem channel_pair_lifts_of_right_endpoint [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    {i j : Fin k} {a b L d : ℕ} (hL : (m.apply j).length = b + L)
    (hpre : (m.apply j).drop b <+: (m.apply i).drop a) (hd0 : 0 < d) (hdL : d < L)
    (hJ : IsJunction m.deletionLength (m.sites i) (a + d)) (hlt : L < d + m.upperCutLength) :
    (T.runPrefix m.apply i a, T.runPrefix m.apply j b) ∈ T.channel W i j := by
  have hδ := m.delta_pos
  obtain ⟨c, hc, hce⟩ := hJ
  obtain ⟨o, ho, hol, hth, hoc⟩ := m.site_occ hc
  obtain ⟨jk2, jsep, jlen, jwin⟩ := m.junction_window hc
  rw [hce] at jk2 jlen jwin
  have hsi := m.strictlySeparated i
  have hcret := retained_of_mem_sites hsi hc
  have hcne : ∀ c' ∈ m.sites i, c ≠ c' + m.deletionLength := fun c' hc' => hsi.ne_right hδ hc hc'
  obtain ⟨hnt1, hnt2, hnpos⟩ := m.upperCutLength_spec ho hth
  rw [hoc] at hnt2
  have hsp := m.site_spec ho hth
  rw [hoc] at hsp
  have hEl := (upperOcc_spec ho).2.1
  rw [hol] at hEl
  obtain ⟨r, hr⟩ := hpre
  have hlenx : a + L ≤ (m.apply i).length := by
    have := congrArg List.length hr
    simp only [List.length_append, List.length_drop] at this
    omega
  have hY : (m.apply j).drop b = ((m.apply i).drop a).take L := by
    rw [← hr, List.take_append_of_le_length (by simp; omega),
        List.take_of_length_le (by simp; omega)]
  -- no junction of the host strictly inside `(a + d, a + L)`
  have hfreeR : ∀ J', IsJunction m.deletionLength (m.sites i) J' →
      ¬ (a + d < J' ∧ J' < a + d + (L - d)) := by
    rintro J' hJ' ⟨h1, h2⟩
    rcases jsep J' hJ' with h | h <;> omega
  -- the target suffix is original text, shorter than the last marker of its word
  have hT : (m.apply j).drop b = (W j).drop ((W j).length - L) ∧
      T.runPrefix m.apply j b = T.runPrefix W j ((W j).length - L) ∧
      ((j ∈ active W (t + 1) ∧ L < (marker W (t + 1) j).length) ∨
        (1 ≤ t ∧ j ∉ active W (t + 1))) := by
    by_cases hj : j ∈ active W (t + 1)
    · have hσ := marker_suffix W (t + 1) j
      have hterm := fun c' hc' => m.terminal hfr hj (c := c') hc'
      have hσl := hσ.length_le
      have hlenj : (m.apply j).length ≤ (W j).length := by
        rw [BlockDeletion.apply, length_deletePositions]; exact retainedCount_le _
      have hLs : L < (marker W (t + 1) j).length := by
        refine Nat.lt_of_not_le fun hge => ?_
        obtain ⟨hw1, -⟩ := m.tail_window hterm hσl (b' := (m.apply j).length -
          (marker W (t + 1) j).length) le_rfl (by omega)
        rw [show (m.apply j).length - ((m.apply j).length - (marker W (t + 1) j).length) =
          (marker W (t + 1) j).length by omega, ← List.suffix_iff_eq_drop.mp hσ] at hw1
        -- the terminal marker is a suffix of the target suffix, hence ends at `a + L` in the host
        have hσY : marker W (t + 1) j <:+ (m.apply j).drop b := by
          rw [← hw1, show (m.apply j).length - (marker W (t + 1) j).length = b + (L -
            (marker W (t + 1) j).length) by omega, ← List.drop_drop]
          exact List.drop_suffix _ _
        have hσU : marker W (t + 1) j <:+ (m.apply i).take (a + L) := by
          rw [List.take_add, ← hY]
          exact hσY.trans (List.suffix_append _ _)
        have hanc : a + L ∈ contextAnchors W (t + 1) (m.apply i) :=
          (mem_contextAnchors_succ W).mpr ⟨hlenx, j, hj, hσU⟩
        obtain ⟨p, hp, hret, hkp⟩ :=
          (m.contextAnchors_apply (r := t + 1) (by omega) le_rfl i _).mp hanc
        have hpA : p ∈ anchors W (t + 1) i := mem_insert_of_mem hp
        have hka := greatestPreimage_add_eq (show 0 < L - d by omega) hfreeR hret
          (fun c' hc' => (m.anchor_ne_site hpA hc').2) (by rw [hkp]; omega)
        rw [jk2] at hka
        have hno := (upperOcc_spec ho).2.2.2.2 p (hol ▸ hpA)
        exact hno ⟨by omega, by omega⟩
      obtain ⟨hw1, hw2⟩ := m.tail_window hterm hσl (b' := b) (by omega) (by omega)
      rw [show (m.apply j).length - b = L by omega] at hw1 hw2
      refine ⟨hw1, ?_, Or.inl ⟨hj, hLs⟩⟩
      rw [m.runPrefix_apply j b, hw2]
    · have ht : 1 ≤ t := by
        -- at level `0` an inactive word is empty, and so is its edited word
        by_contra h0
        have hnil : W j = [] := not_not.mp fun h =>
          hj (by rw [show t = 0 by omega]; exact (mem_active_one W).mpr h)
        have hlen := congrArg List.length (m.apply_of_inactive hj).2
        rw [hnil, List.length_nil] at hlen
        omega
      obtain ⟨hnil, happ⟩ := m.apply_of_inactive hj
      have hb : b = (W j).length - L := by rw [happ] at hL; omega
      refine ⟨by rw [happ, hb], ?_, Or.inr ⟨ht, hj⟩⟩
      rw [m.runPrefix_apply j b, hnil, hb]; simp [sitePositions]
  obtain ⟨hYold, hqj, hcase⟩ := hT
  -- the comparison starts at most `w` letters left of the junction
  set w := windowLength W t (W i) c with hwdef
  have hlab := m.labels_eq o ho hth
  rw [hoc, hol] at hlab
  have hdi : depthCut W t o m.minDepth = c + m.deletionLength := by omega
  rw [hdi] at hlab
  have hdw : d ≤ w := by
    refine Nat.le_of_not_lt fun hwd => ?_
    have ht : 1 ≤ t := by
      rcases hcase with ⟨hj, hLs⟩ | ⟨ht, -⟩
      · by_contra h0
        have h1 : (marker W (t + 1) j).length = 1 := by
          rw [show t = 0 by omega] at hj ⊢; exact length_marker_one hj
        omega
      · exact ht
    -- the level-`t` marker `τ` ending at the site
    have hcA : c ∈ contextAnchors W t (W i) := by
      have := hsp.2.2.2.2.2.1
      rw [hol] at this
      exact mem_contextAnchors_of_mem_anchors_of_lt_length this (by omega)
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    obtain ⟨-, h, hh, hτ⟩ := (mem_contextAnchors_succ W).mp hcA
    have hτw : (marker W (t' + 1) h).length ≤ w := le_windowLength (by omega) le_rfl hh hτ
    set τ := marker W (t' + 1) h with hτdef
    have hτpos : 1 ≤ τ.length := List.length_pos_iff.mpr (marker_ne_nil (by omega) hh)
    -- the window left of the junction is original text
    have hfreeS : ∀ J', IsJunction m.deletionLength (m.sites i) J' →
        ¬ (a + d - τ.length < J' ∧ J' < a + d - τ.length + τ.length) :=
      fun J' hJ' h => m.junction_not_in_labelWindow hfr hc hJ' (by omega) (by omega)
    have hka := greatestPreimage_add_eq hτpos hfreeS hcret hcne (by rw [hce]; omega)
    have hwinS : ((m.apply i).drop (a + d - τ.length)).take τ.length =
        ((W i).drop (greatestPreimage (sitePositions m.deletionLength (m.sites i))
          (a + d - τ.length))).take τ.length := take_drop_deleteSites _ hfreeS
    rw [show greatestPreimage (sitePositions m.deletionLength (m.sites i))
        (a + d - τ.length) = c - τ.length by omega] at hwinS
    have hcW : c ≤ (W i).length := by omega
    have hτold : ((W i).drop (c - τ.length)).take τ.length = τ :=
      (List.prefix_iff_eq_take.mp ((suffix_take_iff hcW).mp hτ).2).symm
    have hτU : τ <+: (m.apply i).drop (a + (d - τ.length)) := by
      rw [show a + (d - τ.length) = a + d - τ.length by omega]
      rw [← List.take_append_drop τ.length ((m.apply i).drop (a + d - τ.length)), hwinS, hτold]
      exact List.prefix_append _ _
    -- `τ` lies strictly inside the target suffix
    have hτY : τ <+: ((m.apply j).drop b).drop (d - τ.length) := by
      rw [hY, List.drop_take, List.drop_drop, List.prefix_iff_eq_take, List.take_take,
        Nat.min_eq_left (by omega)]
      exact List.prefix_iff_eq_take.mp hτU
    have hLW : L ≤ (W j).length := by
      have := congrArg List.length hYold; simp at this; omega
    rw [hYold, List.drop_drop] at hτY
    rcases hcase with ⟨hj, hLs⟩ | ⟨-, hj⟩
    · have hσ := marker_suffix W (t' + 1 + 1) j
      have hσo := occ_of_suffix hσ
      have hσl := hσ.length_le
      have hτlen : (marker W (t' + 1) h).length = τ.length := rfl
      have hin := prefix_drop_of_occ hσo hτY (by omega) (by omega)
      rcases (marker_occurrences_in_next_marker (by omega) hj).2.2 h hh _ hin with h1 | h1 <;>
        omega
    · have hanc : (W j).length - L + (d - τ.length) + τ.length ∈ contextAnchors W (t' + 1) (W j) :=
        (mem_contextAnchors_succ W).mpr ⟨by omega, h, hh, suffix_take_of_occ hτY⟩
      have hA : (W j).length - L + (d - τ.length) + τ.length ∈ anchors W (t' + 1) j :=
        mem_insert_of_mem hanc
      rw [anchors_eq_singleton (t := t' + 1) (by omega) hj, mem_singleton] at hA
      omega
  -- the original pair, read from the right cut `c + δ`
  have hcW : c ≤ (W i).length := by omega
  have hcW' : c + m.deletionLength ≤ (W i).length := by omega
  obtain ⟨-, -, hlw, hlq⟩ := label_window hcW hcW' hlab (e := d) hdw
  have hfreeD : ∀ J', IsJunction m.deletionLength (m.sites i) J' → ¬ (a < J' ∧ J' < a + d) :=
    fun J' hJ' h => m.junction_not_in_labelWindow hfr hc hJ' (by omega) (by omega)
  have hkaD := greatestPreimage_add_eq hd0 hfreeD hcret hcne hce
  have hkRa : greatestPreimage (sitePositions m.deletionLength (m.sites i)) a = c - d := by omega
  have hwinD : ((m.apply i).drop a).take d = ((W i).drop (c - d)).take d := by
    have := take_drop_deleteSites (W i) hfreeD
    rw [hkRa] at this
    exact this
  have hwinR : ((m.apply i).drop (a + d)).take (L - d) =
      ((W i).drop (c + m.deletionLength)).take (L - d) := by
    rw [show L - d = min (L - d) m.upperCutLength by omega, ← List.take_take, jwin, List.take_take]
  have hYsplit : (m.apply j).drop b =
      ((W i).drop (c + m.deletionLength - d)).take d ++
          ((W i).drop (c + m.deletionLength)).take (L - d) := by
    rw [hY, ← List.take_append_drop d (((m.apply i).drop a).take L), List.take_take,
      Nat.min_eq_left hdL.le, hwinD, hlw, List.drop_take, List.drop_drop, hwinR]
  have hold : (W j).drop ((W j).length - L) <+: (W i).drop (c + m.deletionLength - d) := by
    rw [← hYold, hYsplit]
    conv_rhs =>
        rw [← List.take_append_drop d ((W i).drop (c + m.deletionLength - d)), List.drop_drop,
      show c + m.deletionLength - d + d = c + m.deletionLength by omega]
    exact (List.prefix_append_right_inj _).mpr (List.take_prefix _ _)
  have hqi : T.runPrefix m.apply i a = T.runPrefix W i (c + m.deletionLength - d) := by
    rw [m.runPrefix_apply i a, hkRa, hlq]
  rw [hqi, hqj]
  exact Table.pair_mem_channel (by omega) (by omega) hold

/-- Every channel of the edited tuple, including those from a coordinate to itself and those
with empty target suffixes, is contained in the corresponding channel of the original tuple. -/
theorem channel [DecidableEq S] (hfr : ∀ i, T.Fresh W i)
    (i j : Fin k) : T.channel m.apply i j ⊆ T.channel W i j := by
  intro pq hpq
  obtain ⟨a, ha, b, hb, hpre, rfl⟩ := Table.mem_channel.mp hpq
  have hL : (m.apply j).length = b + ((m.apply j).length - b) := by omega
  set L := (m.apply j).length - b
  by_cases hA : ∃ d, 0 < d ∧ d < L ∧ IsJunction m.deletionLength (m.sites i) (a + d) ∧ L < d +
      m.upperCutLength
  · obtain ⟨d, hd0, hdL, hJ, hlt⟩ := hA
    exact m.channel_pair_lifts_of_right_endpoint hfr hL hpre hd0 hdL hJ hlt
  · have hB : ∀ d, 0 < d → d < L → IsJunction m.deletionLength (m.sites i) (a + d) → d +
      m.upperCutLength ≤ L :=
      fun d h1 h2 h3 => Nat.le_of_not_lt fun h => hA ⟨d, h1, h2, h3, h⟩
    have hm := m.matching hfr hL hpre hB
    have hold :=
        prefix_of_matched (m.delta_pos) (m.strictlySeparated i)
            (m.strictlySeparated j)
      (fun c hc => m.site_text hc) (fun c hc => m.site_text hc) L a b hL hpre hm
    rw [m.runPrefix_apply i a, m.runPrefix_apply j b]
    exact Table.pair_mem_channel
      (greatestPreimage_le_length _ (m.length_not_mem_sitePositions i) ha)
      (greatestPreimage_le_length _ (m.length_not_mem_sitePositions j) hb) hold

/-- A block deletion on a fresh tuple is a fresh domination. -/
theorem freshDominates [DecidableEq S] (hfr : ∀ i, T.Fresh W i) :
    FreshDominates T m.apply W :=
  m.freshDominates_of_channel hfr (m.channel hfr)

end BlockDeletion

end Sites

end DeciSigma1.Holes.Fresh
