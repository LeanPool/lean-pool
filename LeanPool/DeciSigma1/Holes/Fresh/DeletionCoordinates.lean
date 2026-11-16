/-
Copyright (c) 2026 Yaoyu Zhao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaoyu Zhao
-/

module

public import LeanPool.DeciSigma1.Holes.Fresh.Deletion

/-! Ported to Lean Pool’s module system and pinned Lean and Mathlib.

 # Cuts of an edited word

After separated sites of equal length are deleted from a word, every cut of the edited word
comes from a cut of the original word (`Words.retainedCount`, `Words.greatestPreimage`). A
*junction*, a cut at which a deleted text was removed, is the image of every cut from the start
to the end of the deleted text; of these, only the cuts before and after the deleted text are
retained, and the greatest preimage is the cut after it (`greatestPreimage_site`). The channels
of the edited tuple compare texts that may contain junctions, and these maps move such
comparisons back to the original words: if the junctions inside a comparison of edited texts
correspond on both sides and every deleted text is the same word, reinserting it on both sides
gives a comparison of original texts (`prefix_of_matched`).

The module also collects facts on parses and anchors of level `0` and of all levels that the
transport of channels uses (`relativeAnchors_eq_union`).

## Main declarations

- `IsJunction`: the junctions of an edited word.
- `retainedCount_dist`, `greatestPreimage_site`, `greatestPreimage_add_eq`: the cut map is a shift
  between sites, and the greatest preimages at and between junctions.
- `take_drop_deleteSites`: between junctions the edited text is original text.
- `prefix_of_matched`: matched junctions give a comparison of original texts.
-/

@[expose] public section


namespace DeciSigma1.Holes.Fresh

open DeciSigma1.Readers DeciSigma1.Words
open Finset

/-! ## Cuts of a multi-site deletion -/

section Cuts

/-- A junction: the cut of the edited text where a deleted interval was. -/
def IsJunction (δ : ℕ) (cs : Finset ℕ) (a : ℕ) : Prop :=
  ∃ c ∈ cs, retainedCount (sitePositions δ cs) c = a

instance (δ : ℕ) (cs : Finset ℕ) (a : ℕ) : Decidable (IsJunction δ cs a) :=
  inferInstanceAs (Decidable (∃ c ∈ cs, _))

variable {δ : ℕ} {cs : Finset ℕ}

theorem StrictlySeparated.lt (h : StrictlySeparated δ cs) {c c' : ℕ} (hc : c ∈ cs)
    (hc' : c' ∈ cs) (hlt : c < c') : c + δ < c' := h c hc c' hc' hlt

theorem StrictlySeparated.ne_right (h : StrictlySeparated δ cs) (hδ : 0 < δ) {c c' : ℕ}
    (hc : c ∈ cs) (hc' : c' ∈ cs) : c ≠ c' + δ := by
  intro he
  have := h.lt hc' hc (by omega)
  omega

theorem retained_of_mem_sites (hs : StrictlySeparated δ cs) {c : ℕ} (hc : c ∈ cs) :
    Retained δ cs c := by
  intro c' hc' ⟨h1, h2⟩
  have := hs.lt hc' hc h1
  omega

theorem retained_length {n : ℕ} (h : ∀ c ∈ cs, c + δ ≤ n) : Retained δ cs n := by
  rintro c hc ⟨-, h2⟩; have := h c hc; omega

/-- A retained cut that is not the right end of a site does not end a deleted interval. -/
theorem pred_not_mem_sitePositions {p : ℕ} (hp : Retained δ cs p) (hpr : ∀ c ∈ cs, p ≠ c + δ) :
    p = 0 ∨ p - 1 ∉ sitePositions δ cs := by
  by_cases h0 : p = 0
  · exact Or.inl h0
  · refine Or.inr fun h => ?_
    obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp h
    have := hpr c hc
    exact hp c hc ⟨by omega, by omega⟩

/-- The image of a deleted position is a junction. -/
theorem isJunction_of_mem {p : ℕ} (hp : p ∈ sitePositions δ cs) :
    IsJunction δ cs (retainedCount (sitePositions δ cs) p) := by
  obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp hp
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h1
  exact ⟨c, hc, (retainedCount_add_of_mem fun i hi =>
    mem_sitePositions.mpr ⟨c, hc, by omega, by omega⟩).symm⟩

/-- The cut map is a shift on a stretch without sites. -/
theorem retainedCount_dist {p q : ℕ} (hp : Retained δ cs p) (hpq : p ≤ q)
    (hno : ∀ c ∈ cs, ¬ (p ≤ c ∧ c < q)) :
    retainedCount (sitePositions δ cs) q = retainedCount (sitePositions δ cs) p + (q - p) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hpq
  rw [retainedCount_add_of_not_mem, Nat.add_sub_cancel_left]
  intro i hi hm
  obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp hm
  by_cases h : p ≤ c
  · exact hno c hc ⟨h, by omega⟩
  · exact hp c hc ⟨by omega, by omega⟩

/-- The two ends of a site have the same image. -/
theorem retainedCount_site_right {c : ℕ} (hc : c ∈ cs) :
    retainedCount (sitePositions δ cs) (c + δ) = retainedCount (sitePositions δ cs) c :=
  retainedCount_add_of_mem fun i hi => mem_sitePositions.mpr ⟨c, hc, by omega, by omega⟩

/-- At a junction the greatest preimage is the right end of the site. -/
theorem greatestPreimage_site (hs : StrictlySeparated δ cs) {c : ℕ} (hc : c ∈ cs) :
    greatestPreimage (sitePositions δ cs) (retainedCount (sitePositions δ cs) c) = c + δ := by
  rw [← retainedCount_site_right hc]
  refine greatestPreimage_retainedCount fun h => ?_
  obtain ⟨c', hc', h1, h2⟩ := mem_sitePositions.mp h
  rcases lt_trichotomy c c' with h | h | h
  · have := hs.lt hc hc' h; omega
  · omega
  · have := hs.lt hc' hc h; omega

/-- If no junction lies strictly inside `(a, a + n)`, the `n` letters of the edited text read from
`a` are the `n` letters of the original text read from the greatest preimage of `a`. -/
theorem take_drop_deleteSites {α : Type} (x : List α) {a n : ℕ}
    (hfree : ∀ J, IsJunction δ cs J → ¬ (a < J ∧ J < a + n)) :
    ((deletePositions x (sitePositions δ cs)).drop a).take n =
      (x.drop (greatestPreimage (sitePositions δ cs) a)).take n :=
  take_drop_deletePositions x fun _ hp => hfree _ (isJunction_of_mem hp)

/-- If `n ≥ 1` and no junction lies strictly inside `(a, a + n)`, a retained cut with image
`a + n` that is not the right end of a site lies `n` letters after the greatest preimage of
`a`. -/
theorem greatestPreimage_add_eq {a n p : ℕ} (hn : 0 < n)
    (hfree : ∀ J, IsJunction δ cs J → ¬ (a < J ∧ J < a + n)) (hp : Retained δ cs p)
    (hpr : ∀ c ∈ cs, p ≠ c + δ) (hk : retainedCount (sitePositions δ cs) p = a + n) :
    greatestPreimage (sitePositions δ cs) a + n = p := by
  have hret := not_mem_of_no_junction fun q hq => hfree _ (isJunction_of_mem hq)
  refine eq_of_retainedCount_eq (by rw [retainedCount_greatestPreimage_add hret, hk]) (Or.inr ?_)
    (pred_not_mem_sitePositions hp hpr)
  rw [show greatestPreimage (sitePositions δ cs) a + n - 1 = greatestPreimage
      (sitePositions δ cs) a + (n - 1)
    by omega]
  exact hret (n - 1) (by omega)

end Cuts

/-! ## Matched junctions give a comparison of original texts -/

section Matched

variable {α : Type} {δ : ℕ}

theorem drop_eq_take_append_site {x : List α} {F : List α} {p d c : ℕ} (hpc : p + d = c)
    (hF : (x.drop c).take δ = F) :
    x.drop p = (x.drop p).take d ++ (F ++ x.drop (c + δ)) := by
  rw [← hF, ← List.drop_drop, List.take_append_drop, ← hpc, ← List.drop_drop,
    List.take_append_drop]

/-- If the junctions strictly inside a comparison of edited texts correspond on both sides, and
every site deletes the same text `F`, then reinserting `F` on both sides gives a comparison of
original texts, read from the greatest preimages of the cuts. -/
theorem prefix_of_matched (hδ : 0 < δ) {F x y : List α} {cx cy : Finset ℕ}
    (hsx : StrictlySeparated δ cx) (hsy : StrictlySeparated δ cy)
    (hx : ∀ c ∈ cx, c + δ < x.length ∧ (x.drop c).take δ = F)
    (hy : ∀ c ∈ cy, c + δ < y.length ∧ (y.drop c).take δ = F) :
    ∀ L a b, (deletePositions y (sitePositions δ cy)).length = b + L →
      (deletePositions y (sitePositions δ cy)).drop b <+:
        (deletePositions x (sitePositions δ cx)).drop a →
      (∀ d, 0 < d → d < L → (IsJunction δ cx (a + d) ↔ IsJunction δ cy (b + d))) →
      y.drop (greatestPreimage (sitePositions δ cy) b) <+:
          x.drop (greatestPreimage (sitePositions δ cx) a) := by
  intro L
  induction L using Nat.strong_induction_on with
  | _ L ih =>
  intro a b hL hpre hm
  obtain ⟨r, hr⟩ := hpre
  have hlenb : ((deletePositions y (sitePositions δ cy)).drop b).length = L := by simp; omega
  by_cases hex : ∃ d, 0 < d ∧ d < L ∧ IsJunction δ cy (b + d)
  · classical
    have hd0 := (Nat.find_spec hex).1
    have hdL := (Nat.find_spec hex).2.1
    have hdJ := (Nat.find_spec hex).2.2
    set d₁ := Nat.find hex with hd₁
    have hmin : ∀ d, 0 < d → d < d₁ → ¬ IsJunction δ cy (b + d) :=
      fun d h1 h2 h3 => Nat.find_min hex h2 ⟨h1, by omega, h3⟩
    have hfy : ∀ J, IsJunction δ cy J → ¬ (b < J ∧ J < b + d₁) := by
      rintro J hJ ⟨h1, h2⟩
      exact hmin (J - b) (by omega) (by omega) (by rwa [Nat.add_sub_cancel' h1.le])
    have hfx : ∀ J, IsJunction δ cx J → ¬ (a < J ∧ J < a + d₁) := by
      rintro J hJ ⟨h1, h2⟩
      have := (hm (J - a) (by omega) (by omega)).mp (by rwa [Nat.add_sub_cancel' h1.le])
      exact hmin (J - a) (by omega) (by omega) this
    obtain ⟨cT, hcT, hcTe⟩ := hdJ
    obtain ⟨cH, hcH, hcHe⟩ := (hm d₁ hd0 hdL).mpr ⟨cT, hcT, hcTe⟩
    have ky := greatestPreimage_add_eq hd0 hfy (retained_of_mem_sites hsy hcT)
      (fun c hc => hsy.ne_right hδ hcT hc) hcTe
    have kx := greatestPreimage_add_eq hd0 hfx (retained_of_mem_sites hsx hcH)
      (fun c hc => hsx.ne_right hδ hcH hc) hcHe
    have jy := greatestPreimage_site hsy hcT
    have jx := greatestPreimage_site hsx hcH
    rw [hcTe] at jy
    rw [hcHe] at jx
    have hP : ((deletePositions y (sitePositions δ cy)).drop b).take d₁ =
        ((deletePositions x (sitePositions δ cx)).drop a).take d₁ := by
      rw [← hr, List.take_append_of_le_length (by omega)]
    have eqy : y.drop (greatestPreimage (sitePositions δ cy) b) =
        ((deletePositions y (sitePositions δ cy)).drop b).take d₁ ++
          (F ++ y.drop (greatestPreimage (sitePositions δ cy) (b + d₁))) := by
      rw [take_drop_deleteSites y hfy, jy]
      exact drop_eq_take_append_site ky (hy cT hcT).2
    have eqx : x.drop (greatestPreimage (sitePositions δ cx) a) =
        ((deletePositions x (sitePositions δ cx)).drop a).take d₁ ++
          (F ++ x.drop (greatestPreimage (sitePositions δ cx) (a + d₁))) := by
      rw [take_drop_deleteSites x hfx, jx]
      exact drop_eq_take_append_site kx (hx cH hcH).2
    have hpre' : (deletePositions y (sitePositions δ cy)).drop (b + d₁) <+:
        (deletePositions x (sitePositions δ cx)).drop (a + d₁) := by
      rw [← List.drop_drop, ← List.drop_drop, ← hr, List.drop_append_of_le_length (by omega)]
      exact List.prefix_append _ _
    have ih' := ih (L - d₁) (by omega) (a + d₁) (b + d₁) (by omega) hpre' (fun d h1 h2 => by
      have := hm (d₁ + d) (by omega) (by omega)
      rwa [← Nat.add_assoc, ← Nat.add_assoc] at this)
    rw [eqy, eqx, hP]
    exact (List.prefix_append_right_inj _).mpr ((List.prefix_append_right_inj _).mpr ih')
  · have hfy : ∀ J, IsJunction δ cy J → ¬ (b < J ∧ J < b + L) := by
      rintro J hJ ⟨h1, h2⟩
      exact hex ⟨J - b, by omega, by omega, by rwa [Nat.add_sub_cancel' h1.le]⟩
    have hfx : ∀ J, IsJunction δ cx J → ¬ (a < J ∧ J < a + L) := by
      rintro J hJ ⟨h1, h2⟩
      have := (hm (J - a) (by omega) (by omega)).mp (by rwa [Nat.add_sub_cancel' h1.le])
      exact hex ⟨J - a, by omega, by omega, this⟩
    have hyl : y.length ∉ (sitePositions δ cy) := fun h => by
      obtain ⟨c, hc, h1, h2⟩ := mem_sitePositions.mp h
      have := (hy c hc).1; omega
    have hyy : y.drop (greatestPreimage (sitePositions δ cy) b) =
        (deletePositions y (sitePositions δ cy)).drop b := by
      rcases Nat.eq_zero_or_pos L with hL0 | hLpos
      · have hb : b = (deletePositions y (sitePositions δ cy)).length := by omega
        rw [hb, greatestPreimage_length y hyl, List.drop_length, List.drop_length]
      · have ky := greatestPreimage_add_eq hLpos hfy
          (retained_length fun c hc => (hy c hc).1.le)
          (fun c hc he => by have := (hy c hc).1; omega)
          (by rw [← hL, length_deletePositions])
        have h1 := take_drop_deleteSites y hfy
        rw [List.take_of_length_le (by omega),
          List.take_of_length_le (by simp; omega)] at h1
        exact h1.symm
    have : (deletePositions y (sitePositions δ cy)).drop b =
        ((deletePositions x (sitePositions δ cx)).drop a).take L := by
      rw [← hr, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
    rw [hyy, this, take_drop_deleteSites x hfx]
    exact List.take_prefix _ _

end Matched

/-! ## Generic facts on parses and anchors -/

section Generic

variable {α : Type} [DecidableEq α] {k : ℕ}

theorem mem_contextAnchors_of_mem_anchors_of_lt_length {W : Fin k → List α} {t : ℕ} {l : Fin k}
    {p : ℕ}
    (hp : p ∈ anchors W t l) (hlt : p < (W l).length) : p ∈ contextAnchors W t (W l) := by
  rcases mem_insert.mp hp with h | h
  · omega
  · exact h

/-- For an active coordinate, the end of its word is a context anchor, so its anchors are its
context anchors. -/
theorem anchors_eq_contextAnchors {W : Fin k → List α} {t : ℕ} {l : Fin k}
    (hl : l ∈ active W t) : anchors W t l = contextAnchors W t (W l) := by
  apply insert_eq_of_mem
  rcases t with _ | t
  · simp only [contextAnchors, mem_Icc]
    have := List.length_pos_iff.mpr (ne_nil_of_mem_active W hl); omega
  · rw [mem_contextAnchors_succ]
    exact ⟨le_rfl, l, hl, by rw [List.take_length]; exact marker_suffix W _ l⟩

/-- The anchors of a text in a context, at every level: at level `0` all cuts are anchors of
the text alone. -/
theorem relativeAnchors_eq_union {W : Fin k → List α} (t : ℕ) (u z : List α) :
    relativeAnchors W t u z = contextAnchors W t z ∪ crossBoundaryMarkerEnds W t u z := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · ext p
    simp only
        [relativeAnchors, crossBoundaryMarkerEnds, contextAnchors, mem_union, mem_filter, mem_Icc,
      List.length_append, marker_zero, List.length_nil, Nat.not_lt_zero, and_false]
    omega
  · exact relativeAnchors_eq ht u z

/-- The ends of markers that start to the left of `z` lie strictly before every anchor of `z` alone
(at level `0` there are no such ends). -/
theorem crossBoundaryMarkerEnds_lt_inside {W : Fin k → List α} {t : ℕ} {u z : List α}
    {p q : ℕ} (hp : p ∈ crossBoundaryMarkerEnds W t u z) (hq : q ∈ contextAnchors W t z) : p <
        q := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp [crossBoundaryMarkerEnds] at hp
  · by_contra h
    exact not_inside_le_crossBoundaryMarkerEnds ht hp hq (by omega)

/-- Cuts read from the right agree under a shift, as long as the two anchor sets agree. -/
theorem depthCutAt_shift {A Q : Finset ℕ} {base n lo : ℕ}
    (hag : ∀ q, lo ≤ q → q ≤ n → (base + q ∈ A ↔ q ∈ Q)) (hlo : lo ∈ Q) (hn : n ∈ Q)
    (hlon : lo ≤ n) : ∀ d ≤ anchorCount Q lo n, depthCutAt A (base + n) d = base +
        depthCutAt Q n d := by
  intro d
  induction d with
  | zero => intro _; rfl
  | succ d ih =>
    intro hd
    have hlt : lo < n := by
      rcases Nat.eq_or_lt_of_le hlon with h | h
      · subst h; rw [anchorCount_self] at hd; omega
      · exact h
    obtain ⟨hall, hlast⟩ := depthCutAt_spec hlt hn (Or.inr hlo)
    obtain ⟨hrQ, hlr, hrn, -⟩ := hall d (by omega)
    have hr' : depthCutAt Q n (d + 1) ∈ Q ∧ lo ≤ depthCutAt Q n (d + 1) := by
      rcases Nat.lt_or_ge (d + 1) (anchorCount Q lo n) with h | h
      · obtain ⟨h1, h2, -, -⟩ := hall (d + 1) h; exact ⟨h1, h2.le⟩
      · have : d + 1 = anchorCount Q lo n := by omega
        rw [this, hlast]; exact ⟨hlo, le_rfl⟩
    have hprev : depthCutAt Q n (d + 1) = previousAnchor Q (depthCutAt Q n d) := rfl
    have hlt' : depthCutAt Q n (d + 1) < depthCutAt Q n d := by
      rw [hprev]; exact (previousAnchor_spec ⟨lo, hlo, hlr⟩).2
    change previousAnchor A (depthCutAt A (base + n) d) = base + depthCutAt Q n (d + 1)
    rw [ih (by omega)]
    apply le_antisymm
    · apply previousAnchor_le
      intro q hq hqr
      by_contra hcon
      have hqQ : q - base ∈ Q := (hag (q - base) (by omega) (by omega)).mp
        (by rwa [Nat.add_sub_cancel' (by omega)])
      have := le_previousAnchor hqQ (show q - base < depthCutAt Q n d by omega)
      rw [← hprev] at this
      omega
    · exact le_previousAnchor ((hag _ hr'.2 (by omega)).mpr hr'.1) (by omega)

theorem anchorCount_shift {A Q : Finset ℕ} {base n lo : ℕ}
    (hag : ∀ q, lo ≤ q → q ≤ n → (base + q ∈ A ↔ q ∈ Q)) :
    anchorCount A (base + lo) (base + n) = anchorCount Q lo n := by
  unfold anchorCount
  have himg : (Q.filter (fun p => lo < p ∧ p ≤ n)).image (base + ·) =
      A.filter (fun p => base + lo < p ∧ p ≤ base + n) := by
    ext p
    simp only [mem_image, mem_filter]
    constructor
    · rintro ⟨q, ⟨hq, h1, h2⟩, rfl⟩
      exact ⟨(hag q (by omega) h2).mpr hq, by omega, by omega⟩
    · rintro ⟨hp, h1, h2⟩
      refine ⟨p - base, ⟨(hag _ (by omega) (by omega)).mp ?_, by omega, by omega⟩, by omega⟩
      rwa [Nat.add_sub_cancel' (by omega)]
  rw [← himg, card_image_of_injective _ (add_right_injective base)]

omit [DecidableEq α] in
/-- A text segment of a word, read through a window of it. -/
theorem segment_eq {x z : List α} {p n r r' : ℕ} (hz : (x.drop p).take n = z) (h1 : r' ≤ r)
    (h2 : r ≤ n) : (x.drop (p + r')).take (r - r') = (z.drop r').take (r - r') := by
  rw [← hz, List.drop_take, ← List.drop_drop, List.take_take, Nat.min_eq_left (by omega)]

/-- The text between two depth cuts of an upper occurrence is the concatenation of the
corresponding lower blocks. -/
theorem text_depthCut {W : Fin k → List α} {t : ℕ}
    {o : Fin k × ℕ × ℕ} (ho : o ∈ upperOccurrences W t) {d d' : ℕ} (hdd : d ≤ d')
    (hd' : d' ≤ lowerBlockCount W t o) :
    ((W o.1).drop (depthCut W t o d')).take (depthCut W t o d - depthCut W t o d') =
      (((reversedBlocks W t o).take d').drop d).reverse.flatten := by
  induction d', hdd using Nat.le_induction with
  | base =>
    simp only [Nat.sub_self, List.take_zero]
    rw [List.drop_of_length_le (by simp)]; rfl
  | succ d' hdd ih =>
    have hlt := depthCut_lt ho (show d' < lowerBlockCount W t o by omega)
    have hle : depthCut W t o d' ≤ depthCut W t o d := by
      rcases Nat.eq_or_lt_of_le hdd with h | h
      · rw [h]
      · exact (depthCut_lt_of_lt ho h (by omega)).le
    have hd'r : d' < (reversedBlocks W t o).length := by simp; omega
    rw [show depthCut W t o d - depthCut W t o (d' + 1) =
        (depthCut W t o d' - depthCut W t o (d' + 1)) + (depthCut W t o d - depthCut W t o d')
        by omega, List.take_add, List.drop_drop,
      show depthCut W t o (d' + 1) + (depthCut W t o d' - depthCut W t o (d' + 1)) =
        depthCut W t o d' by omega, ih (by omega), List.take_add_one,
      List.getElem?_eq_getElem hd'r, Option.toList_some,
      List.drop_append_of_le_length (by simp; omega), List.reverse_append,
      List.reverse_singleton, List.singleton_append, List.flatten_cons, getElem_reversedBlocks]

theorem mem_ctx_take {W : Fin k → List α} {t : ℕ} {x : List α} {e p : ℕ} (hep : e ≤ p)
    (hp : p ≤ x.length) : e ∈ contextAnchors W t (x.take p) ↔ e ∈ contextAnchors W t x := by
  conv_rhs => rw [← List.take_append_drop p x]
  exact (mem_contextAnchors_append_left (by simp; omega)).symm

/-- Membership in `relativeAnchors` for a text that is a window of a word. -/
theorem mem_relAnchors_iff {W : Fin k → List α} {t : ℕ} {x z : List α} {c n q : ℕ}
    (hz : (x.drop c).take n = z) (hcn : c + n ≤ x.length) (hq1 : 1 ≤ q) (hqn : q ≤ n) :
    q ∈ relativeAnchors W t (x.take c) z ↔ c + q ∈ contextAnchors W t x := by
  have hzl : z.length = n := by rw [← hz]; simp; omega
  have hcat : x.take c ++ z = x.take (c + n) := by rw [List.take_add, hz]
  have hcl : (x.take c).length = c := by simp; omega
  simp only [relativeAnchors, mem_filter, mem_Icc, hzl, hcl, hcat]
  rw [mem_ctx_take (by omega) hcn]
  exact ⟨fun h => h.2, fun h => ⟨⟨hq1, hqn⟩, h⟩⟩

end Generic

end DeciSigma1.Holes.Fresh
