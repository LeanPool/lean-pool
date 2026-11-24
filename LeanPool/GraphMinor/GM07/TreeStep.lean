/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.TreeChart
public import LeanPool.GraphMinor.GM07.Reroute

/-!
# Moving the edges at a root to one side of a tree

This is the main step of (4.4) of Graph Minors VII. Let `T` be a component of the forest `L`, with
root `z` on `bd(Σ)`, and let `H` be a forest whose edges at `z` cross `T` near `z`. We want the
edges at `z` to leave `z` from one chosen point `l` of `φ⁻¹(z)`, without crossing `T`.

Take the half rectangle around `φ⁻¹(T)` from `exists_tree_chart`. Each edge at `z` leaves the image
of this rectangle for the last time at a point on the top or the lateral sides of the rectangle.
Replace the edge up to that point by the straight segment in the rectangle from `l` to that point
(`exists_new_line`). The segments meet only at `l`, because they end on the top and lateral sides
(`ray_eq`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric Complex GraphMinor.Surface GraphMinor.GM11

variable {S S' : Type} [TopologicalSpace S] [TopologicalSpace S']

/-- The straight segment from the point `x₀` of the bottom side to `w`. -/
noncomputable def ray (x₀ : ℝ) (w : ℂ) (t : unitInterval) : ℂ := (x₀ : ℂ) + (t.1 : ℂ) * (w - x₀)

theorem continuous_ray (x₀ : ℝ) (w : ℂ) : Continuous (ray x₀ w) := by
  unfold ray
  fun_prop

theorem ray_zero (x₀ : ℝ) (w : ℂ) : ray x₀ w 0 = x₀ := by simp [ray]

theorem ray_one (x₀ : ℝ) (w : ℂ) : ray x₀ w 1 = w := by simp [ray]

theorem ray_re (x₀ : ℝ) (w : ℂ) (t : unitInterval) :
    (ray x₀ w t).re = x₀ + t.1 * (w.re - x₀) := by
  simp [ray]

theorem ray_im (x₀ : ℝ) (w : ℂ) (t : unitInterval) : (ray x₀ w t).im = t.1 * w.im := by simp [ray]

section Rect

variable {x₀ x₁ x₂ δ : ℝ} {w w' : ℂ}

theorem ray_mem (hx₀ : x₀ ∈ Ioo x₁ x₂) (hw : w ∈ Icc x₁ x₂ ×ℂ Icc 0 δ)
  (t : unitInterval) : ray x₀ w t ∈ Icc x₁ x₂ ×ℂ Icc 0 δ := by
  have h1 : x₁ ≤ w.re := hw.1.1
  have h2 : w.re ≤ x₂ := hw.1.2
  have h3 : 0 ≤ w.im := hw.2.1
  have h4 : w.im ≤ δ := hw.2.2
  have ht0 := t.2.1
  have ht1 := t.2.2
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [ray_re]
    nlinarith [hx₀.1, hx₀.2]
  · rw [ray_re]
    nlinarith [hx₀.1, hx₀.2]
  · rw [ray_im]
    positivity
  · rw [ray_im]
    nlinarith

theorem ray_mem_box (hx₀ : x₀ ∈ Ioo x₁ x₂) (hw : w ∈ Icc x₁ x₂ ×ℂ Icc 0 δ)
  (him : 0 < w.im) {t : unitInterval} (ht : t.1 < 1) : ray x₀ w t ∈ Ioo x₁ x₂ ×ℂ Ico 0 δ := by
  have h1 : x₁ ≤ w.re := hw.1.1
  have h2 : w.re ≤ x₂ := hw.1.2
  have h4 : w.im ≤ δ := hw.2.2
  have ht0 := t.2.1
  have hs : 0 < 1 - t.1 := by linarith
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [ray_re]
    nlinarith [hx₀.1, hx₀.2]
  · rw [ray_re]
    nlinarith [hx₀.1, hx₀.2]
  · rw [ray_im]
    positivity
  · rw [ray_im]
    nlinarith

/-- **Two segments that end on the top and lateral sides do not meet off the bottom side, unless
they are the same.** The segment with the nearer point of the two would end at a point inside the
box. -/
theorem ray_eq (hx₀ : x₀ ∈ Ioo x₁ x₂) (hw : w ∈ Icc x₁ x₂ ×ℂ Icc 0 δ)
  (hw' : w' ∈ Icc x₁ x₂ ×ℂ Icc 0 δ) (him : 0 < w.im) (him' : 0 < w'.im)
    (hB : w ∉ Ioo x₁ x₂ ×ℂ Ico 0 δ) (hB' : w' ∉ Ioo x₁ x₂ ×ℂ Ico 0 δ)
    {t t' : unitInterval} (ht : 0 < t.1) (ht' : 0 < t'.1) (h : ray x₀ w t = ray x₀ w' t') : w = w'
      := by
  have key : ∀ {w w' : ℂ} {t t' : unitInterval}, w ∈ Icc x₁ x₂ ×ℂ Icc 0 δ → 0 < w.im
    → w' ∉ Ioo x₁ x₂ ×ℂ Ico 0 δ → 0 < t.1 → 0 < t'.1 → ray x₀ w t = ray x₀ w' t' → t ≤ t' → w = w'
      := by
    intro w w' t t' hw him hB' ht ht' h hle
    have hle' : t.1 ≤ t'.1 := hle
    have hr : t'.1 * (w'.re - x₀) = t.1 * (w.re - x₀) := by
      have := congrArg Complex.re h
      rw [ray_re, ray_re] at this
      linarith
    have hi : t'.1 * w'.im = t.1 * w.im := by
      have := congrArg Complex.im h
      rw [ray_im, ray_im] at this
      exact this.symm
    let s : unitInterval := ⟨t.1 / t'.1, by positivity, (div_le_one ht').mpr hle'⟩
    have hs : s.1 * t'.1 = t.1 := by
      change t.1 / t'.1 * t'.1 = t.1
      field_simp
    have hw'r : ray x₀ w s = w' := by
      apply Complex.ext
      · rw [ray_re]
        have : t'.1 * (x₀ + s.1 * (w.re - x₀)) = t'.1 * w'.re := by
          calc t'.1 * (x₀ + s.1 * (w.re - x₀)) = t'.1 * x₀ + (s.1 * t'.1) * (w.re - x₀) := by ring
            _ = t'.1 * x₀ + t.1 * (w.re - x₀) := by rw [hs]
            _ = t'.1 * w'.re := by rw [← hr]; ring
        exact mul_left_cancel₀ ht'.ne' this
      · rw [ray_im]
        have : t'.1 * (s.1 * w.im) = t'.1 * w'.im := by
          calc t'.1 * (s.1 * w.im) = (s.1 * t'.1) * w.im := by ring
            _ = t.1 * w.im := by rw [hs]
            _ = t'.1 * w'.im := hi.symm
        exact mul_left_cancel₀ ht'.ne' this
    by_cases hs1 : s.1 < 1
    · exact absurd (hw'r ▸ ray_mem_box hx₀ hw him hs1) hB'
    · have hs2 : s.1 = 1 := le_antisymm s.2.2 (not_lt.mp hs1)
      have : s = 1 := Subtype.ext hs2
      rw [this, ray_one] at hw'r
      exact hw'r
  rcases le_total t t' with hle | hle
  · exact key hw him hB' ht ht' h hle
  · exact (key hw' him' hB ht' ht h.symm hle).symm

end Rect

/-- **The new line of an edge at the root.** The arc `c` runs from `z` to `y`. It leaves the image
`Y` of the rectangle for the last time at a point `φ (χ w)` on the top or lateral sides. The new
line is the segment to `w`, followed by the rest `R` of `c`. -/
theorem exists_new_line {L : Drawing S} {φ : S' → S} [CompactSpace S'] [T2Space S]
  (hJ : IsCutAlongGraph L S' φ) {χ : ℂ → S'} {x₀ x₁ x₂ δ : ℝ} (hχ : IsBdChart χ x₁ x₂ δ)
    (hx₀ : x₀ ∈ Ioo x₁ x₂) {z y : S}
    (hz : φ (χ x₀) = z) {c : Set S} (hc : IsLineWithEnds c z y) {Y W₀ N Q₁ Q₂ : Set S} (hY : Y
      = φ '' (χ '' (Icc x₁ x₂ ×ℂ Icc 0 δ))) (hW₀ : IsOpen W₀) (hzW : z ∈ W₀) (hW₀Y : W₀ ⊆ Y)
        (hyY : y ∉ Y)
    (hcb : ∀ q ∈ c, q ≠ z → q ≠ y → q ∉ bd S) (hYU : ∀ q ∈ Y, q ∈ L.U → q ∈ W₀)
      (hzU : z ∈ L.U ∪ bd S) (hN : Flat N) (hYN : Y ⊆ N) (hcQ : c = Q₁ ∪ Q₂) (hQ₁N : Q₁ ⊆ N)
        (hQ₁p : IsPreconnected Q₁) (hzQ₁ : z ∈ Q₁) (hQ₂ : Disjoint Q₂ Y) :
    ∃ (w : ℂ) (R : Set S), w ∈ Icc x₁ x₂ ×ℂ Icc 0 δ ∧ w ∉ Ioo x₁ x₂ ×ℂ Ico 0 δ ∧ 0 < w.im ∧ φ
      (χ w) ∉ W₀ ∧ φ (χ w) ∈ c ∧ R ⊆ c ∧ c \ N ⊆ R ∧ R ∩ Y = {φ (χ w)} ∧ IsClosed R ∧
      IsLineWithEnds (range (fun t => φ (χ (ray x₀ w t))) ∪ R) z y ∧ ∃ κ l : Path z y,
        (∀ u, κ u ∈ range (fun t => φ (χ (ray x₀ w t))) ∪ R) ∧ (∀ u, l u ∈ c) ∧ κ.Homotopic l := by
  classical
  obtain ⟨hx, hδ, hcont, hinj, hopen, hbdχ⟩ := hχ
  have hYS := hJ.isSurface
  have : T2Space S' := hYS.2.1
  have hφ := hJ.quotientMap.continuous
  have hF : ∀ q, φ q ∈ bd S ∪ L.U ↔ q ∈ bd S' := fun q => by rw [← hJ.preimage_bd_union_U]; rfl
  set Rc : Set ℂ := Icc x₁ x₂ ×ℂ Icc 0 δ with hRc
  set B : Set ℂ := Ioo x₁ x₂ ×ℂ Ico 0 δ with hB
  have hRcc : IsCompact Rc := isCompact_Icc.reProdIm isCompact_Icc
  have hYc : IsClosed Y := by
    rw [hY]
    exact ((hRcc.image_of_continuousOn hcont).image hφ).isClosed
  obtain ⟨f, hf0, hf1⟩ := id hc
  let a : unitInterval → S := fun t => (f t).1
  have hac : Continuous a := by fun_prop
  have hai : Function.Injective a := fun s t h => f.injective (Subtype.ext h)
  have harc : IsArcMap a := ⟨hac, hai⟩
  have hr : range a = c := by
    ext q
    exact ⟨by rintro ⟨t, rfl⟩; exact (f t).2, fun hq => ⟨f.symm ⟨q, hq⟩, by simp [a]⟩⟩
  have ha0 : a 0 = z := hf0
  have ha1 : a 1 = y := hf1
  have hmemc : ∀ t, a t ∈ c := fun t => (f t).2
  have hSet : IsCompact (a ⁻¹' Y) := (hYc.preimage hac).isCompact
  have hzY : z ∈ Y := hW₀Y hzW
  obtain ⟨te, hte, htel⟩ := hSet.exists_isGreatest ⟨0, by rw [mem_preimage, ha0]; exact hzY⟩
  have hte1 : te.1 < 1 := by
    refine lt_of_le_of_ne te.2.2 fun h => hyY ?_
    have : te = 1 := Subtype.ext h
    rw [this, mem_preimage, ha1] at hte
    exact hte
  obtain ⟨t₀, ht₀, -, ht₀W⟩ := exists_initial hac hW₀ (show a 0 ∈ W₀ by rw [ha0]; exact hzW)
  have hte0 : 0 < te.1 := lt_of_lt_of_le ht₀ (htel (hW₀Y (ht₀W t₀ le_rfl)))
  obtain ⟨A, hA, hA0, hAf, hfA, hA1⟩ := exists_tail harc hte0 hte1
  -- A point of the tail in an open subset of `Y` cannot exist.
  have hlast : ∀ O : Set S, IsOpen O → O ⊆ Y → a te ∉ O := fun O hO hOY hin => by
    obtain ⟨s, hs0, -, hs⟩ := exists_initial hA.1 hO (show A 0 ∈ O by rw [hA0]; exact hin)
    have hne : s ≠ 0 := fun h => by rw [h] at hs0; simp at hs0
    obtain ⟨s', hs', he⟩ := hAf s hne
    have : a s' ∈ Y := hOY (he ▸ hs s le_rfl)
    exact absurd (htel this) (not_le.mpr hs')
  have htY : a te ∈ Y := hte
  obtain ⟨_, ⟨w, hw, rfl⟩, hpe⟩ := hY ▸ htY
  have hpW : φ (χ w) ∉ W₀ := fun h => hlast W₀ hW₀ hW₀Y (hpe ▸ h)
  have hte0' : te ≠ 0 := fun h => by rw [h] at hte0; simp at hte0
  have hte1' : te ≠ 1 := fun h => by rw [h] at hte1; simp at hte1
  have hpb : a te ∉ bd S := hcb _ (hmemc te) (fun h => hte0' (hai (h.trans ha0.symm))) fun h
    => hte1' (hai (h.trans ha1.symm))
  have hpU : φ (χ w) ∉ L.U := fun h => hpW (hYU _ (by rw [hY]; exact ⟨_, ⟨w, hw, rfl⟩, rfl⟩) h)
  have hwim : w.im ≠ 0 := fun h => by
    have h1 := (hbdχ w hw).mpr h
    rcases (hF _).mpr h1 with h2 | h2
    · exact hpb (hpe ▸ h2)
    · exact hpU h2
  have hwpos : 0 < w.im := lt_of_le_of_ne hw.2.1 (Ne.symm hwim)
  -- Points of the rectangle off the bottom side are not over `bd(Σ) ∪ U(L)`.
  have hoff : ∀ u ∈ Rc, u.im ≠ 0 → χ u ∉ bd S' := fun u hu h0 h => h0 ((hbdχ u hu).mp h)
  have hwB : w ∉ B := by
    intro hin
    let Bp : Set ℂ := Ioo x₁ x₂ ×ℂ Ioo 0 δ
    have hBpB : Bp ⊆ B := fun u hu => ⟨hu.1, Ioo_subset_Ico_self hu.2⟩
    have hBR : B ⊆ Rc := fun u hu => ⟨Ioo_subset_Icc_self hu.1, Ico_subset_Icc_self hu.2⟩
    have hsplit : χ '' Bp = χ '' B \ bd S' := by
      ext q
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨⟨u, hBpB hu, rfl⟩, hoff u (hBR (hBpB hu)) hu.2.1.ne'⟩
      · rintro ⟨⟨u, hu, rfl⟩, h2⟩
        refine ⟨u, ⟨hu.1, lt_of_le_of_ne hu.2.1 fun h0 => h2 ((hbdχ u (hBR hu)).mpr h0.symm),
          hu.2.2⟩, rfl⟩
    have hopen' : IsOpen (χ '' Bp) := by
      rw [hsplit]
      exact hopen.sdiff (isClosed_bd S')
    have hsub : χ '' Bp ⊆ φ ⁻¹' (bd S ∪ L.U)ᶜ := by
      rintro _ ⟨u, hu, rfl⟩ h
      exact hoff u (hBR (hBpB hu)) hu.2.1.ne' ((hF _).mp h)
    have hO := GM19.isOpen_image_of_isCutMap hJ.toSet.isCutMap hsub hopen'
    refine hlast _ hO ?_ ?_
    · rw [hY]
      exact image_mono (image_mono fun u hu => hBR (hBpB hu))
    · rw [← hpe]
      exact ⟨χ w, ⟨w, ⟨hin.1, hwpos, lt_of_le_of_ne hw.2.2 fun h => (hin.2.2.ne h)⟩, rfl⟩, rfl⟩
  -- The segment.
  let b : unitInterval → S := fun t => φ (χ (ray x₀ w t))
  have hrm : ∀ t, ray x₀ w t ∈ Rc := ray_mem hx₀ hw
  have hbc : Continuous b := hφ.comp (hcont.comp_continuous (continuous_ray x₀ w) hrm)
  have hb0 : b 0 = z := by simp only [b, ray_zero, hz]
  have hb1 : b 1 = a te := by simp only [b, ray_one, hpe]
  have hrimpos : ∀ t : unitInterval, t ≠ 0 → (ray x₀ w t).im ≠ 0 := fun t ht => by
    rw [ray_im]
    exact mul_ne_zero (fun h => ht (Subtype.ext h)) hwim
  have hbi : Function.Injective b := by
    have hstep : ∀ s t : unitInterval, t ≠ 0 → b s = b t → s ≠ 0 → s = t := fun s t ht h hs => by
      have h1 : χ (ray x₀ w t) ∉ bd S' := hoff _ (hrm t) (hrimpos t ht)
      have h2 := hJ.interior_inj _ h1 _ h.symm
      have h3 := hinj (hrm t) (hrm s) h2
      have h4 : t.1 * w.im = s.1 * w.im := by rw [← ray_im, ← ray_im, h3]
      exact (Subtype.ext (mul_right_cancel₀ hwim h4)).symm
    have hzoff : ∀ t : unitInterval, t ≠ 0 → b t ≠ z := fun t ht h => by
      have h1 : χ (ray x₀ w t) ∉ bd S' := hoff _ (hrm t) (hrimpos t ht)
      have h2 : φ (χ (ray x₀ w t)) ∈ bd S ∪ L.U := by
        have : b t = z := h
        simp only [b] at this
        rw [this]
        exact hzU.symm
      exact h1 ((hF _).mp h2)
    intro s t h
    by_cases hs : s = 0
    · by_cases ht : t = 0
      · rw [hs, ht]
      · exact absurd (by rw [← h, hs, hb0]) (hzoff t ht)
    · by_cases ht : t = 0
      · exact absurd (by rw [h, ht, hb0]) (hzoff s hs)
      · exact hstep s t ht h hs
  have hbY : ∀ t, b t ∈ Y := fun t => by
    rw [hY]
    exact ⟨_, ⟨_, hrm t, rfl⟩, rfl⟩
  have hL₁ : IsLineWithEnds (range b) z (a te) := by
    have := isLineWithEnds_range_of_arc (a := b) ⟨hbc, hbi⟩
    rwa [hb0, hb1] at this
  have hL₂ : IsLineWithEnds (range A) (a te) y := by
    have := isLineWithEnds_range_of_arc hA
    rwa [hA0, hA1, ha1] at this
  have hRY : range A ∩ Y = {a te} := by
    ext q
    constructor
    · rintro ⟨⟨s, rfl⟩, h⟩
      by_cases hs : s = 0
      · rw [hs, hA0]
        rfl
      · obtain ⟨s', hs', he⟩ := hAf s hs
        rw [he] at h
        exact absurd (htel h) (not_le.mpr hs')
    · rintro rfl
      exact ⟨⟨0, hA0⟩, htY⟩
  have hRc' : range A ⊆ c := by
    rintro _ ⟨s, rfl⟩
    by_cases hs : s = 0
    · rw [hs, hA0]
      exact hmemc te
    · obtain ⟨s', -, he⟩ := hAf s hs
      rw [he]
      exact hmemc s'
  have hinter : range b ∩ range A = {a te} := by
    ext q
    constructor
    · rintro ⟨⟨t, rfl⟩, h⟩
      have : b t ∈ range A ∩ Y := ⟨h, hbY t⟩
      rwa [hRY] at this
    · rintro rfl
      exact ⟨⟨1, hb1⟩, ⟨0, hA0⟩⟩
  -- The first part of the old edge lies in `Q₁`.
  have hemb : Topology.IsInducing a := (hac.isClosedEmbedding hai).isInducing
  have hpre : IsPreconnected (a ⁻¹' Q₁) := by
    rw [← hemb.isPreconnected_image, image_preimage_eq_of_subset (by
      rw [hr, hcQ]
      exact subset_union_left)]
    exact hQ₁p
  have hteQ : a te ∈ Q₁ := by
    have h1 : a te ∈ Q₁ ∪ Q₂ := hcQ ▸ hmemc te
    rcases h1 with h | h
    · exact h
    · exact (disjoint_left.mp hQ₂ h htY).elim
  have hIcc : Icc 0 te ⊆ a ⁻¹' Q₁ := hpre.Icc_subset (by rw [mem_preimage, ha0]; exact hzQ₁) hteQ
  refine ⟨w, range A, hw, hwB, hwpos, hpW, hpe ▸ hmemc te, hRc', ?_, ?_,
    (isCompact_range hA.1).isClosed, ?_, ?_⟩
  · rintro q ⟨hq, hqN⟩
    obtain ⟨s, rfl⟩ := hr.symm ▸ hq
    by_cases hs : te ≤ s
    · obtain ⟨s', hs'⟩ := hfA s hs
      exact ⟨s', hs'⟩
    · exact absurd (hQ₁N (hIcc ⟨unitInterval.nonneg _, (not_le.mp hs).le⟩)) hqN
  · rw [hRY, hpe]
  · exact hL₁.union hL₂ hinter
  · let pa : Path z y := ⟨⟨a, hac⟩, ha0, ha1⟩
    let κ₁ : Path z (a te) := ⟨⟨b, hbc⟩, hb0, hb1⟩
    let κ₂ : Path (a te) y := ⟨⟨A, hA.1⟩, hA0, hA1.trans ha1⟩
    let l₁ : Path z (a te) := (pa.subpath 0 te).cast (by simp [pa]) rfl
    have hl₁ : ∀ u, l₁ u ∈ Q₁ := fun u => by
      have h1 : (pa.subpath 0 te) u ∈ range (pa.subpath 0 te) := ⟨u, rfl⟩
      rw [Path.range_subpath] at h1
      obtain ⟨v, hv, he⟩ := h1
      rw [uIcc_of_le (show (0 : unitInterval) ≤ te from unitInterval.nonneg te)] at hv
      have h2 : l₁ u = pa v := he.symm
      rw [h2]
      exact hIcc hv
    refine ⟨κ₁.trans κ₂, l₁.trans κ₂, mem_trans (fun u => .inl ⟨u, rfl⟩) (fun u => .inr ⟨u,
      rfl⟩), mem_trans (fun u => hcQ ▸ .inl (hl₁ u)) (fun u => hRc' ⟨u, rfl⟩), ?_⟩
    exact (hN κ₁ l₁ (fun u => hYN (hbY u)) fun u => hQ₁N (hl₁ u)).hcomp (Path.Homotopic.refl _)

/-- The closed set `c` splits into a connected part `Q₁` in `N` that holds `z` (if it is not empty),
and a closed part `Q₂` off `T`. -/
def SplitEdge (c N : Set S) (z : S) (T : Set S) : Prop :=
  ∃ Q₁ Q₂ : Set S, IsClosed Q₂ ∧ c = Q₁ ∪ Q₂ ∧ Q₁ ⊆ N ∧ IsPreconnected Q₁ ∧ (Q₁.Nonempty → z ∈ Q₁)
    ∧ Disjoint Q₂ T

/-- A change of `c` inside a closed set off `T`, away from `N`, keeps the split. -/
theorem SplitEdge.change {c c' N Y Y' T : Set S} {z : S} (h : SplitEdge c N z T)
  (hc' : IsClosed c') (hY : IsClosed Y) (hNY : Disjoint N Y') (hTY : Disjoint Y T)
    (h1 : c' ⊆ c ∪ Y) (h2 : c \ Y' ⊆ c') : SplitEdge c' N z T := by
  obtain ⟨Q₁, Q₂, hQ₂, hc, hN, hp, hz, hd⟩ := h
  refine ⟨Q₁, c' ∩ (Q₂ ∪ Y), hc'.inter (hQ₂.union hY), Subset.antisymm (fun q hq => ?_) ?_, hN,
    hp, hz, ?_⟩
  · rcases h1 hq with hq' | hq'
    · rw [hc] at hq'
      rcases hq' with h3 | h3
      · exact .inl h3
      · exact .inr ⟨hq, .inl h3⟩
    · exact .inr ⟨hq, .inr hq'⟩
  · refine union_subset (fun q hq => h2 ⟨hc ▸ .inl hq, fun hqY => disjoint_left.mp hNY
      (hN hq) hqY⟩) inter_subset_left
  · rw [disjoint_left]
    rintro q ⟨-, h3 | h3⟩ hqT
    · exact disjoint_left.mp hd h3 hqT
    · exact disjoint_left.mp hTY h3 hqT

/-- A line with ends `a` and `b` carries a path from `a` to `b`. -/
theorem exists_path_of_line {L : Set S} {a b : S} (h : IsLineWithEnds L a b) : ∃ p : Path a b, ∀ u,
  p u ∈ L := by
  obtain ⟨f, rfl, rfl⟩ := h
  exact ⟨⟨⟨fun t => (f t).1, by fun_prop⟩, rfl, rfl⟩, fun u => (f u).2⟩

/-- Two edges meet only at vertices. -/
theorem closure_inter_closure_subset {H : Drawing S} {e f : Set S} (he : e ∈ H.E) (hf : f ∈ H.E)
  (hne : e ≠ f) : closure e ∩ closure f ⊆ H.V := by
  rintro q ⟨h1, h2⟩
  by_contra hq
  have h3 : q ∈ e := by rw [← H.closure_diff_V he]; exact ⟨h1, hq⟩
  have h4 : q ∈ f := by rw [← H.closure_diff_V hf]; exact ⟨h2, hq⟩
  exact hne (arcComponent_eq he hf h3 h4)

private theorem incident_edge_has_rectangular_cut
    {S : Type}
    {S' : Type}
    [TopologicalSpace S]
    [TopologicalSpace S']
    {L : Drawing S}
    {φ : S' → S}
    (hJ : IsCutAlongGraph L S' φ)
    {T : Set S}
    {z : S}
    (hzT : z ∈ T)
    (hzb : z ∈ bd S)
    {H : Drawing S}
    (hH : IsSurfaceForest H)
    {N : Set S}
    (hfl : Flat N)
    [CompactSpace S']
    [T2Space S]
    (Q₁ : Set S → Set S)
    (Q₂ : Set S → Set S)
    (hQ : ∀ e ∈ H.E, IsClosed (Q₂ e) ∧ closure e = Q₁ e ∪ Q₂ e ∧ Q₁ e ⊆ N ∧ IsPreconnected (Q₁ e)
      ∧ ((Q₁ e).Nonempty → z ∈ Q₁ e) ∧ Disjoint (Q₂ e) T) :
    let Cbad : Set S := (⋃ e ∈ H.E, Q₂ e) ∪ L.U \ T ∪ H.V \ {z}
    ∀ (χ : ℂ → S'),
    ∀ (x₁ : ℝ),
    ∀ (x₂ : ℝ),
    ∀ (δ : ℝ),
    (IsBdChart χ x₁ x₂ δ) →
    let Rc : Set ℂ := Icc x₁ x₂ ×ℂ Icc 0 δ
    let B : Set ℂ := Ioo x₁ x₂ ×ℂ Ico 0 δ
    ∀ (x₀ : ℝ),
    (x₀ ∈ Ioo x₁ x₂) →
    (φ (χ ↑x₀) = z) →
    let Y : Set S := φ '' χ '' Rc
    (∀ q ∈ Y, q ∈ N ∧ q ∉ Cbad) →
    let W₀ : Set S := (φ '' (χ '' B)ᶜ)ᶜ
    (IsOpen W₀) →
    (T ⊆ W₀) →
    (W₀ ⊆ Y) →
    (∀ q ∈ Y, q ∈ L.U → q ∈ W₀) →
    (∀ e ∈ H.E, z ∈ closure e → z ∈ H.V) →
    (∀ e ∈ H.E, Disjoint (Q₂ e) Y) →
    ∀ (e : Set S),
    (e ∈ H.E) →
    (z ∈ closure e) →
    ∃ w R y, closure e ∩ H.V = {z, y} ∧ w ∈ Rc ∧ w ∉ B ∧ 0 < w.im ∧ φ (χ w) ∉ W₀ ∧ φ (χ w) ∈
      closure e ∧ R ⊆ closure e ∧ closure e \ N ⊆ R ∧ R ∩ Y = {φ (χ w)} ∧ IsClosed R ∧
      IsLineWithEnds ((range fun t => φ (χ (ray x₀ w t))) ∪ R) z y ∧ ∃ κ l : Path z y, (∀ (u :
      ↑unitInterval), κ u ∈ (range fun t => φ (χ (ray x₀ w t))) ∪ R) ∧ (∀ (u : ↑unitInterval), l u
      ∈ closure e) ∧ κ.Homotopic l := by
  intro Cbad χ x₁ x₂ δ hχ Rc B x₀ hx₀ hzx Y hYM W₀ hW₀ hTW hW₀Y hYU hzH hQY e he hz
  obtain ⟨u, v, -, hcap, hline⟩ := edge_line_of_forest hH.2 he
  have hzc : z ∈ ({u, v} : Set S) := by rw [← hcap]; exact ⟨hz, hzH e he hz⟩
  obtain ⟨y, hcap', hline'⟩ : ∃ y, closure e ∩ H.V = {z, y} ∧ IsLineWithEnds (closure e) z y := by
    rcases hzc with rfl | h
    · exact ⟨v, hcap, hline⟩
    · obtain rfl : z = v := h
      exact ⟨u, by rw [hcap, pair_comm], hline.symm⟩
  obtain ⟨hclosed, hc, hN', hp, h0, hd⟩ := hQ e he
  have hyV : y ∈ closure e ∩ H.V := by rw [hcap']; exact .inr rfl
  have hne : y ≠ z := fun h => by
    have hC := edge_line_of_forest hH.2 he
    obtain ⟨u', v', huv, hcap'', -⟩ := hC
    rw [hcap', h] at hcap''
    simp only [mem_singleton_iff, insert_eq_of_mem] at hcap''
    have h1 : u' ∈ ({z} : Set S) := by rw [hcap'']; exact .inl rfl
    have h2 : v' ∈ ({z} : Set S) := by rw [hcap'']; exact .inr rfl
    exact huv (h1.trans h2.symm)
  have hyY : y ∉ Y := fun h => (hYM y h).2 (.inr ⟨hyV.2, hne⟩)
  have hcb : ∀ q ∈ closure e, q ≠ z → q ≠ y → q ∉ bd S := fun q hq h1 h2 hb => by
    have h3 : q ∈ closure e ∩ H.V := ⟨hq, hH.1 ⟨hb, H.closure_subset_U he hq⟩⟩
    rw [hcap'] at h3
    rcases h3 with h3 | h3
    · exact h1 h3
    · exact h2 h3
  have hne₁ : (Q₁ e).Nonempty := by
    by_contra hn
    rw [not_nonempty_iff_eq_empty] at hn
    rw [hn, empty_union] at hc
    exact disjoint_left.mp hd (hc ▸ hz) hzT
  obtain ⟨w, R, h⟩ := exists_new_line hJ hχ hx₀ hzx hline' rfl hW₀ (hTW hzT) hW₀Y hyY hcb hYU
    (.inr hzb) hfl (fun q hq => (hYM q hq).1) hc hN' hp (h0 hne₁) (hQY e he)
  exact ⟨w, R, y, hcap', h⟩

private theorem rerouted_incident_edges_inter_only_at_vertices
    {S : Type}
    [TopologicalSpace S]
    {z : S}
    {H : Drawing S}
    (Y : Set S)
    (hzH : ∀ e ∈ H.E, z ∈ closure e → z ∈ H.V)
    (R : Set S → Set S)
    (b : Set S → ↑unitInterval → S) :
    let G : Set S → Set S := fun e => range (b e)
    (∀ e ∈ H.E, z ∈ closure e → G e ⊆ Y) →
    (∀ (e : Set S), b e 0 = z) →
    (∀ e ∈ H.E, z ∈ closure e → ∀ f ∈ H.E, z ∈ closure f → e ≠ f → ∀ (t t' :
      ↑unitInterval), t ≠ 0 → t' ≠ 0 → b e t ≠ b f t') →
    (∀ e ∈ H.E, z ∈ closure e → ∀ q ∈ R e, q ∈ Y → q = b e 1) →
    ∀ (M : Set S → Set S),
    (∀ (e : Set S), z ∈ closure e → M e = G e ∪ R e) →
    (∀ e ∈ H.E, z ∈ closure e → R e ⊆ closure e) →
    ∀ (e : Set S),
    (e ∈ H.E) →
    (z ∈ closure e) →
    ∀ (f : Set S),
    (f ∈ H.E) →
    (z ∈ closure f) →
    (e ≠ f) →
    ∀ (q : S),
    (q ∈ M e ∩ M f) →
    q ∈ H.V := by
  intro G hGY hb0 hsame hRY M hMs hRc' e he hz f hf hzf hef q hq
  obtain ⟨h1, h2⟩ := hq
  rw [hMs e hz] at h1
  rw [hMs f hzf] at h2
  have hzV := hzH e he hz
  have hmix : ∀ e, e ∈ H.E → z ∈ closure e → ∀ f, f ∈ H.E → z ∈ closure f → e ≠ f → q ∈ G e
    → q ∈ R f → q ∈ H.V := fun e he hz f hf hzf hef h1 h2 => by
    obtain ⟨t, rfl⟩ := h1
    by_cases ht : t = 0
    · rw [ht, hb0]
      exact hzV
    · exact absurd (hRY f hf hzf _ h2 (hGY e he hz ⟨t, rfl⟩)) (hsame e he hz f hf hzf hef t 1 ht
        one_ne_zero)
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · obtain ⟨t, rfl⟩ := h1
      obtain ⟨t', ht'⟩ := h2
      by_cases ht : t = 0
      · rw [ht, hb0]
        exact hzV
      · by_cases ht0 : t' = 0
        · rw [← ht', ht0, hb0]
          exact hzV
        · exact absurd ht'.symm (hsame e he hz f hf hzf hef t t' ht ht0)
    · exact hmix e he hz f hf hzf hef h1 h2
  · rcases h2 with h2 | h2
    · exact hmix f hf hzf e he hz hef.symm h2 h1
    · exact closure_inter_closure_subset he hf hef ⟨hRc' e he hz h1, hRc' f hf hzf h2⟩

private theorem rerouted_and_unmoved_edges_inter_only_at_vertices
    {S : Type}
    [TopologicalSpace S]
    {z : S}
    {H : Drawing S}
    (Y : Set S)
    (R : Set S → Set S)
    (G : Set S → Set S)
    (hGY : ∀ e ∈ H.E, z ∈ closure e → G e ⊆ Y)
    (M : Set S → Set S)
    (hMs : ∀ (e : Set S), z ∈ closure e → M e = G e ∪ R e)
    (hMn : ∀ (e : Set S), z ∉ closure e → M e = closure e)
    (hRc' : ∀ e ∈ H.E, z ∈ closure e → R e ⊆ closure e)
    (hoffY : ∀ e ∈ H.E, z ∉ closure e → ∀ q ∈ closure e, q ∉ Y)
    (e : Set S)
    (he : e ∈ H.E)
    (hz : z ∈ closure e)
    (f : Set S)
    (hf : f ∈ H.E)
    (hzf : z ∉ closure f)
    (hef : e ≠ f)
    (q : S)
    (hq : q ∈ M e ∩ M f) :
    q ∈ H.V := by
  obtain ⟨h1, h2⟩ := hq
  rw [hMs e hz] at h1
  rw [hMn f hzf] at h2
  rcases h1 with h1 | h1
  · exact absurd (hGY e he hz h1) (hoffY f hf hzf q h2)
  · exact closure_inter_closure_subset he hf hef ⟨hRc' e he hz h1, h2⟩

private theorem root_set_in_open_neighbourhood
    {S : Type}
    {S' : Type}
    [TopologicalSpace S']
    {φ : S' → S}
    {T : Set S}
    (χ : ℂ → S')
    (x₁ : ℝ)
    (x₂ : ℝ)
    (δ : ℝ)
    (hχ : IsBdChart χ x₁ x₂ δ)
    (hA : ∀ a ∈ φ ⁻¹' T, ∃ x ∈ Ioo x₁ x₂, χ ↑x = a) :
    let B : Set ℂ := Ioo x₁ x₂ ×ℂ Ico 0 δ
    let W₀ : Set S := (φ '' (χ '' B)ᶜ)ᶜ
    T ⊆ W₀ := by
  intro B W₀
  rintro t ht ⟨x, hx, rfl⟩
  obtain ⟨r, hr, he⟩ := hA x ht
  refine hx ⟨r, ?_, he⟩
  refine ⟨?_, ?_⟩
  · rw [mem_preimage, ofReal_re]
    exact hr
  · rw [mem_preimage, ofReal_im]
    exact ⟨le_rfl, hχ.hδ⟩

private theorem rerouted_edge_subset_original_union_chart
    {S : Type}
    [TopologicalSpace S]
    {z : S}
    {H : Drawing S}
    (Y : Set S)
    (R : Set S → Set S)
    (G : Set S → Set S)
    (hGY : ∀ e ∈ H.E, z ∈ closure e → G e ⊆ Y)
    (M : Set S → Set S)
    (hMs : ∀ (e : Set S), z ∈ closure e → M e = G e ∪ R e)
    (hMn : ∀ (e : Set S), z ∉ closure e → M e = closure e)
    (hRc' : ∀ e ∈ H.E, z ∈ closure e → R e ⊆ closure e)
    (e : Set S)
    (he : e ∈ H.E)
    (q : S)
    (hq : q ∈ M e) :
    q ∈ closure e ∪ Y := by
  by_cases hz : z ∈ closure e
  · rw [hMs e hz] at hq
    rcases hq with h1 | h1
    · exact .inr (hGY e he hz h1)
    · exact .inl (hRc' e he hz h1)
  · rw [hMn e hz] at hq
    exact .inl hq

private theorem assemble_forest_root_step
    {S : Type}
    {S' : Type}
    [TopologicalSpace S]
    [TopologicalSpace S']
    {L : Drawing S}
    {φ : S' → S}
    (hJ : IsCutAlongGraph L S' φ)
    {T : Set S}
    (hTU : T ⊆ L.U)
    {z : S}
    (hzT : z ∈ T)
    (hzb : z ∈ bd S)
    {l₀ : S'}
    {H : Drawing S}
    {N : Set S}
    (hV : ∀ v ∈ H.V, v ≠ z → v ∉ T)
    [T2Space S']
    (hφ : Continuous φ)
    (hFiff : ∀ (q : S'), φ q ∈ bd S ∪ L.U ↔ q ∈ bd S')
    (hEfin : H.E.Finite)
    (Q₁ : Set S → Set S)
    (Q₂ : Set S → Set S)
    (hQ : ∀ e ∈ H.E, IsClosed (Q₂ e) ∧ closure e = Q₁ e ∪ Q₂ e ∧ Q₁ e ⊆ N ∧ IsPreconnected (Q₁ e)
      ∧ ((Q₁ e).Nonempty → z ∈ Q₁ e) ∧ Disjoint (Q₂ e) T)
    (χ : ℂ → S')
    (x₁ : ℝ)
    (x₂ : ℝ)
    (δ : ℝ)
    (hχ : IsBdChart χ x₁ x₂ δ) :
    let Rc : Set ℂ := Icc x₁ x₂ ×ℂ Icc 0 δ
    ∀ (B : Set ℂ),
    ∀ (x₀ : ℝ),
    (χ ↑x₀ = l₀) →
    ∀ (Y : Set S),
    (IsClosed Y) →
    ∀ (W₀ : Set S),
    (T ⊆ W₀) →
    (W₀ ⊆ Y) →
    (∀ e ∈ H.E, z ∈ closure e → z ∈ H.V) →
    (∀ e ∈ H.E, z ∉ closure e → closure e = Q₂ e) →
    ∀ (w : Set S → ℂ),
    ∀ (R : Set S → Set S),
    ∀ (y : (e : Set S) → e ∈ H.E → z ∈ closure e → S),
    (∀ (e : Set S) (a : e ∈ H.E) (a_1 : z ∈ closure e), closure e ∩ H.V = {z, y e a a_1} ∧
      w e ∈ Rc ∧ w e ∉ B ∧ 0 < (w e).im ∧ φ (χ (w e)) ∉ W₀ ∧ φ (χ (w e)) ∈ closure e ∧ R e ⊆
      closure e ∧ closure e \ N ⊆ R e ∧ R e ∩ Y = {φ (χ (w e))} ∧ IsClosed (R e) ∧ IsLineWithEnds
      ((range fun t => φ (χ (ray x₀ (w e) t))) ∪ R e) z (y e a a_1) ∧ ∃ κ l : Path z (y e a a_1),
      (∀ (u : ↑unitInterval), κ u ∈ (range fun t => φ (χ (ray x₀ (w e) t))) ∪ R e) ∧ (∀ (u :
      ↑unitInterval), l u ∈ closure e) ∧ κ.Homotopic l) →
    let b : Set S → ↑unitInterval → S := fun e t => φ (χ (ray x₀ (w e) t))
    let G : Set S → Set S := fun e => range (b e)
    (∀ e ∈ H.E, z ∈ closure e → ∀ (t : ↑unitInterval), ray x₀ (w e) t ∈ Rc) →
    (∀ e ∈ H.E, z ∈ closure e → ∀ (t : ↑unitInterval), t ≠ 0 → χ (ray x₀ (w e) t) ∉ bd
      S') →
    (∀ e ∈ H.E, z ∈ closure e → ∀ (t : ↑unitInterval), t ≠ 0 → b e t ∉ bd S ∪ L.U) →
    (∀ (e : Set S), b e 0 = z) →
    (∀ e ∈ H.E, z ∈ closure e → ∀ q ∈ R e, q ∈ Y → q = b e 1) →
    ∀ (M : Set S → Set S),
    (∀ (e : Set S), z ∈ closure e → M e = G e ∪ R e) →
    (∀ (e : Set S), z ∉ closure e → M e = closure e) →
    ∀ (P : Drawing S),
    (P.V = H.V) →
    (P.U = H.V ∪ ⋃ e ∈ H.E, M e) →
    (IsSurfaceForest P) →
    (ForestsHomotopic P H) →
    (∀ e' ∈ P.E, ∃ e ∈ H.E, closure e' = M e) →
    (Y ⊆ N) →
    (∀ e ∈ H.E, M e ⊆ closure e ∪ Y) →
    ∃ (P : Drawing S) (Y : Set S), IsClosed Y ∧ Y ⊆ N ∧ P.V = H.V ∧ IsSurfaceForest P ∧
      ForestsHomotopic P H ∧ P.U ∩ T ⊆ {z} ∧ (∀ e' ∈ P.E, ∃ e ∈ H.E, closure e' ⊆ closure e ∪ Y ∧
      closure e \ N ⊆ closure e') ∧ P.U ⊆ H.U ∪ Y ∧ ∀ z' ∈ φ ⁻¹' {z}, z' ≠ l₀ → z' ∉ closure (φ
      ⁻¹' (P.U \ P.V)) := by
  intro Rc B x₀ hxl Y hYc W₀ hTW hW₀Y hzH hnon w R y hP b G hrm hoffb hoffF hb0 hRY M hMs hMn P
    hPV hPU hPf hPh hPe hYN hMY
  classical
  refine ⟨P, Y, hYc, hYN, hPV, hPf, hPh, ?_, ?_, ?_, ?_⟩
  · rintro q ⟨hq, hqT⟩
    rw [hPU] at hq
    rcases hq with h | h
    · by_contra hn
      exact hV q h hn hqT
    · obtain ⟨e, he, h⟩ := mem_iUnion₂.mp h
      by_cases hz : z ∈ closure e
      · rw [hMs e hz] at h
        rcases h with ⟨t, rfl⟩ | h1
        · by_cases ht : t = 0
          · rw [ht, hb0]
            rfl
          · exact absurd (Or.inr (hTU hqT)) (hoffF e he hz t ht)
        · have h2 := hRY e he hz q h1 (hW₀Y (hTW hqT))
          have h3 : φ (χ (w e)) ∉ W₀ := (hP e he hz).2.2.2.2.1
          have h4 : b e 1 = φ (χ (w e)) := by simp only [b, ray_one]
          rw [h2, h4] at hqT
          exact absurd (hTW hqT) h3
      · rw [hMn e hz, hnon e he hz] at h
        exact absurd hqT (disjoint_left.mp (hQ e he).2.2.2.2.2 h)
  · intro e' he'
    obtain ⟨e, he, hc⟩ := hPe e' he'
    refine ⟨e, he, hc ▸ hMY e he, fun q hq => ?_⟩
    rw [hc]
    by_cases hz : z ∈ closure e
    · rw [hMs e hz]
      exact .inr ((hP e he hz).2.2.2.2.2.2.2.1 hq)
    · rw [hMn e hz]
      exact hq.1
  · rw [hPU]
    refine union_subset (fun q hq => .inl (H.V_subset_U hq)) (iUnion₂_subset fun e he q hq => ?_)
    rcases hMY e he hq with h | h
    · exact .inl (H.closure_subset_U he h)
    · exact .inr h
  · intro z' hz' hne hin
    have hz'' : φ z' = z := hz'
    let C : Set S := ⋃ e ∈ H.E, if z ∈ closure e then R e else closure e
    have hCcl : IsClosed C := hEfin.isClosed_biUnion fun e he => by
      by_cases hz : z ∈ closure e
      · rw [ite_eq_left hz]
        exact (hP e he hz).2.2.2.2.2.2.2.2.2.1
      · rw [ite_eq_right hz]
        exact isClosed_closure
    let D : Set S' := ⋃ e ∈ {e ∈ H.E | z ∈ closure e}, χ '' range (ray x₀ (w e))
    have hDc : IsClosed D := (hEfin.subset (sep_subset _ _)).isClosed_biUnion fun e he => by
      have h1 : IsCompact (range (ray x₀ (w e))) := isCompact_range (continuous_ray _ _)
      have h2 : range (ray x₀ (w e)) ⊆ Rc := by
        rintro _ ⟨t, rfl⟩
        exact hrm e he.1 he.2 t
      exact (h1.image_of_continuousOn (hχ.cont.mono h2)).isClosed
    have hsub : φ ⁻¹' (P.U \ P.V) ⊆ φ ⁻¹' C ∪ D := by
      rintro q ⟨hq1, hq2⟩
      rw [hPU] at hq1
      rw [hPV] at hq2
      rcases hq1 with h | h
      · exact absurd h hq2
      · obtain ⟨e, he, h⟩ := mem_iUnion₂.mp h
        by_cases hz : z ∈ closure e
        · rw [hMs e hz] at h
          rcases h with ⟨t, ht⟩ | h1
          · by_cases ht0 : t = 0
            · rw [ht0, hb0] at ht
              exact absurd (ht ▸ hzH e he hz) hq2
            · have h2 : q = χ (ray x₀ (w e) t) := (hJ.interior_inj _ (hoffb e he hz t ht0) _
                ht).symm
              exact .inr (mem_iUnion₂.mpr ⟨e, ⟨he, hz⟩, _, ⟨t, rfl⟩, h2.symm⟩)
          · refine .inl (mem_iUnion₂.mpr ⟨e, he, ?_⟩)
            rw [ite_eq_left hz]
            exact h1
        · refine .inl (mem_iUnion₂.mpr ⟨e, he, ?_⟩)
          rw [ite_eq_right hz]
          rw [hMn e hz] at h
          exact h
    have hcl := closure_minimal hsub ((hCcl.preimage hφ).union hDc) hin
    rcases hcl with h | h
    · obtain ⟨e, he, h⟩ := mem_iUnion₂.mp h
      by_cases hz : z ∈ closure e
      · rw [ite_eq_left hz] at h
        have h1 : z ∈ R e := hz'' ▸ h
        have h2 := hRY e he hz z h1 (hW₀Y (hTW hzT))
        have h3 : φ (χ (w e)) ∉ W₀ := (hP e he hz).2.2.2.2.1
        have h4 : b e 1 = φ (χ (w e)) := by simp only [b, ray_one]
        rw [h4] at h2
        exact h3 (h2 ▸ hTW hzT)
      · rw [ite_eq_right hz] at h
        exact hz (hz'' ▸ h)
    · obtain ⟨e, he, _, ⟨t, rfl⟩, h1⟩ := mem_iUnion₂.mp h
      by_cases ht : t = 0
      · rw [ht, ray_zero, hxl] at h1
        exact hne h1.symm
      · refine hoffb e he.1 he.2 t ht ?_
        rw [h1, ← hFiff, hz'']
        exact .inl hzb

private theorem distinct_incident_edges_have_distinct_cut_points
    {S : Type}
    {S' : Type}
    [TopologicalSpace S]
    {L : Drawing S}
    {φ : S' → S}
    {T : Set S}
    {z : S}
    (hzT : z ∈ T)
    {H : Drawing S}
    {N : Set S}
    (Q₂ : Set S → Set S) :
    let Cbad : Set S := (⋃ e ∈ H.E, Q₂ e) ∪ L.U \ T ∪ H.V \ {z}
    ∀ (χ : ℂ → S'),
    ∀ (Rc : Set ℂ),
    ∀ (B : Set ℂ),
    ∀ (x₀ : ℝ),
    let Y : Set S := φ '' χ '' Rc
    (∀ q ∈ Y, q ∈ N ∧ q ∉ Cbad) →
    ∀ (W₀ : Set S),
    (T ⊆ W₀) →
    ∀ (w : Set S → ℂ),
    ∀ (R : Set S → Set S),
    ∀ (y : (e : Set S) → e ∈ H.E → z ∈ closure e → S),
    (∀ (e : Set S) (a : e ∈ H.E) (a_1 : z ∈ closure e), closure e ∩ H.V = {z, y e a a_1} ∧
      w e ∈ Rc ∧ w e ∉ B ∧ 0 < (w e).im ∧ φ (χ (w e)) ∉ W₀ ∧ φ (χ (w e)) ∈ closure e ∧ R e ⊆
      closure e ∧ closure e \ N ⊆ R e ∧ R e ∩ Y = {φ (χ (w e))} ∧ IsClosed (R e) ∧ IsLineWithEnds
      ((range fun t => φ (χ (ray x₀ (w e) t))) ∪ R e) z (y e a a_1) ∧ ∃ κ l : Path z (y e a a_1),
      (∀ (u : ↑unitInterval), κ u ∈ (range fun t => φ (χ (ray x₀ (w e) t))) ∪ R e) ∧ (∀ (u :
      ↑unitInterval), l u ∈ closure e) ∧ κ.Homotopic l) →
    ∀ (e : Set S),
    (e ∈ H.E) →
    (z ∈ closure e) →
    ∀ (f : Set S),
    (f ∈ H.E) →
    (z ∈ closure f) →
    (e ≠ f) →
    (w e = w f) →
    False := by
  intro Cbad χ Rc B x₀ Y hYM W₀ hTW w R y hP e he hz f hf hzf hef h
  have hp := hP e he hz
  have hq := hP f hf hzf
  have h1 : φ (χ (w e)) ∈ closure e := hp.2.2.2.2.2.1
  have h2 : φ (χ (w e)) ∈ closure f := h ▸ hq.2.2.2.2.2.1
  have h3 := closure_inter_closure_subset he hf hef ⟨h1, h2⟩
  have h4 : φ (χ (w e)) ∈ Y := ⟨_, ⟨_, hp.2.1, rfl⟩, rfl⟩
  have h5 : φ (χ (w e)) ≠ z := fun h6 => hp.2.2.2.2.1 (h6 ▸ hTW hzT)
  exact (hYM _ h4).2 (.inr ⟨h3, h5⟩)

private theorem distinct_rerouting_rays_avoid_each_other
    {S : Type}
    {S' : Type}
    [TopologicalSpace S]
    [TopologicalSpace S']
    {L : Drawing S}
    {φ : S' → S}
    (hJ : IsCutAlongGraph L S' φ)
    {z : S}
    {H : Drawing S}
    {N : Set S}
    (χ : ℂ → S')
    (x₁ : ℝ)
    (x₂ : ℝ)
    (δ : ℝ)
    (hχ : IsBdChart χ x₁ x₂ δ) :
    let Rc : Set ℂ := Icc x₁ x₂ ×ℂ Icc 0 δ
    let B : Set ℂ := Ioo x₁ x₂ ×ℂ Ico 0 δ
    ∀ (x₀ : ℝ),
    (x₀ ∈ Ioo x₁ x₂) →
    ∀ (Y : Set S),
    ∀ (W₀ : Set S),
    ∀ (w : Set S → ℂ),
    ∀ (R : Set S → Set S),
    ∀ (y : (e : Set S) → e ∈ H.E → z ∈ closure e → S),
    (∀ (e : Set S) (a : e ∈ H.E) (a_1 : z ∈ closure e), closure e ∩ H.V = {z, y e a a_1} ∧
      w e ∈ Rc ∧ w e ∉ B ∧ 0 < (w e).im ∧ φ (χ (w e)) ∉ W₀ ∧ φ (χ (w e)) ∈ closure e ∧ R e ⊆
      closure e ∧ closure e \ N ⊆ R e ∧ R e ∩ Y = {φ (χ (w e))} ∧ IsClosed (R e) ∧ IsLineWithEnds
      ((range fun t => φ (χ (ray x₀ (w e) t))) ∪ R e) z (y e a a_1) ∧ ∃ κ l : Path z (y e a a_1),
      (∀ (u : ↑unitInterval), κ u ∈ (range fun t => φ (χ (ray x₀ (w e) t))) ∪ R e) ∧ (∀ (u :
      ↑unitInterval), l u ∈ closure e) ∧ κ.Homotopic l) →
    let b : Set S → ↑unitInterval → S := fun e t => φ (χ (ray x₀ (w e) t))
    (∀ e ∈ H.E, z ∈ closure e → ∀ (t : ↑unitInterval), ray x₀ (w e) t ∈ Rc) →
    (∀ e ∈ H.E, z ∈ closure e → ∀ (t : ↑unitInterval), t ≠ 0 → χ (ray x₀ (w e) t) ∉ bd
      S') →
    (∀ e ∈ H.E, z ∈ closure e → ∀ f ∈ H.E, z ∈ closure f → e ≠ f → w e ≠ w f) →
    ∀ e ∈ H.E, z ∈ closure e → ∀ f ∈ H.E, z ∈ closure f → e ≠ f → ∀ (t t' : ↑unitInterval), t ≠ 0
      → t' ≠ 0 → b e t ≠ b f t' := by
  intro Rc B x₀ hx₀ Y W₀ w R y hP b hrm hoffb hwne e he hz f hf hzf hef t t' ht ht' h
  have h1 := hJ.interior_inj _ (hoffb e he hz t ht) _ h
  have h2 := hχ.inj (hrm e he hz t) (hrm f hf hzf t') h1
  have hp := hP e he hz
  have hq := hP f hf hzf
  exact hwne e he hz f hf hzf hef (ray_eq hx₀ hp.2.1 hq.2.1 hp.2.2.2.1 hq.2.2.2.1 hp.2.2.1
    hq.2.2.1 (unitInterval.pos_iff_ne_zero.mpr ht) (unitInterval.pos_iff_ne_zero.mpr ht') h2)

/-- **The step of (4.4) at one root.** Let `T` be a component of the forest `L`, with the point `z`
on `bd(Σ)`, and let `N` be a flat open set around `T`. If the only vertex of `H` on `T` is `z`, and
the edges of `H` split as in `SplitEdge`, then we can change `H` inside `N` so that it meets `T`
only at `z`, and it leaves `z` only from the point `l₀` of the fibre of `z`. -/
theorem exists_root_step (hS : IsSurface S) {L : Drawing S} {φ : S' → S}
  (hJ : IsCutAlongGraph L S' φ) (hNo : NoArcs L) {T : Set S} (hT : IsPreconnected T)
    (hTc : IsClosed T) (hrest : IsClosed (L.U \ T)) (hTU : T ⊆ L.U)
    {z : S} (hzT : z ∈ T) (hzb : z ∈ bd S) {l₀ : S'} (hl₀ : φ l₀ = z) {H : Drawing S}
      (hH : IsSurfaceForest H) {N : Set S} (hNo' : IsOpen N) (hfl : Flat N) (hTN : T ⊆ N)
    (hV : ∀ v ∈ H.V, v ≠ z → v ∉ T) (hE : ∀ e ∈ H.E, SplitEdge (closure e) N z T) :
    ∃ (P : Drawing S) (Y : Set S), IsClosed Y ∧ Y ⊆ N ∧ P.V = H.V ∧ IsSurfaceForest P
      ∧ ForestsHomotopic P H ∧ P.U ∩ T ⊆ {z} ∧ (∀ e' ∈ P.E, ∃ e ∈ H.E, closure e' ⊆ closure e ∪ Y
        ∧ closure e \ N ⊆ closure e') ∧ P.U ⊆ H.U ∪ Y ∧
      ∀ z' ∈ φ ⁻¹' {z}, z' ≠ l₀ → z' ∉ closure (φ ⁻¹' (P.U \ P.V)) := by
  classical
  have hY' := hJ.isSurface
  have : CompactSpace S' := hY'.1
  have : T2Space S' := hY'.2.1
  have : T2Space S := hS.2.1
  have hφ := hJ.quotientMap.continuous
  have hsurj := hJ.quotientMap.surjective
  have hFiff : ∀ q, φ q ∈ bd S ∪ L.U ↔ q ∈ bd S' := fun q => by rw [← hJ.preimage_bd_union_U]; rfl
  have hEfin : H.E.Finite := H.finite_edges
  choose! Q₁ Q₂ hQ using hE
  let Cbad : Set S := (⋃ e ∈ H.E, Q₂ e) ∪ (L.U \ T) ∪ (H.V \ {z})
  have hCc : IsClosed Cbad := ((hEfin.isClosed_biUnion fun e he => (hQ e he).1).union hrest).union
    (H.finite_V.subset sdiff_subset).isClosed
  have hTC : ∀ t ∈ T, t ∉ Cbad := fun t ht => by
    rintro ((h | h) | h)
    · obtain ⟨e, he, h⟩ := mem_iUnion₂.mp h
      exact disjoint_left.mp (hQ e he).2.2.2.2.2 h ht
    · exact h.2 ht
    · exact hV t h.1 h.2 ht
  obtain ⟨χ, x₁, x₂, δ, hχ, hmap, hA⟩ := exists_tree_chart hS hJ hNo hT hTc hrest hTU hzT hzb
    (hNo'.inter hCc.isOpen_compl) fun t ht => ⟨hTN ht, hTC t ht⟩
  set Rc : Set ℂ := Icc x₁ x₂ ×ℂ Icc 0 δ with hRc
  set B : Set ℂ := Ioo x₁ x₂ ×ℂ Ico 0 δ with hB
  have hRcc : IsCompact Rc := isCompact_Icc.reProdIm isCompact_Icc
  obtain ⟨x₀, hx₀, hxl⟩ := hA l₀ (by rw [mem_preimage, hl₀]; exact hzT)
  have hzx : φ (χ x₀) = z := by rw [hxl, hl₀]
  let Y : Set S := φ '' (χ '' Rc)
  have hYc : IsClosed Y := ((hRcc.image_of_continuousOn hχ.cont).image hφ).isClosed
  have hYM : ∀ q ∈ Y, q ∈ N ∧ q ∉ Cbad := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact hmap w hw
  have hBR : B ⊆ Rc := fun u hu => ⟨Ioo_subset_Icc_self hu.1, Ico_subset_Icc_self hu.2⟩
  let W₀ : Set S := (φ '' (χ '' B)ᶜ)ᶜ
  have hW₀ : IsOpen W₀ := (hφ.isClosedMap _ hχ.isOpen.isClosed_compl).isOpen_compl
  have hTW : T ⊆ W₀ := by
    exact root_set_in_open_neighbourhood (S := S) (S' := S') (φ := φ) (T := T) χ x₁ x₂ δ hχ hA
  have hW₀Y : W₀ ⊆ Y := fun q hq => by
    obtain ⟨x, rfl⟩ := hsurj q
    by_contra hn
    refine hq ⟨x, fun hx => hn ?_, rfl⟩
    obtain ⟨u, hu, rfl⟩ := hx
    exact ⟨_, ⟨u, hBR hu, rfl⟩, rfl⟩
  have hYU : ∀ q ∈ Y, q ∈ L.U → q ∈ W₀ := fun q hq hU => by
    by_cases hqT : q ∈ T
    · exact hTW hqT
    · exact absurd (Or.inl (Or.inr ⟨hU, hqT⟩)) (hYM q hq).2
  have hzH : ∀ e ∈ H.E, z ∈ closure e → z ∈ H.V := fun e he hz => hH.1 ⟨hzb, H.closure_subset_U he
    hz⟩
  -- An edge off `z` misses `Y`.
  have hnon : ∀ e ∈ H.E, z ∉ closure e → closure e = Q₂ e := fun e he hz => by
    obtain ⟨-, hc, -, -, h0, -⟩ := hQ e he
    have h1 : Q₁ e = ∅ := by
      by_contra hne
      exact hz (hc ▸ .inl (h0 (nonempty_iff_ne_empty.mpr hne)))
    rw [hc, h1, empty_union]
  have hQY : ∀ e ∈ H.E, Disjoint (Q₂ e) Y := fun e he => by
    rw [disjoint_left]
    intro q h1 h2
    exact (hYM q h2).2 (.inl (.inl (mem_iUnion₂.mpr ⟨e, he, h1⟩)))
  have hstar : ∀ e, e ∈ H.E → z ∈ closure e → ∃ (w : ℂ) (R : Set S) (y : S), closure e ∩ H.V
    = {z, y} ∧ w ∈ Rc ∧ w ∉ B ∧ 0 < w.im ∧ φ (χ w) ∉ W₀ ∧ φ (χ w) ∈ closure e ∧ R ⊆ closure e
      ∧ closure e \ N ⊆ R ∧ R ∩ Y = {φ (χ w)} ∧ IsClosed R ∧
      IsLineWithEnds (range (fun t => φ (χ (ray x₀ w t))) ∪ R) z y ∧ ∃ κ l : Path z y,
        (∀ u, κ u ∈ range (fun t => φ (χ (ray x₀ w t))) ∪ R) ∧ (∀ u, l u ∈ closure e)
          ∧ κ.Homotopic l := fun e he hz => by
    exact incident_edge_has_rectangular_cut (S := S) (S' := S') (L := L) (φ := φ) hJ (T := T) (z
      := z) hzT hzb (H := H) hH (N := N) hfl Q₁ Q₂ hQ  χ x₁ x₂ δ hχ   x₀ hx₀ hzx  hYM
      hW₀ hTW hW₀Y hYU hzH hQY e he hz
  choose! w R y hP using hstar
  let b : Set S → unitInterval → S := fun e t => φ (χ (ray x₀ (w e) t))
  let G : Set S → Set S := fun e => range (b e)
  have hrm : ∀ e, e ∈ H.E → z ∈ closure e → ∀ t, ray x₀ (w e) t ∈ Rc := fun e he hz => ray_mem hx₀
    (hP e he hz).2.1
  have hGY : ∀ e, e ∈ H.E → z ∈ closure e → G e ⊆ Y := by
    rintro e he hz _ ⟨t, rfl⟩
    exact ⟨_, ⟨_, hrm e he hz t, rfl⟩, rfl⟩
  have him : ∀ e, e ∈ H.E → z ∈ closure e → ∀ t : unitInterval, t ≠ 0 → (ray x₀ (w e) t).im ≠ 0
    := fun e he hz t ht => by
    rw [ray_im]
    exact mul_ne_zero (fun h => ht (Subtype.ext h)) (hP e he hz).2.2.2.1.ne'
  have hoffb : ∀ e, e ∈ H.E → z ∈ closure e → ∀ t : unitInterval, t ≠ 0 → χ (ray x₀
    (w e) t) ∉ bd S' := fun e he hz t ht h =>
    him e he hz t ht ((hχ.bd _ (hrm e he hz t)).mp h)
  have hoffF : ∀ e, e ∈ H.E → z ∈ closure e → ∀ t : unitInterval, t ≠ 0 → b e t ∉ bd S ∪ L.U
    := fun e he hz t ht h =>
    hoffb e he hz t ht ((hFiff _).mp h)
  have hb0 : ∀ e, b e 0 = z := fun e => by simp only [b, ray_zero, hzx]
  -- Different edges at `z` end at different points of the rectangle.
  have hwne : ∀ e, e ∈ H.E → z ∈ closure e → ∀ f, f ∈ H.E → z ∈ closure f → e ≠ f → w e ≠ w f
    := fun e he hz f hf hzf hef h => by
    exact distinct_incident_edges_have_distinct_cut_points (S := S) (S' := S') (L := L) (φ := φ)
      (T := T) (z := z) hzT (H := H) (N := N) Q₂  χ Rc B x₀  hYM W₀ hTW w R y hP e he hz f hf
      hzf hef h
  have hsame : ∀ e, e ∈ H.E → z ∈ closure e → ∀ f, f ∈ H.E → z ∈ closure f → e ≠ f
    → ∀ t t' : unitInterval, t ≠ 0 → t' ≠ 0 → b e t ≠ b f t' := by
    exact distinct_rerouting_rays_avoid_each_other (S := S) (S' := S') (L := L) (φ := φ) hJ (z :=
      z) (H := H) (N := N) χ x₁ x₂ δ hχ   x₀ hx₀ Y W₀ w R y hP  hrm hoffb hwne
  have hRY : ∀ e, e ∈ H.E → z ∈ closure e → ∀ q ∈ R e, q ∈ Y → q = b e 1 := fun e he hz q h1 h2
    => by
    have h3 : q ∈ R e ∩ Y := ⟨h1, h2⟩
    rw [(hP e he hz).2.2.2.2.2.2.2.2.1] at h3
    have : b e 1 = φ (χ (w e)) := by simp only [b, ray_one]
    rw [this]
    exact h3
  let M : Set S → Set S := fun e => if z ∈ closure e then G e ∪ R e else closure e
  have hMs : ∀ e, z ∈ closure e → M e = G e ∪ R e := fun e h => ite_eq_left h
  have hMn : ∀ e, z ∉ closure e → M e = closure e := fun e h => ite_eq_right h
  have hRc' : ∀ e, e ∈ H.E → z ∈ closure e → R e ⊆ closure e := fun e he hz =>
    (hP e he hz).2.2.2.2.2.2.1
  have hoffY : ∀ e, e ∈ H.E → z ∉ closure e → ∀ q ∈ closure e, q ∉ Y := fun e he hz q hq hY => by
    rw [hnon e he hz] at hq
    exact disjoint_left.mp (hQY e he) hq hY
  have hmeet₁ : ∀ e, e ∈ H.E → z ∈ closure e → ∀ f, f ∈ H.E → z ∈ closure f → e ≠ f
    → M e ∩ M f ⊆ H.V := fun e he hz f hf hzf hef q hq => by
    exact rerouted_incident_edges_inter_only_at_vertices (S := S) (z := z) (H := H) Y hzH R b
      hGY hb0 hsame hRY M hMs hRc' e he hz f hf hzf hef q hq
  have hmeet₂ : ∀ e, e ∈ H.E → z ∈ closure e → ∀ f, f ∈ H.E → z ∉ closure f → e ≠ f
    → M e ∩ M f ⊆ H.V := fun e he hz f hf hzf hef q hq => by
    exact rerouted_and_unmoved_edges_inter_only_at_vertices (S := S) (z := z) (H := H) Y R G hGY M
      hMs hMn hRc' hoffY e he hz f hf hzf hef q hq
  obtain ⟨P, hPV, hPU, hPf, hPh, hPe, -⟩ := exists_reroute hH M (fun e a c hl => by
      by_cases hz : z ∈ closure e
      · have hp := hP e hl.1 hz
        generalize y e hl.1 hz = y' at hp
        rw [hMs e hz]
        have h1 : ({a, c} : Set S) = {z, y'} := hl.2.2.2.symm.trans hp.1
        have hline := hp.2.2.2.2.2.2.2.2.2.2.1
        rcases pair_eq_pair_iff.mp h1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hline
        · exact hline.symm
      · rw [hMn e hz]
        obtain ⟨u, v, -, hcap, hline⟩ := edge_line_of_forest hH.2 hl.1
        have h1 := hl.2.2.2
        rw [hcap] at h1
        rcases pair_eq_pair_iff.mp h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
        · rw [← h2, ← h3]
          exact hline
        · rw [← h2, ← h3]
          exact hline.symm) (fun e he q hq => by
      by_cases hz : z ∈ closure e
      · rw [hMs e hz] at hq
        rcases hq.1 with h1 | h1
        · by_cases hqz : q = z
          · rw [hqz]
            exact hz
          · exact absurd (Or.inr ⟨hq.2, hqz⟩) (hYM q (hGY e he hz h1)).2
        · exact hRc' e he hz h1
      · rw [hMn e hz] at hq
        exact hq.1) (fun e he f hf hef => by
      by_cases hz : z ∈ closure e
      · by_cases hzf : z ∈ closure f
        · exact hmeet₁ e he hz f hf hzf hef
        · exact hmeet₂ e he hz f hf hzf hef
      · by_cases hzf : z ∈ closure f
        · rw [inter_comm]
          exact hmeet₂ f hf hzf e he hz hef.symm
        · rw [hMn e hz, hMn f hzf]
          exact closure_inter_closure_subset he hf hef) (fun e he q hq => by
      by_cases hz : z ∈ closure e
      · rw [hMs e hz] at hq
        rcases hq.1 with ⟨t, rfl⟩ | h1
        · by_cases ht : t = 0
          · rw [ht, hb0]
            exact hzH e he hz
          · exact absurd (Or.inl hq.2) (hoffF e he hz t ht)
        · exact hH.1 ⟨hq.2, H.closure_subset_U he (hRc' e he hz h1)⟩
      · rw [hMn e hz] at hq
        exact hH.1 ⟨hq.2, H.closure_subset_U he hq.1⟩) (fun e a c hl => by
      by_cases hz : z ∈ closure e
      · have hp := hP e hl.1 hz
        generalize y e hl.1 hz = y' at hp
        rw [hMs e hz]
        obtain ⟨κ, l, h1, h2, h3⟩ := hp.2.2.2.2.2.2.2.2.2.2.2
        have h4 : ({a, c} : Set S) = {z, y'} := hl.2.2.2.symm.trans hp.1
        rcases pair_eq_pair_iff.mp h4 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact ⟨κ, l, h1, h2, h3⟩
        · refine ⟨κ.symm, l.symm, fun u => ?_, fun u => ?_, h3.symm₂⟩
          · exact h1 _
          · exact h2 _
      · rw [hMn e hz]
        obtain ⟨u, v, -, hcap, hline⟩ := edge_line_of_forest hH.2 hl.1
        have h1 := hl.2.2.2
        rw [hcap] at h1
        have hline' : IsLineWithEnds (closure e) a c := by
          rcases pair_eq_pair_iff.mp h1 with ⟨h2, h3⟩ | ⟨h2, h3⟩
          · rw [← h2, ← h3]
            exact hline
          · rw [← h2, ← h3]
            exact hline.symm
        obtain ⟨p, hp⟩ := exists_path_of_line hline'
        exact ⟨p, p, hp, hp, Path.Homotopic.refl _⟩)
  have hYN : Y ⊆ N := fun q hq => (hYM q hq).1
  have hMY : ∀ e ∈ H.E, M e ⊆ closure e ∪ Y := fun e he q hq => by
    exact rerouted_edge_subset_original_union_chart (S := S) (z := z) (H := H) Y R G hGY M hMs hMn
      hRc' e he q hq
  exact assemble_forest_root_step (S := S) (S' := S') (L := L) (φ := φ) hJ (T := T) hTU (z := z)
    hzT hzb (l₀ := l₀) (H := H) (N := N) hV hφ hFiff hEfin Q₁ Q₂ hQ χ x₁ x₂ δ hχ  B x₀ hxl Y
    hYc W₀ hTW hW₀Y hzH hnon w R y hP   hrm hoffb hoffF hb0 hRY M hMs hMn P hPV hPU hPf hPh
    hPe hYN hMY


end GraphMinor.GM07
