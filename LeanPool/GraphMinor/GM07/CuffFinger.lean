/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffShift
public import LeanPool.GraphMinor.GM07.JoinDiscs
public import LeanPool.GraphMinor.Surface.AddCrosscap

/-!
# Three facts on discs in a surface with boundary

These are used in the choice of the `O`-arcs `A'` and `A` in the proof of Graph Minors VII, (6.1),
page 237: which disc holds which (`disc_subset_of_int_off_bd`), the outer side of a disc near a
point of its
boundary (`exists_side_nbhd`), and a finger from a disc to a point outside it (`exists_finger`).
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Function GraphMinor.Surface GraphMinor.GM11 Metric

universe u

variable {T : Type u} [TopologicalSpace T] [T2Space T]

omit [T2Space T] in
theorem inside_or_off {X B : Set T} (hX : IsPreconnected X) (hB : IsClosed B) (hf : Disjoint X
  (frontier B)) : X ⊆ interior B ∨ X ⊆ Bᶜ := by
  have hcov : X ⊆ interior B ∪ Bᶜ := fun x hx => by
    by_cases h1 : x ∈ B
    · refine .inl ?_
      by_contra h2
      exact disjoint_left.mp hf hx ⟨subset_closure h1, h2⟩
    · exact .inr h1
  have hd : Disjoint (interior B) Bᶜ := disjoint_left.mpr fun x hx hx' => hx' (interior_subset hx)
  exact hX.subset_or_subset isOpen_interior hB.isOpen_compl hd hcov

theorem frontier_disc_subset (hman : ∀ x : T, IsManifoldPoint x) {Δ : Set T}
  (hΔ : IsClosedDisc Δ) : frontier Δ ⊆ discBd Δ := by
  rintro x hx
  have h1 : x ∈ Δ := hΔ.isClosed.frontier_subset hx
  by_contra hb
  exact hx.2 (interior_maximal (discInt_subset Δ) (hΔ.isOpen_discInt hman) ⟨h1, hb⟩)

/-- If the inside of `Δ₁` misses the boundary of `Δ₂`, and the insides meet, then `Δ₁ ⊆ Δ₂`. -/
theorem disc_subset_of_int_off_bd (hman : ∀ x : T, IsManifoldPoint x) {Δ₁ Δ₂ : Set T}
  (h₁ : IsClosedDisc Δ₁) (h₂ : IsClosedDisc Δ₂) (hoff : Disjoint (discInt Δ₁) (discBd Δ₂)) (hm :
    (discInt Δ₁ ∩ Δ₂).Nonempty) : Δ₁ ⊆ Δ₂ := by
  have hf : Disjoint (discInt Δ₁) (frontier Δ₂) := hoff.mono_right (frontier_disc_subset hman h₂)
  rcases inside_or_off h₁.isPreconnected_discInt h₂.isClosed hf with h | h
  · have : closure (discInt Δ₁) ⊆ Δ₂ := closure_minimal (h.trans interior_subset) h₂.isClosed
    exact h₁.subset_closure_discInt.trans this
  · obtain ⟨x, hx, hx'⟩ := hm
    exact absurd hx' (h hx)

omit [T2Space T] in
/-- Near a point of the boundary of a disc, the part off the disc is connected and not empty. -/
theorem exists_side_nbhd (hman : ∀ x : T, IsManifoldPoint x) {B E : Set T} (hB : IsClosedDisc B)
  (hE : IsClosedDisc E) (hBE : B ⊆ E \ discBd E) {x : T} (hx : x ∈ discBd B) {W : Set T}
    (hW : IsOpen W) (hxW : x ∈ W) :
    ∃ N, IsOpen N ∧ x ∈ N ∧ N ⊆ W ∧ IsPreconnected (N \ B) ∧ (N \ B).Nonempty := by
  classical
  obtain ⟨p⟩ := hB.isOArc_discBd
  obtain ⟨c, c', hc, hc', hm, hm', hl, hr, hin, hs, hcp⟩ := exists_disc_collar hB hE hBE p
  let w₀ : Circle := p.symm ⟨x, hx⟩
  have hcw : c w₀ = x := by
    rw [hcp]
    simp [w₀]
  have hw1 : ‖(w₀ : ℂ)‖ = 1 := by simp
  have hw₀ : (w₀ : ℂ) ≠ 0 := by simp
  -- the part of the open ball that goes into `W`
  have hV : IsOpen (ball (0 : ℂ) 2 ∩ c ⁻¹' W) := (hc.mono
    ball_subset_closedBall).isOpen_inter_preimage isOpen_ball hW
  have hw₀V : (w₀ : ℂ) ∈ ball (0 : ℂ) 2 ∩ c ⁻¹' W := ⟨by simp, by rw [mem_preimage, hcw]; exact hxW⟩
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV _ hw₀V
  let δ : ℝ := min (ε / 4) (1 / 4)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδ1 : δ ≤ 1 / 4 := min_le_right _ _
  have hδε : δ ≤ ε / 4 := min_le_left _ _
  -- the box around `w₀`
  let un : ℂ → ℂ := fun z => z / w₀
  have hun : Continuous un := by fun_prop
  have hnun : ∀ z, ‖un z‖ = ‖z‖ := fun z => by simp [un]
  let Box : Set ℂ := {z | 0 < (un z).re ∧ |‖z‖ - 1| < δ ∧ |(un z).im| < δ}
  have hBoxO : IsOpen Box := by
    have e : Box = {z | 0 < (un z).re} ∩ ({z | |‖z‖ - 1| < δ} ∩ {z | |(un z).im| < δ}) := rfl
    rw [e]
    refine (isOpen_lt continuous_const (Complex.continuous_re.comp hun)).inter
      ((isOpen_lt ?_ continuous_const).inter (isOpen_lt ?_ continuous_const))
    · fun_prop
    · exact (Complex.continuous_im.comp hun).abs
  have hBoxε : ∀ z ∈ Box, z ∈ ball (w₀ : ℂ) ε := fun z hz => by
    obtain ⟨h1, h2, h3⟩ := hz
    obtain ⟨h2l, h2r⟩ := abs_lt.mp h2
    have h3' := abs_lt.mp h3
    set u := un z with hu
    have hn : ‖u‖ = ‖z‖ := hnun z
    have hsq : u.re * u.re + u.im * u.im = ‖u‖ * ‖u‖ := by
      rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
      ring
    have hre : u.re ≤ ‖u‖ := Complex.re_le_norm u
    have hlow : 1 - 2 * δ ≤ u.re := by
      rw [hn] at hsq
      by_contra hc
      push Not at hc
      nlinarith
    have hz' : z - w₀ = (u - 1) * w₀ := by
      rw [hu]
      simp only [un]
      field_simp
    have hb : ‖u - 1‖ ≤ |u.re - 1| + |u.im| := by
      have := Complex.norm_le_abs_re_add_abs_im (u - 1)
      simpa using this
    have hb1 : |u.re - 1| ≤ 2 * δ := abs_le.mpr ⟨by linarith, by linarith⟩
    rw [mem_ball, dist_eq_norm, hz', norm_mul, hw1, mul_one]
    linarith [h3'.1, h3'.2, abs_lt.mpr h3', abs_nonneg u.im]
  have hBoxb : Box ⊆ ball (0 : ℂ) 2 := fun z hz => (hεV (hBoxε z hz)).1
  have hBoxW : Box ⊆ c ⁻¹' W := fun z hz => (hεV (hBoxε z hz)).2
  have hw₀Box : (w₀ : ℂ) ∈ Box := by
    have : un (w₀ : ℂ) = 1 := div_self hw₀
    refine ⟨by simp [this], ?_, by simp [this, hδ]⟩
    rw [hw1]
    simpa using hδ
  have hb2 : ball (0 : ℂ) 2 ⊆ closedBall 0 2 := ball_subset_closedBall
  have hint : discInt E = c '' ball 0 2 := by
    ext y
    constructor
    · rintro ⟨hy, hyb⟩
      refine ⟨c' y, ?_, hr hy⟩
      have h1 : ‖c' y‖ ≤ 2 := by simpa using hm' hy
      refine mem_ball_zero_iff.mpr (lt_of_le_of_ne h1 fun h2 => hyb ?_)
      rw [← hs, ← hr hy]
      exact mem_image_of_mem c (by simpa using h2)
    · rintro ⟨z, hz, rfl⟩
      refine ⟨hm (hb2 hz), fun hb => ?_⟩
      rw [← hs] at hb
      obtain ⟨y, hy, he⟩ := hb
      rw [hl.injOn (sphere_subset_closedBall hy) (hb2 hz) he] at hy
      have h1 : ‖z‖ = 2 := by simpa using hy
      have h2 : ‖z‖ < 2 := by simpa using hz
      linarith
  let f : ℝ × ℝ → ℂ := fun q => (((Real.sqrt (q.1 * q.1 - q.2 * q.2) : ℝ) : ℂ) +
    (q.2 : ℂ) * Complex.I) * w₀
  have hfc : Continuous f := by
    have := Real.continuous_sqrt
    fun_prop
  let P : Set (ℝ × ℝ) := Ioo 1 (1 + δ) ×ˢ Ioo (-δ) δ
  have hPc : IsPreconnected P := ((convex_Ioo _ _).prod (convex_Ioo _ _)).isPreconnected
  have hunf : ∀ q : ℝ × ℝ, un (f q) = ((Real.sqrt (q.1 * q.1 - q.2 * q.2) : ℝ) : ℂ) +
    (q.2 : ℂ) * Complex.I := fun q => by
    simp only [un, f]
    field_simp
  have hnf : ∀ q : ℝ × ℝ, q ∈ P → ‖f q‖ = q.1 := fun q hq => by
    have h1 := hq.1.1
    have h2 := hq.2.1
    have h3 := hq.2.2
    have hpos : 0 ≤ q.1 * q.1 - q.2 * q.2 := by nlinarith
    rw [← hnun, hunf, Complex.norm_def, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
      Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.add_im, Complex.mul_im,
        zero_add]
    rw [Real.mul_self_sqrt hpos]
    rw [show q.1 * q.1 - q.2 * q.2 + q.2 * q.2 = q.1 * q.1 by ring,
      Real.sqrt_mul_self (by linarith)]
  have hfB : ∀ q ∈ P, f q ∈ Box := fun q hq => by
    have hn := hnf q hq
    have h1 := hq.1.1
    have h2 := hq.1.2
    have h3 := hq.2.1
    have h4 := hq.2.2
    have hpos : 0 < q.1 * q.1 - q.2 * q.2 := by nlinarith
    refine ⟨?_, ?_, ?_⟩
    · rw [hunf]
      simpa using hpos
    · rw [hn]
      exact abs_lt.mpr ⟨by linarith, by linarith⟩
    · rw [hunf]
      simpa using abs_lt.mpr ⟨h3, h4⟩
  have hdiff : c '' Box \ B = c '' (f '' P) := by
    ext y
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzB⟩
      have hzn : 1 < ‖z‖ := by
        by_contra hle
        exact hzB (hin ▸ mem_image_of_mem c (by simpa using not_lt.mp hle))
      obtain ⟨h1, h2, h3⟩ := hz
      have hsq : (un z).re * (un z).re + (un z).im * (un z).im = ‖z‖ * ‖z‖ := by
        rw [← hnun, ← Complex.normSq_apply, Complex.normSq_eq_norm_sq]
        ring
      refine ⟨z, ⟨(‖z‖, (un z).im), ⟨⟨hzn, ?_⟩, abs_lt.mp h3⟩, ?_⟩, rfl⟩
      · have := (abs_lt.mp h2).2
        linarith
      · have h4 : Real.sqrt (‖z‖ * ‖z‖ - (un z).im * (un z).im) = (un z).re := by
          rw [show ‖z‖ * ‖z‖ - (un z).im * (un z).im = (un z).re * (un z).re by linarith]
          exact Real.sqrt_mul_self h1.le
        simp only [f]
        rw [h4, Complex.re_add_im]
        simp only [un]
        field_simp
    · rintro ⟨_, ⟨q, hq, rfl⟩, rfl⟩
      have hn := hnf q hq
      have h1 := hq.1.1
      have h2 := hq.1.2
      have h3 := hq.2.1
      have h4 := hq.2.2
      have hpos : 0 < q.1 * q.1 - q.2 * q.2 := by nlinarith
      have hBq : f q ∈ Box := hfB q hq
      refine ⟨⟨f q, hBq, rfl⟩, fun hin' => ?_⟩
      rw [← hin] at hin'
      obtain ⟨y, hy, he⟩ := hin'
      have hyb : y ∈ closedBall (0 : ℂ) 2 := by
        have : ‖y‖ ≤ 1 := by simpa using hy
        simp only [mem_closedBall_zero_iff]
        linarith
      rw [hl.injOn hyb (hb2 (hBoxb hBq)) he] at hy
      have : ‖f q‖ ≤ 1 := by simpa using hy
      linarith
  refine ⟨c '' Box, ?_, ⟨w₀, hw₀Box, hcw⟩, ?_, ?_, ?_⟩
  · have : c '' Box = discInt E ∩ c' ⁻¹' Box := by
      ext y
      constructor
      · rintro ⟨z, hz, rfl⟩
        refine ⟨hint ▸ mem_image_of_mem c (hBoxb hz), ?_⟩
        rw [mem_preimage, hl (hb2 (hBoxb hz))]
        exact hz
      · rintro ⟨hy, hyB⟩
        exact ⟨c' y, hyB, hr hy.1⟩
    rw [this]
    have h1 := hc'.mono (discInt_subset E)
    exact h1.isOpen_inter_preimage (hE.isOpen_discInt hman) hBoxO
  · rintro _ ⟨z, hz, rfl⟩
    exact hBoxW hz
  · rw [hdiff]
    refine (hPc.image _ hfc.continuousOn).image _ (hc.mono ?_)
    rintro _ ⟨q, hq, rfl⟩
    exact hb2 (hBoxb (hfB q hq))
  · rw [hdiff]
    refine ⟨_, _, ⟨(1 + δ / 2, 0), ⟨⟨by linarith, by linarith⟩, ⟨by linarith, hδ⟩⟩, rfl⟩, rfl⟩

/-- **A finger from a disc to a point outside it.** We add to `Δ` a thin disc around the line `L`.
The new boundary meets the closed set `Z` only where the old boundary did, and at `b`. The new disc
meets `Z` only in `Δ` and at `b`. -/
theorem exists_finger {T : Type} [TopologicalSpace T] (hT : IsSurface T) {Δ L Z : Set T} {p b : T}
  (hΔ : IsClosedDisc Δ) (hL : IsLineWithEnds L p b) (hpb : p ≠ b) (hp : p ∈ discBd Δ)
    (hLΔ : L ∩ Δ ⊆ {p}) (hb : b ∉ Δ)
    (hZ : IsClosed Z) (hbZ : b ∈ Z) (hLZ : L ∩ Z ⊆ {b}) (hoff : Disjoint (Δ ∪ L) (bd T)) :
    ∃ Δ₁, IsClosedDisc Δ₁ ∧ Δ ⊆ Δ₁ ∧ b ∈ discBd Δ₁ ∧ discBd Δ ∩ Z ⊆ discBd Δ₁ ∧ discBd Δ₁ ∩ Z ⊆
      (discBd Δ ∩ Z) ∪ {b} ∧ Disjoint Δ₁ (bd T) ∧
      Δ₁ ∩ Z ⊆ Δ ∪ {b} := by
  classical
  have : CompactSpace T := hT.1
  have : T2Space T := hT.2.1
  obtain ⟨R, tR, i, K, hR, hi, hK, hcov, hcap, -⟩ := exists_capAll T hT
  have : T2Space R := hR.2.1
  have hii := hi.injective
  have hpΔ : p ∈ Δ := Surface.discBd_subset _ hp
  have hpL : p ∈ L := hL.left_mem
  have hbL : b ∈ L := hL.right_mem
  have hpZ : p ∉ Z := fun h => hpb (hLZ ⟨hpL, h⟩)
  have hoffK : ∀ x ∈ Δ ∪ L, i x ∉ K := fun x hx hK' => by
    have h1 : i x ∈ range i ∩ K := ⟨mem_range_self x, hK'⟩
    rw [hcap] at h1
    obtain ⟨y, hy, he⟩ := h1
    rw [hii he] at hy
    exact disjoint_left.mp hoff hx hy
  have hline := image_line hi.isEmbedding hL
  let Y : Set R := i '' (Δ ∪ Z) ∪ K
  have hYc : IsClosed Y := (hi.isClosedMap _ (hΔ.isClosed.union hZ)).union hK
  have hLY : i '' L ∩ Y ⊆ {i p, i b} := by
    rintro _ ⟨⟨x, hx, rfl⟩, hxY⟩
    rcases hxY with ⟨y, hy, he⟩ | hxK
    · rw [hii he] at hy
      rcases hy with hy | hy
      · exact .inl (by rw [show x = p from hLΔ ⟨hx, hy⟩])
      · exact .inr (by rw [show x = b from hLZ ⟨hx, hy⟩]; rfl)
    · exact absurd hxK (hoffK x (.inr hx))
  obtain ⟨Ln, -, -, hLn, hLnL, hLnY, hpLn, hbLn, -⟩ := exists_edge_lens hR hline
    (hii.ne hpb) hYc hLY
  obtain ⟨hA, hAb⟩ := isClosedDisc_image hΔ hi.continuous.continuousOn hii.injOn
  have hsL : i p ∈ Ln ∧ i b ∈ Ln := ⟨Surface.discBd_subset _ hpLn, Surface.discBd_subset _ hbLn⟩
  have hLnY' : ∀ x ∈ Ln, x ∈ Y → x = i p ∨ x = i b := fun x hx hy => hLnY ⟨hx, hy⟩
  have hAB : i '' Δ ∩ Ln = {i p} := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hyL⟩
      rcases hLnY' _ hyL (.inl ⟨y, .inl hy, rfl⟩) with h | h
      · exact h
      · rw [hii h] at hy
        exact absurd hy hb
    · rintro rfl
      exact ⟨mem_image_of_mem i hpΔ, hsL.1⟩
  let W : Set R := (i '' Z ∪ K)ᶜ
  have hW : IsOpen W := ((hi.isClosedMap _ hZ).union hK).isOpen_compl
  have hpW : i p ∈ W := by
    rintro (⟨y, hy, he⟩ | hK')
    · rw [hii he] at hy
      exact hpZ hy
    · exact hoffK p (.inl hpΔ) hK'
  obtain ⟨D, hD, h1, h2, -, h4, h5⟩ := exists_join hR hA hLn hAB
    (by rw [hAb]; exact mem_image_of_mem i hp) hpLn hW hpW
  have hbW : ∀ x ∈ Z, i x ∉ W := fun x hx h => h (.inl (mem_image_of_mem i hx))
  have hLnr : Ln ⊆ range i := fun x hx => by
    rcases hcov.ge (mem_univ x) with h | h
    · exact h
    · rcases hLnY' x hx (.inr h) with rfl | rfl <;> exact mem_range_self _
  have hDr : D ⊆ range i := fun x hx => by
    rcases h2 hx with (⟨y, -, rfl⟩ | h) | h
    · exact mem_range_self y
    · exact hLnr h
    · rcases hcov.ge (mem_univ x) with h' | h'
      · exact h'
      · exact absurd (.inr h') h
  have : Nonempty T := ⟨p⟩
  obtain ⟨hD₁, hbd⟩ := isClosedDisc_preimage hi hD hDr
  refine ⟨i ⁻¹' D, hD₁, fun x hx => h1 (.inl (mem_image_of_mem i hx)), ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbd]
    exact h4 ⟨.inr hbLn, hbW b hbZ⟩
  · rintro x ⟨hx, hxZ⟩
    rw [hbd]
    refine h4 ⟨.inl ?_, hbW x hxZ⟩
    rw [hAb]
    exact mem_image_of_mem i hx
  · rintro x ⟨hx, hxZ⟩
    rw [hbd] at hx
    rcases h5 hx with (h | h) | h
    · rw [hAb] at h
      obtain ⟨y, hy, he⟩ := h
      rw [hii he] at hy
      exact .inl ⟨hy, hxZ⟩
    · rcases hLnY' _ (Surface.discBd_subset _ h) (.inl ⟨x, .inr hxZ, rfl⟩) with h' | h'
      · rw [hii h'] at hxZ
        exact absurd hxZ hpZ
      · exact .inr (hii h')
    · exact absurd h (hbW x hxZ)
  · rw [disjoint_left]
    intro x hx hxb
    have hxK : i x ∈ K := by
      have h6 : i x ∈ i '' bd T := mem_image_of_mem i hxb
      rw [← hcap] at h6
      exact h6.2
    rcases h2 hx with (⟨y, hy, he⟩ | h) | h
    · rw [hii he] at hy
      exact hoffK x (.inl hy) hxK
    · rcases hLnY' _ h (.inr hxK) with h' | h'
      · rw [hii h'] at hxK
        exact hoffK p (.inl hpΔ) hxK
      · rw [hii h'] at hxK
        exact hoffK b (.inr hbL) hxK
    · exact h (.inr hxK)
  · rintro x ⟨hx, hxZ⟩
    rcases h2 hx with (⟨y, hy, he⟩ | h) | h
    · rw [hii he] at hy
      exact .inl hy
    · rcases hLnY' _ h (.inl ⟨x, .inr hxZ, rfl⟩) with h' | h'
      · exact .inl (hii h' ▸ hpΔ)
      · exact .inr (hii h')
    · exact absurd h (hbW x hxZ)

/-- The same for a surface in any universe that is homeomorphic to one in the lowest universe, such
as a surface model. -/
theorem exists_finger_of_homeo {T : Type u} [TopologicalSpace T] {T₀ : Type} [TopologicalSpace T₀]
  (hT : IsSurface T) (e : T ≃ₜ T₀) {Δ L Z : Set T} {p b : T} (hΔ : IsClosedDisc Δ)
    (hL : IsLineWithEnds L p b) (hpb : p ≠ b)
    (hp : p ∈ discBd Δ) (hLΔ : L ∩ Δ ⊆ {p}) (hb : b ∉ Δ) (hZ : IsClosed Z) (hbZ : b ∈ Z)
      (hLZ : L ∩ Z ⊆ {b}) (hoff : Disjoint (Δ ∪ L) (bd T)) :
    ∃ Δ₁, IsClosedDisc Δ₁ ∧ Δ ⊆ Δ₁ ∧ b ∈ discBd Δ₁ ∧ discBd Δ ∩ Z ⊆ discBd Δ₁ ∧ discBd Δ₁ ∩ Z ⊆
      (discBd Δ ∩ Z) ∪ {b} ∧ Disjoint Δ₁ (bd T) := by
  classical
  have : T2Space T := hT.2.1
  have hT₀ : IsSurface T₀ := isSurface_of_homeo e hT
  have : T2Space T₀ := hT₀.2.1
  have hbdT : ∀ x, e x ∈ bd T₀ ↔ x ∈ bd T := fun x => not_congr (isInteriorPoint_homeomorph_iff e x)
  obtain ⟨hΔ₀, hb₀⟩ := isClosedDisc_image hΔ e.continuous.continuousOn e.injective.injOn
  have hmem : ∀ {x : T} {A : Set T}, e x ∈ e '' A ↔ x ∈ A := fun {x A} => e.injective.mem_set_image
  have hline : IsLineWithEnds (e '' L) (e p) (e b) := image_line e.isEmbedding hL
  obtain ⟨Δ₁, h1, h2, h3, h4, h5, h6, -⟩ := exists_finger hT₀ (Δ := e '' Δ) (L := e '' L) (Z
    := e '' Z)
    hΔ₀ hline (e.injective.ne hpb) (by rw [hb₀]; exact mem_image_of_mem e hp)
    (by
      rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
      have := hLΔ ⟨hx, hmem.mp hy⟩
      rw [show x = p from this]
      rfl) (fun h => hb (hmem.mp h)) (e.isClosedMap _ hZ) (mem_image_of_mem e hbZ)
    (by
      rintro _ ⟨⟨x, hx, rfl⟩, hy⟩
      have := hLZ ⟨hx, hmem.mp hy⟩
      rw [show x = b from this]
      rfl)
    (by
      rw [disjoint_left]
      rintro _ (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩) hy
      · exact disjoint_left.mp hoff (.inl hx) ((hbdT x).mp hy)
      · exact disjoint_left.mp hoff (.inr hx) ((hbdT x).mp hy))
  have hsym : Function.LeftInverse e.symm e := e.left_inv
  obtain ⟨hD, hDb⟩ := isClosedDisc_image h1 e.symm.continuous.continuousOn e.symm.injective.injOn
  have hee : ∀ {A : Set T₀} {x : T}, x ∈ e.symm '' A ↔ e x ∈ A := fun {A x} => by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro h
      exact ⟨e x, h, by simp⟩
  refine ⟨e.symm '' Δ₁, hD, fun x hx => hee.mpr (h2 (mem_image_of_mem e hx)), ?_, ?_, ?_, ?_⟩
  · rw [hDb]
    exact hee.mpr h3
  · rintro x ⟨hx, hxZ⟩
    rw [hDb]
    refine hee.mpr (h4 ⟨?_, mem_image_of_mem e hxZ⟩)
    rw [hb₀]
    exact mem_image_of_mem e hx
  · rintro x ⟨hx, hxZ⟩
    rw [hDb] at hx
    rcases h5 ⟨hee.mp hx, mem_image_of_mem e hxZ⟩ with ⟨h7, -⟩ | h7
    · rw [hb₀] at h7
      exact .inl ⟨hmem.mp h7, hxZ⟩
    · exact .inr (e.injective h7)
  · rw [disjoint_left]
    intro x hx hxb
    exact disjoint_left.mp h6 (hee.mp hx) ((hbdT x).mpr hxb)

end GraphMinor.GM07
