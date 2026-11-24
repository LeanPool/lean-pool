/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.CuffSlide

/-!
# A half rectangle around an arc of the boundary

For (4.4) of Graph Minors VII we need a chart of `Σ` around an arc of `bd(Σ)`: a rectangle with the
arc on its bottom side (`exists_bd_chart`). Cap the cuffs to get a closed surface. There a strip
around the arc is given by `exists_stripChart_of_arc`, and one half of the strip lies in `Σ`.
-/

@[expose] public section

namespace GraphMinor.GM07

open Set Topology Metric Complex GraphMinor.Surface GraphMinor.GM11

variable {S : Type} [TopologicalSpace S]

/-- A chart `χ` from the rectangle `[x₁, x₂] × [0, δ]` to `Σ`, with the bottom side in `bd(Σ)`. The
part of the rectangle without the top and the two lateral sides is open in `Σ`. -/
structure IsBdChart (χ : ℂ → S) (x₁ x₂ δ : ℝ) : Prop where
  hx : x₁ < x₂
  hδ : 0 < δ
  cont : ContinuousOn χ (Icc x₁ x₂ ×ℂ Icc 0 δ)
  inj : InjOn χ (Icc x₁ x₂ ×ℂ Icc 0 δ)
  isOpen : IsOpen (χ '' (Ioo x₁ x₂ ×ℂ Ico 0 δ))
  bd : ∀ w ∈ Icc x₁ x₂ ×ℂ Icc 0 δ, χ w ∈ bd S ↔ w.im = 0

private theorem convex_portion_cannot_cross_cuff
    {S : Type}
    [TopologicalSpace S]
    (T : Type)
    [TopologicalSpace T]
    (j : S → T)
    (hj : IsClosedEmbedding j)
    (O : Set ℂ)
    (K : ℂ → T)
    (hK : StripChart O K)
    (R : Set ℂ)
    (hRO : R ⊆ O)
    (hfr : frontier (range j) = j '' bd S)
    (hbdaxis : ∀ w ∈ R, K w ∈ j '' bd S → w.im = 0) :
    ∀ {P : ℝ → Prop}, Convex ℝ {w | w ∈ R ∧ P w.im} → (∀ (r : ℝ), P r → r ≠ 0) → ∀ w ∈ R, ∀ w' ∈
      R, P w.im → P w'.im → K w ∈ range j → K w' ∈ range j := by
  intro P hconv hP w hw w' hw' h1 h2 h3
  by_contra hn
  have hset : IsPreconnected (K '' {w : ℂ | w ∈ R ∧ P w.im}) :=
    hconv.isPreconnected.image K (hK.hc.mono fun z hz => hRO hz.1)
  have hcov : K '' {w : ℂ | w ∈ R ∧ P w.im} ⊆ range j ∪ closure (range j)ᶜ := fun z _ => by
    by_cases hzr : z ∈ range j
    · exact .inl hzr
    · exact .inr (subset_closure hzr)
  obtain ⟨z, ⟨w₀, hw₀, rfl⟩, hz⟩ := isPreconnected_closed_iff.mp hset _ _ hj.isClosed_range
    isClosed_closure hcov
    ⟨K w, ⟨w, ⟨hw, h1⟩, rfl⟩, h3⟩ ⟨K w', ⟨w', ⟨hw', h2⟩, rfl⟩, subset_closure hn⟩
  have hz' : K w₀ ∈ frontier (range j) := by
    rw [frontier_eq_closure_inter_closure, hj.isClosed_range.closure_eq]
    exact hz
  rw [hfr] at hz'
  exact hP _ hw₀.2 (hbdaxis w₀ hw₀.1 hz')

private theorem boundary_chart_has_consistent_inward_side
    {S : Type}
    [TopologicalSpace S]
    (hS : IsSurface S)
    {g : ℝ → S}
    {a : ℝ}
    {b : ℝ}
    {c : ℝ}
    {d : ℝ}
    (hac : a ≤ c) (hdb : d ≤ b)
    (hbd : ∀ u ∈ Icc a b, g u ∈ bd S)
    (T : Type)
    [TopologicalSpace T]
    (j : S → T)
    (hj : IsClosedEmbedding j)
    (par : ↑unitInterval → ℝ)
    (K : ℂ → T)
    (R : Set ℂ)
    (haxis : ∀ w ∈ R, w.im = 0 → ∃ u, par u ∈ Icc c d ∧ K w = j (g (par u)))
    (hup : ∀ w ∈ R, ∀ w' ∈ R, 0 < w.im → 0 < w'.im → K w ∈ range j → K w' ∈ range j)
    (hlo : ∀ w ∈ R, ∀ w' ∈ R, w.im < 0 → w'.im < 0 → K w ∈ range j → K w' ∈ range j)
    (Wo : Set ℂ)
    (hWoR : Wo ⊆ R)
    (hKW : IsOpen (K '' Wo))
    (m : ℝ)
    (hmW : ↑m ∈ Wo)
    (um : ↑unitInterval)
    (hKm : K ↑m = j (g (par um)))
    (hfm : K ↑m ∈ frontier (range j)) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ (∀ w ∈ R, 0 < s * w.im → K w ∈ range j) ∧
      ∀ w ∈ R, s * w.im < 0 → K w ∉ range j := by
  obtain ⟨w₁, hw₁, hw₁n⟩ : ∃ w₁ ∈ Wo, K w₁ ∉ range j := by
    have h2 : K (m : ℂ) ∈ closure (range j)ᶜ := by
      rw [frontier_eq_closure_inter_closure] at hfm
      exact hfm.2
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp h2 _ hKW (mem_image_of_mem K hmW)
    obtain ⟨w, hw, rfl⟩ := hz1
    exact ⟨w, hw, hz2⟩
  obtain ⟨w₂, hw₂, hw₂r, hw₂b⟩ : ∃ w₂ ∈ Wo, K w₂ ∈ range j ∧ w₂.im ≠ 0 := by
    have h2 := mem_closure_compl_bd (hS.2.2 (g (par um)))
    have h3 : IsOpen (j ⁻¹' (K '' Wo)) := hKW.preimage hj.continuous
    have hoc : g (par um) ∈ j ⁻¹' (K '' Wo) := by
      rw [mem_preimage, ← hKm]
      exact mem_image_of_mem K hmW
    obtain ⟨z, hz1, hz2⟩ := mem_closure_iff.mp h2 _ h3 hoc
    obtain ⟨w, hw, he⟩ := hz1
    refine ⟨w, hw, he ▸ ⟨z, rfl⟩, fun h0 => ?_⟩
    obtain ⟨u, hp, he'⟩ := haxis w (hWoR hw) h0
    rw [he] at he'
    rw [hj.injective he'] at hz2
    exact hz2 (hbd _ ⟨by linarith [hp.1], by linarith [hp.2]⟩)
  have hw₁b : w₁.im ≠ 0 := fun h0 => by
    obtain ⟨u, -, he⟩ := haxis w₁ (hWoR hw₁) h0
    exact hw₁n (he ▸ ⟨_, rfl⟩)
  rcases lt_or_gt_of_ne hw₂b with hneg | hpos
  · refine ⟨-1, .inr rfl, fun w hw h => hlo _ (hWoR hw₂) _ hw hneg (by linarith) hw₂r,
      fun w hw h h' => hw₁n ?_⟩
    have hw₁pos : 0 < w₁.im := by
      rcases lt_or_gt_of_ne hw₁b with h1 | h1
      · exact absurd (hlo _ (hWoR hw₂) _ (hWoR hw₁) hneg h1 hw₂r) hw₁n
      · exact h1
    exact hup _ hw _ (hWoR hw₁) (by linarith) hw₁pos h'
  · refine ⟨1, .inl rfl, fun w hw h => hup _ (hWoR hw₂) _ hw hpos (by linarith) hw₂r,
      fun w hw h h' => hw₁n ?_⟩
    have hw₁neg : w₁.im < 0 := by
      rcases lt_or_gt_of_ne hw₁b with h1 | h1
      · exact h1
      · exact absurd (hup _ (hWoR hw₂) _ (hWoR hw₁) hpos h1 hw₂r) hw₁n
    exact hlo _ hw _ (hWoR hw₁) (by linarith) hw₁neg h'

private theorem inner_half_strip_has_open_image
    {S : Type}
    [TopologicalSpace S]
    (T : Type)
    [TopologicalSpace T]
    (j : S → T)
    (hj : IsClosedEmbedding j)
    (K : ℂ → T)
    (x₁ : ℝ)
    (x₂ : ℝ)
    (δ : ℝ) (hδ : 0 < δ)
    (hWoR : (Ioo x₁ x₂ ×ℂ Ioo (-δ) δ) ⊆ (Icc x₁ x₂ ×ℂ Icc (-δ) δ))
    (hKW : IsOpen (K '' (Ioo x₁ x₂ ×ℂ Ioo (-δ) δ)))
    (s : ℝ)
    (hs2 : ∀ w ∈ (Icc x₁ x₂ ×ℂ Icc (-δ) δ), s * w.im < 0 → K w ∉ range j)
    (hs0 : s * s = 1)
    (σ : ℂ → ℂ)
    (hσre : ∀ (w : ℂ), (σ w).re = w.re)
    (hσim : ∀ (w : ℂ), (σ w).im = s * w.im)
    (habss : ∀ (y : ℝ), |s * y| = |y|)
    (χ : ℂ → S)
    (hχ : ∀ w ∈ (Icc x₁ x₂ ×ℂ Icc 0 δ), j (χ w) = K (σ w)) :
    IsOpen (χ '' (Ioo x₁ x₂ ×ℂ Ico 0 δ)) := by
  let R := Icc x₁ x₂ ×ℂ Icc (-δ) δ
  let Wo := Ioo x₁ x₂ ×ℂ Ioo (-δ) δ
  let Q := Icc x₁ x₂ ×ℂ Icc 0 δ
  have hBQ : Ioo x₁ x₂ ×ℂ Ico 0 δ ⊆ Q := fun w hw => ⟨Ioo_subset_Icc_self hw.1,
    Ico_subset_Icc_self hw.2⟩
  have he : χ '' (Ioo x₁ x₂ ×ℂ Ico 0 δ) = j ⁻¹' (K '' Wo) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [mem_preimage, hχ w (hBQ hw)]
      refine mem_image_of_mem K ⟨?_, ?_⟩
      · rw [mem_preimage, hσre]
        exact hw.1
      · rw [mem_preimage, hσim, mem_Ioo, ← abs_lt, habss, abs_lt]
        exact ⟨by linarith [hw.2.1], hw.2.2⟩
    · rintro ⟨w, hw, he⟩
      have hnonneg : 0 ≤ s * w.im := by
        by_contra hn
        exact hs2 w (hWoR hw) (not_le.mp hn) (he ▸ ⟨z, rfl⟩)
      let w' : ℂ := (w.re : ℂ) + ((s * w.im : ℝ) : ℂ) * I
      have hw're : w'.re = w.re := by simp [w']
      have hw'im : w'.im = s * w.im := by simp [w']
      have hσw' : σ w' = w := by
        apply Complex.ext
        · rw [hσre, hw're]
        · rw [hσim, hw'im, ← mul_assoc, hs0, one_mul]
      have hlt : s * w.im < δ := by
        have := abs_lt.mpr hw.2
        rw [← habss] at this
        exact (abs_lt.mp this).2
      have hw'B : w' ∈ Ioo x₁ x₂ ×ℂ Ico 0 δ := by
        constructor
        · rw [mem_preimage, hw're]
          exact hw.1
        · rw [mem_preimage, hw'im]
          exact ⟨hnonneg, hlt⟩
      refine ⟨w', hw'B, hj.injective ?_⟩
      rw [hχ w' (hBQ hw'B), hσw', he]
  rw [he]
  exact hKW.preimage hj.continuous

/-- **A half rectangle around an arc of `bd(Σ)`.** Let `g` be an arc of `bd(Σ)` on `[a, b]`, and let
`Z` be a closed set that misses the part of `g` on `[c, d]`, with `a < c < d < b`. Then there is a
chart that misses `Z`, with the part of `g` between `c` and `d` inside its bottom side. -/
theorem exists_bd_chart (hS : IsSurface S) {g : ℝ → S} {a b c d : ℝ} (hg : Continuous g)
  (hac : a < c) (hcd : c < d) (hdb : d < b)
    (hi : InjOn g (Icc a b)) (hbd : ∀ u ∈ Icc a b, g u ∈ bd S) (hrest : IsClosed
      (bd S \ g '' Ioo a b)) {Z : Set S} (hZ : IsClosed Z)
    (hZg : ∀ u ∈ Icc c d, g u ∉ Z) : ∃ (χ : ℂ → S) (x₁ x₂ δ : ℝ), IsBdChart χ x₁ x₂ δ ∧
      (∀ w ∈ Icc x₁ x₂ ×ℂ Icc 0 δ, χ w ∉ Z) ∧
      ∀ u ∈ Ioo c d, ∃ x ∈ Ioo x₁ x₂, χ (x : ℂ) = g u := by
  classical
  have ht2S : T2Space S := hS.2.1
  have hcS : CompactSpace S := hS.1
  obtain ⟨T, tT, j, K', hT, hj, hK', hu, hi', -⟩ := exists_capAll S hS
  have ht2 : T2Space T := hT.2.1
  have hcT : CompactSpace T := hT.1
  have hab : a < b := by linarith
  have hab' : 0 < b - a := by linarith
  let par : unitInterval → ℝ := fun u => a + u.1 * (b - a)
  have hpar : ∀ u, par u ∈ Icc a b := fun u => by
    have h0 := u.2.1
    have h1 := u.2.2
    exact ⟨by simp only [par]; nlinarith, by simp only [par]; nlinarith⟩
  have hparc : Continuous par := by simp only [par]; fun_prop
  have hparm : StrictMono par := fun s t h => by
    have h' : s.1 < t.1 := h
    simp only [par]
    nlinarith
  have hpars : ∀ r ∈ Icc a b, ∃ u, par u = r := fun r hr => by
    refine ⟨⟨(r - a) / (b - a), div_nonneg (by linarith [hr.1]) hab'.le,
      (div_le_one hab').mpr (by linarith [hr.2])⟩, ?_⟩
    simp only [par]
    field_simp
    ring
  let A : unitInterval → T := fun u => j (g (par u))
  have hA : IsArcMap A := ⟨hj.continuous.comp (hg.comp hparc), fun s t h => hparm.injective (hi
    (hpar s) (hpar t) (hj.injective h))⟩
  obtain ⟨O, K, θ, hK, hθc, hθm, hθ⟩ := exists_stripChart_of_arc hT hA
  obtain ⟨uc, huc⟩ := hpars c ⟨hac.le, by linarith⟩
  obtain ⟨ud, hud⟩ := hpars d ⟨by linarith, hdb.le⟩
  have hucd : uc < ud := hparm.lt_iff_lt.mp (by rw [huc, hud]; exact hcd)
  set x₁ := θ uc with hx₁
  set x₂ := θ ud with hx₂
  have hx : x₁ < x₂ := hθm hucd
  have hreal : ∀ r ∈ Icc x₁ x₂, ∃ u : unitInterval, par u ∈ Icc c d ∧ θ u = r := fun r hr => by
    obtain ⟨u, hu', he⟩ := intermediate_value_Icc hucd.le hθc.continuousOn hr
    refine ⟨u, ⟨?_, ?_⟩, he⟩
    · rw [← huc]
      exact hparm.monotone hu'.1
    · rw [← hud]
      exact hparm.monotone hu'.2
  let Z₂ : Set T := j '' Z ∪ j '' (bd S \ g '' Ioo a b)
  have hZ₂ : IsClosed Z₂ := (hj.isClosedMap _ hZ).union (hj.isClosedMap _ hrest)
  have hAZ : ∀ u : unitInterval, par u ∈ Icc c d → A u ∉ Z₂ := fun u hp => by
    rintro (⟨z, hz, e⟩ | ⟨z, hz, e⟩)
    · rw [hj.injective e] at hz
      exact hZg _ hp hz
    · rw [hj.injective e] at hz
      exact hz.2 ⟨_, ⟨by linarith [hp.1], by linarith [hp.2]⟩, rfl⟩
  let Ω : Set ℂ := O ∩ K ⁻¹' Z₂ᶜ
  have hΩ : IsOpen Ω := hK.hc.isOpen_inter_preimage hK.isOpen hZ₂.isOpen_compl
  have hcpt : IsCompact (((↑) : ℝ → ℂ) '' Icc x₁ x₂) := isCompact_Icc.image continuous_ofReal
  have hsubΩ : ((↑) : ℝ → ℂ) '' Icc x₁ x₂ ⊆ Ω := by
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨u, hp, rfl⟩ := hreal r hr
    refine ⟨(hθ u).1, ?_⟩
    simp only [mem_preimage, mem_compl_iff]
    rw [(hθ u).2]
    exact hAZ u hp
  obtain ⟨δ₀, hδ₀, hth⟩ := hcpt.exists_thickening_subset_open hΩ hsubΩ
  let δ := δ₀ / 2
  have hδ : 0 < δ := by simp only [δ]; linarith
  let R : Set ℂ := Icc x₁ x₂ ×ℂ Icc (-δ) δ
  have hRΩ : R ⊆ Ω := fun z hz => by
    refine hth (mem_thickening_iff.mpr ⟨(z.re : ℂ), ⟨z.re, hz.1, rfl⟩, ?_⟩)
    have h1 : z - (z.re : ℂ) = (z.im : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [dist_eq_norm, h1, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have := abs_le.mpr hz.2
    simp only [δ] at this
    linarith
  have hRO : R ⊆ O := fun z hz => (hRΩ hz).1
  have hfr : frontier (range j) = j '' bd S := cap_frontier hT hj hK' hu hi'
  have hbdaxis : ∀ w ∈ R, K w ∈ j '' bd S → w.im = 0 := fun w hw h => by
    obtain ⟨z, hz, e'⟩ := h
    have h2 : z ∈ g '' Ioo a b := by
      by_contra hn
      exact (hRΩ hw).2 (.inr ⟨z, ⟨hz, hn⟩, e'⟩)
    obtain ⟨r, hr, rfl⟩ := h2
    obtain ⟨u, hu'⟩ := hpars r ⟨hr.1.le, hr.2.le⟩
    have h3 : K w = K (θ u) := by
      rw [(hθ u).2, ← e']
      simp only [A, hu']
    have h4 := hK.hi (hRO hw) (hθ u).1 h3
    rw [h4]
    simp
  have haxis : ∀ w ∈ R, w.im = 0 → ∃ u : unitInterval, par u ∈ Icc c d ∧ K w = j (g (par u))
    := fun w hw h0 => by
    obtain ⟨u, hp, hr⟩ := hreal _ hw.1
    refine ⟨u, hp, ?_⟩
    have h2 : w = (θ u : ℂ) := by
      apply Complex.ext
      · simp [hr]
      · simp [h0]
    rw [h2, (hθ u).2]
  have hside : ∀ {P : ℝ → Prop}, Convex ℝ {w : ℂ | w ∈ R ∧ P w.im} → (∀ r, P r → r ≠ 0)
    → ∀ w ∈ R, ∀ w' ∈ R, P w.im → P w'.im →
      K w ∈ range j → K w' ∈ range j := by
    exact convex_portion_cannot_cross_cuff (S := S) T j hj O K hK R hRO hfr hbdaxis
  have hRconv : Convex ℝ R := ((convex_Icc x₁ x₂).linear_preimage Complex.reLm).inter ((convex_Icc
    (-δ) δ).linear_preimage Complex.imLm)
  have hup : ∀ w ∈ R, ∀ w' ∈ R, 0 < w.im → 0 < w'.im → K w ∈ range j → K w' ∈ range j :=
    hside (P := fun r => 0 < r) (hRconv.inter (convex_halfSpace_im_gt 0)) fun r hr => hr.ne'
  have hlo : ∀ w ∈ R, ∀ w' ∈ R, w.im < 0 → w'.im < 0 → K w ∈ range j → K w' ∈ range j :=
    hside (P := fun r => r < 0) (hRconv.inter (convex_halfSpace_im_lt 0)) fun r hr => hr.ne
  -- The two sides of the bottom.
  let Wo : Set ℂ := Ioo x₁ x₂ ×ℂ Ioo (-δ) δ
  have hWoo : IsOpen Wo := isOpen_Ioo.reProdIm isOpen_Ioo
  have hWoR : Wo ⊆ R := fun w hw => ⟨Ioo_subset_Icc_self hw.1, Ioo_subset_Icc_self hw.2⟩
  have hKW : IsOpen (K '' Wo) := hK.ho _ hWoo fun z hz => hRO (hWoR hz)
  let m := (x₁ + x₂) / 2
  have hm : m ∈ Icc x₁ x₂ := ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
  have hmW : (m : ℂ) ∈ Wo := by
    refine ⟨?_, ?_⟩
    · rw [mem_preimage, ofReal_re]
      exact ⟨by simp only [m]; linarith, by simp only [m]; linarith⟩
    · rw [mem_preimage, ofReal_im]
      exact ⟨by linarith, hδ⟩
  obtain ⟨um, hpm, hKm⟩ := haxis (m : ℂ) (hWoR hmW) (by simp)
  have hgm : g (par um) ∈ bd S := hbd _ ⟨by linarith [hpm.1], by linarith [hpm.2]⟩
  have hfm : K (m : ℂ) ∈ frontier (range j) := by
    rw [hfr, hKm]
    exact mem_image_of_mem j hgm
  have hOrientation : ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ (∀ w ∈ R, 0 < s * w.im → K w ∈ range j) ∧
    (∀ w ∈ R, s * w.im < 0 → K w ∉ range j) := by
    exact boundary_chart_has_consistent_inward_side (S := S) hS (g := g) (a := a) (b := b) (c :=
      c) (d := d) hac.le hdb.le hbd T j hj par K R haxis hup hlo Wo hWoR hKW m hmW um hKm hfm
  obtain ⟨s, hs, hs1, hs2⟩ := hOrientation
  have hs0 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  let σ : ℂ → ℂ := fun w => (w.re : ℂ) + ((s * w.im : ℝ) : ℂ) * I
  have hσc : Continuous σ := by simp only [σ]; fun_prop
  have hσre : ∀ w, (σ w).re = w.re := fun w => by simp [σ]
  have hσim : ∀ w, (σ w).im = s * w.im := fun w => by simp [σ]
  let Q : Set ℂ := Icc x₁ x₂ ×ℂ Icc 0 δ
  have habss : ∀ y : ℝ, |s * y| = |y| := fun y => by rcases hs with rfl | rfl <;> simp
  have hσR : ∀ w ∈ Q, σ w ∈ R := fun w hw => by
    refine ⟨by rw [mem_preimage, hσre]; exact hw.1, ?_⟩
    rw [mem_preimage, hσim, mem_Icc, ← abs_le, habss, abs_le]
    exact ⟨by linarith [hw.2.1], hw.2.2⟩
  have hσr : ∀ w ∈ Q, K (σ w) ∈ range j := fun w hw => by
    by_cases h0 : w.im = 0
    · obtain ⟨u, -, he⟩ := haxis (σ w) (hσR w hw) (by rw [hσim, h0]; simp)
      exact he ▸ ⟨_, rfl⟩
    · refine hs1 _ (hσR w hw) ?_
      rw [hσim, ← mul_assoc, hs0, one_mul]
      exact lt_of_le_of_ne hw.2.1 (Ne.symm h0)
  have hσinj : ∀ w w', σ w = σ w' → w = w' := fun w w' h => by
    have h1 : w.re = w'.re := by rw [← hσre w, ← hσre w', h]
    have h2 : s * w.im = s * w'.im := by rw [← hσim w, ← hσim w', h]
    have h3 : s * (s * w.im) = s * (s * w'.im) := by rw [h2]
    rw [← mul_assoc, ← mul_assoc, hs0, one_mul, one_mul] at h3
    exact Complex.ext h1 h3
  have hne : Nonempty S := ⟨g a⟩
  let χ : ℂ → S := fun w => Function.invFun j (K (σ w))
  have hχ : ∀ w ∈ Q, j (χ w) = K (σ w) := fun w hw => Function.invFun_eq (hσr w hw)
  have hcont : ContinuousOn χ Q := by
    rw [hj.isInducing.continuousOn_iff]
    exact ((hK.hc.comp hσc.continuousOn fun w hw => hRO (hσR w hw))).congr fun w hw => hχ w hw
  have hinj : InjOn χ Q := fun w hw w' hw' h => by
    have h1 : K (σ w) = K (σ w') := by rw [← hχ w hw, ← hχ w' hw', h]
    exact hσinj _ _ (hK.hi (hRO (hσR w hw)) (hRO (hσR w' hw')) h1)
  have hopen : IsOpen (χ '' (Ioo x₁ x₂ ×ℂ Ico 0 δ)) := by
    exact inner_half_strip_has_open_image (S := S) T j hj K x₁ x₂ δ hδ hWoR hKW s hs2 hs0 σ hσre
      hσim
      habss χ hχ
  have hbdiff : ∀ w ∈ Q, χ w ∈ bd S ↔ w.im = 0 := fun w hw => by
    constructor
    · intro h
      have h1 : K (σ w) ∈ j '' bd S := by rw [← hχ w hw]; exact mem_image_of_mem j h
      have h2 := hbdaxis _ (hσR w hw) h1
      rw [hσim] at h2
      rcases mul_eq_zero.mp h2 with h3 | h3
      · rcases hs with rfl | rfl <;> norm_num at h3
      · exact h3
    · intro h0
      obtain ⟨u, hp, he⟩ := haxis (σ w) (hσR w hw) (by rw [hσim, h0]; simp)
      have h1 : χ w = g (par u) := hj.injective (by rw [hχ w hw, he])
      rw [h1]
      exact hbd _ ⟨by linarith [hp.1], by linarith [hp.2]⟩
  refine ⟨χ, x₁, x₂, δ, ⟨hx, hδ, hcont, hinj, hopen, hbdiff⟩, fun w hw hz => ?_, fun u hu' => ?_⟩
  · refine (hRΩ (hσR w hw)).2 (.inl ⟨_, hz, ?_⟩)
    exact hχ w hw
  · obtain ⟨v, hv⟩ := hpars u ⟨by linarith [hu'.1], by linarith [hu'.2]⟩
    have hv1 : uc < v := hparm.lt_iff_lt.mp (by rw [huc, hv]; exact hu'.1)
    have hv2 : v < ud := hparm.lt_iff_lt.mp (by rw [hud, hv]; exact hu'.2)
    refine ⟨θ v, ⟨hθm hv1, hθm hv2⟩, ?_⟩
    have hmem : (θ v : ℂ) ∈ Q := ⟨by simpa using (⟨(hθm hv1).le, (hθm hv2).le⟩ : θ v ∈ Icc x₁ x₂),
      by simpa using hδ.le⟩
    refine hj.injective ?_
    rw [hχ _ hmem]
    have hσθ : σ (θ v : ℂ) = (θ v : ℂ) := by
      apply Complex.ext
      · rw [hσre]
      · rw [hσim]
        simp
    rw [hσθ, (hθ v).2]
    simp only [A, hv]

end GraphMinor.GM07
