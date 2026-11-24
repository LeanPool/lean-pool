/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collapse
public import LeanPool.GraphMinor.Surface.Cap

/-!
# A thin disc around a line

Let `L` be a line with ends `u, v` in a closed surface, and let `Z` be a closed set that meets `L`
only at its ends. Then there is a closed disc around `L` that meets `Z` only at `u, v`, with `u, v`
on its boundary and the rest of `L` inside (`exists_edge_lens`). The line cuts the disc into two
sides, each connected and each with all of `L` in its closure.

We make `L` straight with `exists_stripChart`, and take the region between two graphs over `L`, of
height at most half the distance to `Z`. Its image of the unit disc is `lensMap`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Complex

local notation "𝕀" => unitInterval

/-- A map of the unit disc onto the region of height `w` over the real line. -/
noncomputable def lensMap (w : ℝ → ℝ) (z : ℂ) : ℂ :=
  (z.re : ℂ) + (w z.re * (z.im / Real.sqrt (1 - z.re ^ 2)) : ℝ) * I

theorem lensMap_re (w : ℝ → ℝ) (z : ℂ) : (lensMap w z).re = z.re := by
  simp [lensMap]

theorem lensMap_im (w : ℝ → ℝ) (z : ℂ) : (lensMap w z).im = w z.re * (z.im / Real.sqrt
  (1 - z.re ^ 2)) := by
  simp [lensMap]

theorem abs_ratio_le {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : |z.im / Real.sqrt (1 - z.re ^ 2)|
  ≤ 1 := by
  have h1 : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
    have h2 : ‖z‖ ≤ 1 := by simpa using hz
    have h3 := Complex.sq_norm z
    rw [Complex.normSq_apply] at h3
    nlinarith [norm_nonneg z]
  rw [abs_div, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_one_of_le₀ _ (Real.sqrt_nonneg _)
  exact Real.abs_le_sqrt (by linarith)

theorem continuousOn_lensMap {w : ℝ → ℝ} (hw : Continuous w) (h1 : w 1 = 0) (hm : w (-1)
  = 0) : ContinuousOn (lensMap w) (closedBall 0 1) := by
  have hb : ContinuousOn (fun z : ℂ => w z.re * (z.im / Real.sqrt (1 - z.re ^ 2))) (closedBall 0 1)
    := fun z hz => by
    by_cases hre : z.re ^ 2 < 1
    · have hne : Real.sqrt (1 - z.re ^ 2) ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
      refine ContinuousAt.continuousWithinAt ?_
      have h2 : ContinuousAt (fun z : ℂ => Real.sqrt (1 - z.re ^ 2)) z := by fun_prop
      exact ContinuousAt.mul (by fun_prop) (ContinuousAt.div (by fun_prop) h2 hne)
    · have hz1 : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
        have h2 : ‖z‖ ≤ 1 := by simpa using hz
        have h3 := Complex.sq_norm z
        rw [Complex.normSq_apply] at h3
        nlinarith [norm_nonneg z]
      have hre2 : z.re = 1 ∨ z.re = -1 := by
        have h4 : (z.re - 1) * (z.re + 1) = 0 := by nlinarith [sq_nonneg z.im]
        rcases mul_eq_zero.mp h4 with h5 | h5
        · exact .inl (by linarith)
        · exact .inr (by linarith)
      have hw0 : w z.re = 0 := by
        rcases hre2 with h | h <;> rw [h]
        · exact h1
        · exact hm
      rw [ContinuousWithinAt, hw0, zero_mul]
      have hc : ContinuousAt (fun z : ℂ => w z.re) z := by fun_prop
      refine squeeze_zero_norm' ?_ (show Filter.Tendsto (fun x : ℂ => ‖w x.re‖)
        (𝓝[closedBall 0 1] z) (𝓝 0) from ?_)
      · filter_upwards [self_mem_nhdsWithin] with x hx
        rw [norm_mul]
        have h5 : ‖x.im / Real.sqrt (1 - x.re ^ 2)‖ ≤ 1 := by
          rw [Real.norm_eq_abs]
          exact abs_ratio_le hx
        nlinarith [norm_nonneg (w x.re)]
      · have h2 : Filter.Tendsto (fun x : ℂ => w x.re) (𝓝 z) (𝓝 0) := by
          have := hc.tendsto
          rwa [hw0] at this
        exact (h2.norm.mono_left nhdsWithin_le_nhds).trans (by simp)
  have hl : ContinuousOn (fun z : ℂ => ((z.re : ℂ) + ((w z.re * (z.im / Real.sqrt
    (1 - z.re ^ 2)) : ℝ) : ℂ) * I)) (closedBall 0 1) :=
    ContinuousOn.add (by fun_prop) ((continuous_ofReal.comp_continuousOn hb).mul continuousOn_const)
  exact hl

theorem re_sq_add_im_sq_le {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) : z.re ^ 2 + z.im ^ 2 ≤ 1 := by
  have h2 : ‖z‖ ≤ 1 := by simpa using hz
  have h3 := Complex.sq_norm z
  rw [Complex.normSq_apply] at h3
  nlinarith [norm_nonneg z]

theorem eq_one_or_of_re {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) (h : ¬ z.re ∈ Ioo (-1 : ℝ) 1) : z
  = 1 ∨ z = -1 := by
  have h1 := re_sq_add_im_sq_le hz
  have h2 : z.re ≤ -1 ∨ 1 ≤ z.re := by
    by_contra hc
    push Not at hc
    exact h ⟨hc.1, hc.2⟩
  rcases h2 with h2 | h2
  · right
    have h3 : z.re = -1 := by nlinarith [sq_nonneg z.im]
    have h4 : z.im = 0 := by
      rw [h3] at h1
      nlinarith [sq_nonneg z.im]
    exact Complex.ext (by simpa using h3) (by simpa using h4)
  · left
    have h3 : z.re = 1 := by nlinarith [sq_nonneg z.im]
    have h4 : z.im = 0 := by
      rw [h3] at h1
      nlinarith [sq_nonneg z.im]
    exact Complex.ext (by simpa using h3) (by simpa using h4)

theorem re_mem_Ioo_sqrt {z : ℂ} (h : z.re ∈ Ioo (-1 : ℝ) 1) : 0 < Real.sqrt (1 - z.re ^ 2) :=
  Real.sqrt_pos.mpr (by nlinarith [h.1, h.2])

section plane

variable {Z : Set ℂ}

/-- The height of the lens. -/
noncomputable def lensW (Z : Set ℂ) (s : ℝ) : ℝ := infDist (s : ℂ) Z / 2

theorem lensW_pos (hZ : IsClosed Z) (hne : Z.Nonempty) {s : ℝ} (hs : (s : ℂ) ∉ Z) : 0 < lensW Z s
  := by
  have := (hZ.notMem_iff_infDist_pos hne).mp hs
  unfold lensW
  positivity

theorem lensMap_notMem (hZ : IsClosed Z) (hne : Z.Nonempty) (hs : ∀ s ∈ Ioo (-1 : ℝ) 1,
  (s : ℂ) ∉ Z) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1)
    (hr : z.re ∈ Ioo (-1 : ℝ) 1) : lensMap (lensW Z) z ∉ Z := fun hin => by
  have hpos := lensW_pos hZ hne (hs _ hr)
  have h1 : infDist (z.re : ℂ) Z ≤ dist (z.re : ℂ) (lensMap (lensW Z) z)
    := infDist_le_dist_of_mem hin
  have h2 : dist (z.re : ℂ) (lensMap (lensW Z) z) ≤ lensW Z z.re := by
    have h3 : (z.re : ℂ) - lensMap (lensW Z) z = -(((lensW Z z.re * (z.im / Real.sqrt
      (1 - z.re ^ 2)) : ℝ) : ℂ) * I) := by
      simp [lensMap]
    rw [dist_eq_norm, h3, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      norm_mul, Real.norm_of_nonneg hpos.le, Real.norm_eq_abs]
    nlinarith [abs_ratio_le hz]
  have e : lensW Z z.re = infDist (z.re : ℂ) Z / 2 := rfl
  rw [e] at hpos h2
  linarith

theorem injOn_lensMap (hZ : IsClosed Z) (hne : Z.Nonempty) (hs : ∀ s ∈ Ioo (-1 : ℝ) 1,
  (s : ℂ) ∉ Z) : InjOn (lensMap (lensW Z)) (closedBall 0 1) := fun z hz z' hz' he => by
  have h1 : z.re = z'.re := by rw [← lensMap_re (lensW Z) z, he, lensMap_re]
  by_cases hr : z.re ∈ Ioo (-1 : ℝ) 1
  · have h2 := congrArg Complex.im he
    rw [lensMap_im, lensMap_im, ← h1] at h2
    have hpos := lensW_pos hZ hne (hs _ hr)
    have h3 := mul_left_cancel₀ hpos.ne' h2
    rw [div_left_inj₀ (re_mem_Ioo_sqrt hr).ne'] at h3
    exact Complex.ext h1 h3
  · have hr' : z'.re ∉ Ioo (-1 : ℝ) 1 := h1 ▸ hr
    rcases eq_one_or_of_re hz hr with rfl | rfl <;>
      rcases eq_one_or_of_re hz' hr' with rfl | rfl <;> first | rfl | (norm_num at h1)

end plane

/-- A continuous injective map on a closed disc gives a closed disc. -/
theorem IsClosedDisc.image_injOn {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space Y]
  {Δ : Set X} (hΔ : IsClosedDisc Δ) {f : X → Y} (hf : ContinuousOn f Δ)
    (hi : InjOn f Δ) : IsClosedDisc (f '' Δ) ∧ discBd (f '' Δ) = f '' discBd Δ := by
  classical
  have hcΔ : CompactSpace Δ := by
    obtain ⟨e⟩ := id hΔ
    have : CompactSpace ClosedUnitDisc := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
    exact e.compactSpace
  obtain ⟨e₀⟩ := id hΔ
  let x₀ : Δ := e₀ ⟨0, by simp [ClosedUnitDisc]⟩
  let g : Δ → f '' Δ := fun x => ⟨f x.1, x.1, x.2, rfl⟩
  have hg : Continuous g := (continuousOn_iff_continuous_domRestrict.mp hf).subtype_mk _
  have hb : Function.Bijective g := ⟨fun x y h => Subtype.ext (hi x.2 y.2
    (congrArg Subtype.val h)), fun ⟨_, x, hx, rfl⟩ => ⟨⟨x, hx⟩, rfl⟩⟩
  let e : Δ ≃ₜ f '' Δ := Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective g hb) hg
  let f' : Y → X := fun y => if h : y ∈ f '' Δ then (e.symm ⟨y, h⟩).1 else x₀.1
  have hf' : ContinuousOn f' (f '' Δ) := by
    rw [continuousOn_iff_continuous_domRestrict]
    have he : (f '' Δ).domRestrict f' = fun y => (e.symm y).1 := by
      funext y
      exact dite_eq_left y.2
    rw [he]
    exact continuous_subtype_val.comp e.symm.continuous
  refine hΔ.image hf hf' fun x hx => ?_
  have h1 : f x ∈ f '' Δ := ⟨x, hx, rfl⟩
  have h2 : e ⟨x, hx⟩ = ⟨f x, h1⟩ := rfl
  have h3 : e.symm ⟨f x, h1⟩ = ⟨x, hx⟩ := by rw [← h2, e.symm_apply_apply]
  change f' (f x) = x
  rw [show f' (f x) = (e.symm ⟨f x, h1⟩).1 from dite_eq_left h1, h3]

theorem lensMap_real {w : ℝ → ℝ} (s : ℝ) : lensMap w s = s := by
  apply Complex.ext
  · simp [lensMap]
  · simp [lensMap]

variable {T : Type} [TopologicalSpace T]

private theorem lens_side_path {Φ : ℂ → T} {u v : T}
    (hΦc : ContinuousOn Φ (closedBall 0 1)) (hΦm : Φ (-1) = u) (hΦ1 : Φ 1 = v)
    (c : ℝ) (hc' : |c| = 1) :
    ∃ p : Path u v, range p ⊆ Φ '' closedBall 0 1 ∧
      ∀ t : 𝕀, 0 < t → t < 1 →
      p t ∈ Φ '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < c * z.im} := by
  have hcc : c * c = 1 := by rw [← abs_mul_self, abs_mul, hc', one_mul]
  let z : 𝕀 → ℂ := fun t => ((2 * t.1 - 1 : ℝ) : ℂ) + ((2 * c * t.1 * (1 - t.1) : ℝ) : ℂ) * I
  have hzre : ∀ t, (z t).re = 2 * t.1 - 1 := fun t => by simp [z]
  have hzim : ∀ t, (z t).im = 2 * c * t.1 * (1 - t.1) := fun t => by simp [z]
  have hzb : ∀ t, z t ∈ closedBall (0 : ℂ) 1 := fun t => by
    have h0 := t.2.1
    have h1 := t.2.2
    have hp : 0 ≤ t.1 * (1 - t.1) := mul_nonneg h0 (by linarith)
    have hq : t.1 * (1 - t.1) ≤ 1 := by nlinarith
    have hsq : (z t).re ^ 2 + (z t).im ^ 2 ≤ 1 := by
      rw [hzre, hzim]
      have e : (2 * c * t.1 * (1 - t.1)) ^ 2 = 4 * (c * c) * (t.1 * (1 - t.1)) ^ 2 := by ring
      rw [e, hcc]
      nlinarith
    have h3 := Complex.sq_norm (z t)
    rw [Complex.normSq_apply] at h3
    rw [mem_closedBall_zero_iff]
    nlinarith [norm_nonneg (z t)]
  have hzc : Continuous z := by
    change Continuous fun t : 𝕀 => ((2 * t.1 - 1 : ℝ) : ℂ) + ((2 * c * t.1 * (1 - t.1) : ℝ) : ℂ) * I
    fun_prop
  have hz0 : z 0 = -1 := by
    apply Complex.ext
    · rw [hzre]
      norm_num
    · rw [hzim]
      simp
  have hz1 : z 1 = 1 := by
    apply Complex.ext
    · rw [hzre]
      norm_num
    · rw [hzim]
      simp
  refine ⟨⟨⟨fun t => Φ (z t), hΦc.comp_continuous hzc hzb⟩, by simp [hz0, hΦm], by simp [hz1,
    hΦ1]⟩, ?_, ?_⟩
  · rintro _ ⟨t, rfl⟩
    exact ⟨z t, hzb t, rfl⟩
  · intro t h0 h1
    refine ⟨z t, ⟨hzb t, ?_⟩, rfl⟩
    have h0' : 0 < t.1 := h0
    have h1' : t.1 < 1 := h1
    rw [hzim]
    have e : c * (2 * c * t.1 * (1 - t.1)) = 2 * (c * c) * t.1 * (1 - t.1) := by ring
    rw [e, hcc]
    have := mul_pos h0' (sub_pos.mpr h1')
    nlinarith

private theorem lens_from_disc_map [T2Space T] {L Z : Set T} {u v : T} {Φ : ℂ → T}
    (hΦc : ContinuousOn Φ (closedBall 0 1)) (hΦi : InjOn Φ (closedBall 0 1))
    (hΦm : Φ (-1) = u) (hΦ1 : Φ 1 = v)
    (hsball : ∀ s ∈ Icc (-1 : ℝ) 1, (s : ℂ) ∈ closedBall (0 : ℂ) 1)
    (hΦL : ∀ s ∈ Icc (-1 : ℝ) 1, Φ s ∈ L)
    (hLs : ∀ y ∈ L, ∃ s ∈ Icc (-1 : ℝ) 1, Φ s = y)
    (hΦavoid : ∀ z ∈ closedBall (0 : ℂ) 1, z.re ∈ Ioo (-1 : ℝ) 1 → Φ z ∉ Z) :
    ∃ D A B, IsClosedDisc D ∧ L ⊆ D ∧ D ∩ Z ⊆ {u, v} ∧ u ∈ discBd D ∧ v ∈ discBd D
      ∧ discBd D ∩ L ⊆ {u, v} ∧
      D = A ∪ B ∪ L ∧ IsPreconnected A ∧ IsPreconnected B ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A L
        ∧ Disjoint B L ∧ L ⊆ closure A ∧ L ⊆ closure B ∧
      (∃ p : Path u v, range p ⊆ D ∧ ∀ t : 𝕀, 0 < t → t < 1 → p t ∈ A) ∧
        (∃ p : Path u v, range p ⊆ D ∧ ∀ t : 𝕀, 0 < t → t < 1 → p t ∈ B) ∧
      Disjoint A B ∧ IsPathConnected (A \ discBd D) ∧ IsPathConnected (B \ discBd D) := by
  obtain ⟨hball, hballbd⟩ := isClosedDisc_of_convex (convex_closedBall (0 : ℂ) 1) (by
    rw [interior_closedBall _ one_ne_zero]
    exact ⟨0, by simp⟩) isBounded_closedBall isClosed_closedBall
  obtain ⟨hD, hDb⟩ := hball.image_injOn hΦc hΦi
  rw [hballbd, frontier_closedBall _ one_ne_zero] at hDb
  have hnotL : ∀ z ∈ closedBall (0 : ℂ) 1, z.im ≠ 0 → Φ z ∉ L := fun z hz him hzL => by
    obtain ⟨s, hs', hse⟩ := hLs _ hzL
    have := hΦi (hsball s hs') hz hse
    exact him (by rw [← this]; simp)
  have hclo : ∀ (c : ℝ), c ≠ 0 → |c| = 1 → L ⊆ closure (Φ '' {z | z ∈ closedBall (0 : ℂ) 1
    ∧ 0 < c * z.im}) := fun c _ hc y hy => by
    obtain ⟨s, hs', rfl⟩ := hLs y hy
    refine ContinuousWithinAt.mem_closure_image (hΦc _ (hsball s hs') |>.mono fun z hz => hz.1) ?_
    rw [Metric.mem_closure_iff]
    intro ε hε
    set τ := min 1 (ε / 3) with hτ
    have hτ0 : 0 < τ := lt_min one_pos (by positivity)
    have hτ1 : τ ≤ 1 := min_le_left _ _
    have hτ2 : τ ≤ ε / 3 := min_le_right _ _
    have hsn : ‖(s : ℂ)‖ ≤ 1 := by simpa using hsball s hs'
    have hin : ‖((c : ℂ) * I)‖ = 1 := by simp [hc]
    refine ⟨(1 - τ : ℝ) * (s : ℂ) + (τ : ℝ) * ((c : ℂ) * I), ⟨?_, ?_⟩, ?_⟩
    · rw [mem_closedBall_zero_iff]
      calc _ ≤ ‖((1 - τ : ℝ) : ℂ) * (s : ℂ)‖ + ‖((τ : ℝ) : ℂ) * ((c : ℂ) * I)‖ := norm_add_le _ _
        _ ≤ (1 - τ) * 1 + τ * 1 := by
          have hsn' : ‖s‖ ≤ 1 := by simpa [Complex.norm_real] using hsn
          simp only [norm_mul, hin, Complex.norm_real, Real.norm_of_nonneg hτ0.le,
            Real.norm_of_nonneg (show 0 ≤ 1 - τ by linarith)]
          nlinarith
        _ = 1 := by ring
    · have him : ((1 - τ : ℝ) * (s : ℂ) + (τ : ℝ) * ((c : ℂ) * I)).im = τ * c := by simp
      rw [him]
      have hcc : c * c = 1 := by rw [← abs_mul_self, abs_mul, hc, one_mul]
      nlinarith
    · have he : (s : ℂ) - ((1 - τ : ℝ) * (s : ℂ) + (τ : ℝ) * ((c : ℂ) * I)) = (τ : ℝ) * ((s : ℂ) -
      (c : ℂ) * I) := by
        push_cast
        ring
      rw [dist_eq_norm, he, norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ0.le]
      have h2 : ‖(s : ℂ) - (c : ℂ) * I‖ ≤ 2 := by
        calc _ ≤ ‖(s : ℂ)‖ + ‖(c : ℂ) * I‖ := norm_sub_le _ _
          _ ≤ 2 := by rw [hin]; linarith
      nlinarith
  have hconv : ∀ c : ℝ, Convex ℝ {z : ℂ | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < c * z.im} := fun c => by
    change Convex ℝ (closedBall (0 : ℂ) 1 ∩ {z : ℂ | 0 < c * z.im})
    refine (convex_closedBall _ _).inter ?_
    intro x hx y hy p q hp hq hpq
    have e : c * (p • x + q • y).im = p * (c * x.im) + q * (c * y.im) := by
      simp
      ring
    change 0 < c * (p • x + q • y).im
    rw [e]
    have hx' : 0 < c * x.im := hx
    have hy' : 0 < c * y.im := hy
    rcases hp.eq_or_lt with h | h
    · have : q = 1 := by linarith
      subst h
      simpa [this] using hy'
    · have := mul_pos h hx'
      have := mul_nonneg hq hy'.le
      linarith
  have hupc := hconv 1
  have hloc := hconv (-1)
  have hpath := lens_side_path hΦc hΦm hΦ1
  have hin : ∀ c : ℝ, IsPathConnected (Φ '' {z | z ∈ closedBall (0 : ℂ) 1
    ∧ 0 < c * z.im} \ Φ '' sphere 0 1) ∨ c = 0 := fun c => by
    by_cases hc : c = 0
    · exact .inr hc
    left
    have hbc : Convex ℝ {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧ 0 < c * z.im} := by
      have e : {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧ 0 < c * z.im} = ball (0 : ℂ) 1 ∩ {z | z ∈ closedBall
        (0 : ℂ) 1 ∧ 0 < c * z.im} := by
        ext z
        exact ⟨fun h => ⟨h.1, ball_subset_closedBall h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
      rw [e]
      exact (convex_ball _ _).inter (hconv c)
    have hne : {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧ 0 < c * z.im}.Nonempty := by
      refine ⟨(((1 / 2 : ℝ) * c / |c| : ℝ) : ℂ) * I, ?_, ?_⟩
      · have : ‖(((1 / 2 : ℝ) * c / |c| : ℝ) : ℂ) * I‖ = 1 / 2 := by
          rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_div,
            abs_mul, abs_abs, div_eq_mul_inv]
          have h2 : |c| ≠ 0 := abs_ne_zero.mpr hc
          field_simp
          simp
        rw [mem_ball_zero_iff, this]
        norm_num
      · have h2 : 0 < |c| := abs_pos.mpr hc
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
          Complex.I_re, mul_one, mul_zero, add_zero]
        have : c * ((1 / 2 : ℝ) * c / |c|) = (c * c) / (2 * |c|) := by ring
        rw [this]
        have := mul_self_pos.mpr hc
        positivity
    have e : Φ '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < c * z.im} \ Φ '' sphere 0 1
      = Φ '' {z | z ∈ ball (0 : ℂ) 1 ∧ 0 < c * z.im} := by
      ext y
      constructor
      · rintro ⟨⟨z, hz, rfl⟩, hy⟩
        refine ⟨z, ⟨?_, hz.2⟩, rfl⟩
        have h1 : ‖z‖ ≤ 1 := by simpa using hz.1
        have h2 : ‖z‖ ≠ 1 := fun h => hy ⟨z, by simpa using h, rfl⟩
        simpa using lt_of_le_of_ne h1 h2
      · rintro ⟨z, hz, rfl⟩
        refine ⟨⟨z, ⟨ball_subset_closedBall hz.1, hz.2⟩, rfl⟩, ?_⟩
        rintro ⟨z', hz', he⟩
        have := hΦi (sphere_subset_closedBall hz') (ball_subset_closedBall hz.1) he
        rw [this] at hz'
        have h1 : ‖z‖ = 1 := by simpa using hz'
        have h2 : ‖z‖ < 1 := by simpa using hz.1
        linarith
    rw [e]
    exact (hbc.isPathConnected hne).image' (hΦc.mono fun z hz => ball_subset_closedBall hz.1)
  refine ⟨Φ '' closedBall 0 1, Φ '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < (1 : ℝ) * z.im},
    Φ '' {z | z ∈ closedBall (0 : ℂ) 1 ∧ 0 < (-1 : ℝ) * z.im}, hD, ?_, ?_, ?_, ?_, ?_, ?_,
    (hupc.isPreconnected.image _ (hΦc.mono fun z hz => hz.1)), (hloc.isPreconnected.image _
      (hΦc.mono fun z hz => hz.1)), ?_, ?_, ?_, ?_, hclo 1 one_ne_zero (by simp), hclo (-1)
        (by norm_num) (by simp), hpath 1 (by simp), hpath (-1) (by simp), ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨s, hs', rfl⟩ := hLs y hy
    exact ⟨s, hsball s hs', rfl⟩
  · rintro y ⟨⟨z, hz, rfl⟩, hyZ⟩
    by_cases hre : z.re ∈ Ioo (-1 : ℝ) 1
    · exact absurd hyZ (hΦavoid z hz hre)
    · rcases eq_one_or_of_re hz hre with rfl | rfl
      · exact .inr hΦ1
      · exact .inl hΦm
  · rw [hDb]
    exact ⟨-1, by simp, hΦm⟩
  · rw [hDb]
    exact ⟨1, by simp, hΦ1⟩
  · rintro y ⟨hy, hyL⟩
    rw [hDb] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have hzb : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz
    by_cases hre : z.re ∈ Ioo (-1 : ℝ) 1
    · exfalso
      have him : z.im = 0 := not_ne_iff.mp fun hn => hnotL z hzb hn hyL
      have hz1 : ‖z‖ = 1 := by simpa using hz
      have hsq := Complex.sq_norm z
      rw [Complex.normSq_apply, hz1, him] at hsq
      nlinarith [hre.1, hre.2]
    · rcases eq_one_or_of_re hzb hre with rfl | rfl
      · exact .inr hΦ1
      · exact .inl hΦm
  · apply Subset.antisymm
    · rintro _ ⟨z, hz, rfl⟩
      rcases lt_trichotomy z.im 0 with h | h | h
      · exact .inl (.inr ⟨z, ⟨hz, by linarith⟩, rfl⟩)
      · refine .inr ?_
        have e : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [h])
        rw [e]
        have hn := re_sq_add_im_sq_le hz
        rw [h] at hn
        exact hΦL _ ⟨by nlinarith, by nlinarith⟩
      · exact .inl (.inl ⟨z, ⟨hz, by linarith⟩, rfl⟩)
    · refine union_subset (union_subset (image_mono fun z hz => hz.1) (image_mono fun z hz
      => hz.1)) ?_
      intro y hy
      obtain ⟨s, hs', rfl⟩ := hLs y hy
      exact ⟨s, hsball s hs', rfl⟩
  · exact ⟨_, I, ⟨by simp, by simp⟩, rfl⟩
  · exact ⟨_, -I, ⟨by simp, by simp⟩, rfl⟩
  · rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩
    exact hnotL z hz.1 (by have := hz.2; intro h; simp [h] at this)
  · rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩
    exact hnotL z hz.1 (by have := hz.2; intro h; simp [h] at this)
  · rw [Set.disjoint_left]
    rintro _ ⟨z, hz, rfl⟩ ⟨z', hz', he⟩
    have := hΦi hz'.1 hz.1 he
    rw [this] at hz'
    have h1 := hz.2
    have h2 := hz'.2
    linarith
  · rw [hDb]
    exact (hin 1).resolve_right one_ne_zero
  · rw [hDb]
    exact (hin (-1)).resolve_right (by norm_num)

/-- **A thin disc around a line.** See the module docstring. -/
theorem exists_edge_lens_sides (hT : IsClosedSurface T) {L : Set T} {u v : T}
  (hL : IsLineWithEnds L u v) (_huv : u ≠ v) {Z : Set T} (hZ : IsClosed Z) (hLZ : L ∩ Z ⊆ {u, v}) :
    ∃ D A B, IsClosedDisc D ∧ L ⊆ D ∧ D ∩ Z ⊆ {u, v} ∧ u ∈ discBd D ∧ v ∈ discBd D
      ∧ discBd D ∩ L ⊆ {u, v} ∧
      D = A ∪ B ∪ L ∧ IsPreconnected A ∧ IsPreconnected B ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A L
        ∧ Disjoint B L ∧ L ⊆ closure A ∧ L ⊆ closure B ∧
      (∃ p : Path u v, range p ⊆ D ∧ ∀ t : 𝕀, 0 < t → t < 1 → p t ∈ A) ∧
        (∃ p : Path u v, range p ⊆ D ∧ ∀ t : 𝕀, 0 < t → t < 1 → p t ∈ B) ∧
      Disjoint A B ∧ IsPathConnected (A \ discBd D) ∧ IsPathConnected (B \ discBd D) := by
  classical
  have hcpt : CompactSpace T := hT.1
  have ht2 : T2Space T := hT.2.1
  have hman : ∀ x : T, IsManifoldPoint x := fun x => (hT.2.2 x).isManifoldPoint
  obtain ⟨a, ha, hr, ha0, ha1⟩ := hL.exists_arc
  obtain ⟨D₀, hD₀, hs⟩ := exists_disc_of_arc hT ha
  obtain ⟨h, g, cc⟩ := hD₀.exists_isChart
  have hbc : BallChart 1 (g '' ball 0 1) h g := by
    refine ⟨cc.isOpen_image_ball hman, cc.hc.mono ?_, cc.gc.mono ball_subset_closedBall, ?_, ?_,
      ?_, ?_⟩
    · rintro _ ⟨z, hz, rfl⟩
      exact cc.gm (ball_subset_closedBall hz)
    · rintro _ ⟨z, hz, rfl⟩
      rwa [cc.hg (ball_subset_closedBall hz)]
    · exact fun z hz => ⟨z, hz, rfl⟩
    · rintro _ ⟨z, hz, rfl⟩
      rw [cc.hg (ball_subset_closedBall hz)]
    · exact fun z hz => cc.hg (ball_subset_closedBall hz)
  have hU : range a ⊆ g '' ball 0 1 := by
    rw [← cc.discInt_eq]
    exact hs
  obtain ⟨O, K, θ, hK, hθc, hθm, hθ⟩ := exists_stripChart hman hbc ha hU
  have hlt : θ 0 < θ 1 := hθm (by simp)
  set A : ℝ := (θ 1 - θ 0) / 2 with hA
  set B : ℝ := (θ 0 + θ 1) / 2 with hB
  have hApos : 0 < A := by rw [hA]; linarith
  let aff : ℂ → ℂ := fun z => (B : ℂ) + (A : ℂ) * z
  have haffc : Continuous aff := by fun_prop
  have haffi : Function.Injective aff := fun x y h' => by
    have h1 : (A : ℂ) * x = (A : ℂ) * y := add_left_cancel h'
    exact mul_left_cancel₀ (by exact_mod_cast hApos.ne') h1
  have hreal : ∀ s : ℝ, aff s = ((B + A * s : ℝ) : ℂ) := fun s => by
    simp [aff]
  have hone : aff 1 = (θ 1 : ℂ) := by
    have := hreal 1
    simp only [Complex.ofReal_one] at this
    rw [this]
    congr 1
    rw [hA, hB]
    ring
  have hmone : aff (-1) = (θ 0 : ℂ) := by
    have := hreal (-1)
    simp only [Complex.ofReal_neg, Complex.ofReal_one] at this
    rw [this]
    congr 1
    rw [hA, hB]
    ring
  let O₁ : Set ℂ := aff ⁻¹' O
  have hO₁ : IsOpen O₁ := hK.isOpen.preimage haffc
  let K₁ : ℂ → T := K ∘ aff
  have hK₁c : ContinuousOn K₁ O₁ := hK.hc.comp haffc.continuousOn fun _ h' => h'
  have hK₁i : InjOn K₁ O₁ := fun x hx y hy h' => haffi (hK.hi hx hy h')
  have h1O : (1 : ℂ) ∈ O₁ := by
    change aff 1 ∈ O
    rw [hone]
    exact (hθ 1).1
  have hmO : (-1 : ℂ) ∈ O₁ := by
    change aff (-1) ∈ O
    rw [hmone]
    exact (hθ 0).1
  have hK1 : K₁ 1 = v := by
    change K (aff 1) = v
    rw [hone, (hθ 1).2, ha1]
  have hKm : K₁ (-1) = u := by
    change K (aff (-1)) = u
    rw [hmone, (hθ 0).2, ha0]
  have hsθ : ∀ s ∈ Icc (-1 : ℝ) 1, ∃ t, θ t = B + A * s := fun s hs' => by
    apply mem_range_of_exists_le_of_exists_ge hθc
    · exact ⟨0, by rw [hA, hB]; nlinarith [hs'.1]⟩
    · exact ⟨1, by rw [hA, hB]; nlinarith [hs'.2]⟩
  have hsO : ∀ s ∈ Icc (-1 : ℝ) 1, ∃ t, (s : ℂ) ∈ O₁ ∧ K₁ s = a t ∧ θ t = B + A * s := fun s hs'
    => by
    obtain ⟨t, ht⟩ := hsθ s hs'
    have e : aff s = (θ t : ℂ) := by rw [hreal, ht]
    refine ⟨t, ?_, ?_, ht⟩
    · change aff s ∈ O
      rw [e]
      exact (hθ t).1
    · change K (aff s) = a t
      rw [e, (hθ t).2]
  let Z₁ : Set ℂ := (O₁ᶜ ∪ (O₁ ∩ K₁ ⁻¹' Z)) ∪ {1, -1}
  have hZ₁ : IsClosed Z₁ := by
    have h1 : (O₁ ∩ K₁ ⁻¹' Zᶜ) = (O₁ᶜ ∪ (O₁ ∩ K₁ ⁻¹' Z))ᶜ := by
      ext z
      simp only [mem_inter_iff, mem_preimage, mem_compl_iff, mem_union, not_or, not_and, not_not]
      exact ⟨fun h' => ⟨h'.1, fun _ => h'.2⟩, fun h' => ⟨h'.1, h'.2 h'.1⟩⟩
    have h2 : IsOpen (O₁ ∩ K₁ ⁻¹' Zᶜ) := hK₁c.isOpen_inter_preimage hO₁ hZ.isOpen_compl
    rw [h1] at h2
    exact (isOpen_compl_iff.mp h2).union ((finite_singleton _).insert _).isClosed
  have hZne : Z₁.Nonempty := ⟨1, .inr (.inl rfl)⟩
  have hsZ : ∀ s ∈ Ioo (-1 : ℝ) 1, (s : ℂ) ∉ Z₁ := fun s hs' hin => by
    obtain ⟨t, hO, hKt, hθt⟩ := hsO s ⟨hs'.1.le, hs'.2.le⟩
    have ht0 : t ≠ 0 := fun h' => by
      rw [h', hA, hB] at hθt
      nlinarith [hs'.1]
    have ht1 : t ≠ 1 := fun h' => by
      rw [h', hA, hB] at hθt
      nlinarith [hs'.2]
    rcases hin with (h1 | h1) | h1
    · exact h1 hO
    · have h2 : a t ∈ L ∩ Z := ⟨hr ▸ mem_range_self t, hKt ▸ h1.2⟩
      rcases hLZ h2 with h3 | h3
      · exact ht0 (ha.2 (h3.trans ha0.symm))
      · exact ht1 (ha.2 (h3.trans ha1.symm))
    · rcases h1 with h1 | h1
      · have : s = 1 := by exact_mod_cast h1
        linarith [hs'.2]
      · have h1' : (s : ℂ) = -1 := h1
        have : s = -1 := by
          have h2 := congrArg Complex.re h1'
          simpa using h2
        linarith [hs'.1]
  let w := lensW Z₁
  have hwc : Continuous w := by
    change Continuous fun s : ℝ => infDist (s : ℂ) Z₁ / 2
    exact ((continuous_infDist_pt Z₁).comp continuous_ofReal).div_const 2
  have hw1 : w 1 = 0 := by
    change infDist (((1 : ℝ) : ℂ)) Z₁ / 2 = 0
    have hmem : (1 : ℂ) ∈ Z₁ := .inr (.inl rfl)
    rw [Complex.ofReal_one, infDist_zero_of_mem hmem, zero_div]
  have hwm : w (-1) = 0 := by
    change infDist (((-1 : ℝ) : ℂ)) Z₁ / 2 = 0
    have hmem : (-1 : ℂ) ∈ Z₁ := .inr (.inr rfl)
    rw [Complex.ofReal_neg, Complex.ofReal_one, infDist_zero_of_mem hmem, zero_div]
  have hlc := continuousOn_lensMap hwc hw1 hwm
  have hli := injOn_lensMap hZ₁ hZne hsZ
  have hl1 : lensMap w 1 = 1 := by simpa using lensMap_real (w := w) 1
  have hlm : lensMap w (-1) = -1 := by simpa using lensMap_real (w := w) (-1)
  have hlin : ∀ z ∈ closedBall (0 : ℂ) 1, z.re ∈ Ioo (-1 : ℝ) 1 → lensMap w z ∈ O₁ ∧ K₁
    (lensMap w z) ∉ Z := fun z hz hre => by
    have h1 := lensMap_notMem hZ₁ hZne hsZ hz hre
    have h2 : lensMap w z ∈ O₁ := by
      by_contra hc
      exact h1 (.inl (.inl hc))
    exact ⟨h2, fun h3 => h1 (.inl (.inr ⟨h2, h3⟩))⟩
  have hlO : ∀ z ∈ closedBall (0 : ℂ) 1, lensMap w z ∈ O₁ := fun z hz => by
    by_cases hre : z.re ∈ Ioo (-1 : ℝ) 1
    · exact (hlin z hz hre).1
    · rcases eq_one_or_of_re hz hre with rfl | rfl
      · rw [hl1]
        exact h1O
      · rw [hlm]
        exact hmO
  let Φ : ℂ → T := K₁ ∘ lensMap w
  have hΦc : ContinuousOn Φ (closedBall 0 1) := hK₁c.comp hlc hlO
  have hΦi : InjOn Φ (closedBall 0 1) := fun x hx y hy he => hli hx hy (hK₁i (hlO x hx)
    (hlO y hy) he)
  have hΦ1 : Φ 1 = v := by
    change K₁ (lensMap w 1) = v
    rw [hl1, hK1]
  have hΦm : Φ (-1) = u := by
    change K₁ (lensMap w (-1)) = u
    rw [hlm, hKm]
  have hts : ∀ t, ∃ s ∈ Icc (-1 : ℝ) 1, θ t = B + A * s := fun t => by
    refine ⟨(θ t - B) / A, ⟨?_, ?_⟩, by field_simp; ring⟩
    · rw [le_div_iff₀ hApos]
      have := hθm.monotone (unitInterval.nonneg' (t := t))
      rw [hA, hB]
      linarith
    · rw [div_le_iff₀ hApos]
      have := hθm.monotone (unitInterval.le_one' (t := t))
      rw [hA, hB]
      linarith
  have hsball : ∀ s ∈ Icc (-1 : ℝ) 1, (s : ℂ) ∈ closedBall (0 : ℂ) 1 := fun s hs' => by
    have : |s| ≤ 1 := abs_le.mpr hs'
    simpa [Complex.norm_real] using this
  have hΦs : ∀ t, ∀ s : ℝ, θ t = B + A * s → Φ s = a t := fun t s hst => by
    change K₁ (lensMap w s) = a t
    rw [lensMap_real]
    change K (aff s) = a t
    rw [hreal, ← hst, (hθ t).2]
  have hΦL : ∀ s ∈ Icc (-1 : ℝ) 1, Φ s ∈ L := fun s hs' => by
    obtain ⟨t, -, hKt, hθt⟩ := hsO s hs'
    rw [hΦs t s hθt, ← hr]
    exact mem_range_self t
  have hLs : ∀ y ∈ L, ∃ s ∈ Icc (-1 : ℝ) 1, Φ s = y := fun y hy => by
    obtain ⟨t, rfl⟩ : y ∈ range a := hr ▸ hy
    obtain ⟨s, hs', hst⟩ := hts t
    exact ⟨s, hs', hΦs t s hst⟩
  exact lens_from_disc_map hΦc hΦi hΦm hΦ1 hsball hΦL hLs
    (fun z hz hre => (hlin z hz hre).2)

/-- A thin closed disc around a line, with its two sides. -/
theorem exists_edge_lens (hT : IsClosedSurface T) {L : Set T} {u v : T} (hL : IsLineWithEnds L u v)
  (huv : u ≠ v) {Z : Set T} (hZ : IsClosed Z) (hLZ : L ∩ Z ⊆ {u, v}) :
    ∃ D A B, IsClosedDisc D ∧ L ⊆ D ∧ D ∩ Z ⊆ {u, v} ∧ u ∈ discBd D ∧ v ∈ discBd D
      ∧ discBd D ∩ L ⊆ {u, v} ∧
      D = A ∪ B ∪ L ∧ IsPreconnected A ∧ IsPreconnected B ∧ A.Nonempty ∧ B.Nonempty ∧ Disjoint A L
        ∧ Disjoint B L ∧ L ⊆ closure A ∧ L ⊆ closure B ∧
      (∃ p : Path u v, range p ⊆ D ∧ ∀ t : 𝕀, 0 < t → t < 1 → p t ∈ A) ∧
        (∃ p : Path u v, range p ⊆ D ∧ ∀ t : 𝕀, 0 < t → t < 1 → p t ∈ B) := by
  obtain ⟨D, A, B, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, -⟩
    := exists_edge_lens_sides hT hL huv hZ hLZ
  exact ⟨D, A, B, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17⟩

end GraphMinor.Surface
