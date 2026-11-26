/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Wedge

/-!
# A thin disc around a disc

Let `B` be a closed disc whose boundary lies in the interior of a surface, and let `Z` be a closed
set that meets `B` only on its boundary. We find a closed disc `Δ` around `B` that
meets `Z` only in `B`, and whose boundary leaves `B` at every point off `Z` (`exists_ring`). In a
collar of `B` the height of `Δ` above a point of the boundary of `B` is half the
distance to `Z`.
-/

@[expose] public section

namespace GraphMinor.Surface

open Set Topology Metric Filter

/-- The radial stretch of the plane by the factor `1 + d` in each direction. -/
noncomputable def stretch (d : ℂ → ℝ) (z : ℂ) : ℂ := ((1 + d (z / ‖z‖) : ℝ) : ℂ) * z

theorem norm_unit {z : ℂ} (hz : z ≠ 0) : ‖z / ‖z‖‖ = 1 := by
  rw [norm_div, Complex.norm_real, norm_norm, div_self (norm_ne_zero_iff.mpr hz)]

theorem norm_stretch {d : ℂ → ℝ} (hd : ∀ w, 0 ≤ d w) (z : ℂ) : ‖stretch d z‖ = (1 + d
  (z / ‖z‖)) * ‖z‖ := by
  rw [stretch, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith [hd (z / ‖z‖)])]

theorem continuousOn_stretch {d : ℂ → ℝ} (hc : Continuous d) (hd : ∀ w, 0 ≤ d w) (hb : ∀ w, ‖w‖ = 1
  → d w ≤ 1 / 2) : Continuous (stretch d) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z = 0
  · subst hz
    rw [ContinuousAt]
    have h0 : stretch d 0 = 0 := by simp [stretch]
    rw [h0, tendsto_zero_iff_norm_tendsto_zero]
    refine squeeze_zero (fun _ => norm_nonneg _) (g := fun z => 3 / 2 * ‖z‖) (fun y => ?_) ?_
    · rw [norm_stretch hd]
      by_cases hy : y = 0
      · simp [hy]
      · have := hb _ (norm_unit hy)
        have h2 := norm_nonneg y
        nlinarith
    · have h1 : Continuous fun z : ℂ => 3 / 2 * ‖z‖ := by fun_prop
      simpa using h1.tendsto (0 : ℂ)
  · have h1 : ContinuousAt (fun y : ℂ => y / ‖y‖) z := by
      refine ContinuousAt.div continuousAt_id (by fun_prop) ?_
      exact_mod_cast norm_ne_zero_iff.mpr hz
    have h2 : ContinuousAt (fun y : ℂ => d (y / ‖y‖)) z := hc.continuousAt.comp h1
    unfold stretch
    exact ((Complex.continuous_ofReal.continuousAt.comp (continuousAt_const.add h2))).mul
      continuousAt_id

theorem unit_stretch {d : ℂ → ℝ} (hd : ∀ w, 0 ≤ d w) {z : ℂ} : stretch d z / ‖stretch d z‖
  = z / ‖z‖ := by
  by_cases hz : z = 0
  · simp [hz, stretch]
  have h1 : 0 < 1 + d (z / ‖z‖) := by linarith [hd (z / ‖z‖)]
  rw [norm_stretch hd, stretch]
  push_cast
  have h3 : ((1 : ℂ) + (d (z / ‖z‖) : ℂ)) ≠ 0 := by
    exact_mod_cast h1.ne'
  have h4 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hz
  field_simp

theorem stretch_injective {d : ℂ → ℝ} (hd : ∀ w, 0 ≤ d w) : Function.Injective (stretch d) := by
  intro z z' he
  have h1 : z / ‖z‖ = z' / ‖z'‖ := by
    rw [← unit_stretch hd (z := z), ← unit_stretch hd (z := z'), he]
  have h2 : (1 + d (z / ‖z‖) : ℝ) ≠ 0 := by linarith [hd (z / ‖z‖)]
  rw [stretch, stretch, ← h1] at he
  exact mul_left_cancel₀ (by exact_mod_cast h2) he

/-- A closed disc around a closed disc that meets a closed set only where the small disc does. -/
theorem exists_ring {T : Type} [TopologicalSpace T] (hT : IsSurface T) {B Z : Set T}
  (hB : IsClosedDisc B) (hint : ∀ x ∈ discBd B, IsInteriorPoint x) (hZ : IsClosed Z)
    (hZB : Z ∩ B ⊆ discBd B) : ∃ Δ, IsClosedDisc Δ ∧ B ⊆ Δ ∧ Δ ∩ Z = B ∩ Z ∧ discBd Δ ∩ B = B ∩ Z
      := by
  have ht2 : T2Space T := hT.2.1
  have hman := hT.2.2
  obtain ⟨Δ', hΔ', hin, -⟩ := exists_disc_around hman hB hint isOpen_univ (subset_univ _)
  obtain ⟨p⟩ := hB.isOArc_discBd
  obtain ⟨c, c', hcc, hc'c, hmc, hmc', hl, -, hcB, -, hcp⟩ := exists_disc_collar hB hΔ' hin p
  have hsph : ∀ w : ℂ, ‖w‖ = 1 → c w ∈ discBd B := fun w hw => by
    have h1 := hcp ⟨w, by simpa [Submonoid.unitSphere] using hw⟩
    exact h1 ▸ (p _).2
  have hball : ∀ {z : ℂ}, ‖z‖ ≤ 1 → c z ∈ B := fun {z} hz => hcB ▸ mem_image_of_mem _
    (by simpa using hz)
  have hsub12 : closedBall (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 2 := closedBall_subset_closedBall
    (by norm_num)
  let Zh : Set ℂ := (closedBall 0 2 ∩ c ⁻¹' Z) ∪ sphere 0 2
  have hZhc : IsClosed Zh := (hcc.preimage_isClosed_of_isClosed isClosed_closedBall hZ).union
    isClosed_sphere
  have hZhne : Zh.Nonempty := ⟨2, .inr (by simp)⟩
  let d : ℂ → ℝ := fun w => infDist w Zh / 2
  have hdc : Continuous d := (continuous_infDist_pt Zh).div_const 2
  have hd : ∀ w, 0 ≤ d w := fun w => div_nonneg infDist_nonneg (by norm_num)
  have hb : ∀ w, ‖w‖ = 1 → d w ≤ 1 / 2 := fun w hw => by
    have h1 : infDist w Zh ≤ dist w (2 * w) := infDist_le_dist_of_mem (.inr (by simp [hw]))
    have h2 : dist w (2 * w) = 1 := by
      rw [dist_eq_norm, show w - 2 * w = -w by ring, norm_neg, hw]
    simp only [d]
    linarith
  have hclear : ∀ w : ℂ, ∀ s : ℝ, ‖w‖ = 1 → 0 < d w → 0 ≤ s → s ≤ d w → ((1 + s : ℝ) : ℂ) * w ∉ Zh
    := fun w s hw hdw hs hsd hmem => by
    have h1 : infDist w Zh ≤ dist w (((1 + s : ℝ) : ℂ) * w) := infDist_le_dist_of_mem hmem
    have h2 : dist w (((1 + s : ℝ) : ℂ) * w) = s := by
      rw [dist_eq_norm, show w - ((1 + s : ℝ) : ℂ) * w = -((s : ℂ) * w) by push_cast; ring,
        norm_neg, norm_mul, hw, Complex.norm_real, Real.norm_of_nonneg hs, mul_one]
    simp only [d] at hsd hdw
    linarith
  have hS := continuousOn_stretch hdc hd hb
  have hin2 : ∀ {z : ℂ}, ‖z‖ ≤ 1 → stretch d z ∈ closedBall (0 : ℂ) 2 := fun {z} hz => by
    rw [mem_closedBall, dist_zero_right, norm_stretch hd]
    by_cases h0 : z = 0
    · simp [h0]
    · have := hb _ (norm_unit h0)
      nlinarith [norm_nonneg z, hd (z / ‖z‖)]
  let f : ℂ → T := fun z => c (stretch d z)
  have hfc : ContinuousOn f (closedBall 0 1) := hcc.comp hS.continuousOn fun z hz => hin2
    (by simpa using hz)
  have hfi : InjOn f (closedBall 0 1) := fun z hz z' hz' he => by
    have h1 : ‖z‖ ≤ 1 := by simpa using hz
    have h2 : ‖z'‖ ≤ 1 := by simpa using hz'
    exact stretch_injective hd (by rw [← hl (hin2 h1), ← hl (hin2 h2)]; exact congrArg c' he)
  obtain ⟨hD, hbd⟩ := isClosedDisc_closedBall
  obtain ⟨hΔ, hΔb⟩ := isClosedDisc_image_injOn hD (isCompact_closedBall _ _) hfc hfi
  have hdec : ∀ {z : ℂ}, z ≠ 0 → ‖z / ‖z‖‖ = 1 ∧ ((‖z‖ : ℝ) : ℂ) * (z / ‖z‖) = z := fun {z} hz => by
    refine ⟨norm_unit hz, ?_⟩
    have h4 : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast norm_ne_zero_iff.mpr hz
    field_simp
  have hsubB : B ⊆ f '' closedBall 0 1 := by
    intro y₀ hy₀
    rw [← hcB] at hy₀
    obtain ⟨z, hz, rfl⟩ := hy₀
    have hz1 : ‖z‖ ≤ 1 := by simpa using hz
    by_cases h0 : z = 0
    · exact ⟨0, by simp, by simp [f, stretch, h0]⟩
    obtain ⟨hu, hzz⟩ := hdec h0
    let w := z / ‖z‖
    have h1 : 0 < 1 + d w := by linarith [hd w]
    let y : ℂ := ((‖z‖ / (1 + d w) : ℝ) : ℂ) * w
    have hyn : ‖y‖ = ‖z‖ / (1 + d w) := by
      rw [norm_mul, hu, mul_one, Complex.norm_real, Real.norm_of_nonneg (div_nonneg
        (norm_nonneg _) h1.le)]
    have hyne : y ≠ 0 := by
      rw [← norm_ne_zero_iff, hyn]
      exact (div_pos (norm_pos_iff.mpr h0) h1).ne'
    have hyu : y / ‖y‖ = w := by
      have h2 := (hdec hyne).2
      have h3 : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by
        exact_mod_cast norm_ne_zero_iff.mpr hyne
      apply mul_left_cancel₀ h3
      rw [h2, hyn]
    refine ⟨y, ?_, ?_⟩
    · simp only [mem_closedBall, dist_zero_right]
      rw [hyn, div_le_one h1]
      linarith [hd w]
    · change c (stretch d y) = c z
      congr 1
      rw [stretch, hyu]
      change ((1 + d w : ℝ) : ℂ) * (((‖z‖ / (1 + d w) : ℝ) : ℂ) * w) = z
      rw [← mul_assoc, ← Complex.ofReal_mul, mul_div_cancel₀ _ h1.ne']
      exact hzz
  have hdz : ∀ {w : ℂ}, d w = 0 → w ∈ Zh := fun {w} hw => by
    have h1 : infDist w Zh = 0 := by
      simp only [d] at hw
      linarith
    exact (hZhc.mem_iff_infDist_zero hZhne).mpr h1
  have hzd : ∀ {w : ℂ}, w ∈ Zh → d w = 0 := fun {w} hw => by
    simp only [d]
    rw [infDist_zero_of_mem hw]
    simp
  have hnotz : ∀ {w : ℂ}, ‖w‖ = 1 → w ∈ Zh → c w ∈ Z := by
    rintro w hw (h | h)
    · exact h.2
    · rw [mem_sphere_zero_iff_norm, hw] at h
      norm_num at h
  have hone : ∀ {w : ℂ}, ‖w‖ = 1 → w / ‖w‖ = w := fun {w} hw => by simp [hw]
  have hst : ∀ {w : ℂ}, ‖w‖ = 1 → d w = 0 → stretch d w = w := fun {w} hw h0 => by
    simp [stretch, hone hw, h0]
  have hkey : ∀ z, ‖z‖ ≤ 1 → f z ∈ Z → f z ∈ B := by
    intro z hz hfz
    by_cases h0 : z = 0
    · have h1 : stretch d z = 0 := by simp [h0, stretch]
      change c (stretch d z) ∈ B
      rw [h1]
      exact hball (by simp)
    obtain ⟨hu, hzz⟩ := hdec h0
    set w := z / ‖z‖ with hw
    have hy : stretch d z = (((1 + d w) * ‖z‖ : ℝ) : ℂ) * w := by
      rw [stretch, ← hw]
      push_cast
      rw [mul_assoc]
      congr 1
      exact_mod_cast hzz.symm
    by_cases hτ : (1 + d w) * ‖z‖ ≤ 1
    · refine hball ?_
      rw [norm_stretch hd]
      exact hτ
    · exfalso
      push Not at hτ
      have h1 : (1 + d w) * ‖z‖ ≤ 1 + d w := by nlinarith [hd w]
      have hdw : 0 < d w := by nlinarith [norm_nonneg z]
      have h2 := hclear w ((1 + d w) * ‖z‖ - 1) hu hdw (by linarith) (by linarith)
      rw [show (1 + ((1 + d w) * ‖z‖ - 1) : ℝ) = (1 + d w) * ‖z‖ by ring, ← hy] at h2
      exact h2 (.inl ⟨hin2 hz, hfz⟩)
  refine ⟨_, hΔ, hsubB, ?_, ?_⟩
  · apply subset_antisymm
    · rintro _ ⟨⟨z, hz, rfl⟩, hZz⟩
      exact ⟨hkey z (by simpa using hz) hZz, hZz⟩
    · exact fun x hx => ⟨hsubB hx.1, hx.2⟩
  · rw [hΔb, hbd]
    apply subset_antisymm
    · rintro _ ⟨⟨z, hz, rfl⟩, hzB⟩
      have hz1 : ‖z‖ = 1 := by simpa using hz
      rw [← hcB] at hzB
      obtain ⟨q, hq, he⟩ := hzB
      have h1 : q = stretch d z := by
        rw [← hl (hsub12 hq), he]
        exact hl (hin2 hz1.le)
      have h2 : ‖stretch d z‖ ≤ 1 := by
        rw [← h1]
        simpa using hq
      rw [norm_stretch hd, hone hz1, hz1, mul_one] at h2
      have h3 : d z = 0 := by linarith [hd z]
      have h4 := hst hz1 h3
      refine ⟨by rw [← hcB]; exact ⟨q, hq, he⟩, ?_⟩
      change c (stretch d z) ∈ Z
      rw [h4]
      exact hnotz hz1 (hdz h3)
    · rintro y ⟨hyB, hyZ⟩
      have hyb : y ∈ discBd B := hZB ⟨hyZ, hyB⟩
      let q := p.symm ⟨y, hyb⟩
      have hq : c (q : ℂ) = y := by
        rw [hcp]
        simp [q]
      have hqn : ‖(q : ℂ)‖ = 1 := Circle.norm_coe q
      have h1 : (q : ℂ) ∈ Zh := by
        refine .inl ⟨hsub12 (mem_closedBall_zero_iff.mpr hqn.le), ?_⟩
        rw [mem_preimage, hq]
        exact hyZ
      have h2 := hst hqn (hzd h1)
      exact ⟨⟨_, mem_sphere_zero_iff_norm.mpr hqn, by change c (stretch d q) = y; rw [h2, hq]⟩, hyB⟩

end GraphMinor.Surface
