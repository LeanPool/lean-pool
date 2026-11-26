/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.Section5e

/-!
# The outside of a disc near a point of its boundary

Let `Δ` be a closed disc in a surface and let `y` be a point of its boundary that lies off the
boundary of the
surface. Near `y` the complement of `Δ` is connected. The disc itself may touch the boundary of the
surface
elsewhere, so we pass to a small part of `Δ` near `y`, and use a collar around that part.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface

/-- In the plane, the outside of the unit circle is connected near a point of the circle. Small
polar rectangles
give the connected sets. -/
theorem outside_near {w : ℂ} (hw : ‖w‖ = 1) :
    ∀ W ∈ 𝓝 w, ∃ B ⊆ {u : ℂ | 1 < ‖u‖} ∩ W, IsPreconnected B ∧
      ∃ W' ∈ 𝓝 w, {u : ℂ | 1 < ‖u‖} ∩ W' ⊆ B := by
  intro W hW
  have hw0 : w ≠ 0 := by
    intro h
    simp [h] at hw
  let P : ℝ × ℝ → ℂ := fun p ↦ (p.1 : ℂ) * w * Complex.exp (p.2 * Complex.I)
  have hPc : Continuous P := by fun_prop
  have hP0 : P (1, 0) = w := by simp [P]
  have hpre : P ⁻¹' W ∈ 𝓝 ((1 : ℝ), (0 : ℝ)) := hPc.continuousAt.preimage_mem_nhds (by rwa [hP0])
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp hpre
  have hrect : ∀ r t : ℝ, |r - 1| < ε → |t| < ε → P (r, t) ∈ W := by
    intro r t hr ht
    apply hsub
    rw [Metric.mem_ball, Prod.dist_eq]
    simpa [Real.dist_eq] using And.intro hr ht
  refine ⟨P '' (Ioo 1 (1 + ε) ×ˢ Ioo (-ε) ε), ?_, ?_, ?_⟩
  · rintro _ ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩
    refine ⟨?_, hrect r t ?_ ?_⟩
    · have hr0 : 0 ≤ r := by linarith [hr.1]
      have : ‖P (r, t)‖ = r := by
        simp only [P, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0, hw,
          Complex.norm_exp_ofReal_mul_I, mul_one]
      change 1 < ‖P (r, t)‖
      rw [this]
      exact hr.1
    · rw [abs_lt]
      constructor <;> linarith [hr.1, hr.2]
    · rw [abs_lt]
      exact ⟨ht.1, ht.2⟩
  · exact ((convex_Ioo _ _).prod (convex_Ioo _ _)).isPreconnected.image _ hPc.continuousOn
  · let Q : ℂ → ℝ × ℝ := fun u ↦ (‖u‖, Complex.arg (u / w))
    have hdiv : w / w = 1 := div_self hw0
    have hQ : ContinuousAt Q w := by
      refine continuous_norm.continuousAt.prodMk ?_
      have hA : ContinuousAt Complex.arg (w / w) := by
        rw [hdiv]
        exact Complex.continuousAt_arg (by simp)
      exact ContinuousAt.comp (f := fun u : ℂ ↦ u / w) hA (by fun_prop)
    have hQw : Q w = (1, 0) := by simp [Q, hw, hdiv]
    refine ⟨Q ⁻¹' (Ioo (1 - ε) (1 + ε) ×ˢ Ioo (-ε) ε), hQ.preimage_mem_nhds ?_, ?_⟩
    · rw [hQw]
      exact (isOpen_Ioo.prod isOpen_Ioo).mem_nhds ⟨⟨by linarith, by linarith⟩, ⟨by linarith, hε⟩⟩
    · rintro u ⟨hu, hu'⟩
      refine ⟨(‖u‖, Complex.arg (u / w)), ⟨⟨hu, hu'.1.2⟩, hu'.2⟩, ?_⟩
      have h := Complex.norm_mul_exp_arg_mul_I (u / w)
      have hn : ‖u / w‖ = ‖u‖ := by simp [hw]
      rw [hn] at h
      change (‖u‖ : ℂ) * w * Complex.exp (Complex.arg (u / w) * Complex.I) = u
      calc (‖u‖ : ℂ) * w * Complex.exp (Complex.arg (u / w) * Complex.I)
          = w * ((‖u‖ : ℂ) * Complex.exp (Complex.arg (u / w) * Complex.I)) := by ring
        _ = u := by rw [h]; field_simp

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-- **The outside of a disc near a boundary point.** The point `y` of the boundary of `Δ` lies off
`bd(Σ)`. Then
`Σ \ Δ` is connected near `y`, and `y` is a limit of it. -/
theorem isConnectedNear_compl_disc (hS : IsSurface S) {Δ : Set S} (hΔ : IsClosedDisc Δ) {y : S}
    (hy : y ∈ discBd Δ) (hi : y ∉ bd S) : IsConnectedNear Δᶜ y ∧ y ∈ closure Δᶜ := by
  have hman : ∀ x : S, IsManifoldPoint x := hS.2.2
  have hbdc : IsClosed (bd S) := (cuff_statement S hS).1
  have hnotnhds : ∀ {E : Set S}, E ⊆ Δ → E ∉ 𝓝 y := fun hE hn ↦
    hi (mem_bd_of_disc (Filter.mem_of_superset hn hE) hy)
  refine ⟨?_, ?_⟩
  swap
  · rw [closure_compl]
    exact fun h ↦ hnotnhds subset_rfl (mem_interior_iff_mem_nhds.mp h)
  obtain ⟨h, g, c⟩ := hΔ.exists_isChart
  have hyΔ : y ∈ Δ := discBd_subset Δ hy
  have hgy : g (h y) = y := c.gh hyΔ
  have hz : h y ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hy
  set z := h y with hzdef
  have hzn : ‖z‖ = 1 := by simpa using hz
  have hzc : z ∈ closedBall (0 : ℂ) 1 := sphere_subset_closedBall hz
  have hgpre : g ⁻¹' (bd S)ᶜ ∈ 𝓝[closedBall 0 1] z :=
    (c.gc z hzc).preimage_mem_nhdsWithin (hbdc.isOpen_compl.mem_nhds (by rwa [hgy]))
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhdsWithin_iff.mp hgpre
  let Z : Set ℂ := closedBall 0 1 ∩ closedBall z (ε / 2)
  have hZsub : Z ⊆ closedBall 0 1 := inter_subset_left
  have hZint : (interior Z).Nonempty := by
    let t : ℝ := min (ε / 4) (1 / 2)
    have ht0 : 0 < t := lt_min (by linarith) (by norm_num)
    have ht1 : t ≤ ε / 4 := min_le_left _ _
    have ht2 : t ≤ 1 / 2 := min_le_right _ _
    let p : ℂ := ((1 - t : ℝ) : ℂ) * z
    refine ⟨p, mem_interior.mpr ⟨ball p (t / 2), ?_, isOpen_ball, mem_ball_self (by linarith)⟩⟩
    intro u hu
    have hu' : ‖u - p‖ < t / 2 := by simpa [dist_eq_norm] using hu
    have hp : ‖p‖ = 1 - t := by
      simp only [p, norm_mul, hzn, mul_one, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_nonneg (by linarith)
    have hpz : ‖p - z‖ = t := by
      have : p - z = -((t : ℝ) : ℂ) * z := by
        simp only [p]
        push_cast
        ring
      rw [this, norm_mul, norm_neg, hzn, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos ht0]
    constructor
    · rw [mem_closedBall, dist_zero_right]
      calc ‖u‖ = ‖(u - p) + p‖ := by rw [sub_add_cancel]
        _ ≤ ‖u - p‖ + ‖p‖ := norm_add_le _ _
        _ ≤ 1 := by linarith
    · rw [mem_closedBall, dist_eq_norm]
      calc ‖u - z‖ = ‖(u - p) + (p - z)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖u - p‖ + ‖p - z‖ := norm_add_le _ _
        _ ≤ ε / 2 := by linarith
  have hZd := isClosedDisc_of_convex ((convex_closedBall _ _).inter (convex_closedBall _ _)) hZint
    (isBounded_closedBall.subset hZsub) (isClosed_closedBall.inter isClosed_closedBall)
  have hΔ₀ : IsClosedDisc (g '' Z) := (c.disc_g hZsub hZd.1).1
  have hΔ₀sub : g '' Z ⊆ Δ := image_subset_iff.mpr fun u hu ↦ c.gm (hZsub hu)
  have hΔ₀int : g '' Z ⊆ (bd S)ᶜ := by
    rintro _ ⟨u, hu, rfl⟩
    refine hsub ⟨?_, hu.1⟩
    exact closedBall_subset_ball (half_lt_self hε) hu.2
  have hyZ : y ∈ g '' Z := ⟨z, ⟨hzc, mem_closedBall_self (by linarith)⟩, hgy⟩
  have hybd : y ∈ discBd (g '' Z) := by
    by_contra hn
    exact hnotnhds hΔ₀sub (Filter.mem_of_superset
      ((hΔ₀.isOpen_discInt hman).mem_nhds ⟨hyZ, hn⟩) sdiff_subset)
  obtain ⟨E, hE, hin, -⟩ := Surface.exists_disc_around hman hΔ₀
    (fun x hx ↦ not_not.mp (hΔ₀int (discBd_subset _ hx))) isOpen_univ (subset_univ _)
  obtain ⟨p⟩ := hΔ₀.isOArc_discBd
  obtain ⟨cc, c', hcc, hc', hccm, hc'm, hl, hr, himg, -, hcirc⟩ := exists_disc_collar hΔ₀ hE hin p
  let w : Circle := p.symm ⟨y, hybd⟩
  have hccw : cc w = y := by rw [hcirc]; simp [w]
  have hwn : ‖(w : ℂ)‖ = 1 := by simp
  have hw2 : (w : ℂ) ∈ ball (0 : ℂ) 2 := by simp [hwn]
  have hcw : (w : ℂ) ∈ closedBall (0 : ℂ) 2 := ball_subset_closedBall hw2
  have hc'y : c' y = w := by rw [← hccw]; exact hl hcw
  -- points of `Δ` near `y` are in the small part
  let K₀ : Set S := g '' (closedBall 0 1 \ ball z (ε / 2))
  have hK₀c : IsClosed K₀ := (((isCompact_closedBall (0 : ℂ) 1).inter_right
    isOpen_ball.isClosed_compl).image_of_continuousOn
    (c.gc.mono inter_subset_left)).isClosed
  have hyK₀ : y ∉ K₀ := by
    rintro ⟨u, hu, hgu⟩
    have : u = z := by rw [hzdef, ← hgu]; exact (c.hg hu.1).symm
    exact hu.2 (this ▸ mem_ball_self (by linarith))
  have hΔK₀ : ∀ x ∈ Δ, x ∉ K₀ → x ∈ g '' Z := by
    intro x hx hxn
    have hxm := c.hm hx
    by_cases hb : h x ∈ ball z (ε / 2)
    · exact ⟨h x, ⟨hxm, ball_subset_closedBall hb⟩, c.gh hx⟩
    · exact absurd ⟨h x, ⟨hxm, hb⟩, c.gh hx⟩ hxn
  intro W hW
  have hW₀ : W ∩ K₀ᶜ ∈ 𝓝 y := Filter.inter_mem hW (hK₀c.isOpen_compl.mem_nhds hyK₀)
  have hcat : ContinuousAt cc w := hcc.continuousAt
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hw2) ball_subset_closedBall)
  have hW₂ : cc ⁻¹' (W ∩ K₀ᶜ) ∩ closedBall 0 2 ∈ 𝓝 (w : ℂ) := Filter.inter_mem
    (hcat.preimage_mem_nhds (by rwa [hccw]))
    (Filter.mem_of_superset (isOpen_ball.mem_nhds hw2) ball_subset_closedBall)
  obtain ⟨B, hBs, hBc, W', hW', hW'B⟩ := outside_near hwn _ hW₂
  have hdE : IsOpen (discInt E) := hE.isOpen_discInt hman
  have hyE : y ∈ discInt E := hin hyZ
  have hc'at : ContinuousAt c' y := hc'.continuousAt
    (Filter.mem_of_superset (hdE.mem_nhds hyE) sdiff_subset)
  refine ⟨cc '' B, ?_, hBc.image _ (hcc.mono fun u hu ↦ (hBs hu).2.2), discInt E ∩ c' ⁻¹' W',
    Filter.inter_mem (hdE.mem_nhds hyE) (hc'at.preimage_mem_nhds (by rwa [hc'y])), ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨hu₁, ⟨hu₂, hu₃⟩, hu₄⟩ := hBs hu
    refine ⟨fun hmem ↦ ?_, hu₂⟩
    obtain ⟨v, hv, hve⟩ := himg.symm ▸ hΔK₀ _ hmem hu₃
    have hv2 : v ∈ closedBall (0 : ℂ) 2 := closedBall_subset_closedBall (by norm_num) hv
    have : v = u := by rw [← hl hv2, ← hl hu₄, hve]
    rw [mem_closedBall, dist_zero_right, this] at hv
    exact absurd hu₁ (not_lt.mpr hv)
  · rintro x ⟨hxΔ, hxE, hxW⟩
    have hxE' : x ∈ E := hxE.1
    have hu := hc'm hxE'
    refine ⟨c' x, hW'B ⟨?_, hxW⟩, hr hxE'⟩
    by_contra hnl
    have hu1 : c' x ∈ closedBall (0 : ℂ) 1 := by
      rw [mem_closedBall, dist_zero_right]
      exact not_lt.mp hnl
    have : x ∈ g '' Z := by
      rw [← himg, ← hr hxE']
      exact mem_image_of_mem cc hu1
    exact hxΔ (hΔ₀sub this)

end GraphMinor.GM19
