/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

import LeanPool.GraphMinor.GM12.Section79

public import LeanPool.GraphMinor.GM15.Section3Crosscap
public import LeanPool.GraphMinor.GM14.Section9a
import LeanPool.GraphMinor.Surface.Collar

import LeanPool.GraphMinor.GM12.Section6

import LeanPool.GraphMinor.GM12.Section77

/-!
# Graph Minors XV, (3.4): Parallel Paths Across a Region

This file gives the proof of **Graph Minors XV, (3.4)**, pages 122–123, in a chart of the closed
disc $\bar\Lambda$ in which the paths $P_1, \dots, P_{k-1}$ are vertical chords
(`theorem_3_4_of_chart`). Given a `Σ`-span `(H, η, T)` of order `θ`, a region `Λ` of `H` bounded by
a circuit containing distinct vertices `v₁, …, v_{2k}` in order such that `{v₁, …, v_{2k}}` is free
with respect to `T`, and the drawing `H' = H ∪ P₁ ∪ … ∪ P_{k-1}`, it shows that `H'` with the
induced tangle is a `Σ`-span of order `θ`, and that the regions `r₁, r₂ ⊆ Λ` of `H'` incident with
`v_k, v_{2k}` satisfy `d'(r₁, r₂) ≥ 2k - 6` and `d'(v_k, v_{2k}) ≥ 2k - 8`.
`GraphMinor/GM15/Section3Given.lean` gets such a chart for any such `H'`.

The proof follows Robertson and Seymour, *Graph Minors. XV. Giant Steps*, pages 122–123.
-/

@[expose] public section

namespace GraphMinor.GM15

open Set Function Topology Metric
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM12 GM14
open scoped unitInterval

universe u v w

/-! ## 1. Tangle Metric Bounds Between Incident Regions, Vertices, and Edges -/

section MetricBounds

variable {S : Type w} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]

/-- If `d` is the metric of a respectful tangle `(H, θ, T)`, `r ∈ H.R`, `e ∈ H.E`, and
`e ⊆ closure r`, then `d r e ≤ 2` and `d e r ≤ 2`. -/
theorem hasTangleMetric_region_edge_le (hS : IsClosedSurface S)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hd : HasTangleMetric H θ T d)
    {r e : Set S} (hr : r ∈ H.R) (he : e ∈ H.E) (her : e ⊆ closure r) :
    d r e ≤ 2 ∧ d e r ≤ 2 := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hhd := hd
  obtain ⟨hResp, K, ins, hK, hds, hdeq⟩ := hd
  have hP := hK.2.1
  obtain ⟨y, hy⟩ := he.1
  have hdisj : Disjoint e K.U := disjoint_left.mpr fun z hz hzK => by
    have hzV : z ∈ H.V := by
      have hV_eq : H.V = H.U ∩ K.U := hP.1.symm
      rw [hV_eq]
      exact ⟨(he.2.1 hz).1, hzK⟩
    exact (he.2.1 hz).2 hzV
  obtain ⟨r', hr', hyr'⟩ := exists_region_of_notMem (disjoint_left.mp hdisj hy)
  have her' : e ⊆ r' := subset_region hr' he.2.2.1.isConnected.isPreconnected hdisj hy hyr'
  obtain ⟨z, hzr', hzr⟩ := mem_closure_iff.mp (her hy) r' (region_isOpen hr') hyr'
  have hle : tangleMetric H K ins θ r e ≤ 2 :=
    GM14.tangleMetric_region_edge_le hS hResp hK hds hr he hr' her' ⟨z, hzr, hzr'⟩
  have hre : d r e ≤ 2 := by
    rw [hdeq r (Or.inr hr) e (Or.inl (Or.inr he))]
    exact hle
  have her_le : d e r ≤ 2 := by
    have hsymm := (gm15_theorem_9_1 H θ T d hS inferInstance hhd).2.2.2.1 e (Or.inl (Or.inr he)) r
      (Or.inr hr)
    omega
  exact ⟨hre, her_le⟩

/-- In the setup of XV (3.4), if `2 * (k - 1) ≤ d' e₁ e₂` where `e₁ ⊆ closure r₂`,
`e₂ ⊆ closure r₁`, `v_k ∈ closure r₁`, and `v_{2k} ∈ closure r₂`, then
`2 * k - 6 ≤ d' r₁ r₂` and `2 * k - 8 ≤ d' {v_k} {v_{2k}}` (Graph Minors XV, page 123). -/
theorem tangleMetric_bounds_of_parallel_paths (hS : IsClosedSurface S)
    {H' : Drawing S} {θ k : ℕ}
    {T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d' : Set S → Set S → ℕ}
    (hd' : HasTangleMetric H' θ T' d')
    {r₁ r₂ e₁ e₂ : Set S} {v₁ v₂ : S}
    (hr₁ : r₁ ∈ H'.R) (hr₂ : r₂ ∈ H'.R)
    (he₁ : e₁ ∈ H'.E) (he₂ : e₂ ∈ H'.E)
    (he₁_r₂ : e₁ ⊆ closure r₂) (he₂_r₁ : e₂ ⊆ closure r₁)
    (hv₁ : v₁ ∈ H'.V) (hv₂ : v₂ ∈ H'.V)
    (hv₁_r₁ : v₁ ∈ closure r₁) (hv₂_r₂ : v₂ ∈ closure r₂)
    (hdist : 2 * (k - 1) ≤ d' e₁ e₂) :
    2 * k - 6 ≤ d' r₁ r₂ ∧ 2 * k - 8 ≤ d' {v₁} {v₂} := by
  obtain ⟨_, _, _, hsymm, htri, hvr, _⟩ := gm15_theorem_9_1 H' θ T' d' hS inferInstance hd'
  have hr₁A : r₁ ∈ H'.A := Or.inr hr₁
  have hr₂A : r₂ ∈ H'.A := Or.inr hr₂
  have he₁A : e₁ ∈ H'.A := Or.inl (Or.inr he₁)
  have he₂A : e₂ ∈ H'.A := Or.inl (Or.inr he₂)
  have hv₁A : ({v₁} : Set S) ∈ H'.A := Or.inl (Or.inl ⟨v₁, hv₁, rfl⟩)
  have hv₂A : ({v₂} : Set S) ∈ H'.A := Or.inl (Or.inl ⟨v₂, hv₂, rfl⟩)
  have h_e₁_r₂ : d' e₁ r₂ ≤ 2 := (hasTangleMetric_region_edge_le hS hd' hr₂ he₁ he₁_r₂).2
  have h_r₁_e₂ : d' r₁ e₂ ≤ 2 := (hasTangleMetric_region_edge_le hS hd' hr₁ he₂ he₂_r₁).1
  have h_r₂_r₁ : d' r₂ r₁ = d' r₁ r₂ := hsymm r₂ hr₂A r₁ hr₁A
  have h_tri1 : d' e₁ e₂ ≤ d' e₁ r₂ + d' r₂ e₂ := htri e₁ he₁A r₂ hr₂A e₂ he₂A
  have h_tri2 : d' r₂ e₂ ≤ d' r₂ r₁ + d' r₁ e₂ := htri r₂ hr₂A r₁ hr₁A e₂ he₂A
  have h_r₁_r₂ : 2 * k - 6 ≤ d' r₁ r₂ := by omega
  have hE_ne : H'.E.Nonempty := ⟨e₁, he₁⟩
  have h_v₁_r₁ : d' {v₁} r₁ ≤ 1 := hvr hE_ne v₁ hv₁ r₁ hr₁ hv₁_r₁
  have h_r₁_v₁ : d' r₁ {v₁} = d' {v₁} r₁ := hsymm r₁ hr₁A {v₁} hv₁A
  have h_v₂_r₂ : d' {v₂} r₂ ≤ 1 := hvr hE_ne v₂ hv₂ r₂ hr₂ hv₂_r₂
  have h_tri3 : d' r₁ r₂ ≤ d' r₁ {v₁} + d' {v₁} r₂ := htri r₁ hr₁A {v₁} hv₁A r₂ hr₂A
  have h_tri4 : d' {v₁} r₂ ≤ d' {v₁} {v₂} + d' {v₂} r₂ := htri {v₁} hv₁A {v₂} hv₂A r₂ hr₂A
  refine ⟨h_r₁_r₂, by omega⟩

end MetricBounds

/-! ## 2. Disc Charts Matching a Prescribed Boundary Circle Homeomorphism -/

section DiscChartWithBd

variable {S : Type w} [TopologicalSpace S]

/-- Given a closed disc `Δ ⊆ S` and a boundary homeomorphism `p : Circle ≃ₜ discBd Δ`, there exists
a chart `IsChart Δ h g` such that `g w = (p w).1` for every `w : Circle`. -/
theorem exists_isChart_with_bd {Δ : Set S} (hΔ : IsClosedDisc Δ)
    (p : Circle ≃ₜ discBd Δ) :
    ∃ h g, IsChart Δ h g ∧ ∀ w : Circle, g w = (p w).1 := by
  obtain ⟨h', g', cD⟩ := hΔ.exists_isChart
  have hbdΔ : discBd Δ ⊆ Δ := Surface.discBd_subset Δ
  obtain ⟨r, hr⟩ := exists_homeomorph_image (cD.hc.mono hbdΔ)
    (cD.gc.mono (cD.image_subset hbdΔ)) (cD.gh.mono hbdΔ)
  obtain ⟨o, ho⟩ := exists_circle_sphere
  obtain ⟨h₀, k₀, m₀, hv₀⟩ := exists_bdMatch ((o.symm.trans p).trans r)
  rw [cD.bd] at m₀
  have hoS : Nonempty (Circle ≃ₜ sphere (0 : ℂ) 1) := ⟨o⟩
  obtain ⟨Ψ, hΨ, hΨi⟩ := exists_plane_homeomorph hoS hoS m₀
  rw [closedInner_sphere] at hΨi
  have hΨ_maps : MapsTo Ψ (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) :=
    fun z hz => hΨi ▸ mem_image_of_mem Ψ hz
  have hΨsymm_maps : MapsTo Ψ.symm (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) := by
    intro w hw
    rw [← hΨi] at hw
    obtain ⟨z, hz, rfl⟩ := hw
    simpa using hz
  have hh₀ : ∀ w : Circle, h₀ w = h' (p w).1 := fun w => by
    have h1 := hv₀ (o w)
    rw [ho w] at h1
    rw [h1]
    simp [hr]
  let h : S → ℂ := fun x => Ψ.symm (h' x)
  let g : ℂ → S := fun z => g' (Ψ z)
  have hg_w : ∀ w : Circle, g w = (p w).1 := fun w => by
    have hw : (w : ℂ) ∈ sphere (0 : ℂ) 1 := mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w)
    change g' (Ψ w) = (p w).1
    rw [hΨ hw, hh₀ w, cD.gh (hbdΔ (p w).2)]
  have h_left : LeftInvOn h g (closedBall (0 : ℂ) 1) := fun z hz => by
    change Ψ.symm (h' (g' (Ψ z))) = z
    rw [cD.hg (hΨ_maps hz), Ψ.symm_apply_apply]
  have hg_sph : g '' sphere (0 : ℂ) 1 = discBd Δ := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      let w : Circle := ⟨z, by simpa [Submonoid.unitSphere] using hz⟩
      exact hg_w w ▸ (p w).2
    · intro hx
      obtain ⟨w, hw⟩ := p.surjective ⟨x, hx⟩
      exact ⟨w, mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w),
        (hg_w w).trans (congrArg Subtype.val hw)⟩
  refine ⟨h, g, ⟨Ψ.symm.continuous.comp_continuousOn cD.hc,
    cD.gc.comp Ψ.continuous.continuousOn hΨ_maps,
    hΨsymm_maps.comp cD.hm, cD.gm.comp hΨ_maps,
    fun x hx => by change g' (Ψ (Ψ.symm (h' x))) = x; rw [Ψ.apply_symm_apply, cD.gh hx],
    h_left, ?_⟩, hg_w⟩
  rw [← hg_sph, (h_left.mono sphere_subset_closedBall).image_image]

/-- For any chart `c : IsChart Δ h g`, `g '' ball (0 : ℂ) 1 = Δ \ discBd Δ`. -/
theorem IsChart.g_ball {Δ : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart Δ h g) :
    g '' ball (0 : ℂ) 1 = Δ \ discBd Δ := by
  have hball_eq : ball (0 : ℂ) 1 = closedBall (0 : ℂ) 1 \ sphere (0 : ℂ) 1 := by
    ext z
    simp only [mem_ball_zero_iff, mem_sdiff, mem_closedBall_zero_iff, mem_sphere_zero_iff_norm,
      lt_iff_le_and_ne]
  rw [hball_eq, c.g_sdiff Subset.rfl sphere_subset_closedBall, c.g_closedBall, c.g_sphere]

end DiscChartWithBd

/-! ## 3. Lifting `IsListedInOrderOn` Along a Fixed Circle Homeomorphism -/

section LiftOrder

variable {S : Type w} [TopologicalSpace S]

/-- If `Circle.exp x = Circle.exp y`, then `x - y = k * (2 * Real.pi)` for some `k : ℤ`. -/
theorem circle_exp_eq_iff_sub_eq_int_mul {x y : ℝ} :
    Circle.exp x = Circle.exp y ↔ ∃ k : ℤ, x - y = k * (2 * Real.pi) := by
  have hpi : 2 * Real.pi ≠ 0 := by positivity
  have hx : Circle.exp x = ee (x / (2 * Real.pi)) := by
    unfold ee
    rw [mul_div_cancel₀ _ hpi]
  have hy : Circle.exp y = ee (y / (2 * Real.pi)) := by
    unfold ee
    rw [mul_div_cancel₀ _ hpi]
  rw [hx, hy, ee_eq_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have := congrArg (· * (2 * Real.pi)) hk
    change (x / (2 * Real.pi)) * (2 * Real.pi) = (y / (2 * Real.pi) + k) * (2 * Real.pi) at this
    rw [div_mul_cancel₀ _ hpi, add_mul, div_mul_cancel₀ _ hpi] at this
    linarith
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    have hx_eq : x = y + k * (2 * Real.pi) := by linarith
    rw [hx_eq, add_div, mul_div_cancel_right₀ _ hpi]

/-- Two angles in `[θ₀, θ₀ + 2π)` with the same `Circle.exp` are equal. -/
theorem eq_of_circle_exp_eq_of_mem_Ico {θ₀ x y : ℝ}
    (hx : x ∈ Ico θ₀ (θ₀ + 2 * Real.pi)) (hy : y ∈ Ico θ₀ (θ₀ + 2 * Real.pi))
    (h : Circle.exp x = Circle.exp y) : x = y := by
  obtain ⟨k, hk⟩ := circle_exp_eq_iff_sub_eq_int_mul.mp h
  have hpi : 0 < 2 * Real.pi := by positivity
  have hk_gt : (-1 : ℝ) * (2 * Real.pi) < k * (2 * Real.pi) := by linarith [hx.1, hy.2]
  have hk_lt : (k : ℝ) * (2 * Real.pi) < 1 * (2 * Real.pi) := by linarith [hx.2, hy.1]
  have hk1 : (-1 : ℝ) < k := lt_of_mul_lt_mul_right hk_gt hpi.le
  have hk2 : (k : ℝ) < 1 := lt_of_mul_lt_mul_right hk_lt hpi.le
  have hk0 : k = 0 := by
    exact_mod_cast (by omega : -1 < k ∧ k < 1 → k = 0) ⟨by exact_mod_cast hk1, by exact_mod_cast
      hk2⟩
  subst hk0
  norm_num at hk
  linarith

private theorem angle_lt_full_turn_of_injective_lift
    {θ₀ : ℝ}
    {θ₁ : ℝ}
    {θ₂ : ℝ}
    (hθ₀₁ : θ₀ < θ₁)
    (hθ₁₂ : θ₁ < θ₂)
    (hθ₂_bd : θ₂ < θ₀ + 2 * Real.pi)
    (Γ_R : ℝ → ℝ)
    (hΓ_R_cont : ContinuousOn Γ_R (Icc 0 1))
    (hΓ_R_0 : Γ_R 0 = θ₀)
    (hΓ_R_inj_exp : InjOn (fun u => Circle.exp (Γ_R u)) (Ico 0 1)) :
    ∀ u ∈ Ico 0 1, Γ_R u < θ₀ + 2 * Real.pi := by
  intro u hu
  by_contra hge
  push Not at hge
  have hu_pos : 0 < u := by
    rcases eq_or_lt_of_le hu.1 with rfl | hpos
    · rw [hΓ_R_0] at hge
      linarith
    · exact hpos
  obtain ⟨v, hv_Icc, hv_eq⟩ := intermediate_value_Icc hu.1
    (hΓ_R_cont.mono (Icc_subset_Icc_right hu.2.le))
    ⟨by rw [hΓ_R_0]; linarith, hge⟩
  have hv_Ico : v ∈ Ico (0 : ℝ) 1 := ⟨hv_Icc.1, hv_Icc.2.trans_lt hu.2⟩
  have hv_exp : Circle.exp (Γ_R v) = Circle.exp (Γ_R 0) := by
    rw [hv_eq, hΓ_R_0, Circle.exp_add, Circle.exp_two_pi, mul_one]
  have hv0 : v = 0 := hΓ_R_inj_exp hv_Ico ⟨le_rfl, zero_lt_one⟩ hv_exp
  subst hv0
  rw [hΓ_R_0] at hv_eq
  linarith

/-- Given a fixed circle homeomorphism `g_circ : Circle ≃ₜ C` and a list `l : List S` with
`GM12.IsListedInOrderOn C l` whose elements at indices `0`, `1`, and `idx₂` (`1 < idx₂ < l.length`)
match `g_circ (Circle.exp θ₀)`, `g_circ (Circle.exp θ₁)`, `g_circ (Circle.exp θ₂)` with
`θ₀ < θ₁ < θ₂ < θ₀ + 2π`, there exists a strictly increasing sequence `Θ : ℕ → ℝ` with
`Θ 0 = θ₀`, `Θ i < θ₀ + 2π` for `i < l.length`, and `(g_circ (Circle.exp (Θ i))).1 = l[i]`. -/
theorem exists_increasing_angles_of_isListedInOrderOn
    {C : Set S} (g_circ : Circle ≃ₜ C) {l : List S}
    (hl_ord : GM12.IsListedInOrderOn C l)
    {θ₀ θ₁ θ₂ : ℝ} {idx₂ : ℕ}
    (hidx₁ : 1 < idx₂) (hidx₂ : idx₂ < l.length)
    (hθ₀₁ : θ₀ < θ₁) (hθ₁₂ : θ₁ < θ₂) (hθ₂_bd : θ₂ < θ₀ + 2 * Real.pi)
    (hl0 : (g_circ (Circle.exp θ₀)).1 = l[0]'(by omega))
    (hl1 : (g_circ (Circle.exp θ₁)).1 = l[1]'(by omega))
    (hl2 : (g_circ (Circle.exp θ₂)).1 = l[idx₂]'hidx₂) :
    ∃ Θ : ℕ → ℝ,
      StrictMono Θ ∧
      Θ 0 = θ₀ ∧
      (∀ i < l.length, Θ i < θ₀ + 2 * Real.pi) ∧
      (∀ (i : ℕ) (hi : i < l.length), (g_circ (Circle.exp (Θ i))).1 = l[i]'hi) ∧
      (∀ (i : ℕ) (hi : i < l.length) (θ : ℝ),
        θ ∈ Ico θ₀ (θ₀ + 2 * Real.pi) → (g_circ (Circle.exp θ)).1 = l[i]'hi → Θ i = θ) := by
  have hpi : 0 < 2 * Real.pi := by positivity
  obtain ⟨f_l, t_l, ht_l_mono, ht_l_bd, ht_l_val⟩ := hl_ord
  let h_rel : Circle ≃ₜ Circle := f_l.trans g_circ.symm
  have hh_rel_val : ∀ (i : ℕ) (hi : i < l.length),
      (g_circ (h_rel (Circle.exp (t_l i)))).1 = l[i]'hi := by
    intro i hi
    change (g_circ (g_circ.symm (f_l (Circle.exp (t_l i))))).1 = l[i]'hi
    rw [Homeomorph.apply_symm_apply]
    exact ht_l_val i hi
  have hh_rel_eq : ∀ (i : ℕ) (hi : i < l.length) (θ : ℝ),
      (g_circ (Circle.exp θ)).1 = l[i]'hi → h_rel (Circle.exp (t_l i)) = Circle.exp θ := by
    intro i hi θ hθ
    apply g_circ.injective
    apply Subtype.ext
    rw [hh_rel_val i hi, hθ]
  let γ : C(unitInterval, Circle) :=
    ⟨fun u => h_rel (Circle.exp (t_l 0 + 2 * Real.pi * (u : ℝ))),
      h_rel.continuous.comp (Circle.exp.continuous.comp (by fun_prop))⟩
  have hγ0 : γ 0 = Circle.exp θ₀ := by
    change h_rel (Circle.exp (t_l 0 + 2 * Real.pi * 0)) = Circle.exp θ₀
    rw [mul_zero, add_zero]
    exact hh_rel_eq 0 (by omega) θ₀ hl0
  obtain ⟨Γ, hΓ_exp, hΓ0⟩ :=
    Circle.isCoveringMap_exp.exists_path_lifts γ θ₀ hγ0
  let P : ℝ → unitInterval := projIcc 0 1 zero_le_one
  let m : ℝ → ℝ := fun u => Γ (P u) / (2 * Real.pi)
  have hm_cont : ContinuousOn m (Icc 0 1) :=
    ((Γ.continuous.comp continuous_projIcc).div_const _).continuousOn
  have hm_ee : ∀ u ∈ Icc (0 : ℝ) 1, ee (m u) = h_rel (Circle.exp (t_l 0 + 2 * Real.pi * u)) := by
    intro u hu
    unfold ee m
    rw [mul_div_cancel₀ _ (ne_of_gt hpi)]
    have h1 := congrFun hΓ_exp (P u)
    change Circle.exp (Γ (P u)) = h_rel (Circle.exp (t_l 0 + 2 * Real.pi *
      (projIcc 0 1 zero_le_one u : ℝ))) at h1
    rw [projIcc_of_mem zero_le_one hu] at h1
    exact h1
  have hm_inj : InjOn (fun u => ee (m u)) (Ico 0 1) := by
    intro u₁ hu₁ u₂ hu₂ heq
    dsimp at heq
    rw [hm_ee u₁ ⟨hu₁.1, hu₁.2.le⟩, hm_ee u₂ ⟨hu₂.1, hu₂.2.le⟩] at heq
    have h_exp_eq := h_rel.injective heq
    have h_eq := eq_of_circle_exp_eq_of_mem_Ico (θ₀ := t_l 0)
      ⟨by nlinarith [hu₁.1], by nlinarith [hu₁.2]⟩
      ⟨by nlinarith [hu₂.1], by nlinarith [hu₂.2]⟩ h_exp_eq
    nlinarith
  let Γ_R : ℝ → ℝ := fun u => Γ (P u)
  have hΓ_R_cont : ContinuousOn Γ_R (Icc 0 1) :=
    (Γ.continuous.comp continuous_projIcc).continuousOn
  have hΓ_R_0 : Γ_R 0 = θ₀ := by
    have hP0 : P 0 = 0 := Subtype.ext (by simp [P])
    change Γ (P 0) = θ₀
    rw [hP0, hΓ0]
  have hΓ_R_exp : ∀ u ∈ Icc (0 : ℝ) 1,
      Circle.exp (Γ_R u) = h_rel (Circle.exp (t_l 0 + 2 * Real.pi * u)) := by
    intro u hu
    have h := hm_ee u hu
    unfold ee m at h
    rwa [mul_div_cancel₀ _ (ne_of_gt hpi)] at h
  have hΓ_R_inj_exp : InjOn (fun u => Circle.exp (Γ_R u)) (Ico 0 1) := by
    intro u₁ hu₁ u₂ hu₂ heq
    apply hm_inj hu₁ hu₂
    change Circle.exp (2 * Real.pi * (Γ_R u₁ / (2 * Real.pi))) =
      Circle.exp (2 * Real.pi * (Γ_R u₂ / (2 * Real.pi)))
    rw [mul_div_cancel₀ _ (ne_of_gt hpi), mul_div_cancel₀ _ (ne_of_gt hpi)]
    exact heq
  let u_idx : ℕ → ℝ := fun i => (t_l i - t_l 0) / (2 * Real.pi)
  have hu_idx_mono : StrictMono u_idx := by
    intro i j hij
    dsimp [u_idx]
    exact div_lt_div_of_pos_right (by linarith [ht_l_mono hij]) hpi
  have hu_idx_0 : u_idx 0 = 0 := by simp [u_idx]
  have hu_idx_mem : ∀ i < l.length, u_idx i ∈ Ico (0 : ℝ) 1 := by
    intro i hi
    refine ⟨?_, ?_⟩
    · rw [← hu_idx_0]
      exact hu_idx_mono.monotone (Nat.zero_le i)
    · dsimp [u_idx]
      rw [div_lt_one hpi]
      linarith [ht_l_bd i hi]
  have hΓ_R_u_idx : ∀ (i : ℕ) (hi : i < l.length),
      Circle.exp (Γ_R (u_idx i)) = h_rel (Circle.exp (t_l i)) := by
    intro i hi
    have hu := hu_idx_mem i hi
    rw [hΓ_R_exp (u_idx i) ⟨hu.1, hu.2.le⟩]
    congr 2
    dsimp [u_idx]
    rw [mul_div_cancel₀ _ (ne_of_gt hpi), add_sub_cancel]
  rcases lift_mono_loop hm_cont hm_inj with hm_mono | hm_anti
  · have hΓ_mono : StrictMonoOn Γ_R (Icc 0 1) := by
      intro x hx y hy hxy
      have := hm_mono hx hy hxy
      dsimp [m] at this
      exact (div_lt_div_iff_of_pos_right hpi).mp this
    have hΓ_lt_two_pi : ∀ u ∈ Ico (0 : ℝ) 1, Γ_R u < θ₀ + 2 * Real.pi := by
      exact angle_lt_full_turn_of_injective_lift (θ₀ := θ₀) (θ₁ := θ₁) (θ₂ := θ₂) hθ₀₁ hθ₁₂ hθ₂_bd
        Γ_R hΓ_R_cont hΓ_R_0 hΓ_R_inj_exp
    have hΓ_mem_Ico : ∀ u ∈ Ico (0 : ℝ) 1, Γ_R u ∈ Ico θ₀ (θ₀ + 2 * Real.pi) := by
      intro u hu
      refine ⟨?_, hΓ_lt_two_pi u hu⟩
      rw [← hΓ_R_0]
      exact hΓ_mono.monotoneOn ⟨le_rfl, zero_le_one⟩ ⟨hu.1, hu.2.le⟩ hu.1
    let Θ : ℕ → ℝ := fun i =>
      if i < l.length then Γ_R (u_idx i) else θ₀ + 2 * Real.pi + (i - l.length : ℕ)
    have hΘ_mono : StrictMono Θ := by
      intro i j hij
      dsimp [Θ]
      by_cases hj : j < l.length
      · have hi : i < l.length := hij.trans hj
        simp only [hi, hj, ↓reduceIte]
        have hui := hu_idx_mem i hi
        have huj := hu_idx_mem j hj
        exact hΓ_mono ⟨hui.1, hui.2.le⟩ ⟨huj.1, huj.2.le⟩ (hu_idx_mono hij)
      · by_cases hi : i < l.length
        · simp only [hi, hj, ↓reduceIte]
          have hlt := (hΓ_mem_Ico (u_idx i) (hu_idx_mem i hi)).2
          have hge : (0 : ℝ) ≤ (j - l.length : ℕ) := Nat.cast_nonneg _
          linarith
        · simp only [hi, hj, ↓reduceIte]
          have hsub : i - l.length < j - l.length := by omega
          have hcast : ((i - l.length : ℕ) : ℝ) < ((j - l.length : ℕ) : ℝ) :=
            Nat.cast_lt.mpr hsub
          linarith
    have hΘ_0 : Θ 0 = θ₀ := by
      dsimp [Θ]
      have h0 : 0 < l.length := by omega
      simp only [h0, ↓reduceIte, hu_idx_0, hΓ_R_0]
    have hΘ_bd : ∀ i < l.length, Θ i < θ₀ + 2 * Real.pi := by
      intro i hi
      dsimp [Θ]
      simp only [hi, ↓reduceIte]
      exact (hΓ_mem_Ico (u_idx i) (hu_idx_mem i hi)).2
    have hΘ_val : ∀ (i : ℕ) (hi : i < l.length), (g_circ (Circle.exp (Θ i))).1 = l[i]'hi := by
      intro i hi
      dsimp [Θ]
      simp only [hi, ↓reduceIte]
      rw [hΓ_R_u_idx i hi]
      exact hh_rel_val i hi
    refine ⟨Θ, hΘ_mono, hΘ_0, hΘ_bd, hΘ_val, ?_⟩
    intro i hi θ hθ hval
    have hΘ_mem : Θ i ∈ Ico θ₀ (θ₀ + 2 * Real.pi) := by
      dsimp [Θ]
      simp only [hi, ↓reduceIte]
      exact hΓ_mem_Ico (u_idx i) (hu_idx_mem i hi)
    have h_exp : Circle.exp (Θ i) = Circle.exp θ := by
      apply g_circ.injective
      apply Subtype.ext
      rw [hΘ_val i hi, hval]
    exact eq_of_circle_exp_eq_of_mem_Ico hΘ_mem hθ h_exp
  · exfalso
    have hΓ_anti : StrictAntiOn Γ_R (Icc 0 1) := by
      intro x hx y hy hxy
      have := hm_anti hx hy hxy
      dsimp [m] at this
      exact (div_lt_div_iff_of_pos_right hpi).mp this
    have hΓ_gt_sub : ∀ u ∈ Ico (0 : ℝ) 1, θ₀ - 2 * Real.pi < Γ_R u := by
      intro u hu
      by_contra hle
      push Not at hle
      obtain ⟨v, hv_Icc, hv_eq⟩ := intermediate_value_Icc' hu.1
        (hΓ_R_cont.mono (Icc_subset_Icc_right hu.2.le))
        ⟨hle, by rw [hΓ_R_0]; linarith⟩
      have hv_Ico : v ∈ Ico (0 : ℝ) 1 := ⟨hv_Icc.1, hv_Icc.2.trans_lt hu.2⟩
      have hv_exp : Circle.exp (Γ_R v) = Circle.exp (Γ_R 0) := by
        rw [hv_eq, hΓ_R_0, sub_eq_add_neg, Circle.exp_add, Circle.exp_neg,
          Circle.exp_two_pi, inv_one, mul_one]
      have hv0 : v = 0 := hΓ_R_inj_exp hv_Ico ⟨le_rfl, zero_lt_one⟩ hv_exp
      subst hv0
      rw [hΓ_R_0] at hv_eq
      linarith
    have hΓ_mem_Ico : ∀ u ∈ Ioo (0 : ℝ) 1,
        Γ_R u ∈ Ico (θ₀ - 2 * Real.pi) (θ₀ - 2 * Real.pi + 2 * Real.pi) := by
      intro u hu
      refine ⟨(hΓ_gt_sub u ⟨hu.1.le, hu.2⟩).le, ?_⟩
      rw [sub_add_cancel, ← hΓ_R_0]
      exact hΓ_anti ⟨le_rfl, zero_le_one⟩ ⟨hu.1.le, hu.2.le⟩ hu.1
    have hu1_Ioo : u_idx 1 ∈ Ioo (0 : ℝ) 1 :=
      ⟨hu_idx_0 ▸ hu_idx_mono Nat.zero_lt_one, (hu_idx_mem 1 (by omega)).2⟩
    have hu2_Ioo : u_idx idx₂ ∈ Ioo (0 : ℝ) 1 :=
      ⟨hu_idx_0 ▸ hu_idx_mono (by omega), (hu_idx_mem idx₂ hidx₂).2⟩
    have hΓ_u1 : Γ_R (u_idx 1) = θ₁ - 2 * Real.pi := by
      apply eq_of_circle_exp_eq_of_mem_Ico (hΓ_mem_Ico (u_idx 1) hu1_Ioo)
        ⟨by linarith, by linarith⟩
      rw [hΓ_R_u_idx 1 (by omega), hh_rel_eq 1 (by omega) θ₁ hl1,
        sub_eq_add_neg, Circle.exp_add, Circle.exp_neg, Circle.exp_two_pi, inv_one, mul_one]
    have hΓ_u2 : Γ_R (u_idx idx₂) = θ₂ - 2 * Real.pi := by
      apply eq_of_circle_exp_eq_of_mem_Ico (hΓ_mem_Ico (u_idx idx₂) hu2_Ioo)
        ⟨by linarith, by linarith⟩
      rw [hΓ_R_u_idx idx₂ hidx₂, hh_rel_eq idx₂ hidx₂ θ₂ hl2,
        sub_eq_add_neg, Circle.exp_add, Circle.exp_neg, Circle.exp_two_pi, inv_one, mul_one]
    have hlt_anti : Γ_R (u_idx idx₂) < Γ_R (u_idx 1) :=
      hΓ_anti ⟨hu1_Ioo.1.le, hu1_Ioo.2.le⟩ ⟨hu2_Ioo.1.le, hu2_Ioo.2.le⟩ (hu_idx_mono hidx₁)
    linarith

end LiftOrder

/-! ## 4. Angles, Vertical Chords, and Open Caps in `closedBall (0 : ℂ) 1` -/

section PlaneChordsAndCaps

/-- Model angle `π * ((m + 1) / k)` for the `2k` vertices on `subBd Λ` in XV (3.4). -/
noncomputable def parallelModelAngle (k m : ℕ) : ℝ :=
  Real.pi * ((m + 1 : ℝ) / (k : ℝ))

theorem strictMono_parallelModelAngle {k : ℕ} (hk : 1 ≤ k) :
    StrictMono (parallelModelAngle k) := by
  intro m₁ m₂ hm
  unfold parallelModelAngle
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hm_lt : (m₁ + 1 : ℝ) < (m₂ + 1 : ℝ) := by exact_mod_cast Nat.add_lt_add_right hm 1
  exact mul_lt_mul_of_pos_left (div_lt_div_of_pos_right hm_lt hk_pos) Real.pi_pos

theorem parallelModelAngle_lt_add_two_pi {k : ℕ} (hk : 1 ≤ k) :
    ∀ m < 2 * k, parallelModelAngle k m < parallelModelAngle k 0 + 2 * Real.pi := by
  intro m hm
  unfold parallelModelAngle
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  have hm_le : (m + 1 : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hm
  have hdiv : (m + 1 : ℝ) / (k : ℝ) ≤ 2 := (div_le_iff₀ hk_pos).mpr hm_le
  have h0 : (0 : ℝ) < Real.pi * ((0 + 1 : ℝ) / (k : ℝ)) := by positivity
  nlinarith [Real.pi_pos]

theorem parallelModelAngle_mem_Ioo_pi {k : ℕ} {j : ℕ} (hj : j < k - 1) :
    0 < parallelModelAngle k j ∧ parallelModelAngle k j < Real.pi := by
  have hk : 1 ≤ k := by omega
  have hk_pos : (0 : ℝ) < k := Nat.cast_pos.mpr hk
  unfold parallelModelAngle
  refine ⟨by positivity, ?_⟩
  have hj_lt : (j + 1 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : j + 1 < k)
  have hdiv : (j + 1 : ℝ) / (k : ℝ) < 1 := (div_lt_one hk_pos).mpr hj_lt
  nlinarith [Real.pi_pos]

theorem parallelModelAngle_partner {k : ℕ} {j : ℕ} (hj : j < k - 1) :
    parallelModelAngle k (2 * k - 2 - j) = 2 * Real.pi - parallelModelAngle k j := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold parallelModelAngle
  have hcast : ((2 * k - 2 - j : ℕ) : ℝ) + 1 = 2 * (k : ℝ) - ((j : ℝ) + 1) := by
    have h1 : (2 * k - 2 - j) + 1 = 2 * k - (j + 1) := by omega
    have h1' : ((2 * k - 2 - j : ℕ) : ℝ) + 1 = ((2 * k - (j + 1) : ℕ) : ℝ) := by
      exact_mod_cast h1
    have h2 : j + 1 ≤ 2 * k := by omega
    rw [h1', Nat.cast_sub h2]
    push_cast
    ring
  rw [hcast, sub_div, mul_div_cancel_right₀ 2 hk_ne, mul_sub]
  ring

theorem parallelModelAngle_k_sub_one {k : ℕ} (hk : 1 ≤ k) :
    parallelModelAngle k (k - 1) = Real.pi := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold parallelModelAngle
  have hcast : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by exact_mod_cast Nat.sub_add_cancel hk
  rw [hcast, div_self hk_ne, mul_one]

theorem parallelModelAngle_two_k_sub_one {k : ℕ} (hk : 1 ≤ k) :
    parallelModelAngle k (2 * k - 1) = 2 * Real.pi := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  unfold parallelModelAngle
  have hcast : ((2 * k - 1 : ℕ) : ℝ) + 1 = 2 * (k : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (by omega : 1 ≤ 2 * k)
  rw [hcast, mul_div_cancel_right₀ 2 hk_ne]
  ring

/-- Horizontal coordinate `x_j = cos(π(j+1)/k)` of the `j`-th vertical chord. -/
noncomputable def parallelX (k : ℕ) (j : Fin (k - 1)) : ℝ :=
  Real.cos (parallelModelAngle k j.1)

/-- Vertical half-height `y_j = sin(π(j+1)/k)` of the `j`-th vertical chord. -/
noncomputable def parallelY (k : ℕ) (j : Fin (k - 1)) : ℝ :=
  Real.sin (parallelModelAngle k j.1)

theorem parallelY_pos {k : ℕ} (j : Fin (k - 1)) : 0 < parallelY k j := by
  obtain ⟨h0, hpi⟩ := parallelModelAngle_mem_Ioo_pi j.2
  exact Real.sin_pos_of_pos_of_lt_pi h0 hpi

theorem parallelX_sq_add_parallelY_sq {k : ℕ} (j : Fin (k - 1)) :
    parallelX k j ^ 2 + parallelY k j ^ 2 = 1 :=
  Real.cos_sq_add_sin_sq (parallelModelAngle k j.1)

theorem parallelX_mem_Ioo {k : ℕ} (j : Fin (k - 1)) :
    -1 < parallelX k j ∧ parallelX k j < 1 := by
  have hy : 0 < parallelY k j := parallelY_pos j
  have hsq : parallelX k j ^ 2 < 1 := by
    nlinarith [parallelX_sq_add_parallelY_sq j]
  exact ⟨by nlinarith, by nlinarith⟩

theorem strictAnti_parallelX {k : ℕ} (hk : 1 ≤ k) :
    StrictAnti (parallelX k) := by
  intro j₁ j₂ hj
  obtain ⟨h0₁, hpi₁⟩ := parallelModelAngle_mem_Ioo_pi j₁.2
  obtain ⟨h0₂, hpi₂⟩ := parallelModelAngle_mem_Ioo_pi j₂.2
  exact Real.strictAntiOn_cos ⟨h0₁.le, hpi₁.le⟩ ⟨h0₂.le, hpi₂.le⟩
    (strictMono_parallelModelAngle hk hj)

theorem circle_exp_coe_eq_mk (θ : ℝ) :
    (Circle.exp θ : ℂ) = ⟨Real.cos θ, Real.sin θ⟩ := by
  apply Complex.ext
  · simp [Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  · simp [Circle.coe_exp, Complex.exp_ofReal_mul_I_im]

theorem circle_exp_parallelModelAngle_top {k : ℕ} (j : Fin (k - 1)) :
    (Circle.exp (parallelModelAngle k j.1) : ℂ) = ⟨parallelX k j, parallelY k j⟩ :=
  circle_exp_coe_eq_mk (parallelModelAngle k j.1)

theorem circle_exp_parallelModelAngle_bot {k : ℕ} (j : Fin (k - 1)) :
    (Circle.exp (parallelModelAngle k (2 * k - 2 - j.1)) : ℂ) =
      ⟨parallelX k j, -parallelY k j⟩ := by
  rw [parallelModelAngle_partner j.2, circle_exp_coe_eq_mk]
  unfold parallelX parallelY
  have hsub : 2 * Real.pi - parallelModelAngle k j.1 =
      -(parallelModelAngle k j.1 - 2 * Real.pi) := by ring
  congr 1
  · rw [hsub, Real.cos_neg, Real.cos_sub_two_pi]
  · rw [hsub, Real.sin_neg, Real.sin_sub_two_pi]

theorem circle_exp_parallelModelAngle_k_sub_one {k : ℕ} (hk : 1 ≤ k) :
    (Circle.exp (parallelModelAngle k (k - 1)) : ℂ) = ⟨-1, 0⟩ := by
  rw [parallelModelAngle_k_sub_one hk, circle_exp_coe_eq_mk, Real.cos_pi, Real.sin_pi]

theorem circle_exp_parallelModelAngle_two_k_sub_one {k : ℕ} (hk : 1 ≤ k) :
    (Circle.exp (parallelModelAngle k (2 * k - 1)) : ℂ) = ⟨1, 0⟩ := by
  rw [parallelModelAngle_two_k_sub_one hk, circle_exp_coe_eq_mk, Real.cos_two_pi, Real.sin_two_pi]

theorem mem_closedBall_unit_iff (z : ℂ) :
    z ∈ closedBall (0 : ℂ) 1 ↔ z.re ^ 2 + z.im ^ 2 ≤ 1 := by
  rw [mem_closedBall_zero_iff]
  have h1 : ‖z‖ ≤ 1 ↔ ‖z‖ ^ 2 ≤ 1 := by
    constructor
    · intro h; nlinarith [norm_nonneg z]
    · intro h; nlinarith [norm_nonneg z]
  rw [h1, Complex.sq_norm, Complex.normSq_apply]
  ring_nf

theorem mem_ball_unit_iff (z : ℂ) :
    z ∈ ball (0 : ℂ) 1 ↔ z.re ^ 2 + z.im ^ 2 < 1 := by
  rw [mem_ball_zero_iff]
  have h1 : ‖z‖ < 1 ↔ ‖z‖ ^ 2 < 1 := by
    constructor
    · intro h; nlinarith [norm_nonneg z]
    · intro h; nlinarith [norm_nonneg z]
  rw [h1, Complex.sq_norm, Complex.normSq_apply]
  ring_nf

theorem mem_sphere_unit_iff (z : ℂ) :
    z ∈ sphere (0 : ℂ) 1 ↔ z.re ^ 2 + z.im ^ 2 = 1 := by
  rw [mem_sphere_zero_iff_norm]
  have h1 : ‖z‖ = 1 ↔ ‖z‖ ^ 2 = 1 := by
    constructor
    · intro h; rw [h]; ring
    · intro h; nlinarith [norm_nonneg z]
  rw [h1, Complex.sq_norm, Complex.normSq_apply]
  ring_nf

/-- Vertical chord `{z ∈ closedBall 0 1 | z.re = r}` in the closed unit disc of `ℂ`. -/
def vertChord (r : ℝ) : Set ℂ :=
  {z ∈ closedBall (0 : ℂ) 1 | z.re = r}

/-- Linear parametrization `t ↦ ⟨r, (1 - 2t)y⟩` of `vertChord r` from `⟨r, y⟩` to `⟨r, -y⟩`. -/
def vertChordMap (r y : ℝ) (t : unitInterval) : ℂ :=
  ⟨r, (1 - 2 * (t : ℝ)) * y⟩

theorem continuous_vertChordMap (r y : ℝ) : Continuous (vertChordMap r y) := by
  have h_eq : vertChordMap r y = fun t : unitInterval => (r : ℂ) + (((1 - 2 *
    (t : ℝ)) * y : ℝ) : ℂ) * Complex.I := by
    ext t
    apply Complex.ext <;> simp [vertChordMap]
  rw [h_eq]
  fun_prop

theorem injective_vertChordMap {r y : ℝ} (hy : 0 < y) :
    Function.Injective (vertChordMap r y) := by
  intro t₁ t₂ h
  have him : (vertChordMap r y t₁).im = (vertChordMap r y t₂).im := congrArg Complex.im h
  dsimp [vertChordMap] at him
  apply Subtype.ext
  nlinarith

theorem range_vertChordMap {r y : ℝ} (hry : r ^ 2 + y ^ 2 = 1) (hy : 0 < y) :
    range (vertChordMap r y) = vertChord r := by
  ext z
  simp only [mem_range, vertChord, mem_ofPred_eq, mem_closedBall_unit_iff]
  constructor
  · rintro ⟨t, rfl⟩
    dsimp [vertChordMap]
    refine ⟨?_, rfl⟩
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    have h_abs : (1 - 2 * (t : ℝ)) ^ 2 ≤ 1 := by nlinarith
    nlinarith
  · rintro ⟨h_le, rfl⟩
    have him_sq : z.im ^ 2 ≤ y ^ 2 := by linarith
    have him_bounds : -y ≤ z.im ∧ z.im ≤ y := by
      constructor <;> nlinarith
    let s : ℝ := (1 - z.im / y) / 2
    have hs_mem : s ∈ Icc (0 : ℝ) 1 := by
      dsimp [s]
      have h1 : -1 ≤ z.im / y := (le_div_iff₀ hy).mpr (by linarith)
      have h2 : z.im / y ≤ 1 := (div_le_iff₀ hy).mpr (by linarith)
      exact ⟨by linarith, by linarith⟩
    refine ⟨⟨s, hs_mem⟩, ?_⟩
    apply Complex.ext
    · rfl
    · dsimp [vertChordMap, s]
      have hy_ne : y ≠ 0 := ne_of_gt hy
      field_simp
      ring

theorem vertChord_inter_sphere {r y : ℝ} (hry : r ^ 2 + y ^ 2 = 1) :
    vertChord r ∩ sphere (0 : ℂ) 1 = {⟨r, y⟩, ⟨r, -y⟩} := by
  ext z
  simp only [mem_inter_iff, vertChord, mem_ofPred_eq, mem_closedBall_unit_iff,
    mem_sphere_unit_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨_, rfl⟩, h_eq⟩
    have him_sq : z.im ^ 2 = y ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp him_sq with him | him
    · left; exact Complex.ext rfl him
    · right; exact Complex.ext rfl him
  · rintro (rfl | rfl)
    · exact ⟨⟨by linarith, rfl⟩, by linarith⟩
    · exact ⟨⟨by linarith, rfl⟩, by linarith⟩

theorem vertChord_disjoint {r₁ r₂ : ℝ} (hne : r₁ ≠ r₂) :
    Disjoint (vertChord r₁) (vertChord r₂) :=
  Set.disjoint_left.mpr fun _ hz₁ hz₂ => hne (hz₁.2.symm.trans hz₂.2)

/-- Image of `vertChord r` under a disc chart `c : IsChart Δ h g` is a line with ends
`g ⟨r, y⟩` and `g ⟨r, -y⟩` meeting `discBd Δ` only at its ends. -/
theorem isLineWithEnds_image_vertChord {S : Type w} [TopologicalSpace S] [T2Space S]
    {Δ : Set S} {h : S → ℂ} {g : ℂ → S} (c : IsChart Δ h g)
    {r y : ℝ} (hry : r ^ 2 + y ^ 2 = 1) (hy : 0 < y) :
    IsLineWithEnds (g '' vertChord r) (g ⟨r, y⟩) (g ⟨r, -y⟩) ∧
      g '' vertChord r ⊆ Δ ∧
      (g '' vertChord r) ∩ discBd Δ = {g ⟨r, y⟩, g ⟨r, -y⟩} := by
  have hsub_cb : vertChord r ⊆ closedBall (0 : ℂ) 1 := fun _ hz => hz.1
  have hmap_cb : ∀ t : unitInterval, vertChordMap r y t ∈ closedBall (0 : ℂ) 1 := by
    intro t
    apply hsub_cb
    rw [← range_vertChordMap hry hy]
    exact ⟨t, rfl⟩
  let γ : unitInterval → S := fun t => g (vertChordMap r y t)
  have hγ_cont : Continuous γ :=
    c.gc.comp_continuous (continuous_vertChordMap r y) hmap_cb
  have hγ_inj : Function.Injective γ := by
    intro t₁ t₂ heq
    exact injective_vertChordMap hy (c.injOn (hmap_cb t₁) (hmap_cb t₂) heq)
  have hγ_range : range γ = g '' vertChord r := by
    rw [← range_vertChordMap hry hy, ← range_comp]
    rfl
  have hγ0 : γ 0 = g ⟨r, y⟩ := by
    change g (vertChordMap r y 0) = g ⟨r, y⟩
    congr 1
    apply Complex.ext <;> simp [vertChordMap]
  have hγ1 : γ 1 = g ⟨r, -y⟩ := by
    change g (vertChordMap r y 1) = g ⟨r, -y⟩
    congr 1
    apply Complex.ext <;> simp [vertChordMap]
    ring
  have hLine : IsLineWithEnds (g '' vertChord r) (g ⟨r, y⟩) (g ⟨r, -y⟩) := by
    rw [← hγ_range, ← hγ0, ← hγ1]
    exact GM11.isLine_range hγ_cont hγ_inj
  have hinter : (g '' vertChord r) ∩ discBd Δ = {g ⟨r, y⟩, g ⟨r, -y⟩} := by
    rw [← c.g_sphere, ← c.g_inter hsub_cb sphere_subset_closedBall,
      vertChord_inter_sphere hry, image_pair]
  exact ⟨hLine, c.g_subset hsub_cb, hinter⟩

/-! ## 5. Open and Closed Caps, Boundary O-Arcs, and Pinched Vertical Homeomorphism -/

/-- If `C : Drawing S` has `C.U = range a ∪ range b` for two arcs `a, b : unitInterval → S` with
common
endpoints meeting only at `{0, 1}`, then `IsOArc C.U`, and for any `s₁ < s₂ < s₃ < s₄` in
`unitInterval`, `OccurInCircuitOrder C (a s₁) (a s₂) (a s₃) (a s₄)`. -/
theorem oArc_and_occurInCircuitOrder_of_two_arcs {S : Type w} [TopologicalSpace S] [T2Space S]
    {a b : unitInterval → S} (ha : IsArcMap a) (hb : IsArcMap b)
    (h0 : a 0 = b 0) (h1 : a 1 = b 1)
    (h01 : ∀ s t, a s = b t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1)) :
    IsOArc (range a ∪ range b) ∧
      ∀ {C : Drawing S}, C.U = range a ∪ range b →
        ∀ {s₁ s₂ s₃ s₄ : unitInterval},
        s₁ < s₂ → s₂ < s₃ → s₃ < s₄ →
        OccurInCircuitOrder C (a s₁) (a s₂) (a s₃) (a s₄) := by
  classical
  have hbd : ∀ w : Circle, |(w : ℂ).re| ≤ 1 := fun w => by
    have := Complex.abs_re_le_norm (w : ℂ)
    rwa [Circle.norm_coe] at this
  let τ : Circle → unitInterval := fun w => ⟨(1 - (w : ℂ).re) / 2, by
    have := abs_le.mp (hbd w)
    constructor <;> linarith [this.1, this.2]⟩
  have hτ : Continuous τ := by
    refine Continuous.subtype_mk ?_ _
    have : Continuous fun w : Circle => (w : ℂ) := continuous_subtype_val
    exact ((continuous_const.sub (Complex.continuous_re.comp this)).div_const 2)
  let g_loop : Circle → S := fun w => if 0 ≤ (w : ℂ).im then a (τ w) else b (τ w)
  have him : Continuous fun w : Circle => (w : ℂ).im :=
    Complex.continuous_im.comp continuous_subtype_val
  have hsq : ∀ w : Circle, (w : ℂ).re * (w : ℂ).re + (w : ℂ).im * (w : ℂ).im = 1 := fun w => by
    have h := Complex.sq_norm (w : ℂ)
    rw [Circle.norm_coe, Complex.normSq_apply] at h
    linarith
  have hτ0 : ∀ w : Circle, (w : ℂ).im = 0 → τ w = 0 ∨ τ w = 1 := by
    intro w hw
    have h := hsq w
    rw [hw] at h
    have hfac : ((w : ℂ).re - 1) * ((w : ℂ).re + 1) = 0 := by linarith
    rcases mul_eq_zero.mp hfac with h_eq | h_eq
    · left
      refine Subtype.ext ?_
      change (1 - (w : ℂ).re) / 2 = 0
      rw [sub_eq_zero.mp h_eq]
      norm_num
    · right
      refine Subtype.ext ?_
      change (1 - (w : ℂ).re) / 2 = 1
      rw [eq_neg_of_add_eq_zero_left h_eq]
      norm_num
  have hg_cont : Continuous g_loop := by
    refine Continuous.if_le (ha.1.comp hτ) (hb.1.comp hτ) continuous_const him ?_
    intro w hw
    rcases hτ0 w hw.symm with h_eq | h_eq
    · simp only [h_eq, h0]
    · simp only [h_eq, h1]
  have hre : ∀ {w w' : Circle}, τ w = τ w' → (w : ℂ).re = (w' : ℂ).re := fun {w w'} h => by
    have : (1 - (w : ℂ).re) / 2 = (1 - (w' : ℂ).re) / 2 := congrArg Subtype.val h
    linarith
  have hsame : ∀ {w w' : Circle}, τ w = τ w' → 0 ≤ (w : ℂ).im → 0 ≤ (w' : ℂ).im → w = w' := by
    intro w w' h h_im1 h_im2
    have h3 := hre h
    have h4 := hsq w
    have h5 := hsq w'
    rw [h3] at h4
    have h6 : (w : ℂ).im = (w' : ℂ).im := by nlinarith [mul_self_nonneg ((w : ℂ).im - (w' : ℂ).im)]
    exact Circle.ext (Complex.ext h3 h6)
  have hsameneg : ∀ {w w' : Circle}, τ w = τ w' → (w : ℂ).im < 0 → (w' : ℂ).im < 0 → w = w' := by
    intro w w' h h_im1 h_im2
    have h3 := hre h
    have h4 := hsq w
    have h5 := hsq w'
    rw [h3] at h4
    have h6 : (w : ℂ).im = (w' : ℂ).im := by nlinarith [mul_self_nonneg ((w : ℂ).im - (w' : ℂ).im)]
    exact Circle.ext (Complex.ext h3 h6)
  have him0 : ∀ {w : Circle}, τ w = 0 ∨ τ w = 1 → (w : ℂ).im = 0 := by
    intro w h
    have h4 := hsq w
    have hre1 : (w : ℂ).re = 1 ∨ (w : ℂ).re = -1 := by
      rcases h with h | h
      · left; have : (1 - (w : ℂ).re) / 2 = 0 := congrArg Subtype.val h; linarith
      · right; have : (1 - (w : ℂ).re) / 2 = 1 := congrArg Subtype.val h; linarith
    rcases hre1 with h_eq | h_eq <;> rw [h_eq] at h4 <;> nlinarith [mul_self_nonneg (w : ℂ).im]
  have hmixed : ∀ {w w' : Circle}, 0 ≤ (w : ℂ).im → (w' : ℂ).im < 0 → a (τ w) = b (τ w') → False
    := by
    intro w w' h_im1 h_im2 h
    rcases h01 _ _ h with ⟨_, h3⟩ | ⟨_, h3⟩
    · exact absurd (him0 (Or.inl h3)) h_im2.ne
    · exact absurd (him0 (Or.inr h3)) h_im2.ne
  have hg_inj : Function.Injective g_loop := by
    intro w w' h
    simp only [g_loop] at h
    split_ifs at h with h_im1 h_im2 h_im2
    · exact hsame (ha.2 h) h_im1 h_im2
    · exact (hmixed h_im1 (not_le.mp h_im2) h).elim
    · exact (hmixed h_im2 (not_le.mp h_im1) h.symm).elim
    · exact hsameneg (hb.2 h) (not_le.mp h_im1) (not_le.mp h_im2)
  have hg_range : range g_loop = range a ∪ range b := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      simp only [g_loop]
      split_ifs
      · exact Or.inl ⟨τ w, rfl⟩
      · exact Or.inr ⟨τ w, rfl⟩
    · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · have ht : |(1 - 2 * (t : ℝ))| ≤ 1 := abs_le.mpr ⟨by linarith [t.2.2], by linarith [t.2.1]⟩
        let y := Real.sqrt (1 - (1 - 2 * (t : ℝ)) ^ 2)
        have hy : 0 ≤ y := Real.sqrt_nonneg _
        have hsq' : (1 - 2 * (t : ℝ)) ^ 2 + y ^ 2 = 1 := by
          have : 0 ≤ 1 - (1 - 2 * (t : ℝ)) ^ 2 := by nlinarith [t.2.1, t.2.2]
          rw [Real.sq_sqrt this]; ring
        let w : Circle := ⟨⟨1 - 2 * (t : ℝ), y⟩, by
          change (⟨1 - 2 * (t : ℝ), y⟩ : ℂ) ∈ sphere (0 : ℂ) 1
          rw [mem_sphere_unit_iff]
          exact hsq'⟩
        have hτw : τ w = t := by apply Subtype.ext; change (1 - (1 - 2 * (t : ℝ))) / 2 = t; ring
        refine ⟨w, ?_⟩
        change (if 0 ≤ y then a (τ w) else b (τ w)) = a t
        split_ifs
        rw [hτw]
      · by_cases ht01 : t = 0 ∨ t = 1
        · rcases ht01 with rfl | rfl
          · refine ⟨1, ?_⟩
            have hτ1 : τ 1 = 0 := by apply Subtype.ext; simp [τ]
            have him1 : (0 : ℝ) ≤ ((1 : Circle) : ℂ).im := by simp
            change (if 0 ≤ ((1 : Circle) : ℂ).im then a (τ 1) else b (τ 1)) = b 0
            split_ifs
            rw [hτ1, h0]
          · refine ⟨-1, ?_⟩
            have hτ1 : τ (-1) = 1 := by apply Subtype.ext; simp [τ]
            have him1 : (0 : ℝ) ≤ ((-1 : Circle) : ℂ).im := by simp
            change (if 0 ≤ ((-1 : Circle) : ℂ).im then a (τ (-1)) else b (τ (-1))) = b 1
            split_ifs
            rw [hτ1, h1]
        · push Not at ht01
          have ht0 : 0 < (t : ℝ) := lt_of_le_of_ne t.2.1 (fun h => ht01.1 (Subtype.ext h.symm))
          have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (fun h => ht01.2 (Subtype.ext h))
          have hpos : 0 < 1 - (1 - 2 * (t : ℝ)) ^ 2 := by nlinarith
          let y := -Real.sqrt (1 - (1 - 2 * (t : ℝ)) ^ 2)
          have hy : y < 0 := neg_lt_zero.mpr (Real.sqrt_pos.mpr hpos)
          have hsq' : (1 - 2 * (t : ℝ)) ^ 2 + y ^ 2 = 1 := by
            dsimp [y]; rw [neg_sq, Real.sq_sqrt hpos.le]; ring
          let w : Circle := ⟨⟨1 - 2 * (t : ℝ), y⟩, by
            change (⟨1 - 2 * (t : ℝ), y⟩ : ℂ) ∈ sphere (0 : ℂ) 1
            rw [mem_sphere_unit_iff]
            exact hsq'⟩
          have hτw : τ w = t := by apply Subtype.ext; change (1 - (1 - 2 * (t : ℝ))) / 2 = t; ring
          refine ⟨w, ?_⟩
          change (if 0 ≤ y then a (τ w) else b (τ w)) = b t
          split_ifs with h_if
          · exact (not_le.mpr hy h_if).elim
          · rw [hτw]
  have hEmb : IsEmbedding g_loop := hg_cont.isClosedEmbedding hg_inj |>.isEmbedding
  have hOArc : IsOArc (range a ∪ range b) :=
    ⟨hEmb.toHomeomorph.trans (Homeomorph.setCongr hg_range)⟩
  refine ⟨hOArc, fun {C} hCU {s₁ s₂ s₃ s₄} hs12 hs23 hs34 => ?_⟩
  let φ : Circle ≃ₜ C.U :=
    hEmb.toHomeomorph.trans (Homeomorph.setCongr (hg_range.trans hCU.symm))
  have hφ_coe : ∀ w : Circle, (φ w).1 = g_loop w := fun _ => rfl
  let ang : unitInterval → ℝ := fun s => Real.arccos (1 - 2 * (s : ℝ))
  have hang_mem_Icc : ∀ s : unitInterval, 1 - 2 * (s : ℝ) ∈ Icc (-1 : ℝ) 1 := fun s =>
    ⟨by linarith [s.2.2], by linarith [s.2.1]⟩
  have hang_bounds : ∀ s : unitInterval, 0 ≤ ang s ∧ ang s ≤ Real.pi := fun s =>
    ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩
  have hang_mono : StrictMono ang := by
    intro u₁ u₂ hu
    have hlt : 1 - 2 * (u₂ : ℝ) < 1 - 2 * (u₁ : ℝ) := by
      have : (u₁ : ℝ) < (u₂ : ℝ) := hu
      linarith
    exact Real.strictAntiOn_arccos (hang_mem_Icc u₂) (hang_mem_Icc u₁) hlt
  have hφ_ang : ∀ s : unitInterval, (φ (Circle.exp (ang s))).1 = a s := by
    intro s
    rw [hφ_coe]
    change (if 0 ≤ (Circle.exp (ang s) : ℂ).im then a (τ (Circle.exp (ang s)))
      else b (τ (Circle.exp (ang s)))) = a s
    have him_nonneg : 0 ≤ (Circle.exp (ang s) : ℂ).im := by
      rw [circle_exp_coe_eq_mk]
      exact Real.sin_nonneg_of_mem_Icc (hang_bounds s)
    split_ifs
    congr 1
    apply Subtype.ext
    change (1 - (Circle.exp (ang s) : ℂ).re) / 2 = (s : ℝ)
    rw [circle_exp_coe_eq_mk]
    dsimp [ang]
    rw [Real.cos_arccos (hang_mem_Icc s).1 (hang_mem_Icc s).2]
    ring
  refine ⟨φ, ang s₁, ang s₂, ang s₃, ang s₄, (hang_bounds s₁).1,
    hang_mono hs12, hang_mono hs23, hang_mono hs34, ?_,
    hφ_ang s₁, hφ_ang s₂, hφ_ang s₃, hφ_ang s₄⟩
  linarith [(hang_bounds s₄).2, Real.pi_pos]

/-- Left open cap `{z ∈ ball 0 1 | z.re < r}` in the unit disc. -/
def leftOpenCap (r : ℝ) : Set ℂ :=
  {z ∈ ball (0 : ℂ) 1 | z.re < r}

/-- Right open cap `{z ∈ ball 0 1 | r < z.re}` in the unit disc. -/
def rightOpenCap (r : ℝ) : Set ℂ :=
  {z ∈ ball (0 : ℂ) 1 | r < z.re}

/-- Left closed cap `{z ∈ closedBall 0 1 | z.re ≤ r}` in the unit disc. -/
def leftClosedCap (r : ℝ) : Set ℂ :=
  {z ∈ closedBall (0 : ℂ) 1 | z.re ≤ r}

/-- Right closed cap `{z ∈ closedBall 0 1 | r ≤ z.re}` in the unit disc. -/
def rightClosedCap (r : ℝ) : Set ℂ :=
  {z ∈ closedBall (0 : ℂ) 1 | r ≤ z.re}

/-- Left circular boundary arc `{z ∈ sphere 0 1 | z.re ≤ r}`. -/
def leftSphereArc (r : ℝ) : Set ℂ :=
  {z ∈ sphere (0 : ℂ) 1 | z.re ≤ r}

/-- Right circular boundary arc `{z ∈ sphere 0 1 | r ≤ z.re}`. -/
def rightSphereArc (r : ℝ) : Set ℂ :=
  {z ∈ sphere (0 : ℂ) 1 | r ≤ z.re}

theorem isOpen_leftOpenCap (r : ℝ) : IsOpen (leftOpenCap r) :=
  isOpen_ball.inter (isOpen_lt Complex.continuous_re continuous_const)

theorem isOpen_rightOpenCap (r : ℝ) : IsOpen (rightOpenCap r) :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_re)

theorem isClosed_leftClosedCap (r : ℝ) : IsClosed (leftClosedCap r) :=
  isClosed_closedBall.inter (isClosed_le Complex.continuous_re continuous_const)

theorem isClosed_rightClosedCap (r : ℝ) : IsClosed (rightClosedCap r) :=
  isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_re)

theorem convex_leftOpenCap (r : ℝ) : Convex ℝ (leftOpenCap r) :=
  (convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_lt r)

theorem convex_rightOpenCap (r : ℝ) : Convex ℝ (rightOpenCap r) :=
  (convex_ball (0 : ℂ) 1).inter (convex_halfSpace_re_gt r)

theorem convex_leftClosedCap (r : ℝ) : Convex ℝ (leftClosedCap r) :=
  (convex_closedBall (0 : ℂ) 1).inter (convex_halfSpace_re_le r)

theorem convex_rightClosedCap (r : ℝ) : Convex ℝ (rightClosedCap r) :=
  (convex_closedBall (0 : ℂ) 1).inter (convex_halfSpace_re_ge r)

theorem leftOpenCap_nonempty {r : ℝ} (hr : -1 < r) (hr1 : r < 1) :
    (leftOpenCap r).Nonempty := by
  refine ⟨⟨(r - 1) / 2, 0⟩, ?_, by dsimp; linarith⟩
  rw [mem_ball_unit_iff]
  dsimp
  nlinarith

theorem rightOpenCap_nonempty {r : ℝ} (hr : -1 < r) (hr1 : r < 1) :
    (rightOpenCap r).Nonempty := by
  refine ⟨⟨(r + 1) / 2, 0⟩, ?_, by dsimp; linarith⟩
  rw [mem_ball_unit_iff]
  dsimp
  nlinarith

theorem closure_leftOpenCap {r : ℝ} (hr : -1 < r) (hr1 : r < 1) :
    closure (leftOpenCap r) = leftClosedCap r := by
  refine Subset.antisymm (closure_minimal ?_ (isClosed_leftClosedCap r)) ?_
  · intro z hz
    exact ⟨ball_subset_closedBall hz.1, hz.2.le⟩
  · intro z hz
    let z₀ : ℂ := ⟨(r - 1) / 2, 0⟩
    have hz₀ : z₀ ∈ leftOpenCap r := by
      refine ⟨?_, by dsimp [z₀]; linarith⟩
      rw [mem_ball_unit_iff]; dsimp [z₀]; nlinarith
    rw [_root_.mem_closure_iff]
    intro U hU hzU
    have hcont : Continuous (fun t : ℝ => (1 - t) • z + t • z₀) := by fun_prop
    have h0 : (1 - (0 : ℝ)) • z + (0 : ℝ) • z₀ ∈ U := by simpa using hzU
    obtain ⟨δ, hδ_pos, hδU⟩ := Metric.isOpen_iff.mp (hU.preimage hcont) 0 h0
    let t : ℝ := min (δ / 2) (1 / 2)
    have ht_pos : 0 < t := lt_min (by linarith) (by norm_num)
    have ht_lt1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have ht_ball : t ∈ ball (0 : ℝ) δ := by
      rw [mem_ball_zero_iff, Real.norm_of_nonneg ht_pos.le]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨(1 - t) • z + t • z₀, hδU ht_ball, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]
      have hz_norm : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz.1
      have hz₀_norm : ‖z₀‖ < 1 := mem_ball_zero_iff.mp hz₀.1
      calc ‖(1 - t) • z + t • z₀‖
          ≤ ‖(1 - t) • z‖ + ‖t • z₀‖ := norm_add_le _ _
        _ = (1 - t) * ‖z‖ + t * ‖z₀‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
              Real.norm_of_nonneg ht_pos.le]
        _ < (1 - t) * 1 + t * 1 := by nlinarith
        _ = 1 := by ring
    · show ((1 - t) • z + t • z₀).re < r
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      have hz_re : z.re ≤ r := hz.2
      have hz₀_re : z₀.re < r := hz₀.2
      nlinarith

theorem closure_rightOpenCap {r : ℝ} (hr : -1 < r) (hr1 : r < 1) :
    closure (rightOpenCap r) = rightClosedCap r := by
  refine Subset.antisymm (closure_minimal ?_ (isClosed_rightClosedCap r)) ?_
  · intro z hz
    exact ⟨ball_subset_closedBall hz.1, hz.2.le⟩
  · intro z hz
    let z₀ : ℂ := ⟨(r + 1) / 2, 0⟩
    have hz₀ : z₀ ∈ rightOpenCap r := by
      refine ⟨?_, by dsimp [z₀]; linarith⟩
      rw [mem_ball_unit_iff]; dsimp [z₀]; nlinarith
    rw [_root_.mem_closure_iff]
    intro U hU hzU
    have hcont : Continuous (fun t : ℝ => (1 - t) • z + t • z₀) := by fun_prop
    have h0 : (1 - (0 : ℝ)) • z + (0 : ℝ) • z₀ ∈ U := by simpa using hzU
    obtain ⟨δ, hδ_pos, hδU⟩ := Metric.isOpen_iff.mp (hU.preimage hcont) 0 h0
    let t : ℝ := min (δ / 2) (1 / 2)
    have ht_pos : 0 < t := lt_min (by linarith) (by norm_num)
    have ht_lt1 : t < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
    have ht_ball : t ∈ ball (0 : ℝ) δ := by
      rw [mem_ball_zero_iff, Real.norm_of_nonneg ht_pos.le]
      exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
    refine ⟨(1 - t) • z + t • z₀, hδU ht_ball, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [mem_ball_zero_iff]
      have hz_norm : ‖z‖ ≤ 1 := mem_closedBall_zero_iff.mp hz.1
      have hz₀_norm : ‖z₀‖ < 1 := mem_ball_zero_iff.mp hz₀.1
      calc ‖(1 - t) • z + t • z₀‖
          ≤ ‖(1 - t) • z‖ + ‖t • z₀‖ := norm_add_le _ _
        _ = (1 - t) * ‖z‖ + t * ‖z₀‖ := by
            rw [norm_smul, norm_smul, Real.norm_of_nonneg (by linarith),
              Real.norm_of_nonneg ht_pos.le]
        _ < (1 - t) * 1 + t * 1 := by nlinarith
        _ = 1 := by ring
    · show r < ((1 - t) • z + t • z₀).re
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      have hz_re : r ≤ z.re := hz.2
      have hz₀_re : r < z₀.re := hz₀.2
      nlinarith

theorem leftClosedCap_sdiff_leftOpenCap (r : ℝ) :
    leftClosedCap r \ leftOpenCap r = leftSphereArc r ∪ vertChord r := by
  ext z
  simp only [leftClosedCap, leftOpenCap, leftSphereArc, vertChord, mem_sdiff, mem_union,
    mem_ofPred_eq, mem_closedBall_zero_iff, mem_ball_zero_iff, mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨⟨h1, h2⟩, hnot⟩
    by_cases h_eq1 : ‖z‖ = 1
    · exact Or.inl ⟨h_eq1, h2⟩
    · have hlt1 : ‖z‖ < 1 := lt_of_le_of_ne h1 h_eq1
      have h_ge : r ≤ z.re := not_lt.mp (fun hlt => hnot ⟨hlt1, hlt⟩)
      exact Or.inr ⟨h1, le_antisymm h2 h_ge⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, rfl⟩)
    · exact ⟨⟨h1.le, h2⟩, fun ⟨hlt, _⟩ => hlt.ne h1⟩
    · exact ⟨⟨h1, le_rfl⟩, fun ⟨_, hlt⟩ => hlt.ne rfl⟩

theorem rightClosedCap_sdiff_rightOpenCap (r : ℝ) :
    rightClosedCap r \ rightOpenCap r = rightSphereArc r ∪ vertChord r := by
  ext z
  simp only [rightClosedCap, rightOpenCap, rightSphereArc, vertChord, mem_sdiff, mem_union,
    mem_ofPred_eq, mem_closedBall_zero_iff, mem_ball_zero_iff, mem_sphere_zero_iff_norm]
  constructor
  · rintro ⟨⟨h1, h2⟩, hnot⟩
    by_cases h_eq1 : ‖z‖ = 1
    · exact Or.inl ⟨h_eq1, h2⟩
    · have hlt1 : ‖z‖ < 1 := lt_of_le_of_ne h1 h_eq1
      have h_le : z.re ≤ r := not_lt.mp (fun hlt => hnot ⟨hlt1, hlt⟩)
      exact Or.inr ⟨h1, le_antisymm h_le h2⟩
  · rintro (⟨h1, h2⟩ | ⟨h1, rfl⟩)
    · exact ⟨⟨h1.le, h2⟩, fun ⟨hlt, _⟩ => hlt.ne h1⟩
    · exact ⟨⟨h1, le_rfl⟩, fun ⟨_, hlt⟩ => hlt.ne rfl⟩

/-- Angular parametrization of the left circular arc `leftSphereArc (cos θ₀)` for `θ₀ ∈ (0, π)`. -/
noncomputable def leftSphereArcMap (θ₀ : ℝ) (s : unitInterval) : ℂ :=
  (Circle.exp (θ₀ + (2 * Real.pi - 2 * θ₀) * (s : ℝ)) : ℂ)

/-- Angular parametrization of the right circular arc `rightSphereArc (cos θ₀)` for `θ₀ ∈ (0, π)`.
-/
noncomputable def rightSphereArcMap (θ₀ : ℝ) (s : unitInterval) : ℂ :=
  (Circle.exp ((2 * Real.pi - θ₀) + 2 * θ₀ * (s : ℝ)) : ℂ)

theorem isArcMap_leftSphereArcMap {θ₀ : ℝ} (h0 : 0 < θ₀) (hpi : θ₀ < Real.pi) :
    IsArcMap (leftSphereArcMap θ₀) := by
  refine ⟨?_, ?_⟩
  · unfold leftSphereArcMap
    exact continuous_subtype_val.comp (Circle.exp.continuous.comp (by fun_prop))
  · intro s₁ s₂ h
    have h_exp : Circle.exp (θ₀ + (2 * Real.pi - 2 * θ₀) * (s₁ : ℝ)) =
        Circle.exp (θ₀ + (2 * Real.pi - 2 * θ₀) * (s₂ : ℝ)) :=
      Subtype.ext h
    have hs1 : θ₀ + (2 * Real.pi - 2 * θ₀) * (s₁ : ℝ) ∈ Ico θ₀ (θ₀ + 2 * Real.pi) :=
      ⟨by nlinarith [s₁.2.1], by nlinarith [s₁.2.2]⟩
    have hs2 : θ₀ + (2 * Real.pi - 2 * θ₀) * (s₂ : ℝ) ∈ Ico θ₀ (θ₀ + 2 * Real.pi) :=
      ⟨by nlinarith [s₂.2.1], by nlinarith [s₂.2.2]⟩
    have heq := eq_of_circle_exp_eq_of_mem_Ico hs1 hs2 h_exp
    apply Subtype.ext
    nlinarith

theorem isArcMap_rightSphereArcMap {θ₀ : ℝ} (h0 : 0 < θ₀) (hpi : θ₀ < Real.pi) :
    IsArcMap (rightSphereArcMap θ₀) := by
  refine ⟨?_, ?_⟩
  · unfold rightSphereArcMap
    exact continuous_subtype_val.comp (Circle.exp.continuous.comp (by fun_prop))
  · intro s₁ s₂ h
    have h_exp : Circle.exp ((2 * Real.pi - θ₀) + 2 * θ₀ * (s₁ : ℝ)) =
        Circle.exp ((2 * Real.pi - θ₀) + 2 * θ₀ * (s₂ : ℝ)) :=
      Subtype.ext h
    have hs1 : (2 * Real.pi - θ₀) + 2 * θ₀ * (s₁ : ℝ) ∈
        Ico (2 * Real.pi - θ₀) ((2 * Real.pi - θ₀) + 2 * Real.pi) :=
      ⟨by nlinarith [s₁.2.1], by nlinarith [s₁.2.2]⟩
    have hs2 : (2 * Real.pi - θ₀) + 2 * θ₀ * (s₂ : ℝ) ∈
        Ico (2 * Real.pi - θ₀) ((2 * Real.pi - θ₀) + 2 * Real.pi) :=
      ⟨by nlinarith [s₂.2.1], by nlinarith [s₂.2.2]⟩
    have heq := eq_of_circle_exp_eq_of_mem_Ico hs1 hs2 h_exp
    apply Subtype.ext
    nlinarith

theorem range_leftSphereArcMap {θ₀ : ℝ} (h0 : 0 < θ₀) (hpi : θ₀ < Real.pi) :
    range (leftSphereArcMap θ₀) = leftSphereArc (Real.cos θ₀) := by
  ext z
  simp only [mem_range, leftSphereArc, mem_ofPred_eq]
  constructor
  · rintro ⟨s, rfl⟩
    unfold leftSphereArcMap
    refine ⟨mem_sphere_zero_iff_norm.mpr (Circle.norm_coe _), ?_⟩
    rw [circle_exp_coe_eq_mk]
    dsimp
    let θ := θ₀ + (2 * Real.pi - 2 * θ₀) * (s : ℝ)
    have hθ_lo : θ₀ ≤ θ := by dsimp [θ]; nlinarith [s.2.1]
    have hθ_hi : θ ≤ 2 * Real.pi - θ₀ := by dsimp [θ]; nlinarith [s.2.2]
    rcases le_total θ Real.pi with hle | hge
    · exact Real.strictAntiOn_cos.antitoneOn ⟨h0.le, hpi.le⟩ ⟨h0.le.trans hθ_lo, hle⟩ hθ_lo
    · have hsub : 2 * Real.pi - θ = -(θ - 2 * Real.pi) := by ring
      have hcos : Real.cos θ = Real.cos (2 * Real.pi - θ) := by
        rw [hsub, Real.cos_neg, Real.cos_sub_two_pi]
      rw [hcos]
      exact Real.strictAntiOn_cos.antitoneOn ⟨h0.le, hpi.le⟩
        ⟨by linarith, by linarith⟩ (by linarith)
  · rintro ⟨hz_sph, hz_re⟩
    have hsq : z.re ^ 2 + z.im ^ 2 = 1 := (mem_sphere_unit_iff z).mp hz_sph
    have hre_Icc : z.re ∈ Icc (-1 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
    let α := Real.arccos z.re
    have hα_lo : θ₀ ≤ α := by
      have h1 : Real.arccos (Real.cos θ₀) ≤ Real.arccos z.re :=
        Real.strictAntiOn_arccos.antitoneOn hre_Icc ⟨(Real.neg_one_le_cos θ₀),
          (Real.cos_le_one θ₀)⟩ hz_re
      rwa [Real.arccos_cos h0.le hpi.le] at h1
    have hα_hi : α ≤ Real.pi := Real.arccos_le_pi z.re
    have hcos_α : Real.cos α = z.re := Real.cos_arccos hre_Icc.1 hre_Icc.2
    have hsin_α : Real.sin α = Real.sqrt (1 - z.re ^ 2) := Real.sin_arccos z.re
    have h_im_abs : z.im ^ 2 = Real.sin α ^ 2 := by
      rw [hsin_α, Real.sq_sqrt (by nlinarith)]; linarith
    let θ := if 0 ≤ z.im then α else 2 * Real.pi - α
    have hθ_bounds : θ₀ ≤ θ ∧ θ ≤ 2 * Real.pi - θ₀ := by
      dsimp [θ]; split_ifs <;> constructor <;> linarith
    have hexp_θ : (Circle.exp θ : ℂ) = z := by
      rw [circle_exp_coe_eq_mk]
      apply Complex.ext
      · dsimp [θ]
        split_ifs
        · exact hcos_α
        · have hsub : 2 * Real.pi - α = -(α - 2 * Real.pi) := by ring
          rw [hsub, Real.cos_neg, Real.cos_sub_two_pi, hcos_α]
      · dsimp [θ]
        split_ifs with him
        · have hsin_nonneg : 0 ≤ Real.sin α := by rw [hsin_α]; exact Real.sqrt_nonneg _
          nlinarith [sq_nonneg (z.im - Real.sin α)]
        · push Not at him
          have hsub : 2 * Real.pi - α = -(α - 2 * Real.pi) := by ring
          rw [hsub, Real.sin_neg, Real.sin_sub_two_pi]
          have hsin_nonneg : 0 ≤ Real.sin α := by rw [hsin_α]; exact Real.sqrt_nonneg _
          nlinarith [sq_nonneg (z.im + Real.sin α)]
    let s : ℝ := (θ - θ₀) / (2 * Real.pi - 2 * θ₀)
    have hden_pos : 0 < 2 * Real.pi - 2 * θ₀ := by linarith
    have hs_mem : s ∈ Icc (0 : ℝ) 1 := by
      dsimp [s]
      exact ⟨div_nonneg (by linarith) hden_pos.le, (div_le_one hden_pos).mpr (by linarith)⟩
    refine ⟨⟨s, hs_mem⟩, ?_⟩
    change (Circle.exp (θ₀ + (2 * Real.pi - 2 * θ₀) * s) : ℂ) = z
    have h_eq : θ₀ + (2 * Real.pi - 2 * θ₀) * s = θ := by
      dsimp [s]
      rw [mul_div_cancel₀ _ (ne_of_gt hden_pos)]
      ring
    rw [h_eq, hexp_θ]

theorem range_rightSphereArcMap {θ₀ : ℝ} (h0 : 0 < θ₀) (hpi : θ₀ < Real.pi) :
    range (rightSphereArcMap θ₀) = rightSphereArc (Real.cos θ₀) := by
  ext z
  simp only [mem_range, rightSphereArc, mem_ofPred_eq]
  constructor
  · rintro ⟨s, rfl⟩
    unfold rightSphereArcMap
    refine ⟨mem_sphere_zero_iff_norm.mpr (Circle.norm_coe _), ?_⟩
    rw [circle_exp_coe_eq_mk]
    dsimp
    let θ := (2 * Real.pi - θ₀) + 2 * θ₀ * (s : ℝ)
    have hθ_lo : 2 * Real.pi - θ₀ ≤ θ := by dsimp [θ]; nlinarith [s.2.1]
    have hθ_hi : θ ≤ 2 * Real.pi + θ₀ := by dsimp [θ]; nlinarith [s.2.2]
    rcases le_total θ (2 * Real.pi) with hle | hge
    · have hsub : 2 * Real.pi - θ = -(θ - 2 * Real.pi) := by ring
      have hcos : Real.cos θ = Real.cos (2 * Real.pi - θ) := by
        rw [hsub, Real.cos_neg, Real.cos_sub_two_pi]
      rw [hcos]
      exact Real.strictAntiOn_cos.antitoneOn ⟨by linarith, by linarith⟩
        ⟨h0.le, hpi.le⟩ (by linarith)
    · have hcos : Real.cos θ = Real.cos (θ - 2 * Real.pi) := Real.cos_sub_two_pi θ |>.symm
      rw [hcos]
      exact Real.strictAntiOn_cos.antitoneOn ⟨by linarith, by linarith⟩
        ⟨h0.le, hpi.le⟩ (by linarith)
  · rintro ⟨hz_sph, hz_re⟩
    have hsq : z.re ^ 2 + z.im ^ 2 = 1 := (mem_sphere_unit_iff z).mp hz_sph
    have hre_Icc : z.re ∈ Icc (-1 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
    let α := Real.arccos z.re
    have hα_lo : 0 ≤ α := Real.arccos_nonneg z.re
    have hα_hi : α ≤ θ₀ := by
      have h1 : Real.arccos z.re ≤ Real.arccos (Real.cos θ₀) :=
        Real.strictAntiOn_arccos.antitoneOn ⟨Real.neg_one_le_cos θ₀, Real.cos_le_one θ₀⟩ hre_Icc
          hz_re
      rwa [Real.arccos_cos h0.le hpi.le] at h1
    have hcos_α : Real.cos α = z.re := Real.cos_arccos hre_Icc.1 hre_Icc.2
    have hsin_α : Real.sin α = Real.sqrt (1 - z.re ^ 2) := Real.sin_arccos z.re
    have h_im_abs : z.im ^ 2 = Real.sin α ^ 2 := by
      rw [hsin_α, Real.sq_sqrt (by nlinarith)]; linarith
    let θ := if 0 ≤ z.im then 2 * Real.pi + α else 2 * Real.pi - α
    have hθ_bounds : 2 * Real.pi - θ₀ ≤ θ ∧ θ ≤ 2 * Real.pi + θ₀ := by
      dsimp [θ]; split_ifs <;> constructor <;> linarith
    have hexp_θ : (Circle.exp θ : ℂ) = z := by
      rw [circle_exp_coe_eq_mk]
      apply Complex.ext
      · dsimp [θ]
        split_ifs
        · have hsub : 2 * Real.pi + α - 2 * Real.pi = α := by ring
          rw [← Real.cos_sub_two_pi (2 * Real.pi + α), hsub, hcos_α]
        · have hsub : 2 * Real.pi - α = -(α - 2 * Real.pi) := by ring
          rw [hsub, Real.cos_neg, Real.cos_sub_two_pi, hcos_α]
      · dsimp [θ]
        split_ifs with him
        · have hsub : 2 * Real.pi + α - 2 * Real.pi = α := by ring
          rw [← Real.sin_sub_two_pi (2 * Real.pi + α), hsub]
          have hsin_nonneg : 0 ≤ Real.sin α := by rw [hsin_α]; exact Real.sqrt_nonneg _
          nlinarith [sq_nonneg (z.im - Real.sin α)]
        · push Not at him
          have hsub : 2 * Real.pi - α = -(α - 2 * Real.pi) := by ring
          rw [hsub, Real.sin_neg, Real.sin_sub_two_pi]
          have hsin_nonneg : 0 ≤ Real.sin α := by rw [hsin_α]; exact Real.sqrt_nonneg _
          nlinarith [sq_nonneg (z.im + Real.sin α)]
    let s : ℝ := (θ - (2 * Real.pi - θ₀)) / (2 * θ₀)
    have hden_pos : 0 < 2 * θ₀ := by linarith
    have hs_mem : s ∈ Icc (0 : ℝ) 1 := by
      dsimp [s]
      exact ⟨div_nonneg (by linarith) hden_pos.le, (div_le_one hden_pos).mpr (by linarith)⟩
    refine ⟨⟨s, hs_mem⟩, ?_⟩
    change (Circle.exp ((2 * Real.pi - θ₀) + 2 * θ₀ * s) : ℂ) = z
    have h_eq : (2 * Real.pi - θ₀) + 2 * θ₀ * s = θ := by
      dsimp [s]
      rw [mul_div_cancel₀ _ (ne_of_gt hden_pos)]
      ring
    rw [h_eq, hexp_θ]

/-- Vertical pinching scale `s_k(r) = 1 - min (1/2) (∏ j : Fin (k - 1), (r - parallelX k j)^2)`. -/
noncomputable def vertPinchScale (k : ℕ) (r : ℝ) : ℝ :=
  1 - min (1 / 2 : ℝ) (∏ j : Fin (k - 1), (r - parallelX k j) ^ 2)

theorem continuous_vertPinchScale (k : ℕ) : Continuous (vertPinchScale k) := by
  unfold vertPinchScale
  fun_prop

theorem vertPinchScale_bounds (k : ℕ) (r : ℝ) :
    1 / 2 ≤ vertPinchScale k r ∧ vertPinchScale k r ≤ 1 := by
  unfold vertPinchScale
  have hprod : 0 ≤ ∏ j : Fin (k - 1), (r - parallelX k j) ^ 2 :=
    Finset.prod_nonneg fun _ _ => sq_nonneg _
  have hmin_ge : 0 ≤ min (1 / 2 : ℝ) (∏ j : Fin (k - 1), (r - parallelX k j) ^ 2) :=
    le_min (by norm_num) hprod
  have hmin_le : min (1 / 2 : ℝ) (∏ j : Fin (k - 1), (r - parallelX k j) ^ 2) ≤ 1 / 2 :=
    min_le_left _ _
  exact ⟨by linarith, by linarith⟩

theorem vertPinchScale_pos (k : ℕ) (r : ℝ) : 0 < vertPinchScale k r := by
  linarith [(vertPinchScale_bounds k r).1]

theorem vertPinchScale_eq_one_iff (k : ℕ) (r : ℝ) :
    vertPinchScale k r = 1 ↔ ∃ j : Fin (k - 1), r = parallelX k j := by
  unfold vertPinchScale
  have hsub : 1 - min (1 / 2 : ℝ) (∏ j : Fin (k - 1), (r - parallelX k j) ^ 2) = 1 ↔
      min (1 / 2 : ℝ) (∏ j : Fin (k - 1), (r - parallelX k j) ^ 2) = 0 := by
    constructor <;> intro h <;> linarith
  rw [hsub]
  have hmin0 : min (1 / 2 : ℝ) (∏ j : Fin (k - 1), (r - parallelX k j) ^ 2) = 0 ↔
      ∏ j : Fin (k - 1), (r - parallelX k j) ^ 2 = 0 := by
    constructor
    · intro h
      rcases min_choice (1 / 2 : ℝ) (∏ j : Fin (k - 1), (r - parallelX k j) ^ 2) with h1 | h2
      · linarith
      · linarith
    · intro h
      rw [h, min_eq_right (by norm_num)]
  rw [hmin0, Finset.prod_eq_zero_iff]
  simp [sub_eq_zero]

/-- Horizontal clamp-averaging map `(r + max a (min b r)) / 2` for `a ≤ b`. -/
noncomputable def pinchRe (a b r : ℝ) : ℝ :=
  (r + max a (min b r)) / 2

/-- Inverse of `pinchRe a b`: `2 * y - max a (min b y)`. -/
noncomputable def pinchReInv (a b y : ℝ) : ℝ :=
  2 * y - max a (min b y)

theorem continuous_pinchRe (a b : ℝ) : Continuous (pinchRe a b) := by
  unfold pinchRe; fun_prop

theorem continuous_pinchReInv (a b : ℝ) : Continuous (pinchReInv a b) := by
  unfold pinchReInv; fun_prop

theorem pinchReInv_pinchRe {a b : ℝ} (hab : a ≤ b) (r : ℝ) :
    pinchReInv a b (pinchRe a b r) = r := by
  unfold pinchRe pinchReInv
  rcases le_total r b with hrb | hbr
  · rw [min_eq_right hrb]
    rcases le_total a r with har | hra
    · rw [max_eq_right har, min_eq_right (by linarith), max_eq_right (by linarith)]
      ring
    · rw [max_eq_left hra, min_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  · rw [min_eq_left hbr, max_eq_right hab, min_eq_left (by linarith), max_eq_right hab]
    ring

theorem pinchRe_pinchReInv {a b : ℝ} (hab : a ≤ b) (y : ℝ) :
    pinchRe a b (pinchReInv a b y) = y := by
  unfold pinchRe pinchReInv
  rcases le_total y b with hyb | hby
  · rw [min_eq_right hyb]
    rcases le_total a y with hay | hya
    · rw [max_eq_right hay, min_eq_right (by linarith), max_eq_right (by linarith)]
      ring
    · rw [max_eq_left hya, min_eq_right (by linarith), max_eq_left (by linarith)]
      ring
  · rw [min_eq_left hby, max_eq_right hab, min_eq_left (by linarith), max_eq_right hab]
    ring

theorem pinchRe_of_mem_Icc {a b r : ℝ} (hr : r ∈ Icc a b) :
    pinchRe a b r = r := by
  unfold pinchRe
  rw [min_eq_right hr.2, max_eq_right hr.1]
  ring

theorem pinchRe_sq_le {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (r : ℝ) :
    (pinchRe a b r) ^ 2 ≤ r ^ 2 := by
  unfold pinchRe
  have hab : a ≤ b := ha.trans hb
  rcases le_total r b with hrb | hbr
  · rw [min_eq_right hrb]
    rcases le_total a r with har | hra
    · rw [max_eq_right har]; nlinarith
    · rw [max_eq_left hra]; nlinarith
  · rw [min_eq_left hbr, max_eq_right hab]; nlinarith

theorem pinchRe_mem_Ioo_of_mem_Icc {a b r : ℝ} (ha : -1 < a) (hab : a ≤ b) (hb : b < 1)
    (hr : r ∈ Icc (-1 : ℝ) 1) :
    pinchRe a b r ∈ Ioo (-1 : ℝ) 1 := by
  unfold pinchRe
  have hcl_lo : a ≤ max a (min b r) := le_max_left _ _
  have hcl_hi : max a (min b r) ≤ b := max_le hab (min_le_left _ _)
  exact ⟨by linarith [hr.1], by linarith [hr.2]⟩

/-- Vertical pinching homeomorphism `Ψ : ℂ ≃ₜ ℂ` fixing `vertChord (parallelX k j)` for every
`j : Fin (k - 1)` and mapping `closedBall 0 1 \ ⋃ j, {top j, bot j}` into `ball 0 1`. -/
noncomputable def pinchVertHomeo (k : ℕ) (hk : 3 ≤ k) : ℂ ≃ₜ ℂ := by
  let a : ℝ := min 0 (parallelX k ⟨k - 2, by omega⟩)
  let b : ℝ := max 0 (parallelX k ⟨0, by omega⟩)
  have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
  exact
    { toFun := fun z => ⟨pinchRe a b z.re, vertPinchScale k z.re * z.im⟩
      invFun := fun w =>
        ⟨pinchReInv a b w.re, (vertPinchScale k (pinchReInv a b w.re))⁻¹ * w.im⟩
      left_inv := fun z => by
        apply Complex.ext
        · exact pinchReInv_pinchRe hab z.re
        · dsimp
          rw [pinchReInv_pinchRe hab z.re,
            inv_mul_cancel_left₀ (ne_of_gt (vertPinchScale_pos k z.re))]
      right_inv := fun w => by
        apply Complex.ext
        · exact pinchRe_pinchReInv hab w.re
        · dsimp
          rw [mul_inv_cancel_left₀ (ne_of_gt (vertPinchScale_pos k (pinchReInv a b w.re)))]
      continuous_toFun := by
        have h_eq : (fun z : ℂ => (⟨pinchRe a b z.re, vertPinchScale k z.re * z.im⟩ : ℂ)) =
            fun z : ℂ => (pinchRe a b z.re : ℂ) +
              ((vertPinchScale k z.re * z.im : ℝ) : ℂ) * Complex.I := by
          ext z; apply Complex.ext <;> simp
        rw [h_eq]
        have := continuous_pinchRe a b
        have := continuous_vertPinchScale k
        fun_prop
      continuous_invFun := by
        have h_eq : (fun w : ℂ => (⟨pinchReInv a b w.re,
            (vertPinchScale k (pinchReInv a b w.re))⁻¹ * w.im⟩ : ℂ)) =
            fun w : ℂ => (pinchReInv a b w.re : ℂ) +
              (((vertPinchScale k (pinchReInv a b w.re))⁻¹ * w.im : ℝ) : ℂ) * Complex.I := by
          ext w; apply Complex.ext <;> simp
        rw [h_eq]
        have := continuous_pinchReInv a b
        have := continuous_vertPinchScale k
        have h_ne : ∀ w : ℂ, vertPinchScale k (pinchReInv a b w.re) ≠ 0 :=
          fun w => ne_of_gt (vertPinchScale_pos k _)
        fun_prop (disch := assumption) }

theorem pinchVertHomeo_apply (k : ℕ) (hk : 3 ≤ k) (z : ℂ) :
    pinchVertHomeo k hk z =
      ⟨pinchRe (min 0 (parallelX k ⟨k - 2, by omega⟩))
        (max 0 (parallelX k ⟨0, by omega⟩)) z.re,
        vertPinchScale k z.re * z.im⟩ := rfl

theorem pinchVertHomeo_apply_of_re_eq {k : ℕ} (hk : 3 ≤ k) {z : ℂ} (j : Fin (k - 1))
    (hz : z.re = parallelX k j) :
    pinchVertHomeo k hk z = z := by
  rw [pinchVertHomeo_apply]
  have hanti := (strictAnti_parallelX (by omega : 1 ≤ k)).antitone
  have hj_le : j ≤ (⟨k - 2, by omega⟩ : Fin (k - 1)) := by
    rw [Fin.le_def]
    dsimp
    have := j.2
    omega
  have hj_lo : parallelX k ⟨k - 2, by omega⟩ ≤ parallelX k j := hanti hj_le
  have hj_hi : parallelX k j ≤ parallelX k ⟨0, by omega⟩ :=
    hanti (show (⟨0, by omega⟩ : Fin (k - 1)) ≤ j from Fin.le_def.mpr (Nat.zero_le _))
  have hmem : z.re ∈ Icc (min 0 (parallelX k ⟨k - 2, by omega⟩))
      (max 0 (parallelX k ⟨0, by omega⟩)) := by
    rw [hz]
    exact ⟨(min_le_right _ _).trans hj_lo, hj_hi.trans (le_max_right _ _)⟩
  have hscale : vertPinchScale k z.re = 1 :=
    (vertPinchScale_eq_one_iff k z.re).mpr ⟨j, hz⟩
  apply Complex.ext
  · exact pinchRe_of_mem_Icc hmem
  · dsimp; rw [hscale, one_mul]

theorem pinchVertHomeo_norm_sq_le (k : ℕ) (hk : 3 ≤ k) (z : ℂ) :
    (pinchVertHomeo k hk z).re ^ 2 + (pinchVertHomeo k hk z).im ^ 2 ≤
      z.re ^ 2 + z.im ^ 2 := by
  rw [pinchVertHomeo_apply]
  dsimp
  have hre : (pinchRe (min 0 (parallelX k ⟨k - 2, by omega⟩))
      (max 0 (parallelX k ⟨0, by omega⟩)) z.re) ^ 2 ≤ z.re ^ 2 :=
    pinchRe_sq_le (min_le_left _ _) (le_max_left _ _) z.re
  have hs := vertPinchScale_bounds k z.re
  have him : (vertPinchScale k z.re * z.im) ^ 2 ≤ z.im ^ 2 := by
    have : (vertPinchScale k z.re) ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg z.im]
  linarith

theorem image_closedBall_pinchVertHomeo_subset (k : ℕ) (hk : 3 ≤ k) :
    (pinchVertHomeo k hk) '' closedBall (0 : ℂ) 1 ⊆ closedBall (0 : ℂ) 1 := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_closedBall_unit_iff] at hz ⊢
  exact (pinchVertHomeo_norm_sq_le k hk z).trans hz

theorem image_ball_pinchVertHomeo_subset (k : ℕ) (hk : 3 ≤ k) :
    (pinchVertHomeo k hk) '' ball (0 : ℂ) 1 ⊆ ball (0 : ℂ) 1 := by
  rintro _ ⟨z, hz, rfl⟩
  rw [mem_ball_unit_iff] at hz ⊢
  exact (pinchVertHomeo_norm_sq_le k hk z).trans_lt hz

theorem image_closedBall_pinchVertHomeo_inter_sphere (k : ℕ) (hk : 3 ≤ k) :
    ((pinchVertHomeo k hk) '' closedBall (0 : ℂ) 1) ∩ sphere (0 : ℂ) 1 =
      ⋃ j : Fin (k - 1), {⟨parallelX k j, parallelY k j⟩, ⟨parallelX k j, -parallelY k j⟩} := by
  ext w
  simp only [mem_inter_iff, mem_image, mem_iUnion, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨z, hz_cb, rfl⟩, hz_sph⟩
    rw [mem_closedBall_unit_iff] at hz_cb
    rw [mem_sphere_unit_iff] at hz_sph
    let a : ℝ := min 0 (parallelX k ⟨k - 2, by omega⟩)
    let b : ℝ := max 0 (parallelX k ⟨0, by omega⟩)
    have ha_gt : -1 < a := lt_min (by norm_num) (parallelX_mem_Ioo _).1
    have hb_lt : b < 1 := max_lt (by norm_num) (parallelX_mem_Ioo _).2
    have hab : a ≤ b := (min_le_left _ _).trans (le_max_left _ _)
    have hz_re_Icc : z.re ∈ Icc (-1 : ℝ) 1 := ⟨by nlinarith, by nlinarith⟩
    have hre_Ioo : (pinchVertHomeo k hk z).re ∈ Ioo (-1 : ℝ) 1 :=
      pinchRe_mem_Ioo_of_mem_Icc ha_gt hab hb_lt hz_re_Icc
    have hre_sq_lt : (pinchVertHomeo k hk z).re ^ 2 < 1 := by
      nlinarith [hre_Ioo.1, hre_Ioo.2]
    have hre_sq_le : (pinchVertHomeo k hk z).re ^ 2 ≤ z.re ^ 2 :=
      pinchRe_sq_le (min_le_left _ _) (le_max_left _ _) z.re
    have hs := vertPinchScale_bounds k z.re
    have him_sq_le : (pinchVertHomeo k hk z).im ^ 2 ≤ z.im ^ 2 := by
      change (vertPinchScale k z.re * z.im) ^ 2 ≤ z.im ^ 2
      have : (vertPinchScale k z.re) ^ 2 ≤ 1 := by nlinarith
      nlinarith [sq_nonneg z.im]
    have him_sq_pos : 0 < (pinchVertHomeo k hk z).im ^ 2 := by linarith
    have hzim_sq_pos : 0 < z.im ^ 2 := lt_of_lt_of_le him_sq_pos him_sq_le
    have him_sq_eq : (vertPinchScale k z.re * z.im) ^ 2 = z.im ^ 2 := by
      change (pinchVertHomeo k hk z).im ^ 2 = z.im ^ 2
      linarith
    have hscale_sq : (vertPinchScale k z.re) ^ 2 = 1 := by nlinarith
    have hscale_eq : vertPinchScale k z.re = 1 := by nlinarith [hs.1]
    obtain ⟨j, hj⟩ := (vertPinchScale_eq_one_iff k z.re).mp hscale_eq
    refine ⟨j, ?_⟩
    rw [pinchVertHomeo_apply_of_re_eq hk j hj] at hz_sph ⊢
    have hz_im_sq : z.im ^ 2 = parallelY k j ^ 2 := by
      have := parallelX_sq_add_parallelY_sq j
      rw [← hj] at this
      linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz_im_sq with him | him
    · left; exact Complex.ext hj him
    · right; exact Complex.ext hj him
  · rintro ⟨j, rfl | rfl⟩
    · have h1 : (⟨parallelX k j, parallelY k j⟩ : ℂ) ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_unit_iff]; exact parallelX_sq_add_parallelY_sq j
      exact ⟨⟨⟨parallelX k j, parallelY k j⟩, sphere_subset_closedBall h1,
        pinchVertHomeo_apply_of_re_eq hk j rfl⟩, h1⟩
    · have h1 : (⟨parallelX k j, -parallelY k j⟩ : ℂ) ∈ sphere (0 : ℂ) 1 := by
        rw [mem_sphere_unit_iff]; dsimp; rw [neg_sq]; exact parallelX_sq_add_parallelY_sq j
      exact ⟨⟨⟨parallelX k j, -parallelY k j⟩, sphere_subset_closedBall h1,
        pinchVertHomeo_apply_of_re_eq hk j rfl⟩, h1⟩

/-! ## 6. Chart Image Properties, Single-Region `IsCappedSplit`, and Pinched Subdisc `Δ` -/

theorem isChart_g_ball_eq_region {S : Type w} [TopologicalSpace S]
    {Λ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart (closure Λ) h g) (hΛ_open : IsOpen Λ)
    (hdiscBd : discBd (closure Λ) = subBd Λ) :
    g '' ball (0 : ℂ) 1 = Λ := by
  rw [IsChart.g_ball c, hdiscBd, subBd_eq_frontier, hΛ_open.frontier_eq]
  ext x
  simp only [mem_sdiff]
  exact ⟨fun ⟨hx_cl, hx_not⟩ => by_contra fun hx => hx_not ⟨hx_cl, hx⟩,
    fun hx => ⟨subset_closure hx, fun ⟨_, hx_not⟩ => hx_not hx⟩⟩

theorem isChart_isOpen_image_of_subset_ball {S : Type w} [TopologicalSpace S]
    {Λ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart (closure Λ) h g) (hΛ_open : IsOpen Λ)
    (hdiscBd : discBd (closure Λ) = subBd Λ)
    {U : Set ℂ} (hU_open : IsOpen U) (hU_sub : U ⊆ ball (0 : ℂ) 1) :
    IsOpen (g '' U) := by
  have hg_ball : g '' ball (0 : ℂ) 1 = Λ := isChart_g_ball_eq_region c hΛ_open hdiscBd
  have h_eq : g '' U = Λ ∩ h ⁻¹' U := by
    ext x
    simp only [mem_image, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨z, hzU, rfl⟩
      refine ⟨hg_ball ▸ ⟨z, hU_sub hzU, rfl⟩, ?_⟩
      rw [c.hg (ball_subset_closedBall (hU_sub hzU))]
      exact hzU
    · rintro ⟨hxΛ, hxhU⟩
      exact ⟨h x, hxhU, c.gh (subset_closure hxΛ)⟩
  rw [h_eq]
  exact (c.hc.mono subset_closure).isOpen_inter_preimage hΛ_open hU_open

theorem isChart_closure_image_of_subset_closedBall {S : Type w} [TopologicalSpace S] [T2Space S]
    {Δ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart Δ h g) {U : Set ℂ} (hU_sub : U ⊆ closedBall (0 : ℂ) 1) :
    closure (g '' U) = g '' closure U := by
  have hcl_sub : closure U ⊆ closedBall (0 : ℂ) 1 :=
    closure_minimal hU_sub isClosed_closedBall
  have hcomp : IsCompact (g '' closure U) :=
    ((isCompact_closedBall (0 : ℂ) 1).of_isClosed_subset isClosed_closure
      hcl_sub).image_of_continuousOn
      (c.gc.mono hcl_sub)
  refine Subset.antisymm (closure_minimal (image_mono subset_closure) hcomp.isClosed) ?_
  rintro _ ⟨z, hz_cl, rfl⟩
  rw [_root_.mem_closure_iff]
  intro V hV hgzV
  have hcont_at : ContinuousWithinAt g (closedBall (0 : ℂ) 1) z := c.gc z (hcl_sub hz_cl)
  obtain ⟨W, hW_open, hzW, hW_sub⟩ :=
    mem_nhdsWithin.mp (hcont_at.preimage_mem_nhdsWithin (hV.mem_nhds hgzV))
  obtain ⟨w, hwW, hwU⟩ := _root_.mem_closure_iff.mp hz_cl W hW_open hzW
  exact ⟨g w, hW_sub ⟨hwW, hU_sub hwU⟩, w, hwU, rfl⟩

theorem isChart_subBd_image_of_isOpen_subset_ball {S : Type w} [TopologicalSpace S] [T2Space S]
    {Λ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart (closure Λ) h g) (hΛ_open : IsOpen Λ)
    (hdiscBd : discBd (closure Λ) = subBd Λ)
    {U : Set ℂ} (hU_open : IsOpen U) (hU_sub : U ⊆ ball (0 : ℂ) 1) :
    subBd (g '' U) = g '' (closure U \ U) := by
  have hU_cb : U ⊆ closedBall (0 : ℂ) 1 := hU_sub.trans ball_subset_closedBall
  have hcl_cb : closure U ⊆ closedBall (0 : ℂ) 1 := closure_minimal hU_cb isClosed_closedBall
  rw [subBd_eq_frontier, (isChart_isOpen_image_of_subset_ball c hΛ_open hdiscBd hU_open
    hU_sub).frontier_eq,
    isChart_closure_image_of_subset_closedBall c hU_cb, ← c.g_sdiff hcl_cb hU_cb]

/-- Any nonempty open preconnected set `U ⊆ S` disjoint from `H'.U` with `subBd U ⊆ H'.U` is a
region `U ∈ H'.R`. -/
theorem mem_R_of_isOpen_isPreconnected {S : Type w} [TopologicalSpace S]
    (hS : IsClosedSurface S) {H' : Drawing S} {U : Set S}
    (hU_open : IsOpen U) (hU_ne : U.Nonempty) (hU_conn : IsPreconnected U)
    (hDisj : Disjoint U H'.U) (hBdU : subBd U ⊆ H'.U) :
    U ∈ H'.R := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨x₀, hx₀⟩ := hU_ne
  obtain ⟨r, hr, hx₀r⟩ := GM11.exists_region_of_notMem (Γ := H') (disjoint_left.mp hDisj hx₀)
  have hUr : U ⊆ r := GM11.subset_region hr hU_conn hDisj hx₀ hx₀r
  obtain ⟨_, hclU⟩ := isOpen_disjoint_subBd_and_closure_eq hU_open
  have hrU : r ⊆ U := by
    have hdis_fr : Disjoint r (frontier (closure U)) := by
      refine disjoint_left.mpr fun y hyr hyfr => ?_
      exact GM11.region_subset hr hyr (hBdU (subBd_eq_frontier U ▸ frontier_closure_subset hyfr))
    have hr_cl : r ⊆ closure U :=
      GM14.subset_of_disjoint_frontier (GM11.region_isPreconnected hr) isClosed_closure
        hdis_fr hx₀r (subset_closure hx₀)
    intro y hyr
    rcases hclU ▸ hr_cl hyr with hyU | hyBd
    · exact hyU
    · exact (GM11.region_subset hr hyr (hBdU hyBd)).elim
  exact Subset.antisymm hUr hrU ▸ hr

/-- Decomposition of a closed surface `S` into `P₁ = univ \ Λ` and `P₂ = closure Λ` along a single
2-cell region `Λ ∈ H.R` bounded by an `O`-arc `subBd Λ`. -/
theorem isCappedSplit_single_region {S : Type w} [TopologicalSpace S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {H : Drawing S} {Λ : Set S}
    (hΛ : Λ ∈ H.R) (hOpenDisc : IsOpenDisc Λ) (hOArc : IsOArc (subBd Λ))
    (hCD : IsClosedDisc (closure Λ)) (hdiscBd : discBd (closure Λ) = subBd Λ)
    (hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ) :
    GM12.IsCappedSplit (fun _ : Fin 1 => subBd Λ) (univ \ Λ) (closure Λ)
      (Subtype.val : ↥(univ \ Λ) → S) (fun _ : Fin 1 => Λ) := by
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hΛ_open : IsOpen Λ := GM11.region_isOpen hΛ
  have hsubBd_eq : subBd Λ = closure Λ \ Λ := by
    rw [subBd_eq_frontier, hΛ_open.frontier_eq]
  obtain ⟨hSurf₁, _, hbd₁, _⟩ := compl_open_isSurface hS hΛ_open hOArc hout
  obtain ⟨φD⟩ := id hCD
  obtain ⟨eD₀⟩ := nonempty_disc_homeo
  have hSurf₂ : IsSurface ↥(closure Λ) :=
    isSurface_of_homeo (eD₀.trans φD) (isSurface_model 0 0 1).1
  refine
    { surface := ⟨hS, inferInstance⟩
      isOArc := fun _ => hOArc
      disjoint := fun i j hij => (hij (Subsingleton.elim i j)).elim
      manifold₁ := hSurf₁
      manifold₂ := hSurf₂
      union := by
        ext x
        simp only [mem_union, mem_sdiff, mem_univ, true_and, iff_true]
        exact (em (x ∈ Λ)).symm.imp_right fun hx => subset_closure hx
      inter := by
        rw [iUnion_const, hsubBd_eq]
        ext x
        simp only [mem_inter_iff, mem_sdiff, mem_univ, true_and]
        exact and_comm
      bd₁ := by
        rw [iUnion_const, hbd₁, Subtype.image_preimage_coe]
        refine inter_eq_right.mpr ?_
        rw [hsubBd_eq]
        exact fun x hx => ⟨mem_univ x, hx.2⟩
      bd₂ := by rw [iUnion_const, ← hdiscBd]; rfl
      surface_hat := hS
      isEmbedding := IsEmbedding.subtypeVal
      isOpenDisc := fun _ => hOpenDisc
      bounds := fun _ => by
        rw [Subtype.image_preimage_coe]
        refine (inter_eq_right.mpr ?_).symm
        rw [hsubBd_eq]
        exact fun x hx => ⟨mem_univ x, hx.2⟩
      disjoint_D := fun i j hij => (hij (Subsingleton.elim i j)).elim
      compl := by
        rw [Subtype.range_coe, iUnion_const]
        ext x
        simp only [mem_compl_iff, mem_sdiff, mem_univ, true_and, not_not] }

/-- Image of `pinchVertHomeo k hk '' closedBall 0 1` under `c : IsChart (closure Λ) h g` is a
closed disc `Δ ⊆ closure Λ` containing all vertical chords `g '' vertChord (parallelX k j)` and
meeting `subBd Λ` only at the chord endpoints. -/
theorem exists_pinched_vert_disc {S : Type w} [TopologicalSpace S]
    (hS : IsClosedSurface S) {Λ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart (closure Λ) h g) (hCD : IsClosedDisc (closure Λ))
    (hOArc : IsOArc (subBd Λ)) (hΛ_open : IsOpen Λ)
    (hdiscBd : discBd (closure Λ) = subBd Λ)
    (hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ)
    {k : ℕ} (hk : 3 ≤ k) :
    let Ψ := pinchVertHomeo k hk
    let Δ := g '' (Ψ '' closedBall (0 : ℂ) 1)
    IsClosedDisc Δ ∧
      Δ ⊆ closure Λ ∧
      subBd Δ = g '' (Ψ '' sphere (0 : ℂ) 1) ∧
      IsOArc (subBd Δ) ∧
      (∀ j : Fin (k - 1), g '' vertChord (parallelX k j) ⊆ Δ) ∧
      Δ ∩ subBd Λ =
        ⋃ j : Fin (k - 1), {g ⟨parallelX k j, parallelY k j⟩, g ⟨parallelX k j, -parallelY k j⟩} ∧
      Δ ∩ (univ \ Λ) =
        ⋃ j : Fin (k - 1), {g ⟨parallelX k j, parallelY k j⟩, g ⟨parallelX k j, -parallelY k j⟩} ∧
      univ \ Λ ⊆ closure (univ \ Δ) ∧
      (∀ j : Fin (k - 1),
        (g '' vertChord (parallelX k j)) ∩ closure (univ \ Δ) =
          {g ⟨parallelX k j, parallelY k j⟩, g ⟨parallelX k j, -parallelY k j⟩}) := by
  intro Ψ Δ
  have hΨ_cb : MapsTo Ψ (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) :=
    fun z hz => image_closedBall_pinchVertHomeo_subset k hk ⟨z, hz, rfl⟩
  have hΔ_sub_cl : Δ ⊆ closure Λ :=
    c.g_subset (image_closedBall_pinchVertHomeo_subset k hk)
  let f : S → S := fun x => g (Ψ (h x))
  let f' : S → S := fun y => g (Ψ.symm (h y))
  have hf_cont : ContinuousOn f (closure Λ) :=
    c.gc.comp (Ψ.continuous.continuousOn.comp c.hc c.hm) (hΨ_cb.comp c.hm)
  have hf_image_cl : f '' closure Λ = Δ := by
    rw [← c.g_closedBall]
    ext y
    simp only [f, Δ, mem_image]
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨Ψ (h (g z)), ⟨h (g z), by rwa [c.hg hz], rfl⟩, rfl⟩
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨g z, ⟨z, hz, rfl⟩, by rw [c.hg hz]⟩
  have hf_image_bd : f '' discBd (closure Λ) = g '' (Ψ '' sphere (0 : ℂ) 1) := by
    have : f '' discBd (closure Λ) = g '' (Ψ '' (h '' discBd (closure Λ))) := by
      ext y; simp [f, mem_image]
    rw [this, c.bd]
  have hΨsymm_maps : MapsTo (fun y => Ψ.symm (h y)) Δ (closedBall (0 : ℂ) 1) := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    change Ψ.symm (h (g (Ψ z))) ∈ closedBall (0 : ℂ) 1
    rw [c.hg (hΨ_cb hz), Ψ.symm_apply_apply]
    exact hz
  have hf'_cont : ContinuousOn f' (f '' closure Λ) := by
    rw [hf_image_cl]
    exact c.gc.comp (Ψ.symm.continuous.continuousOn.comp (c.hc.mono hΔ_sub_cl) (mapsTo_univ _ _))
      hΨsymm_maps
  have h_left : LeftInvOn f' f (closure Λ) := fun x hx => by
    change g (Ψ.symm (h (g (Ψ (h x))))) = x
    rw [c.hg (hΨ_cb (c.hm hx)), Ψ.symm_apply_apply, c.gh hx]
  obtain ⟨hΔ_disc, hΔ_discBd⟩ := hCD.image hf_cont hf'_cont h_left
  rw [hf_image_cl] at hΔ_disc
  rw [hf_image_cl, hf_image_bd] at hΔ_discBd
  have hΔ_subBd : subBd Δ = g '' (Ψ '' sphere (0 : ℂ) 1) :=
    (IsClosedDisc.subBd_eq_discBd hS hΔ_disc).trans hΔ_discBd
  have hbd_sub_cl : subBd Λ ⊆ closure Λ := hdiscBd ▸ Surface.discBd_subset (closure Λ)
  have hf_image_subBd : f '' subBd Λ = subBd Δ := by
    rw [← hdiscBd, hf_image_bd, hΔ_subBd]
  have hΔ_oArc : IsOArc (subBd Δ) := by
    rw [← hf_image_subBd]
    exact hOArc.image (hf_cont.mono hbd_sub_cl)
      (hf'_cont.mono (image_mono hbd_sub_cl)) (h_left.mono hbd_sub_cl)
  have hchord_sub_Ψ : ∀ j : Fin (k - 1), vertChord (parallelX k j) ⊆ Ψ '' closedBall (0 : ℂ) 1 := by
    intro j z hz
    exact ⟨z, hz.1, pinchVertHomeo_apply_of_re_eq hk j hz.2⟩
  have hchord_sub_Δ : ∀ j : Fin (k - 1), g '' vertChord (parallelX k j) ⊆ Δ :=
    fun j => image_mono (hchord_sub_Ψ j)
  have hΔ_inter_subBd : Δ ∩ subBd Λ =
      ⋃ j : Fin (k - 1), {g ⟨parallelX k j, parallelY k j⟩, g ⟨parallelX k j, -parallelY k j⟩} := by
    rw [← hdiscBd, ← c.g_sphere,
      ← c.g_inter (image_closedBall_pinchVertHomeo_subset k hk) sphere_subset_closedBall,
      image_closedBall_pinchVertHomeo_inter_sphere k hk, image_iUnion]
    simp only [image_pair]
  have hsubBd_eq_sdiff : subBd Λ = closure Λ \ Λ := by
    rw [subBd_eq_frontier, hΛ_open.frontier_eq]
  have hΔ_inter_compl : Δ ∩ (univ \ Λ) = Δ ∩ subBd Λ := by
    rw [hsubBd_eq_sdiff]
    ext x
    simp only [mem_inter_iff, mem_sdiff, mem_univ, true_and]
    exact ⟨fun ⟨hxΔ, hx_not_Λ⟩ => ⟨hxΔ, hΔ_sub_cl hxΔ, hx_not_Λ⟩,
      fun ⟨hxΔ, _, hx_not_Λ⟩ => ⟨hxΔ, hx_not_Λ⟩⟩
  have hcompl_sub_cl_compl : univ \ Λ ⊆ closure (univ \ Δ) := by
    intro x hx
    by_cases hx_cl : x ∈ closure Λ
    · have hx_out : x ∈ closure (closure Λ)ᶜ := hout x ⟨hx_cl, hx.2⟩
      have hsub_compl : (closure Λ)ᶜ ⊆ univ \ Δ :=
        fun y hy => ⟨mem_univ y, fun hyΔ => hy (hΔ_sub_cl hyΔ)⟩
      exact closure_mono hsub_compl hx_out
    · exact subset_closure ⟨mem_univ x, fun hxΔ => hx_cl (hΔ_sub_cl hxΔ)⟩
  have hchord_inter_compl : ∀ j : Fin (k - 1),
      (g '' vertChord (parallelX k j)) ∩ closure (univ \ Δ) =
        {g ⟨parallelX k j, parallelY k j⟩, g ⟨parallelX k j, -parallelY k j⟩} := by
    intro j
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨z, hz, rfl⟩, hgz_cl⟩
      have hz_Ψ : Ψ z = z := pinchVertHomeo_apply_of_re_eq hk j hz.2
      have hgz_Δ : g z ∈ Δ := hchord_sub_Δ j ⟨z, hz, rfl⟩
      have hgz_bdΔ : g z ∈ subBd Δ := ⟨subset_closure hgz_Δ, hgz_cl⟩
      rw [hΔ_subBd] at hgz_bdΔ
      obtain ⟨w, ⟨u, hu_sph, rfl⟩, hgw_eq⟩ := hgz_bdΔ
      have hwu : Ψ u = z := c.injOn (hΨ_cb (sphere_subset_closedBall hu_sph)) hz.1 hgw_eq
      have hzu : z = u := Ψ.injective (hz_Ψ.trans hwu.symm)
      have hz_inter : z ∈ vertChord (parallelX k j) ∩ sphere (0 : ℂ) 1 :=
        ⟨hz, hzu ▸ hu_sph⟩
      rw [vertChord_inter_sphere (parallelX_sq_add_parallelY_sq j)] at hz_inter
      rcases hz_inter with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rintro x (rfl | rfl)
      · have htop_sph : (⟨parallelX k j, parallelY k j⟩ : ℂ) ∈ sphere (0 : ℂ) 1 :=
          (mem_sphere_unit_iff _).mpr (parallelX_sq_add_parallelY_sq j)
        have htop_bd : g ⟨parallelX k j, parallelY k j⟩ ∈ subBd Λ := by
          rw [← hdiscBd, ← c.g_sphere]
          exact ⟨_, htop_sph, rfl⟩
        exact ⟨⟨_, ⟨sphere_subset_closedBall htop_sph, rfl⟩, rfl⟩,
          hcompl_sub_cl_compl ⟨mem_univ _, (hsubBd_eq_sdiff ▸ htop_bd).2⟩⟩
      · have hbot_sph : (⟨parallelX k j, -parallelY k j⟩ : ℂ) ∈ sphere (0 : ℂ) 1 := by
          rw [mem_sphere_unit_iff]; dsimp; rw [neg_sq]; exact parallelX_sq_add_parallelY_sq j
        have hbot_bd : g ⟨parallelX k j, -parallelY k j⟩ ∈ subBd Λ := by
          rw [← hdiscBd, ← c.g_sphere]
          exact ⟨_, hbot_sph, rfl⟩
        exact ⟨⟨_, ⟨sphere_subset_closedBall hbot_sph, rfl⟩, rfl⟩,
          hcompl_sub_cl_compl ⟨mem_univ _, (hsubBd_eq_sdiff ▸ hbot_bd).2⟩⟩
  exact ⟨hΔ_disc, hΔ_sub_cl, hΔ_subBd, hΔ_oArc, hchord_sub_Δ,
    hΔ_inter_subBd, hΔ_inter_compl.trans hΔ_inter_subBd,
    hcompl_sub_cl_compl, hchord_inter_compl⟩

/-- A path `P_bd` in `H'.interSet (subBd Λ)` with `(P_bd.V ∩ range v).ncard ≤ 2` cannot contain
both endpoints `a j = g ⟨parallelX k j, parallelY k j⟩` and
`b j = g ⟨parallelX k j, -parallelY k j⟩` of a vertical chord, because any preconnected subset of
`subBd Λ` containing both `a j` (positive imaginary part) and `b j` (negative imaginary part) must
contain `g ⟨-1, 0⟩ = v i_k` or `g ⟨1, 0⟩ = v i_last` (zero imaginary part), giving 3 distinct
vertices in `P_bd.V ∩ range v`. -/
theorem no_both_ends_in_bd_path {S : Type w} [TopologicalSpace S] [T2Space S]
    {H' : Drawing S} {Λ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart (closure Λ) h g)
    {k : ℕ} (hk : 3 ≤ k) {v : Fin (2 * k) → S}
    (hv_H'V : ∀ i : Fin (2 * k), v i ∈ H'.V)
    {i_k i_last : Fin (2 * k)}
    (hg_ik : g ⟨-1, 0⟩ = v i_k) (hg_ilast : g ⟨1, 0⟩ = v i_last)
    (hg_a : ∀ j : Fin (k - 1), g ⟨parallelX k j, parallelY k j⟩ = v ⟨j.1, by omega⟩)
    (hg_b : ∀ j : Fin (k - 1), g ⟨parallelX k j, -parallelY k j⟩ = v ⟨2 * k - 2 - j.1, by omega⟩)
    {u₀ v₀ : S} {P_bd : Drawing S}
    (hP_sub : P_bd.IsSubdrawing H')
    (hPU_bd : P_bd.U ⊆ discBd (closure Λ))
    (hP_path : P_bd.IsPathBetween u₀ v₀)
    (huv₀ : u₀ ≠ v₀)
    (hPV_X : (P_bd.V ∩ range v).ncard ≤ 2) :
    ∀ j : Fin (k - 1),
      ¬ (g ⟨parallelX k j, parallelY k j⟩ ∈ P_bd.V ∧
         g ⟨parallelX k j, -parallelY k j⟩ ∈ P_bd.V) := by
  intro j ⟨ha_PV, hb_PV⟩
  set a_j := g ⟨parallelX k j, parallelY k j⟩
  set b_j := g ⟨parallelX k j, -parallelY k j⟩
  have hPU_D : P_bd.U ⊆ closure Λ := hPU_bd.trans (Surface.discBd_subset (closure Λ))
  have hP_line : IsLineWithEnds P_bd.U u₀ v₀ := GM14.isLine_of_isPathBetween hP_path huv₀
  have hPU_conn : IsPreconnected P_bd.U := by
    obtain ⟨γ, hγ_arc, hγ_range, _, _⟩ := hP_line.exists_arc
    exact hγ_range ▸ isPreconnected_range hγ_arc.1
  let im_h : S → ℝ := fun x => (h x).im
  have him_cont : ContinuousOn im_h P_bd.U :=
    (Complex.continuous_im.comp_continuousOn c.hc).mono hPU_D
  have him_conn : IsPreconnected (im_h '' P_bd.U) := hPU_conn.image im_h him_cont
  have htop_cb : (⟨parallelX k j, parallelY k j⟩ : ℂ) ∈ closedBall (0 : ℂ) 1 :=
    sphere_subset_closedBall ((mem_sphere_unit_iff _).mpr (parallelX_sq_add_parallelY_sq j))
  have hbot_cb : (⟨parallelX k j, -parallelY k j⟩ : ℂ) ∈ closedBall (0 : ℂ) 1 := by
    refine sphere_subset_closedBall ((mem_sphere_unit_iff _).mpr ?_)
    dsimp; rw [neg_sq]; exact parallelX_sq_add_parallelY_sq j
  have him_a : im_h a_j = parallelY k j := by
    change (h (g ⟨parallelX k j, parallelY k j⟩)).im = parallelY k j
    rw [c.hg htop_cb]
  have him_b : im_h b_j = -parallelY k j := by
    change (h (g ⟨parallelX k j, -parallelY k j⟩)).im = -parallelY k j
    rw [c.hg hbot_cb]
  have hy_pos : 0 < parallelY k j := parallelY_pos j
  have h0_mem : (0 : ℝ) ∈ im_h '' P_bd.U :=
    him_conn.ordConnected.out ⟨b_j, P_bd.V_subset_U hb_PV, him_b⟩
      ⟨a_j, P_bd.V_subset_U ha_PV, him_a⟩ ⟨by linarith, by linarith⟩
  obtain ⟨z, hz_PU, hz_im⟩ := h0_mem
  have hhz_sph : h z ∈ sphere (0 : ℂ) 1 := c.bd ▸ ⟨z, hPU_bd hz_PU, rfl⟩
  have hhz_re_sq : (h z).re ^ 2 = 1 := by
    have h1 := (mem_sphere_unit_iff (h z)).mp hhz_sph
    change (h z).im = 0 at hz_im
    nlinarith
  have hhz_eq : h z = ⟨-1, 0⟩ ∨ h z = ⟨1, 0⟩ := by
    have hre : (h z).re = -1 ∨ (h z).re = 1 := by
      have : ((h z).re + 1) * ((h z).re - 1) = 0 := by nlinarith
      rcases mul_eq_zero.mp this with h1 | h2
      · exact Or.inl (by linarith)
      · exact Or.inr (by linarith)
    rcases hre with h1 | h2
    · exact Or.inl (Complex.ext h1 hz_im)
    · exact Or.inr (Complex.ext h2 hz_im)
  have hz_eq : z = v i_k ∨ z = v i_last := by
    have hgh : g (h z) = z := c.gh (hPU_D hz_PU)
    rcases hhz_eq with h1 | h2
    · exact Or.inl (by rw [← hgh, h1, hg_ik])
    · exact Or.inr (by rw [← hgh, h2, hg_ilast])
  have hz_X_H'V : z ∈ range v ∧ z ∈ H'.V := by
    rcases hz_eq with rfl | rfl
    · exact ⟨⟨i_k, rfl⟩, hv_H'V i_k⟩
    · exact ⟨⟨i_last, rfl⟩, hv_H'V i_last⟩
  have hz_PV : z ∈ P_bd.V :=
    (isSubdrawing_U_inter_V hP_sub) ▸ ⟨hz_PU, hz_X_H'V.2⟩
  have ha_mem : a_j ∈ P_bd.V ∩ range v :=
    ⟨ha_PV, ⟨⟨j.1, by omega⟩, (hg_a j).symm⟩⟩
  have hb_mem : b_j ∈ P_bd.V ∩ range v :=
    ⟨hb_PV, ⟨⟨2 * k - 2 - j.1, by omega⟩, (hg_b j).symm⟩⟩
  have hz_mem : z ∈ P_bd.V ∩ range v := ⟨hz_PV, hz_X_H'V.1⟩
  have hab_ne : a_j ≠ b_j := fun heq => by
    have := congrArg im_h heq
    linarith [him_a, him_b, hy_pos]
  have haz_ne : a_j ≠ z := fun heq => by
    have := congrArg im_h heq
    linarith [him_a, hz_im, hy_pos]
  have hbz_ne : b_j ≠ z := fun heq => by
    have := congrArg im_h heq
    linarith [him_b, hz_im, hy_pos]
  have hsub3 : ({a_j, b_j, z} : Set S) ⊆ P_bd.V ∩ range v := by
    rintro w (rfl | rfl | rfl)
    · exact ha_mem
    · exact hb_mem
    · exact hz_mem
  have hfin : (P_bd.V ∩ range v).Finite := P_bd.finite_V.subset inter_subset_left
  have hcard3 : ({a_j, b_j, z} : Set S).ncard = 3 := by
    rw [ncard_insert_of_notMem (by simp [hab_ne, haz_ne]),
      ncard_pair hbz_ne]
  have hle := ncard_le_ncard hsub3 hfin
  omega

/-- On the pinched closed disc boundary `subBd Δ = g '' (pinchVertHomeo k hk '' sphere 0 1)`,
the chord endpoints `List.ofFn a ++ (List.ofFn b).reverse` are listed in circular order. -/
theorem isListedInOrderOn_pinched_bd {S : Type w} [TopologicalSpace S] [T2Space S]
    {Λ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart (closure Λ) h g)
    {k : ℕ} (hk : 3 ≤ k) {v : Fin (2 * k) → S}
    (p_circ : Circle ≃ₜ ↥(subBd Λ))
    (hp_circ_v : ∀ i : Fin (2 * k), (p_circ (Circle.exp (parallelModelAngle k i.1))).1 = v i)
    (hg_circ : ∀ w : Circle, g w = (p_circ w).1)
    {Δ : Set S} (hΔ_subBd : subBd Δ = g '' (pinchVertHomeo k hk '' sphere (0 : ℂ) 1)) :
    let a : Fin (k - 1) → S := fun j => v ⟨j.1, by omega⟩
    let b : Fin (k - 1) → S := fun j => v ⟨2 * k - 2 - j.1, by omega⟩
    (List.ofFn a ++ (List.ofFn b).reverse).Nodup ∧
      GM12.IsListedInOrderOn (subBd Δ) (List.ofFn a ++ (List.ofFn b).reverse) := by
  intro a b
  let Ψ := pinchVertHomeo k hk
  let idx : ℕ → Fin (2 * k) := fun m =>
    if hm : m < k - 1 then ⟨m, by omega⟩
    else if hm2 : m < 2 * (k - 1) then ⟨m + 1, by omega⟩
    else ⟨0, by omega⟩
  have hlist_get : ∀ (m : ℕ) (hm : m < (List.ofFn a ++ (List.ofFn b).reverse).length),
      (List.ofFn a ++ (List.ofFn b).reverse)[m]'hm = v (idx m) := by
    intro m hm
    have hlen : (List.ofFn a ++ (List.ofFn b).reverse).length = 2 * (k - 1) := by
      simp [two_mul]
    have hm_lt : m < 2 * (k - 1) := hlen ▸ hm
    by_cases hm1 : m < k - 1
    · rw [List.getElem_append_left (by simp [hm1])]
      simp [a, idx, hm1]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.length_ofFn, List.getElem_reverse, List.getElem_ofFn, b, idx, hm1, hm_lt,
        ↓reduceDIte]
      congr 1
      ext
      dsimp
      omega
  -- Construct `Circle ≃ₜ ↥(subBd Δ)` via `w ↦ g (Ψ w)`.
  have hΨ_cb : MapsTo Ψ (closedBall (0 : ℂ) 1) (closedBall (0 : ℂ) 1) :=
    fun z hz => image_closedBall_pinchVertHomeo_subset k hk ⟨z, hz, rfl⟩
  let φ_map : Circle → ↥(subBd Δ) := fun w =>
    ⟨g (Ψ w), by
      rw [hΔ_subBd]
      exact ⟨Ψ w, ⟨w, mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w), rfl⟩, rfl⟩⟩
  have hφ_cont : Continuous φ_map := by
    refine Continuous.subtype_mk ?_ _
    have h1 : Continuous (fun w : Circle => Ψ w) := Ψ.continuous.comp continuous_subtype_val
    have h2 : ∀ w : Circle, Ψ w ∈ closedBall (0 : ℂ) 1 :=
      fun w => hΨ_cb (sphere_subset_closedBall (mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w)))
    exact c.gc.comp_continuous h1 h2
  have hφ_bij : Function.Bijective φ_map := by
    refine ⟨fun w₁ w₂ heq => ?_, fun ⟨y, hy⟩ => ?_⟩
    · have h1 := congrArg Subtype.val heq
      have hw₁_cb : Ψ w₁ ∈ closedBall (0 : ℂ) 1 :=
        hΨ_cb (sphere_subset_closedBall (mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w₁)))
      have hw₂_cb : Ψ w₂ ∈ closedBall (0 : ℂ) 1 :=
        hΨ_cb (sphere_subset_closedBall (mem_sphere_zero_iff_norm.mpr (Circle.norm_coe w₂)))
      exact Subtype.ext (Ψ.injective (c.injOn hw₁_cb hw₂_cb h1))
    · rw [hΔ_subBd] at hy
      obtain ⟨_, ⟨z, hz_sph, rfl⟩, rfl⟩ := hy
      exact ⟨⟨z, hz_sph⟩, Subtype.ext rfl⟩
  let f_Δ : Circle ≃ₜ ↥(subBd Δ) :=
    hφ_cont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective φ_map hφ_bij)
  have hf_Δ_val : ∀ w : Circle, (f_Δ w).1 = g (Ψ w) := fun _ => rfl
  have hk1 : 1 ≤ k := by omega
  let t_ab : ℕ → ℝ := fun m =>
    if m < k - 1 then parallelModelAngle k m
    else if m < 2 * (k - 1) then parallelModelAngle k (m + 1)
    else parallelModelAngle k 0 + 2 * Real.pi + (m : ℝ)
  have ht_mono : StrictMono t_ab := by
    have hmono₀ := strictMono_parallelModelAngle hk1
    have hbd₀ := parallelModelAngle_lt_add_two_pi hk1
    intro m₁ m₂ hm
    dsimp [t_ab]
    split_ifs with h1 h2 h3 h4 h5 <;> try omega
    · exact hmono₀ hm
    · exact hmono₀ (by omega)
    · have := hbd₀ m₁ (by omega)
      linarith
    · exact hmono₀ (by omega)
    · have := hbd₀ (m₁ + 1) (by omega)
      linarith
    · have : (m₁ : ℝ) < (m₂ : ℝ) := Nat.cast_lt.mpr hm
      linarith
  have ht_bd : ∀ m < (List.ofFn a ++ (List.ofFn b).reverse).length,
      t_ab m < t_ab 0 + 2 * Real.pi := by
    intro m hm
    have hlen : (List.ofFn a ++ (List.ofFn b).reverse).length = 2 * (k - 1) := by
      simp [two_mul]
    have hm_lt : m < 2 * (k - 1) := hlen ▸ hm
    have ht0 : t_ab 0 = parallelModelAngle k 0 := by
      dsimp [t_ab]; rw [ite_eq_left (by omega)]
    rw [ht0]
    dsimp [t_ab]
    split_ifs with h1
    · exact parallelModelAngle_lt_add_two_pi hk1 m (by omega)
    · exact parallelModelAngle_lt_add_two_pi hk1 (m + 1) (by omega)
  have ht_val : ∀ (m : ℕ) (hm : m < (List.ofFn a ++ (List.ofFn b).reverse).length),
      (f_Δ (Circle.exp (t_ab m))).1 = (List.ofFn a ++ (List.ofFn b).reverse)[m]'hm := by
    intro m hm
    rw [hlist_get m hm, hf_Δ_val]
    have hlen : (List.ofFn a ++ (List.ofFn b).reverse).length = 2 * (k - 1) := by
      simp [two_mul]
    have hm_lt : m < 2 * (k - 1) := hlen ▸ hm
    by_cases hm1 : m < k - 1
    · have ht_m : t_ab m = parallelModelAngle k m := by
        dsimp [t_ab]; rw [ite_eq_left hm1]
      have hidx_m : idx m = ⟨m, by omega⟩ := by
        dsimp [idx]; rw [dite_eq_left hm1]
      rw [ht_m, hidx_m]
      let j : Fin (k - 1) := ⟨m, hm1⟩
      have hexp : (Circle.exp (parallelModelAngle k j.1) : ℂ) = ⟨parallelX k j, parallelY k j⟩ :=
        circle_exp_parallelModelAngle_top j
      have hΨ_fix : Ψ (Circle.exp (parallelModelAngle k j.1)) =
          Circle.exp (parallelModelAngle k j.1) := by
        rw [hexp]
        exact pinchVertHomeo_apply_of_re_eq hk j rfl
      change g (Ψ (Circle.exp (parallelModelAngle k j.1))) = v ⟨j.1, by omega⟩
      rw [hΨ_fix, hg_circ]
      exact hp_circ_v ⟨j.1, by omega⟩
    · have ht_m : t_ab m = parallelModelAngle k (m + 1) := by
        dsimp [t_ab]; rw [ite_eq_right hm1, ite_eq_left hm_lt]
      have hidx_m : idx m = ⟨m + 1, by omega⟩ := by
        dsimp [idx]; rw [dite_eq_right hm1, dite_eq_left hm_lt]
      rw [ht_m, hidx_m]
      let j : Fin (k - 1) := ⟨2 * k - 3 - m, by omega⟩
      have hj_sub : 2 * k - 2 - j.1 = m + 1 := by dsimp [j]; omega
      have hexp : (Circle.exp (parallelModelAngle k (m + 1)) : ℂ) =
          ⟨parallelX k j, -parallelY k j⟩ := by
        rw [← hj_sub]
        exact circle_exp_parallelModelAngle_bot j
      have hΨ_fix : Ψ (Circle.exp (parallelModelAngle k (m + 1))) =
          Circle.exp (parallelModelAngle k (m + 1)) := by
        rw [hexp]
        exact pinchVertHomeo_apply_of_re_eq hk j rfl
      change g (Ψ (Circle.exp (parallelModelAngle k (m + 1)))) = v ⟨m + 1, by omega⟩
      rw [hΨ_fix, hg_circ]
      exact hp_circ_v ⟨m + 1, by omega⟩
  have hOrd : GM12.IsListedInOrderOn (subBd Δ) (List.ofFn a ++ (List.ofFn b).reverse) :=
    ⟨f_Δ, t_ab, ht_mono, ht_bd, ht_val⟩
  -- Deduce `Nodup` from `ht_val` and injectivity on `[t_ab 0, t_ab 0 + 2π)`.
  have hNodup : (List.ofFn a ++ (List.ofFn b).reverse).Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro ⟨m₁, hm₁⟩ ⟨m₂, hm₂⟩ heq
    apply Fin.ext
    dsimp at heq
    rw [← ht_val m₁ hm₁, ← ht_val m₂ hm₂] at heq
    have h_exp : Circle.exp (t_ab m₁) = Circle.exp (t_ab m₂) :=
      f_Δ.injective (Subtype.ext heq)
    have h_t_eq : t_ab m₁ = t_ab m₂ :=
      eq_of_circle_exp_eq_of_mem_Ico
        ⟨ht_mono.monotone (Nat.zero_le m₁), ht_bd m₁ hm₁⟩
        ⟨ht_mono.monotone (Nat.zero_le m₂), ht_bd m₂ hm₂⟩ h_exp
    exact ht_mono.injective h_t_eq
  exact ⟨hNodup, hOrd⟩

theorem leftSphereArc_subset_sphere (r : ℝ) : leftSphereArc r ⊆ sphere (0 : ℂ) 1 :=
  fun _ hz => hz.1

theorem rightSphereArc_subset_sphere (r : ℝ) : rightSphereArc r ⊆ sphere (0 : ℂ) 1 :=
  fun _ hz => hz.1

theorem vertChord_subset_closedBall (r : ℝ) : vertChord r ⊆ closedBall (0 : ℂ) 1 :=
  fun _ hz => hz.1

theorem leftSphereArc_inter_vertChord {r y : ℝ} (hry : r ^ 2 + y ^ 2 = 1) :
    leftSphereArc r ∩ vertChord r = {⟨r, y⟩, ⟨r, -y⟩} := by
  ext z
  simp only [mem_inter_iff, leftSphereArc, vertChord, mem_ofPred_eq,
    mem_sphere_unit_iff, mem_closedBall_unit_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨hsph, _⟩, ⟨_, rfl⟩⟩
    have him : z.im ^ 2 = y ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with h | h
    · left; exact Complex.ext rfl h
    · right; exact Complex.ext rfl h
  · rintro (rfl | rfl)
    · exact ⟨⟨by linarith, le_rfl⟩, ⟨by linarith, rfl⟩⟩
    · exact ⟨⟨by dsimp; linarith, le_rfl⟩, ⟨by dsimp; linarith, rfl⟩⟩

theorem rightSphereArc_inter_vertChord {r y : ℝ} (hry : r ^ 2 + y ^ 2 = 1) :
    rightSphereArc r ∩ vertChord r = {⟨r, y⟩, ⟨r, -y⟩} := by
  ext z
  simp only [mem_inter_iff, rightSphereArc, vertChord, mem_ofPred_eq,
    mem_sphere_unit_iff, mem_closedBall_unit_iff, mem_insert_iff, mem_singleton_iff]
  constructor
  · rintro ⟨⟨hsph, _⟩, ⟨_, rfl⟩⟩
    have him : z.im ^ 2 = y ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp him with h | h
    · left; exact Complex.ext rfl h
    · right; exact Complex.ext rfl h
  · rintro (rfl | rfl)
    · exact ⟨⟨by linarith, le_rfl⟩, ⟨by linarith, rfl⟩⟩
    · exact ⟨⟨by dsimp; linarith, le_rfl⟩, ⟨by dsimp; linarith, rfl⟩⟩

theorem leftSphereArcMap_zero (θ₀ : ℝ) :
    leftSphereArcMap θ₀ 0 = (Circle.exp θ₀ : ℂ) := by
  unfold leftSphereArcMap
  simp

theorem leftSphereArcMap_one (θ₀ : ℝ) :
    leftSphereArcMap θ₀ 1 = (Circle.exp (2 * Real.pi - θ₀) : ℂ) := by
  unfold leftSphereArcMap
  congr 2
  push_cast
  ring

theorem rightSphereArcMap_zero (θ₀ : ℝ) :
    rightSphereArcMap θ₀ 0 = (Circle.exp (2 * Real.pi - θ₀) : ℂ) := by
  unfold rightSphereArcMap
  simp

theorem rightSphereArcMap_one (θ₀ : ℝ) :
    rightSphereArcMap θ₀ 1 = (Circle.exp θ₀ : ℂ) := by
  unfold rightSphereArcMap
  have h : (2 * Real.pi - θ₀) + 2 * θ₀ * ((1 : unitInterval) : ℝ) = θ₀ + 2 * Real.pi := by
    push_cast; ring
  rw [h, Circle.exp_add, Circle.exp_two_pi, mul_one]

/-- `subBd r₁ = g '' leftSphereArc x_last ∪ L j_last` is an `O`-arc, and any four vertices
`w₁, w₂, w₃, w₄ ∈ H.V ∩ subBd Λ` appearing in circular order between `v ⟨k - 2, _⟩` and
`v ⟨k, _⟩` on `subBd Λ` occur in circuit order on `H'.interSet (subBd r₁)`. -/
theorem occurInCircuitOrder_leftCap {S : Type w} [TopologicalSpace S] [T2Space S]
    {H H' : Drawing S} {Λ r₁ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart (closure Λ) h g)
    {k : ℕ} (hk : 3 ≤ k) {v : Fin (2 * k) → S}
    (p_circ : Circle ≃ₜ ↥(subBd Λ))
    (hp_circ_v : ∀ i : Fin (2 * k), (p_circ (Circle.exp (parallelModelAngle k i.1))).1 = v i)
    (hg_circ : ∀ w : Circle, g w = (p_circ w).1)
    (hSub_H : H.IsSubdrawing H')
    (hr₁_bd : subBd r₁ =
      g '' leftSphereArc (parallelX k ⟨k - 2, by omega⟩) ∪
        g '' vertChord (parallelX k ⟨k - 2, by omega⟩)) :
    IsOArc (subBd r₁) ∧
      ((H'.interSet (subBd r₁)).U = subBd r₁ →
       ∀ w₁ w₂ w₃ w₄ : S,
        w₁ ∈ H.V ∩ subBd Λ → w₂ ∈ H.V ∩ subBd Λ →
        w₃ ∈ H.V ∩ subBd Λ → w₄ ∈ H.V ∩ subBd Λ →
        GM12.IsListedInOrderOn (subBd Λ)
          (List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁, w₂, w₃, w₄] ++
            List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)) →
        w₁ ∈ (H'.interSet (subBd r₁)).V ∧ w₂ ∈ (H'.interSet (subBd r₁)).V ∧
        w₃ ∈ (H'.interSet (subBd r₁)).V ∧ w₄ ∈ (H'.interSet (subBd r₁)).V ∧
        OccurInCircuitOrder (H'.interSet (subBd r₁)) w₁ w₂ w₃ w₄) := by
  have hk1 : 1 ≤ k := by omega
  let j_last : Fin (k - 1) := ⟨k - 2, by omega⟩
  let θ_last : ℝ := parallelModelAngle k j_last.1
  obtain ⟨hθ_last_pos, hθ_last_pi⟩ := parallelModelAngle_mem_Ioo_pi j_last.2
  let x_last : ℝ := parallelX k j_last
  let y_last : ℝ := parallelY k j_last
  let a_last : S := g ⟨x_last, y_last⟩
  let b_last : S := g ⟨x_last, -y_last⟩
  let a₁ : unitInterval → S := g ∘ leftSphereArcMap θ_last
  have hArc_left : IsArcMap (leftSphereArcMap θ_last) :=
    isArcMap_leftSphereArcMap hθ_last_pos hθ_last_pi
  have hRange_left : range (leftSphereArcMap θ_last) = leftSphereArc x_last :=
    range_leftSphereArcMap hθ_last_pos hθ_last_pi
  have hLeft_cb : leftSphereArc x_last ⊆ closedBall (0 : ℂ) 1 :=
    (leftSphereArc_subset_sphere x_last).trans sphere_subset_closedBall
  have hmaps_left : ∀ t : unitInterval,
      leftSphereArcMap θ_last t ∈ closedBall (0 : ℂ) 1 :=
    fun t => hLeft_cb (hRange_left ▸ ⟨t, rfl⟩)
  have ha₁_arc : IsArcMap a₁ := by
    refine ⟨c.gc.comp_continuous hArc_left.1 hmaps_left, fun t₁ t₂ heq => ?_⟩
    exact hArc_left.2 (c.injOn (hmaps_left t₁) (hmaps_left t₂) heq)
  have ha₁_range : range a₁ = g '' leftSphereArc x_last := by
    rw [range_comp, hRange_left]
  have ha₁_0 : a₁ 0 = a_last := by
    change g (leftSphereArcMap θ_last 0) = a_last
    rw [leftSphereArcMap_zero]
    exact congrArg g (circle_exp_parallelModelAngle_top j_last)
  have ha₁_1 : a₁ 1 = b_last := by
    change g (leftSphereArcMap θ_last 1) = b_last
    rw [leftSphereArcMap_one, ← parallelModelAngle_partner j_last.2]
    exact congrArg g (circle_exp_parallelModelAngle_bot j_last)
  have hL_line : IsLineWithEnds (g '' vertChord x_last) a_last b_last :=
    (isLineWithEnds_image_vertChord c (parallelX_sq_add_parallelY_sq j_last)
      (parallelY_pos j_last)).1
  obtain ⟨a₂, ha₂_arc, ha₂_range, ha₂_0, ha₂_1⟩ := hL_line.exists_arc
  have hinter_arcs : range a₁ ∩ range a₂ = {a_last, b_last} := by
    rw [ha₁_range, ha₂_range, ← c.g_inter hLeft_cb (vertChord_subset_closedBall x_last),
      leftSphereArc_inter_vertChord (parallelX_sq_add_parallelY_sq j_last), image_pair]
  have h01 : ∀ s t, a₁ s = a₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t hst
    have hmem : a₁ s ∈ range a₁ ∩ range a₂ := ⟨⟨s, rfl⟩, ⟨t, hst.symm⟩⟩
    rw [hinter_arcs] at hmem
    rcases hmem with h_eq | h_eq
    · left
      have hs : s = 0 := ha₁_arc.2 (h_eq.trans ha₁_0.symm)
      have ht : t = 0 := ha₂_arc.2 (hst.symm.trans (h_eq.trans ha₂_0.symm))
      exact ⟨hs, ht⟩
    · right
      have hs : s = 1 := ha₁_arc.2 (h_eq.trans ha₁_1.symm)
      have ht : t = 1 := ha₂_arc.2 (hst.symm.trans (h_eq.trans ha₂_1.symm))
      exact ⟨hs, ht⟩
  have hsubBd_union : subBd r₁ = range a₁ ∪ range a₂ := by
    rw [hr₁_bd, ha₁_range, ha₂_range]
  have htwo := oArc_and_occurInCircuitOrder_of_two_arcs ha₁_arc ha₂_arc
    (ha₁_0.trans ha₂_0.symm) (ha₁_1.trans ha₂_1.symm) h01
  refine ⟨hsubBd_union ▸ htwo.1, fun hU_r₁ w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄ hl₁_ord => ?_⟩
  let A_list := List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩)
  let B_list := List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)
  set l₁ := A_list ++ [w₁, w₂, w₃, w₄] ++ B_list
  have hlen_A : A_list.length = k - 1 := List.length_ofFn
  have hlen_B : B_list.length = k := List.length_ofFn
  have hlen_l₁ : l₁.length = 2 * k + 3 := by
    simp [l₁, A_list, B_list]; omega
  have hl₁_0 : (p_circ (Circle.exp (parallelModelAngle k 0))).1 = l₁[0]'(by omega) := by
    have hget0 : l₁[0]'(by omega) = v ⟨0, by omega⟩ := by
      dsimp [l₁]
      rw [List.getElem_append_left (by simp [A_list]),
        List.getElem_append_left (by simp [A_list]; omega)]
      simp [A_list]
    rw [hget0]
    exact hp_circ_v ⟨0, by omega⟩
  have hl₁_1 : (p_circ (Circle.exp (parallelModelAngle k 1))).1 = l₁[1]'(by omega) := by
    have hget1 : l₁[1]'(by omega) = v ⟨1, by omega⟩ := by
      dsimp [l₁]
      rw [List.getElem_append_left (by simp [A_list]),
        List.getElem_append_left (by simp [A_list]; omega)]
      simp [A_list]
    rw [hget1]
    exact hp_circ_v ⟨1, by omega⟩
  have hl₁_kp3 : (p_circ (Circle.exp (parallelModelAngle k k))).1 = l₁[k + 3]'(by omega) := by
    have hget : l₁[k + 3]'(by omega) = v ⟨k, by omega⟩ := by
      dsimp [l₁]
      rw [List.getElem_append_right (by simp [A_list]; omega)]
      have hlen_AW : (A_list ++ [w₁, w₂, w₃, w₄]).length = k + 3 := by simp [A_list]; omega
      simp only [hlen_AW, Nat.sub_self, B_list, List.getElem_ofFn, add_zero]
    rw [hget]
    exact hp_circ_v ⟨k, by omega⟩
  obtain ⟨θ, hθ_mono, hθ_0, hθ_bd, hθ_val, hθ_uniq⟩ :=
    exists_increasing_angles_of_isListedInOrderOn p_circ (l := l₁) hl₁_ord
      (idx₂ := k + 3) (by omega) (by omega)
      (strictMono_parallelModelAngle hk1 Nat.zero_lt_one)
      (strictMono_parallelModelAngle hk1 (by omega : 1 < k))
      (parallelModelAngle_lt_add_two_pi hk1 k (by omega))
      hl₁_0 hl₁_1 hl₁_kp3
  have hmodel_Ico : ∀ m < 2 * k,
      parallelModelAngle k m ∈ Ico (parallelModelAngle k 0) (parallelModelAngle k 0 + 2 * Real.pi)
        :=
    fun m hm => ⟨(strictMono_parallelModelAngle hk1).monotone (Nat.zero_le m),
      parallelModelAngle_lt_add_two_pi hk1 m hm⟩
  have hθ_km2 : θ (k - 2) = parallelModelAngle k (k - 2) := by
    have hget : l₁[k - 2]'(by omega) = v ⟨k - 2, by omega⟩ := by
      dsimp [l₁]
      rw [List.getElem_append_left (by simp [A_list]; omega),
        List.getElem_append_left (by simp [A_list]; omega)]
      simp [A_list]
    exact hθ_uniq (k - 2) (by omega) (parallelModelAngle k (k - 2)) (hmodel_Ico (k - 2) (by omega))
      ((hp_circ_v ⟨k - 2, by omega⟩).trans hget.symm)
  have hθ_kp3 : θ (k + 3) = parallelModelAngle k k :=
    hθ_uniq (k + 3) (by omega) (parallelModelAngle k k) (hmodel_Ico k (by omega)) hl₁_kp3
  have hget_w : l₁[k - 1]'(by omega) = w₁ ∧ l₁[k]'(by omega) = w₂ ∧
      l₁[k + 1]'(by omega) = w₃ ∧ l₁[k + 2]'(by omega) = w₄ := by
    have h_elem : ∀ (i m : ℕ) (hi : i < l₁.length) (hm : m < 4),
        i = k - 1 + m → l₁[i]'hi = [w₁, w₂, w₃, w₄][m]'hm := by
      rintro _ m hi hm rfl
      dsimp [l₁]
      rw [List.getElem_append_left (by simp [A_list]; omega),
        List.getElem_append_right (by simp [A_list])]
      simp only [hlen_A, Nat.add_sub_cancel_left]
    exact ⟨h_elem (k - 1) 0 (by omega) (by omega) (by omega),
      h_elem k 1 (by omega) (by omega) (by omega),
      h_elem (k + 1) 2 (by omega) (by omega) (by omega),
      h_elem (k + 2) 3 (by omega) (by omega) (by omega)⟩
  have hlt1 : parallelModelAngle k (k - 2) < θ (k - 1) :=
    hθ_km2 ▸ hθ_mono (by omega : k - 2 < k - 1)
  have hlt2 : θ (k - 1) < θ k := hθ_mono (by omega)
  have hlt3 : θ k < θ (k + 1) := hθ_mono (by omega)
  have hlt4 : θ (k + 1) < θ (k + 2) := hθ_mono (by omega)
  have hlt5 : θ (k + 2) < parallelModelAngle k k :=
    hθ_kp3 ▸ hθ_mono (by omega : k + 2 < k + 3)
  have h_partner_k : parallelModelAngle k k = 2 * Real.pi - θ_last := by
    have h := parallelModelAngle_partner j_last.2
    have hsub : 2 * k - 2 - j_last.1 = k := by dsimp [j_last]; omega
    rwa [hsub] at h
  let Δθ : ℝ := 2 * Real.pi - 2 * θ_last
  have hΔθ_eq : Δθ = parallelModelAngle k k - parallelModelAngle k (k - 2) := by
    dsimp [Δθ, θ_last, j_last]
    linarith [h_partner_k]
  have hΔθ_pos : 0 < Δθ := by
    rw [hΔθ_eq]; linarith
  let s₁_r : ℝ := (θ (k - 1) - θ_last) / Δθ
  let s₂_r : ℝ := (θ k - θ_last) / Δθ
  let s₃_r : ℝ := (θ (k + 1) - θ_last) / Δθ
  let s₄_r : ℝ := (θ (k + 2) - θ_last) / Δθ
  have hs_ord : 0 < s₁_r ∧ s₁_r < s₂_r ∧ s₂_r < s₃_r ∧ s₃_r < s₄_r ∧ s₄_r < 1 :=
    ⟨div_pos (by dsimp [θ_last, j_last]; linarith) hΔθ_pos,
     div_lt_div_of_pos_right (by linarith) hΔθ_pos,
     div_lt_div_of_pos_right (by linarith) hΔθ_pos,
     div_lt_div_of_pos_right (by linarith) hΔθ_pos,
     (div_lt_one hΔθ_pos).mpr (by rw [hΔθ_eq]; dsimp [θ_last, j_last]; linarith)⟩
  let s₁ : unitInterval := ⟨s₁_r, ⟨hs_ord.1.le, by linarith [hs_ord.2.1, hs_ord.2.2.1,
    hs_ord.2.2.2.1, hs_ord.2.2.2.2]⟩⟩
  let s₂ : unitInterval := ⟨s₂_r, ⟨by linarith [hs_ord.1, hs_ord.2.1], by linarith [hs_ord.2.2.1,
    hs_ord.2.2.2.1, hs_ord.2.2.2.2]⟩⟩
  let s₃ : unitInterval := ⟨s₃_r, ⟨by linarith [hs_ord.1, hs_ord.2.1, hs_ord.2.2.1], by linarith
    [hs_ord.2.2.2.1, hs_ord.2.2.2.2]⟩⟩
  let s₄ : unitInterval := ⟨s₄_r, ⟨by linarith [hs_ord.1, hs_ord.2.1, hs_ord.2.2.1,
    hs_ord.2.2.2.1], hs_ord.2.2.2.2.le⟩⟩
  have ha₁_apply : ∀ (m : ℕ) (hm : m < l₁.length) (s : unitInterval),
      (s : ℝ) = (θ m - θ_last) / Δθ → a₁ s = l₁[m]'hm := by
    intro m hm s hs
    change g (Circle.exp (θ_last + Δθ * (s : ℝ))) = l₁[m]'hm
    rw [hs]
    have h_angle : θ_last + Δθ * ((θ m - θ_last) / Δθ) = θ m := by
      rw [mul_div_cancel₀ _ (ne_of_gt hΔθ_pos)]
      ring
    rw [h_angle, hg_circ, hθ_val m hm]
  have hs₁_val : a₁ s₁ = w₁ := (ha₁_apply (k - 1) (by omega) s₁ rfl).trans hget_w.1
  have hs₂_val : a₁ s₂ = w₂ := (ha₁_apply k (by omega) s₂ rfl).trans hget_w.2.1
  have hs₃_val : a₁ s₃ = w₃ := (ha₁_apply (k + 1) (by omega) s₃ rfl).trans hget_w.2.2.1
  have hs₄_val : a₁ s₄ = w₄ := (ha₁_apply (k + 2) (by omega) s₄ rfl).trans hget_w.2.2.2
  have hcl_r₁ : IsClosed (subBd r₁) := isClosed_closure.inter isClosed_closure
  have hw_V : ∀ {w : S} {s : unitInterval}, w ∈ H.V ∩ subBd Λ → a₁ s = w →
      w ∈ (H'.interSet (subBd r₁)).V := by
    intro w s hw has
    rw [interSet_V_of_isClosed H' hcl_r₁]
    refine ⟨hSub_H.1 hw.1, ?_⟩
    rw [hsubBd_union]
    exact Or.inl ⟨s, has⟩
  refine ⟨hw_V hw₁ hs₁_val, hw_V hw₂ hs₂_val, hw_V hw₃ hs₃_val, hw_V hw₄ hs₄_val, ?_⟩
  rw [← hs₁_val, ← hs₂_val, ← hs₃_val, ← hs₄_val]
  exact htwo.2 (hU_r₁.trans hsubBd_union)
    (show s₁ < s₂ from hs_ord.2.1)
    (show s₂ < s₃ from hs_ord.2.2.1)
    (show s₃ < s₄ from hs_ord.2.2.2.1)

/-- `subBd r₂ = g '' rightSphereArc x_first ∪ L 0` is an `O`-arc, and any four vertices
`u₁, u₂, u₃, u₄ ∈ H.V ∩ subBd Λ` appearing in circular order after `v ⟨2 * k - 2, _⟩` on `subBd Λ`
occur in circuit order on `H'.interSet (subBd r₂)`. -/
theorem occurInCircuitOrder_rightCap {S : Type w} [TopologicalSpace S] [T2Space S]
    {H H' : Drawing S} {Λ r₂ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart (closure Λ) h g)
    {k : ℕ} (hk : 3 ≤ k) {v : Fin (2 * k) → S}
    (p_circ : Circle ≃ₜ ↥(subBd Λ))
    (hp_circ_v : ∀ i : Fin (2 * k), (p_circ (Circle.exp (parallelModelAngle k i.1))).1 = v i)
    (hg_circ : ∀ w : Circle, g w = (p_circ w).1)
    (hSub_H : H.IsSubdrawing H')
    (hr₂_bd : subBd r₂ =
      g '' rightSphereArc (parallelX k ⟨0, by omega⟩) ∪
        g '' vertChord (parallelX k ⟨0, by omega⟩)) :
    IsOArc (subBd r₂) ∧
      ((H'.interSet (subBd r₂)).U = subBd r₂ →
       ∀ u₁ u₂ u₃ u₄ : S,
        u₁ ∈ H.V ∩ subBd Λ → u₂ ∈ H.V ∩ subBd Λ →
        u₃ ∈ H.V ∩ subBd Λ → u₄ ∈ H.V ∩ subBd Λ →
        GM12.IsListedInOrderOn (subBd Λ)
          (List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩) ++ [u₁, u₂, u₃, u₄]) →
        u₁ ∈ (H'.interSet (subBd r₂)).V ∧ u₂ ∈ (H'.interSet (subBd r₂)).V ∧
        u₃ ∈ (H'.interSet (subBd r₂)).V ∧ u₄ ∈ (H'.interSet (subBd r₂)).V ∧
        OccurInCircuitOrder (H'.interSet (subBd r₂)) u₁ u₂ u₃ u₄) := by
  have hk1 : 1 ≤ k := by omega
  let j_first : Fin (k - 1) := ⟨0, by omega⟩
  let θ_first : ℝ := parallelModelAngle k j_first.1
  obtain ⟨hθ_first_pos, hθ_first_pi⟩ := parallelModelAngle_mem_Ioo_pi j_first.2
  let x_first : ℝ := parallelX k j_first
  let y_first : ℝ := parallelY k j_first
  let a_first : S := g ⟨x_first, y_first⟩
  let b_first : S := g ⟨x_first, -y_first⟩
  let a₁ : unitInterval → S := g ∘ rightSphereArcMap θ_first
  have hArc_right : IsArcMap (rightSphereArcMap θ_first) :=
    isArcMap_rightSphereArcMap hθ_first_pos hθ_first_pi
  have hRange_right : range (rightSphereArcMap θ_first) = rightSphereArc x_first :=
    range_rightSphereArcMap hθ_first_pos hθ_first_pi
  have hRight_cb : rightSphereArc x_first ⊆ closedBall (0 : ℂ) 1 :=
    (rightSphereArc_subset_sphere x_first).trans sphere_subset_closedBall
  have hmaps_right : ∀ t : unitInterval,
      rightSphereArcMap θ_first t ∈ closedBall (0 : ℂ) 1 :=
    fun t => hRight_cb (hRange_right ▸ ⟨t, rfl⟩)
  have ha₁_arc : IsArcMap a₁ := by
    refine ⟨c.gc.comp_continuous hArc_right.1 hmaps_right, fun t₁ t₂ heq => ?_⟩
    exact hArc_right.2 (c.injOn (hmaps_right t₁) (hmaps_right t₂) heq)
  have ha₁_range : range a₁ = g '' rightSphereArc x_first := by
    rw [range_comp, hRange_right]
  have ha₁_0 : a₁ 0 = b_first := by
    change g (rightSphereArcMap θ_first 0) = b_first
    rw [rightSphereArcMap_zero, ← parallelModelAngle_partner j_first.2]
    exact congrArg g (circle_exp_parallelModelAngle_bot j_first)
  have ha₁_1 : a₁ 1 = a_first := by
    change g (rightSphereArcMap θ_first 1) = a_first
    rw [rightSphereArcMap_one]
    exact congrArg g (circle_exp_parallelModelAngle_top j_first)
  have hL_line : IsLineWithEnds (g '' vertChord x_first) b_first a_first :=
    ((isLineWithEnds_image_vertChord c (parallelX_sq_add_parallelY_sq j_first)
      (parallelY_pos j_first)).1).symm
  obtain ⟨a₂, ha₂_arc, ha₂_range, ha₂_0, ha₂_1⟩ := hL_line.exists_arc
  have hinter_arcs : range a₁ ∩ range a₂ = {b_first, a_first} := by
    rw [ha₁_range, ha₂_range, ← c.g_inter hRight_cb (vertChord_subset_closedBall x_first),
      rightSphereArc_inter_vertChord (parallelX_sq_add_parallelY_sq j_first), image_pair,
      pair_comm]
  have h01 : ∀ s t, a₁ s = a₂ t → (s = 0 ∧ t = 0) ∨ (s = 1 ∧ t = 1) := by
    intro s t hst
    have hmem : a₁ s ∈ range a₁ ∩ range a₂ := ⟨⟨s, rfl⟩, ⟨t, hst.symm⟩⟩
    rw [hinter_arcs] at hmem
    rcases hmem with h_eq | h_eq
    · left
      have hs : s = 0 := ha₁_arc.2 (h_eq.trans ha₁_0.symm)
      have ht : t = 0 := ha₂_arc.2 (hst.symm.trans (h_eq.trans ha₂_0.symm))
      exact ⟨hs, ht⟩
    · right
      have hs : s = 1 := ha₁_arc.2 (h_eq.trans ha₁_1.symm)
      have ht : t = 1 := ha₂_arc.2 (hst.symm.trans (h_eq.trans ha₂_1.symm))
      exact ⟨hs, ht⟩
  have hsubBd_union : subBd r₂ = range a₁ ∪ range a₂ := by
    rw [hr₂_bd, ha₁_range, ha₂_range]
  have htwo := oArc_and_occurInCircuitOrder_of_two_arcs ha₁_arc ha₂_arc
    (ha₁_0.trans ha₂_0.symm) (ha₁_1.trans ha₂_1.symm) h01
  refine ⟨hsubBd_union ▸ htwo.1, fun hU_r₂ u₁ u₂ u₃ u₄ hu₁ hu₂ hu₃ hu₄ hl₂_ord => ?_⟩
  let A_list := List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩)
  set l₂ := A_list ++ [u₁, u₂, u₃, u₄]
  have hlen_A : A_list.length = 2 * k - 1 := List.length_ofFn
  have hlen_l₂ : l₂.length = 2 * k + 3 := by
    simp [l₂, A_list]; omega
  have hl₂_0 : (p_circ (Circle.exp (parallelModelAngle k 0))).1 = l₂[0]'(by omega) := by
    have hget0 : l₂[0]'(by omega) = v ⟨0, by omega⟩ := by
      dsimp [l₂]
      rw [List.getElem_append_left (by simp [A_list]; omega)]
      simp [A_list]
    rw [hget0]
    exact hp_circ_v ⟨0, by omega⟩
  have hl₂_1 : (p_circ (Circle.exp (parallelModelAngle k 1))).1 = l₂[1]'(by omega) := by
    have hget1 : l₂[1]'(by omega) = v ⟨1, by omega⟩ := by
      dsimp [l₂]
      rw [List.getElem_append_left (by simp [A_list]; omega)]
      simp [A_list]
    rw [hget1]
    exact hp_circ_v ⟨1, by omega⟩
  have hl₂_2 : (p_circ (Circle.exp (parallelModelAngle k 2))).1 = l₂[2]'(by omega) := by
    have hget2 : l₂[2]'(by omega) = v ⟨2, by omega⟩ := by
      dsimp [l₂]
      rw [List.getElem_append_left (by simp [A_list]; omega)]
      simp [A_list]
    rw [hget2]
    exact hp_circ_v ⟨2, by omega⟩
  obtain ⟨θ, hθ_mono, hθ_0, hθ_bd, hθ_val, hθ_uniq⟩ :=
    exists_increasing_angles_of_isListedInOrderOn p_circ (l := l₂) hl₂_ord
      (idx₂ := 2) (by omega) (by omega)
      (strictMono_parallelModelAngle hk1 Nat.zero_lt_one)
      (strictMono_parallelModelAngle hk1 (by omega : 1 < 2))
      (parallelModelAngle_lt_add_two_pi hk1 2 (by omega))
      hl₂_0 hl₂_1 hl₂_2
  have hmodel_Ico : ∀ m < 2 * k,
      parallelModelAngle k m ∈ Ico (parallelModelAngle k 0) (parallelModelAngle k 0 + 2 * Real.pi)
        :=
    fun m hm => ⟨(strictMono_parallelModelAngle hk1).monotone (Nat.zero_le m),
      parallelModelAngle_lt_add_two_pi hk1 m hm⟩
  have hθ_2km2 : θ (2 * k - 2) = parallelModelAngle k (2 * k - 2) := by
    have hget : l₂[2 * k - 2]'(by omega) = v ⟨2 * k - 2, by omega⟩ := by
      dsimp [l₂]
      rw [List.getElem_append_left (by simp [A_list]; omega)]
      simp [A_list]
    exact hθ_uniq (2 * k - 2) (by omega) (parallelModelAngle k (2 * k - 2))
      (hmodel_Ico (2 * k - 2) (by omega)) ((hp_circ_v ⟨2 * k - 2, by omega⟩).trans hget.symm)
  have hget_u : l₂[2 * k - 1]'(by omega) = u₁ ∧ l₂[2 * k]'(by omega) = u₂ ∧
      l₂[2 * k + 1]'(by omega) = u₃ ∧ l₂[2 * k + 2]'(by omega) = u₄ := by
    have h_elem : ∀ (i m : ℕ) (hi : i < l₂.length) (hm : m < 4),
        i = 2 * k - 1 + m → l₂[i]'hi = [u₁, u₂, u₃, u₄][m]'hm := by
      rintro _ m hi hm rfl
      dsimp [l₂]
      rw [List.getElem_append_right (by simp [A_list])]
      simp only [hlen_A, Nat.add_sub_cancel_left]
    exact ⟨h_elem (2 * k - 1) 0 (by omega) (by omega) (by omega),
      h_elem (2 * k) 1 (by omega) (by omega) (by omega),
      h_elem (2 * k + 1) 2 (by omega) (by omega) (by omega),
      h_elem (2 * k + 2) 3 (by omega) (by omega) (by omega)⟩
  have hlt1 : parallelModelAngle k (2 * k - 2) < θ (2 * k - 1) :=
    hθ_2km2 ▸ hθ_mono (by omega : 2 * k - 2 < 2 * k - 1)
  have hlt2 : θ (2 * k - 1) < θ (2 * k) := hθ_mono (by omega)
  have hlt3 : θ (2 * k) < θ (2 * k + 1) := hθ_mono (by omega)
  have hlt4 : θ (2 * k + 1) < θ (2 * k + 2) := hθ_mono (by omega)
  have hlt5 : θ (2 * k + 2) < parallelModelAngle k 0 + 2 * Real.pi :=
    hθ_bd (2 * k + 2) (by omega)
  have h_partner_0 : parallelModelAngle k (2 * k - 2) = 2 * Real.pi - θ_first := by
    have h := parallelModelAngle_partner j_first.2
    have hsub : 2 * k - 2 - j_first.1 = 2 * k - 2 := rfl
    rwa [hsub] at h
  let Δθ : ℝ := 2 * θ_first
  have hΔθ_eq : Δθ = parallelModelAngle k 0 + 2 * Real.pi - parallelModelAngle k (2 * k - 2) := by
    dsimp [Δθ, θ_first, j_first]
    linarith [h_partner_0]
  have hΔθ_pos : 0 < Δθ := by
    rw [hΔθ_eq]; linarith
  let s₁_r : ℝ := (θ (2 * k - 1) - (2 * Real.pi - θ_first)) / Δθ
  let s₂_r : ℝ := (θ (2 * k) - (2 * Real.pi - θ_first)) / Δθ
  let s₃_r : ℝ := (θ (2 * k + 1) - (2 * Real.pi - θ_first)) / Δθ
  let s₄_r : ℝ := (θ (2 * k + 2) - (2 * Real.pi - θ_first)) / Δθ
  have hs_ord : 0 < s₁_r ∧ s₁_r < s₂_r ∧ s₂_r < s₃_r ∧ s₃_r < s₄_r ∧ s₄_r < 1 :=
    ⟨div_pos (by linarith [h_partner_0]) hΔθ_pos,
     div_lt_div_of_pos_right (by linarith) hΔθ_pos,
     div_lt_div_of_pos_right (by linarith) hΔθ_pos,
     div_lt_div_of_pos_right (by linarith) hΔθ_pos,
     (div_lt_one hΔθ_pos).mpr (by rw [hΔθ_eq]; linarith [h_partner_0])⟩
  let s₁ : unitInterval := ⟨s₁_r, ⟨hs_ord.1.le, by linarith [hs_ord.2.1, hs_ord.2.2.1,
    hs_ord.2.2.2.1, hs_ord.2.2.2.2]⟩⟩
  let s₂ : unitInterval := ⟨s₂_r, ⟨by linarith [hs_ord.1, hs_ord.2.1], by linarith [hs_ord.2.2.1,
    hs_ord.2.2.2.1, hs_ord.2.2.2.2]⟩⟩
  let s₃ : unitInterval := ⟨s₃_r, ⟨by linarith [hs_ord.1, hs_ord.2.1, hs_ord.2.2.1], by linarith
    [hs_ord.2.2.2.1, hs_ord.2.2.2.2]⟩⟩
  let s₄ : unitInterval := ⟨s₄_r, ⟨by linarith [hs_ord.1, hs_ord.2.1, hs_ord.2.2.1,
    hs_ord.2.2.2.1], hs_ord.2.2.2.2.le⟩⟩
  have ha₁_apply : ∀ (m : ℕ) (hm : m < l₂.length) (s : unitInterval),
      (s : ℝ) = (θ m - (2 * Real.pi - θ_first)) / Δθ → a₁ s = l₂[m]'hm := by
    intro m hm s hs
    change g (Circle.exp ((2 * Real.pi - θ_first) + Δθ * (s : ℝ))) = l₂[m]'hm
    rw [hs]
    have h_angle : (2 * Real.pi - θ_first) + Δθ * ((θ m - (2 * Real.pi - θ_first)) / Δθ) = θ m := by
      rw [mul_div_cancel₀ _ (ne_of_gt hΔθ_pos)]
      ring
    rw [h_angle, hg_circ, hθ_val m hm]
  have hs₁_val : a₁ s₁ = u₁ := (ha₁_apply (2 * k - 1) (by omega) s₁ rfl).trans hget_u.1
  have hs₂_val : a₁ s₂ = u₂ := (ha₁_apply (2 * k) (by omega) s₂ rfl).trans hget_u.2.1
  have hs₃_val : a₁ s₃ = u₃ := (ha₁_apply (2 * k + 1) (by omega) s₃ rfl).trans hget_u.2.2.1
  have hs₄_val : a₁ s₄ = u₄ := (ha₁_apply (2 * k + 2) (by omega) s₄ rfl).trans hget_u.2.2.2
  have hcl_r₂ : IsClosed (subBd r₂) := isClosed_closure.inter isClosed_closure
  have hu_V : ∀ {u : S} {s : unitInterval}, u ∈ H.V ∩ subBd Λ → a₁ s = u →
      u ∈ (H'.interSet (subBd r₂)).V := by
    intro u s hu has
    rw [interSet_V_of_isClosed H' hcl_r₂]
    refine ⟨hSub_H.1 hu.1, ?_⟩
    rw [hsubBd_union]
    exact Or.inl ⟨s, has⟩
  refine ⟨hu_V hu₁ hs₁_val, hu_V hu₂ hs₂_val, hu_V hu₃ hs₃_val, hu_V hu₄ hs₄_val, ?_⟩
  rw [← hs₁_val, ← hs₂_val, ← hs₃_val, ← hs₄_val]
  exact htwo.2 (hU_r₂.trans hsubBd_union)
    (show s₁ < s₂ from hs_ord.2.1)
    (show s₂ < s₃ from hs_ord.2.2.1)
    (show s₃ < s₄ from hs_ord.2.2.2.1)

end PlaneChordsAndCaps

/-! ## 8. Proof of Graph Minors XV, (3.4) -/

section Theorem34

private theorem drawing_inter_le' {S : Type w} [TopologicalSpace S]
    (H' : Drawing S) {D : Set S} (hD : IsClosed D) :
    (PaintingOrDrawing.drawing H').inter D ≤ H'.toHypergraph := by
  refine ⟨inter_subset_left, fun _ h => h.1, fun e he => ?_⟩
  ext v
  change (e ∈ H'.E ∧ v ∈ H'.V ∧ v ∈ closure e) ↔
    (e ∈ H'.E ∧ v ∈ H'.V ∧ v ∈ closure e) ∧ e ⊆ D ∧ v ∈ D
  exact ⟨fun h => ⟨h, he.2, hD.closure_subset_iff.mpr he.2 h.2.2⟩, fun h => h.1⟩

private theorem isRespectful_inducedBySubgraph' {S : Type w} [TopologicalSpace S] [T2Space S]
    {H₀ H' : Drawing S} {θ' : ℕ}
    {T₀ : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hSub : H₀.IsSubdrawing H')
    (hResp₀ : (PaintingOrDrawing.drawing H₀).IsRespectful θ' T₀) :
    (PaintingOrDrawing.drawing H').IsRespectful θ'
      (GM12.inducedBySubgraph H'.toHypergraph H₀.toHypergraph θ' T₀) := by
  exact GM12.isRespectful_inducedBySubgraph hSub hResp₀

private theorem rigid_gluing_of_parallel_chords
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    (H : Drawing S)
    (θ : ℕ)
    (k : ℕ)
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (Λ : Set S)
    (v : Fin (2 * k) → S)
    (i_k : Fin (2 * k))
    (i_last : Fin (2 * k))
    (hk : 3 ≤ k)
    (hv_mem : ∀ (i : Fin (2 * k)), v i ∈ H.V ∩ subBd Λ)
    (hFree_v : IsFreeSet H.toHypergraph T θ (range v))
    {h : S → ℂ}
    {g : ℂ → S}
    (c : IsChart (closure Λ) h g)
    (H' : Drawing S)
    (P' : Fin (k - 1) → Drawing S)
    (hSub_H : H.IsSubdrawing H')
    (hP'_disj : Pairwise fun i j => Disjoint (P' i).U (P' j).U)
    (hS : IsClosedSurface S)
    [ConnectedSpace S]
    (hRigid_H : IsRigid H)
    (hT : IsTangle H.toHypergraph θ T)
    (hθ : 3 ≤ θ)
    (hΛ_open : IsOpen Λ)
    (hCD : IsClosedDisc (closure Λ))
    (hdiscBd : discBd (closure Λ) = subBd Λ)
    (hHU_compl : H.U ⊆ univ \ Λ) :
    let a : Fin (k - 1) → S := fun j => v ⟨j.1, by omega⟩
    let b : Fin (k - 1) → S := fun j => v ⟨2 * k - 2 - j.1, by omega⟩
    (∀ (j : Fin (k - 1)), g { re := parallelX k j, im := parallelY k j } = a j) →
    (∀ (j : Fin (k - 1)), g { re := parallelX k j, im := -parallelY k j } = b j) →
    (g { re := -1, im := 0 } = v i_k) →
    (g { re := 1, im := 0 } = v i_last) →
    ∀ (L : Fin (k - 1) → Set S),
    (∀ (j : Fin (k - 1)), (P' j).U = L j ∧ (P' j).IsPathBetween (a j) (b j) ∧ (P'
      j).IsSubdrawing H' ∧ a j ∈ (P' j).V ∧ b j ∈ (P' j).V) →
    (∀ (j : Fin (k - 1)), IsLineWithEnds (L j) (a j) (b j)) →
    (∀ (j : Fin (k - 1)), L j ⊆ closure Λ) →
    (∀ (j : Fin (k - 1)), L j ∩ discBd (closure Λ) = {a j, b j}) →
    (IsCappedSplit (fun _ : Fin 1 => subBd Λ) (univ \ Λ) (closure Λ) (Subtype.val :
      ↥(univ \ Λ) → S) (fun _ : Fin 1 => Λ)) →
    (IsCappedDrawing (Subtype.val : ↥(univ \ Λ) → S) H' H) →
    (univ \ Λ ∩ closure Λ = subBd Λ) →
    (univ \ Λ ∩ closure Λ ⊆ H'.U) →
    (range v ⊆ H'.V ∩ (univ \ Λ ∩ closure Λ)) →
    (closure Λ ∩ H'.U ⊆ discBd (closure Λ) ∪ ⋃ j, (P' j).U) →
    IsRigid H' := by
  intro a b hg_a hg_b hg_ik hg_ilast L hP' hL_line hL_sub_cl hL_inter_discBd hSplit_Λ hCap_Λ
    hSplit_inter_eq hInterU_Λ hX_sub_Λ hP₂_U
  refine theorem_3_2_proof (fun _ : Fin 1 => subBd Λ) (univ \ Λ) (closure Λ)
    (Subtype.val : ↥(univ \ Λ) → S) (fun _ : Fin 1 => Λ) H' H (range v)
    hSplit_Λ hCap_Λ hInterU_Λ hX_sub_Λ
    (fun _ _ _ i j _ _ => Subsingleton.elim i j) ?_ ?_ ?_
  · intro F hF hFU hFV
    have hX_coe : Subtype.val '' (Subtype.val ⁻¹' range v : Set ↥(univ \ Λ)) = range v := by
      rw [Subtype.image_preimage_coe]
      refine inter_eq_right.mpr ?_
      rintro _ ⟨i, rfl⟩
      exact hHU_compl (H.V_subset_U (hv_mem i).1)
    rw [hX_coe]
    exact theorem_3_3_claim_3 hS hRigid_H hT hθ hFree_v hF hFU hFV
  · intro F hF_P₂ hF hFU hFV
    exact dial_of_oArc_in_striped_disc hS hCD Subset.rfl hP₂_U
      (fun j => (hP' j).1 ▸ hL_sub_cl j)
      (fun j => (hP' j).1 ▸ hL_line j)
      (fun j => (hP' j).2.2.1)
      (fun j => (hP' j).1 ▸ hL_inter_discBd j)
      hP'_disj hF_P₂ hF hFU hFV
  · intro F u₀ v₀ P_bd hF_P₂ _ _ hF_line hF_U hP_sub_inter hP_path hPX_card
    have hcl_inter : IsClosed ((univ \ Λ) ∩ closure Λ) :=
      (isClosed_univ.sdiff hΛ_open).inter isClosed_closure
    have hP_sub_H' : P_bd.IsSubdrawing H' := by
      refine ⟨hP_sub_inter.1.trans ?_, hP_sub_inter.2.trans ?_⟩
      · rw [interSet_V_of_isClosed H' hcl_inter]
        exact inter_subset_left
      · rw [interSet_E H']
        exact fun _ he => he.1
    have hPU_inter : P_bd.U ⊆ (univ \ Λ) ∩ closure Λ := by
      refine (isSubdrawing_U_subset hP_sub_inter).trans ?_
      rw [(H'.interSet ((univ \ Λ) ∩ closure Λ)).U_eq,
        interSet_V_of_isClosed H' hcl_inter, interSet_E]
      exact union_subset inter_subset_right
        (iUnion₂_subset fun e he => hcl_inter.closure_subset_iff.mpr he.2)
    have hPU_bd : P_bd.U ⊆ discBd (closure Λ) := by
      rw [hdiscBd, ← hSplit_inter_eq]
      exact hPU_inter
    have hPU_D : P_bd.U ⊆ closure Λ := hPU_bd.trans (Surface.discBd_subset (closure Λ))
    obtain ⟨ψ_F, hψ_F0, hψ_F1⟩ := id hF_line
    have huv₀ : u₀ ≠ v₀ := fun heq => zero_ne_one
      (ψ_F.injective (Subtype.ext (hψ_F0.trans (heq.trans hψ_F1.symm))))
    have hNo_both₀ := no_both_ends_in_bd_path c hk
      (fun i => hSub_H.1 (hv_mem i).1) hg_ik hg_ilast hg_a hg_b
      hP_sub_H' hPU_bd hP_path huv₀ hPX_card
    have hNo_both : ∀ j : Fin (k - 1), ¬ (a j ∈ P_bd.V ∧ b j ∈ P_bd.V) := by
      intro j
      rw [← hg_a j, ← hg_b j]
      exact hNo_both₀ j
    exact openDisc_of_chord_in_striped_disc hS hCD Subset.rfl hP₂_U
      (fun j => (hP' j).1 ▸ hL_line j)
      (fun j => (hP' j).2.2.1)
      (fun j => ⟨(hP' j).2.2.2.1, (hP' j).2.2.2.2⟩)
      (fun j => (hP' j).1 ▸ hL_inter_discBd j)
      hPU_D hF_P₂ hPU_bd hF_line hF_U hP_sub_H' hP_path hNo_both

private theorem image_disjoint_of_avoids_parallel_chords {S : Type w} [TopologicalSpace S]
    {H H' : Drawing S} {k : ℕ} {Λ : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : IsChart (closure Λ) h g)
    (hHU_compl : H.U ⊆ univ \ Λ)
    (hH'_U : H'.U = H.U ∪ ⋃ j : Fin (k - 1), g '' vertChord (parallelX k j))
    {B : Set ℂ} (hB : B ⊆ ball 0 1) (hB_image : g '' B ⊆ Λ)
    (hAvoid : ∀ z ∈ B, ∀ j : Fin (k - 1), z.re ≠ parallelX k j) :
    Disjoint (g '' B) H'.U := by
  refine Set.disjoint_left.mpr ?_
  rintro _ ⟨z, hz, rfl⟩ hxU
  rw [hH'_U] at hxU
  rcases hxU with hxH | hxL
  · exact (hHU_compl hxH).2 (hB_image ⟨z, hz, rfl⟩)
  · obtain ⟨j, w, hw, hgw⟩ := mem_iUnion.mp hxL
    have hzw := c.injOn (ball_subset_closedBall (hB hz)) hw.1 hgw.symm
    exact hAvoid z hz j (congrArg Complex.re hzw |>.trans hw.2)

private theorem normal_boundary_of_glued_chords
    {S : Type w}
    [TopologicalSpace S]
    (H : Drawing S)
    (k : ℕ)
    (H' : Drawing S)
    (P' : Fin (k - 1) → Drawing S)
    (hH'_V : H'.V = H.V ∪ ⋃ j, (P' j).V)
    (a : Fin (k - 1) → S)
    (b : Fin (k - 1) → S)
    (L : Fin (k - 1) → Set S)
    (hH'_U : H'.U = H.U ∪ ⋃ j, L j)
    (ha_V : ∀ (j : Fin (k - 1)), a j ∈ H.V)
    (hb_V : ∀ (j : Fin (k - 1)), b j ∈ H.V)
    (Δ : Set S)
    (F_Δ : Set S)
    (hchord_inter_compl : ∀ (j : Fin (k - 1)), L j ∩ closure (univ \ Δ) = {a j, b j})
    (hHU_inter_Δ : H.U ∩ Δ ⊆ ⋃ j, {a j, b j})
    (hab_sub_FΔ : range a ∪ range b ⊆ F_Δ)
    (hFΔ_sub_Δ : F_Δ ⊆ Δ)
    (hFΔ_sub_cl_compl : F_Δ ⊆ closure (univ \ Δ)) :
    H'.IsNormal F_Δ ∧ H'.V ∩ F_Δ = range a ∪ range b := by
  refine glued_isNormal_and_V_inter (X_C := range a ∪ range b) ?_ ?_ ?_ hH'_U hH'_V
  · rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · exact ha_V j
    · exact hb_V j
  · refine Subset.antisymm ?_ ?_
    · intro x ⟨hxU, hxF⟩
      have hx_u : x ∈ ⋃ j : Fin (k - 1), {a j, b j} := hHU_inter_Δ ⟨hxU, hFΔ_sub_Δ hxF⟩
      obtain ⟨j, rfl | rfl⟩ := mem_iUnion.mp hx_u
      · exact Or.inl ⟨j, rfl⟩
      · exact Or.inr ⟨j, rfl⟩
    · rintro x (⟨j, rfl⟩ | ⟨j, rfl⟩)
      · exact ⟨H.V_subset_U (ha_V j), hab_sub_FΔ (Or.inl ⟨j, rfl⟩)⟩
      · exact ⟨H.V_subset_U (hb_V j), hab_sub_FΔ (Or.inr ⟨j, rfl⟩)⟩
  · rintro x ⟨hxL, hxF⟩
    obtain ⟨j, hxj⟩ := mem_iUnion.mp hxL
    have hx_pair : x ∈ ({a j, b j} : Set S) :=
      hchord_inter_compl j ▸ ⟨hxj, hFΔ_sub_cl_compl hxF⟩
    rcases hx_pair with rfl | rfl
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨j, rfl⟩

private theorem parallel_chord_cap_regions
    {S : Type w}
    [TopologicalSpace S]
    [T2Space S]
    {α : Type u}
    {β : Type v}
    (G : Graph α β)
    (H : Drawing S)
    (θ_star : ℕ)
    (θ : ℕ)
    (k : ℕ)
    (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ)
    (Λ : Set S)
    (v : Fin (2 * k) → S)
    (i_k : Fin (2 * k))
    (i_last : Fin (2 * k))
    (hOArc : IsOArc (subBd Λ))
    (hk : 3 ≤ k)
    (hv_mem : ∀ (i : Fin (2 * k)), v i ∈ H.V ∩ subBd Λ)
    (hFree_v : IsFreeSet H.toHypergraph T θ (range v))
    (hik : ↑i_k = k - 1)
    (hilast : ↑i_last = 2 * k - 1)
    (p_circ : Circle ≃ₜ ↑(subBd Λ))
    (hp_circ_v : ∀ (i : Fin (2 * k)), ↑(p_circ (Circle.exp (parallelModelAngle k ↑i))) = v i)
    {h : S → ℂ}
    {g : ℂ → S}
    (c : IsChart (closure Λ) h g)
    (hg_circ : ∀ (w : Circle), g ↑w = ↑(p_circ w))
    (H' : Drawing S)
    (η' : SpanEmbedding H' G)
    (P' : Fin (k - 1) → Drawing S)
    (hH'_V : H'.V = H.V ∪ ⋃ j, (P' j).V)
    (hH'_E : H'.E = H.E ∪ ⋃ j, (P' j).E)
    (hSub_H : H.IsSubdrawing H')
    (hP'_disj : Pairwise fun i j => Disjoint (P' i).U (P' j).U)
    (hS : IsClosedSurface S)
    [hConn : ConnectedSpace S]
    (hResp_H : IsRespectfulDrawingTangle H θ T)
    (hT : IsTangle H.toHypergraph θ T)
    (h2k_le : 2 * k ≤ θ)
    (hk1 : 1 ≤ k)
    (hΛ_open : IsOpen Λ)
    (hout : ∀ x ∈ closure Λ \ Λ, x ∈ closure (closure Λ)ᶜ)
    (hCD : IsClosedDisc (closure Λ))
    (hdiscBd : discBd (closure Λ) = subBd Λ)
    (hsubBd_sub_HU : subBd Λ ⊆ H.U)
    (hHU_compl : H.U ⊆ univ \ Λ) :
    let a : Fin (k - 1) → S := fun j => v ⟨j.1, by omega⟩
    let b : Fin (k - 1) → S := fun j => v ⟨2 * k - 2 - j.1, by omega⟩
    (∀ (j : Fin (k - 1)), g { re := parallelX k j, im := parallelY k j } = a j) →
    (∀ (j : Fin (k - 1)), g { re := parallelX k j, im := -parallelY k j } = b j) →
    ∀ (hik_eq : i_k = ⟨k - 1, by omega⟩),
    (g { re := -1, im := 0 } = v i_k) →
    (g { re := 1, im := 0 } = v i_last) →
    let L : Fin (k - 1) → Set S := fun j => g '' vertChord (parallelX k j)
    (∀ (j : Fin (k - 1)), (P' j).U = L j ∧ (P' j).IsPathBetween (a j) (b j) ∧ (P'
      j).IsSubdrawing H' ∧ a j ∈ (P' j).V ∧ b j ∈ (P' j).V) →
    (H'.U = H.U ∪ ⋃ j, L j) →
    (∀ (j : Fin (k - 1)), IsLineWithEnds (L j) (a j) (b j)) →
    (∀ (j : Fin (k - 1)), a j ∈ H.V) →
    (∀ (j : Fin (k - 1)), b j ∈ H.V) →
    (H'.interSet (univ \ Λ) = H) →
    (H'.U \ Λ = H.U) →
    ((PaintingOrDrawing.drawing H').IsTwoCell) →
    (inducedTangle H'.toHypergraph H.toHypergraph T θ = inducedBySubgraph
      H'.toHypergraph H.toHypergraph θ T) →
    (IsSigmaSpan G H' η' θ_star θ T_star (GM10.inducedTangle H'.toHypergraph
      H.toHypergraph T θ)) →
    ∀ (d' : Set S → Set S → ℕ),
    (HasTangleMetric H' θ (GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ) d') →
    (∀ x ∈ H.A, ∀ y ∈ H.A, d x y ≤ d' x y) →
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S))) (d' : Set S → Set S → ℕ) (r₁ r₂ :
      Set S), IsSigmaSpan G H' η' θ_star θ T_star T' ∧ HasTangleMetric H' θ T' d' ∧ r₁ ∈ H'.R ∧ r₂
      ∈ H'.R ∧ r₁ ⊆ Λ ∧ r₂ ⊆ Λ ∧ H'.interSet (univ \ Λ) = H ∧ H'.U \ Λ = H.U ∧ T' =
      GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ ∧ (∀ x ∈ H.A, ∀ y ∈ H.A, d x y ≤ d' x
      y) ∧ IsOArc (subBd r₁) ∧ IsOArc (subBd r₂) ∧ (H'.interSet (subBd r₁)).IsCircuit ∧
      (H'.interSet (subBd r₂)).IsCircuit ∧ v i_k ∈ subBd r₁ ∧ v i_last ∈ subBd r₂ ∧ (∀ w₁ w₂ w₃ w₄
      : S, w₁ ∈ H.V ∩ subBd Λ → w₂ ∈ H.V ∩ subBd Λ → w₃ ∈ H.V ∩ subBd Λ → w₄ ∈ H.V ∩ subBd Λ →
      (List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁, w₂, w₃, w₄] ++ List.ofFn (fun
      j : Fin k => v ⟨k + j.1, by omega⟩)).Nodup → GM12.IsListedInOrderOn (subBd Λ) (List.ofFn
      (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁, w₂, w₃, w₄] ++ List.ofFn (fun j : Fin k
      => v ⟨k + j.1, by omega⟩)) → w₁ ∈ (H'.interSet (subBd r₁)).V ∧ w₂ ∈ (H'.interSet (subBd
      r₁)).V ∧ w₃ ∈ (H'.interSet (subBd r₁)).V ∧ w₄ ∈ (H'.interSet (subBd r₁)).V ∧
      OccurInCircuitOrder (H'.interSet (subBd r₁)) w₁ w₂ w₃ w₄) ∧ (∀ u₁ u₂ u₃ u₄ : S, u₁ ∈ H.V ∩
      subBd Λ → u₂ ∈ H.V ∩ subBd Λ → u₃ ∈ H.V ∩ subBd Λ → u₄ ∈ H.V ∩ subBd Λ → (List.ofFn (fun j :
      Fin (2 * k - 1) => v ⟨j.1, by omega⟩) ++ [u₁, u₂, u₃, u₄]).Nodup → GM12.IsListedInOrderOn
      (subBd Λ) (List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩) ++ [u₁, u₂, u₃, u₄]) →
      u₁ ∈ (H'.interSet (subBd r₂)).V ∧ u₂ ∈ (H'.interSet (subBd r₂)).V ∧ u₃ ∈ (H'.interSet (subBd
      r₂)).V ∧ u₄ ∈ (H'.interSet (subBd r₂)).V ∧ OccurInCircuitOrder (H'.interSet (subBd r₂)) u₁
      u₂ u₃ u₄) ∧ 2 * k - 6 ≤ d' r₁ r₂ ∧ 2 * k - 8 ≤ d' {v i_k} {v i_last} := by
  intro a b hg_a hg_b hik_eq hg_ik hg_ilast L hP' hH'_U hL_line ha_V hb_V hInter_compl
    hH'U_sdiff_Λ h2Cell_H' hT'_eq hSpan' d' hd' hd_le_d'
  let T' := GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ
  let j_last : Fin (k - 1) := ⟨k - 2, by omega⟩
  let j_first : Fin (k - 1) := ⟨0, by omega⟩
  let x_last : ℝ := parallelX k j_last
  let x_first : ℝ := parallelX k j_first
  obtain ⟨hx_last_lo, hx_last_hi⟩ := parallelX_mem_Ioo j_last
  obtain ⟨hx_first_lo, hx_first_hi⟩ := parallelX_mem_Ioo j_first
  let r₁ : Set S := g '' leftOpenCap x_last
  let r₂ : Set S := g '' rightOpenCap x_first
  have hg_ball : g '' ball (0 : ℂ) 1 = Λ := isChart_g_ball_eq_region c hΛ_open hdiscBd
  have hleft_sub_ball : leftOpenCap x_last ⊆ ball (0 : ℂ) 1 := fun _ hz => hz.1
  have hright_sub_ball : rightOpenCap x_first ⊆ ball (0 : ℂ) 1 := fun _ hz => hz.1
  have hr₁_sub_Λ : r₁ ⊆ Λ := hg_ball ▸ image_mono hleft_sub_ball
  have hr₂_sub_Λ : r₂ ⊆ Λ := hg_ball ▸ image_mono hright_sub_ball
  have hr₁_open : IsOpen r₁ :=
    isChart_isOpen_image_of_subset_ball c hΛ_open hdiscBd (isOpen_leftOpenCap x_last)
      hleft_sub_ball
  have hr₂_open : IsOpen r₂ :=
    isChart_isOpen_image_of_subset_ball c hΛ_open hdiscBd (isOpen_rightOpenCap x_first)
      hright_sub_ball
  have hr₁_ne : r₁.Nonempty := (leftOpenCap_nonempty hx_last_lo hx_last_hi).image g
  have hr₂_ne : r₂.Nonempty := (rightOpenCap_nonempty hx_first_lo hx_first_hi).image g
  have hr₁_conn : IsPreconnected r₁ :=
    (convex_leftOpenCap x_last).isPreconnected.image g
      (c.gc.mono (hleft_sub_ball.trans ball_subset_closedBall))
  have hr₂_conn : IsPreconnected r₂ :=
    (convex_rightOpenCap x_first).isPreconnected.image g
      (c.gc.mono (hright_sub_ball.trans ball_subset_closedBall))
  have hr₁_bd : subBd r₁ = g '' leftSphereArc x_last ∪ L j_last := by
    rw [isChart_subBd_image_of_isOpen_subset_ball c hΛ_open hdiscBd
        (isOpen_leftOpenCap x_last) hleft_sub_ball,
      closure_leftOpenCap hx_last_lo hx_last_hi,
      leftClosedCap_sdiff_leftOpenCap, image_union]
  have hr₂_bd : subBd r₂ = g '' rightSphereArc x_first ∪ L j_first := by
    rw [isChart_subBd_image_of_isOpen_subset_ball c hΛ_open hdiscBd
        (isOpen_rightOpenCap x_first) hright_sub_ball,
      closure_rightOpenCap hx_first_lo hx_first_hi,
      rightClosedCap_sdiff_rightOpenCap, image_union]
  have hLj_sub_H'U : ∀ j : Fin (k - 1), L j ⊆ H'.U := fun j => by
    rw [hH'_U]
    exact (subset_iUnion L j).trans subset_union_right
  have hr₁_bd_U : subBd r₁ ⊆ H'.U := by
    rw [hr₁_bd]
    refine union_subset ?_ (hLj_sub_H'U j_last)
    calc g '' leftSphereArc x_last
        ⊆ g '' sphere (0 : ℂ) 1 := image_mono (leftSphereArc_subset_sphere x_last)
      _ = discBd (closure Λ) := c.g_sphere
      _ = subBd Λ := hdiscBd
      _ ⊆ H.U := hsubBd_sub_HU
      _ ⊆ H'.U := isSubdrawing_U_subset hSub_H
  have hr₂_bd_U : subBd r₂ ⊆ H'.U := by
    rw [hr₂_bd]
    refine union_subset ?_ (hLj_sub_H'U j_first)
    calc g '' rightSphereArc x_first
        ⊆ g '' sphere (0 : ℂ) 1 := image_mono (rightSphereArc_subset_sphere x_first)
      _ = discBd (closure Λ) := c.g_sphere
      _ = subBd Λ := hdiscBd
      _ ⊆ H.U := hsubBd_sub_HU
      _ ⊆ H'.U := isSubdrawing_U_subset hSub_H
  have hr₁_disj : Disjoint r₁ H'.U := by
    refine image_disjoint_of_avoids_parallel_chords c hHU_compl hH'_U
      (fun _ hz => hz.1) hr₁_sub_Λ ?_
    intro z hz j
    have hj_le : j ≤ j_last := Fin.le_def.mpr (by dsimp [j_last]; omega)
    exact (hz.2.trans_le ((strictAnti_parallelX hk1).antitone hj_le)).ne
  have hr₂_disj : Disjoint r₂ H'.U := by
    refine image_disjoint_of_avoids_parallel_chords c hHU_compl hH'_U
      (fun _ hz => hz.1) hr₂_sub_Λ ?_
    intro z hz j
    have hj_ge : j_first ≤ j := Fin.le_def.mpr (Nat.zero_le _)
    exact (((strictAnti_parallelX hk1).antitone hj_ge).trans_lt hz.2).ne.symm
  have hr₁_R : r₁ ∈ H'.R :=
    mem_R_of_isOpen_isPreconnected hS hr₁_open hr₁_ne hr₁_conn hr₁_disj hr₁_bd_U
  have hr₂_R : r₂ ∈ H'.R :=
    mem_R_of_isOpen_isPreconnected hS hr₂_open hr₂_ne hr₂_conn hr₂_disj hr₂_bd_U
  obtain ⟨hOArc_r₁, hOrd_r₁⟩ :=
    occurInCircuitOrder_leftCap c hk p_circ hp_circ_v hg_circ hSub_H hr₁_bd
  obtain ⟨hOArc_r₂, hOrd_r₂⟩ :=
    occurInCircuitOrder_rightCap c hk p_circ hp_circ_v hg_circ hSub_H hr₂_bd
  obtain ⟨hCirc_r₁, hU_r₁, _⟩ := interSet_subBd_isCircuit_and_U_eq hS hr₁_R hOArc_r₁
  obtain ⟨hCirc_r₂, hU_r₂, _⟩ := interSet_subBd_isCircuit_and_U_eq hS hr₂_R hOArc_r₂
  have hv_ik_r₁ : v i_k ∈ subBd r₁ := by
    rw [hr₁_bd, ← hg_ik]
    refine Or.inl ⟨⟨-1, 0⟩, ⟨?_, hx_last_lo.le⟩, rfl⟩
    rw [mem_sphere_unit_iff]; norm_num
  have hv_ilast_r₂ : v i_last ∈ subBd r₂ := by
    rw [hr₂_bd, ← hg_ilast]
    refine Or.inl ⟨⟨1, 0⟩, ⟨?_, hx_first_hi.le⟩, rfl⟩
    rw [mem_sphere_unit_iff]; norm_num
  -- Step 7: Pinched subdisc `Δ`, `GM12Theorem61Statement`, and metric bounds.
  obtain ⟨hΔ_disc, _, hΔ_subBd, hΔ_oArc, hchord_sub_Δ,
    _, hΔ_inter_compl₀, hcompl_sub_cl_compl, hchord_inter_compl₀⟩ :=
    exists_pinched_vert_disc hS c hCD hOArc hΛ_open hdiscBd hout hk
  let Ψ := pinchVertHomeo k hk
  let Δ : Set S := g '' (Ψ '' closedBall (0 : ℂ) 1)
  let F_Δ : Set S := subBd Δ
  have hΔ_inter_compl : Δ ∩ (univ \ Λ) = ⋃ j : Fin (k - 1), {a j, b j} := by
    refine hΔ_inter_compl₀.trans (iUnion_congr fun j => ?_)
    rw [hg_a j, hg_b j]
  have hchord_inter_compl : ∀ j : Fin (k - 1),
      L j ∩ closure (univ \ Δ) = {a j, b j} := by
    intro j
    exact (hchord_inter_compl₀ j).trans (by rw [hg_a j, hg_b j])
  obtain ⟨_, _, hInter_cl_compl⟩ :=
    glued_interSet_base_eq isClosed_closure ha_V hb_V
      (hHU_compl.trans hcompl_sub_cl_compl) hchord_inter_compl
      hH'_U hH'_V hH'_E hP'
  have hHU_inter_Δ : H.U ∩ Δ ⊆ ⋃ j : Fin (k - 1), {a j, b j} := by
    rw [Set.inter_comm, ← hΔ_inter_compl]
    exact inter_subset_inter_right _ hHU_compl
  obtain ⟨hP'_sub_Δ, hInter_Δ_U⟩ :=
    glued_interSet_paths_eq hΔ_disc.isClosed hchord_sub_Δ hHU_inter_Δ hH'_V hH'_E hP'
  have hab_sub_FΔ : range a ∪ range b ⊆ F_Δ := by
    rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
    · have hmem : a j ∈ L j ∩ closure (univ \ Δ) :=
        hchord_inter_compl j ▸ Or.inl rfl
      exact ⟨subset_closure (hchord_sub_Δ j hmem.1), hmem.2⟩
    · have hmem : b j ∈ L j ∩ closure (univ \ Δ) :=
        hchord_inter_compl j ▸ Or.inr rfl
      exact ⟨subset_closure (hchord_sub_Δ j hmem.1), hmem.2⟩
  have hFΔ_sub_Δ : F_Δ ⊆ Δ := fun _ hx => hΔ_disc.isClosed.closure_subset hx.1
  have hFΔ_sub_cl_compl : F_Δ ⊆ closure (univ \ Δ) := fun _ hx => hx.2
  have hNorm_and_V_FΔ : H'.IsNormal F_Δ ∧ H'.V ∩ F_Δ = range a ∪ range b := by
    exact normal_boundary_of_glued_chords (S := S) H k H' P' hH'_V a b L hH'_U ha_V hb_V Δ F_Δ
      hchord_inter_compl hHU_inter_Δ hab_sub_FΔ hFΔ_sub_Δ hFΔ_sub_cl_compl
  obtain ⟨hNodup_ab, hOrder_ab⟩ :=
    isListedInOrderOn_pinched_bd c hk p_circ hp_circ_v hg_circ hΔ_subBd
  have hex_e_path : ∀ j : Fin (k - 1), ∃ e, e ∈ (P' j).E := by
    intro j
    obtain ⟨ψ_j, hψ_j0, hψ_j1⟩ := hL_line j
    have hab_ne : a j ≠ b j := fun heq => zero_ne_one
      (ψ_j.injective (Subtype.ext (hψ_j0.trans (heq.trans hψ_j1.symm))))
    have h_walk_edge : ∀ {u w : S} (W : GraphWalk (P' j).toGraph u w), u ≠ w → ∃ e, e ∈ W.edges
      := by
      intro u w W hne
      cases W with
      | nil => exact (hne rfl).elim
      | cons _ _ => exact ⟨_, List.mem_cons_self⟩
    obtain ⟨W, _, _, hWE⟩ := (hP' j).2.1
    obtain ⟨e, heW⟩ := h_walk_edge W hab_ne
    exact ⟨e, hWE ▸ heW⟩
  choose e_path he_path using hex_e_path
  have hFree_FΔ : IsFreeSet (H'.interSet (closure (univ \ Δ))).toHypergraph T θ
      (F_Δ ∩ (H'.interSet (closure (univ \ Δ))).V) := by
    rw [hInter_cl_compl]
    have hsub_v : F_Δ ∩ H.V ⊆ range v := by
      intro x ⟨hxF, hxHV⟩
      have hx_ab : x ∈ range a ∪ range b :=
        hNorm_and_V_FΔ.2 ▸ ⟨hSub_H.1 hxHV, hxF⟩
      rcases hx_ab with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact ⟨⟨j.1, by omega⟩, rfl⟩
      · exact ⟨⟨2 * k - 2 - j.1, by omega⟩, rfl⟩
    have hcard_le : (F_Δ ∩ H.V).ncard ≤ θ :=
      le_trans (Set.ncard_le_ncard hsub_v (Set.finite_range v)) hFree_v.2.1
    have hFree_trunc := theorem_3_3_claim_2 hT hFree_v hsub_v hcard_le
    exact ⟨hFree_trunc.1, hFree_trunc.2.1,
      fun A B hAB hXA => hFree_trunc.2.2 ⟨hAB, hT.order_lt hAB⟩ hXA⟩
  have hdist_61 : 2 * (k - 1) ≤ d' (e_path j_first) (e_path j_last) :=
    GraphMinor.GM12.theorem_6_1_proof.{w} H' F_Δ Δ (k - 1) θ T d' a b P' e_path j_first j_last
      hS hConn (by omega) (by omega)
      h2Cell_H' hΔ_oArc hNorm_and_V_FΔ.1 hΔ_disc rfl
      hNodup_ab hOrder_ab (by rw [Set.inter_comm]; exact hNorm_and_V_FΔ.2.symm)
      (fun j => ⟨(hP' j).2.1, hP'_sub_Δ j⟩)
      hP'_disj hInter_Δ_U he_path
      (hInter_cl_compl.symm ▸ hResp_H.1)
      (hInter_cl_compl.symm ▸ hResp_H)
      (by rw [hInter_cl_compl, ← hT'_eq]; exact hd')
      hFree_FΔ rfl rfl
  have he₁_sub_r₂ : e_path j_first ⊆ closure r₂ := by
    intro x hx
    have hxL : x ∈ L j_first := (hP' j_first).1 ▸ ((he_path j_first).2.1 hx).1
    have hx_bd : x ∈ subBd r₂ := hr₂_bd ▸ Or.inr hxL
    exact hx_bd.1
  have he₂_sub_r₁ : e_path j_last ⊆ closure r₁ := by
    intro x hx
    have hxL : x ∈ L j_last := (hP' j_last).1 ▸ ((he_path j_last).2.1 hx).1
    have hx_bd : x ∈ subBd r₁ := hr₁_bd ▸ Or.inr hxL
    exact hx_bd.1
  obtain ⟨hd'_r₁_r₂, hd'_vk_vlast⟩ :=
    tangleMetric_bounds_of_parallel_paths hS hd' hr₁_R hr₂_R
      ((hP' j_first).2.2.1.2 (he_path j_first))
      ((hP' j_last).2.2.1.2 (he_path j_last))
      he₁_sub_r₂ he₂_sub_r₁
      (hSub_H.1 (hv_mem i_k).1) (hSub_H.1 (hv_mem i_last).1)
      hv_ik_r₁.1 hv_ilast_r₂.1 hdist_61
  refine ⟨T', d', r₁, r₂,
    hSpan', hd', hr₁_R, hr₂_R, hr₁_sub_Λ, hr₂_sub_Λ,
    hInter_compl, hH'U_sdiff_Λ, rfl, hd_le_d',
    hOArc_r₁, hOArc_r₂, hCirc_r₁, hCirc_r₂, hv_ik_r₁, hv_ilast_r₂,
    fun w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄ _ hOrd_w => hOrd_r₁ hU_r₁ w₁ w₂ w₃ w₄ hw₁ hw₂ hw₃ hw₄ hOrd_w,
    fun u₁ u₂ u₃ u₄ hu₁ hu₂ hu₃ hu₄ _ hOrd_u => hOrd_r₂ hU_r₂ u₁ u₂ u₃ u₄ hu₁ hu₂ hu₃ hu₄ hOrd_u,
    hd'_r₁_r₂, hd'_vk_vlast⟩

/-- The proof of Graph Minors XV, (3.4), pages 122–123, in a chart of $\bar\Lambda$ in which the
paths $P_1, \dots, P_{k-1}$ are the vertical chords at `parallelX k j`. The chart `g` maps the unit
circle onto $bd(\Lambda)$ by `p_circ`, with $v_i$ at the angle `parallelModelAngle k i`.
`theorem_3_4_proof` (`GraphMinor/GM15/Section3Given.lean`) moves any paths across $\Lambda$ onto
these chords and then applies this. -/
theorem theorem_3_4_of_chart {S : Type w} [TopologicalSpace S] [T2Space S] {α : Type u}
    {β : Type v} (G : Graph α β) (H : Drawing S) (η : SpanEmbedding H G)
    (θ_star θ k : ℕ) (T_star : Set (Hypergraph α β × Hypergraph α β))
    (T : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
    (d : Set S → Set S → ℕ) (Λ : Set S) (v : Fin (2 * k) → S) (i_k i_last : Fin (2 * k))
    (hSpan : IsSigmaSpan G H η θ_star θ T_star T) (hd : HasTangleMetric H θ T d)
    (hΛ : Λ ∈ H.R) (hOArc : IsOArc (subBd Λ)) (hk : 3 ≤ k)
    (hNodup_v : (List.ofFn v).Nodup) (hv_mem : ∀ i : Fin (2 * k), v i ∈ H.V ∩ subBd Λ)
    (hFree_v : IsFreeSet H.toHypergraph T θ (range v))
    (hik : i_k.1 = k - 1) (hilast : i_last.1 = 2 * k - 1)
    (p_circ : Circle ≃ₜ ↥(subBd Λ))
    (hp_circ_v : ∀ i : Fin (2 * k), (p_circ (Circle.exp (parallelModelAngle k i.1))).1 = v i)
    {h : S → ℂ} {g : ℂ → S} (c : IsChart (closure Λ) h g)
    (hg_circ : ∀ w : Circle, g w = (p_circ w).1)
    (H' : Drawing S) (η' : SpanEmbedding H' G) (P' : Fin (k - 1) → Drawing S)
    (hH'_U : H'.U = H.U ∪ ⋃ j : Fin (k - 1), g '' vertChord (parallelX k j))
    (hH'_V : H'.V = H.V ∪ ⋃ j : Fin (k - 1), (P' j).V)
    (hH'_E : H'.E = H.E ∪ ⋃ j : Fin (k - 1), (P' j).E)
    (hSub_H : H.IsSubdrawing H')
    (hP' : ∀ j : Fin (k - 1), (P' j).U = g '' vertChord (parallelX k j) ∧
      (P' j).IsPathBetween (v ⟨j.1, by omega⟩) (v ⟨2 * k - 2 - j.1, by omega⟩) ∧
      (P' j).IsSubdrawing H' ∧ v ⟨j.1, by omega⟩ ∈ (P' j).V ∧
      v ⟨2 * k - 2 - j.1, by omega⟩ ∈ (P' j).V)
    (hP'_disj : Pairwise (fun i j => Disjoint (P' i).U (P' j).U))
    (hvm_H : ∀ x ∈ H.V, η'.vMap x = η.vMap x) (hem_H : ∀ e ∈ H.E, η'.eMap e = η.eMap e) :
    ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
      (d' : Set S → Set S → ℕ) (r₁ r₂ : Set S),
      IsSigmaSpan G H' η' θ_star θ T_star T' ∧
      HasTangleMetric H' θ T' d' ∧
      r₁ ∈ H'.R ∧ r₂ ∈ H'.R ∧ r₁ ⊆ Λ ∧ r₂ ⊆ Λ ∧
      H'.interSet (univ \ Λ) = H ∧
      H'.U \ Λ = H.U ∧
      T' = GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ ∧
      (∀ x ∈ H.A, ∀ y ∈ H.A, d x y ≤ d' x y) ∧
      IsOArc (subBd r₁) ∧ IsOArc (subBd r₂) ∧
      (H'.interSet (subBd r₁)).IsCircuit ∧ (H'.interSet (subBd r₂)).IsCircuit ∧
      v i_k ∈ subBd r₁ ∧ v i_last ∈ subBd r₂ ∧
      (∀ w₁ w₂ w₃ w₄ : S,
        w₁ ∈ H.V ∩ subBd Λ → w₂ ∈ H.V ∩ subBd Λ →
        w₃ ∈ H.V ∩ subBd Λ → w₄ ∈ H.V ∩ subBd Λ →
        (List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁, w₂, w₃, w₄] ++
          List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)).Nodup →
        GM12.IsListedInOrderOn (subBd Λ)
          (List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁, w₂, w₃, w₄] ++
            List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)) →
        w₁ ∈ (H'.interSet (subBd r₁)).V ∧ w₂ ∈ (H'.interSet (subBd r₁)).V ∧
        w₃ ∈ (H'.interSet (subBd r₁)).V ∧ w₄ ∈ (H'.interSet (subBd r₁)).V ∧
        OccurInCircuitOrder (H'.interSet (subBd r₁)) w₁ w₂ w₃ w₄) ∧
      (∀ u₁ u₂ u₃ u₄ : S,
        u₁ ∈ H.V ∩ subBd Λ → u₂ ∈ H.V ∩ subBd Λ →
        u₃ ∈ H.V ∩ subBd Λ → u₄ ∈ H.V ∩ subBd Λ →
        (List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩) ++ [u₁, u₂, u₃, u₄]).Nodup →
        GM12.IsListedInOrderOn (subBd Λ)
          (List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩) ++ [u₁, u₂, u₃, u₄]) →
        u₁ ∈ (H'.interSet (subBd r₂)).V ∧ u₂ ∈ (H'.interSet (subBd r₂)).V ∧
        u₃ ∈ (H'.interSet (subBd r₂)).V ∧ u₄ ∈ (H'.interSet (subBd r₂)).V ∧
        OccurInCircuitOrder (H'.interSet (subBd r₂)) u₁ u₂ u₃ u₄) ∧
      2 * k - 6 ≤ d' r₁ r₂ ∧ 2 * k - 8 ≤ d' {v i_k} {v i_last} := by
  classical
  have hS : IsClosedSurface S :=
    ⟨hSpan.isSurface.1, hSpan.isSurface.2.1, fun x =>
      by_contra fun hx => Set.eq_empty_iff_forall_notMem.mp hSpan.bd_empty x hx⟩
  have hConn : ConnectedSpace S := hSpan.isConnected
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  have hRigid_H : IsRigid H := hSpan.isRigid
  have hResp_H : IsRespectfulDrawingTangle H θ T := hSpan.isRespectful
  have hT : IsTangle H.toHypergraph θ T := hResp_H.2.1
  -- The `2k` vertices are distinct and free, so `2k ≤ θ`.
  have h2k_le : 2 * k ≤ θ := by
    have hinj : Function.Injective v := List.nodup_ofFn.mp hNodup_v
    have hcard := hFree_v.2.1
    rwa [Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card, Fintype.card_fin] at hcard
  have hθ : 3 ≤ θ := by omega
  have hk1 : 1 ≤ k := by omega
  have hΛ_open : IsOpen Λ := GM11.region_isOpen hΛ
  have hΛ_disc : IsOpenDisc Λ := hResp_H.1.2 Λ hΛ
  obtain ⟨hout, hCD, hdiscBd, _, _⟩ :=
    isClosedDisc_closure_of_region_tangle hS hResp_H hθ hΛ hOArc
  have hsubBd_eq_sdiff : subBd Λ = closure Λ \ Λ := by
    rw [subBd_eq_frontier, hΛ_open.frontier_eq]
  obtain ⟨_, hU_bdΛ, _⟩ := interSet_subBd_isCircuit_and_U_eq hS hΛ hOArc
  have hsubBd_sub_HU : subBd Λ ⊆ H.U := by
    have hcl : IsClosed (subBd Λ) := isClosed_closure.inter isClosed_closure
    rw [← hU_bdΛ, (H.interSet (subBd Λ)).U_eq,
      interSet_V_of_isClosed H hcl, interSet_E]
    exact union_subset (inter_subset_left.trans H.V_subset_U)
      (iUnion₂_subset fun e he => H.closure_subset_U he.1)
  have hHU_compl : H.U ⊆ univ \ Λ :=
    fun x hxU => ⟨mem_univ x, fun hxΛ => GM11.region_subset hΛ hxΛ hxU⟩
  let a : Fin (k - 1) → S := fun j => v ⟨j.1, by omega⟩
  let b : Fin (k - 1) → S := fun j => v ⟨2 * k - 2 - j.1, by omega⟩
  have hg_a : ∀ j : Fin (k - 1), g ⟨parallelX k j, parallelY k j⟩ = a j := fun j => by
    rw [← circle_exp_parallelModelAngle_top j, hg_circ, hp_circ_v ⟨j.1, by omega⟩]
  have hg_b : ∀ j : Fin (k - 1), g ⟨parallelX k j, -parallelY k j⟩ = b j := fun j => by
    rw [← circle_exp_parallelModelAngle_bot j, hg_circ, hp_circ_v ⟨2 * k - 2 - j.1, by omega⟩]
  have hik_eq : i_k = ⟨k - 1, by omega⟩ := Fin.ext hik
  have hilast_eq : i_last = ⟨2 * k - 1, by omega⟩ := Fin.ext hilast
  have hg_ik : g ⟨-1, 0⟩ = v i_k := by
    rw [← circle_exp_parallelModelAngle_k_sub_one hk1, hg_circ, hik_eq,
      hp_circ_v ⟨k - 1, by omega⟩]
  have hg_ilast : g ⟨1, 0⟩ = v i_last := by
    rw [← circle_exp_parallelModelAngle_two_k_sub_one hk1, hg_circ, hilast_eq,
      hp_circ_v ⟨2 * k - 1, by omega⟩]
  -- Step 2: Vertical chord lines `L j` and glued span `(H', η')`.
  let L : Fin (k - 1) → Set S := fun j => g '' vertChord (parallelX k j)
  replace hP' : ∀ j : Fin (k - 1), (P' j).U = L j ∧ (P' j).IsPathBetween (a j) (b j) ∧
      (P' j).IsSubdrawing H' ∧ a j ∈ (P' j).V ∧ b j ∈ (P' j).V := hP'
  replace hH'_U : H'.U = H.U ∪ ⋃ j : Fin (k - 1), L j := hH'_U
  have hL_props : ∀ j : Fin (k - 1),
      IsLineWithEnds (L j) (a j) (b j) ∧
      L j ⊆ closure Λ ∧
      L j ∩ discBd (closure Λ) = {a j, b j} := by
    intro j
    obtain ⟨h1, h2, h3⟩ :=
      isLineWithEnds_image_vertChord c (parallelX_sq_add_parallelY_sq j) (parallelY_pos j)
    rw [hg_a j, hg_b j] at h1 h3
    exact ⟨h1, h2, h3⟩
  have hL_line : ∀ j : Fin (k - 1), IsLineWithEnds (L j) (a j) (b j) :=
    fun j => (hL_props j).1
  have hL_sub_cl : ∀ j : Fin (k - 1), L j ⊆ closure Λ :=
    fun j => (hL_props j).2.1
  have hL_inter_discBd : ∀ j : Fin (k - 1), L j ∩ discBd (closure Λ) = {a j, b j} :=
    fun j => (hL_props j).2.2
  have hL_inter_subBd : ∀ j : Fin (k - 1), L j ∩ subBd Λ = {a j, b j} :=
    hdiscBd ▸ hL_inter_discBd
  have ha_mem : ∀ j : Fin (k - 1), a j ∈ H.V ∩ subBd Λ := fun j => hv_mem ⟨j.1, by omega⟩
  have hb_mem : ∀ j : Fin (k - 1), b j ∈ H.V ∩ subBd Λ := fun j => hv_mem ⟨2 * k - 2 - j.1, by
    omega⟩
  have ha_V : ∀ j : Fin (k - 1), a j ∈ H.V := fun j => (ha_mem j).1
  have hb_V : ∀ j : Fin (k - 1), b j ∈ H.V := fun j => (hb_mem j).1
  have hcl_inter_compl : closure Λ ∩ (univ \ Λ) = subBd Λ := by
    rw [hsubBd_eq_sdiff]
    ext x
    simp only [mem_inter_iff, mem_sdiff, mem_univ, true_and]
  have hL_inter_compl : ∀ j : Fin (k - 1), L j ∩ (univ \ Λ) = {a j, b j} := by
    intro j
    have h1 : L j ∩ (univ \ Λ) = L j ∩ (closure Λ ∩ (univ \ Λ)) := by
      ext x
      exact ⟨fun ⟨hxL, hxC⟩ => ⟨hxL, hL_sub_cl j hxL, hxC⟩, fun ⟨hxL, _, hxC⟩ => ⟨hxL, hxC⟩⟩
    rw [h1, hcl_inter_compl, hL_inter_subBd j]
  have hL_inter_HU : ∀ j : Fin (k - 1), L j ∩ H.U = {a j, b j} := by
    intro j
    refine Subset.antisymm ?_ ?_
    · exact (inter_subset_inter_right _ hHU_compl).trans (hL_inter_compl j).subset
    · rw [← hL_inter_subBd j]
      exact inter_subset_inter_right _ hsubBd_sub_HU
  -- Step 3: Base drawing restriction `H'.interSet (univ \ Λ) = H` and `H'.U \ Λ = H.U`.
  obtain ⟨hU_compl, hV_compl, hInter_compl⟩ :=
    glued_interSet_base_eq (isClosed_univ.sdiff hΛ_open) ha_V hb_V hHU_compl
      hL_inter_compl hH'_U hH'_V hH'_E hP'
  have hH'U_sdiff_Λ : H'.U \ Λ = H.U := by
    rw [← hU_compl, sdiff_eq, compl_eq_univ_sdiff]
  -- Step 4: Prove `IsRigid H'` via `theorem_3_2_proof` on the single-region split `(univ \ Λ,
  -- closure Λ)`.
  have hSplit_Λ : GM12.IsCappedSplit (fun _ : Fin 1 => subBd Λ) (univ \ Λ) (closure Λ)
      (Subtype.val : ↥(univ \ Λ) → S) (fun _ : Fin 1 => Λ) :=
    isCappedSplit_single_region hS hΛ hΛ_disc hOArc hCD hdiscBd hout
  have hCap_Λ : GM12.IsCappedDrawing (Subtype.val : ↥(univ \ Λ) → S) H' H := by
    refine ⟨?_, ?_⟩
    · rw [Subtype.image_preimage_coe, Set.inter_comm, hU_compl]
    · rw [Subtype.image_preimage_coe, Set.inter_comm, hV_compl]
  have hSplit_inter_eq : (univ \ Λ) ∩ closure Λ = subBd Λ := by
    rw [hSplit_Λ.inter, iUnion_const]
  have hInterU_Λ : (univ \ Λ) ∩ closure Λ ⊆ H'.U := by
    rw [hSplit_inter_eq]
    exact hsubBd_sub_HU.trans (isSubdrawing_U_subset hSub_H)
  have hX_sub_Λ : range v ⊆ H'.V ∩ ((univ \ Λ) ∩ closure Λ) := by
    rw [hSplit_inter_eq]
    rintro _ ⟨i, rfl⟩
    exact ⟨hSub_H.1 (hv_mem i).1, (hv_mem i).2⟩
  have hP₂_U : closure Λ ∩ H'.U ⊆ discBd (closure Λ) ∪ ⋃ j : Fin (k - 1), (P' j).U := by
    rw [hH'_U, inter_union_distrib_left]
    refine union_subset ?_ ?_
    · have h1 : closure Λ ∩ H.U ⊆ discBd (closure Λ) := by
        rw [hdiscBd, ← hcl_inter_compl]
        exact inter_subset_inter_right _ hHU_compl
      exact h1.trans subset_union_left
    · refine (inter_subset_right.trans ?_).trans subset_union_right
      refine iUnion_mono fun j => ?_
      rw [(hP' j).1]
  have hRigid_H' : IsRigid H' := by
    exact rigid_gluing_of_parallel_chords (S := S) H θ k T Λ v i_k i_last hk hv_mem hFree_v (h :=
      h) (g := g) c H' P' hSub_H hP'_disj hS hRigid_H hT hθ hΛ_open hCD hdiscBd hHU_compl hg_a
      hg_b hg_ik hg_ilast L hP' hL_line hL_sub_cl hL_inter_discBd hSplit_Λ hCap_Λ hSplit_inter_eq
      hInterU_Λ hX_sub_Λ hP₂_U
  -- Step 5: `IsSigmaSpan G H' η' θ_star θ T_star T'` and metric `d'`.
  have hH'_U_ne : H'.U.Nonempty :=
    ⟨v ⟨0, by omega⟩, H'.V_subset_U (hSub_H.1 (hv_mem ⟨0, by omega⟩).1)⟩
  have h2Cell_H' : (PaintingOrDrawing.drawing H').IsTwoCell :=
    isTwoCell_of_isRigid hS hRigid_H' hH'_U_ne
  let T' := GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ
  obtain ⟨hT'_eq, hT'_tangle, hCtrl_T'⟩ :=
    inducedTangle_eq_and_isControlling_of_isSubdrawing hSub_H hvm_H hem_H (by omega)
      hSpan.isControlling
  have hResp_T' : (PaintingOrDrawing.drawing H').IsRespectful θ T' := by
    dsimp [T']
    rw [hT'_eq]
    exact isRespectful_inducedBySubgraph' hSub_H hResp_H.2.2
  have hRDT' : IsRespectfulDrawingTangle H' θ T' := ⟨h2Cell_H', hT'_tangle, hResp_T'⟩
  have hSpan' : IsSigmaSpan G H' η' θ_star θ T_star T' :=
    { isSurface := hSpan.isSurface
      isConnected := hSpan.isConnected
      bd_empty := hSpan.bd_empty
      isRigid := hRigid_H'
      isRespectful := hRDT'
      isControlling := hCtrl_T' }
  obtain ⟨K', hK'⟩ := GM11.exists_radialDrawing hS hRDT'.1
  obtain ⟨ins', hins'⟩ := exists_derivedSlope hRDT' hK'.2.1
  let d' : Set S → Set S → ℕ := fun x y =>
    if x ∈ H'.A ∧ y ∈ H'.A then tangleMetric H' K' ins' θ x y else d x y
  have hd' : HasTangleMetric H' θ T' d' :=
    ⟨hRDT', K', ins', hK', hins', fun x hx y hy => by
      dsimp [d']
      rw [ite_eq_left ⟨hx, hy⟩]⟩
  have hd_le_d' : ∀ x ∈ H.A, ∀ y ∈ H.A, d x y ≤ d' x y := by
    intro x hx y hy
    by_cases hxy : x ∈ H'.A ∧ y ∈ H'.A
    · exact (GraphMinor.GM12.gm15_theorem_7_7.{w} H' H θ θ T' T d' d hS hConn hd' hSub_H hResp_H.1
        le_rfl hd).2
        rfl hT'_eq x hxy.1 y hxy.2 x hx y hy Subset.rfl Subset.rfl
    · dsimp [d']
      rw [ite_eq_right hxy]
  -- Step 6: Cap regions `r₁, r₂ ⊆ Λ` and their boundary circuits.
  have extreme_regions :
      ∃ (T' : Set (Hypergraph S (Set S) × Hypergraph S (Set S)))
        (d' : Set S → Set S → ℕ) (r₁ r₂ : Set S),
        IsSigmaSpan G H' η' θ_star θ T_star T' ∧
        HasTangleMetric H' θ T' d' ∧
        r₁ ∈ H'.R ∧ r₂ ∈ H'.R ∧ r₁ ⊆ Λ ∧ r₂ ⊆ Λ ∧
        H'.interSet (univ \ Λ) = H ∧
        H'.U \ Λ = H.U ∧
        T' = GM10.inducedTangle H'.toHypergraph H.toHypergraph T θ ∧
        (∀ x ∈ H.A, ∀ y ∈ H.A, d x y ≤ d' x y) ∧
        IsOArc (subBd r₁) ∧ IsOArc (subBd r₂) ∧
        (H'.interSet (subBd r₁)).IsCircuit ∧ (H'.interSet (subBd r₂)).IsCircuit ∧
        v i_k ∈ subBd r₁ ∧ v i_last ∈ subBd r₂ ∧
        (∀ w₁ w₂ w₃ w₄ : S,
          w₁ ∈ H.V ∩ subBd Λ → w₂ ∈ H.V ∩ subBd Λ →
          w₃ ∈ H.V ∩ subBd Λ → w₄ ∈ H.V ∩ subBd Λ →
          (List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁, w₂, w₃, w₄] ++
            List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)).Nodup →
          GM12.IsListedInOrderOn (subBd Λ)
            (List.ofFn (fun j : Fin (k - 1) => v ⟨j.1, by omega⟩) ++ [w₁, w₂, w₃, w₄] ++
              List.ofFn (fun j : Fin k => v ⟨k + j.1, by omega⟩)) →
          w₁ ∈ (H'.interSet (subBd r₁)).V ∧ w₂ ∈ (H'.interSet (subBd r₁)).V ∧
          w₃ ∈ (H'.interSet (subBd r₁)).V ∧ w₄ ∈ (H'.interSet (subBd r₁)).V ∧
          OccurInCircuitOrder (H'.interSet (subBd r₁)) w₁ w₂ w₃ w₄) ∧
        (∀ u₁ u₂ u₃ u₄ : S,
          u₁ ∈ H.V ∩ subBd Λ → u₂ ∈ H.V ∩ subBd Λ →
          u₃ ∈ H.V ∩ subBd Λ → u₄ ∈ H.V ∩ subBd Λ →
          (List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩) ++ [u₁, u₂, u₃, u₄]).Nodup →
          GM12.IsListedInOrderOn (subBd Λ)
            (List.ofFn (fun j : Fin (2 * k - 1) => v ⟨j.1, by omega⟩) ++ [u₁, u₂, u₃, u₄]) →
          u₁ ∈ (H'.interSet (subBd r₂)).V ∧ u₂ ∈ (H'.interSet (subBd r₂)).V ∧
          u₃ ∈ (H'.interSet (subBd r₂)).V ∧ u₄ ∈ (H'.interSet (subBd r₂)).V ∧
          OccurInCircuitOrder (H'.interSet (subBd r₂)) u₁ u₂ u₃ u₄) ∧
        2 * k - 6 ≤ d' r₁ r₂ ∧ 2 * k - 8 ≤ d' {v i_k} {v i_last} := by
    exact parallel_chord_cap_regions (S := S) (α := α) (β := β) G H θ_star θ k T_star T d Λ v i_k
      i_last hOArc hk hv_mem hFree_v hik hilast p_circ hp_circ_v (h := h) (g := g) c hg_circ H' η'
      P' hH'_V hH'_E hSub_H hP'_disj hS hResp_H hT h2k_le hk1 hΛ_open hout hCD hdiscBd
      hsubBd_sub_HU hHU_compl hg_a hg_b hik_eq hg_ik hg_ilast hP' hH'_U hL_line ha_V hb_V
      hInter_compl hH'U_sdiff_Λ h2Cell_H' hT'_eq hSpan' d' hd' hd_le_d'
  exact extreme_regions

end Theorem34

end GraphMinor.GM15
