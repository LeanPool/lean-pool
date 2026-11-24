/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2StraightArcChart
public import LeanPool.GraphMinor.GM12.Section2RayChartPatch

/-!
# An isolated arc end has a ray chart

For the leaf-entry patch on XII page 243, remove the other edges and
the far part of the incident edge from a neighbourhood of the leaf.
The drawing there is exactly the initial part of one arc. Straight
coordinates identify this arc with an increasing real interval.
Restrict the chart to points before its far endpoint and to the chosen
neighbourhood. The drawing is then exactly the positive real ray,
so the slit-patch construction applies.
-/

public section

namespace GraphMinor.GM12

open Set Topology Complex Surface

/-- A set which agrees near an arc's initial endpoint with that arc
has an open ray chart at the endpoint. -/
theorem exists_ray_chart_of_arc_germ
    {S : Type*} [TopologicalSpace S]
    (hman : ∀ x : S, IsManifoldPoint x)
    {R : ℝ} {U : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : BallChart R U h g) {a : unitInterval → S} (ha : IsArcMap a) (hU : range a ⊆ U)
    {B W : Set S} (haB : range a ⊆ B) (hW : IsOpen W) (haW : a 0 ∈ W)
    (hBW : B ∩ W ⊆ range a) :
    ∃ (O : Set ℂ) (K : ℂ → S) (q : ℂ),
      IsOpen O ∧ ContinuousOn K O ∧ InjOn K O ∧
      (∀ V : Set ℂ, IsOpen V → V ⊆ O → IsOpen (K '' V)) ∧
      q ∈ O ∧ q.im = 0 ∧ K q = a 0 ∧
      ∀ z ∈ O, K z ∈ B ↔ z.im = 0 ∧ q.re ≤ z.re := by
  obtain ⟨O, K, θ, hO, hK, hi, ho, hθc, hθm, hθ⟩ :=
    exists_straight_arc_chart hman c ha hU
  let O' := (O ∩ K ⁻¹' W) ∩ {z : ℂ | z.re < θ 1}
  have hO' : IsOpen O' :=
    (hK.isOpen_inter_preimage hO hW).inter (isOpen_Iio.preimage continuous_re)
  have hsub : O' ⊆ O := inter_subset_left.trans inter_subset_left
  have hqW : K (θ 0) ∈ W := by rw [(hθ 0).2]; exact haW
  have hqO : ((θ 0 : ℝ) : ℂ) ∈ O' :=
    ⟨⟨(hθ 0).1, hqW⟩, by simpa using hθm zero_lt_one⟩
  refine ⟨O', K, (θ 0 : ℂ), hO', hK.mono hsub, hi.mono hsub,
    fun V hV hVO => ho V hV (hVO.trans hsub), hqO, by simp, (hθ 0).2, ?_⟩
  intro z hz
  constructor
  · intro hzB
    obtain ⟨t, ht⟩ := hBW ⟨hzB, hz.1.2⟩
    have he : K z = K (θ t) := ht.symm.trans (hθ t).2.symm
    have hzθ : z = (θ t : ℂ) := hi (hsub hz) (hθ t).1 he
    rw [hzθ]
    exact ⟨by simp, by simpa using hθm.monotone (unitInterval.nonneg t)⟩
  · rintro ⟨hzim, hzr⟩
    have hzr' : θ 0 ≤ z.re := by simpa using hzr
    have hzI : z.re ∈ Icc (θ 0) (θ 1) := ⟨hzr', hz.2.le⟩
    obtain ⟨t, _, ht⟩ := intermediate_value_Icc (show (0 : unitInterval) ≤ 1 from zero_le_one)
      hθc.continuousOn hzI
    have hθz : (θ t : ℂ) = z := Complex.ext (by simpa using ht) (by simpa using hzim.symm)
    have hKz : K z = a t := by rw [← hθz]; exact (hθ t).2
    exact hKz.symm ▸ haB (mem_range_self t)

/-- The ray chart at an isolated arc end yields a simply connected
patch with path-connected puncture and the required local coverage. -/
theorem exists_slit_patch_of_arc_germ
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hman : ∀ x : S, IsManifoldPoint x)
    {R : ℝ} {U : Set S} {h : S → ℂ} {g : ℂ → S}
    (c : BallChart R U h g) {a : unitInterval → S} (ha : IsArcMap a) (hU : range a ⊆ U)
    {B W : Set S} (haB : range a ⊆ B) (hW : IsOpen W) (haW : a 0 ∈ W)
    (hBW : B ∩ W ⊆ range a) :
    ∃ N X : Set S, IsOpen N ∧ a 0 ∈ N ∧ a 0 ∈ X ∧
      IsSimplyConnectedSet X ∧ IsPathConnected (X \ {a 0}) ∧
      X ⊆ Bᶜ ∪ {a 0} ∧ N \ B ⊆ X := by
  obtain ⟨O, K, q, hO, hK, hi, ho, hq, hqim, hKq, hB⟩ :=
    exists_ray_chart_of_arc_germ hman c ha hU haB hW haW hBW
  have hpatch := exists_slit_patch_of_ray_chart hO hK hi ho hq hqim hB
  rwa [hKq] at hpatch

end GraphMinor.GM12
