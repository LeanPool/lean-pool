/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2SlitBall
public import LeanPool.GraphMinor.GM12.Section2StarChart
import LeanPool.GraphMinor.Surface.Gluing

/-!
# A simply connected patch beside the end of a ray

For the leaf-entry patch on XII page 243, assume coordinates identify
the drawing with the positive real ray. Map a slit ball back to the
surface, keeping its tip. The ball's star contraction proves simple
connectedness, and the punctured slit ball stays path-connected.
The chart is open, so all sufficiently near points off the drawing
belong to this patch.
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric Surface

/-- Open injective coordinates identifying a closed-set germ with a
ray supply the required contractible slit patch at its endpoint. -/
theorem exists_slit_patch_of_ray_chart
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {O : Set ℂ} {K : ℂ → S} (hO : IsOpen O) (hK : ContinuousOn K O) (hi : InjOn K O)
    (ho : ∀ W : Set ℂ, IsOpen W → W ⊆ O → IsOpen (K '' W))
    {q : ℂ} (hq : q ∈ O) (hqim : q.im = 0) {B : Set S}
    (hB : ∀ z ∈ O, K z ∈ B ↔ z.im = 0 ∧ q.re ≤ z.re) :
    ∃ N X : Set S, IsOpen N ∧ K q ∈ N ∧ K q ∈ X ∧
      IsSimplyConnectedSet X ∧ IsPathConnected (X \ {K q}) ∧
      X ⊆ Bᶜ ∪ {K q} ∧ N \ B ⊆ X := by
  classical
  obtain ⟨ε, hε, hεO⟩ := Metric.isOpen_iff.mp hO q hq
  let δ := ε / 2
  have hδ : 0 < δ := half_pos hε
  have hδle : δ < ε := by dsimp [δ]; linarith
  have hclosed : closedBall q δ ⊆ O := (closedBall_subset_ball hδle).trans hεO
  have hball : ball q δ ⊆ O := ball_subset_closedBall.trans hclosed
  let A := ball q δ ∩ {z : ℂ | z.im ≠ 0 ∨ z.re ≤ q.re}
  have hqA : q ∈ A := ⟨mem_ball_self hδ, Or.inr le_rfl⟩
  have hAO : A ⊆ O := inter_subset_left.trans hball
  have hAclosed : A ⊆ closedBall q δ := inter_subset_left.trans ball_subset_closedBall
  obtain ⟨k, hkc, hkinv⟩ := exists_inv_of_compactOn (isCompact_closedBall q δ)
    (hK.mono hclosed) (hi.mono hclosed)
  have hsimple : IsSimplyConnectedSet (K '' A) := image_starConvex_isSimplyConnected
    (hK.mono hAO) (hkc.mono (image_mono hAclosed))
    (fun z hz => hkinv (hAclosed hz)) (starConvex_slit_ball_tip hqim hδ) hqA
  have hpunct : (K '' A) \ {K q} = K '' (A \ {q}) := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzne⟩
      exact ⟨z, ⟨hz, fun he => hzne (congrArg K he)⟩, rfl⟩
    · rintro ⟨z, ⟨hz, hzne⟩, rfl⟩
      refine ⟨⟨z, hz, rfl⟩, ?_⟩
      intro he
      exact hzne (hi (hAO hz) hq he)
  have hpath : IsPathConnected ((K '' A) \ {K q}) := by
    rw [hpunct]
    exact (isPathConnected_slit_ball_puncture hqim hδ).image'
      (hK.mono (sdiff_subset.trans hAO))
  refine ⟨K '' ball q δ, K '' A, ho _ isOpen_ball hball,
    mem_image_of_mem K (mem_ball_self hδ), mem_image_of_mem K hqA, hsimple, hpath, ?_, ?_⟩
  · rintro x ⟨z, hz, rfl⟩
    by_cases hzB : K z ∈ B
    · have hray := (hB z (hAO hz)).mp hzB
      have hzre : z.re = q.re := by
        rcases hz.2 with hzim | hzre
        · exact (hzim hray.1).elim
        · exact le_antisymm hzre hray.2
      have hzq : z = q := Complex.ext hzre (hray.1.trans hqim.symm)
      exact Or.inr (congrArg K hzq)
    · exact Or.inl hzB
  · rintro x ⟨⟨z, hzball, rfl⟩, hzB⟩
    refine ⟨z, ⟨hzball, ?_⟩, rfl⟩
    by_cases hzim : z.im = 0
    · right
      have hn : ¬ q.re ≤ z.re := fun hle => hzB ((hB z (hball hzball)).mpr ⟨hzim, hle⟩)
      exact (lt_of_not_ge hn).le
    · exact Or.inl hzim

end GraphMinor.GM12
