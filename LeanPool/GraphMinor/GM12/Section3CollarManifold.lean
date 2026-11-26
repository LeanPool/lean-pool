/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CollarComplement
public import LeanPool.GraphMinor.GM12.Section3CircleExterior
public import LeanPool.GraphMinor.GM12.Section3RestrictedCharts
import LeanPool.GraphMinor.Surface.DiscsInSurface

/-!
# Surface charts at a deleted disc boundary

In XII (3.1), page 245, the collar of a deleted disc identifies the
remaining surface with the circle exterior. The collar is open near
the inner circle by invariance of domain. Restricting this open map
transfers the half-plane chart to the remaining surface.
-/

public section

namespace GraphMinor.GM12

open Set Metric Topology Surface

/-- A collar avoiding all other deleted discs supplies a surface chart
at each point of its inner boundary. -/
theorem isManifoldPoint_discComplement_of_collar
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (i : ι) {E : Set S} {c : ℂ → S} {c' : S → ℂ}
    (hc : ContinuousOn c (closedBall 0 2)) (hc' : ContinuousOn c' E)
    (hcE : MapsTo c (closedBall 0 2) E)
    (hmiss : ∀ j, j ≠ i → Disjoint E (Δ j))
    (hl : LeftInvOn c' c (closedBall 0 2))
    (himage : c '' closedBall 0 1 = Δ i)
    (p : Circle ≃ₜ discBd (Δ i)) (hp : ∀ w : Circle, c w = (p w).val)
    (w : Circle) :
    IsManifoldPoint (⟨c w, disc_boundary_subset_discComplement hS Δ hΔ hdisj i
      (hp w ▸ (p w).property)⟩ : discComplement Δ) := by
  let M : Set ℂ := ball 0 2
  have hMsub : M ⊆ closedBall (0 : ℂ) 2 := ball_subset_closedBall
  have himsub : c '' M ⊆ E := image_subset_iff.mpr (hcE.mono hMsub Subset.rfl)
  obtain ⟨f, hf⟩ := exists_homeomorph_image (hc.mono hMsub) (hc'.mono himsub)
    (hl.mono hMsub)
  have hopen : IsOpen (c '' M) := isOpen_image_of_manifold isOpen_ball
    (hc.mono hMsub) (hl.injOn.mono hMsub) (fun _ _ => (hS.2.2 _).isManifoldPoint)
  let e : M → S := fun z => c z.val
  have heq : e = Subtype.val ∘ f := by
    funext z
    exact (hf z).symm
  have he : IsOpenEmbedding e := by
    rw [heq]
    exact hopen.isOpenEmbedding_subtypeVal.comp f.isOpenEmbedding
  have hwM : (w : ℂ) ∈ M := by
    rw [mem_ball_zero_iff, Circle.norm_coe]
    norm_num
  have hmem : ∀ z : M, e z ∈ discComplement Δ ↔ 1 ≤ ‖z.val‖ := fun z =>
    collar_mem_discComplement_iff hS Δ hΔ hdisj i hcE hmiss hl himage p hp (hMsub z.property)
  exact isManifoldPoint_of_open_coordinate_model (Y := {z : ℂ | 1 ≤ ‖z‖}) isOpen_ball he hmem
    (z := ⟨w, hwM⟩) (by change 1 ≤ ‖(w : ℂ)‖; rw [Circle.norm_coe])
    (isManifoldPoint_circleExterior_boundary (Circle.norm_coe w))

end GraphMinor.GM12
