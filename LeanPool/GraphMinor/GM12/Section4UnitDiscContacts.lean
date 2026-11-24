/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4ConvexBoundaryParam
import LeanPool.GraphMinor.GM19.DiscTouch

/-!
# A unit subdisc retaining the parameters of its contacts

For the target disc preparation of XII (4.5), page 253, take
the convex hull of the prescribed unit-circle marks and the
closed disc of radius one half. Strict convexity puts every
other point inside the unit circle. The radial boundary
parametrization fixes each prescribed mark, so their circle
parameters and cyclic order are retained.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric Topology

/-- A finite nonempty set on the unit circle is exactly the
contact set of a smaller closed disc. Its boundary can be
parametrized so that each contact keeps its original circle
parameter, as needed for XII (4.5)'s target discs, page 253. -/
theorem exists_unit_disc_contacts_with_param {N : Set ℂ}
    (hN : N ⊆ sphere 0 1) (hfin : N.Finite) (hne : N.Nonempty) :
    ∃ (K : Set ℂ) (p : Circle → ℂ), IsClosedDisc K ∧ K ⊆ closedBall 0 1 ∧
      K ∩ sphere 0 1 = N ∧ N ⊆ discBd K ∧
      Continuous p ∧ Function.Injective p ∧ range p = discBd K ∧
      ∀ w : Circle, (w : ℂ) ∈ N → p w = w := by
  let K := convexHull ℝ (N ∪ closedBall (0 : ℂ) (1 / 2))
  have hKcompact : IsCompact K := GM19.isCompact_convexHull_union hfin hne
    (isCompact_closedBall _ _) (convex_closedBall _ _) ⟨0, by simp⟩
  have hKconvex : Convex ℝ K := convex_convexHull _ _
  have hsmall : ball (0 : ℂ) (1 / 2) ⊆ K :=
    ball_subset_closedBall.trans (subset_union_right.trans (subset_convexHull _ _))
  have h0 : K ∈ 𝓝 (0 : ℂ) := Filter.mem_of_superset (ball_mem_nhds _ (by norm_num)) hsmall
  have hKN : K ⊆ ball (0 : ℂ) 1 ∪ N :=
    convexHull_min (union_subset subset_union_right
      (fun x hx => Or.inl (closedBall_subset_ball (by norm_num) hx)))
      (GM19.convex_ball_union_of_subset_sphere hN)
  have hKsub : K ⊆ closedBall (0 : ℂ) 1 :=
    hKN.trans (union_subset ball_subset_closedBall (hN.trans sphere_subset_closedBall))
  have hNK : N ⊆ K := fun n hn => subset_convexHull ℝ _ (Or.inl hn)
  obtain ⟨hKd, p, hpcont, hpinj, hprange, hpfix⟩ :=
    exists_convex_boundary_param_fixing_circle hKconvex h0 hKcompact.isBounded hKcompact.isClosed
      hKsub
  have hcontact : K ∩ sphere (0 : ℂ) 1 = N := by
    apply Subset.antisymm
    · rintro z ⟨hzK, hzS⟩
      rcases hKN hzK with hzB | hzN
      · have hlt := mem_ball_zero_iff.mp hzB
        rw [mem_sphere_zero_iff_norm.mp hzS] at hlt
        exact False.elim ((lt_irrefl (1 : ℝ)) hlt)
      · exact hzN
    · intro z hz
      exact ⟨hNK hz, hN hz⟩
  have hNbd : N ⊆ discBd K := by
    intro n hn
    let w : Circle := ⟨n, hN hn⟩
    have hfix : p w = n := hpfix w (hNK hn)
    exact hprange ▸ (show n ∈ range p from ⟨w, hfix⟩)
  exact ⟨K, p, hKd, hKsub, hcontact, hNbd, hpcont, hpinj, hprange,
    (fun w hw => hpfix w (hNK hw))⟩

end GraphMinor.GM12
