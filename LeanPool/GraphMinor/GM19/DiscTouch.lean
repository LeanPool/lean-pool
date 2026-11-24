/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM19.FragmentCollapse
public import LeanPool.GraphMinor.Surface.ArcDisc
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.Analysis.InnerProductSpace.Convex
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Join

/-!
# A smaller disc that touches the boundary in given points

Let `D` be a closed disc and let `N` be a finite nonempty subset of its boundary. Then `D` holds a
closed disc that meets the boundary of `D` exactly in `N`. In the unit disc we take the convex hull
of `N` and a smaller disc. The
hull meets the unit circle only in `N`, since a segment between two points of the closed unit disc
lies in the open disc except at its ends.

The proof of (15.2) applies this to the disc of a cuff and to the disc of an edge of size 3.
-/

@[expose] public section

namespace GraphMinor.GM19

open Set Topology Metric GraphMinor.Surface

/-- The convex hull of a nonempty finite set of the plane and a compact convex nonempty set is
compact. -/
theorem isCompact_convexHull_union {A B : Set ℂ} (hA : A.Finite) (hAn : A.Nonempty)
  (hB : IsCompact B) (hBc : Convex ℝ B) (hBn : B.Nonempty) : IsCompact (convexHull ℝ (A ∪ B)) := by
  rw [convexHull_union (hAn) hBn, hBc.convexHull_eq]
  have hA' : IsCompact (convexHull ℝ A) := hA.isCompact_convexHull (𝕜 := ℝ)
  have himg : convexJoin ℝ (convexHull ℝ A) B = (fun p : ℂ × ℂ × ℝ =>
    (1 - p.2.2) • p.1 + p.2.2 • p.2.1) '' (convexHull ℝ A ×ˢ B ×ˢ Icc 0 1) := by
    ext x
    rw [mem_convexJoin]
    constructor
    · rintro ⟨a, ha, b, hb, hx⟩
      rw [segment_eq_image] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨(a, b, t), ⟨ha, hb, ht⟩, rfl⟩
    · rintro ⟨⟨a, b, t⟩, ⟨ha, hb, ht⟩, rfl⟩
      refine ⟨a, ha, b, hb, ?_⟩
      rw [segment_eq_image]
      exact ⟨t, ht, rfl⟩
  rw [himg]
  exact (hA'.prod (hB.prod isCompact_Icc)).image (by fun_prop)

/-- The open unit disc with a set of points of the unit circle is convex. -/
theorem convex_ball_union_of_subset_sphere {N : Set ℂ} (hN : N ⊆ sphere 0 1) : Convex ℝ (ball
  (0 : ℂ) 1 ∪ N) := by
  have hstrict : StrictConvex ℝ (closedBall (0 : ℂ) 1) := strictConvex_closedBall ℝ 0 1
  have hint : interior (closedBall (0 : ℂ) 1) = ball 0 1 := interior_closedBall _ one_ne_zero
  have hsub : ball (0 : ℂ) 1 ∪ N ⊆ closedBall 0 1 := union_subset ball_subset_closedBall
    (hN.trans sphere_subset_closedBall)
  intro x hx y hy a b ha hb hab
  rcases ha.eq_or_lt with rfl | ha'
  · have : b = 1 := by linarith
    subst this
    simpa using hy
  rcases hb.eq_or_lt with rfl | hb'
  · have : a = 1 := by linarith
    subst this
    simpa using hx
  by_cases hxy : x = y
  · subst hxy
    have : a • x + b • x = x := by rw [← add_smul, hab, one_smul]
    rwa [this]
  · exact .inl (hint ▸ hstrict (hsub hx) (hsub hy) hxy ha' hb' hab)

variable {S : Type} [TopologicalSpace S] [T2Space S]

/-- **A disc that touches the boundary of a closed disc in a given finite set.** -/
theorem IsClosedDisc.exists_touching {D : Set S} (hD : IsClosedDisc D) {N : Set S}
  (hN : N ⊆ discBd D) (hfin : N.Finite) (hne : N.Nonempty) :
    ∃ D', IsClosedDisc D' ∧ D' ⊆ D ∧ D' ∩ discBd D = N ∧ N ⊆ discBd D' := by
  classical
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  set N₀ := h '' N with hN₀
  have hNs : N₀ ⊆ sphere 0 1 := fun x hx => by
    obtain ⟨y, hy, rfl⟩ := hx
    exact c.bd ▸ mem_image_of_mem h (hN hy)
  set K := convexHull ℝ (N₀ ∪ closedBall (0 : ℂ) (1 / 2)) with hK
  have hKcpt : IsCompact K := isCompact_convexHull_union (hfin.image h) (hne.image h)
    (isCompact_closedBall _ _) (convex_closedBall _ _) ⟨0, by simp⟩
  have hKcl : IsClosed K := hKcpt.isClosed
  have hKc : Convex ℝ K := convex_convexHull _ _
  have hsmall : ball (0 : ℂ) (1 / 2) ⊆ K := ball_subset_closedBall.trans (subset_union_right.trans
    (subset_convexHull _ _))
  have hKQ : K ⊆ ball 0 1 ∪ N₀ := convexHull_min (union_subset subset_union_right (fun x hx => .inl
    (closedBall_subset_ball (by norm_num) hx))) (convex_ball_union_of_subset_sphere hNs)
  have hKb : K ⊆ closedBall 0 1 := hKQ.trans (union_subset ball_subset_closedBall
    (hNs.trans sphere_subset_closedBall))
  have hint : (interior K).Nonempty := by
    refine ⟨0, interior_mono hsmall ?_⟩
    rw [isOpen_ball.interior_eq]
    simp
  obtain ⟨hKd, hKf⟩ := isClosedDisc_of_convex hKc hint (isBounded_closedBall.subset hKb) hKcl
  have hgi : InjOn g K := fun x hx y hy he => by
    have h₁ := c.hg (hKb hx)
    have h₂ := c.hg (hKb hy)
    rw [← h₁, ← h₂]
    exact congrArg h he
  obtain ⟨hd', hb'⟩ := isClosedDisc_image_injOn hKd (c.gc.mono hKb) hgi
  rw [hKf] at hb'
  have hmemK : ∀ n ∈ N, h n ∈ K := fun n hn => subset_convexHull _ _ (.inl (mem_image_of_mem _ hn))
  have hgh : ∀ n ∈ N, g (h n) = n := fun n hn => c.gh (Surface.discBd_subset _ (hN hn))
  refine ⟨g '' K, hd', ?_, ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact c.gm (hKb hy)
  · ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hb⟩
      have h₁ : h (g y) ∈ sphere (0 : ℂ) 1 := c.bd ▸ mem_image_of_mem h hb
      rw [c.hg (hKb hy)] at h₁
      rcases hKQ hy with hy' | ⟨n, hn, rfl⟩
      · exact absurd h₁ (fun h' => (ne_of_lt (mem_ball_zero_iff.mp hy'))
        (mem_sphere_zero_iff_norm.mp h'))
      · rwa [hgh n hn]
    · intro hx
      exact ⟨⟨h x, hmemK x hx, hgh x hx⟩, hN hx⟩
  · intro n hn
    rw [hb', ← hgh n hn]
    refine mem_image_of_mem _ ⟨subset_closure (hmemK n hn), fun hi => ?_⟩
    have h₁ : h n ∈ ball (0 : ℂ) 1 := by
      have := interior_mono hKb hi
      rwa [interior_closedBall _ one_ne_zero] at this
    have h₂ : h n ∈ sphere (0 : ℂ) 1 := hNs (mem_image_of_mem _ hn)
    exact (ne_of_lt (mem_ball_zero_iff.mp h₁)) (mem_sphere_zero_iff_norm.mp h₂)

end GraphMinor.GM19
