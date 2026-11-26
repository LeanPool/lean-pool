/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM09.EarCompare
public import LeanPool.GraphMinor.GM09.RuralAdd

/-!
# Placing small discs in a closed disc

The last step of (11.11) of Graph Minors IX places a closed disc for each small clique of a rural
neighborhood, so that the discs meet only at common vertices. This file holds the plane facts that
step needs.

A closed disc contains a smaller closed disc that meets its boundary in any given finite set
(`exists_inscribed_disc`). Each point of a closed disc lies on the boundary of an arbitrarily small
closed disc that meets the outer boundary at most there (`exists_small_disc_at`). Finitely many
lines can be thickened one after another to closed discs that meet only at common ends
(`exists_lenses`).
-/

@[expose] public section

namespace GraphMinor.GM09

open Set Function Topology Metric GraphMinor GraphMinor.Surface

universe u

/-- A point of the unit circle is not in the closed convex hull of a small ball and a finite subset
of the unit circle that misses it. -/
theorem not_mem_closure_convexHull_of_sphere {F : Set ℂ} (hfin : F.Finite) (hF : F ⊆ sphere 0 1)
    {x : ℂ} (hx : ‖x‖ = 1) (hxF : x ∉ F) :
    x ∉ closure (convexHull ℝ (F ∪ closedBall 0 (1 / 2))) := by
  set A : Set ℂ := F ∪ closedBall 0 (1 / 2) with hA
  have hAc : IsCompact A := hfin.isCompact.union (isCompact_closedBall _ _)
  have hAne : A.Nonempty := ⟨0, Or.inr (by simp)⟩
  have hlt : ∀ y ∈ A, inner ℝ x y < 1 := by
    rintro y (hy | hy)
    · have hy1 : ‖y‖ = 1 := by simpa using hF hy
      refine lt_of_le_of_ne ?_ fun h => hxF ?_
      · have := real_inner_le_norm x y
        rwa [hx, hy1, one_mul] at this
      · rw [(inner_eq_one_iff_of_norm_eq_one hx hy1).mp h]
        exact hy
    · have hy1 : ‖y‖ ≤ 1 / 2 := by simpa using hy
      have := real_inner_le_norm x y
      rw [hx] at this
      linarith
  have hcf : Continuous fun y : ℂ => inner ℝ x y := continuous_const.inner continuous_id
  obtain ⟨y₀, hy₀, hmax⟩ := hAc.exists_isMaxOn hAne hcf.continuousOn
  have hsub : A ⊆ {y : ℂ | inner ℝ x y ≤ inner ℝ x y₀} := fun y hy => hmax hy
  have hconv : Convex ℝ {y : ℂ | inner ℝ x y ≤ inner ℝ x y₀} :=
    convex_halfSpace_le (f := fun y => inner ℝ x y)
      ⟨fun a b => inner_add_right _ _ _, fun c a => inner_smul_right _ _ _⟩ _
  have hcl : IsClosed {y : ℂ | inner ℝ x y ≤ inner ℝ x y₀} :=
    isClosed_le hcf continuous_const
  intro h
  have h' := closure_minimal (convexHull_min hsub hconv) hcl h
  have h₁ : inner ℝ x x ≤ inner ℝ x y₀ := h'
  have h₂ := hlt y₀ hy₀
  rw [real_inner_self_eq_norm_sq, hx] at h₁
  linarith

/-- A finite subset of the unit circle is the trace on the circle of a closed disc in the unit
disc that has the finite set on its boundary. -/
theorem exists_inscribed_disc_unit {F : Set ℂ} (hF : F.Finite) (hs : F ⊆ sphere 0 1) :
    ∃ K ⊆ closedBall (0 : ℂ) 1, IsClosedDisc K ∧ F ⊆ discBd K ∧ K ∩ sphere 0 1 = F := by
  set A : Set ℂ := F ∪ closedBall 0 (1 / 2) with hA
  have hAb : A ⊆ closedBall 0 1 := by
    refine union_subset (hs.trans sphere_subset_closedBall)
      (closedBall_subset_closedBall (by norm_num))
  have hK : closure (convexHull ℝ A) ⊆ closedBall 0 1 :=
    closure_minimal (convexHull_min hAb (convex_closedBall 0 1)) isClosed_closedBall
  have hbdd : Bornology.IsBounded (closure (convexHull ℝ A)) := isBounded_closedBall.subset hK
  have hbig : closedBall (0 : ℂ) (1 / 2) ⊆ closure (convexHull ℝ A) :=
    (subset_union_right.trans (subset_convexHull ℝ A)).trans subset_closure
  have hne : (interior (closure (convexHull ℝ A))).Nonempty := by
    refine ⟨0, interior_mono hbig ?_⟩
    rw [interior_closedBall _ (by norm_num)]
    simp
  obtain ⟨hd, hbd⟩ := isClosedDisc_of_convex (convex_convexHull ℝ A).closure hne hbdd
    isClosed_closure
  have hmem : ∀ x ∈ F, x ∈ closure (convexHull ℝ A) := fun x hx =>
    subset_closure (subset_convexHull ℝ A (Or.inl hx))
  refine ⟨_, hK, hd, ?_, ?_⟩
  · intro x hx
    rw [hbd, isClosed_closure.frontier_eq]
    refine ⟨hmem x hx, fun hi => ?_⟩
    have h := interior_mono hK hi
    rw [interior_closedBall _ (by norm_num)] at h
    have h1 : ‖x‖ = 1 := by simpa using hs hx
    simp [h1] at h
  · ext x
    constructor
    · rintro ⟨hx, hxs⟩
      by_contra hxF
      exact not_mem_closure_convexHull_of_sphere hF hs (by simpa using hxs) hxF hx
    · intro hx
      exact ⟨hmem x hx, hs hx⟩

/-- A finite subset of the boundary of a closed disc is the trace on that boundary of a closed disc
inside it that has the finite set on its own boundary. -/
theorem exists_inscribed_disc {S : Type u} [TopologicalSpace S] {D F : Set S} (hD : IsClosedDisc D)
    (hF : F.Finite) (hs : F ⊆ discBd D) :
    ∃ K ⊆ D, IsClosedDisc K ∧ F ⊆ discBd K ∧ K ∩ discBd D = F := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hFD : F ⊆ D := hs.trans (Surface.discBd_subset D)
  have himg : h '' F ⊆ sphere 0 1 := by
    rw [← c.bd]
    exact image_mono hs
  obtain ⟨K, hK, hd, hb, ht⟩ := exists_inscribed_disc_unit (hF.image h) himg
  obtain ⟨hd', hbd'⟩ := c.disc_g hK hd
  refine ⟨g '' K, c.g_subset hK, hd', ?_, ?_⟩
  · rw [hbd']
    intro x hx
    exact ⟨h x, hb (mem_image_of_mem h hx), c.gh (hFD hx)⟩
  · ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzb⟩
      have hzs : h (g z) ∈ sphere (0 : ℂ) 1 := by
        rw [← c.bd]
        exact mem_image_of_mem h hzb
      rw [c.hg (hK hz)] at hzs
      have hzm : z ∈ K ∩ sphere 0 1 := ⟨hz, hzs⟩
      rw [ht] at hzm
      obtain ⟨y, hy, rfl⟩ := hzm
      rwa [c.gh (hFD hy)]
    · intro hx
      exact ⟨⟨h x, Surface.discBd_subset K (hb (mem_image_of_mem h hx)), c.gh (hFD hx)⟩, hs hx⟩

/-- A closed round disc of positive radius in the complex plane is a closed disc. -/
theorem isClosedDisc_closedBall_complex (c : ℂ) {r : ℝ} (hr : 0 < r) :
    IsClosedDisc (closedBall c r) ∧ discBd (closedBall c r) = sphere c r := by
  have h := isClosedDisc_of_convex (convex_closedBall c r)
    (by
      rw [interior_closedBall _ hr.ne']
      exact ⟨c, by simpa using hr⟩) isBounded_closedBall isClosed_closedBall
  rw [frontier_closedBall _ hr.ne'] at h
  exact h

/-- Each point of the unit disc is on the boundary of a small round disc in the unit disc, which
meets the unit circle at most in that point. -/
theorem exists_small_ball_at {p : ℂ} (hp : ‖p‖ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ (c : ℂ) (r : ℝ), 0 < r ∧ closedBall c r ⊆ closedBall 0 1 ∧ closedBall c r ⊆ ball p ε ∧
      p ∈ sphere c r ∧ closedBall c r ∩ sphere 0 1 ⊆ {p} := by
  have hnear : ∀ {c : ℂ} {r : ℝ}, 3 * r < ε → dist p c = r → closedBall c r ⊆ ball p ε := by
    intro c r hr hd x hx
    have h₁ : dist x c ≤ r := hx
    have := dist_triangle x c p
    rw [dist_comm c p, hd] at this
    rw [mem_ball]
    have hr0 : 0 ≤ r := hd ▸ dist_nonneg
    linarith
  rcases hp.lt_or_eq with hlt | heq
  · set r : ℝ := min (ε / 4) ((1 - ‖p‖) / 4) with hr
    have hr0 : 0 < r := lt_min (by linarith) (by linarith)
    have hr1 : r ≤ ε / 4 := min_le_left _ _
    have hr2 : r ≤ (1 - ‖p‖) / 4 := min_le_right _ _
    have hdist : dist p (p + (r : ℂ)) = r := by
      rw [dist_eq_norm]
      simp [abs_of_pos hr0]
    have hbound : ∀ x ∈ closedBall (p + (r : ℂ)) r, ‖x‖ < 1 := by
      intro x hx
      have h₁ : dist x (p + (r : ℂ)) ≤ r := hx
      have h₂ : ‖x‖ ≤ dist x (p + (r : ℂ)) + ‖p + (r : ℂ)‖ := by
        rw [dist_eq_norm]
        simpa using norm_add_le (x - (p + (r : ℂ))) (p + (r : ℂ))
      have h₃ : ‖p + (r : ℂ)‖ ≤ ‖p‖ + r := by
        refine (norm_add_le _ _).trans ?_
        simp [abs_of_pos hr0]
      linarith
    refine ⟨p + (r : ℂ), r, hr0, fun x hx => ?_, hnear (by linarith) hdist, hdist, ?_⟩
    · simpa using (hbound x hx).le
    · rintro x ⟨hx, hxs⟩
      have h1 : ‖x‖ = 1 := by simpa using hxs
      exact absurd h1 (hbound x hx).ne
  · set r : ℝ := min (ε / 4) (1 / 2) with hr
    have hr0 : 0 < r := lt_min (by linarith) (by norm_num)
    have hr1 : r ≤ ε / 4 := min_le_left _ _
    have hr2 : r ≤ 1 / 2 := min_le_right _ _
    have hc : ‖(1 - r) • p‖ = 1 - r := by
      rw [norm_smul, heq, mul_one, Real.norm_eq_abs, abs_of_pos (by linarith)]
    have hdist : dist p ((1 - r) • p) = r := by
      rw [dist_eq_norm]
      have : p - (1 - r) • p = r • p := by
        rw [sub_smul, one_smul]
        abel
      rw [this, norm_smul, heq, mul_one, Real.norm_eq_abs, abs_of_pos hr0]
    refine ⟨(1 - r) • p, r, hr0, fun x hx => ?_, hnear (by linarith) hdist, hdist, ?_⟩
    · have h₁ : dist x ((1 - r) • p) ≤ r := hx
      have h₂ : ‖x‖ ≤ dist x ((1 - r) • p) + ‖(1 - r) • p‖ := by
        rw [dist_eq_norm]
        simpa using norm_add_le (x - (1 - r) • p) ((1 - r) • p)
      simp only [mem_closedBall, dist_zero_right]
      linarith
    · rintro x ⟨hx, hxs⟩
      have h1 : ‖x‖ = 1 := by simpa using hxs
      have h₁ : ‖x - (1 - r) • p‖ ≤ r := by
        have : dist x ((1 - r) • p) ≤ r := hx
        rwa [dist_eq_norm] at this
      have hsq : ‖x - (1 - r) • p‖ ^ 2 ≤ r ^ 2 := by
        have := norm_nonneg (x - (1 - r) • p)
        gcongr
      rw [norm_sub_sq_real, h1, hc, inner_smul_right] at hsq
      have hin : (1 : ℝ) ≤ inner ℝ x p := by
        have hpos : 0 < 1 - r := by linarith
        nlinarith
      have hle := real_inner_le_norm x p
      rw [h1, heq] at hle
      have heq' : inner ℝ x p = (1 : ℝ) := le_antisymm (by linarith) hin
      exact (inner_eq_one_iff_of_norm_eq_one h1 heq).mp heq'

/-- Each point of a closed disc is on the boundary of a closed disc inside it, in a given
neighbourhood of the point, which meets the outer boundary at most in that point. -/
theorem exists_small_disc_at {S : Type u} [TopologicalSpace S] {D W : Set S} (hD : IsClosedDisc D)
    {a : S} (ha : a ∈ D) (hW : IsOpen W) (haW : a ∈ W) :
    ∃ K ⊆ D, K ⊆ W ∧ IsClosedDisc K ∧ a ∈ discBd K ∧ K ∩ discBd D ⊆ {a} := by
  obtain ⟨h, g, c⟩ := hD.exists_isChart
  have hp : h a ∈ closedBall (0 : ℂ) 1 := c.hm ha
  have hcont : ContinuousWithinAt g (closedBall 0 1) (h a) := c.gc _ hp
  have hnhds : g ⁻¹' W ∈ 𝓝[closedBall 0 1] h a :=
    hcont (hW.mem_nhds (by rw [c.gh ha]; exact haW))
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhdsWithin_iff.mp hnhds
  obtain ⟨z, r, hr, hsub, hnear, hmem, htouch⟩ := exists_small_ball_at (by simpa using hp) hε
  obtain ⟨hd, hbd⟩ := isClosedDisc_closedBall_complex z hr
  obtain ⟨hd', hbd'⟩ := c.disc_g hsub hd
  refine ⟨g '' closedBall z r, c.g_subset hsub, ?_, hd', ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    exact hball ⟨hnear hy, hsub hy⟩
  · rw [hbd', hbd]
    exact ⟨h a, hmem, c.gh ha⟩
  · rintro _ ⟨⟨y, hy, rfl⟩, hyb⟩
    have hys : h (g y) ∈ sphere (0 : ℂ) 1 := by
      rw [← c.bd]
      exact mem_image_of_mem h hyb
    rw [c.hg (hsub hy)] at hys
    have := htouch ⟨hy, hys⟩
    rw [mem_singleton_iff] at this ⊢
    rw [this, c.gh ha]

/-- A closed set which meets the boundary of a closed disc in a finite set misses a point of the
interior of the disc. -/
theorem exists_interior_point_off {Δ Z : Set EuclideanPlane} (hΔ : IsClosedDisc Δ) (hZ : IsClosed Z)
    (hfin : (Z ∩ discBd Δ).Finite) : ∃ a ∈ interior Δ, a ∉ Z := by
  have hO := hΔ.isOArc_discBd
  obtain ⟨p, q, -, hp, hq, -, hpq, -⟩ := hO.exists_three
  have hinf : (discBd Δ).Infinite := hO.isPreconnected.infinite_of_nontrivial ⟨p, hp, q, hq, hpq⟩
  obtain ⟨b, hb, hbZ⟩ := (hinf.sdiff hfin).nonempty
  have hbZ' : b ∉ Z := fun h => hbZ ⟨h, hb⟩
  have hcl : b ∈ closure (interior Δ) := by
    rw [closure_interior_of_isClosedDisc hΔ]
    exact Surface.discBd_subset Δ hb
  obtain ⟨a, haZ, hai⟩ := mem_closure_iff.mp hcl Zᶜ hZ.isOpen_compl hbZ'
  exact ⟨a, hai, haZ⟩

/-- Thicken finitely many lines to closed discs, one after another. Each disc meets its closed set
`R i` only in the ends of its line, and two of the discs meet only in common ends. -/
theorem exists_lenses {ι : Type*} (I : Finset ι) {l R : ι → Set EuclideanPlane}
    {a b : ι → EuclideanPlane} (hl : ∀ i ∈ I, IsLineWithEnds (l i) (a i) (b i))
    (hab : ∀ i ∈ I, a i ≠ b i) (hR : ∀ i ∈ I, IsClosed (R i))
    (hmeet : ∀ i ∈ I, l i ∩ R i ⊆ {a i, b i})
    (hcross : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → l i ⊆ R j) :
    ∃ D : ι → Set EuclideanPlane, (∀ i ∈ I, IsClosedDisc (D i) ∧ l i ⊆ D i ∧
        D i ∩ R i ⊆ {a i, b i} ∧ a i ∈ discBd (D i) ∧ b i ∈ discBd (D i) ∧
        IsPreconnected (D i \ {a i, b i})) ∧
      ∀ i ∈ I, ∀ j ∈ I, i ≠ j → D i ∩ D j ⊆ {a i, b i} ∩ {a j, b j} := by
  classical
  induction I using Finset.induction_on with
  | empty => exact ⟨fun _ => ∅, by simp, by simp⟩
  | insert i I hi ih =>
    obtain ⟨D, hD, hp⟩ := ih (fun j hj => hl j (Finset.mem_insert_of_mem hj))
      (fun j hj => hab j (Finset.mem_insert_of_mem hj))
      (fun j hj => hR j (Finset.mem_insert_of_mem hj))
      (fun j hj => hmeet j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hcross j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
    have hii := Finset.mem_insert_self i I
    have hclosed : IsClosed (R i ∪ ⋃ j ∈ I, D j) :=
      (hR i hii).union (I.finite_toSet.isClosed_biUnion fun j hj => (hD j hj).1.isCompact.isClosed)
    have hne : ∀ j ∈ I, i ≠ j := fun j hj h => hi (h ▸ hj)
    have hlz : l i ∩ (R i ∪ ⋃ j ∈ I, D j) ⊆ {a i, b i} := by
      rintro x ⟨hx, hx' | hx'⟩
      · exact hmeet i hii ⟨hx, hx'⟩
      · obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp hx'
        have hin : x ∈ l i ∩ R j := ⟨hx, hcross i hii j (Finset.mem_insert_of_mem hj) (hne j hj) hx⟩
        have hend : x ∈ ({a j, b j} : Set _) := (hD j hj).2.2.1 ⟨hxj, hin.2⟩
        have hlj : l j ⊆ R i := hcross j (Finset.mem_insert_of_mem hj) i hii (hne j hj).symm
        have hxl : x ∈ l j := by
          rcases hend with rfl | rfl
          · exact (hl j (Finset.mem_insert_of_mem hj)).left_mem
          · exact (hl j (Finset.mem_insert_of_mem hj)).right_mem
        exact hmeet i hii ⟨hx, hlj hxl⟩
    obtain ⟨L, -, hL, hsub, hdz, hau, hbu, hpc, -⟩ :=
      exists_plane_lens (hl i hii) (hab i hii) hclosed hlz
    refine ⟨Function.update D i L, ?_, ?_⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · simp only [Function.update_self]
        exact ⟨hL, hsub, fun x hx => hdz ⟨hx.1, Or.inl hx.2⟩, hau, hbu, hpc⟩
      · rw [Function.update_of_ne (hne j hj').symm]
        exact hD j hj'
    · have hcr : ∀ j ∈ I, L ∩ D j ⊆ {a i, b i} ∩ {a j, b j} := by
        intro j hj x hx
        have hend : x ∈ ({a i, b i} : Set _) :=
          hdz ⟨hx.1, Or.inr (mem_iUnion₂.mpr ⟨j, hj, hx.2⟩)⟩
        refine ⟨hend, (hD j hj).2.2.1 ⟨hx.2, ?_⟩⟩
        refine hcross i hii j (Finset.mem_insert_of_mem hj) (hne j hj) ?_
        rcases hend with rfl | rfl
        · exact (hl i hii).left_mem
        · exact (hl i hii).right_mem
      intro j hj k hk hjk
      rcases Finset.mem_insert.mp hj with rfl | hj' <;>
        rcases Finset.mem_insert.mp hk with rfl | hk'
      · exact (hjk rfl).elim
      · rw [Function.update_self, Function.update_of_ne hjk.symm]
        exact hcr k hk'
      · rw [Function.update_of_ne hjk, Function.update_self, inter_comm, inter_comm {a j, b j}]
        exact hcr j hj'
      · rw [Function.update_of_ne (hne j hj').symm, Function.update_of_ne (hne k hk').symm]
        exact hp j hj' k hk' hjk

end GraphMinor.GM09
