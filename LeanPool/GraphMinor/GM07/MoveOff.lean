/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Slit
public import LeanPool.GraphMinor.GM07.GoodEdge
import LeanPool.GraphMinor.GM12.Section4DiscMatch

/-!
# Moving a forest off a line

For (7.5), page 241: "We may assume that `U(H) ∩ ē = ∅`." The line `ē` lies in a disc off the
boundary. We shrink this disc to a small
disc that misses the forest. The homeomorphism is the identity near the boundary, so the forest is
the same up to homoplasty.
-/

public section

namespace GraphMinor.GM07

open Set Topology Function Metric GraphMinor.Surface GraphMinor.GM11

universe u

/-- A line off the boundary lies inside a disc off the boundary. -/
theorem exists_disc_of_line_aux {M : Type} [TopologicalSpace M] (hM : IsSurface M) {L : Set M} {u v
  : M}
    (hL : IsLineWithEnds L u v) (hd : L ∩ bd M = ∅) : ∃ B, IsClosedDisc B ∧ L ⊆ discInt B
      ∧ B ∩ bd M = ∅ := by
  classical
  have ht2M : T2Space M := hM.2.1
  obtain ⟨K₀, s, _, hs1, hK₀c, hK₀i, _, hK₀bd, _, _, hLine⟩ :=
    exists_line_chart_aux hM hL hd isOpen_univ (subset_univ L)
  let B : Set ℂ := closedBall 0 1
  have hBc : IsCompact B := isCompact_closedBall _ _
  obtain ⟨hD, hDb⟩ := closedBall_disc (zero_lt_one' ℝ)
  obtain ⟨K', hK'c, hK'l⟩ := exists_inv_of_compactOn hBc hK₀c hK₀i
  obtain ⟨hE, hEb⟩ := hD.image hK₀c hK'c hK'l
  rw [hDb] at hEb
  have hzof : ∀ x ∈ L, ∃ z ∈ B, ‖z‖ < 1 ∧ K₀ z = x := fun x hx => by
    obtain ⟨z, hz, him, hre, rfl⟩ := (hLine x).mp hx
    refine ⟨z, hz, ?_, rfl⟩
    have : z = (z.re : ℂ) := Complex.ext (by simp) (by simp [him])
    rw [this, Complex.norm_real, Real.norm_eq_abs]
    simpa using hre.trans_lt hs1
  refine ⟨K₀ '' B, hE, fun x hx => ?_, ?_⟩
  · obtain ⟨z, hz, hnorm, rfl⟩ := hzof x hx
    refine ⟨⟨z, hz, rfl⟩, fun hb => ?_⟩
    rw [hEb] at hb
    obtain ⟨w, hw, he⟩ := hb
    have hwB : w ∈ B := sphere_subset_closedBall hw
    rw [hK₀i hwB hz he, mem_sphere_zero_iff_norm] at hw
    exact hnorm.ne hw
  · rw [eq_empty_iff_forall_notMem]
    rintro x ⟨⟨z, hz, rfl⟩, hb⟩
    exact hK₀bd z hz hb

/-- A line off the boundary lies inside a disc off the boundary. -/
theorem exists_disc_of_line {S : Type u} [TopologicalSpace S] {M : Type} [TopologicalSpace M]
  (hM : IsSurface M) (h : S ≃ₜ M)
    {L : Set S} {u v : S} (hL : IsLineWithEnds L u v) (hd : L ∩ bd S = ∅) : ∃ B, IsClosedDisc B
      ∧ L ⊆ discInt B ∧ B ∩ bd S = ∅ := by
  have ht2 : T2Space M := hM.2.1
  have hbd : h '' bd S = bd M := image_bd_homeomorph h
  have hS2 : T2Space S := h.isEmbedding.t2Space
  have hL' : IsLineWithEnds (h '' L) (h u) (h v) := by
    obtain ⟨f, h0, h1⟩ := hL
    refine ⟨f.trans (h.image L), ?_, ?_⟩
    · change h (f 0).1 = h u
      rw [h0]
    · change h (f 1).1 = h v
      rw [h1]
  obtain ⟨B, hB, hLB, hoff⟩ := exists_disc_of_line_aux hM hL' (by
    rw [← hbd, ← image_inter h.injective, hd, image_empty])
  have hB' := isClosedDisc_image_of_injOn hB h.symm.continuous h.symm.injective.injOn
  have hinv : ∀ x, h.symm (h x) = x := h.symm_apply_apply
  refine ⟨h.symm '' B, hB'.1, fun x hx => ?_, ?_⟩
  · have h1 := hLB (mem_image_of_mem h hx)
    refine ⟨⟨h x, h1.1, hinv x⟩, fun hb => ?_⟩
    rw [hB'.2] at hb
    obtain ⟨y, hy, he⟩ := hb
    have : y = h x := by rw [← he, h.apply_symm_apply]
    exact h1.2 (this ▸ hy)
  · rw [eq_empty_iff_forall_notMem]
    rintro x ⟨⟨y, hy, rfl⟩, hb⟩
    have h2 : y ∈ B ∩ bd M := ⟨hy, by
      rw [← hbd]
      exact ⟨h.symm y, hb, h.apply_symm_apply y⟩⟩
    rw [hoff] at h2
    exact h2

/-- A forest has no loops. -/
theorem IsSurfaceForest.closure_edge_line {S : Type u} [TopologicalSpace S] {H : Drawing S}
  (hH : IsSurfaceForest H) {f : Set S} (hf : f ∈ H.E) :
    ∃ u v, IsLineWithEnds (closure f) u v := by
  classical
  rcases H.edge_cond f hf with ⟨u, v, -, -, hl⟩ | ⟨v, hcap, -⟩
  · exact ⟨u, v, hl⟩
  · exfalso
    have hv : v ∈ H.V := by
      have : v ∈ closure f ∩ H.V := by rw [hcap]; rfl
      exact this.2
    have hlink : H.toGraph.IsLink f v v := ⟨hf, hv, hv, by rw [hcap]; simp⟩
    have := hH.2 v (.cons hlink (.nil hv)) (by simp [GraphWalk.IsSimpleClosed, GraphWalk.support,
      GraphWalk.edges])
    simp [GraphWalk.length, GraphWalk.edges] at this

/-- "We may assume that `U(H) ∩ ē = ∅`." -/
theorem exists_move_off_line {S : Type u} [TopologicalSpace S] (hS : IsSurface S) [ConnectedSpace
  S] {M : Type} [TopologicalSpace M] (hM : IsSurface M)
    (h : S ≃ₜ M) {H : Drawing S} (hH : IsSurfaceForest H) {L : Set S} {u v : S}
      (hL : IsLineWithEnds L u v) (hd : L ∩ bd S = ∅) :
    ∃ β : S ≃ₜ S, (∀ x ∈ bd S, β x = x) ∧ Disjoint (β '' H.U) L := by
  classical
  have ht2 : T2Space S := hS.2.1
  have hman := hS.2.2
  obtain ⟨B, hB, hLB, hoff⟩ := exists_disc_of_line hM h hL hd
  have hBint : ∀ x ∈ B, IsInteriorPoint x := fun x hx => by
    by_contra hn
    have h1 : x ∈ B ∩ bd S := ⟨hx, hn⟩
    rw [hoff] at h1
    exact h1
  -- A larger disc, off the boundary.
  obtain ⟨E, hE, hBE, hEs⟩ := exists_disc_around hman hB (fun x hx => hBint x
    (Surface.discBd_subset _ hx)) (isClosed_bd S).isOpen_compl
    (fun x hx hb => by
      have h1 : x ∈ B ∩ bd S := ⟨Surface.discBd_subset _ hx, hb⟩
      rw [hoff] at h1
      exact h1)
  have hEoff : ∀ x ∈ bd S, x ∉ E := fun x hx hxE => by
    rcases hEs hxE with h1 | h1
    · have h2 : x ∈ B ∩ bd S := ⟨h1, hx⟩
      rw [hoff] at h2
      exact h2
    · exact h1 hx
  -- A point of the inside of `B` off the forest, in a small disc off the forest.
  have hfin : (closure '' H.E).Finite := H.finite_edges.image _
  obtain ⟨p, hp, hpoff⟩ := exists_mem_discInt_off hS hB hfin (by
    rintro _ ⟨f, hf, rfl⟩
    exact hH.closure_edge_line hf)
  have hUclosed : IsClosed (⋃₀ (closure '' H.E)) := hfin.isClosed_sUnion (by
    rintro _ ⟨f, -, rfl⟩
    exact isClosed_closure)
  have hOpen := (hB.isOpen_discInt hman).inter hUclosed.isOpen_compl
  obtain ⟨D₀, hD₀, hpD₀, hD₀s⟩ := exists_disc_in_open (hBint p hp.1) hOpen ⟨hp, hpoff⟩
  obtain ⟨q, hq, hqV⟩ : ∃ q ∈ discBd D₀, q ∉ H.V := by
    by_contra hn
    push Not at hn
    exact (infinite_of_isOArc hD₀.isOArc_discBd) (H.finite_V.subset hn)
  have hqO := hD₀s (Surface.discBd_subset _ hq)
  have hqU : q ∉ H.U := fun hU => by
    rw [H.U_eq] at hU
    rcases hU with hV | hU
    · exact hqV hV
    · obtain ⟨f, hf, hx⟩ := mem_iUnion₂.mp hU
      exact hqO.2 ⟨closure f, ⟨f, hf, rfl⟩, hx⟩
  obtain ⟨A, hA, hqA, hAs⟩ := exists_disc_in_open (hBint q hqO.1.1) ((hB.isOpen_discInt hman).inter
    H.isClosed_U.isOpen_compl) ⟨hqO.1, hqU⟩
  obtain ⟨e, he, hfix⟩ := GraphMinor.GM12.exists_disc_onto_nested hman hA hB hE (fun x hx =>
    (hAs hx).1) hBE
  refine ⟨e, fun x hx => hfix x (hEoff x hx), ?_⟩
  rw [disjoint_left]
  rintro _ ⟨x, hxU, rfl⟩ hxL
  have h1 : e x ∈ B := (hLB hxL).1
  rw [← he] at h1
  obtain ⟨y, hy, hyx⟩ := h1
  rw [e.injective hyx] at hy
  exact (hAs hy).2 hxU

end GraphMinor.GM07
