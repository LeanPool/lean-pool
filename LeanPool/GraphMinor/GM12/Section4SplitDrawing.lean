/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RegionWalk
import LeanPool.GraphMinor.GM11.SplitEdge
import LeanPool.GraphMinor.GM12.Section4ParallelAugment

/-!
# Removing loops by subdividing the target edges

For the replacement at the start of XII (4.3), page 249,
subdivide each edge once. The new midpoint differs from both
original ends, so neither half is a loop. A vertex incident with
an original edge stays incident with one half, and every new
midpoint is incident with both halves. Thus subdivision introduces
no isolated vertex.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The left half-edge of a subdivision has the original left end
and its new midpoint as ends. -/
theorem splitData_isLink_left
    {S : Type*} [TopologicalSpace S] {Γ H : Drawing S}
    {A B : Set S → Set S} {m x y : Set S → S}
    (hd : SplitData Γ H A B m x y) {e : Set S} (he : e ∈ Γ.E) :
    H.toGraph.IsLink (A e) (x e) (m e) :=
  ⟨hd.A_mem e he, hd.V_sub (hd.x_mem e he), hd.mid_V₂ he, hd.cap_A e he⟩

/-- The right half-edge of a subdivision has its new midpoint and
the original right end as ends. -/
theorem splitData_isLink_right
    {S : Type*} [TopologicalSpace S] {Γ H : Drawing S}
    {A B : Set S → Set S} {m x y : Set S → S}
    (hd : SplitData Γ H A B m x y) {e : Set S} (he : e ∈ Γ.E) :
    H.toGraph.IsLink (B e) (m e) (y e) :=
  ⟨hd.B_mem e he, hd.mid_V₂ he, hd.V_sub (hd.y_mem e he), hd.cap_B e he⟩

/-- Subdividing every edge removes loops and preserves the absence
of isolated vertices, as used in XII (4.3), page 249. -/
theorem splitData_loopless_and_no_isolated
    {S : Type*} [TopologicalSpace S] {Γ H : Drawing S}
    {A B : Set S → Set S} {m x y : Set S → S}
    (hd : SplitData Γ H A B m x y)
    (hincident : ∀ z ∈ Γ.V, ∃ e, Γ.toGraph.Inc e z) :
    (∀ e z, ¬ H.toGraph.IsLink e z z) ∧
      ∀ z ∈ H.V, ∃ e, H.toGraph.Inc e z := by
  constructor
  · intro e z hloop
    obtain ⟨u, v, huv, hcap⟩ := hd.noLoop e hloop.edge_mem
    have hpair : ({u, v} : Set S) = {z} := hcap.symm.trans (by simpa using hloop.2.2.2)
    have hu : u = z := Set.mem_singleton_iff.mp (hpair.subset (by simp))
    have hv : v = z := Set.mem_singleton_iff.mp (hpair.subset (by simp))
    exact huv (hu.trans hv.symm)
  · intro z hz
    rw [hd.V_eq] at hz
    rcases hz with hz | ⟨e, he, rfl⟩
    · obtain ⟨e, hez⟩ := hincident z hz
      have he : e ∈ Γ.E := hez.edge_mem
      have hlink : Γ.toGraph.IsLink e (x e) (y e) :=
        ⟨he, hd.x_mem e he, hd.y_mem e he, hd.cap e he⟩
      rcases hez.eq_or_eq_of_isLink hlink with hz | hz
      · exact ⟨A e, hz ▸ (splitData_isLink_left hd he).inc_left⟩
      · exact ⟨B e, hz ▸ (splitData_isLink_right hd he).inc_right⟩
    · exact ⟨A e, (splitData_isLink_left hd he).inc_right⟩

/-- A drawing without isolated vertices has a loopless subdivision
without isolated vertices, used before adding parallel copies in
XII (4.3), page 249. -/
theorem exists_loopless_split_without_isolated
    {S : Type*} [TopologicalSpace S] [T2Space S] [Nonempty S]
    (Γ : Drawing S) (hincident : ∀ z ∈ Γ.V, ∃ e, Γ.toGraph.Inc e z) :
    ∃ (H : Drawing S) (A B : Set S → Set S) (m x y : Set S → S),
      SplitData Γ H A B m x y ∧ (∀ e z, ¬ H.toGraph.IsLink e z z) ∧
        ∀ z ∈ H.V, ∃ e, H.toGraph.Inc e z := by
  obtain ⟨H, A, B, m, x, y, hU, hV, hprops, hall⟩ := exists_split Γ
  have hd : SplitData Γ H A B m x y := by
    refine ⟨hU, hV, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hall⟩
    all_goals
      intro e he
      obtain ⟨hA, hB, hm, hmA, hmB, hdisj, hunion, hx, hy, hcap, hcapA, hcapB⟩ := hprops e he
      assumption
  exact ⟨H, A, B, m, x, y, hd, splitData_loopless_and_no_isolated hd hincident⟩

/-- Subdivision followed by parallel copies gives the loopless
minimum-degree-two drawing used in XII (4.3), page 249, when the
original drawing has no isolated vertices. The subdivision data
records how to recover the original edges. -/
theorem exists_subdivision_in_minimum_degree_two_drawing
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S)
    (hincident : ∀ z ∈ Γ.V, ∃ e, Γ.toGraph.Inc e z) :
    ∃ (K H : Drawing S) (A B : Set S → Set S) (m x y : Set S → S),
      SplitData Γ K A B m x y ∧ K.IsSubdrawing H ∧ H.V = K.V ∧
        (∀ e z, ¬ H.toGraph.IsLink e z z) ∧
        ∀ z ∈ H.V, ∃ e f, e ≠ f ∧ H.toGraph.Inc e z ∧ H.toGraph.Inc f z := by
  obtain ⟨K, A, B, m, x, y, hd, hloop, hinc⟩ := exists_loopless_split_without_isolated Γ hincident
  obtain ⟨H, hKH, hHV, hHloop, hHinc⟩ := exists_minimum_degree_two_augmentation hS K hloop hinc
  exact ⟨K, H, A, B, m, x, y, hd, hKH, hHV, hHloop, hHinc⟩

end GraphMinor.GM12
