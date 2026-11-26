/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.RegionWalk
import LeanPool.GraphMinor.GM12.Section4PendantAugment
import LeanPool.GraphMinor.GM12.Section4SplitDrawing
import LeanPool.GraphMinor.GM11.Walks

/-!
# Completing the geometric target replacement

For XII (4.3), page 249, first give every isolated vertex a
pendant edge. There are only finitely many original vertices.
New vertices are already incident with their pendant edges, and
subdrawing inclusion preserves every existing incidence. Then
subdivide all edges and add parallel copies, obtaining a loopless
drawing with at least two incident edges at every vertex.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

private theorem inc_of_subdrawing
    {S : Type*} [TopologicalSpace S] {Γ H : Drawing S} (h : Γ.IsSubdrawing H)
    {e : Set S} {v : S} (he : Γ.toGraph.Inc e v) : H.toGraph.Inc e v := by
  obtain ⟨w, hl⟩ := he
  exact ⟨w, (h.isLink_iff hl.edge_mem).mp hl⟩

private theorem augment_vertices
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S)
    (Γ : Drawing S) {V : Set S} (hV : V.Finite) (hsub : V ⊆ Γ.V) :
    ∃ H : Drawing S, Γ.IsSubdrawing H ∧
      (∀ v ∈ V, ∃ e, H.toGraph.Inc e v) ∧
      ∀ v ∈ H.V, v ∈ Γ.V ∨ ∃ e, H.toGraph.Inc e v := by
  classical
  revert hsub
  induction V, hV using Set.Finite.induction_on with
  | empty =>
    intro _
    exact ⟨Γ, Drawing.IsSubdrawing.refl Γ, by simp, fun v hv => Or.inl hv⟩
  | @insert v V hv hV ih =>
    intro hsub
    obtain ⟨K, hΓK, hdone, hnew⟩ := ih (fun x hx => hsub (Or.inr hx))
    have hvK : v ∈ K.V := hΓK.1 (hsub (Or.inl rfl))
    by_cases hvinc : ∃ e, K.toGraph.Inc e v
    · refine ⟨K, hΓK, ?_, hnew⟩
      intro x hx
      rcases hx with hx | hx
      · exact hx ▸ hvinc
      · exact hdone x hx
    · obtain ⟨H, w, e, hKH, hHV, _, hl⟩ := exists_pendant_augmentation hS K hvK
        (fun e he => hvinc ⟨e, he⟩)
      refine ⟨H, hΓK.trans hKH, ?_, ?_⟩
      · intro x hx
        rcases hx with hx | hx
        · exact hx ▸ ⟨e, hl.inc_left⟩
        · obtain ⟨f, hf⟩ := hdone x hx
          exact ⟨f, inc_of_subdrawing hKH hf⟩
      · intro x hx
        rw [hHV] at hx
        rcases hx with hx | hx
        · exact Or.inr (hx ▸ ⟨e, hl.inc_right⟩)
        · rcases hnew x hx with hxΓ | ⟨f, hf⟩
          · exact Or.inl hxΓ
          · exact Or.inr ⟨f, inc_of_subdrawing hKH hf⟩

/-- The isolated-vertex augmentation in XII (4.3), page 249.
Every original vertex remains, and every resulting vertex is incident
with an edge. -/
theorem exists_augmentation_without_isolated_vertices
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (Γ : Drawing S) :
    ∃ H : Drawing S, Γ.IsSubdrawing H ∧ ∀ v ∈ H.V, ∃ e, H.toGraph.Inc e v := by
  obtain ⟨H, hΓH, hdone, hnew⟩ := augment_vertices hS Γ Γ.finite_V subset_rfl
  refine ⟨H, hΓH, ?_⟩
  intro v hv
  rcases hnew v hv with hvΓ | hinc
  · exact hdone v hvΓ
  · exact hinc

/-- The geometric construction of the loopless minimum-degree-two
replacement in XII (4.3), page 249. Pendant augmentation retains
the original as a subdrawing, subdivision records both halves of each
edge, and the final augmentation retains that subdivision. -/
theorem exists_loopless_minimum_degree_two_replacement
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (Γ : Drawing S) :
    ∃ (Γ₀ K H : Drawing S) (A B : Set S → Set S) (m x y : Set S → S),
      Γ.IsSubdrawing Γ₀ ∧ SplitData Γ₀ K A B m x y ∧ K.IsSubdrawing H ∧
        (∀ e z, ¬ H.toGraph.IsLink e z z) ∧
        ∀ z ∈ H.V, ∃ e f, e ≠ f ∧ H.toGraph.Inc e z ∧ H.toGraph.Inc f z := by
  obtain ⟨Γ₀, hΓ₀, hinc⟩ := exists_augmentation_without_isolated_vertices hS Γ
  obtain ⟨K, H, A, B, m, x, y, hd, hKH, _, hloop, htwo⟩ :=
    exists_subdivision_in_minimum_degree_two_drawing hS Γ₀ hinc
  exact ⟨Γ₀, K, H, A, B, m, x, y, hΓ₀, hd, hKH, hloop, htwo⟩

end GraphMinor.GM12
