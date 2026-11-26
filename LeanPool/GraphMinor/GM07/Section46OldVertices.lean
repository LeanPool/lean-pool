/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46SeamPartsDefs
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46EdgeSegments

/-!
# Which refined edges meet old seam vertices

Central edges have their closed intervals inside an old open edge,
so their closures miss `V(J)`. Each linking edge has an old seam vertex
as one end. These incidences are used for coverage of `L` and to separate
linking from central edges in VII (4.6), page 226.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

/-- Closed central edges stay inside their old open edges. -/
theorem central_closure_subset_old_edge {S : Type*} [TopologicalSpace S] [T2Space S]
    {J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {e : Set S} (he : e ∈ J.E) {s t : unitInterval}
    (hs : s ∈ Ioo 0 1) (ht : t ∈ Ioo 0 1) (hst : s < t) :
    closure (γ e '' Ioo s t) ⊆ e := by
  rw [closure_image_Ioo_eq_Icc hγ he hst (.inl hs.1)]
  rintro x ⟨u, hu, rfl⟩
  exact (congrArg (fun A => γ e u ∈ A) (hγ.image e he)).mp
    ⟨u, ⟨hs.1.trans_le hu.1, hu.2.trans_lt ht.2⟩, rfl⟩

/-- A closed central edge contains no old seam vertex, in VII (4.6),
page 226. -/
theorem central_closure_disjoint_old_vertices {S : Type*} [TopologicalSpace S] [T2Space S]
    {G J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (s t : longSeamEdges G J μ w → unitInterval)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e)
    {f : Set S} (hf : f ∈ centralEdges G J μ w γ s t) : Disjoint (closure f) J.V := by
  obtain ⟨e, rfl⟩ := hf
  apply disjoint_left.mpr
  intro x hx hxV
  have hxE := central_closure_subset_old_edge hγ e.2.1
    (hcuts e).1 (hcuts e).2.1 (hcuts e).2.2 hx
  exact (e.2.1.2.1 hxE).2 hxV

/-- Each linking edge has an old seam vertex as an end, in VII (4.6),
page 226. -/
theorem linking_closure_meets_old_vertices {S : Type*} [TopologicalSpace S] [T2Space S]
    {G J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (s t : longSeamEdges G J μ w → unitInterval)
    (hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e)
    {f : Set S} (hf : f ∈ linkingEdges G J μ w γ s t) :
    (closure f ∩ J.V).Nonempty := by
  rcases hf with ⟨e, rfl⟩ | ⟨e, rfl⟩
  · have hs := (hcuts e).1
    refine ⟨γ e.1 0, ?_, hγ.zero e.1 e.2.1⟩
    rw [closure_image_Ioo_eq_Icc hγ e.2.1 hs.1 (.inr hs.2)]
    exact ⟨0, ⟨le_rfl, hs.1.le⟩, rfl⟩
  · have ht := (hcuts e).2.1
    refine ⟨γ e.1 1, ?_, hγ.one e.1 e.2.1⟩
    rw [closure_image_Ioo_eq_Icc hγ e.2.1 ht.2 (.inl ht.1)]
    exact ⟨1, ⟨ht.2.le, le_rfl⟩, rfl⟩

end GraphMinor.GM07
