/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Cited
import LeanPool.GraphMinor.GM12.Section3AddNormalCircle
import LeanPool.GraphMinor.GM12.Section3OutsideDiscRegions
import LeanPool.GraphMinor.GM12.Section3ThetaSphere
import LeanPool.GraphMinor.GM11.Section6

import LeanPool.GraphMinor.GM07.Section7
import LeanPool.GraphMinor.GM07.Bridge

/-!
# A normal essential circle outside one disc

For the one-cuff minimum-existence step used by XII (3.1), page 245,
add the deleted disc's normal boundary to the drawing. Its complement
is the closure of a union of regions. This complement is not planar:
on a surface other than the sphere, a containing disc would also
contain the deleted disc, and hence fill the whole closed surface.
The normal-circle criterion VII (5.5), page 231, therefore supplies a
normal circle in the complement which is not null-homotopic.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

universe u

/-- On a closed surface other than the sphere, the complement of one
disc contains a normal non-null-homotopic circle whenever its boundary
is normal. This uses cited VII (5.5) over its original drawing. -/
theorem exists_normal_nonnull_oArc_outside_disc
    {S : Type u} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) (hns : ¬ IsSphere S) (Γ : Drawing S)
    {D : Set S} (hD : IsClosedDisc D) (hnD : Γ.IsNormal (discBd D)) :
    ∃ F : Set S, IsOArc F ∧ Γ.IsNormal F ∧ F ⊆ closure Dᶜ ∧ ¬ IsNullHomotopicOArc F := by
  classical
  obtain ⟨G, hGU, hnorm⟩ := exists_drawing_add_normal_oArc Γ hD.isOArc_discBd hnD
  have hclosed : IsClosed D := hD.isCompact.isClosed
  have hbd : frontier D ⊆ G.U := by
    rw [IsClosedDisc.frontier_eq_discBd hS hD, hGU]
    exact subset_union_right
  let R := {r ∈ G.R | Disjoint r D}
  have hZ : closure Dᶜ = closure (⋃₀ R) :=
    closure_compl_eq_closure_outside_regions hS G hclosed hbd
  have hproper : closure Dᶜ ≠ univ := by
    intro heq
    obtain ⟨x, hx⟩ := hD.nonempty_discInt
    have hxZ : x ∈ closure Dᶜ := heq.symm ▸ mem_univ x
    have hxfr : x ∈ frontier D := by
      rw [frontier_eq_closure_inter_closure]
      exact ⟨subset_closure hx.1, hxZ⟩
    exact hx.2 (IsClosedDisc.frontier_eq_discBd hS hD ▸ hxfr)
  have hnotplanar : ¬ IsPlanar (closure Dᶜ) := by
    rintro ⟨E, hE, hZE⟩
    have hbdE : discBd D ⊆ E := by
      intro x hx
      have hxfr : x ∈ frontier D := (IsClosedDisc.frontier_eq_discBd hS hD).symm ▸ hx
      rw [frontier_eq_closure_inter_closure] at hxfr
      exact hZE hxfr.2
    have hDE := disc_subset_of_boundary_subset_disc_of_not_sphere hS hns hD hE hbdE
    apply closed_disc_ne_univ hS hE
    apply Set.eq_univ_of_univ_subset
    intro x _
    by_cases hx : x ∈ D
    · exact hDE hx
    · exact hZE (subset_closure hx)
  have hGproper : G.IsProper := by
    rintro x ⟨hx, _⟩
    exact (hx (hS.2.2 x)).elim
  have hcriterion := GraphMinor.GM07.gm07_theorem_5_5 S ⟨hS.1, hS.2.1, fun x =>
    (hS.2.2 x).isManifoldPoint⟩
    inferInstance G hGproper R (fun _ hr => hr.1) (hZ ▸ hproper)
  have hnall : ¬ ∀ F : Set S, G.IsNormal F → IsOArc F →
      F ⊆ closure Dᶜ → IsNullHomotopicOArc F := by
    intro hall
    apply hnotplanar
    rw [hZ]
    exact hcriterion.mpr (fun F hn hF hFZ => hall F hn hF (hZ.symm ▸ hFZ))
  push Not at hnall
  obtain ⟨F, hnF, hF, hFZ, hnull⟩ := hnall
  exact ⟨F, hF, hnorm F hnF, hFZ, hnull⟩

end GraphMinor.GM12
