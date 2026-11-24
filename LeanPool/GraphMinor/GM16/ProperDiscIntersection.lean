/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM15.Section7
public import LeanPool.GraphMinor.GM16.ProperArrangement
import LeanPool.GraphMinor.GM09.Basic
public import LeanPool.GraphMinor.GM16.ProperDiscTransport
import LeanPool.GraphMinor.GM09.Section4b
import LeanPool.GraphMinor.GM10.Section12
import LeanPool.GraphMinor.GM11.OArcCircuit
import LeanPool.GraphMinor.GM11.Section81
import LeanPool.GraphMinor.GM14.Section7b
import LeanPool.GraphMinor.Surface.CircleMove

/-!
# An arrangement disc outside a normal disc

Claim (1) of XV (7.7), pages 139–140, uses the following disc intersection fact. A society disc that
is not contained in a normal disc meets it only at boundary vertices. Connectedness of the disc
interior proves the assertion.
-/

public section
namespace GraphMinor.GM16
open Set Function Topology
open Graph SimpleGraph Hypergraph Surface GM06 GM09 GM10 GM11 GM14 GM15
universe u v w
variable {α : Type u} {β : Type v}

theorem inter_disc_subset_subBd_of_not_subset
    {S : Type w} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S) {α : Type u} {β : Type v}
    {S₀ : Set (Society α β)} {α₀_disc : Society α β → Set S} {α₀_pt : α → S}
    (hArr : IsSurfaceArrangement S₀ α₀_disc α₀_pt)
    {Δ : Set S} (hΔ : IsClosedDisc Δ)
    (hNorm : IsArrangementNormal S₀ α₀_disc α₀_pt (subBd Δ))
    {A : Society α β} (hA : A ∈ S₀) (hnot_sub : ¬ α₀_disc A ⊆ Δ) :
    α₀_disc A ∩ Δ ⊆ subBd Δ ∧ α₀_disc A ∩ Δ ⊆ α₀_pt '' A.Ω.bar := by
  let D := α₀_disc A
  obtain ⟨hD, hD_bd⟩ := hArr.isClosedDisc A hA
  have hfr_D : frontier D = subBd D := (GM11.subBd_eq_frontier D).symm
  have hfr_Δ : frontier Δ = subBd Δ := (GM11.subBd_eq_frontier Δ).symm
  have hdis_fr : Disjoint (D \ frontier D) (frontier Δ) := by
    rw [hfr_D, hfr_Δ, Set.disjoint_left]
    rintro x ⟨hxD, hx_not_bd⟩ hx_bdΔ
    obtain ⟨v, hv, rfl⟩ := hNorm A hA ⟨hx_bdΔ, hxD⟩
    exact hx_not_bd (hD_bd v hv)
  have hdis_Δ : Disjoint (D \ frontier D) Δ := by
    refine (GM14.subset_or_disjoint_of_frontier hΔ.isClosed
      (GM14.IsClosedDisc.isPreconnected_diff_frontier hS hD) hdis_fr).resolve_left ?_
    intro hsub
    exact hnot_sub ((GM14.IsClosedDisc.subset_closure_diff_frontier hS hD).trans
      (hΔ.isClosed.closure_subset_iff.mpr hsub))
  have hD_compl : D ⊆ closure Δᶜ :=
    (GM14.IsClosedDisc.subset_closure_diff_frontier hS hD).trans
      (closure_mono (Set.disjoint_left.mp hdis_Δ))
  have hsub_bd : D ∩ Δ ⊆ subBd Δ := by
    rintro x ⟨hxD, hxΔ⟩
    rw [← hfr_Δ, frontier_eq_closure_inter_closure]
    exact ⟨subset_closure hxΔ, hD_compl hxD⟩
  refine ⟨hsub_bd, fun x hx => hNorm A hA ⟨hsub_bd hx, hx.1⟩⟩


end GraphMinor.GM16
