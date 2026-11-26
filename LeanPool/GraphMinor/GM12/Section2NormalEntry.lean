/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2EntryExistence
import LeanPool.GraphMinor.GM12.Section2SectorCover
import LeanPool.GraphMinor.GM12.Section2TerminalSectors

/-!
# An entering edge for a normal approach at a vertex of degree at least two

For the omitted entry lemma on XII page 243, a normal approach stays in
one sector near its endpoint. Normalize the approach in reverse, use
the closed sector cover and connectedness to choose the sector, then
apply the entry-edge existence theorem for that sector.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The entry edge exists at a vertex with at least two half-edges.
This proves that case of the omitted assertion in XII's trace definition,
page 243, directly from a normal approach and radial maximality. -/
theorem exists_entersLike_of_two_halfEdges {S : Type*} [TopologicalSpace S]
    [T2Space S] [ConnectedSpace S] (hS : IsClosedSurface S)
    {Γ K : Drawing S} (hrad : PreRad (.drawing Γ) K)
    (hmax : RadMax (.drawing Γ) K) (hE : Γ.E.Nonempty)
    {γ : Set S → unitInterval → S} (hγ : EdgePar Γ γ)
    {v : S} (hv : v ∈ Γ.V) (h2 : 2 ≤ Nat.card (halfEdges Γ γ v))
    {r : Set S} (hr : r ∈ Γ.R) {w : S} (hw : w ∈ r) (hwV : w ∈ K.V)
    {f : ℝ → S} (hf : Continuous f) {a c : ℝ} (hac : a < c) (hfc : f c = v)
    (hinside : ∀ t ∈ Ioo a c, f t ∈ r) :
    ∃ e ∈ K.E, EntersLike f a c e r v w := by
  obtain ⟨next, ρ, P, W, Q, τ, hsec, hcover⟩ :=
    exists_sectors_with_cover hS Γ hγ hv h2
  obtain ⟨k, h, hh, hlocal⟩ := exists_terminal_sector_of_approach hsec hcover hf hac hfc
    (fun t ht => region_subset hr (hinside t ht))
  have hρr : ρ k = r := region_eq_of_mem (hsec.corners.region k) hr
    (hlocal h ⟨le_rfl, hh.2⟩).1 (hinside h hh)
  have hwρ : w ∈ ρ k := hρr.symm ▸ hw
  obtain ⟨e, he, hentry⟩ := exists_entersLike_of_sector hS hrad hmax hE hv hsec hcover k hwρ hwV
    hh hf.continuousOn hfc hlocal
  exact ⟨e, he, hρr ▸ hentry⟩

end GraphMinor.GM12
