/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73ImageIncidence
public import LeanPool.GraphMinor.GM12.Section73RadialCleanup
import LeanPool.GraphMinor.GM12.Section73ContractedFaces

/-!
# The cleaned contraction of the radial star

For XII (7.3), page 261, contract the reduced radial star and remove
parallel spokes bounding empty discs. The construction gives a
two-cell pre-radial drawing of the drawing after vertex deletion.
It retains the image vertices and uses only surviving old spoke
images as edges. Every region contains at most one surviving edge
of the original drawing. Maximality is a separate verification.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Contracting the reduced radial star and cleaning up empty
bigons gives a two-cell pre-radial drawing after vertex deletion.
This is the contraction and deletion construction of XII (7.3),
page 261, with the global maximality check left separate. -/
theorem exists_cleaned_radial_star_contraction
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V)
    (hunique : ∀ e ∈ K.E, ∀ g ∈ K.E, ∀ u : S,
      K.toGraph.IsLink e v u → K.toGraph.IsLink g v u → e = g)
    {r' : Set S} (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r') :
    ∃ (f : C(S, S)) (H J : Drawing S), Function.Surjective f ∧
      (∀ x ∉ r', f x = x) ∧
      (∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v) ∧
      (∀ x y, f x = f y ↔ x = y ∨
        (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
        (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e)) ∧
      H.U = f '' K.U ∧ H.V = f '' K.V ∧
      H.E = (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g} ∧
      J.IsSubdrawing H ∧ J.V = H.V ∧
      (PaintingOrDrawing.drawing J).IsTwoCell ∧
      (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsPreRadialDrawing J ∧
      (∀ r ∈ J.R, ∀ a ∈ (deleteVertices Γ {v}).E, ∀ b ∈ (deleteVertices Γ {v}).E,
        a ⊆ r → b ⊆ r → a = b) := by
  obtain ⟨f, H, hsurj, hfix, hcollapse, hfibre, hHU, hHV, hHE,
      hHtwo, hcap, hV, hhub, hregion, hlink⟩ :=
    exists_contracted_radial_incidence hS hK hE hv hunique hr' hvr'
  have hface : ∀ r ∈ H.R, ∀ a ∈ (deleteVertices Γ {v}).E,
      ∀ b ∈ (deleteVertices Γ {v}).E, a ⊆ r → b ⊆ r → a = b := by
    intro r hr
    obtain ⟨_, _, _, _, huniq⟩ := contracted_radial_region_edges hS hK hE hv hr' hvr'
      f hsurj hfix hfibre hHU hr
    exact huniq
  obtain ⟨J, hJH, hJV, hJtwo, hJpre, hJface⟩ :=
    exists_preRadial_subdrawing_by_cleanup hS hHtwo hcap hV hhub hregion hlink hface
  exact ⟨f, H, J, hsurj, hfix, hcollapse, hfibre, hHU, hHV, hHE,
    hJH, hJV, hJtwo, hJpre, hJface⟩

end GraphMinor.GM12
