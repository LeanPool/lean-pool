/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46LongEdges
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46LongCutParameters

/-!
# The sets `W(e)` and `W` in VII (4.6)

Choose the two ordered contacts on each long edge, as on page 225.
Their union is finite and lies in `V(G)` off the old seam vertices.
Thus these are precisely points that can be added when forming `J⁺`.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

universe u

/-- The cut points `W(e)` on all long edges, and their union `W`, in
VII (4.6), page 225. The counts refer to the closed linking intervals
and the open central interval in the edge parameter. -/
theorem exists_W_for_long_edges {S : Type u} [TopologicalSpace S] [T2Space S]
    {G J : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (hμ : 0 < μ) :
    ∃ (s t : longSeamEdges G J μ w → unitInterval)
      (W : longSeamEdges G J μ w → Set S),
      (∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
        W e = {γ e.1 (s e), γ e.1 (t e)} ∧ (W e).ncard = 2 ∧ W e ⊆ e.1 ∩ G.V ∧
        (γ e.1 '' Iic (s e) ∩ G.V).ncard = μ + 1 ∧
        (γ e.1 '' Ici (t e) ∩ G.V).ncard = μ + 1 ∧
        w ≤ (γ e.1 '' Ioo (s e) (t e) ∩ G.V).ncard) ∧
      (⋃ e, W e).Finite ∧ (⋃ e, W e) ⊆ G.V \ J.V := by
  classical
  have hex := fun e : longSeamEdges G J μ w =>
    exists_long_edge_cut_parameters (G := G) hγ e.2.1 hμ e.2.2
  choose s hs t ht hst hsG htG hne hleft hright hmid using hex
  let W : longSeamEdges G J μ w → Set S := fun e => {γ e.1 (s e), γ e.1 (t e)}
  have hsub : (⋃ e, W e) ⊆ G.V \ J.V := by
    intro x hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    have hxG : x ∈ e.1 ∩ G.V := by
      rcases he with rfl | rfl
      · exact hsG e
      · exact htG e
    exact ⟨hxG.2, (e.2.1.2.1 hxG.1).2⟩
  refine ⟨s, t, W, ?_, G.finite_V.subset (hsub.trans sdiff_subset), hsub⟩
  intro e
  refine ⟨hs e, ht e, hst e, rfl, ncard_pair (hne e), ?_, hleft e, hright e, hmid e⟩
  intro x hx
  rcases hx with rfl | rfl
  · exact hsG e
  · exact htG e

end GraphMinor.GM07
