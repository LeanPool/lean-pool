/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46LongEdges
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46W
import LeanPool.GraphMinor.GM07.Section46JPlus
import LeanPool.GraphMinor.GM07.Section46SplitEdges

/-!
# The refined seam graph of VII (4.6)

This assembles the construction on page 225. Choose `W(e)` on every
long edge, add their union `W` to the vertices, and identify all edges
of `J⁺`. Short edges stay unchanged. Each long edge supplies two linking
edges and one central edge, with the contact counts used on page 226.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

/-- The construction of `W(e)`, `W`, and `J⁺`, with all its edges and
contact counts, in VII (4.6), page 225. -/
theorem exists_J_plus_with_split_edges {S : Type*} [TopologicalSpace S] [T2Space S]
    (G J : Drawing S) {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (hμ : 0 < μ) :
    ∃ (s t : longSeamEdges G J μ w → unitInterval)
      (W : longSeamEdges G J μ w → Set S) (J' : Drawing S),
      (∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
        W e = {γ e.1 (s e), γ e.1 (t e)} ∧ (W e).ncard = 2 ∧ W e ⊆ e.1 ∩ G.V ∧
        (γ e.1 '' Iic (s e) ∩ G.V).ncard = μ + 1 ∧
        (γ e.1 '' Ici (t e) ∩ G.V).ncard = μ + 1 ∧
        w ≤ (γ e.1 '' Ioo (s e) (t e) ∩ G.V).ncard) ∧
      (⋃ e, W e).Finite ∧ (⋃ e, W e) ⊆ G.V \ J.V ∧
      J'.U = J.U ∧ J'.V = J.V ∪ ⋃ e, W e ∧
      J'.E = shortSeamEdges G J μ w ∪ ⋃ e : longSeamEdges G J μ w,
        {γ e.1 '' Ioo 0 (s e), γ e.1 '' Ioo (s e) (t e), γ e.1 '' Ioo (t e) 1} := by
  obtain ⟨s, t, W, hcuts, hfin, hsub⟩ := exists_W_for_long_edges (G := G) hγ hμ
  have hWU : (⋃ e, W e) ⊆ J.U := by
    intro x hx
    obtain ⟨e, hxe⟩ := mem_iUnion.mp hx
    exact J.closure_subset_U e.2.1 (subset_closure ((hcuts e).2.2.2.2.2.1 hxe).1)
  obtain ⟨J', hU, hV⟩ := exists_J_plus J hfin hWU
  refine ⟨s, t, W, J', hcuts, hfin, hsub, hU, hV, ?_⟩
  exact J_plus_edges hγ s t W
    (fun e => ⟨(hcuts e).1, (hcuts e).2.1, (hcuts e).2.2.1, (hcuts e).2.2.2.1⟩) hU hV

end GraphMinor.GM07
