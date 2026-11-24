/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46SeamPartsDefs
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section2
import LeanPool.GraphMinor.GM07.Section46Constants
import LeanPool.GraphMinor.GM07.Section46SeamRefinement
import LeanPool.GraphMinor.GM07.Section46SeamParts
import LeanPool.GraphMinor.GM07.Section46BoundaryEdges
import LeanPool.GraphMinor.GM07.Section46LCoverage
import LeanPool.GraphMinor.GM07.Section46SeamEdgeCounts
import LeanPool.GraphMinor.GM07.Section46LContactBounds
import LeanPool.GraphMinor.GM07.Section46DrawingContactCount

/-!
# Constructing and counting the seam parts

This assembles `W(e)`, `J⁺`, `K`, and `L` of VII (4.6), pages 225–226.
The closed retained edges cover `U(L)`. Each has at most `w + 2μ + 1`
contacts with `V(G)`, and there are at most `6(2a+b+c-1)` such edges
by (2.4). Their sum is exactly the bound `v - 2k` used on page 226.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

/-- The construction and vertex-contact bound for `L` in VII (4.6),
pages 225–226, with actual seam-part drawings. -/
theorem exists_seam_parts_with_L_bound {S : Type*} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {G J : Drawing S} (hG : G.IsProper)
    (hmin : N.IsMinimalFor G) (hJ : N.IsSeamGraphFor J)
    {a b c k : ℕ} (hc : 2 ≤ c) (hmodel : Nonempty (S ≃ₜ SurfaceModel a b c))
    (hcuffs : 2 ≤ (cuffs S).ncard) (hbd : (G.V ∩ bd S).ncard ≤ 2 * k)
    (hiii : ∀ C ∈ cuffs S, 2 ≤ (G.V ∩ C).ncard)
    {γ : Set S → unitInterval → S} (hγ : EdgePar J γ) :
    ∃ (s t : longSeamEdges G J (muModel a b c k) (wMaxModel a b c k) → unitInterval)
      (W : longSeamEdges G J (muModel a b c k) (wMaxModel a b c k) → Set S)
      (J' K L : Drawing S),
      (∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
        W e = {γ e.1 (s e), γ e.1 (t e)} ∧ (W e).ncard = 2 ∧ W e ⊆ e.1 ∩ G.V ∧
        (γ e.1 '' Iic (s e) ∩ G.V).ncard = muModel a b c k + 1 ∧
        (γ e.1 '' Ici (t e) ∩ G.V).ncard = muModel a b c k + 1 ∧
        wMaxModel a b c k ≤ (γ e.1 '' Ioo (s e) (t e) ∩ G.V).ncard) ∧
      J'.U = J.U ∧ J'.V = J.V ∪ ⋃ e, W e ∧
      K.IsSubdrawing J' ∧ K.V = ⋃ e, W e ∧
      K.E = centralEdges G J (muModel a b c k) (wMaxModel a b c k) γ s t ∧
      L.IsSubdrawing J' ∧ L.V = J'.V ∧
      L.E = forestSeamEdges J' (centralEdges G J (muModel a b c k) (wMaxModel a b c k) γ s t) ∧
      L.IsProper ∧ HasNoIsolatedVertices L ∧ (G.V ∩ L.U).ncard ≤ vModel a b c k - 2 * k := by
  have : T2Space S := hS.2.1
  have hk := two_le_k_of_boundary_4_6 hcuffs hbd hiii
  have hkμ : 2 * k ≤ muModel a b c k := by
    unfold muModel
    exact Nat.le_add_left _ _
  have hμ : 0 < muModel a b c k := by omega
  have hsmall : (G.V ∩ bd S).ncard < 2 * muModel a b c k + wMaxModel a b c k + 2 := by omega
  obtain ⟨s, t, W, J', hfull, _, _, hU, hV, _⟩ := exists_J_plus_with_split_edges G J hγ hμ
  have hcuts : ∀ e, s e ∈ Ioo 0 1 ∧ t e ∈ Ioo 0 1 ∧ s e < t e ∧
      W e = {γ e.1 (s e), γ e.1 (t e)} := by
    intro e
    exact ⟨(hfull e).1, (hfull e).2.1, (hfull e).2.2.1, (hfull e).2.2.2.1⟩
  obtain ⟨K, L, hK, hKV, hKE, hL, hLV, hLE⟩ := exists_K_and_L hγ s t W hcuts hU hV
  have hp := isProper_L hS N hJ hU hV hLE
  have hn := hasNoIsolatedVertices_L hS N hJ hγ s t W hcuts hsmall hU hV hLV hLE
  have hleft : ∀ e, (γ e.1 '' Iic (s e) ∩ G.V).ncard = muModel a b c k + 1 := by
    intro e
    obtain ⟨_, _, _, _, _, _, hl, _, _⟩ := hfull e
    exact hl
  have hright : ∀ e, (γ e.1 '' Ici (t e) ∩ G.V).ncard = muModel a b c k + 1 := by
    intro e
    obtain ⟨_, _, _, _, _, _, _, hr, _⟩ := hfull e
    exact hr
  have hper := L_edge_contact_bound hγ s t W hcuts hleft hright hU hV hLE
  have hcontacts := ncard_vertex_contacts_U_le_edges_mul G L hn hper
  have hLEcard := L_edge_ncard_le_two_mul_old_edges hγ s t W hcuts hU hV hLE
  have hJEcard := (theorem_2_4_proof hS (by omega) hmodel hG hmin hJ).2
  have hLsize : L.E.ncard ≤ 6 * (2 * a + b + c - 1) := by omega
  have hbound : (G.V ∩ L.U).ncard ≤ vModel a b c k - 2 * k := by
    unfold vModel
    rw [Nat.add_sub_cancel]
    exact hcontacts.trans (Nat.mul_le_mul_right _ hLsize)
  exact ⟨s, t, W, J', K, L, hfull, hU, hV, hK, hKV, hKE, hL, hLV, hLE, hp, hn, hbound⟩

end GraphMinor.GM07
