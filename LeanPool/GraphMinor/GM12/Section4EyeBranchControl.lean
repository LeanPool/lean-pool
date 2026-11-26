/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.GM15.Defs
public import LeanPool.GraphMinor.GM12.Section4EndPartition
import LeanPool.GraphMinor.GM12.Section4SpanControl
import LeanPool.GraphMinor.GM12.Section4ExternalPathBranches
import LeanPool.GraphMinor.GM12.Section4SpanBranchBound
import LeanPool.GraphMinor.GM12.Section4EyeRegionDistance

/-!
# Controlling the branches joined through the eyes

XII (4.5), page 253, joins the connected endpoint classes by
the external paths, retaining one edge of each path. Every
class has endpoints incident with two distinct eye regions.
Their region distance gives distant vertices in the connected
class, and (4.1) bounds any separation containing the enlarged
branch. Thus the retained edges and enlarged branches form a
controlled minor.
-/

public section

namespace GraphMinor.GM12

open Set Surface Hypergraph GM14 GM15

/-- The branch construction and separation estimate at the end
of XII (4.5), page 253, for a connected endpoint partition and
its disjoint external paths. -/
theorem controlsMinor_of_eye_connections
    {S α β W E : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    [Fintype W] [Finite E] (hS : IsClosedSurface S)
    {G : Graph α β} {Γ : Drawing S} (η : SpanEmbedding Γ G)
    {θstar θ t : ℕ}
    {Tstar : Set (Hypergraph α β × Hypergraph α β)}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hm : HasTangleMetric Γ θ T d)
    (hCtrl : IsControllingTangle G Γ η θstar θ Tstar T) (hEΓ : Γ.E.Nonempty)
    (L : Graph W E) (κ : E × Bool → W) (σ : Fin t × Bool ≃ E)
    (hlink : ∀ e, L.IsLink e (κ (e, false)) (κ (e, true)))
    (hκne : ∀ e, κ (e, false) ≠ κ (e, true))
    (htwo : ∀ w, ∃ i j, i ≠ j ∧ ∃ b c d e : Bool,
      κ (σ (i, b), c) = w ∧ κ (σ (j, d), e) = w)
    (r : Fin t → Set S) (hr : ∀ i, r i ∈ Γ.R)
    (hfar : ∀ i j, i ≠ j → 2 * Fintype.card W + 2 ≤ d (r i) (r j))
    (hθ : Fintype.card W ≤ θ)
    (ends : E × Bool → S) (hends : ∀ q, ends q ∈ Γ.V)
    (hinc : ∀ i b c, ends (σ (i, b), c) ∈ closure (r i))
    (H : W → Drawing S) (hH : ∀ w, (H w).IsSubdrawing Γ)
    (hHc : ∀ w, IsConnectedDrawing (H w))
    (hHH : Pairwise (fun v w => Disjoint (H v).V (H w).V))
    (hclass : ∀ w, (H w).V ∩ range ends = edgeEndClass ends κ w)
    (P : E → Graph α β)
    (hP : ∀ e, IsHPathWithEnds G η.imageGraph (P e)
      (η.vMap (ends (e, false))) (η.vMap (ends (e, true))))
    (hPP : Pairwise (fun e f => Disjoint (P e).vertexSet (P f).vertexSet)) :
    ControlsMinor (Hypergraph.ofGraph G hCtrl.isTangle_star.finite_V
      hCtrl.isTangle_star.finite_E) θstar Tstar L := by
  let _ := Fintype.ofFinite E
  have hpoint : ∀ q, ends q ∈ (H (κ q)).V := by
    intro q
    have hx : ends q ∈ edgeEndClass ends κ (κ q) := ⟨q, rfl, rfl⟩
    exact ((hclass (κ q)).symm.subset hx).1
  have hHne : ∀ w, (H w).V.Nonempty := by
    intro w
    obtain ⟨i, j, hij, b, c, d, e, hi, hj⟩ := htwo w
    exact ⟨ends (σ (i, b), c), hi ▸ hpoint _⟩
  have hTG := hCtrl.isTangle_star
  obtain ⟨A, hA, hAA, hAV⟩ := exists_embedded_connecting_branches hTG.finite_V hTG.finite_E
    η H hH hHne hHc (fun v w hvw => hHH hvw)
  have hAF : ∀ w, (A w).vertexSet ⊆ η.imageGraph.vertexSet := by
    intro w x hx
    obtain ⟨y, hy, rfl⟩ := (hAV w).subset hx
    exact η.bijOn_v.mapsTo ((hH w).1 hy)
  have heA : ∀ q, η.vMap (ends q) ∈ (A (κ q)).vertexSet := by
    intro q
    rw [hAV]
    exact mem_image_of_mem η.vMap (hpoint q)
  obtain ⟨C, b, hC, hCC, hAC, hbinj, hjoin⟩ := exists_branches_from_external_paths
    hTG.finite_V hTG.finite_E A hA hAA hAF P
    (fun e => η.vMap (ends (e, false))) (fun e => η.vMap (ends (e, true)))
    (fun e => κ (e, false)) (fun e => κ (e, true)) hP
    (fun e f hef => hPP hef) (fun e => heA (e, false)) (fun e => heA (e, true))
  have hcard : L.vertexSet.ncard ≤ Fintype.card W := by
    simpa only [Nat.card_eq_fintype_card] using ncard_le_card L.vertexSet
  refine ⟨C, b, fun w _ => hC w, fun v _ w _ hvw => hCC v w hvw, ?_, ?_,
    fun e _ f _ hef heq => hef (hbinj heq), hcard.trans (hθ.trans hCtrl.theta_le), ?_⟩
  · intro e u v hl huv
    obtain ⟨heG, x, hx, y, hy, hxy⟩ := hjoin e
    rcases (hlink e).eq_and_eq_or_eq_and_eq hl with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · rw [hu] at hx
      rw [hv] at hy
      exact ⟨heG, ⟨x, hx, hxy.inc_left⟩, y, hy, hxy.inc_right⟩
    · rw [hv] at hx
      rw [hu] at hy
      exact ⟨heG, ⟨y, hy, hxy.inc_right⟩, x, hx, hxy.inc_left⟩
  · intro e w hl
    have h := (hlink e).eq_and_eq_or_eq_and_eq hl
    rcases h with ⟨h0, h1⟩ | ⟨h0, h1⟩ <;>
      exact False.elim (hκne e (h0.trans h1.symm))
  · intro A' B' hAB hord w hw
    obtain ⟨i, j, hij, c, e, f, g, hi, hj⟩ := htwo w
    have hiH : ends (σ (i, c), e) ∈ (H w).V := hi ▸ hpoint _
    have hjH : ends (σ (j, f), g) ∈ (H w).V := hj ▸ hpoint _
    have hdist := incident_vertices_distant_of_regions_distant hS hm hEΓ
      (hends (σ (i, c), e)) (hends (σ (j, f), g)) (hr i) (hr j)
      (hinc i c e) (hinc j f g) (hfar i j hij)
    exact not_subset_small_side_of_embedded_distant_drawing hS η hm hCtrl hθ
      (hHc w) (hH w) hiH hjH hdist
      (fun x hx => (hAC w).vertexSet_subset ((hAV w).symm.subset hx)) hAB
      (hord.trans_le hcard)

end GraphMinor.GM12
