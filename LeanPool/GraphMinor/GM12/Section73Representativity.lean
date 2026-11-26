/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73ShortWalkNull
import LeanPool.GraphMinor.GM12.Section73TracePath
import LeanPool.GraphMinor.GM12.Section73TraceHubCount
import LeanPool.GraphMinor.GM12.Section73PeriodNull
import LeanPool.GraphMinor.GM12.Section73MinimalCircle
import LeanPool.GraphMinor.GM12.Section2TraceExistence
import LeanPool.GraphMinor.GM12.Section2CurveCounts
import LeanPool.GraphMinor.GM11.FlatCover
import LeanPool.GraphMinor.GM11.Section64

/-!
# Representativity after contracting a radial star

For XII (7.3), page 261, a short non-null normal circle can be
chosen to meet every region in a connected set. Its radial trace
visits the merged hub at most once. Lifting it therefore adds at
most two edges. The old slope contracts this short lifted walk,
and composing with the collapse contracts the original circle.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- The constructed radial star contraction preserves representativity
with order decreased by one, as used in XII (7.3), page 261. -/
theorem isRepresentative_of_radial_star_contraction
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K J : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {v : S} (hv : v ∈ Γ.V) {r' : Set S}
    (hr' : r' ∈ (deleteVertices Γ {v}).R) (hvr' : v ∈ r')
    (f : C(S, S)) (hfix : ∀ x ∉ r', f x = x)
    (hcollapse : ∀ x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e, f x = v)
    (hfibre : ∀ x y, f x = f y ↔ x = y ∨
      (x ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e) ∧
      (y ∈ {v} ∪ ⋃ e ∈ {e ∈ K.E | v ∈ closure e}, closure e))
    (hJV : J.V = f '' K.V)
    (hJE : J.E ⊆ (fun g => f '' g) '' {g ∈ K.E | v ∉ closure g})
    (hJpre : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsPreRadialDrawing J)
    {θ : ℕ} {ins : Drawing S → Set S} (hs : IsSlope K (2 * θ) ins)
    (hJ : (PaintingOrDrawing.drawing (deleteVertices Γ {v})).IsRadialDrawing J)
    (hE' : (deleteVertices Γ {v}).E.Nonempty)
    : (deleteVertices Γ {v}).IsRepresentative (θ - 1) := by
  refine ⟨inferInstance, ?_⟩
  intro F hF hn hcard
  by_contra hnon
  obtain ⟨G, hG, hGn, hGnon, hcount, hconn⟩ :=
    exists_minimal_nonNull_normal_circle hS hF hn hnon
  obtain ⟨φ, hφ, hrange, hφn, hlen⟩ := exists_normal_curve_of_oArc hG hGn
  obtain ⟨u, W, hW⟩ := exists_trace hS hJ hE' hφn
  rcases hW.2 with ⟨_, _, _, r, hr, hφr, _⟩ | ⟨_, hWlen, a, hsteps⟩
  · have hGr : G ⊆ r := hrange ▸ hφr
    obtain ⟨D, _, hD, hbd⟩ := exists_disc_in_openDisc (hJ.1.2 r hr) hG hGr
    exact hGnon (isNullHomotopicOArcIn_of_subset_disc hG (subset_univ _) hD
      (hbd ▸ Surface.discBd_subset D))
  · have hvcount : walkVertexCount v W ≤ 1 :=
      traceSteps_hub_count_le_one hφ hr' (hrange.symm ▸ hconn r' hr') hvr'
        (l := a) le_rfl le_rfl W hsteps
    have hlength : W.length + 2 * walkVertexCount v W < 2 * θ := by
      rw [hWlen, hlen, inter_comm]
      omega
    have hloop : ∀ e x y, J.toGraph.IsLink e x y → x ≠ y := by
      intro e x y hel heq
      subst y
      have hb := bipartite_of_preRadial hJpre e x x hel
      by_cases hx : x ∈ (deleteVertices Γ {v}).V
      · exact (hb.mp hx) hx
      · exact hx (hb.mpr hx)
    obtain ⟨q, hq⟩ := exists_edge_paths hloop
    have hq' : ∀ e x y (h : J.toGraph.IsLink e x y), range (q e x y h) ⊆ closure e :=
      fun e x y h => (hq e x y h).subset
    have hwNull := walkPath_null_of_vertex_deletion_lift hS hK hE hv hr' hvr'
      f hfix hcollapse hfibre hJV hJE hJpre hs q hq' W hlength
    obtain ⟨ha, hb, hpath⟩ := traceSteps_path_homotopic ⟨hJ.1, hJpre⟩
      (periodicCurve_continuous φ) q hq' W hsteps
    have hnull := closedCurve_null_of_period_path φ a ha hb (hpath.trans hwNull)
    have hnullRange : IsNullHomotopicOArc (range φ) := ⟨hφ.toHomeomorph, hnull⟩
    exact hGnon (hrange ▸ hnullRange)

end GraphMinor.GM12
