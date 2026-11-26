/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2EntryImageRestriction
public import LeanPool.GraphMinor.GM12.Section2TraceVertexRestriction
import LeanPool.GraphMinor.GM12.Section2TraceExistence
import LeanPool.GraphMinor.GM12.Section2PeriodicHits
import LeanPool.GraphMinor.GM11.Section4

/-!
# Trace drawings shrink when curve images shrink

For the restriction step of XII (2.1), pages 243--244, every edge
of the smaller trace is an entry or an exit along a region visit.
The image-entry restriction theorem puts it in the original trace.
The already proved vertex containment supplies the other part of
subdrawing containment. Trace existence then gives the desired
trace of a smaller normal curve. The result here assumes that the
original drawing has an edge.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

private theorem traceSteps_edges_subset_of_image
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {φ : C(Circle, S)} {u : S} (W : GraphWalk K.toGraph u u) (hW : IsTrace Γ K φ W)
    {g : ℝ → S} (hg : Continuous g) (himage : ∀ t, g t ∈ range φ)
    {a b : ℝ} {v z : S} (P : GraphWalk K.toGraph v z) (hP : TraceSteps Γ K g a b P) :
    ∀ e ∈ P.edges, e ∈ W.edges := by
  cases hPcase : P with
  | nil hv => simp only [GraphWalk.edges, List.not_mem_nil, false_implies, implies_true]
  | cons hlink rest =>
    rw [hPcase] at hP
    cases hrestcase : rest with
    | nil hv => rw [hrestcase] at hP; exact hP.elim
    | cons hlink' tail =>
      rw [hrestcase] at hP
      obtain ⟨c, hac, hga, hv, hgc, hwK, r, hr, hwr, hgr, hleave, henter, htail⟩ := hP
      have hx := (traceSteps_parameters tail htail).2.2.1
      have hfirst := trace_mem_edges_of_leaving_in_image hS hK hE W hW hv hr
        ⟨hwr, hwK⟩ hlink.1 hg hac hga hgr (fun t _ => himage t) hleave
      have hsecond := trace_mem_edges_of_entry_in_image hS hK hE W hW hx hr
        ⟨hwr, hwK⟩ hlink'.1 hg hac hgc hgr (fun t _ => himage t) henter
      have hrest := traceSteps_edges_subset_of_image hS hK hE W hW hg himage tail htail
      intro e he
      simp only [GraphWalk.edges, List.mem_cons] at he
      rcases he with rfl | rfl | he
      · exact hfirst
      · exact hsecond
      · exact hrest e he
termination_by P.length
decreasing_by
  simp_all only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

/-- The edge part of trace restriction in XII (2.1), pages 243--244,
for drawings with an edge. The smaller curve need not be injective. -/
theorem trace_edges_subset_of_range_subset
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {φ ψ : C(Circle, S)} {u v : S}
    (W : GraphWalk K.toGraph u u) (P : GraphWalk K.toGraph v v)
    (hW : IsTrace Γ K φ W) (hP : IsTrace Γ K ψ P) (hsub : range ψ ⊆ range φ) :
    (walkDrawing K P).E ⊆ (walkDrawing K W).E := by
  rcases hP.2 with ⟨_, hlen, _⟩ | ⟨_, _, a, hsteps⟩
  · intro e he
    rw [walkDrawing_E, (support_of_length_zero hlen).2] at he
    exact (List.not_mem_nil he).elim
  · have hmem := traceSteps_edges_subset_of_image hS hK hE W hW
      (periodicCurve_continuous ψ)
      (fun t => hsub (mem_range_self (Circle.exp (2 * Real.pi * t)))) P hsteps
    intro e he
    rw [walkDrawing_E] at he ⊢
    exact hmem e he

/-- Both vertices and edges of a trace of a smaller curve image
belong to the original trace drawing, as used in XII (2.1). -/
theorem trace_isSubdrawing_of_range_subset
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {φ ψ : C(Circle, S)} {u v : S}
    (W : GraphWalk K.toGraph u u) (P : GraphWalk K.toGraph v v)
    (hW : IsTrace Γ K φ W) (hP : IsTrace Γ K ψ P) (hsub : range ψ ⊆ range φ) :
    (walkDrawing K P).IsSubdrawing (walkDrawing K W) :=
  ⟨trace_vertices_subset_of_range_subset hK W P hW hP hsub,
    trace_edges_subset_of_range_subset hS hK hE W P hW hP hsub⟩

/-- Existence and containment of the trace under image restriction,
for the nonempty-edge case of the restriction step in XII (2.1). -/
theorem exists_trace_subdrawing_of_range_subset
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {φ ψ : C(Circle, S)} {u : S} (W : GraphWalk K.toGraph u u)
    (hW : IsTrace Γ K φ W) (hψ : IsNormalCurve Γ ψ) (hsub : range ψ ⊆ range φ) :
    ∃ (v : S) (P : GraphWalk K.toGraph v v), IsTrace Γ K ψ P ∧
      (walkDrawing K P).IsSubdrawing (walkDrawing K W) := by
  obtain ⟨v, P, hP⟩ := exists_trace hS hK hE hψ
  exact ⟨v, P, hP, trace_isSubdrawing_of_range_subset hS hK hE W P hW hP hsub⟩

end GraphMinor.GM12
