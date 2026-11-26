/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TraceParameters
public import LeanPool.GraphMinor.GM12.Section2EntryUnique
import LeanPool.GraphMinor.GM11.RadialRegions

/-!
# A trace is determined by its parameter interval

For XII's trace definition on page 243, the next vertex visit is fixed
by normality. Its intervening region determines the radial hub, and
entry and exit uniqueness determine the two edges. Removing that pair
and repeating proves equality of the vertex and edge lists of traces
on the same interval.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

universe u

/-- On a fixed real parameter interval, two sequences of trace steps
have the same edge and vertex lists. Entry-edge uniqueness uses the
proved XI (7.2), so no statement hypothesis remains. -/
theorem traceSteps_walk_lists_unique
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {f : ℝ → S} (hf : Continuous f) {a b : ℝ} {u v : S}
    (W W' : GraphWalk K.toGraph u v)
    (hW : TraceSteps Γ K f a b W) (hW' : TraceSteps Γ K f a b W') :
    W.edges = W'.edges ∧ W.support = W'.support := by
  cases hWcase : W with
  | nil hv =>
    rw [hWcase] at hW
    have hab : a = b := hW.1
    cases hW'case : W' with
    | nil hv' => exact ⟨rfl, rfl⟩
    | cons hl' rest' =>
      rw [hW'case] at hW'
      cases hrest'case : rest' with
      | nil hv' => rw [hrest'case] at hW'; exact hW'.elim
      | cons hl₂' rest' =>
        rw [hrest'case] at hW'
        obtain ⟨c', hac', _, _, _, _, r', hr', _, _, _, _, ht'⟩ := hW'
        have hcb := (traceSteps_parameters rest' ht').1
        exact (not_lt_of_ge (hab ▸ hcb) hac').elim
  | @cons _ w _ e hl rest =>
    rw [hWcase] at hW
    cases hrestcase : rest with
    | nil hv => rw [hrestcase] at hW; exact hW.elim
    | @cons _ x _ e₂ hl₂ rest =>
      rw [hrestcase] at hW
      obtain ⟨c, hac, hfa, hu, hfc, hwK, r, hr, hwr, hfr, hleave, henter, ht⟩ := hW
      obtain ⟨hcb, _, hx, _, _⟩ := traceSteps_parameters rest ht
      cases hW'case : W' with
      | nil hv' =>
        rw [hW'case] at hW'
        have hab : a = b := hW'.1
        exact (not_lt_of_ge (hab ▸ hcb) hac).elim
      | @cons _ w' _ e' hl' rest' =>
        rw [hW'case] at hW'
        cases hrest'case : rest' with
        | nil hv' => rw [hrest'case] at hW'; exact hW'.elim
        | @cons _ x' _ e₂' hl₂' rest' =>
          rw [hrest'case] at hW'
          obtain ⟨c', hac', hfa', hu', hfc', hwK', r', hr', hwr', hfr', hleave', henter', ht'⟩
            := hW'
          have hx' := (traceSteps_parameters rest' ht').2.2.1
          have hcc : c = c' := next_vertex_parameter_unique hac hac'
            (hfc.symm ▸ hx) (hfc'.symm ▸ hx') hr hr' hfr hfr'
          subst c'
          have hxx : x = x' := hfc.symm.trans hfc'
          cases hxx
          have hmid : (a + c) / 2 ∈ Ioo a c := ⟨by linarith, by linarith⟩
          have hrr : r = r' := region_eq_of_mem hr hr' (hfr _ hmid) (hfr' _ hmid)
          subst r'
          have hrad : PreRad (.drawing Γ) K := ⟨hK.1, hK.2.1⟩
          have hww : w' = w := hub_unique hrad hr hwr hwK hwr' hwK'
          subst w'
          have heq := leavesLike_edge_unique hS hConn hK hr hu ⟨hwr, hwK⟩
            hl.1 hl'.1 hl.2.2.2 hl'.2.2.2 hf hfa hfr hleave hleave'
          have heq₂ := entersLike_edge_unique hS hConn hK hr hx ⟨hwr, hwK⟩
            hl₂.1 hl₂'.1 (hl₂.2.2.2.trans (pair_comm _ _))
            (hl₂'.2.2.2.trans (pair_comm _ _)) hf hfc hfr henter henter'
          obtain ⟨hedges, hvertices⟩ := traceSteps_walk_lists_unique hS hConn hK hf rest _ ht ht'
          simp only [GraphWalk.edges, GraphWalk.support, heq, heq₂, hedges, hvertices, and_self]
termination_by W.length
decreasing_by
  rw [hWcase, hrestcase]
  simp only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

/-- Trace steps on the same parameter interval give the same underlying
subdrawing. This is the drawing form of trace determinacy used when
comparing restrictions of curves. -/
theorem traceSteps_drawing_unique
    {S : Type u} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {Γ K : Drawing S} (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {f : ℝ → S} (hf : Continuous f) {a b : ℝ} {u v : S}
    (W W' : GraphWalk K.toGraph u v)
    (hW : TraceSteps Γ K f a b W) (hW' : TraceSteps Γ K f a b W') :
    walkDrawing K W = walkDrawing K W' := by
  obtain ⟨he, hv⟩ := traceSteps_walk_lists_unique hS hConn hK hf W W' hW hW'
  apply Drawing.ext_of_V_E
  · rw [walkDrawing_V, walkDrawing_V, hv]
  · rw [walkDrawing_E, walkDrawing_E, he]

end GraphMinor.GM12
