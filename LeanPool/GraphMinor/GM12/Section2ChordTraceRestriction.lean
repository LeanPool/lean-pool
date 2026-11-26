/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2LocalImageRestriction
import LeanPool.GraphMinor.GM12.Section2PeriodicHits
import LeanPool.GraphMinor.GM11.Section4
import LeanPool.GraphMinor.GM11.Walks

/-!
# The smaller trace after adding a region chord

In Case 2 of XII (2.1), page 244, each smaller circle lies in the
original circle together with a closed region chord. The chord misses
the drawing vertices. Hence every entry and exit of its trace is
already recorded in the original trace. A positive-length walk has
no isolated support vertex, so edge containment also gives vertex
containment. This proves the subdrawing inclusion needed after the
inductive hypothesis.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

private theorem support_subset_of_edges_subset
    {α β : Type*} {G : Graph α β} {u v x y : α}
    (W : GraphWalk G u v) (P : GraphWalk G x y) (hpos : 0 < P.length)
    (hE : ∀ e ∈ P.edges, e ∈ W.edges) : ∀ z ∈ P.support, z ∈ W.support := by
  cases hPcase : P with
  | nil hx =>
    rw [hPcase] at hpos
    simp only [GraphWalk.length_nil, lt_self_iff_false] at hpos
  | @cons _ _ _ e₀ hl rest =>
    rw [hPcase] at hE hpos
    have he := hE e₀ (by simp only [GraphWalk.edges, List.mem_cons]; exact Or.inl trivial)
    intro z hz
    simp only [GraphWalk.support, List.mem_cons] at hz
    rcases hz with rfl | hz
    · exact W.left_mem_support_of_mem_edges he hl
    · cases hrestcase : rest with
      | nil hy =>
        rw [hrestcase] at hz
        have hzy : z = y := by simpa only [GraphWalk.support, List.mem_singleton] using hz
        subst z
        exact W.left_mem_support_of_mem_edges he hl.symm
      | cons hl' tail =>
        rw [hrestcase] at hz hE
        exact support_subset_of_edges_subset W (GraphWalk.cons hl' tail)
          (by simp only [GraphWalk.length_cons]; omega)
          (fun e he => hE e (by
            simp only [GraphWalk.edges, List.mem_cons] at he ⊢
            exact Or.inr he)) z hz
termination_by P.length
decreasing_by
  simp_all only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

private theorem traceSteps_edges_subset_off_closed_set
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {φ : C(Circle, S)} {u : S} (W : GraphWalk K.toGraph u u) (hW : IsTrace Γ K φ W)
    {L : Set S} (hL : IsClosed L) (hLV : Disjoint L Γ.V)
    {g : ℝ → S} (hg : Continuous g) (himage : ∀ t, g t ∈ range φ ∪ L)
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
      have hfirst := trace_mem_edges_of_leaving_off_closed_set hS hK hE W hW hL hLV hv hr
        ⟨hwr, hwK⟩ hlink.1 hg hac hga hgr (fun t _ => himage t) hleave
      have hsecond := trace_mem_edges_of_entry_off_closed_set hS hK hE W hW hL hLV hx hr
        ⟨hwr, hwK⟩ hlink'.1 hg hac hgc hgr (fun t _ => himage t) henter
      have hrest := traceSteps_edges_subset_off_closed_set hS hK hE W hW hL hLV hg himage tail htail
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

/-- A positive-length trace of a curve in the original image together
with a closed chord avoiding drawing vertices is a subdrawing of
the original trace, as required in XII (2.1), Case 2, page 244. -/
theorem trace_isSubdrawing_of_range_subset_union
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {φ ψ : C(Circle, S)} {u v : S}
    (W : GraphWalk K.toGraph u u) (P : GraphWalk K.toGraph v v)
    (hW : IsTrace Γ K φ W) (hP : IsTrace Γ K ψ P) (hpos : 0 < P.length)
    {L : Set S} (hL : IsClosed L) (hLV : Disjoint L Γ.V)
    (hsub : range ψ ⊆ range φ ∪ L) :
    (walkDrawing K P).IsSubdrawing (walkDrawing K W) := by
  have hmem : ∀ e ∈ P.edges, e ∈ W.edges := by
    rcases hP.2 with ⟨_, hlen, _⟩ | ⟨_, _, a, hsteps⟩
    · exact (not_lt_of_ge hlen.le hpos).elim
    · exact traceSteps_edges_subset_off_closed_set hS hK hE W hW hL hLV
        (periodicCurve_continuous ψ)
        (fun t => hsub (mem_range_self (Circle.exp (2 * Real.pi * t)))) P hsteps
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [walkDrawing_V] at hz ⊢
    exact support_subset_of_edges_subset W P hpos hmem z hz
  · intro e he
    rw [walkDrawing_E] at he ⊢
    exact hmem e he

end GraphMinor.GM12
