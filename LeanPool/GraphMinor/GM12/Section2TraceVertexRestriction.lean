/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2TraceImage
import LeanPool.GraphMinor.GM11.RadialRegions
import LeanPool.GraphMinor.GM11.Section4

/-!
# Vertex containment under restriction of the curve image

For the restriction step in XII (2.1), pages 243--244, a trace vertex
is either an original vertex visited by the curve, or the radial hub
of a region visited by the curve. Both visits remain visits of the
original curve when images are included. The original trace records
them, and uniqueness of each region's hub identifies the middle walk
vertices. Thus every vertex of the restricted trace is already in
the original trace. No injectivity of the restricted curve is needed.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

private theorem traceSteps_support_property
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {f : ℝ → S} {P : S → Prop}
    {a b : ℝ} {u v : S} (W : GraphWalk K.toGraph u v) (hW : TraceSteps Γ K f a b W)
    (hV : ∀ s ∈ Icc a b, f s ∈ Γ.V → P (f s))
    (hR : ∀ r ∈ Γ.R, ∀ w ∈ K.V, w ∈ r → (∃ s ∈ Ioo a b, f s ∈ r) → P w) :
    ∀ x ∈ W.support, P x := by
  cases hWcase : W with
  | nil hv =>
    rw [hWcase] at hW
    obtain ⟨hab, hfa, hu⟩ := hW
    intro x hx
    have hxu : x = u := by simpa only [GraphWalk.support, List.mem_singleton] using hx
    subst x
    exact hfa ▸ hV a ⟨le_rfl, hab.le⟩ (hfa.symm ▸ hu)
  | @cons _ w _ e hlink rest =>
    rw [hWcase] at hW
    cases hrestcase : rest with
    | nil hv => rw [hrestcase] at hW; exact hW.elim
    | cons hlink' tail =>
      rw [hrestcase] at hW
      obtain ⟨c, hac, hfa, hu, _, hwK, r, hr, hwr, hfr, _, _, htail⟩ := hW
      have hcb : c ≤ b := (traceSteps_parameters tail htail).1
      have hPu : P u := hfa ▸ hV a ⟨le_rfl, hac.le.trans hcb⟩ (hfa.symm ▸ hu)
      have hmid : (a + c) / 2 ∈ Ioo a c := ⟨by linarith, by linarith⟩
      have hPw : P w := hR r hr w hwK hwr
        ⟨(a + c) / 2, ⟨hmid.1, hmid.2.trans_le hcb⟩, hfr _ hmid⟩
      have htailP := traceSteps_support_property tail htail
        (fun s hs hsV => hV s ⟨hac.le.trans hs.1, hs.2⟩ hsV)
        (fun r hr w hw hwr hs => hR r hr w hw hwr (by
          obtain ⟨s, hs, hfs⟩ := hs
          exact ⟨s, ⟨hac.trans hs.1, hs.2⟩, hfs⟩))
      intro x hx
      simp only [GraphWalk.support, List.mem_cons] at hx
      rcases hx with rfl | rfl | hx
      · exact hPu
      · exact hPw
      · exact htailP x hx
termination_by W.length
decreasing_by
  simp_all only [GraphWalk.length, GraphWalk.edges, List.length_cons]
  omega

/-- The vertex part of trace restriction in XII (2.1), pages 243--244.
For any two traced normal curves with included images, the second
trace's vertex set is included in the first trace's vertex set. -/
theorem trace_vertices_subset_of_range_subset
    {S : Type*} [TopologicalSpace S] [T1Space S] {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {φ ψ : C(Circle, S)} {u v : S}
    (W : GraphWalk K.toGraph u u) (W' : GraphWalk K.toGraph v v)
    (hW : IsTrace Γ K φ W) (hW' : IsTrace Γ K ψ W') (hsub : range ψ ⊆ range φ) :
    (walkDrawing K W').V ⊆ (walkDrawing K W).V := by
  have hrad : PreRad (.drawing Γ) K := ⟨hK.1, hK.2.1⟩
  have hhub : ∀ r ∈ Γ.R, ∀ w ∈ K.V, w ∈ r → (range ψ ∩ r).Nonempty →
      w ∈ (walkDrawing K W).V := by
    intro r hr w hwK hwr hmeet
    have hmeet' : (range φ ∩ r).Nonempty := hmeet.mono (inter_subset_inter_left r hsub)
    obtain ⟨z, hzW, hzr⟩ := trace_region_in_image W hW hr hmeet'
    have hzdraw : z ∈ (walkDrawing K W).V := by rw [walkDrawing_V]; exact hzW
    have hzK : z ∈ K.V := (walkDrawing_isSubdrawing K W).1 hzdraw
    have hwz : w = z := hub_unique hrad hr hzr hzK hwr hwK
    exact hwz.symm ▸ hzdraw
  rcases hW'.2 with ⟨_, hlen, hvK, r, hr, hψr, hvr⟩ | ⟨_, _, a, hsteps⟩
  · have hvdraw : v ∈ (walkDrawing K W).V := hhub r hr v hvK hvr
      ⟨ψ 1, mem_range_self 1, hψr (mem_range_self 1)⟩
    intro x hx
    rw [walkDrawing_V, (support_of_length_zero hlen).1] at hx
    have hxv : x = v := by simpa only [List.mem_singleton, mem_ofPred_eq] using hx
    exact hxv.symm ▸ hvdraw
  · have hP := traceSteps_support_property (P := fun x => x ∈ (walkDrawing K W).V) W' hsteps
      (fun s _ hsV => by
        rw [walkDrawing_V]
        exact trace_vertex_in_image W hW
          (hsub (mem_range_self (Circle.exp (2 * Real.pi * s)))) hsV)
      (fun r hr w hw hwr hs => by
        obtain ⟨s, _, hsr⟩ := hs
        exact hhub r hr w hw hwr ⟨periodicCurve ψ s,
          mem_range_self (Circle.exp (2 * Real.pi * s)), hsr⟩)
    intro x hx
    rw [walkDrawing_V] at hx
    exact hP x hx

end GraphMinor.GM12
