/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ShortTrace
public import LeanPool.GraphMinor.GM12.Section2Theorem
import LeanPool.GraphMinor.GM12.Section2TangleTraceExistence

/-!
# A short normal curve cannot enclose two separated prescribed discs

Claim (1) in the proof of XII (3.2), page 246, takes a trace of the
short normal curve. Each prescribed region meets a selected inside
bounded by a circle in that curve's image. XII (2.1) makes both regions
meet the trace inside. This trace has length twice the curve length,
so the radial metric is below the prescribed separation threshold.
The two disc indices must therefore agree.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14

/-- Claim (1) in the proof of Graph Minors XII (3.2), page 246.
Selected insides of circles in one short normal curve cannot include
two prescribed discs whose regions are sufficiently separated. -/
theorem short_curve_enclosing_discs_indices_eq
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ η : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    (hη : η ≤ θ) (Δ r : ι → Set S) (hr : ∀ i, r i ∈ Γ.R)
    (hrΔ : ∀ i, (r i ∩ Δ i).Nonempty)
    (hsep : ∀ i j, i ≠ j → η ≤ tangleMetric Γ K ins θ (r i) (r j))
    {φ : C(Circle, S)} (hφ : IsNormalCurve Γ φ) (hlen : curveLength Γ φ < η)
    {F₁ F₂ D₁ D₂ : Set S} (hF₁ : IsOArc F₁) (hF₂ : IsOArc F₂)
    (hF₁φ : F₁ ⊆ range φ) (hF₂φ : F₂ ⊆ range φ)
    (hD₁ : IsClosedDisc D₁) (hD₂ : IsClosedDisc D₂)
    (hbd₁ : subBd D₁ = F₁) (hbd₂ : subBd D₂ = F₂)
    (hm₁ : ((PaintingOrDrawing.drawing Γ).inter D₁,
      (PaintingOrDrawing.drawing Γ).interOutside D₁) ∈ T)
    (hm₂ : ((PaintingOrDrawing.drawing Γ).inter D₂,
      (PaintingOrDrawing.drawing Γ).interOutside D₂) ∈ T)
    {i j : ι} (hi : Δ i ⊆ D₁) (hj : Δ j ⊆ D₂) : i = j := by
  have hlenθ : curveLength Γ φ < θ := hlen.trans_le hη
  obtain ⟨u, W, hW⟩ := exists_trace_of_curveLength_lt_tangle_order hS hT hK hφ hlenθ
  have hiD : (r i ∩ D₁).Nonempty := (hrΔ i).mono (inter_subset_inter_right (r i) hi)
  have hjD : (r j ∩ D₂).Nonempty := (hrΔ j).mono (inter_subset_inter_right (r j) hj)
  have hiW := (theorem_2_1_proof hS hT hrespect hK hd W hW hlenθ hF₁ hF₁φ hD₁ hbd₁ hm₁
    (Or.inr (hr i)) hiD).2
  have hjW := (theorem_2_1_proof hS hT hrespect hK hd W hW hlenθ hF₂ hF₂φ hD₂ hbd₂ hm₂
    (Or.inr (hr j)) hjD).2
  exact short_trace_meeting_separated_regions hS hK hd hη r hr hsep hW hlen hiW hjW

end GraphMinor.GM12
