/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2Case2Trace
import LeanPool.GraphMinor.GM12.Section2WalkInside

/-!
# The inductive conclusion in Case 2 of XII (2.1)

Apply the inductive hypothesis to the smaller circle and trace
constructed by the theta-disc argument. Its selected inside still
meets the chosen atom. Its trace drawing is contained in the original
trace drawing, so monotonicity of walk insides gives the conclusion
for the original curve. This is the last step of Case 2 on page 244.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Case 2 of XII (2.1), page 244, from the inductive assertion for
all strictly smaller positive lengths. -/
theorem theorem_2_1_case2
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K) (hE : Γ.E.Nonempty)
    {θ : ℕ} {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : IsPretangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    {φ : C(Circle, S)} (hφi : Function.Injective φ) (hF : IsOArc (range φ))
    {u : S} (W : GraphWalk K.toGraph u u) (hW : IsTrace Γ K φ W)
    (hcount : curveLength Γ φ < θ)
    {r Δ C : Set S} (hr : r ∈ Γ.R) (hdisconn : ¬ IsPreconnected (range φ ∩ r))
    (hΔ : IsClosedDisc Δ) (hbd : subBd Δ = range φ)
    (hm : ((PaintingOrDrawing.drawing Γ).inter Δ,
      (PaintingOrDrawing.drawing Γ).interOutside Δ) ∈ T)
    (hC : (C ∩ Δ).Nonempty)
    {ins : Drawing S → Set S}
    (hInd : ∀ (ψ : C(Circle, S)), IsEmbedding ψ →
      0 < curveLength Γ ψ → curveLength Γ ψ < curveLength Γ φ →
      ∀ (v : S) (P : GraphWalk K.toGraph v v), IsTrace Γ K ψ P →
      ∀ D : Set S, IsClosedDisc D → subBd D = range ψ →
      ((PaintingOrDrawing.drawing Γ).inter D,
        (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T →
      (C ∩ D).Nonempty → (C ∩ insWalk ins K P).Nonempty) :
    (C ∩ insWalk ins K W).Nonempty := by
  obtain ⟨ψ, D, v, P, hψemb, hP, hψpos, hsmall, hD, hbdD, hmD, hCD, hsub⟩ :=
    theorem_2_1_case2_smaller_trace hS hK hE hT hrespect hφi hF W hW hcount
      hr hdisconn hΔ hbd hm hC
  exact meets_insWalk_of_subdrawing ins K W P hsub
    (hInd ψ hψemb hψpos hsmall v P hP D hD hbdD hmD hCD)

end GraphMinor.GM12
