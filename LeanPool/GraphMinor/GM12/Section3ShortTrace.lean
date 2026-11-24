/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2
public import LeanPool.GraphMinor.GM12.Section4WalkMetric

/-!
# A short trace cannot meet two separated regions

Claim (1) in the proof of XII (3.2), page 246, applies (2.1) to make
the two prescribed regions meet the inside of one trace. The trace
then witnesses distance less than the separation threshold. This file
proves that metric step. The atom-transfer assertion of (2.1) is not
assumed or asserted here: the two intersections are explicit inputs.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14 Hypergraph

/-- A trace has twice the length of its original curve, including
in the zero-length case of the definition on XII, page 243. -/
theorem trace_length_eq_two_mul_curveLength
    {S : Type*} [TopologicalSpace S] {Γ K : Drawing S} {φ : C(Circle, S)}
    {u : S} {W : GraphWalk K.toGraph u u} (hW : IsTrace Γ K φ W) :
    W.length = 2 * curveLength Γ φ := by
  rcases hW.2 with h | h
  · rw [h.1, mul_zero, h.2.1]
  · exact h.2.1

/-- The metric step of claim (1) in XII (3.2), page 246. Once (2.1)
has made two prescribed regions meet the trace inside, their prescribed
separation forces their indices to agree. -/
theorem short_trace_meeting_separated_regions
    {S ι : Type*} [TopologicalSpace S] [T1Space S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ η : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {ins : Drawing S → Set S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hd : IsDerivedSlope (PaintingOrDrawing.drawing Γ) K θ T ins)
    (hη : η ≤ θ) (r : ι → Set S) (hr : ∀ i, r i ∈ Γ.R)
    (hsep : ∀ i j, i ≠ j → η ≤ tangleMetric Γ K ins θ (r i) (r j))
    {φ : C(Circle, S)} {u : S} {W : GraphWalk K.toGraph u u}
    (hW : IsTrace Γ K φ W) (hlen : curveLength Γ φ < η)
    {i j : ι} (hi : (r i ∩ insWalk ins K W).Nonempty)
    (hj : (r j ∩ insWalk ins K W).Nonempty) : i = j := by
  obtain ⟨v, ⟨hvr, hvK⟩, _⟩ := hK.2.1.2.2.1 (r i) (hr i)
  obtain ⟨w, ⟨hwr, hwK⟩, _⟩ := hK.2.1.2.2.1 (r j) (hr j)
  have hc : ∀ k x, x ∈ K.V → x ∈ r k → IsCorrespondingAtom Γ K (r k) {x} := by
    intro k x hxK hxr
    exact ⟨Or.inr (hr k), Or.inl (Or.inl ⟨x, hxK, rfl⟩),
      Or.inr (Or.inr ⟨hr k, x, ⟨hxK, hxr⟩, rfl⟩)⟩
  have hl : W.length < 2 * θ := theorem_2_1_length hW (hlen.trans_le hη)
  have hiW := (corresponding_atom_subset_iff hS hK hd (hc i v hvK hvr) W hl).mpr hi
  have hjW := (corresponding_atom_subset_iff hS hK hd (hc j w hwK hwr) W hl).mpr hj
  have hdW := tangleMetric_le_of_walk (hc i v hvK hvr) (hc j w hwK hwr)
    W hl (trace_length_eq_two_mul_curveLength hW) hiW hjW
  by_contra hij
  exact (not_lt_of_ge (hsep i j hij)) (hdW.trans_lt hlen)

end GraphMinor.GM12
