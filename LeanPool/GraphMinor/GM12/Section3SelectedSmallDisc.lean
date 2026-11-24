/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3ShortCurve
public import LeanPool.GraphMinor.GM12.Section3SmallDiscUnique
import LeanPool.GraphMinor.GM12.Section2CurveCounts

/-!
# Selecting the small discs in the proof of XII (3.2)

Claim (1) puts at most one prescribed disc in the selected inside
of a short normal circle. For claim (2), compare any other disc
bounded by that circle and enclosing at most one prescribed disc.
Outside the sphere-with-at-most-two-discs cases the proved disc
uniqueness lemma makes the two discs equal. Thus the other disc is
selected by the tangle as well. These are the first two claims on
page 246.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11 GM14

/-- The selected inside of a short normal circle includes at most
one separated prescribed disc, by claim (1) of XII (3.2), page 246. -/
theorem selected_disc_includes_at_most_one_prescribed_disc
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
    {F D : Set S} (hF : IsOArc F) (hn : Γ.IsNormal F)
    (hlen : (Γ.V ∩ F).ncard < η) (hD : IsClosedDisc D) (hbd : subBd D = F)
    (hm : ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T) :
    ∀ i j, Δ i ⊆ D → Δ j ⊆ D → i = j := by
  obtain ⟨φ, _, hφrange, hφ, hφlen⟩ := exists_normal_curve_of_oArc hF hn
  have hlenφ : curveLength Γ φ < η := hφlen ▸ hlen
  intro i j hi hj
  exact short_curve_enclosing_discs_indices_eq hS hT hrespect hK hd hη Δ r hr hrΔ hsep
    hφ hlenφ hF hF hφrange.symm.subset hφrange.symm.subset hD hD hbd hbd hm hm hi hj

/-- Claim (2) in the proof of Graph Minors XII (3.2), page 246.
A short normal circle in the punctured surface selects any disc that
it bounds which includes at most one prescribed disc, in the allowed
surface cases. -/
theorem small_disc_is_selected_of_at_most_one_prescribed_disc
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ η : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    (hT : GM10.IsTangle Γ.toHypergraph θ T)
    (hrespect : (PaintingOrDrawing.drawing Γ).IsRespectful θ T)
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    {ins : Drawing S → Set S} (hd : IsDerivedSlope (.drawing Γ) K θ T ins)
    (hη : η ≤ θ) (Δ r : ι → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hcase : ¬ IsSphere S ∨ 3 ≤ Nat.card ι) (hr : ∀ i, r i ∈ Γ.R)
    (hrΔ : ∀ i, (r i ∩ Δ i).Nonempty)
    (hsep : ∀ i j, i ≠ j → η ≤ tangleMetric Γ K ins θ (r i) (r j))
    {F D : Set S} (hF : IsOArc F) (hn : Γ.IsNormal F)
    (hlen : (Γ.V ∩ F).ncard < η) (hFstar : F ⊆ discComplement Δ)
    (hD : IsClosedDisc D) (hbdD : discBd D = F)
    (honeD : ∀ i j, Δ i ⊆ D → Δ j ⊆ D → i = j) :
    ((PaintingOrDrawing.drawing Γ).inter D,
      (PaintingOrDrawing.drawing Γ).interOutside D) ∈ T := by
  have hlenθ : (F ∩ Γ.V).ncard < θ := by
    rw [inter_comm]
    exact hlen.trans_le hη
  obtain ⟨E, hE, hbdE, hmE⟩ := hrespect.2 F hF hn hlenθ
  have honeE := selected_disc_includes_at_most_one_prescribed_disc hS hT hrespect hK hd
    hη Δ r hr hrΔ hsep hF hn hlen hE hbdE hmE
  have hbE : discBd E = F :=
    (IsClosedDisc.frontier_eq_discBd hS hE).symm.trans ((subBd_eq_frontier E).symm.trans hbdE)
  have heq := eq_of_discBd_eq_of_at_most_one_deleted_disc hS Δ hΔ hcase hD hE
    (hbdD.trans hbE.symm) (hbdD.symm ▸ hFstar) honeD honeE
  simpa only [heq] using hmE

end GraphMinor.GM12
