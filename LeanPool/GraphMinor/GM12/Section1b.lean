/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

import LeanPool.GraphMinor.GM14.RadialAtoms

public import LeanPool.GraphMinor.GM12.Section1
public import LeanPool.GraphMinor.GM12.Cited
import LeanPool.GraphMinor.GM11.RadialFacts
import LeanPool.GraphMinor.GM11.PaintingFacts
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM11.Section85
import LeanPool.GraphMinor.GM11.Section91

/-!
# Graph Minors XII, (1.2): a distant edge

Choose a point in the corresponding radial atom and apply XI (8.12). The radial region it
provides contains an original edge. XI (8.5) rules out a short closed walk containing both atoms.
If this edge is the starting atom, choose another edge in its place.

The last step requires at least two edges. This corrects XII (1.2), which fails for the single
edge drawing on the sphere with its respectful tangle of order two. XIV (7.1) includes this
hypothesis.
-/

public section

namespace GraphMinor.GM12

open Set Topology GraphMinor.Surface GraphMinor.GM10 GraphMinor.GM11 GraphMinor.GM14 Hypergraph

universe u

variable {S : Type u} [TopologicalSpace S] [T1Space S]

omit [T1Space S] in
private theorem atom_nonempty {Γ : Drawing S} {x : Set S} (hx : x ∈ Γ.A) : x.Nonempty := by
  rcases hx with (⟨v, -, rfl⟩ | hx) | hx
  · exact singleton_nonempty v
  · exact hx.1
  · exact region_nonempty hx

omit [T1Space S] in
/-- Every atom of the original drawing has a unique corresponding
atom in its radial drawing. -/
theorem existsUnique_correspondingAtom {H K : Drawing S}
    (hK : (PaintingOrDrawing.drawing H).IsRadialDrawing K) {x : Set S} (hx : x ∈ H.A) :
    ∃! x' : Set S, IsCorrespondingAtom H K x x' :=
  GM14.existsUnique_correspondingAtom hK hx

/-- An edge whose corresponding radial region rules out short walks between its atom and
the starting atom. When the edge is the starting atom, the same obstruction works for
every other atom. -/
theorem exists_edge_for_metric_eq_order (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric H θ T d) (hE : H.E.Nonempty) {z : Set S} (hz : z ∈ H.A) :
    ∃ e ∈ H.E, ∀ y ∈ H.A, z ≠ y → (y = e ∨ z = e) → d z y = θ := by
  have : T2Space S := hS.2.1
  have : ConnectedSpace S := hConn
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hResp, K, ins, hK, hd, hd_eq⟩ := hMetric
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS (⟨hResp.2.1.one_le,
      hResp.2.1.isSeparation, hResp.2.1.order_lt,
      hResp.2.1.axiom1, hResp.2.1.axiom2⟩ : IsPretangle H.toHypergraph θ T) hK.2.1.1 hd
  have hrf := GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  obtain ⟨z', hz', hz'_uniq⟩ := existsUnique_correspondingAtom hK hz
  obtain ⟨c, hc⟩ := atom_nonempty hz'.2.1
  obtain ⟨r₁, hr₁, hno₁⟩ := GM11.theorem_8_12_proof hS hsl c
  obtain ⟨e₁, he₁, he₁r₁⟩ := hrf.1 r₁ hr₁
  have he₁_corr : IsCorrespondingAtom H K e₁ r₁ :=
    ⟨Or.inl (Or.inr he₁), Or.inr hr₁, Or.inr (Or.inl ⟨he₁, hr₁, he₁r₁⟩)⟩
  refine ⟨e₁, he₁, fun y hy hne hEndpoint => ?_⟩
  rw [hd_eq z hz y hy]
  rcases GM11.tangleMetric_cases (ins := ins) (θ := θ) hK.2.1 hne with h | ⟨_, hw⟩
  · exact h
  exfalso
  obtain ⟨_, W, z₁, y₁, hz₁, hy₁, hW, _, hzW, hyW⟩ := hw
  have hzEq : z₁ = z' := hz'_uniq z₁ hz₁
  have hrW : r₁ ⊆ insWalk ins K W := by
    rcases hEndpoint with he | he
    · have hyCorr : IsCorrespondingAtom H K y r₁ := he.symm ▸ he₁_corr
      have hyEq : y₁ = r₁ := (existsUnique_correspondingAtom hK hy).unique hy₁ hyCorr
      exact hyEq ▸ hyW
    · have hzCorr : IsCorrespondingAtom H K z r₁ := he.symm ▸ he₁_corr
      have hzRadial : z₁ = r₁ := (existsUnique_correspondingAtom hK hz).unique hz₁ hzCorr
      exact hzRadial ▸ hzW
  exact hno₁ _ (GM11.theorem_8_5_proof hS hsl W hW).1
    ⟨hzW (hzEq.symm ▸ hc), hrW⟩

/-- When a second edge is available if needed, every atom has an edge at distance equal to
the order of the tangle. -/
theorem exists_edge_dist_eq_theta_of_metric (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric H θ T d) (hE : H.E.Nonempty)
    {z : Set S} (hz : z ∈ H.A) (hzE : 2 ≤ H.E.ncard ∨ z ∉ H.E) :
    ∃ e ∈ H.E, d z e = θ := by
  obtain ⟨e, he, hDist⟩ := exists_edge_for_metric_eq_order hS hConn hMetric hE hz
  by_cases hze : z = e
  · have hTwo : 2 ≤ H.E.ncard := hzE.resolve_right (fun h => h (hze.symm ▸ he))
    obtain ⟨e', he', hne⟩ := exists_ne_of_one_lt_ncard (s := H.E) (by omega) z
    exact ⟨e', he', hDist _ (Or.inl (Or.inr he')) hne.symm (Or.inr hze)⟩
  · exact ⟨e, he, hDist _ (Or.inl (Or.inr he)) hze (Or.inl rfl)⟩

/-- Graph Minors XII, (1.2), page 242, with the necessary hypothesis that there are at least
two edges, as in XIV (7.1). The proof uses the established XI (8.5) and (8.12). -/
theorem theorem_1_2_proof (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hd : HasTangleMetric Γ θ T d)
    (hE : 2 ≤ Γ.E.ncard) {c : Set S} (hc : c ∈ Γ.A) :
    ∃ e ∈ Γ.E, d c e = θ := by
  have he : Γ.E.Nonempty := (Set.ncard_pos Γ.finite_edges).mp (lt_of_lt_of_le (by decide) hE)
  exact exists_edge_dist_eq_theta_of_metric hS inferInstance hd he hc (Or.inl hE)

end GraphMinor.GM12
