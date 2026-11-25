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
import LeanPool.GraphMinor.GM11.CitedResults
import LeanPool.GraphMinor.GM11.RadialFacts
import LeanPool.GraphMinor.GM11.PaintingFacts
import LeanPool.GraphMinor.GM11.Section6

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

private theorem exists_edge_dist_eq_theta (hS : IsClosedSurface S) (hConn : ConnectedSpace S)
    {H : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ}
    (hMetric : HasTangleMetric H θ T d) (hE : H.E.Nonempty)
    {z : Set S} (hz : z ∈ H.A) (hzE : 2 ≤ H.E.ncard ∨ z ∉ H.E) :
    ∃ e ∈ H.E, d z e = θ := by
  have : T2Space S := hS.2.1
  have : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  obtain ⟨hResp, K, ins, hK, hd, hd_eq⟩ := hMetric
  have hsl : IsSlope K (2 * θ) ins :=
    GM11.isSlope_of_derived (Γ := PaintingOrDrawing.drawing H) hS (⟨hResp.2.1.one_le,
      hResp.2.1.isSeparation, hResp.2.1.order_lt,
      hResp.2.1.axiom1, hResp.2.1.axiom2⟩ : IsPretangle H.toHypergraph θ T) hK.2.1.1 hd
  have hrf := GM11.regionFacts_of_radial ⟨hK.1, hK.2.1⟩ hS hK.2.2 hE
  obtain ⟨z', hz', hz'_uniq⟩ := existsUnique_correspondingAtom hK hz
  obtain ⟨c, hc⟩ := atom_nonempty hz'.2.1
  obtain ⟨r₁, hr₁, hno₁⟩ := GM11.gm14_theorem_8_12 S hS hConn K (2 * θ) ins hsl c
  obtain ⟨e₁, he₁, he₁r₁⟩ := hrf.1 r₁ hr₁
  have he₁_corr : IsCorrespondingAtom H K e₁ r₁ :=
    ⟨Or.inl (Or.inr he₁), Or.inr hr₁, Or.inr (Or.inl ⟨he₁, hr₁, he₁r₁⟩)⟩
  by_cases he₁z : e₁ = z
  · subst he₁z
    have hzE' : 2 ≤ H.E.ncard := hzE.resolve_right (not_not.mpr he₁)
    obtain ⟨e₂, he₂, he₂ne⟩ := exists_ne_of_one_lt_ncard (s := H.E) (by omega) e₁
    have hz'_eq_r₁ : z' = r₁ := (hz'_uniq r₁ he₁_corr).symm
    refine ⟨e₂, he₂, ?_⟩
    rw [hd_eq e₁ hz e₂ (Or.inl (Or.inr he₂))]
    unfold tangleMetric
    split_ifs with h1 h2
    · exact absurd h1 (Ne.symm he₂ne)
    · exfalso
      obtain ⟨u, W, z₁', r₂', hz₁', -, hW, hzW, -⟩ := h2
      have hz₁_eq : z₁' = r₁ := (hz'_uniq z₁' hz₁').trans hz'_eq_r₁
      subst hz₁_eq
      have hrest := (GM11.gm12_theorem_8_5 S hS hConn K (2 * θ) ins hsl u W hW).1
      exact hno₁ (insWalk ins K W) hrest ⟨hzW (hz'_eq_r₁ ▸ hc), hzW⟩
    · rfl
  · refine ⟨e₁, he₁, ?_⟩
    rw [hd_eq z hz e₁ (Or.inl (Or.inr he₁))]
    unfold tangleMetric
    split_ifs with h1 h2
    · exact absurd h1 (Ne.symm he₁z)
    · exfalso
      obtain ⟨u, W, z₁', r₁', hz₁', hr₁', hW, hzW, hrW⟩ := h2
      have hz₁_eq : z₁' = z' := hz'_uniq z₁' hz₁'
      have hr₁_eq : r₁' = r₁ :=
        (existsUnique_correspondingAtom hK (Or.inl (Or.inr he₁))).unique hr₁' he₁_corr
      subst hz₁_eq hr₁_eq
      have hrest := (GM11.gm12_theorem_8_5 S hS hConn K (2 * θ) ins hsl u W hW).1
      exact hno₁ (insWalk ins K W) hrest ⟨hzW hc, hrW⟩
    · rfl

/-- Graph Minors XII, (1.2), page 242, with the necessary hypothesis that there are at least
two edges, as in XIV (7.1). The proof uses the established XI (8.5) and (8.12). -/
theorem theorem_1_2_proof (hS : IsClosedSurface S) [ConnectedSpace S]
    {Γ : Drawing S} {θ : ℕ}
    {T : Set (Hypergraph S (Set S) × Hypergraph S (Set S))}
    {d : Set S → Set S → ℕ} (hd : HasTangleMetric Γ θ T d)
    (hE : 2 ≤ Γ.E.ncard) {c : Set S} (hc : c ∈ Γ.A) :
    ∃ e ∈ Γ.E, d c e = θ := by
  have he : Γ.E.Nonempty := (Set.ncard_pos Γ.finite_edges).mp (lt_of_lt_of_le (by decide) hE)
  exact exists_edge_dist_eq_theta hS inferInstance hd he hc (Or.inl hE)

end GraphMinor.GM12
