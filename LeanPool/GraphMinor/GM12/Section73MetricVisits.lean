/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section73PointRestraintVisits
public import LeanPool.GraphMinor.GM14.Defs
import LeanPool.GraphMinor.GM12.Section77
import LeanPool.GraphMinor.GM11.Section91
import LeanPool.GraphMinor.GM11.Section85

/-!
# Metric witnesses with bounded visits

XII (7.3), page 262, applies XI (9.2) to a shortest metric walk.
Its inside is a restraint by XI (8.5), whose perimeter is at most
the walk length. The two-visit selection therefore preserves the
metric budget. When the second corresponding atom is the hub
singleton, the distinguished-point selection gives one hub visit.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11 GM14

/-- A metric below the order, between distinct atoms, has a
witness no longer than twice the metric and visiting every vertex
at most twice, as required in XII (7.3)(i), page 262. -/
theorem exists_tangleMetric_walk_with_two_visit_bound
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ} {ins : Drawing S → Set S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hs : IsSlope K (2 * θ) ins) {a b : Set S} (hab : a ≠ b)
    (hlt : tangleMetric Γ K ins θ a b < θ) :
    ∃ (p : S) (W : GraphWalk K.toGraph p p) (a' b' : Set S),
      IsCorrespondingAtom Γ K a a' ∧ IsCorrespondingAtom Γ K b b' ∧
      W.length ≤ 2 * tangleMetric Γ K ins θ a b ∧ W.length < 2 * θ ∧
      a' ⊆ insWalk ins K W ∧ b' ⊆ insWalk ins K W ∧
      ∀ v, walkVertexCount v W ≤ 2 := by
  rcases tangleMetric_cases (ins := ins) (θ := θ) hK.2.1 hab with heq | ⟨_, hwit⟩
  · rw [heq] at hlt
    exact (Nat.lt_irrefl θ hlt).elim
  obtain ⟨u, Z, a', b', ha', hb', hZshort, hZlen, haZ, hbZ⟩ := hwit
  obtain ⟨hY, hperim⟩ := theorem_8_5_proof hS hs Z hZshort
  obtain ⟨p, W, hlen, hshort, haW, hbW, hcount⟩ :=
    exists_restraint_walk_with_two_visit_bound hS hs ha'.2.1 hb'.2.1 hY haZ hbZ
  exact ⟨p, W, a', b', ha', hb', (hlen.trans hperim).trans_eq hZlen,
    hshort, haW, hbW, hcount⟩

/-- If the atom corresponding to the second metric argument is
`{v}`, its metric witness can be chosen with at most one visit to
`v`. This is the witness refinement in XII (7.3)(ii), page 262. -/
theorem exists_tangleMetric_walk_with_one_point_visit_bound
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {Γ K : Drawing S} {θ : ℕ} {ins : Drawing S → Set S}
    (hK : (PaintingOrDrawing.drawing Γ).IsRadialDrawing K)
    (hs : IsSlope K (2 * θ) ins) {a b : Set S} {v : S}
    (hcor : IsCorrespondingAtom Γ K b {v}) (hab : a ≠ b)
    (hlt : tangleMetric Γ K ins θ a b < θ) :
    ∃ (p : S) (W : GraphWalk K.toGraph p p) (a' : Set S),
      IsCorrespondingAtom Γ K a a' ∧
      W.length ≤ 2 * tangleMetric Γ K ins θ a b ∧ W.length < 2 * θ ∧
      a' ⊆ insWalk ins K W ∧ v ∈ insWalk ins K W ∧ walkVertexCount v W ≤ 1 := by
  let : LocallyConnectedSpace S := IsClosedSurface.locallyConnectedSpace hS
  rcases tangleMetric_cases (ins := ins) (θ := θ) hK.2.1 hab with heq | ⟨_, hwit⟩
  · rw [heq] at hlt
    exact (Nat.lt_irrefl θ hlt).elim
  obtain ⟨u, Z, a', b', ha', hb', hZshort, hZlen, haZ, hbZ⟩ := hwit
  have hb'eq : b' = {v} := (existsUnique_correspondingAtom' hK hcor.1).unique hb' hcor
  have hvZ : v ∈ insWalk ins K Z := (hb'eq ▸ hbZ) (mem_singleton v)
  obtain ⟨hY, hperim⟩ := theorem_8_5_proof hS hs Z hZshort
  obtain ⟨p, W, hlen, hshort, haW, hvW, hcount⟩ :=
    exists_restraint_walk_with_one_point_visit_bound hS hs ha'.2.1 hcor.2.1 hY haZ hvZ
  exact ⟨p, W, a', ha', (hlen.trans hperim).trans_eq hZlen, hshort, haW, hvW, hcount⟩

end GraphMinor.GM12
