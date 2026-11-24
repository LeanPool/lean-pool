/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CliqueCrossingLabels
public import LeanPool.GraphMinor.GM12.Section4PortDrawing
import LeanPool.GraphMinor.GM12.Section4PortOrdering
import LeanPool.GraphMinor.GM12.Section4CliqueHamiltonArcs

/-!
# A finite clique drawn by crossing arcs

This assembles the source drawing in XII (4.5), pages 252--253.
Label the clique ports by ordered pairs of distinct vertices.
Sort them into vertex blocks with the Hamilton priorities, choose
arcs in general position, and convert their port positions to
vertex-pair coordinates. The crossing tests give a different
crossing edge for every edge. All witnesses are constructed here.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface

/-- The finite crossing-arc construction for the source clique
in XII (4.5), pages 252--253. The arcs are simple, avoid nonincident
vertices, meet pairwise finitely, and have no triple meeting away
from vertices. Every edge has a different crossing edge. -/
theorem exists_clique_crossing_arcs {p : ℕ} (hp : 4 ≤ p) :
    ∃ ψ : (Fin (p * (p - 1) / 2) × Bool) ≃ {q : Fin p × Fin p // q.1 ≠ q.2},
      (∀ i b, (ψ (i, !b)).val = ((ψ (i, b)).val.2, (ψ (i, b)).val.1)) ∧
    ∃ (v : Fin p → ℂ) (s : Fin (p * (p - 1) / 2) × Bool → ℝ)
      (E : Fin (p * (p - 1) / 2) → Set ℂ) (F : Fin p → Fin p → ℝ),
      Function.Injective v ∧ (∀ i, 1 < ‖v i‖) ∧
      Function.Injective (fun x => (ee (s x) : ℂ)) ∧ (∀ x, s x ∈ Ioo 0 1) ∧
      (∀ i, IsLineWithEnds (E i) (v (ψ (i, false)).val.1) (v (ψ (i, true)).val.1)) ∧
      (∀ i j, v j ∈ E i ↔ j = (ψ (i, false)).val.1 ∨ j = (ψ (i, true)).val.1) ∧
      (∀ i, E i ∩ closedBall 0 1 = segment ℝ (ee (s (i, false)) : ℂ) (ee (s (i, true)) : ℂ)) ∧
      (∀ i j, i ≠ j → (E i ∩ E j).Finite) ∧
      (∀ i j, i ≠ j → E i ∩ E j ⊆
        (segment ℝ (ee (s (i, false)) : ℂ) (ee (s (i, true)) : ℂ) ∩
          segment ℝ (ee (s (j, false)) : ℂ) (ee (s (j, true)) : ℂ)) ∪ range v) ∧
      (∀ i j k, i ≠ j → j ≠ k → i ≠ k → E i ∩ E j ∩ E k ⊆ range v) ∧
      (∀ i, ∃ j, j ≠ i ∧ ∃ x : ℂ, x ∈ E i ∩ E j ∧ x ∉ range v) ∧
      (∀ w, ∃ i j, i ≠ j ∧ E i ∩ E j = {v w}) ∧
      (∀ v w, F v w ∈ Ioo 0 1) ∧
      (∀ v w i j, v < i → F v w < F i j) ∧
      (∀ v w z, hamiltonPortPriority v w < hamiltonPortPriority v z → F v w < F v z) ∧
      ∀ v w (hvw : v ≠ w), F v w = s (ψ.symm ⟨(v, w), hvw⟩) := by
  obtain ⟨ψ, hψ⟩ := exists_clique_port_bijection p
  let κ := fun x => (ψ x).val.1
  let priority := fun x => hamiltonPortPriority (ψ x).val.1 (ψ x).val.2
  obtain ⟨ρ, hρ, hρblocks, hρpriority⟩ := exists_port_ordering κ priority
  have hκ : ∀ i, κ (i, false) ≠ κ (i, true) := by
    intro i
    have hflip := congrArg Prod.fst (hψ i false)
    change (ψ (i, true)).val.1 = (ψ (i, false)).val.2 at hflip
    change (ψ (i, false)).val.1 ≠ (ψ (i, true)).val.1
    rw [hflip]
    exact (ψ (i, false)).property
  obtain ⟨v, s, E, hvinj, hvnorm, hsinj, hs, hsorder, hEline, hEvertex, hEdisc,
    _, hEfinite, hEinter, hEtriple, _⟩ := exists_port_edge_arcs κ hκ ρ hρ
  have hsblocks : ∀ x y, (ψ x).val.1 < (ψ y).val.1 → s x < s y :=
    fun x y hxy => hsorder x y (hρblocks x y hxy)
  have hspriority : ∀ x y, (ψ x).val.1 = (ψ y).val.1 →
      hamiltonPortPriority (ψ x).val.1 (ψ x).val.2 <
        hamiltonPortPriority (ψ y).val.1 (ψ y).val.2 → s x < s y :=
    fun x y hsame hlt => hsorder x y (hρpriority x y hsame hlt)
  obtain ⟨F, hF, hFblocks, hFpriority, hcoord⟩ :=
    exists_clique_port_matrix hp ψ s hs hsblocks hspriority
  have hcross : ∀ i, ∃ j, j ≠ i ∧ ∃ x : ℂ, x ∈ E i ∩ E j ∧ x ∉ range v := by
    intro i
    obtain ⟨j, hji, x, hxi, hxj⟩ :=
      every_labelled_clique_chord_has_crossing hp ψ hψ s F hF hFblocks hFpriority hcoord i
    have hxEi : x ∈ E i ∩ closedBall (0 : ℂ) 1 := hEdisc i ▸ hxi
    have hxEj : x ∈ E j ∩ closedBall (0 : ℂ) 1 := hEdisc j ▸ hxj
    refine ⟨j, hji, x, ⟨hxEi.1, hxEj.1⟩, ?_⟩
    rintro ⟨k, rfl⟩
    exact (not_le_of_gt (hvnorm k)) (mem_closedBall_zero_iff.mp hxEi.2)
  exact ⟨ψ, hψ, v, s, E, F, hvinj, hvnorm, hsinj, hs, hEline, hEvertex,
    hEdisc, hEfinite, hEinter, hEtriple, hcross,
    fun w => exists_two_incident_Hamilton_arcs (by omega : 3 ≤ p) ψ hψ s v E
      hEvertex hEinter F hF hFblocks hFpriority hcoord w,
    hF, hFblocks, hFpriority, hcoord⟩

end GraphMinor.GM12
