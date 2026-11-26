/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4GeneralPositionPorts
public import LeanPool.GraphMinor.GM12.Section4PortEdgeArc
public import LeanPool.GraphMinor.GM12.Section4PortNeighborhoods
import LeanPool.GraphMinor.GM12.Section4PortIntersections

/-!
# Simple edge arcs from ordered vertex blocks

For the source crossing drawing in XII (4.5), page 253, choose
separate neighborhoods at the circle centers of the vertices.
Ordered ports in each block give chords in general position.
Join each chord to the two outer vertices. The resulting edge
arcs are simple, and their portions inside the unit disc are
exactly their chords.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface

/-- Construct the simple edge arcs of the port drawing used in
XII (4.5), page 253. The edge ends are prescribed by `κ`, and `ρ`
orders their vertex blocks around the circle. -/
theorem exists_port_edge_arcs {m n : ℕ}
    (κ : Fin n × Bool → Fin m) (hκ : ∀ i, κ (i, false) ≠ κ (i, true))
    (ρ : (Fin n × Bool) ≃ Fin (2 * n))
    (horder : Monotone (fun i => κ (ρ.symm i))) :
    ∃ (v : Fin m → ℂ) (p : Fin n × Bool → ℝ) (E : Fin n → Set ℂ),
      Function.Injective v ∧ (∀ i, 1 < ‖v i‖) ∧
      Function.Injective (fun x => (ee (p x) : ℂ)) ∧
      (∀ x, p x ∈ Ioo 0 1) ∧
      (∀ x y, ρ x < ρ y → p x < p y) ∧
      (∀ i, IsLineWithEnds (E i) (v (κ (i, false))) (v (κ (i, true)))) ∧
      (∀ i j, v j ∈ E i ↔ j = κ (i, false) ∨ j = κ (i, true)) ∧
      (∀ i, E i ∩ closedBall 0 1 = segment ℝ (ee (p (i, false)) : ℂ) (ee (p (i, true)) : ℂ)) ∧
      (∀ i j, i ≠ j →
        (segment ℝ (ee (p (i, false)) : ℂ) (ee (p (i, true)) : ℂ) ∩
          segment ℝ (ee (p (j, false)) : ℂ) (ee (p (j, true)) : ℂ)).Finite) ∧
      (∀ i j, i ≠ j → (E i ∩ E j).Finite) ∧
      (∀ i j, i ≠ j → E i ∩ E j ⊆
        (segment ℝ (ee (p (i, false)) : ℂ) (ee (p (i, true)) : ℂ) ∩
          segment ℝ (ee (p (j, false)) : ℂ) (ee (p (j, true)) : ℂ)) ∪ range v) ∧
      (∀ i j k, i ≠ j → j ≠ k → i ≠ k → E i ∩ E j ∩ E k ⊆ range v) ∧
      ∀ i j k, i ≠ j → j ≠ k → i ≠ k → ∀ x ∈ closedBall (0 : ℂ) 1,
        ¬ (x ∈ E i ∧ x ∈ E j ∧ x ∈ E k) := by
  let ξ : Fin m → ℝ := fun i => ((i.val : ℝ) + 1) / ((m : ℝ) + 1)
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hξ : StrictMono ξ := by
    intro i j hij
    change ((i.val : ℝ) + 1) / ((m : ℝ) + 1) <
      ((j.val : ℝ) + 1) / ((m : ℝ) + 1)
    apply div_lt_div_of_pos_right _ hden
    have hval : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    linarith
  have hξ01 : ∀ i, ξ i ∈ Ioo (0 : ℝ) 1 := by
    intro i
    constructor
    · exact div_pos (by positivity) hden
    · apply (div_lt_one hden).mpr
      have hi : (i.val : ℝ) < (m : ℝ) := by exact_mod_cast i.isLt
      linarith
  have hcenters : Function.Injective (fun i => (ee (ξ i) : ℂ)) := by
    intro i j hij
    apply hξ.injective
    exact ee_injOn_short_interval (by norm_num : (1 : ℝ) ≤ 0 + 1)
      (hξ01 i) (hξ01 j) (Subtype.ext hij)
  obtain ⟨v, U, O, hU, hUdisj⟩ := exists_disjoint_outer_vertex_neighborhoods
    (fun i => (ee (ξ i) : ℂ)) (by intro i; simp) hcenters
  let c : Fin (2 * n) → ℝ := fun i => ξ (κ (ρ.symm i))
  let Q : Fin (2 * n) → Set ℂ := fun i => O (κ (ρ.symm i))
  obtain ⟨p, hp, hporder, hpinj, hne, hthree⟩ := exists_ordered_general_position_ports
    ρ c (hξ.monotone.comp horder) (fun i => hξ01 _)
    Q (fun i => (hU _).2.2.2.2.2.1) (fun i => (hU _).2.2.2.2.2.2.1)
  have hpO : ∀ x, (ee (p x) : ℂ) ∈ O (κ x) := by
    intro x
    simpa only [Q, ρ.symm_apply_apply] using (hp x).2
  let a : Fin n → ℂ := fun i => (ee (p (i, false)) : ℂ)
  let b : Fin n → ℂ := fun i => (ee (p (i, true)) : ℂ)
  have hvisible : ∀ x, 1 < ((starRingEnd ℂ) (ee (p x) : ℂ) * v (κ x)).re ∧
      segment ℝ (ee (p x) : ℂ) (v (κ x)) ⊆ U (κ x) := by
    intro x
    exact (hU _).2.2.2.2.2.2.2.2 _ (hpO x)
  have hab : ∀ i, a i ≠ b i := by
    intro i hi
    have h := hpinj hi
    exact Bool.false_ne_true (congrArg Prod.snd h)
  let E : Fin n → Set ℂ := fun i =>
    (segment ℝ (a i) (v (κ (i, false))) ∪ segment ℝ (a i) (b i)) ∪
      segment ℝ (b i) (v (κ (i, true)))
  have hE : ∀ i, IsLineWithEnds (E i) (v (κ (i, false))) (v (κ (i, true))) ∧
      E i ∩ closedBall 0 1 = segment ℝ (a i) (b i) := by
    intro i
    apply port_edge_isLine (by simp [a]) (by simp [b]) (hab i)
      (hvisible (i, false)).1 (hvisible (i, true)).1
    exact (hUdisj _ _ (hκ i)).mono (hvisible (i, false)).2 (hvisible (i, true)).2
  have hinside : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      ∀ x ∈ closedBall (0 : ℂ) 1, ¬ (x ∈ E i ∧ x ∈ E j ∧ x ∈ E k) := by
    intro i j k hij hjk hik x hxD hx
    have hline : ∀ l, x ∈ E l → x ∈ line[ℝ, a l, b l] := by
      intro l hxE
      have hseg : x ∈ segment ℝ (a l) (b l) :=
        (hE l).2 ▸ (show x ∈ E l ∩ closedBall 0 1 from ⟨hxE, hxD⟩)
      exact (line[ℝ, a l, b l]).convex.segment_subset
        (left_mem_affineSpan_pair _ _ _) (right_mem_affineSpan_pair _ _ _) hseg
    exact hthree i j k hij hjk hik x ⟨hline i hx.1, hline j hx.2.1, hline k hx.2.2⟩
  refine ⟨v, p, E, ?_, ?_, hpinj, fun x => (hp x).1, hporder,
    fun i => (hE i).1, ?_, fun i => (hE i).2, ?_, ?_, ?_, ?_, hinside⟩
  · intro i j hij
    by_contra hneij
    exact Set.disjoint_left.mp (hUdisj i j hneij) (hU i).2.2.2.1
      (hij ▸ (hU j).2.2.2.1)
  · intro i
    exact (hU i).2.2.2.2.1
  · intro i j
    exact port_edge_vertex_mem_iff v κ (fun x => (ee (p x) : ℂ)) (by intro x; simp)
      (fun j => (hU j).2.2.2.2.1) U (fun j => (hU j).2.2.2.1) hUdisj
      (fun x => (hvisible x).2) i j
  · intro i j hij
    exact finite_chord_inter_of_ne_lines (hne i j hij)
  · intro i j hij
    exact finite_port_edge_inter v κ (fun x => (ee (p x) : ℂ)) (by intro x; simp)
      hpinj (fun x => (hvisible x).1) U hUdisj (fun x => (hvisible x).2) hij (hne i j hij)
  · intro i j hij
    exact port_edge_inter_subset_chords_union_vertices v κ
      (fun x => (ee (p x) : ℂ)) (by intro x; simp) hpinj
      (fun x => (hvisible x).1) U hUdisj (fun x => (hvisible x).2) hij
  · intro i j k hij hjk hik x hx
    have hpair := port_edge_inter_subset_chords_union_vertices v κ
      (fun x => (ee (p x) : ℂ)) (by intro x; simp) hpinj
      (fun x => (hvisible x).1) U hUdisj (fun x => (hvisible x).2) hij
      (show x ∈ E i ∩ E j from hx.1)
    rcases hpair with hchord | hxv
    · have hxD := (unit_chord_geometry (by simp [a] : ‖a i‖ = 1) (by simp [b] : ‖b i‖ = 1)
        (hab i)).2.1 hchord.1
      exact False.elim (hinside i j k hij hjk hik x hxD ⟨hx.1.1, hx.1.2, hx.2⟩)
    · exact hxv

end GraphMinor.GM12
