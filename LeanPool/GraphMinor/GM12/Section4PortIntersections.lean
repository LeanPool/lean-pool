/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4OuterPorts
import LeanPool.GraphMinor.Surface.Lunes

/-!
# Intersections of complete port edge arcs

In the crossing construction of XII (4.5), page 253, the inner
chords lie in the unit disc and the outer pieces lie in disjoint
vertex neighborhoods. Two outer pieces can meet only at their
common vertex. Hence two complete edge arcs meet only at their
chord intersections or at vertices. This gives finite pairwise
intersections once the chords are chosen in general position.
-/

public section

namespace GraphMinor.GM12

open Set Metric Surface

/-- The three straight pieces of an edge in the coordinate port
construction for XII (4.5), page 253: an outer piece, the inner
chord, and the other outer piece. -/
@[expose] noncomputable def portEdgeArc {m n : ℕ} (v : Fin m → ℂ)
    (κ : Fin n × Bool → Fin m) (a : Fin n × Bool → ℂ) (i : Fin n) : Set ℂ :=
  (segment ℝ (a (i, false)) (v (κ (i, false))) ∪
    segment ℝ (a (i, false)) (a (i, true))) ∪
    segment ℝ (a (i, true)) (v (κ (i, true)))

/-- Two complete port edge arcs meet only in their inner chords
or at outer vertices. This is the pairwise-intersection assertion
for the source drawing in XII (4.5), page 253. -/
theorem port_edge_inter_subset_chords_union_vertices {m n : ℕ}
    (v : Fin m → ℂ) (κ : Fin n × Bool → Fin m) (a : Fin n × Bool → ℂ)
    (ha : ∀ x, ‖a x‖ = 1) (hinj : Function.Injective a)
    (hvisible : ∀ x, 1 < ((starRingEnd ℂ) (a x) * v (κ x)).re)
    (U : Fin m → Set ℂ) (hU : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hsub : ∀ x, segment ℝ (a x) (v (κ x)) ⊆ U (κ x))
    {i j : Fin n} (hij : i ≠ j) :
    ((segment ℝ (a (i, false)) (v (κ (i, false))) ∪
        segment ℝ (a (i, false)) (a (i, true))) ∪
      segment ℝ (a (i, true)) (v (κ (i, true)))) ∩
      ((segment ℝ (a (j, false)) (v (κ (j, false))) ∪
        segment ℝ (a (j, false)) (a (j, true))) ∪
      segment ℝ (a (j, true)) (v (κ (j, true)))) ⊆
    (segment ℝ (a (i, false)) (a (i, true)) ∩
      segment ℝ (a (j, false)) (a (j, true))) ∪ range v := by
  intro x hx
  have hclass : ∀ l, x ∈
      ((segment ℝ (a (l, false)) (v (κ (l, false))) ∪
        segment ℝ (a (l, false)) (a (l, true))) ∪
        segment ℝ (a (l, true)) (v (κ (l, true)))) →
      (x ∈ segment ℝ (a (l, false)) (a (l, true))) ∨
        ∃ b : Bool, x ∈ segment ℝ (a (l, b)) (v (κ (l, b))) := by
    intro l hl
    rcases hl with (hl | hl) | hl
    · exact Or.inr ⟨false, hl⟩
    · exact Or.inl hl
    · exact Or.inr ⟨true, hl⟩
  have hD : ∀ l, segment ℝ (a (l, false)) (a (l, true)) ⊆ closedBall (0 : ℂ) 1 :=
    fun l => (convex_closedBall (0 : ℂ) 1).segment_subset (by simp [ha]) (by simp [ha])
  have hport : ∀ l b, x ∈ segment ℝ (a (l, b)) (v (κ (l, b))) →
      x ∈ closedBall (0 : ℂ) 1 → x = a (l, b) := by
    intro l b hxleg hxD
    exact show x ∈ ({a (l, b)} : Set ℂ) from
      outer_port_segment_inter_disc (ha _) (hvisible _) ▸ And.intro hxleg hxD
  rcases hclass i hx.1 with hxi | ⟨bi, hxi⟩
  · rcases hclass j hx.2 with hxj | ⟨bj, hxj⟩
    · exact Or.inl ⟨hxi, hxj⟩
    · have hxeq := hport j bj hxj (hD i hxi)
      have hends : a (j, bj) = a (i, false) ∨ a (j, bj) = a (i, true) := by
        have hunit : a (j, bj) ∈ sphere (0 : ℂ) 1 := by simp [ha]
        have hgeom := unit_chord_geometry (ha (i, false)) (ha (i, true))
          (fun h => Bool.false_ne_true (congrArg Prod.snd (hinj h)))
        exact show a (j, bj) ∈ ({a (i, false), a (i, true)} : Set ℂ) from
          hgeom.2.2 ▸ And.intro (hxeq ▸ hxi) hunit
      exact False.elim (hends.elim
        (fun h => hij (congrArg Prod.fst (hinj h)).symm)
        (fun h => hij (congrArg Prod.fst (hinj h)).symm))
  · rcases hclass j hx.2 with hxj | ⟨bj, hxj⟩
    · have hxeq := hport i bi hxi (hD j hxj)
      have hgeom := unit_chord_geometry (ha (j, false)) (ha (j, true))
        (fun h => Bool.false_ne_true (congrArg Prod.snd (hinj h)))
      have hends : a (i, bi) = a (j, false) ∨ a (i, bi) = a (j, true) :=
        show a (i, bi) ∈ ({a (j, false), a (j, true)} : Set ℂ) from
          hgeom.2.2 ▸ And.intro (hxeq ▸ hxj) (by simp [ha])
      exact False.elim (hends.elim
        (fun h => hij (congrArg Prod.fst (hinj h)))
        (fun h => hij (congrArg Prod.fst (hinj h))))
    · by_cases howner : κ (i, bi) = κ (j, bj)
      · have hstar := outer_port_segments_inter (ha (i, bi)) (ha (j, bj))
          (fun h => hij (congrArg Prod.fst (hinj h))) (hvisible (i, bi))
          (howner ▸ hvisible (j, bj))
        have hmeet : x ∈ segment ℝ (a (i, bi)) (v (κ (i, bi))) ∩
            segment ℝ (a (j, bj)) (v (κ (i, bi))) :=
          ⟨hxi, howner.symm ▸ hxj⟩
        have hxv : x = v (κ (i, bi)) := show x ∈ ({v (κ (i, bi))} : Set ℂ) from
          hstar ▸ hmeet
        exact Or.inr ⟨κ (i, bi), hxv.symm⟩
      · exact False.elim (Set.disjoint_left.mp (hU _ _ howner) (hsub _ hxi) (hsub _ hxj))

/-- The complete port edge arcs have finite pairwise intersections
when the chord supporting lines are distinct. This proves condition
(ii) of the crossing construction in XII (4.5), page 253. -/
theorem finite_port_edge_inter {m n : ℕ}
    (v : Fin m → ℂ) (κ : Fin n × Bool → Fin m) (a : Fin n × Bool → ℂ)
    (ha : ∀ x, ‖a x‖ = 1) (hinj : Function.Injective a)
    (hvisible : ∀ x, 1 < ((starRingEnd ℂ) (a x) * v (κ x)).re)
    (U : Fin m → Set ℂ) (hU : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hsub : ∀ x, segment ℝ (a x) (v (κ x)) ⊆ U (κ x))
    {i j : Fin n} (hij : i ≠ j)
    (hne : line[ℝ, a (i, false), a (i, true)] ≠ line[ℝ, a (j, false), a (j, true)]) :
    (portEdgeArc v κ a i ∩ portEdgeArc v κ a j).Finite := by
  exact ((finite_chord_inter_of_ne_lines hne).union (finite_range v)).subset
    (port_edge_inter_subset_chords_union_vertices v κ a ha hinj hvisible U hU hsub hij)

/-- A complete port edge arc passes through exactly its two
assigned outer vertices. This proves condition (i) for the source
crossing drawing in XII (4.5), page 253. -/
theorem port_edge_vertex_mem_iff {m n : ℕ}
    (v : Fin m → ℂ) (κ : Fin n × Bool → Fin m) (a : Fin n × Bool → ℂ)
    (ha : ∀ x, ‖a x‖ = 1) (hvnorm : ∀ j, 1 < ‖v j‖)
    (U : Fin m → Set ℂ) (hvU : ∀ j, v j ∈ U j)
    (hU : ∀ i j, i ≠ j → Disjoint (U i) (U j))
    (hsub : ∀ x, segment ℝ (a x) (v (κ x)) ⊆ U (κ x)) (i : Fin n) (j : Fin m) :
    v j ∈ portEdgeArc v κ a i ↔ j = κ (i, false) ∨ j = κ (i, true) := by
  have howner : ∀ x, v j ∈ segment ℝ (a x) (v (κ x)) → j = κ x := by
    intro x hx
    by_contra hne
    exact Set.disjoint_left.mp (hU j (κ x) hne) (hvU j) (hsub x hx)
  constructor
  · intro hj
    rcases hj with (hj | hj) | hj
    · exact Or.inl (howner _ hj)
    · have hD : v j ∈ closedBall (0 : ℂ) 1 :=
        (convex_closedBall (0 : ℂ) 1).segment_subset (by simp [ha]) (by simp [ha]) hj
      exact False.elim ((not_le_of_gt (hvnorm j)) (mem_closedBall_zero_iff.mp hD))
    · exact Or.inr (howner _ hj)
  · rintro (rfl | rfl)
    · exact Or.inl (Or.inl (right_mem_segment _ _ _))
    · exact Or.inr (right_mem_segment _ _ _)

end GraphMinor.GM12
