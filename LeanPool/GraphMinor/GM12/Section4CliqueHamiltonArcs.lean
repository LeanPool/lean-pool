/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4CliquePortCoordinates
public import LeanPool.GraphMinor.GM12.Section4HamiltonChordSeparation

/-!
# The two Hamilton edge arcs at each vertex

In XII (4.5), page 252, each vertex has two incident edges that
do not cross. Their Hamilton chords are disjoint. Any other
intersection of their complete arcs is an outer vertex, and their
only common endpoint is the chosen vertex. Thus their complete
arcs meet exactly at that vertex.
-/

public section

namespace GraphMinor.GM12

open Set Surface

/-- The incoming and outgoing Hamilton edge arcs meet exactly
at their common vertex. This verifies condition (vii) of the source
construction in XII (4.5), page 252, for the complete edge arcs. -/
theorem exists_two_incident_Hamilton_arcs {p : ℕ} (hp : 3 ≤ p)
    (ψ : (Fin (p * (p - 1) / 2) × Bool) ≃ {q : Fin p × Fin p // q.1 ≠ q.2})
    (hψ : ∀ i b, (ψ (i, !b)).val = ((ψ (i, b)).val.2, (ψ (i, b)).val.1))
    (s : Fin (p * (p - 1) / 2) × Bool → ℝ)
    (V : Fin p → ℂ) (E : Fin (p * (p - 1) / 2) → Set ℂ)
    (hEvertex : ∀ i j, V j ∈ E i ↔ j = (ψ (i, false)).val.1 ∨ j = (ψ (i, true)).val.1)
    (hEinter : ∀ i j, i ≠ j → E i ∩ E j ⊆
      (segment ℝ (ee (s (i, false)) : ℂ) (ee (s (i, true)) : ℂ) ∩
        segment ℝ (ee (s (j, false)) : ℂ) (ee (s (j, true)) : ℂ)) ∪ range V)
    (F : Fin p → Fin p → ℝ) (hF : ∀ v w, F v w ∈ Ioo 0 1)
    (hblocks : ∀ v w i j, v < i → F v w < F i j)
    (hpriority : ∀ v w z, hamiltonPortPriority v w < hamiltonPortPriority v z → F v w < F v z)
    (hcoord : ∀ v w (hvw : v ≠ w), F v w = s (ψ.symm ⟨(v, w), hvw⟩)) (v : Fin p) :
    ∃ i j : Fin (p * (p - 1) / 2), i ≠ j ∧ E i ∩ E j = {V v} := by
  let pre := (finRotate p).symm v
  let next := finRotate p v
  have hvpre : v ≠ pre := Ne.symm (finRotate_predecessor_ne_self_of_two_le (by omega : 2 ≤ p) v)
  have hvnext : v ≠ next := Ne.symm (finRotate_ne_self_of_two_le (by omega : 2 ≤ p) v)
  let q := ψ.symm ⟨(v, pre), hvpre⟩
  let r := ψ.symm ⟨(v, next), hvnext⟩
  let i := q.1
  let j := r.1
  have hq : (ψ (i, q.2)).val = (v, pre) :=
    congrArg Subtype.val (ψ.apply_symm_apply ⟨(v, pre), hvpre⟩)
  have hr : (ψ (j, r.2)).val = (v, next) :=
    congrArg Subtype.val (ψ.apply_symm_apply ⟨(v, next), hvnext⟩)
  have hfirst := clique_port_chord_eq_matrix ψ hψ s F hcoord i q.2
  have hsecond := clique_port_chord_eq_matrix ψ hψ s F hcoord j r.2
  rw [show (ψ (i, q.2)).val.1 = v from congrArg Prod.fst hq,
    show (ψ (i, q.2)).val.2 = pre from congrArg Prod.snd hq] at hfirst
  rw [show (ψ (j, r.2)).val.1 = v from congrArg Prod.fst hr,
    show (ψ (j, r.2)).val.2 = next from congrArg Prod.snd hr] at hsecond
  have hdisj := hamilton_matrix_chords_disjoint hp F hF hblocks hpriority v
  rw [segment_symm ℝ (ee (F pre v) : ℂ) (ee (F v pre) : ℂ), ← hfirst, ← hsecond] at hdisj
  have hij : i ≠ j := by
    intro heq
    rw [heq] at hdisj
    exact disjoint_left.mp hdisj (left_mem_segment _ _ _) (left_mem_segment _ _ _)
  have hendsI := clique_port_endpoint_set ψ hψ i q.2
  have hendsJ := clique_port_endpoint_set ψ hψ j r.2
  rw [show (ψ (i, q.2)).val.1 = v from congrArg Prod.fst hq,
    show (ψ (i, q.2)).val.2 = pre from congrArg Prod.snd hq] at hendsI
  rw [show (ψ (j, r.2)).val.1 = v from congrArg Prod.fst hr,
    show (ψ (j, r.2)).val.2 = next from congrArg Prod.snd hr] at hendsJ
  have hVI : ∀ t, V t ∈ E i ↔ t ∈ ({v, pre} : Set (Fin p)) := by
    intro t
    rw [← hendsI]
    exact hEvertex i t
  have hVJ : ∀ t, V t ∈ E j ↔ t ∈ ({v, next} : Set (Fin p)) := by
    intro t
    rw [← hendsJ]
    exact hEvertex j t
  refine ⟨i, j, hij, ?_⟩
  ext x
  constructor
  · intro hx
    rcases hEinter i j hij hx with hchord | ⟨t, rfl⟩
    · exact False.elim (disjoint_left.mp hdisj hchord.1 hchord.2)
    · rcases (hVI t).mp hx.1 with htv | htpre
      · exact congrArg V htv
      · rcases (hVJ t).mp hx.2 with htv | htnext
        · exact congrArg V htv
        · exact False.elim (finRotate_predecessor_ne_successor hp v (htpre.symm.trans htnext))
  · rintro rfl
    exact ⟨(hVI v).mpr (Or.inl rfl), (hVJ v).mpr (Or.inl rfl)⟩

end GraphMinor.GM12
