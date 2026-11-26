/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.R434.TightTriangles
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! A residual packing leaves a triangle partition and a charged remainder. -/

@[expose] public section

open Finset
open scoped BigOperators

namespace GapExtremal.R434

variable {V : Type} [Fintype V] [DecidableEq V]
variable (B : SimpleGraph V) [DecidableRel B.Adj]

/-- The difference between two thirds of the edge count and the score of a piece. -/
noncomputable def pieceSlack (Q : Finset V) : ℝ :=
  2 * (e B Q : ℝ) / 3 - (w B Q : ℝ)

theorem pieceSlack_formula (Q : Finset V) :
    pieceSlack B Q = (Q.card.choose 2 : ℝ) + 1 - 4 * (e B Q : ℝ) / 3 := by
  unfold pieceSlack w
  push_cast
  ring

theorem packing_to_triangles (c : V → Fin 3) (hc : ∀ ⦃x y⦄, B.Adj x y → c x ≠ c y)
    {P : Finset (Finset V)} (hP : IsPack P) :
    ∃ (T : Finset (OrderedTriangle V)) (X : Finset (Sym2 V)),
      (∀ t ∈ T, c t.1 = 0 ∧ c t.2.1 = 1 ∧ c t.2.2 = 2) ∧
      (T : Set (OrderedTriangle V)).PairwiseDisjoint triangleEdges ∧
      X ∪ T.biUnion triangleEdges = B.edgeFinset ∧
      Disjoint X (T.biUnion triangleEdges) ∧
      (X.card : ℝ) ≤ 27 * (2 * (B.edgeFinset.card : ℝ) / 3 - ∑ Q ∈ P, (w B Q : ℝ)) := by
  classical
  let E (Q : Finset V) := (inducedOn B Q).edgeFinset
  let P' := P.filter fun Q => 2 ≤ Q.card
  let Z := P'.filter fun Q => pieceSlack B Q = 0
  let W := P'.filter fun Q => pieceSlack B Q ≠ 0
  have hP' : P' ⊆ P := filter_subset _ _
  have hZ : Z ⊆ P' := filter_subset _ _
  have hW : W ⊆ P' := filter_subset _ _
  have hE : (P : Set (Finset V)).PairwiseDisjoint E := induced_edges_disjoint_of_pack B hP
  have hEB (Q : Finset V) : E Q ⊆ B.edgeFinset := by
    intro f hf
    induction f using Sym2.inductionOn with
    | _ x y =>
      have h : B.Adj x y ∧ x ∈ Q ∧ y ∈ Q := SimpleGraph.mem_edgeFinset.mp hf
      exact SimpleGraph.mem_edgeFinset.mpr h.1
  have hs (Q : Finset V) (hQ : Q ∈ P') :
      0 ≤ pieceSlack B Q ∧
        (pieceSlack B Q = 0 → (Q.card = 3 ∧ e B Q = 3) ∨ (Q.card = 6 ∧ e B Q = 12)) ∧
        (pieceSlack B Q ≠ 0 → (e B Q : ℝ) ≤ 27 * pieceSlack B Q) := by
    rw [pieceSlack_formula]
    exact slack_of_tripartite_counts _ _ (mem_filter.mp hQ).2 (tripartite_edge_bound B c hc Q)
  have hdecomp (Q : Finset V) (hQ : Q ∈ Z) :
      ∃ T : Finset (OrderedTriangle V),
        (∀ t ∈ T, c t.1 = 0 ∧ c t.2.1 = 1 ∧ c t.2.2 = 2) ∧
        (T : Set (OrderedTriangle V)).PairwiseDisjoint triangleEdges ∧ T.biUnion triangleEdges
          = E Q := by
    obtain ⟨hQP, hz⟩ := mem_filter.mp hQ
    have hs' := (hs Q hQP).2.1 hz
    have ht : 3 * e B Q = Q.card ^ 2 := by rcases hs' with ⟨hv,he⟩ | ⟨hv,he⟩ <;> simp [hv,he]
    have hcard : Q.card / 3 ≠ 0 := by rcases hs' with ⟨hv,_⟩ | ⟨hv,_⟩ <;> simp [hv]
    let _ : NeZero (Q.card / 3) := ⟨hcard⟩
    obtain ⟨hparts, hcomplete⟩ := tight_tripartite B c hc Q ht
    refine triangulate_uniform_piece B c hc Q (Q.card / 3) (fun i => ?_) hcomplete
    have := hparts i
    omega
  let F (Q : Finset V) : Finset (OrderedTriangle V) :=
    if h : Q ∈ Z then (hdecomp Q h).choose else ∅
  have hF (Q : Finset V) (hQ : Q ∈ Z) :
      (∀ t ∈ F Q, c t.1 = 0 ∧ c t.2.1 = 1 ∧ c t.2.2 = 2) ∧
      (F Q : Set (OrderedTriangle V)).PairwiseDisjoint triangleEdges ∧
      (F Q).biUnion triangleEdges = E Q := by
    simpa only [F, dite_eq_left hQ] using (hdecomp Q hQ).choose_spec
  let T := Z.biUnion F
  let U := Z.biUnion E
  let D := P'.biUnion E
  let X := B.edgeFinset \ U
  have hUD : U ⊆ D := by
    intro f hf
    obtain ⟨Q, hQ, he⟩ := mem_biUnion.mp hf
    exact mem_biUnion.mpr ⟨Q, hZ hQ, he⟩
  have hDB : D ⊆ B.edgeFinset := by
    intro f hf
    obtain ⟨Q, _, he⟩ := mem_biUnion.mp hf
    exact hEB Q he
  have hTU : T.biUnion triangleEdges = U := by
    ext f
    simp only [T, U, mem_biUnion]
    constructor
    · rintro ⟨t, ⟨Q,hQ,ht⟩, hf⟩
      exact ⟨Q, hQ, (hF Q hQ).2.2 ▸ mem_biUnion.mpr ⟨t, ht, hf⟩⟩
    · rintro ⟨Q, hQ, hf⟩
      rw [← (hF Q hQ).2.2] at hf
      obtain ⟨t, ht, hf⟩ := mem_biUnion.mp hf
      exact ⟨t, ⟨Q,hQ,ht⟩, hf⟩
  have hdisj : (T : Set (OrderedTriangle V)).PairwiseDisjoint triangleEdges := by
    intro t ht u hu htu
    obtain ⟨Q, hQ, ht⟩ := mem_biUnion.mp ht
    obtain ⟨Q', hQ', hu⟩ := mem_biUnion.mp hu
    by_cases h : Q = Q'
    · subst Q'
      exact (hF Q hQ).2.1 ht hu htu
    · have hsub (t : OrderedTriangle V) (Q : Finset V) (hQ : Q ∈ Z) (ht : t ∈ F Q) :
          triangleEdges t ⊆ E Q :=
        fun _ he => (hF Q hQ).2.2 ▸ mem_biUnion.mpr ⟨t, ht, he⟩
      exact Disjoint.mono (hsub _ _ hQ ht) (hsub _ _ hQ' hu)
        (hE (hP' (hZ hQ)) (hP' (hZ hQ')) h)
  refine ⟨T,X,?_,hdisj,?_,?_,?_⟩
  · intro t ht
    obtain ⟨Q,hQ,ht⟩ := mem_biUnion.mp ht
    exact (hF Q hQ).1 t ht
  · rw [hTU]
    exact sdiff_union_of_subset (hUD.trans hDB)
  · rw [hTU]
    exact disjoint_sdiff_self_left
  have hD : D.card = ∑ Q ∈ P', e B Q :=
    card_biUnion (fun _ hq _ hr hn => hE (hP' hq) (hP' hr) hn)
  have hU : U.card = ∑ Q ∈ Z, e B Q :=
    card_biUnion (fun _ hq _ hr hn => hE (hP' (hZ hq)) (hP' (hZ hr)) hn)
  have hparts : (∑ Q ∈ Z, e B Q) + ∑ Q ∈ W, e B Q = ∑ Q ∈ P', e B Q :=
    sum_filter_add_sum_filter_not P' (fun Q => pieceSlack B Q = 0) (e B)
  have hX : X.card + U.card = B.edgeFinset.card := by
    have hr := card_union_of_disjoint (s := X) (t := U) disjoint_sdiff_self_left
    rw [sdiff_union_of_subset (hUD.trans hDB)] at hr
    exact hr.symm
  have hXC : (X.card : ℝ) = (B.edgeFinset.card : ℝ) - D.card + ∑ Q ∈ W, (e B Q : ℝ) := by
    have hsum : (D.card : ℝ) = U.card + ∑ Q ∈ W, (e B Q : ℝ) := by
      rw [hD,hU]
      exact_mod_cast hparts.symm
    have hcast : (X.card : ℝ) + U.card = B.edgeFinset.card := by exact_mod_cast hX
    linarith only [hsum, hcast]
  have hWsum : ∑ Q ∈ W, (e B Q : ℝ) ≤ 27 * ∑ Q ∈ P', pieceSlack B Q := by
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ Q ∈ W, 27 * pieceSlack B Q :=
        sum_le_sum fun Q hQ => (hs Q (hW hQ)).2.2 (mem_filter.mp hQ).2
      _ ≤ _ := sum_le_sum_of_subset_of_nonneg hW
        fun Q hQ _ => mul_nonneg (by norm_num) (hs Q hQ).1
  have hnon : (D.card : ℝ) ≤ B.edgeFinset.card := by exact_mod_cast card_le_card hDB
  have hscore : ∑ Q ∈ P, (w B Q : ℝ) ≤ ∑ Q ∈ P', (w B Q : ℝ) := by
    let P'' := P.filter fun Q => ¬2 ≤ Q.card
    have hsplit : (∑ Q ∈ P', (w B Q : ℝ)) + ∑ Q ∈ P'', (w B Q : ℝ) =
        ∑ Q ∈ P, (w B Q : ℝ) := sum_filter_add_sum_filter_not P _ _
    have hnonpos : ∑ Q ∈ P'', (w B Q : ℝ) ≤ 0 := by
      apply sum_nonpos
      intro Q hQ
      have hv : Q.card ≤ 1 := by
        have hh := (mem_filter.mp hQ).2
        omega
      have he0 : e B Q = 0 := by
        have hh := tripartite_edge_bound B c hc Q
        have hsq : Q.card ^ 2 ≤ 1 := by simpa using Nat.pow_le_pow_left hv 2
        omega
      have hchoose : Q.card.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [w, he0, hchoose]
    linarith only [hsplit, hnonpos]
  have hloss : ∑ Q ∈ P', pieceSlack B Q =
      2 * (D.card : ℝ) / 3 - ∑ Q ∈ P', (w B Q : ℝ) := by
    simp only [pieceSlack, sum_sub_distrib, div_eq_mul_inv, ← sum_mul, ← mul_sum]
    congr 1
    have hd : (D.card : ℝ) = ∑ Q ∈ P', (e B Q : ℝ) := by exact_mod_cast hD
    rw [hd]
  linarith only [hXC,hWsum,hnon,hscore,hloss]

end GapExtremal.R434
