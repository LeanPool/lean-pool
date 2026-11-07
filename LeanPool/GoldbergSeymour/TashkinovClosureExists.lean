/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Data.Finset.Max
public import LeanPool.GoldbergSeymour.TashkinovClosure
public import Mathlib.Data.Fintype.Card

/-!
# Tashkinov Closure Exists

Part of the dependency closure of the Goldberg–Seymour edge-colouring theorem.
Adapted from Wesley Pegden’s Trellis formalization at
88d98c1d1a59d1f1bf7c4eb58e73f3945f6daf12; module paths and namespace changed.
-/

@[expose] public section

namespace GoldbergSeymour

theorem TashkinovClosureExists {V E : Type*} [Fintype V] [Fintype E]
    {G : LooplessMultigraph V E} {k : ℕ} {e0 : E}
    (phi : PartialEdgeColoring E k) (T : TreeSequence G e0) :
    ∃ T' : TreeSequence G e0, TashkinovClosure phi T T' := by
  classical
  have length_bound : ∀ S : TreeSequence G e0, S.length ≤ Fintype.card V := by
    intro S
    have h := Fintype.card_le_of_injective S.vertex S.vertex_injective
    have h' : S.length + 1 ≤ Fintype.card V := by simpa using h
    omega
  let lengths : Finset ℕ := (Finset.range (Fintype.card V + 1)).filter
    (fun n => ∃ S : TreeSequence G e0,
      TashkinovAugmentationSequence phi T S ∧ S.length = n)
  have lengths_nonempty : lengths.Nonempty := by
    have hT : T.length ≤ Fintype.card V := length_bound T
    refine ⟨T.length, ?_⟩
    simp only [lengths, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_of_le hT, ⟨T, Relation.ReflTransGen.refl, rfl⟩⟩
  let largest : ℕ := lengths.max' lengths_nonempty
  have largest_mem : largest ∈ lengths := by
    exact Finset.max'_mem lengths lengths_nonempty
  obtain ⟨S, hreach, hlength⟩ := (Finset.mem_filter.mp largest_mem).2
  have hclosed : ColoredVertexSetClosed G phi (TreeSequenceVertexSet S) := by
    by_contra hnot
    unfold ColoredVertexSetClosed at hnot
    push Not at hnot
    obtain ⟨f, c, z, hf, hz, hfc, hcz⟩ := hnot
    simp only [BoundaryEdges, Finset.mem_filter, Finset.mem_univ, true_and] at hf
    obtain ⟨x, hx, y, hy, hxy⟩ := hf
    have vertex_mem : ∀ i : Fin (S.length + 1),
        S.vertex i ∈ TreeSequenceVertexSet S := by
      intro i
      simp [TreeSequenceVertexSet]
    have edge_new : ∀ i : Fin S.length, f ≠ S.edge i := by
      intro i he
      obtain ⟨q, hq⟩ := S.attaches i
      have hyend : y ∈ G.ends (S.edge i) := by
        rw [← he, hxy]
        exact Sym2.mem_iff.mpr (Or.inr rfl)
      rw [hq] at hyend
      rcases Sym2.mem_iff.mp hyend with hqv | hqv
      · exact hy (by simpa [← hqv] using vertex_mem i.succ)
      · exact hy (by simpa [← hqv] using vertex_mem (Fin.castLT q (by omega)))
    let U : TreeSequence G e0 :=
      { length := S.length + 1
        positive := by omega
        vertex := Fin.lastCases y (fun i => S.vertex i)
        edge := Fin.lastCases f (fun i => S.edge i)
        vertex_injective := by
          intro i j
          revert j
          refine Fin.lastCases ?_ (fun i => ?_) i
          · intro j
            refine Fin.lastCases ?_ (fun j => ?_) j
            · intro hij
              apply Fin.ext
              rfl
            · intro hij
              dsimp only [Fin.lastCases] at hij
              rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at hij
              have heq : y = S.vertex j := by
                exact hij
              exact (hy (heq ▸ vertex_mem j)).elim
          · intro j
            refine Fin.lastCases ?_ (fun j => ?_) j
            · intro hij
              dsimp only [Fin.lastCases] at hij
              rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_last] at hij
              have heq : S.vertex i = y := by
                exact hij
              exact (hy (heq ▸ vertex_mem i)).elim
            · intro hij
              dsimp only [Fin.lastCases] at hij
              rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_castSucc] at hij
              exact congrArg Fin.castSucc (S.vertex_injective hij)
        edge_injective := by
          intro i j
          revert j
          refine Fin.lastCases ?_ (fun i => ?_) i
          · intro j
            refine Fin.lastCases ?_ (fun j => ?_) j
            · intro hij
              apply Fin.ext
              rfl
            · intro hij
              dsimp only [Fin.lastCases] at hij
              rw [Fin.reverseInduction_last, Fin.reverseInduction_castSucc] at hij
              exact False.elim (edge_new j hij)
          · intro j
            refine Fin.lastCases ?_ (fun j => ?_) j
            · intro hij
              dsimp only [Fin.lastCases] at hij
              rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_last] at hij
              exact False.elim (edge_new i hij.symm)
            · intro hij
              dsimp only [Fin.lastCases] at hij
              rw [Fin.reverseInduction_castSucc, Fin.reverseInduction_castSucc] at hij
              exact congrArg Fin.castSucc (S.edge_injective hij)
        first_edge := by
          have hzero : (⟨0, Nat.succ_pos _⟩ : Fin (S.length + 1)) =
              (⟨0, S.positive⟩ : Fin S.length).castSucc := by rfl
          rw [hzero]
          simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
          exact S.first_edge
        attaches := by
          intro j
          by_cases hj : j = Fin.last S.length
          · subst j
            obtain ⟨i, hi⟩ := by
              simpa [TreeSequenceVertexSet] using hx
            refine ⟨i, ?_⟩
            have hc : (Fin.castLT i (by omega) : Fin (S.length + 1 + 1)) = i.castSucc := by
              apply Fin.ext
              rfl
            rw [hc]
            simp only [Fin.lastCases_last, Fin.succ_last, Nat.succ_eq_add_one,
                Fin.lastCases_castSucc]
            rw [← hi] at hxy
            rw [hxy]
            exact (Sym2.eq_iff).2 (Or.inr ⟨rfl, rfl⟩)
          · have hjle : j.val ≤ S.length := Nat.lt_succ_iff.mp j.isLt
            have hjne : j.val ≠ S.length := by
              intro he
              apply hj
              apply Fin.ext
              simpa using he
            have hj' : j.val < S.length := Nat.lt_of_le_of_ne hjle hjne
            obtain ⟨i, hi⟩ := S.attaches (j.castPred hj)
            have hjform : j = (j.castPred hj).castSucc := by
              apply Fin.ext
              rfl
            have hji : (j.castPred hj).val + 1 ≤ j.val + 1 := by
              rw [show (j.castPred hj).val = j.val by rfl]
            refine ⟨Fin.castLE hji i, ?_⟩
            convert hi using 1
            · apply congrArg G.ends
              conv_lhs => rw [hjform]
              simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
            · apply (Sym2.eq_iff).2
              left
              constructor
              · have hjs : j.succ = (j.castPred hj).succ.castSucc := by
                  apply Fin.ext
                  rfl
                rw [hjs]
                simp only [Fin.lastCases, Fin.reverseInduction_castSucc]
              · have ibound : i.val < S.length + 1 := by omega
                have hq :
                    (Fin.castLE hji i).castLT (by omega) =
                      (i.castLT ibound).castSucc := by
                  apply Fin.ext
                  rfl
                rw [hq]
                simp only [Fin.lastCases, Fin.reverseInduction_castSucc] }
    have hstep : TashkinovAugmentation phi S U := by
      refine ⟨by simp [U], ?_, c, ?_, ?_⟩
      · refine ⟨Nat.le_succ _, ?_, ?_⟩
        · intro i
          dsimp [U]
          have hc : Fin.castLE (Nat.succ_le_succ (Nat.le_succ S.length)) i = i.castSucc := by
            apply Fin.ext
            rfl
          rw [hc]
          simp [Fin.lastCases, Fin.reverseInduction_castSucc]
        · intro j
          have hc : Fin.castLE (Nat.le_succ S.length) j = j.castSucc := by
            apply Fin.ext
            rfl
          rw [hc]
          simp [U, Fin.lastCases, Fin.reverseInduction_castSucc]
      · simpa [U, Fin.lastCases] using hfc
      · exact Finset.mem_biUnion.mpr ⟨z, hz, hcz⟩
    have hnew : TashkinovAugmentationSequence phi T U := hreach.tail hstep
    have hUmem : largest + 1 ∈ lengths := by
      apply Finset.mem_filter.mpr
      constructor
      · have hu := length_bound U
        have hu' : S.length + 1 ≤ Fintype.card V := by simpa [U] using hu
        simpa [hlength] using Nat.lt_succ_of_le hu'
      · refine ⟨U, hnew, ?_⟩
        simp [U, hlength]
    have hle := Finset.le_max' lengths (largest + 1) hUmem
    omega
  exact ⟨S, hreach, hclosed⟩

end GoldbergSeymour

end
