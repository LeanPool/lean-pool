/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import Mathlib.Init

public import LeanPool.ApollonianSuperharmonic.P5442T1WebGeometry
public import LeanPool.ApollonianSuperharmonic.P4062T1ParentalRestriction
public import LeanPool.ApollonianSuperharmonic.P4062T1RemainderGeometry
public import Mathlib.Algebra.Order.Ring.Star

-- [TABLET NODE: P5442T1LaplacianBound]

/-!
# P5442T1LaplacianBound

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem P5442T1LaplacianBound (P : FordFareyParameter) :
    ∀ x, FourNeighborLaplacian (FordOdometer P) x ≤ 1 := by
-- BODY
  classical
  have coords (q : Nat) (x : GaussianInt) :
      x ∈ P4062T1InteriorSquare q ↔
        1 ≤ x.re ∧ x.re ≤ (q : Int) - 1 ∧
        1 ≤ x.im ∧ x.im ≤ (q : Int) - 1 := by
    constructor
    · intro hx
      obtain ⟨⟨a, b⟩, hab, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
      exact ⟨(Finset.mem_Icc.mp ha).1, (Finset.mem_Icc.mp ha).2,
        (Finset.mem_Icc.mp hb).1, (Finset.mem_Icc.mp hb).2⟩
    · intro hx
      exact Finset.mem_image.mpr ⟨(x.re, x.im), Finset.mem_product.mpr
        ⟨Finset.mem_Icc.mpr ⟨hx.1, hx.2.1⟩,
          Finset.mem_Icc.mpr hx.2.2⟩, by cases x; rfl⟩
  have main : ∀ n, ∀ P : FordFareyParameter, P.q = n →
      ∀ x, FourNeighborLaplacian (FordOdometer P) x ≤ 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro P hn x
      obtain ⟨hp, hw, _, ho⟩ := P5442T1WebGeometry P
      let t : Int → Int → GaussianInt := fun m n =>
        ⟨n * (P.q : Int), n * (P.q₁ : Int) - m * (P.q : Int)⟩
      let W : Set GaussianInt := {x | ∃ m n : Int,
        x - t m n ∈ LatticeVertexBoundary (FordVertexDomain P.q)}
      change (∀ x ∈ W, FourNeighborLaplacian (FordOdometer P) x = 1) at hw
      by_cases hx : x ∈ W
      · exact le_of_eq (hw x hx)
      obtain ⟨m, k, ho⟩ := ho x hx
      let y := x - t m k
      have hy : y ∈ P4062T1InteriorSquare P.q := ho x .refl
      have he : FourNeighborLaplacian (FordOdometer P) x =
          FourNeighborLaplacian (FordOdometer P) y := by
        have he := (hp m k).2 y
        simpa only [y, t, sub_add_cancel] using he
      rw [he]
      have hyc := (coords P.q y).mp hy
      by_cases h1 : P.q = 1
      · omega
      by_cases h2 : P.q = 2
      · have hab : P.q₁ = 1 ∧ P.q₂ = 1 := by
          have hs := P.sum_q
          have ht := P.q₁_lt
          have hd := P.det₁
          rw [h2] at hs ht hd
          by_cases hz : P.q₁ = 0
          · rw [hz] at hd
            norm_num at hd
            omega
          · constructor <;> omega
        have hyeq : y = (⟨1, 1⟩ : GaussianInt) := by ext <;> dsimp <;> omega
        have hm : FordBoundaryMultiplicity P y = 4 := by
          rw [hyeq]
          unfold FordBoundaryMultiplicity
          have hb : ∀ i : Fin 4,
              (⟨1, 1⟩ : GaussianInt) ∈
                LatticeVertexBoundary (FordRecursiveVertexDomains P i) := by
            intro i
            fin_cases i
            · refine ⟨?_, ⟨⟨2, 1⟩, ?_, ?_, ?_⟩⟩
              all_goals norm_num [FordRecursiveVertexDomains, hab.1, hab.2, h2]
            · refine ⟨?_, ⟨⟨0, 1⟩, ?_, ?_, ?_⟩⟩
              all_goals norm_num [FordRecursiveVertexDomains, hab.1, hab.2, h2]
            · refine ⟨?_, ⟨⟨1, 2⟩, ?_, ?_, ?_⟩⟩
              all_goals norm_num [FordRecursiveVertexDomains, hab.1, hab.2, h2]
            · refine ⟨?_, ⟨⟨1, 0⟩, ?_, ?_, ?_⟩⟩
              all_goals norm_num [FordRecursiveVertexDomains, hab.1, hab.2, h2]
          simp only [Finset.filter_true_of_mem (fun i _ => hb i), Finset.card_univ,
            Fintype.card_fin]
        have ht := (FordLaplacianTable P).2.2 (by omega) y
          hyc.1 hyc.2.1 hyc.2.2.1 hyc.2.2.2
        rw [ht.2.2 hm]
        norm_num
      have hbig : 2 < P.q := by have := P.q_pos; omega
      obtain ⟨A, B, _, _, _, _, hA, hB, _, restrictions⟩ :=
        P4062T1ParentalRestriction P hbig
      let E := (P4062T1RecursiveInteriors P 0 ∪ P4062T1RecursiveInteriors P 1) ∪
        (P4062T1RecursiveInteriors P 2 ∪ P4062T1RecursiveInteriors P 3)
      by_cases hyE : y ∈ E
      · have select : ∃ i : Fin 4, y ∈ P4062T1RecursiveInteriors P i := by
          rcases Finset.mem_union.mp hyE with h | h
          · rcases Finset.mem_union.mp h with h | h
            · exact ⟨0, h⟩
            · exact ⟨1, h⟩
          · rcases Finset.mem_union.mp h with h | h
            · exact ⟨2, h⟩
            · exact ⟨3, h⟩
        obtain ⟨i, hi⟩ := select
        rw [(restrictions i).2 y hi]
        apply ih (if i.val < 2 then A else B).q
          (by split_ifs <;> omega) (if i.val < 2 then A else B) rfl
      · have rem := P4062T1RemainderGeometry P hbig
        obtain ⟨_, hW, _, _, _, hmult, _, _⟩ := rem
        have hyW : y ∈ P4062T1InteriorSquare P.q \ E :=
          Finset.mem_sdiff.mpr ⟨hy, hyE⟩
        rw [hW] at hyW
        have hj : ∃ j : Fin 2, y ∈ (P4062T1RemainderPaths P j).1 := by
          rcases Finset.mem_union.mp hyW with h | h
          · exact ⟨0, h⟩
          · exact ⟨1, h⟩
        obtain ⟨j, hj⟩ := hj
        have hm := (hmult j y hj).2.1
        have ht := (FordLaplacianTable P).2.2 (by omega) y
          hyc.1 hyc.2.1 hyc.2.2.1 hyc.2.2.2
        by_cases hr : y = (P4062T1RemainderPaths P j).2
        · rw [ite_eq_left hr] at hm
          rw [ht.2.1 hm]
          norm_num
        · rw [ite_eq_right hr] at hm
          exact le_of_eq (ht.1 hm)
  exact main P.q P rfl

end ApollonianSuperharmonic

end
