/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.WallEnclosedDisc
import LeanPool.GraphMinor.GM16.WallLeftBrickLines
import LeanPool.GraphMinor.GM16.WallMiddleBrickLines
import LeanPool.GraphMinor.GM16.WallReflection
import LeanPool.GraphMinor.GM16.LineImageEmbedding
import Mathlib.Tactic.Linarith

/-!
# Common boundary lines between a brick and the outside face

Leftmost bricks have the boundary lines already constructed.
Middle bricks can meet the outside only at the top or bottom.
Reflect a rightmost brick to a leftmost one. These cases cover all
bricks and supply the remaining common-face-line geometry for
the rigidity assertion in XVI (4.2), page 53.
-/

public section
namespace GraphMinor.GM16
open Set Topology Surface

/-- Any two distinct points common to a closed brick and the outer
boundary can be joined within their intersection by a line. -/
theorem exists_line_in_brick_outer_intersection {θ i j : ℕ}
    (hθ : 4 ≤ θ) (hEven : Even θ) (hi : i + 2 < 2 * θ + 1) (hj : j + 1 < θ)
    (hParity : Even (i + j)) {a b : ℝ × ℝ} (hab : a ≠ b)
    (ha : a ∈ (Icc (i : ℝ) ((i : ℝ) + 2) ×ˢ Icc (j : ℝ) ((j : ℝ) + 1)) ∩ frontier
      (wallEnclosedSet θ))
    (hb : b ∈ (Icc (i : ℝ) ((i : ℝ) + 2) ×ˢ Icc (j : ℝ) ((j : ℝ) + 1)) ∩ frontier
      (wallEnclosedSet θ)) :
    ∃ K, IsLineWithEnds K a b ∧
      K ⊆ (Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1)) ∩ frontier (wallEnclosedSet θ) := by
  by_cases hiLeft : i ≤ 1
  · exact exists_line_in_left_brick_outer_intersection hθ hEven hiLeft hj hParity hab ha hb
  by_cases hiMiddle : i+4 ≤ 2*θ
  · exact exists_line_in_middle_brick_outer_intersection hθ hEven (by omega) hiMiddle hj hab ha hb
  let k := 2*θ-(i+2)
  have hk : k ≤ 1 := by dsimp only [k]; omega
  have hki : k+i+2=2*θ := by dsimp only [k]; omega
  have hkiReal : (k : ℝ)+(i : ℝ)+2=2*(θ : ℝ) := by exact_mod_cast hki
  have hkParity : Even (k+j) := by
    obtain ⟨t,ht⟩ := hParity
    exact ⟨θ+j-t-1,by omega⟩
  let σ := wallHorizontalReflection θ
  let B := Icc (i : ℝ) ((i : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1)
  let B' := Icc (k : ℝ) ((k : ℝ)+2) ×ˢ Icc (j : ℝ) ((j : ℝ)+1)
  have hRect : σ '' B' = B := by
    rw [wallHorizontalReflection_image_rectangle]
    rw [show 2*(θ : ℝ)-((k : ℝ)+2)=(i : ℝ) by linarith,
      show 2*(θ : ℝ)-(k : ℝ)=(i : ℝ)+2 by linarith]
  have hInter : σ '' (B' ∩ frontier (wallEnclosedSet θ)) = B ∩ frontier (wallEnclosedSet θ) := by
    rw [image_inter σ.injective,hRect,wallHorizontalReflection_frontier]
  have hSource (p : ℝ × ℝ) (hp : p ∈ B ∩ frontier (wallEnclosedSet θ)) :
      σ p ∈ B' ∩ frontier (wallEnclosedSet θ) := by
    constructor
    · change (↑k ≤ 2*(θ : ℝ)-p.1 ∧ 2*(θ : ℝ)-p.1 ≤ ↑k+2) ∧
        p.2 ∈ Icc (j : ℝ) ((j : ℝ)+1)
      exact ⟨⟨by linarith [hp.1.1.2],by linarith [hp.1.1.1]⟩,hp.1.2⟩
    · exact wallHorizontalReflection_frontier θ ▸ mem_image_of_mem σ hp.2
  obtain ⟨K,hK,hSub⟩ := exists_line_in_left_brick_outer_intersection hθ hEven hk hj hkParity
    (fun he => hab (σ.injective he)) (hSource a ha) (hSource b hb)
  refine ⟨σ '' K,?_,?_⟩
  · have hLine := isLineWithEnds_image_embedding σ.isEmbedding hK
    have haσ : σ (σ a)=a := wallHorizontalReflection_involutive θ a
    have hbσ : σ (σ b)=b := wallHorizontalReflection_involutive θ b
    rw [haσ,hbσ] at hLine
    exact hLine
  · rw [← hInter]
    exact image_mono hSub

end GraphMinor.GM16
