/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.IntegerLaplacianCastBridge
public import LeanPool.ApollonianSuperharmonic.IntegerSuperharmonicRepresentative
public import LeanPool.ApollonianSuperharmonic.PSDQuadraticIntegerApproximation
public import LeanPool.ApollonianSuperharmonic.QuadraticGrowthAtInfinity
public import LeanPool.ApollonianSuperharmonic.RealLaplacianLinearity

-- [TABLET NODE: SuperharmonicDownwardClosure]

/-!
# SuperharmonicDownwardClosure

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem SuperharmonicDownwardClosure
    (A B : Matrix (Fin 2) (Fin 2) Real) (hA : A.IsSymm)
    (hB : exists f : IntegerLatticeFunction,
      IntegerSuperharmonicRepresentative B f)
    (hgap : (B - A).PosSemidef) :
    exists g : IntegerLatticeFunction,
      IntegerSuperharmonicRepresentative A g := by
-- BODY
  obtain ⟨f, hf⟩ := hB
  have hDsymm : (B - A).IsSymm := by
    change (B - A).transpose = B - A
    simpa [Matrix.IsHermitian] using hgap.1
  obtain ⟨d, hd₁, hd₂, hd₃, hd₄, hd₅⟩ :=
    PSDQuadraticIntegerApproximation (B - A) hDsymm hgap
  let g : IntegerLatticeFunction := fun x => f x - d x
  refine ⟨g, ?_⟩
  refine ⟨hA, ?_, ?_⟩
  · intro ε hε
    have hhalf : 0 < ε / 2 := by linarith
    obtain ⟨R, hR⟩ := hf.2.1 (ε / 2) hhalf
    refine ⟨max R (max (32 / ε ^ 2) (8 / ε)), ?_⟩
    intro x hx
    have ht : 0 ≤ (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 := by positivity
    have hR' : R ≤ (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 :=
      le_trans (le_max_left _ _) hx
    have hlarge : 32 / ε ^ 2 ≤ (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
    have hlarge' : 8 / ε ≤ (x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2 :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    have hre : |(x.re : ℝ)| ^ 2 = (x.re : ℝ) ^ 2 := by rw [sq_abs]
    have him : |(x.im : ℝ)| ^ 2 = (x.im : ℝ) ^ 2 := by rw [sq_abs]
    have hsquare : (|(x.re : ℝ)| + |(x.im : ℝ)|) ^ 2 ≤
        2 * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) := by
      nlinarith [sq_nonneg (|(x.re : ℝ)| - |(x.im : ℝ)|)]
    have habs : ((abs x.re + abs x.im : Int) : ℝ) =
        |(x.re : ℝ)| + |(x.im : ℝ)| := by simp [Int.cast_add, Int.cast_abs]
    have hlin : ((abs x.re + abs x.im : Int) : ℝ) + 1 ≤
        (ε / 2) * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) := by
      rw [habs]
      have hprod : 32 ≤ ε ^ 2 * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) := by
        apply (div_le_iff₀ (sq_pos_of_pos hε)).mp at hlarge
        nlinarith
      have hprod' : 8 ≤ ε * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) := by
        apply (div_le_iff₀ hε).mp at hlarge'
        nlinarith
      have hmul := mul_le_mul_of_nonneg_right hprod ht
      have hsquare' := mul_le_mul_of_nonneg_left hsquare (by norm_num : (0 : ℝ) ≤ 16)
      have hsum : |(x.re : ℝ)| + |(x.im : ℝ)| ≤
          ε * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) / 4 := by
        nlinarith [sq_nonneg (ε * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) -
          4 * (|(x.re : ℝ)| + |(x.im : ℝ)|))]
      nlinarith
    have hfd : |(f x : ℝ) - LatticeQuadraticForm B x| ≤
        (ε / 2) * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) := hR x hR'
    have hdl : LatticeQuadraticForm (B - A) x -
        ((abs x.re + abs x.im : Int) : ℝ) - 1 ≤ (d x : ℝ) := (hd₄ x).1
    have hdu : (d x : ℝ) ≤ LatticeQuadraticForm (B - A) x +
        ((abs x.re + abs x.im : Int) : ℝ) + 1 := (hd₄ x).2
    have hquad : LatticeQuadraticForm B x - LatticeQuadraticForm (B - A) x =
        LatticeQuadraticForm A x := by
      simp [LatticeQuadraticForm, Matrix.sub_mulVec]
      ring
    rw [show (g x : ℝ) = (f x : ℝ) - (d x : ℝ) by simp [g], ← hquad]
    have hdiff : |(d x : ℝ) - LatticeQuadraticForm (B - A) x| ≤
        ((abs x.re + abs x.im : Int) : ℝ) + 1 := by
      rw [abs_le]
      constructor <;> linarith
    calc
      |(f x : ℝ) - (d x : ℝ) -
          (LatticeQuadraticForm B x - LatticeQuadraticForm (B - A) x)| =
          |((f x : ℝ) - LatticeQuadraticForm B x) -
            ((d x : ℝ) - LatticeQuadraticForm (B - A) x)| := by
              congr 1; ring
      _ ≤ |(f x : ℝ) - LatticeQuadraticForm B x| +
          |(d x : ℝ) - LatticeQuadraticForm (B - A) x| := abs_sub _ _
      _ ≤ (ε / 2) * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) +
          (((abs x.re + abs x.im : Int) : ℝ) + 1) :=
            add_le_add hfd hdiff
      _ ≤ ε * ((x.re : ℝ) ^ 2 + (x.im : ℝ) ^ 2) := by nlinarith [hlin]
  · intro x
    have hfl := hf.2.2 x
    have hdl := hd₅ x
    change FourNeighborLaplacian (fun y => f y - d y) x ≤ 1
    have hident : FourNeighborLaplacian (fun y => f y - d y) x =
        FourNeighborLaplacian f x - FourNeighborLaplacian d x := by
      simp only [FourNeighborLaplacian]
      ring
    rw [hident]
    linarith

end ApollonianSuperharmonic

end
