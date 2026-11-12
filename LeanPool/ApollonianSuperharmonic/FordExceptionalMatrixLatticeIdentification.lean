/-
Copyright (c) 2026 Wesley Pegden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wesley Pegden
-/
module

public import LeanPool.ApollonianSuperharmonic.CircleMatrix
public import LeanPool.ApollonianSuperharmonic.FordCoordinateConfiguration
public import LeanPool.ApollonianSuperharmonic.FordExceptionalLattice
public import LeanPool.ApollonianSuperharmonic.FordPeakMatrix
public import LeanPool.ApollonianSuperharmonic.IntegralityLattice

-- [TABLET NODE: FordExceptionalMatrixLatticeIdentification]

/-!
# FordExceptionalMatrixLatticeIdentification

Adapted from Wesley Pegden’s Apache-2.0 Trellis formalization of Levine–Pegden–Smart.
Changes: pool module paths, public exports, project namespace and current Mathlib compatibility.
-/

@[expose] public section

namespace ApollonianSuperharmonic

theorem FordExceptionalMatrixLatticeIdentification (P : FordFareyParameter)
    (C : BandCircle) (hC : C.1.1 = FordCircleCoordinate P.p P.q) :
    CircleMatrix C = FordPeakMatrix P.p P.q P.q_pos P.reduced ∧
      IntegralityLattice C = FordExceptionalLattice P := by
-- BODY
  have hmatrix :
      CircleMatrix C =
        let c : ℝ := C.1.1.1
        let x : ℝ := C.1.1.2.re
        let y : ℝ := C.1.1.2.im
        (2 * c)⁻¹ • ![![1 + x, y], ![y, 1 - x]] := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [CircleMatrix, BandCircleEuclideanData]
    all_goals field_simp
  constructor
  · rw [FordPeakMatrix]
    apply Matrix.ext
    intro i j
    fin_cases i <;> fin_cases j
    all_goals change _ = (1 / ((P.q : ℝ) ^ 2)) * _
    all_goals simp [hmatrix, hC, FordCircleCoordinate]
    all_goals field_simp
    all_goals ring
  · apply le_antisymm
    · intro u hu
      change ∀ i : Fin 2, ∃ n : ℤ, Matrix.mulVec (CircleMatrix C)
        ![((u.re : ℤ) : ℝ), ((u.im : ℤ) : ℝ)] i = (n : ℝ) at hu
      have hzero := hu 0
      have hone := hu 1
      simp? [hmatrix, hC, FordCircleCoordinate, Matrix.mulVec,
        ] at hzero hone
      rcases hzero with ⟨zeroValue, zeroEquation⟩
      rcases hone with ⟨oneValue, oneEquation⟩
      rw [GaussianInt.toComplex_def₂] at zeroEquation oneEquation
      field_simp at zeroEquation oneEquation
      have qReal : (P.q : ℝ) ≠ 0 := by exact_mod_cast P.q_pos.ne'
      have oneProduct := (div_eq_iff qReal).mp oneEquation
      have oneInteger : u.re * P.p = oneValue * (P.q : ℤ) := by
        exact_mod_cast oneProduct
      have qdividesReal : (P.q : ℤ) ∣ u.re := by
        refine ⟨P.p₁ * u.re - (P.q₁ : ℤ) * oneValue, ?_⟩
        calc
          u.re = (P.p₁ * (P.q : ℤ) - (P.q₁ : ℤ) * P.p) * u.re := by
            have determinant : P.p₁ * (P.q : ℤ) - (P.q₁ : ℤ) * P.p = 1 := P.det₁
            rw [determinant]
            ring
          _ = P.p₁ * ((P.q : ℤ) * u.re) - (P.q₁ : ℤ) * (P.p * u.re) := by ring
          _ = P.p₁ * ((P.q : ℤ) * u.re) - (P.q₁ : ℤ) * (u.re * P.p) := by ring
          _ = P.p₁ * ((P.q : ℤ) * u.re) - (P.q₁ : ℤ) * (u.re * P.p) := by ring
          _ = (P.q : ℤ) * (P.p₁ * u.re - (P.q₁ : ℤ) * oneValue) := by
            rw [oneInteger]
            ring
      rcases qdividesReal with ⟨integerPart, integerEquation⟩
      have qSquare : (P.q : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 qReal
      have zeroProduct := (div_eq_iff qSquare).mp zeroEquation
      have zeroCleanReal : (u.re : ℝ) + (P.p : ℝ) * (P.q : ℝ) * u.im =
          (zeroValue : ℝ) * (P.q : ℝ) ^ 2 := by
        linarith [zeroProduct]
      have zeroClean : u.re + P.p * (P.q : ℤ) * u.im =
          zeroValue * (P.q : ℤ) ^ 2 := by
        exact_mod_cast zeroCleanReal
      have reducedEquation : integerPart + P.p * u.im =
          zeroValue * (P.q : ℤ) := by
        apply (mul_left_cancel₀ (by exact_mod_cast P.q_pos.ne' : (P.q : ℤ) ≠ 0))
        calc
          (P.q : ℤ) * (integerPart + P.p * u.im) =
              u.re + P.p * (P.q : ℤ) * u.im := by rw [integerEquation]; ring
          _ = zeroValue * (P.q : ℤ) ^ 2 := zeroClean
          _ = (P.q : ℤ) * (zeroValue * (P.q : ℤ)) := by ring
      have secondDivides : (P.q : ℤ) ∣ (P.q₁ : ℤ) * integerPart - u.im := by
        refine ⟨(P.q₁ : ℤ) * zeroValue - P.p₁ * u.im, ?_⟩
        calc
          (P.q₁ : ℤ) * integerPart - u.im =
              (P.q₁ : ℤ) * (integerPart + P.p * u.im) -
                (P.p * (P.q₁ : ℤ) + 1) * u.im := by ring
          _ = (P.q₁ : ℤ) * (zeroValue * (P.q : ℤ)) -
                (P.p₁ * (P.q : ℤ)) * u.im := by
            rw [reducedEquation]
            congr 1
            calc
              (P.p * (P.q₁ : ℤ) + 1) * u.im =
                  (P.p * (P.q₁ : ℤ) + 1) * u.im := rfl
              _ = (P.p₁ * (P.q : ℤ)) * u.im := by
                have determinant : P.p₁ * (P.q : ℤ) - (P.q₁ : ℤ) * P.p = 1 := P.det₁
                have relation : P.p * (P.q₁ : ℤ) + 1 = P.p₁ * (P.q : ℤ) := by
                  linarith [determinant]
                rw [relation]
          _ = (P.q : ℤ) * ((P.q₁ : ℤ) * zeroValue - P.p₁ * u.im) := by ring
      rcases secondDivides with ⟨secondPart, secondEquation⟩
      have generatorOne : (⟨(P.q : ℤ), (P.q₁ : ℤ)⟩ : GaussianInt) ∈
          FordExceptionalLattice P := AddSubgroup.subset_closure (by simp)
      have generatorTwo : (⟨0, -(P.q : ℤ)⟩ : GaussianInt) ∈
          FordExceptionalLattice P := AddSubgroup.subset_closure (by simp)
      have combination : u = integerPart • (⟨(P.q : ℤ), (P.q₁ : ℤ)⟩ : GaussianInt) +
          secondPart • (⟨0, -(P.q : ℤ)⟩ : GaussianInt) := by
        ext
        · simp [integerEquation]
          ring
        · simp
          linarith [secondEquation]
      rw [combination]
      exact (FordExceptionalLattice P).add_mem
        ((FordExceptionalLattice P).zsmul_mem generatorOne integerPart)
        ((FordExceptionalLattice P).zsmul_mem generatorTwo secondPart)
    · rw [FordExceptionalLattice, AddSubgroup.closure_le]
      intro u hu
      rcases hu with (rfl | rfl)
      · change ∀ i : Fin 2, ∃ n : ℤ, _
        intro i
        fin_cases i
        · refine ⟨-P.p, ?_⟩
          simp [hmatrix, hC, FordCircleCoordinate, Matrix.mulVec,
            ]
          field_simp [show (P.q : ℝ) ≠ 0 by exact_mod_cast P.q_pos.ne']
        · refine ⟨0, ?_⟩
          simp [hmatrix, hC, FordCircleCoordinate, Matrix.mulVec,
            ]
      · change ∀ i : Fin 2, ∃ n : ℤ, _
        intro i
        fin_cases i
        · refine ⟨P.p₁, ?_⟩
          simp [hmatrix, hC, FordCircleCoordinate, Matrix.mulVec,
            ]
          field_simp [show (P.q : ℝ) ≠ 0 by exact_mod_cast P.q_pos.ne']
          have relation : P.p * (P.q₁ : ℤ) + 1 = P.p₁ * (P.q : ℤ) := by
            linarith [P.det₁]
          have relationReal : (P.p : ℝ) * (P.q₁ : ℝ) + 1 =
              (P.p₁ : ℝ) * (P.q : ℝ) := by exact_mod_cast relation
          nlinarith [relationReal]
        · refine ⟨P.p, ?_⟩
          simp [hmatrix, hC, FordCircleCoordinate, Matrix.mulVec,
            ]
          field_simp [show (P.q : ℝ) ≠ 0 by exact_mod_cast P.q_pos.ne']

end ApollonianSuperharmonic

end
