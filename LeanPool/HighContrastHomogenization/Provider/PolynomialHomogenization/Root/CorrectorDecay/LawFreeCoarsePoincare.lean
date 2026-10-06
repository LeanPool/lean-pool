/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.PrintOrderJointTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteLipschitzCoreBase
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarsePoincare
public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.SobolevPublic

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.LawFreeCoarsePoincare

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open FiniteLipschitzCoreInternal

noncomputable section

private theorem poincareUpperEllipticityFactor_le_of_weakError_le_one
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d}
    {s : ℝ} (hs : 0 < s) {k : ℤ}
    (herror : scalarIdentityWeakError a s k ≤ 1) :
    Book.Ch03.poincareUpperEllipticityFactor
        (originCube d k) a s (.finite 2) ≤
      Real.sqrt (4 * (d : ℝ)) := by
  let E := scalarIdentityWeakError a s k
  have hE : 0 ≤ E := scalarIdentityWeakError_nonneg a s k
  have hEsq : E ^ 2 + 1 ≤ 2 := by
    dsimp only [E] at hE ⊢
    nlinarith only [hE, herror]
  have hraw :=
    Book.Ch02.inv_mul_LambdaSq_finite_two_le_card_mul_homogenizationError_sq_add_one
      (originCube d k) a hs (by norm_num : (0 : ℝ) < 1)
  have hLambda :
      Book.Ch02.LambdaSq (originCube d k) s (.finite 2) a ≤
        2 * (d : ℝ) * (E ^ 2 + 1) := by
    simpa [E, scalarIdentityWeakError, scalarMatrix] using hraw
  have hLambda' :
      Book.Ch02.LambdaSq (originCube d k) s (.finite 2) a ≤
        4 * (d : ℝ) := by
    calc
      _ ≤ 2 * (d : ℝ) * (E ^ 2 + 1) := hLambda
      _ ≤ 2 * (d : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left hEsq (by positivity)
      _ = 4 * (d : ℝ) := by ring
  simpa only [Book.Ch03.poincareUpperEllipticityFactor,
    Real.sqrt_eq_rpow] using! Real.sqrt_le_sqrt hLambda'

/-- At a scalar-identity good scale, the coarse-Poincare gradient and flux
rows have a dimension/order-only energy bound.  In particular, neither
microscopic ellipticity constant enters the multiplier. -/
theorem exists_lawFreeCoarsePoincareRowsConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (k : ℤ)
        (u : Book.Ch03.CubeSolution (originCube d k) a),
        scalarIdentityWeakError a s k ≤ 1 →
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo
              (originCube d k) s u.toH1.grad ≤
            C * Book.Ch03.h1EnergyNormOnCube
              (originCube d k) a u.toH1 ∧
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo
              (originCube d k) s
              (fun x ↦ matVecMul
                (Book.Ch03.publicCoeffField (originCube d k) a x)
                (u.toH1.grad x)) ≤
            C * Book.Ch03.h1EnergyNormOnCube
              (originCube d k) a u.toH1 := by
  let K : ℝ := (d : ℝ) * Real.rpow 3 ((d : ℝ) + s)
  let B : ℝ := Book.Ch03.poincareDiscountFactor s (.finite 2)
  let L : ℝ := Real.sqrt (4 * (d : ℝ))
  let C : ℝ := 1 + K * B * L
  have hK : 0 ≤ K := by
    exact mul_nonneg (Nat.cast_nonneg d) (Real.rpow_nonneg (by norm_num) _)
  have hB : 0 ≤ B := by
    dsimp only [B, Book.Ch03.poincareDiscountFactor]
    exact Real.rpow_nonneg
      (Book.Ch02.book_geometricDiscount_pos (mul_pos hs (by norm_num))).le _
  have hL : 0 ≤ L := Real.sqrt_nonneg _
  have hC : 0 < C := by
    dsimp only [C]
    exact add_pos_of_pos_of_nonneg zero_lt_one
      (mul_nonneg (mul_nonneg hK hB) hL)
  refine ⟨C, hC, ?_⟩
  intro a k u herror
  let Q := originCube d k
  let D := Book.Ch03.h1EnergyNormOnCube Q a u.toH1
  have hD : 0 ≤ D := by
    dsimp only [D, Book.Ch03.h1EnergyNormOnCube]
    exact Real.sqrt_nonneg _
  have hgradMem : MemVectorL2 (cubeSet Q) u.toH1.grad := by
    simpa [Q, Book.Ch03.publicH1ToCubeSet_grad] using
      (Book.Ch03.publicH1ToCubeSet u.toH1).grad_memVectorL2
  have hfluxMem : MemVectorL2 (cubeSet Q)
      (fun x ↦ matVecMul (Book.Ch03.publicCoeffField Q a x)
        (u.toH1.grad x)) := by
    exact memVectorL2_matVecMul_of_isEllipticFieldOn
      (Book.Ch03.publicCoeffField_isEllipticFieldOn_cubeSet Q a) hgradMem
  have hnoteGrad :=
    Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo_le_note_constant_mul_cubeBesovNegativeVectorSeminormTwo
      Q s u.toH1.grad hs hgradMem
  have hnoteFlux :=
    Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo_le_note_constant_mul_cubeBesovNegativeVectorSeminormTwo
      Q s (fun x ↦ matVecMul (Book.Ch03.publicCoeffField Q a x)
        (u.toH1.grad x)) hs hfluxMem
  rw [Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo,
    Book.Ch03.publicDualBesovScaleWeight_eq_cubeBesovScaleWeight] at hnoteGrad
  rw [Book.Ch03.scaleNormalizedDualNegativeBesovVectorNormTwo,
    Book.Ch03.publicDualBesovScaleWeight_eq_cubeBesovScaleWeight] at hnoteFlux
  have hgradRaw := Book.Ch03.coarsePoincareGradient_negativeBesov_le
    Q a u hs (q := .finite 2) (by norm_num)
  have hfluxRaw := Book.Ch03.coarsePoincareFlux_negativeBesov_le
    Q a u hs (q := .finite 2) (by norm_num)
  have hlower : Book.Ch03.poincareLowerEllipticityFactor
      Q a s (.finite 2) ≤ L := by
    rw [poincareLowerEllipticityFactor_finite_two_eq_sqrt_inv]
    exact Real.sqrt_le_sqrt (by
      simpa only [Q, L] using
        scalarIdentityWeakError_le_one_lowerEllipticity hs herror)
  have hupper : Book.Ch03.poincareUpperEllipticityFactor
      Q a s (.finite 2) ≤ L := by
    simpa only [Q, L] using
      poincareUpperEllipticityFactor_le_of_weakError_le_one hs herror
  have henergy : Book.Ch03.solutionEnergyNorm Q a u = D :=
    solutionEnergyNorm_eq_h1EnergyNormOnCube Q a u
  have hgradSemi : cubeBesovNegativeVectorSeminormTwo Q s u.toH1.grad ≤
      B * L * D := by
    calc
      _ ≤ Book.Ch03.coarsePoincareGradientRHS Q a s (.finite 2) u := by
        simpa only [Book.Ch03.solutionGradientField,
          Book.Ch03.scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo]
          using hgradRaw
      _ = B * Book.Ch03.poincareLowerEllipticityFactor
          Q a s (.finite 2) * D := by
        rw [Book.Ch03.coarsePoincareGradientRHS, henergy]
      _ ≤ B * L * D := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hlower hB) hD
  have hfluxAE :
      (fun x ↦ matVecMul ((a.coeffOn Q).toCoeffField x)
          (u.toH1.grad x)) =ᵐ[volumeMeasureOn (cubeSet Q)]
        fun x ↦ matVecMul (Book.Ch03.publicCoeffField Q a x)
          (u.toH1.grad x) := by
    filter_upwards [Book.Ch03.publicCoeffField_ae_eq_cubeSet Q a] with x hx
    rw [hx]
  have hfluxSemi : cubeBesovNegativeVectorSeminormTwo Q s
      (fun x ↦ matVecMul (Book.Ch03.publicCoeffField Q a x)
        (u.toH1.grad x)) ≤ B * L * D := by
    calc
      _ = cubeBesovNegativeVectorSeminormTwo Q s
          (fun x ↦ matVecMul ((a.coeffOn Q).toCoeffField x)
            (u.toH1.grad x)) :=
        cubeBesovNegativeVectorSeminormTwo_eq_of_ae_eq_on_cubeSet
          s hfluxAE.symm
      _ ≤ Book.Ch03.coarsePoincareFluxRHS Q a s (.finite 2) u := by
        simpa only [Book.Ch03.solutionFluxField,
          Book.Ch03.scaleNormalizedNegativeBesovVectorNorm_finite_two_eq_cubeBesovNegativeVectorSeminormTwo]
          using! hfluxRaw
      _ = B * Book.Ch03.poincareUpperEllipticityFactor
          Q a s (.finite 2) * D := by
        rw [Book.Ch03.coarsePoincareFluxRHS, henergy]
      _ ≤ B * L * D := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hupper hB) hD
  have hKC : K * B * L ≤ C := by
    dsimp only [C]
    exact le_add_of_nonneg_left (by norm_num)
  constructor
  · calc
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s u.toH1.grad ≤
          K * cubeBesovNegativeVectorSeminormTwo Q s u.toH1.grad := by
        simpa only [K] using! hnoteGrad
      _ ≤ K * (B * L * D) := mul_le_mul_of_nonneg_left hgradSemi hK
      _ = (K * B * L) * D := by ring
      _ ≤ C * D := mul_le_mul_of_nonneg_right hKC hD
  · calc
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s
          (fun x ↦ matVecMul (Book.Ch03.publicCoeffField Q a x)
            (u.toH1.grad x)) ≤
          K * cubeBesovNegativeVectorSeminormTwo Q s
            (fun x ↦ matVecMul (Book.Ch03.publicCoeffField Q a x)
              (u.toH1.grad x)) := by
        simpa only [K] using! hnoteFlux
      _ ≤ K * (B * L * D) := mul_le_mul_of_nonneg_left hfluxSemi hK
      _ = (K * B * L) * D := by ring
      _ ≤ C * D := mul_le_mul_of_nonneg_right hKC hD

end

end HighContrast
end HCPolySupport
