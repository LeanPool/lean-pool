/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.CenteredResponseCarriers
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.EuclideanL2CZ
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Recovery

/-!
# High-contrast homogenization: Provider.Response.ConstantSkewSolenoidal

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant skew matrices and potential fields

A constant skew matrix maps the weak gradient of an `H¹` function to a
solenoidal field.  The proof tests first against a smooth compactly supported
function.  Weak integration by parts moves one derivative onto that test, and
the resulting contraction of a skew matrix with its symmetric Hessian
vanishes.  Density of smooth tests then gives the Sobolev statement.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory Set

noncomputable section

variable {d : ℕ}

private theorem skew_contraction_symmetric_zero (h : Mat d)
    (hh : IsSkewMat h) (F : Fin d → Fin d → ℝ)
    (hF : ∀ i j, F i j = F j i) :
    ∑ i, ∑ j, h i j * F i j = 0 := by
  have hswap :
      (∑ i, ∑ j, h i j * F i j) =
        -(∑ i, ∑ j, h i j * F i j) := by
    calc
      (∑ i, ∑ j, h i j * F i j) =
          ∑ i, ∑ j, h j i * F j i := by
            simpa only using
              (Finset.sum_comm :
                (∑ i, ∑ j, h i j * F i j) =
                  ∑ j, ∑ i, h i j * F i j)
      _ = ∑ i, ∑ j, -(h i j * F i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        have hji : h j i = -h i j := by
          have hij := congrFun (congrFun hh i) j
          simpa [IsSkewMat, matTranspose, Matrix.transpose_apply,
            Matrix.neg_apply] using hij
        rw [hji, hF j i]
        ring
      _ = -(∑ i, ∑ j, h i j * F i j) := by
        simp
  linarith only [hswap]

/-- A constant matrix maps an `L²` Sobolev gradient to an `L²` vector field. -/
theorem memVectorL2_constMatrix_mul_gradient
    {U : Set (Vec d)} (h : Mat d) (u : H1Function U) :
    MemVectorL2 U (fun x ↦ matVecMul h (u.grad x)) := by
  rw [MemVectorL2, MeasureTheory.memLp_pi_iff]
  intro i
  change MemL2On U (fun x ↦ ∑ j, h i j * u.grad x j)
  exact MeasureTheory.memLp_finsetSum Finset.univ fun j _ ↦
    (u.gradMemL2 j).const_mul (h i j)

/-- Multiplication of a weak gradient by a constant skew matrix gives a
solenoidal field. -/
theorem isSolenoidalOn_constSkew_mul_gradient
    {U : Set (Vec d)}
    (hU : IsOpen U) (h : Mat d) (hh : IsSkewMat h) (u : H1Function U) :
    IsSolenoidalOn U (fun x ↦ matVecMul h (u.grad x)) := by
  have hmem := memVectorL2_constMatrix_mul_gradient h u
  refine IsSolenoidalOn.of_test_of_contDiff_of_memVectorL2 hmem hU ?_
  intro ψ hψ hψcompact hψsub
  let D : Fin d → Vec d → ℝ := fun i ↦ euclideanCoordDeriv i ψ
  let ψ₀ : H10Function U :=
    H10Function.ofContDiff hU hψ hψcompact hψsub
  have hDmem (i : Fin d) : MemScalarL2 U (D i) := by
    simpa [D, ψ₀, H10Function.ofContDiff, H1Function.ofContDiff,
      euclideanCoordDeriv] using! ψ₀.toH1Function.gradMemL2 i
  have hterm (i j : Fin d) :
      IntegrableOn (fun x ↦ h i j * u.grad x j * D i x) U :=
    ((u.gradMemL2 j).const_mul (h i j)).integrable_mul (hDmem i)
  let F : Fin d → Fin d → ℝ := fun i j ↦
    ∫ x in U, u x * euclideanCoordSecondDeriv i j ψ x ∂volume
  have hFsymm : ∀ i j, F i j = F j i := by
    intro i j
    apply integral_congr_ae
    filter_upwards with x
    rw [euclideanCoordSecondDeriv_comm hψ i j x]
  have hcontract : ∑ i, ∑ j, h i j * F i j = 0 :=
    skew_contraction_symmetric_zero h hh F hFsymm
  have hweak (i j : Fin d) :
      ∫ x in U, u.grad x j * D i x ∂volume = -F i j := by
    have hw := u.hasWeakGradient j (D i)
      (contDiff_euclideanCoordDeriv hψ i)
      (hasCompactSupport_euclideanCoordDeriv hψcompact i)
      ((tsupport_euclideanCoordDeriv_subset_tsupport i ψ).trans hψsub)
    change
      (∫ x in U, u x * euclideanCoordSecondDeriv i j ψ x ∂volume) =
        -∫ x in U, u.grad x j * D i x ∂volume at hw
    change (∫ x in U, u.grad x j * D i x ∂volume) = -F i j
    dsimp only [F]
    linarith only [hw]
  have hinnerInt (i : Fin d) :
      IntegrableOn (fun x ↦ ∑ j, h i j * u.grad x j * D i x) U :=
    MeasureTheory.integrable_finsetSum Finset.univ fun j _ ↦ hterm i j
  calc
    ∫ x in U,
        vecDot (matVecMul h (u.grad x))
          (fun i ↦ (fderiv ℝ ψ x) (basisVec i)) ∂volume =
        ∫ x in U, ∑ i, ∑ j, h i j * u.grad x j * D i x ∂volume := by
          congr 1
          funext x
          simp only [vecDot, matVecMul, D, euclideanCoordDeriv]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.sum_mul]
    _ = ∑ i, ∑ j,
        ∫ x in U, h i j * u.grad x j * D i x ∂volume := by
          rw [MeasureTheory.integral_finsetSum Finset.univ
            (fun i _ ↦ hinnerInt i)]
          apply Finset.sum_congr rfl
          intro i _
          exact MeasureTheory.integral_finsetSum Finset.univ
            (fun j _ ↦ hterm i j)
    _ = ∑ i, ∑ j, -(h i j * F i j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          calc
            ∫ x in U, h i j * u.grad x j * D i x ∂volume =
                h i j * ∫ x in U, u.grad x j * D i x ∂volume := by
                  have heq :
                      (fun x ↦ h i j * u.grad x j * D i x) =
                        fun x ↦ h i j * (u.grad x j * D i x) := by
                    funext x
                    ring
                  rw [heq, MeasureTheory.integral_const_mul]
            _ = -(h i j * F i j) := by rw [hweak i j]; ring
    _ = -(∑ i, ∑ j, h i j * F i j) := by simp
    _ = 0 := by rw [hcontract]; simp

end

end HCPolySupport.HighContrast.Response
