/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ConstantSkewCoefficient
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Dilation
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.SolutionIntegrability

/-!
# High-contrast homogenization: Provider.Response.ConstantSkewResponse

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant-skew covariance of the response functional

The harmonic solution spaces for `a` and `a - g` have the same gradients when
`g` is constant and skew.  On those common gradients, subtracting `g` from the
coefficient is exactly compensated by replacing the second load `q` with
`q - g p`.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem matVecMul_sub (A B : Mat d) (x : Vec d) :
    matVecMul (A - B) x = matVecMul A x - matVecMul B x := by
  funext i
  simp only [matVecMul, Matrix.sub_apply, Pi.sub_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem symmPart_sub_skew (A g : Mat d) (hg : IsSkewMat g) :
    symmPart (A - g) = symmPart A := by
  ext i j
  have hji : g j i = -g i j := by
    have hij := congrFun (congrFun hg i) j
    simpa [IsSkewMat, matTranspose, Matrix.transpose_apply,
      Matrix.neg_apply] using hij
  simp only [symmPart, Matrix.sub_apply]
  rw [hji]
  ring

private theorem vecDot_skew_mulVec_swap (g : Mat d) (hg : IsSkewMat g)
    (p z : Vec d) :
    vecDot p (matVecMul g z) = -vecDot (matVecMul g p) z := by
  have hmatrix :
      dotProduct p (Matrix.mulVec g z) =
        dotProduct (Matrix.mulVec (Matrix.transpose g) p) z := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  have htranspose : Matrix.transpose g = -g := hg
  rw [htranspose, Matrix.neg_mulVec, neg_dotProduct] at hmatrix
  simpa [vecDot, matVecMul, dotProduct, Matrix.mulVec] using hmatrix

/-- A solution for `a` gives a solution with the same `H¹` representative for
`a - g`. -/
theorem exists_solution_subSkew
    {U : Domain d} {a b : CoeffOn U} (g : Mat d) (hg : IsSkewMat g)
    (hshift : b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x ↦ a.toCoeffField x - g) (u : Solution U a) :
    ∃ v : Solution U b, v.toH1 = u.toH1 := by
  let gfield : Vec d → Vec d := fun x ↦ matVecMul g (u.toH1.grad x)
  have hgmem : MemVectorL2 (U : Set (Vec d)) gfield :=
    memVectorL2_constMatrix_mul_gradient g u.toH1
  have hgsol : IsSolenoidalOn (U : Set (Vec d)) gfield :=
    isSolenoidalOn_constSkew_mul_gradient U.isOpen g hg u.toH1
  have hnegmem : MemVectorL2 (U : Set (Vec d)) ((-1 : ℝ) • gfield) :=
    hgmem.const_smul (-1)
  have hnegsol : IsSolenoidalOn (U : Set (Vec d)) ((-1 : ℝ) • gfield) :=
    isSolenoidalOn_smul hgsol (-1)
  have hsum :
      IsSolenoidalOn (U : Set (Vec d))
        ((fun x ↦ matVecMul (a.toCoeffField x) (u.toH1.grad x)) +
          (-1 : ℝ) • gfield) :=
    isSolenoidalOn_add_of_memVectorL2 u.flux_memVectorL2 hnegmem
      u.isHarmonic.2 hnegsol
  refine ⟨{ toH1 := u.toH1
            isHarmonic := ⟨u.isHarmonic.1, ?_⟩ }, rfl⟩
  refine IsSolenoidalOn.congr_ae ?_ hsum
  filter_upwards [hshift] with x hx
  rw [hx]
  change
    matVecMul (a.toCoeffField x) (u.toH1.grad x) +
        (-1 : ℝ) • matVecMul g (u.toH1.grad x) =
      matVecMul (a.toCoeffField x - g) (u.toH1.grad x)
  rw [matVecMul_sub]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  ring

/-- Conversely, a solution for `a - g` gives a solution with the same `H¹`
representative for `a`. -/
theorem exists_solution_of_subSkew
    {U : Domain d} {a b : CoeffOn U} (g : Mat d) (hg : IsSkewMat g)
    (hshift : b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x ↦ a.toCoeffField x - g) (v : Solution U b) :
    ∃ u : Solution U a, u.toH1 = v.toH1 := by
  let gfield : Vec d → Vec d := fun x ↦ matVecMul g (v.toH1.grad x)
  have hgmem : MemVectorL2 (U : Set (Vec d)) gfield :=
    memVectorL2_constMatrix_mul_gradient g v.toH1
  have hgsol : IsSolenoidalOn (U : Set (Vec d)) gfield :=
    isSolenoidalOn_constSkew_mul_gradient U.isOpen g hg v.toH1
  have hsum :
      IsSolenoidalOn (U : Set (Vec d))
        ((fun x ↦ matVecMul (b.toCoeffField x) (v.toH1.grad x)) + gfield) :=
    isSolenoidalOn_add_of_memVectorL2 v.flux_memVectorL2 hgmem
      v.isHarmonic.2 hgsol
  refine ⟨{ toH1 := v.toH1
            isHarmonic := ⟨v.isHarmonic.1, ?_⟩ }, rfl⟩
  refine IsSolenoidalOn.congr_ae ?_ hsum
  filter_upwards [hshift] with x hx
  change
    matVecMul (b.toCoeffField x) (v.toH1.grad x) +
        matVecMul g (v.toH1.grad x) =
      matVecMul (a.toCoeffField x) (v.toH1.grad x)
  rw [hx]
  rw [matVecMul_sub]
  ext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

/-- The response value of matching solutions is covariant under a constant
skew recentering. -/
theorem responseValue_subSkew
    {U : Domain d} {a b : CoeffOn U} (g : Mat d) (hg : IsSkewMat g)
    (hshift : b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x ↦ a.toCoeffField x - g)
    (p q : Vec d) (u : Solution U a) (v : Solution U b)
    (hv : v.toH1 = u.toH1) :
    responseValue U b p q v =
      responseValue U a p (q - matVecMul g p) u := by
  unfold responseValue Book.Ch02.average
  congr 1
  apply integral_congr_ae
  filter_upwards [hshift] with x hx
  unfold responseIntegrand
  rw [hx, hv, symmPart_sub_skew (a.toCoeffField x) g hg,
    matVecMul_sub]
  have hswap := vecDot_skew_mulVec_swap g hg p (u.toH1.grad x)
  have hpflux :
      vecDot p
          (matVecMul (a.toCoeffField x) (u.toH1.grad x) -
            matVecMul g (u.toH1.grad x)) =
        vecDot p (matVecMul (a.toCoeffField x) (u.toH1.grad x)) -
          vecDot p (matVecMul g (u.toH1.grad x)) := by
    simp only [vecDot, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  have hqsub :
      vecDot (q - matVecMul g p) (u.toH1.grad x) =
        vecDot q (u.toH1.grad x) -
          vecDot (matVecMul g p) (u.toH1.grad x) := by
    simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  rw [hpflux, hqsub, hswap]
  ring

/-- The admissible response-value sets agree after the load correction. -/
theorem responseValueSet_subSkew
    {U : Domain d} {a b : CoeffOn U} (g : Mat d) (hg : IsSkewMat g)
    (hshift : b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x ↦ a.toCoeffField x - g) (p q : Vec d) :
    responseValueSet U b p q =
      responseValueSet U a p (q - matVecMul g p) := by
  ext m
  constructor
  · rintro ⟨v, rfl⟩
    obtain ⟨u, hu⟩ := exists_solution_of_subSkew g hg hshift v
    exact ⟨u, responseValue_subSkew g hg hshift p q u v hu.symm⟩
  · rintro ⟨u, rfl⟩
    obtain ⟨v, hv⟩ := exists_solution_subSkew g hg hshift u
    exact ⟨v, (responseValue_subSkew g hg hshift p q u v hv).symm⟩

/-- Constant-skew covariance of the Chapter 2 response functional. -/
theorem responseJ_subSkew_of_ae
    {U : Domain d} {a b : CoeffOn U} (g : Mat d) (hg : IsSkewMat g)
    (hshift : b.toCoeffField =ᵐ[volumeMeasureOn (U : Set (Vec d))]
      fun x ↦ a.toCoeffField x - g) (p q : Vec d) :
    responseJ U b p q = responseJ U a p (q - matVecMul g p) := by
  unfold responseJ
  rw [responseValueSet_subSkew g hg hshift p q]

/-- Constant-skew covariance specialized to the recentered coefficient sample. -/
theorem responseJ_subSkew (U : Domain d) (a : CoeffSpace d)
    (g : Mat d) (hg : IsSkewMat g) (p q : Vec d) :
    responseJ U ((a.subSkew g hg).coeffOn U) p q =
      responseJ U (a.coeffOn U) p (q - matVecMul g p) :=
  responseJ_subSkew_of_ae g hg (CoeffSpace.coeffOn_subSkew_ae a U g hg) p q

end

end HCPolySupport.HighContrast.Response
