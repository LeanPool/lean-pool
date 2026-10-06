/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.AffineChapter3Comparison
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.DeterministicNormalization
public import LeanPool.HighContrastHomogenization.Support.PDE.DirichletRHS
public import LeanPool.HighContrastHomogenization.Support.Sobolev.PotentialSolenoidalL2Realization

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexCubeComparison

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Identity harmonic replacement on a comparison cube

An `H¹` weak solution on an open triadic cube has an identity-coefficient
harmonic replacement with the same boundary trace.  The replacement is built
by solving for its zero-trace correction, so both the second weak equation and
the Chapter 3 comparison datum are consequences rather than inputs.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A high-contrast weak solution on a compatible Chapter 3 cube family admits
an identity-coefficient, zero-force comparison datum on that same cube. -/
theorem exists_identityCoarseGrainingComparisonDatum_of_hcWeakSolution
    {Q : TriadicCube d} {a : Book.Ch03.CoeffFamily d}
    (u : H1Function (Book.Ch02.cubeDomain Q : Set (Vec d)))
    (hu : IsWeakSolutionOn (a.coeffOn Q).toCoeffField
      (Book.Ch02.cubeDomain Q : Set (Vec d)) u.grad) :
    ∃ W : Book.Ch03.CoarseGrainingComparisonDatum Q a
        (identityConstantCoeffMatrix d) (0 : Vec d → Vec d),
      W.u = u := by
  by_cases hd : d = 0
  · subst d
    let U : Set (Vec 0) := Book.Ch02.cubeDomain Q
    let v : H1Function U := u
    have hv : IsWeakSolutionOn
        (constantCoeffField (identityConstantCoeffMatrix 0).matrix) U v.grad := by
      intro phi _hphi
      constructor <;> simp [vecDot]
    have hwTrace :
        (0 : H10Function U).toH1Function.toFun =ᵐ[volumeMeasureOn U]
          fun x => u.toFun x - v.toFun x := by
      filter_upwards with x
      change (0 : ℝ) = u.toFun x - u.toFun x
      ring
    obtain ⟨W, hWu, _hWv⟩ :=
      coarseGrainingComparisonDatum_zero_of_hcWeakSolutions
        (a0 := identityConstantCoeffMatrix 0) u v hu hv 0 hwTrace
    exact ⟨W, hWu⟩
  · let : NeZero d := ⟨hd⟩
    let U : Set (Vec d) := Book.Ch02.cubeDomain Q
    let a0 : Book.Ch03.ConstantCoeffMatrix d := identityConstantCoeffMatrix d
    let b0 : CoeffField d := constantCoeffField a0.matrix
    have hb0_apply (x ξ : Vec d) : matVecMul (b0 x) ξ = ξ := by
      change matVecMul (1 : Mat d) ξ = ξ
      funext i
      simp [matVecMul, Matrix.one_apply]
    have hRealize :
        PotentialSolenoidalL2Data.HasPotentialZeroTraceClosureRealization U :=
      PotentialSolenoidalL2Data.hasPotentialZeroTraceClosureRealization_of_isOpenBoundedConvexDomain
        (by simpa [U] using (Book.Ch02.cubeDomain Q).isDomain)
    have hEll0 : IsEllipticFieldOn a0.lam a0.Lam U b0 := by
      simpa [U, b0] using
        Book.Ch03.constantCoeffMatrix_isEllipticFieldOn_constantCoeffField
          a0 (Book.Ch02.cubeDomain Q).measurableSet
    obtain ⟨w, hw⟩ :=
      exists_isZeroTraceDirichletRhsWeakSolution_of_potentialZeroTraceClosureRealization
        (a := b0) (U := U) (g := u.grad)
        u.grad_memVectorL2 hRealize
        (by simpa [U] using (Book.Ch02.cubeDomain Q).nonempty) hEll0
    let v : H1Function U := u - w.toH1Function
    have hv : IsWeakSolutionOn b0 U v.grad := by
      intro phi hphi
      let psi : H10Function U :=
        H10Function.ofContDiff (Book.Ch02.cubeDomain Q).isOpen
          hphi.contDiff hphi.hasCompactSupport hphi.tsupport_subset
      have hpsiGrad : psi.toH1Function.grad = smoothGrad phi := by
        rfl
      have hpairInt : IntegrableOn
          (fun x => vecDot (psi.toH1Function.grad x) (v.grad x)) U :=
        integrableOn_vecDot_of_memVectorL2
          psi.toH1Function.grad_memVectorL2 v.grad_memVectorL2
      refine ⟨?_, ?_⟩
      · simpa only [hb0_apply, hpsiGrad] using hpairInt
      · have hcorr :
            ∫ x in U, vecDot (w.toH1Function.grad x) (psi.toH1Function.grad x)
                ∂volume =
              ∫ x in U, vecDot (u.grad x) (psi.toH1Function.grad x) ∂volume := by
            simpa only [hb0_apply] using hw psi
        have hEq :
            ∫ x in U, vecDot (psi.toH1Function.grad x) (u.grad x) ∂volume =
              ∫ x in U,
                vecDot (psi.toH1Function.grad x) (w.toH1Function.grad x) ∂volume := by
          calc
            ∫ x in U, vecDot (psi.toH1Function.grad x) (u.grad x) ∂volume =
                ∫ x in U, vecDot (u.grad x) (psi.toH1Function.grad x) ∂volume := by
                  refine integral_congr_ae ?_
                  filter_upwards with x
                  exact vecDot_comm _ _
            _ = ∫ x in U,
                vecDot (w.toH1Function.grad x) (psi.toH1Function.grad x) ∂volume :=
              hcorr.symm
            _ = ∫ x in U,
                vecDot (psi.toH1Function.grad x) (w.toH1Function.grad x) ∂volume := by
                  refine integral_congr_ae ?_
                  filter_upwards with x
                  exact vecDot_comm _ _
        have huInt : IntegrableOn
            (fun x => vecDot (psi.toH1Function.grad x) (u.grad x)) U :=
          integrableOn_vecDot_of_memVectorL2
            psi.toH1Function.grad_memVectorL2 u.grad_memVectorL2
        have hwInt : IntegrableOn
            (fun x => vecDot (psi.toH1Function.grad x) (w.toH1Function.grad x)) U :=
          integrableOn_vecDot_of_memVectorL2
            psi.toH1Function.grad_memVectorL2 w.toH1Function.grad_memVectorL2
        calc
          ∫ x in U, vecDot (smoothGrad phi x) (matVecMul (b0 x) (v.grad x))
                ∂volume =
              ∫ x in U,
                (vecDot (psi.toH1Function.grad x) (u.grad x) -
                  vecDot (psi.toH1Function.grad x) (w.toH1Function.grad x))
                ∂volume := by
                  refine MeasureTheory.setIntegral_congr_fun
                    (Book.Ch02.cubeDomain Q).measurableSet ?_
                  intro x _hx
                  have hgrad : v.grad x = u.grad x - w.toH1Function.grad x := by
                    show (u - w.toH1Function).grad x = u.grad x - w.toH1Function.grad x
                    rw [H1Function.sub_grad]
                  simp only [hb0_apply, hpsiGrad, hgrad, sub_eq_add_neg, vecDot_add_right,
                    vecDot_neg_right]
          _ = (∫ x in U, vecDot (psi.toH1Function.grad x) (u.grad x) ∂volume) -
                ∫ x in U,
                  vecDot (psi.toH1Function.grad x) (w.toH1Function.grad x) ∂volume :=
            MeasureTheory.integral_sub huInt hwInt
          _ = 0 := sub_eq_zero.mpr hEq
    have hwTrace :
        w.toH1Function.toFun =ᵐ[volumeMeasureOn U]
          fun x => u.toFun x - v.toFun x := by
      filter_upwards with x
      show w.toH1Function.toFun x = u.toFun x - (u - w.toH1Function).toFun x
      rw [H1Function.sub_toFun]
      change w.toH1Function.toFun x = u.toFun x - (u.toFun x - w.toH1Function.toFun x)
      ring
    obtain ⟨W, hWu, _hWv⟩ :=
      coarseGrainingComparisonDatum_zero_of_hcWeakSolutions
        (a0 := a0) u v hu hv w hwTrace
    exact ⟨W, by simpa [a0] using hWu⟩

end

end HighContrast
end HCPolySupport
