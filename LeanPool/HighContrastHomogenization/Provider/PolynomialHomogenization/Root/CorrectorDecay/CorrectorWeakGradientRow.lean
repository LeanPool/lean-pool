/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.LawFreeCoarsePoincare
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicGrowthGoodTail
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalRepresentative

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.CorrectorWeakGradientRow

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The weak corrector row at a good scale

The public quantitative datum of the anchored corrector is its weak norm: the
scale-normalized negative Besov norm of the affine-plus-corrector gradient on a
centered triadic cube.  At a good scale the coarse-Poincare gradient row bounds
that norm by the coefficient energy of the cube solution, and the energy is
bounded by the Euclidean slope through the joint weighted gradient row.  Both
inputs are law-free: the multiplier carries only the dimension and the
multiscale order, and no pointwise ellipticity constant appears anywhere.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set

open scoped ENNReal

noncomputable section

private theorem dualNegativeBesovVectorNormTwo_congr_on_cubeSet
    {d : ℕ} {Q : TriadicCube d} {F G : Vec d → Vec d} (s : ℝ)
    (hFG : F =ᵐ[volumeMeasureOn (cubeSet Q)] G) :
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s F =
      cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s G := by
  unfold cubeScaleNormalizedDualNegativeBesovVectorNormTwo
  congr 1
  refine Finset.sum_congr rfl fun i _hi => ?_
  exact Book.Ch03.cubeBesovDualFullNorm_eq_of_ae_eq_on_cubeSet
    s (2 : ℝ≥0∞) (2 : ℝ≥0∞) (hFG.fun_comp fun z => z i)

/-- **The weak corrector row.**  At a good scale the scale-normalized negative
Besov norm of the affine-plus-corrector gradient on a centered triadic cube is
bounded by the Euclidean slope, with a constant depending only on the dimension
and the multiscale order. -/
theorem exists_scalarIdentityGoodTailCorrectorWeakGradientRowConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ c : ℝ, c ∈ Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a) (e : Vec d),
          ∃ N : ℝ, 0 ≤ N ∧ ∀ q : ℕ, n.toNat ≤ q →
            cubeScaleNormalizedDualNegativeBesovVectorNormTwo
                (originCube d (q : ℤ)) s
                (fun x => e + (finiteAffineCorrectionJointLocalLimit a hCauchy
                  e).globalGradientRepresentative x) ≤ N := by
  obtain ⟨CP, hCP, hrows⟩ := exists_lawFreeCoarsePoincareRowsConstant d s hs
  obtain ⟨B, c, hB, hc, hweighted⟩ :=
    exists_scalarIdentityGoodTailJointWeightedGradientBoundConstant d s hs hs_lt
  refine ⟨c, hc, ?_⟩
  intro a delta n hdelta hgood hCauchy e
  refine ⟨CP * B * euclideanNorm e,
    mul_nonneg (mul_nonneg hCP.le hB.le) (euclideanNorm_nonneg e), ?_⟩
  intro q hq
  have hnq : n ≤ (q : ℤ) := (Int.self_le_toNat n).trans (Int.ofNat_le.mpr hq)
  set Q : TriadicCube d := originCube d (q : ℤ) with hQ
  set u : Book.Ch03.CubeSolution Q a :=
    finiteAffineCorrectionJointLocalCubeSolution a hCauchy e q with hu
  set Phi : NormalizedLocalH1Carrier d :=
    finiteAffineCorrectionJointLocalLimit a hCauchy e with hPhi
  have hweak : scalarIdentityWeakError a s (q : ℤ) ≤ 1 :=
    (hgood.weakError_le hnq).trans (hdelta.2.trans hc.2.le)
  have henergy :
      Book.Ch03.h1EnergyNormOnCube Q a u.toH1 ≤ B * euclideanNorm e := by
    have hbound := hweighted a delta n hdelta hgood hCauchy e q hnq
    have heq :
        weightedGradNorm (a.coeffOn Q).toCoeffField (openCubeSet Q) u.toH1.grad =
          ENNReal.ofReal (Book.Ch03.h1EnergyNormOnCube Q a u.toH1) :=
      weightedGradNorm_eq_ofReal_h1EnergyNormOnCube Q a u.toH1
    refine (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg hB.le (euclideanNorm_nonneg e))).1 ?_
    rw [← heq]
    simpa only [hQ, hu, localGradientCube,
      finiteAffineCorrectionJointLocalCubeSolution_toH1] using hbound
  have hboundary :
      (show H1Function (localGradientCube d q) from by
        simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
          finiteAffineBoundaryH1 (q : ℤ) e).grad = fun _ => e := by
    simpa only using! finiteAffineBoundaryH1_grad (m := (q : ℤ)) e
  have hdecomp : ∀ x : Vec d,
      u.toH1.grad x = e + (Phi.localH1Function q).grad x := by
    intro x
    simp only [hu, hPhi, finiteAffineCorrectionJointLocalCubeSolution_toH1,
      finiteAffineCorrectionJointLocalH1, H1Function.add_grad, hboundary]
  have hlocal : (Phi.localH1Function q).grad =ᵐ[volumeMeasureOn (cubeSet Q)]
      Phi.globalGradientRepresentative := by
    have hopen := (Phi.globalGradientRepresentative_ae_eq_localH1Gradient q).symm
    have hset : volumeMeasureOn (cubeSet Q) =
        volumeMeasureOn (localGradientCube d q) := by
      rw [hQ, localGradientCube]
      exact volume_restrict_cubeSet_eq_volume_restrict_openCubeSet _
    rw [hset]
    exact hopen
  have hae : u.toH1.grad =ᵐ[volumeMeasureOn (cubeSet Q)]
      fun x => e + Phi.globalGradientRepresentative x := by
    filter_upwards [hlocal] with x hx
    rw [hdecomp x, hx]
  rw [← dualNegativeBesovVectorNormTwo_congr_on_cubeSet s hae]
  calc
    cubeScaleNormalizedDualNegativeBesovVectorNormTwo Q s u.toH1.grad
        ≤ CP * Book.Ch03.h1EnergyNormOnCube Q a u.toH1 :=
          (hrows a (q : ℤ) u hweak).1
    _ ≤ CP * (B * euclideanNorm e) :=
          mul_le_mul_of_nonneg_left henergy hCP.le
    _ = CP * B * euclideanNorm e := by ring

end

end HighContrast
end HCPolySupport
