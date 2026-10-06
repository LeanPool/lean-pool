/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalSameProjectionDecay
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicGrowthGoodTail

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1BaseSlopeEnergyControl

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Energy control of the base exact slope

The large-scale Lipschitz estimate controls the original solution on the base
cube without a volume-ratio loss.  Coefficient-energy Minkowski and exact
minimality then control the finite affine comparison and its boundary slope.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory
open scoped ENNReal

noncomputable section

private theorem sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube_base
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (k : ℤ) (u : H1Function (openCubeSet (originCube d k))) :
    Real.sqrt (normalizedLocalSymmetricEnergy
        (Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
          (originCube d k) a) u.gradToHilbertVectorL2) =
      Book.Ch03.h1EnergyNormOnCube (originCube d k) a u := by
  rw [sqrt_normalizedEnergy_grad_eq_weightedGradNorm_toReal]
  rw [weightedGradNorm_congr_coeff_ae_on _
    (Book.Ch03.publicCoeffField_ae_eq_openCubeSet (originCube d k) a)]
  erw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]
  rw [ENNReal.toReal_ofReal]
  unfold Book.Ch03.h1EnergyNormOnCube
  exact Real.sqrt_nonneg _

private theorem finite_affine_minimizer_energy_le_twice_solution
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    {n m : ℕ} (hnm : (n : ℤ) ≤ (m : ℤ))
    (u : Book.Ch03.CubeSolution (originCube d (m : ℤ)) a) :
    Book.Ch03.h1EnergyNormOnCube (originCube d (n : ℤ)) a
        (finiteCubeSolutionRestriction a hnm
          (finiteAffineCubeSolution a (m : ℤ)
            (finiteAffineExactMinimizer a hnm u))).toH1 ≤
      2 * Book.Ch03.h1EnergyNormOnCube (originCube d (n : ℤ)) a
        (finiteCubeSolutionRestriction a hnm u).toH1 := by
  let b := finiteAffineExactMinimizer a hnm u
  let uN := finiteCubeSolutionRestriction a hnm u
  let w := finiteCubeSolutionRestriction a hnm
    (finiteAffineCubeSolution a (m : ℤ) b)
  let r := finiteAffineGradientResidual a hnm u b
  let hEll := Book.Ch03.publicCoeffField_isEllipticFieldOn_openCubeSet
    (originCube d (n : ℤ)) a
  have hvol : 0 < volume (openCubeSet (originCube d (n : ℤ))) :=
    (ENNReal.toReal_pos_iff.mp
      (volume_openCubeSet_originCube_toReal_pos (d := d) (n : ℤ))).1
  have hvoltop : volume (openCubeSet (originCube d (n : ℤ))) ≠ ⊤ :=
    (volume_openCubeSet_lt_top (originCube d (n : ℤ))).ne
  have hclass : w.toH1.gradToHilbertVectorL2 =
      uN.toH1.gradToHilbertVectorL2 - r.toH1.gradToHilbertVectorL2 := by
    apply MeasureTheory.Lp.ext
    filter_upwards [w.toH1.coeFn_gradToHilbertVectorL2,
        uN.toH1.coeFn_gradToHilbertVectorL2,
        r.toH1.coeFn_gradToHilbertVectorL2,
        MeasureTheory.Lp.coeFn_sub uN.toH1.gradToHilbertVectorL2
          r.toH1.gradToHilbertVectorL2] with x hwx hux hrx hsub
    rw [hwx, hsub, Pi.sub_apply, hux, hrx]
    simp only [w, uN, finiteCubeSolutionRestriction_grad,
      finiteAffineCubeSolution, r, finiteAffineGradientResidual_grad]
    change WithLp.toLp 2 ((finiteAffineSolution a (m : ℤ) b).toH1.grad x) =
      WithLp.toLp 2 (u.toH1.grad x) - WithLp.toLp 2
        (u.toH1.grad x - (finiteAffineSolution a (m : ℤ) b).toH1.grad x)
    rw [← WithLp.toLp_sub]
    congr 1
    abel
  have htri := sqrt_normalizedLocalSymmetricEnergy_add_le hEll hvol hvoltop
    uN.toH1.gradToHilbertVectorL2 (-r.toH1.gradToHilbertVectorL2)
  have hneg_eq : normalizedLocalSymmetricEnergy hEll (-r.toH1.gradToHilbertVectorL2) =
      normalizedLocalSymmetricEnergy hEll r.toH1.gradToHilbertVectorL2 :=
    normalizedLocalSymmetricEnergy_neg_increment _ _
  have henergyTri : Book.Ch03.h1EnergyNormOnCube
        (originCube d (n : ℤ)) a w.toH1 ≤
      Book.Ch03.h1EnergyNormOnCube (originCube d (n : ℤ)) a uN.toH1 +
        Book.Ch03.h1EnergyNormOnCube (originCube d (n : ℤ)) a r.toH1 := by
    have htri' : √(normalizedLocalSymmetricEnergy hEll w.toH1.gradToHilbertVectorL2) ≤
        √(normalizedLocalSymmetricEnergy hEll uN.toH1.gradToHilbertVectorL2) +
          √(normalizedLocalSymmetricEnergy hEll r.toH1.gradToHilbertVectorL2) := by
      rw [hclass, sub_eq_add_neg, ← hneg_eq]
      exact htri
    have hw : √(normalizedLocalSymmetricEnergy hEll w.toH1.gradToHilbertVectorL2) =
        Book.Ch03.h1EnergyNormOnCube (originCube d (n : ℤ)) a w.toH1 :=
      sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube_base a (n : ℤ) w.toH1
    have hu : √(normalizedLocalSymmetricEnergy hEll uN.toH1.gradToHilbertVectorL2) =
        Book.Ch03.h1EnergyNormOnCube (originCube d (n : ℤ)) a uN.toH1 :=
      sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube_base a (n : ℤ) uN.toH1
    have hr : √(normalizedLocalSymmetricEnergy hEll r.toH1.gradToHilbertVectorL2) =
        Book.Ch03.h1EnergyNormOnCube (originCube d (n : ℤ)) a r.toH1 :=
      sqrt_normalizedEnergy_grad_eq_h1EnergyNormOnCube_base a (n : ℤ) r.toH1
    rw [hw, hu, hr] at htri'
    exact htri'
  refine henergyTri.trans ?_
  have hspec := finiteAffineExactMinimizer_spec a hnm u
  have hbridge := weightedGradNorm_finiteAffineGradientResidual a hnm u b
  have hspec' : weightedGradNorm
        (a.coeffOn (originCube d (n : ℤ))).toCoeffField
        (openCubeSet (originCube d (n : ℤ)))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a (m : ℤ) b).toH1.grad x) =
      finiteAffineGradientExcess a (n : ℤ) (m : ℤ) u := by
    simpa only [b] using hspec
  rw [hspec'] at hbridge
  have hr0 : 0 ≤ Book.Ch03.h1EnergyNormOnCube
      (originCube d (n : ℤ)) a r.toH1 := by
    unfold Book.Ch03.h1EnergyNormOnCube
    positivity
  have hrEq : Book.Ch03.h1EnergyNormOnCube
        (originCube d (n : ℤ)) a r.toH1 =
      (finiteAffineGradientExcess a (n : ℤ) (m : ℤ) u).toReal := by
    have hreal := congrArg ENNReal.toReal hbridge
    symm
    simpa only [r, ENNReal.toReal_ofReal hr0] using hreal
  have hexcess := finiteAffineGradientExcess_le
    a (n : ℤ) (m : ℤ) u (0 : Vec d)
  have hzero := finiteAffineSolution_grad_smul
    a (m : ℤ) (0 : ℝ) (0 : Vec d)
  have hzeroN : (finiteAffineSolution a (m : ℤ) (0 : Vec d)).toH1.grad
      =ᵐ[volumeMeasureOn (openCubeSet (originCube d (n : ℤ)))] fun _ ↦ 0 :=
    ae_mono (Measure.restrict_mono_set volume
      (openCubeSet_originCube_subset_of_le hnm)) (by
        have hmeas : volumeMeasureOn
            (Book.Ch02.cubeDomain (originCube d (m : ℤ))).carrier =
            volume.restrict (openCubeSet (originCube d (m : ℤ))) := rfl
        rw [hmeas] at hzero
        filter_upwards [hzero] with x hx
        simpa only [zero_smul] using hx)
  have hcandEq : weightedGradNorm
        (a.coeffOn (originCube d (n : ℤ))).toCoeffField
        (openCubeSet (originCube d (n : ℤ)))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a (m : ℤ) (0 : Vec d)).toH1.grad x) =
      weightedGradNorm
        (a.coeffOn (originCube d (n : ℤ))).toCoeffField
        (openCubeSet (originCube d (n : ℤ))) uN.toH1.grad := by
    apply weightedGradNorm_congr_ae
    filter_upwards [hzeroN] with x hx
    simp only [uN, finiteCubeSolutionRestriction_grad]
    rw [hx]
    simp
  rw [hcandEq, weightedGradNorm_eq_ofReal_h1EnergyNormOnCube] at hexcess
  have hexcessReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hexcess
  have hu0 : 0 ≤ Book.Ch03.h1EnergyNormOnCube
      (originCube d (n : ℤ)) a uN.toH1 := by
    unfold Book.Ch03.h1EnergyNormOnCube
    positivity
  rw [ENNReal.toReal_ofReal hu0] at hexcessReal
  rw [hrEq]
  linarith only [hexcessReal]

/-- The exact base-cube minimizing slope is bounded by the original outer
solution energy with a dimension-only constant. -/
theorem exists_baseExactMinimizerSlopeEnergyConstants
    (d : ℕ) [NeZero d] (s : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ K c : ℝ, 0 < K ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n m : ℕ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta (n : ℤ) →
        (hnm2 : n + 2 ≤ m) →
        ∀ u : Book.Ch03.CubeSolution (originCube d (m : ℤ)) a,
          euclideanNorm (finiteAffineExactMinimizer a
              (by exact_mod_cast (show n ≤ m by omega) :
                (n : ℤ) ≤ (m : ℤ)) u) ≤
            K * Book.Ch03.h1EnergyNormOnCube
              (originCube d (m : ℤ)) a u.toH1 := by
  obtain ⟨cA, hcA, hcoercive⟩ :=
    exists_scalarIdentityGoodTailFiniteAffineSlopeAverageCoercivityThreshold
      d s hs hs_lt
  obtain ⟨CL, cL, hCL, hcL, hLipschitz⟩ :=
    exists_scalarIdentityFiniteLipschitzConstant d s hs hs_lt
  let K : ℝ := 4 * Real.sqrt (4 * (d : ℝ)) * CL
  let c : ℝ := min cA cL
  have hK : 0 < K := by
    dsimp only [K]
    have hd : 0 < (d : ℝ) := by exact_mod_cast Nat.pos_of_neZero d
    exact mul_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (by positivity)))
      (lt_of_lt_of_le zero_lt_one hCL)
  have hc0 : 0 < c := by dsimp only [c]; exact lt_min hcA.1 hcL.1
  have hc1 : c < 1 := (min_le_left cA cL).trans_lt hcA.2
  refine ⟨K, c, hK, ⟨hc0, hc1⟩, ?_⟩
  intro a delta n m hdelta hgood hnm2 u
  let hnm : (n : ℤ) ≤ (m : ℤ) := by exact_mod_cast (show n ≤ m by omega)
  let b := finiteAffineExactMinimizer a hnm u
  let uN : Book.Ch03.CubeSolution (originCube d (n : ℤ)) a :=
    finiteCubeSolutionRestriction a hnm u
  let w : Book.Ch03.CubeSolution (originCube d (n : ℤ)) a :=
    finiteCubeSolutionRestriction a hnm
      (finiteAffineCubeSolution a (m : ℤ) b)
  have hdeltaA : delta ∈ Set.Ioc (0 : ℝ) cA :=
    ⟨hdelta.1, hdelta.2.trans (min_le_left _ _)⟩
  have hdeltaL : delta ≤ cL := hdelta.2.trans (min_le_right _ _)
  have hgoodL : ScalarIdentityGoodTailOnInterval a s cL
      (n : ℤ) (m : ℤ) :=
    (hgood.interval (by omega)).mono hdeltaL
  have hLip := hLipschitz a (n : ℤ) (m : ℤ) (by omega) hgoodL u
  have hinnerEq : weightedGradNorm
        (a.coeffOn (originCube d (n : ℤ))).toCoeffField
        (openCubeSet (originCube d (n : ℤ))) u.toH1.grad =
      ENNReal.ofReal (Book.Ch03.h1EnergyNormOnCube
        (originCube d (n : ℤ)) a uN.toH1) := by
    rw [show u.toH1.grad = uN.toH1.grad by
      simp only [uN, finiteCubeSolutionRestriction_grad]]
    exact weightedGradNorm_eq_ofReal_h1EnergyNormOnCube _ _ _
  have houterEq : weightedGradNorm
        (a.coeffOn (originCube d (m : ℤ))).toCoeffField
        (openCubeSet (originCube d (m : ℤ))) u.toH1.grad =
      ENNReal.ofReal (Book.Ch03.h1EnergyNormOnCube
        (originCube d (m : ℤ)) a u.toH1) :=
    weightedGradNorm_eq_ofReal_h1EnergyNormOnCube _ _ _
  rw [hinnerEq, houterEq] at hLip
  have hLipReal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) hLip
  have hCL0 : 0 ≤ CL := hCL.trans' zero_le_one
  have henergyU : Book.Ch03.h1EnergyNormOnCube
        (originCube d (n : ℤ)) a uN.toH1 ≤
      CL * Book.Ch03.h1EnergyNormOnCube
        (originCube d (m : ℤ)) a u.toH1 := by
    have hn0 : 0 ≤ Book.Ch03.h1EnergyNormOnCube
        (originCube d (n : ℤ)) a uN.toH1 := by
      unfold Book.Ch03.h1EnergyNormOnCube
      positivity
    have hm0 : 0 ≤ Book.Ch03.h1EnergyNormOnCube
        (originCube d (m : ℤ)) a u.toH1 := by
      unfold Book.Ch03.h1EnergyNormOnCube
      positivity
    simpa only [ENNReal.toReal_ofReal hn0, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hCL0, ENNReal.toReal_ofReal hm0] using hLipReal
  have hweakN : scalarIdentityWeakError a s (n : ℤ) ≤ 1 :=
    (hgood.weakError_le le_rfl).trans (hdelta.2.trans hc1.le)
  have hbavg := hcoercive a delta (n : ℤ) hdeltaA hgood n (m - n - 2)
    (le_refl (n : ℤ)) b
  rw [show ((n + (m - n - 2) + 2 : ℕ) : ℤ) = (m : ℤ) by omega] at hbavg
  have havg := euclideanNorm_cubeAverageVec_solutionGradient_le
    a s hs (n : ℤ) hweakN w
  have havgEq : cubeAverageVec (originCube d (n : ℤ)) w.toH1.grad =
      cubeAverageVec (originCube d (n : ℤ))
        (finiteAffineSolution a (m : ℤ) b).toH1.grad := by rfl
  rw [← havgEq] at hbavg
  have hwenergy : Book.Ch03.h1EnergyNormOnCube
        (originCube d (n : ℤ)) a w.toH1 ≤
      2 * Book.Ch03.h1EnergyNormOnCube
        (originCube d (n : ℤ)) a uN.toH1 :=
    finite_affine_minimizer_energy_le_twice_solution a hnm u
  calc
    euclideanNorm b ≤ 2 * euclideanNorm
        (cubeAverageVec (originCube d (n : ℤ)) w.toH1.grad) := hbavg
    _ ≤ 2 * (Real.sqrt (4 * (d : ℝ)) *
        Book.Ch03.h1EnergyNormOnCube (originCube d (n : ℤ)) a w.toH1) := by
      exact mul_le_mul_of_nonneg_left havg (by norm_num)
    _ ≤ 2 * (Real.sqrt (4 * (d : ℝ)) *
        (2 * Book.Ch03.h1EnergyNormOnCube
          (originCube d (n : ℤ)) a uN.toH1)) := by gcongr
    _ ≤ 2 * (Real.sqrt (4 * (d : ℝ)) *
        (2 * (CL * Book.Ch03.h1EnergyNormOnCube
          (originCube d (m : ℤ)) a u.toH1))) := by gcongr
    _ = K * Book.Ch03.h1EnergyNormOnCube
        (originCube d (m : ℤ)) a u.toH1 := by
      dsimp only [K]
      ring

end

end Root
end HighContrast
end HCPolySupport
