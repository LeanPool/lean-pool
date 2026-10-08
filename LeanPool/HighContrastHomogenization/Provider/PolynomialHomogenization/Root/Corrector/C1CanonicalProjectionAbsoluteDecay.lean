/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1WeightedEnergyTriangle
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalSameProjectionDecay

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalProjectionAbsoluteDecay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Absolute decay of the canonical finite projection

The same-projection decay is combined with the scale-uniform energy bounds
for the joint corrector and the finite affine solution.  The resulting bound
depends only on the slope and retains the real decay exponent.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The canonical base projection approximates the joint affine-corrector
gradient at every intermediate cube with a slope-proportional bound. -/
theorem exists_canonicalFiniteCorrectorAbsoluteDecayConstants
    (d : ℕ) [NeZero d] (s eta : ℝ)
    (hs : 0 < s) (hs_lt : s < 1 / 2)
    (hetaHalf : 1 / 2 ≤ eta) (heta1 : eta < 1) :
    ∃ C c : ℝ, 0 < C ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n0 : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n0 →
        ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
          (Phi : Vec d → NormalizedLocalH1Carrier d),
          IsFiniteAffineCorrectionJointLocalEquation a Phi →
          ∀ (n m : ℕ), n0 ≤ (n : ℤ) →
            ∀ hnm2 : n + 2 ≤ m,
            ∀ hT : Function.Injective
              (finiteTrialHarmonicGradientLinearMap a (by omega : n ≤ m)),
              let P := finiteCorrectorWeightedProjection a hCauchy
                (by omega : n ≤ m) hT
              ∀ (e : Vec d) (q : ℕ), q ∈ Finset.Icc n m →
                weightedGradNorm
                    (a.coeffOn (originCube d (q : ℤ))).toCoeffField
                    (openCubeSet (originCube d (q : ℤ)))
                    (fun x ↦ (e + (Phi e).globalGradientRepresentative x) -
                      (finiteAffineSolution a (m : ℤ) (P e)).toH1.grad x) ≤
                  ENNReal.ofReal
                    (C * Real.rpow 3 (-eta * ((m - q : ℕ) : ℝ)) *
                      euclideanNorm e) := by
  obtain ⟨Cproj, cProj, hCproj, hcProj, hproj⟩ :=
    exists_canonicalFiniteCorrectorSameProjectionDecayConstants
      d s eta hs hs_lt hetaHalf heta1
  obtain ⟨B, cJoint, hB, hcJoint, hjoint⟩ :=
    exists_scalarIdentityGoodTailJointWeightedGradientBoundConstant
      d s hs hs_lt
  obtain ⟨E, hE, hfinite⟩ :=
    exists_finiteAffineSolutionEnergyEstimateConstant d s hs
      (hs_lt.trans (by norm_num))
  let A : ℝ := B + 2 * E
  let C : ℝ := Cproj * A
  let c : ℝ := min cProj cJoint
  have hA : 0 < A := add_pos hB (mul_pos (by norm_num) hE)
  have hC : 0 < C := mul_pos hCproj hA
  have hc0 : 0 < c := by dsimp only [c]; exact lt_min hcProj.1 hcJoint.1
  have hc1 : c < 1 := (min_le_left cProj cJoint).trans_lt hcProj.2
  refine ⟨C, c, hC, ⟨hc0, hc1⟩, ?_⟩
  intro a delta n0 hdelta hgood hCauchy Phi hPhi n m hn hnm2 hT
  dsimp only
  intro e q hq
  have hdeltaProj : delta ∈ Set.Ioc (0 : ℝ) cProj :=
    ⟨hdelta.1, hdelta.2.trans (min_le_left _ _)⟩
  have hdeltaJoint : delta ∈ Set.Ioc (0 : ℝ) cJoint :=
    ⟨hdelta.1, hdelta.2.trans (min_le_right _ _)⟩
  let P := finiteCorrectorWeightedProjection a hCauchy
    (by omega : n ≤ m) hT
  have hdecay := hproj a delta n0 hdeltaProj hgood hCauchy Phi hPhi
    n m hn hnm2 hT e q hq
  let jointM := finiteAffineCorrectionJointLocalH1 a hCauchy e m
  let finiteM := (finiteAffineSolution a (m : ℤ) e).toH1
  have htri := weightedGradNorm_sub_le_add_sub_h1 a (m : ℤ)
    jointM (0 : H1Function (openCubeSet (originCube d (m : ℤ)))) finiteM
  have hzeroJoint : weightedGradNorm
        (a.coeffOn (originCube d (m : ℤ))).toCoeffField
        (openCubeSet (originCube d (m : ℤ)))
        (fun x ↦ jointM.grad x - (0 : H1Function
          (openCubeSet (originCube d (m : ℤ)))).grad x) =
      weightedGradNorm
        (a.coeffOn (originCube d (m : ℤ))).toCoeffField
        (openCubeSet (originCube d (m : ℤ))) jointM.grad := by
    apply weightedGradNorm_congr_ae
    filter_upwards [] with x
    simp
  have hzeroFinite : weightedGradNorm
        (a.coeffOn (originCube d (m : ℤ))).toCoeffField
        (openCubeSet (originCube d (m : ℤ)))
        (fun x ↦ (0 : H1Function
          (openCubeSet (originCube d (m : ℤ)))).grad x - finiteM.grad x) =
      weightedGradNorm
        (a.coeffOn (originCube d (m : ℤ))).toCoeffField
        (openCubeSet (originCube d (m : ℤ))) finiteM.grad := by
    rw [weightedGradNorm_sub_comm_h1 a (m : ℤ)
      (0 : H1Function (openCubeSet (originCube d (m : ℤ)))) finiteM]
    apply weightedGradNorm_congr_ae
    filter_upwards [] with x
    simp
  rw [hzeroJoint, hzeroFinite] at htri
  have hjointM := hjoint a delta n0 hdeltaJoint hgood hCauchy e m
    (hn.trans (by exact_mod_cast (show n ≤ m by omega)))
  have hweakM : scalarIdentityWeakError a s (m : ℤ) ≤ 1 :=
    (hgood.weakError_le
      (hn.trans (by exact_mod_cast (show n ≤ m by omega)))).trans
        (hdelta.2.trans hc1.le)
  have hfiniteReal := hfinite a (m : ℤ) e
  have hfiniteReal' : Book.Ch03.h1EnergyNormOnCube
      (originCube d (m : ℤ)) a finiteM ≤ 2 * E * euclideanNorm e := by
    dsimp only [finiteM]
    have hnonneg := euclideanNorm_nonneg e
    calc
      _ ≤ E * (1 + scalarIdentityWeakError a s (m : ℤ)) *
          euclideanNorm e := hfiniteReal
      _ ≤ E * 2 * euclideanNorm e := by
        gcongr
        linarith only [hweakM]
      _ = 2 * E * euclideanNorm e := by ring
  have hfiniteW : weightedGradNorm
        (a.coeffOn (originCube d (m : ℤ))).toCoeffField
        (openCubeSet (originCube d (m : ℤ))) finiteM.grad ≤
      ENNReal.ofReal (2 * E * euclideanNorm e) := by
    rw [weightedGradNorm_eq_ofReal_h1EnergyNormOnCube]
    exact ENNReal.ofReal_le_ofReal hfiniteReal'
  have hterminalLocal : weightedGradNorm
        (a.coeffOn (originCube d (m : ℤ))).toCoeffField
        (openCubeSet (originCube d (m : ℤ)))
        (fun x ↦ jointM.grad x - finiteM.grad x) ≤
      ENNReal.ofReal (A * euclideanNorm e) := by
    calc
      _ ≤ weightedGradNorm
            (a.coeffOn (originCube d (m : ℤ))).toCoeffField
            (openCubeSet (originCube d (m : ℤ))) jointM.grad +
          weightedGradNorm
            (a.coeffOn (originCube d (m : ℤ))).toCoeffField
            (openCubeSet (originCube d (m : ℤ))) finiteM.grad := htri
      _ ≤ ENNReal.ofReal (B * euclideanNorm e) +
          ENNReal.ofReal (2 * E * euclideanNorm e) :=
        add_le_add hjointM hfiniteW
      _ = ENNReal.ofReal (A * euclideanNorm e) := by
        rw [← ENNReal.ofReal_add
          (mul_nonneg hB.le (euclideanNorm_nonneg e))
          (mul_nonneg (mul_nonneg (by norm_num) hE.le)
            (euclideanNorm_nonneg e))]
        congr 1
        dsimp only [A]
        ring
  have hPhiLimit : IsFiniteAffineCorrectionJointLocalLimit a Phi := by
    simpa only [IsFiniteAffineCorrectionJointLocalLimit] using hPhi.1
  have hPhiEq : Phi = finiteAffineCorrectionJointLocalLimit a hCauchy :=
    (isFiniteAffineCorrectionJointLocalLimit_iff_eq a hCauchy Phi).mp hPhiLimit
  have hboundary :
      (show H1Function (localGradientCube d m) from by
        simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
          finiteAffineBoundaryH1 (m : ℤ) e).grad = fun _ ↦ e := by
    simpa only using! finiteAffineBoundaryH1_grad (m := (m : ℤ)) e
  have hglobal :=
    (finiteAffineCorrectionJointLocalLimit a hCauchy
      e).globalGradientRepresentative_ae_eq_localH1Gradient m
  have hjointField : jointM.grad =ᵐ[volumeMeasureOn
      (openCubeSet (originCube d (m : ℤ)))]
      (fun x ↦ e + (Phi e).globalGradientRepresentative x) := by
    rw [hPhiEq]
    filter_upwards [hglobal] with x hx
    simp only [jointM, finiteAffineCorrectionJointLocalH1,
      H1Function.add_grad, hboundary, hx]
  have hterminal : weightedGradNorm
        (a.coeffOn (originCube d (m : ℤ))).toCoeffField
        (openCubeSet (originCube d (m : ℤ)))
        (fun x ↦ (e + (Phi e).globalGradientRepresentative x) -
          (finiteAffineSolution a (m : ℤ) e).toH1.grad x) ≤
      ENNReal.ofReal (A * euclideanNorm e) := by
    have heq : weightedGradNorm
          (a.coeffOn (originCube d (m : ℤ))).toCoeffField
          (openCubeSet (originCube d (m : ℤ)))
          (fun x ↦ jointM.grad x - finiteM.grad x) =
        weightedGradNorm
          (a.coeffOn (originCube d (m : ℤ))).toCoeffField
          (openCubeSet (originCube d (m : ℤ)))
          (fun x ↦ (e + (Phi e).globalGradientRepresentative x) -
            (finiteAffineSolution a (m : ℤ) e).toH1.grad x) := by
      apply weightedGradNorm_congr_ae
      filter_upwards [hjointField] with x hx
      rw [hx]
    rw [← heq]
    exact hterminalLocal
  calc
    _ ≤ ENNReal.ofReal
          (Cproj * Real.rpow 3 (-eta * ((m - q : ℕ) : ℝ))) *
        weightedGradNorm
          (a.coeffOn (originCube d (m : ℤ))).toCoeffField
          (openCubeSet (originCube d (m : ℤ)))
          (fun x ↦ (e + (Phi e).globalGradientRepresentative x) -
            (finiteAffineSolution a (m : ℤ) e).toH1.grad x) := hdecay
    _ ≤ ENNReal.ofReal
          (Cproj * Real.rpow 3 (-eta * ((m - q : ℕ) : ℝ))) *
        ENNReal.ofReal (A * euclideanNorm e) := by gcongr
    _ = ENNReal.ofReal
        (C * Real.rpow 3 (-eta * ((m - q : ℕ) : ℝ)) *
          euclideanNorm e) := by
      rw [← ENNReal.ofReal_mul
        (p := Cproj * Real.rpow 3 (-eta * ((m - q : ℕ) : ℝ)))
        (q := A * euclideanNorm e)
        (mul_nonneg hCproj.le (Real.rpow_nonneg (by norm_num) _))]
      congr 1
      dsimp only [C]
      ring

end

end Root
end HighContrast
end HCPolySupport
