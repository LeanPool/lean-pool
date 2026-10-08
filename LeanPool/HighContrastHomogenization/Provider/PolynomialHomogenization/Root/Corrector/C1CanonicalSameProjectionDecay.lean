/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.Corrector.C1JointTargetRestriction
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorGlobalRepresentative

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.Corrector.C1CanonicalSameProjectionDecay

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Same-projection decay for the canonical slope map

The canonical least-squares projection on the base cube is the exact base
minimizer.  The fixed-base decay theorem can therefore retain that one linear
projection while the observation cube ranges through the full finite interval.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory
open scoped ENNReal

noncomputable section

/-- The canonical projection chosen on the base cube has the same real-rate
decay on every intermediate cube. -/
theorem exists_canonicalFiniteCorrectorSameProjectionDecayConstants
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
                      (C * Real.rpow 3 (-eta * ((m - q : ℕ) : ℝ))) *
                    weightedGradNorm
                      (a.coeffOn (originCube d (m : ℤ))).toCoeffField
                      (openCubeSet (originCube d (m : ℤ)))
                      (fun x ↦ (e + (Phi e).globalGradientRepresentative x) -
                        (finiteAffineSolution a (m : ℤ) e).toH1.grad x) := by
  obtain ⟨C, c, hC, hc, hfixed⟩ :=
    exists_scalarIdentityFiniteAffineFixedBaseDecayConstants
      d s eta hs hs_lt hetaHalf heta1
  refine ⟨C, c, hC, hc, ?_⟩
  intro a delta n0 hdelta hgood hCauchy Phi hPhi n m hn hnm2 hT
  dsimp only
  intro e q hq
  have hgoodN : ScalarIdentityGoodTail a s delta (n : ℤ) :=
    hgood.mono_start hn
  let u := finiteAffineCorrectionJointLocalCubeSolution a hCauchy e m
  have hJ := jointTargetHarmonicGradient_eq_restricted_outer
    a hCauchy e (show n ≤ m by omega)
  have hP := finiteCorrectorWeightedProjection_eq_exactMinimizer_of_target
    a hCauchy (show n ≤ m by omega) hT e u hJ
  have hraw := hfixed a delta n m hdelta hgoodN hnm2 u q hq
  rw [← hP] at hraw
  have hPhiLimit : IsFiniteAffineCorrectionJointLocalLimit a Phi := by
    simpa only [IsFiniteAffineCorrectionJointLocalLimit] using hPhi.1
  have hPhiEq : Phi = finiteAffineCorrectionJointLocalLimit a hCauchy :=
    (isFiniteAffineCorrectionJointLocalLimit_iff_eq a hCauchy Phi).mp hPhiLimit
  have hboundary :
      (show H1Function (localGradientCube d m) from by
        simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
          finiteAffineBoundaryH1 (m : ℤ) e).grad = fun _ ↦ e := by
    simpa only using! finiteAffineBoundaryH1_grad (m := (m : ℤ)) e
  have hqm : q ≤ m := (Finset.mem_Icc.mp hq).2
  have hmu : volumeMeasureOn (openCubeSet (originCube d (q : ℤ))) ≤
      volumeMeasureOn (openCubeSet (originCube d (m : ℤ))) :=
    Measure.restrict_mono_set volume
      (openCubeSet_originCube_subset_of_le (by exact_mod_cast hqm))
  have hglobal :=
    ((finiteAffineCorrectionJointLocalLimit a hCauchy
      e).globalGradientRepresentative_ae_eq_localH1Gradient m).filter_mono
      (ae_mono hmu)
  have hfield : u.toH1.grad =ᵐ[volumeMeasureOn
      (openCubeSet (originCube d (q : ℤ)))]
      (fun x ↦ e + (Phi e).globalGradientRepresentative x) := by
    rw [hPhiEq]
    filter_upwards [hglobal] with x hx
    simp only [u, finiteAffineCorrectionJointLocalCubeSolution,
      finiteAffineCorrectionJointLocalH1, H1Function.add_grad,
      hboundary, hx]
  have hleft : weightedGradNorm
        (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        (openCubeSet (originCube d (q : ℤ)))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a (m : ℤ)
            ((finiteCorrectorWeightedProjection a hCauchy
              (show n ≤ m by omega) hT) e)).toH1.grad x) =
      weightedGradNorm
        (a.coeffOn (originCube d (q : ℤ))).toCoeffField
        (openCubeSet (originCube d (q : ℤ)))
        (fun x ↦ (e + (Phi e).globalGradientRepresentative x) -
          (finiteAffineSolution a (m : ℤ)
            ((finiteCorrectorWeightedProjection a hCauchy
              (show n ≤ m by omega) hT) e)).toH1.grad x) := by
    apply weightedGradNorm_congr_ae
    filter_upwards [hfield] with x hx
    rw [hx]
  rw [← hleft]
  refine hraw.trans ?_
  have hglobalM :=
    (finiteAffineCorrectionJointLocalLimit a hCauchy
      e).globalGradientRepresentative_ae_eq_localH1Gradient m
  have hfieldM : u.toH1.grad =ᵐ[volumeMeasureOn
      (openCubeSet (originCube d (m : ℤ)))]
      (fun x ↦ e + (Phi e).globalGradientRepresentative x) := by
    rw [hPhiEq]
    filter_upwards [hglobalM] with x hx
    simp only [u, finiteAffineCorrectionJointLocalCubeSolution,
      finiteAffineCorrectionJointLocalH1, H1Function.add_grad,
      hboundary, hx]
  have hright : weightedGradNorm
        (a.coeffOn (originCube d (m : ℤ))).toCoeffField
        (openCubeSet (originCube d (m : ℤ)))
        (fun x ↦ u.toH1.grad x -
          (finiteAffineSolution a (m : ℤ) e).toH1.grad x) =
      weightedGradNorm
        (a.coeffOn (originCube d (m : ℤ))).toCoeffField
        (openCubeSet (originCube d (m : ℤ)))
        (fun x ↦ (e + (Phi e).globalGradientRepresentative x) -
          (finiteAffineSolution a (m : ℤ) e).toH1.grad x) := by
    apply weightedGradNorm_congr_ae
    filter_upwards [hfieldM] with x hx
    rw [hx]
  have hexcess := finiteAffineGradientExcess_le a (m : ℤ) (m : ℤ) u e
  rw [hright] at hexcess
  simpa only [mul_comm] using
    mul_le_mul_left hexcess
      (ENNReal.ofReal (C * Real.rpow 3 (-eta * ((m - q : ℕ) : ℝ))))

end

end Root
end HighContrast
end HCPolySupport
