/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.FiniteAffineVaryingSlopeLimit

/-!
# High-contrast homogenization: Provider.Regularity.CanonicalSlopeLocalCoercivity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Local coercivity of the canonical corrector slope

Finite affine average-slope coercivity passes to the canonical joint local
limit. Hence a canonical full-gradient class which vanishes on one admissible
fixed cube must have zero slope.
-/

namespace HCPolySupport
namespace HighContrast

open _root_.Filter
open scoped Topology

noncomputable section

private theorem continuous_euclideanNorm_local {d : ℕ} :
    Continuous (euclideanNorm : Vec d → ℝ) := by
  rw [show (euclideanNorm : Vec d → ℝ) =
      fun x => ‖HilbertVec.ofVecL d x‖ by
    funext x
    rw [HilbertVec.ofVecL_apply]
    exact euclideanNorm_eq_norm_ofVec x]
  exact continuous_norm.comp (HilbertVec.ofVecL d).continuous

/-- Under a sufficiently small scalar good tail, the canonical slope is
controlled by its full-gradient average on every cube beyond the starting
scale. -/
theorem exists_scalarIdentityGoodTailCanonicalLocalSlopeCoercivityThreshold
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
          (e : Vec d) (q : ℕ), n ≤ (q : ℤ) →
          euclideanNorm e ≤ 2 * euclideanNorm
            (localGradientClassAverage
              ((show LocalGradientL2 d q from
                  constantGradientOnOriginCube e (q : ℤ)) +
                (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q)) := by
  obtain ⟨c, hc, hfinite⟩ :=
    exists_scalarIdentityGoodTailFiniteAffineSlopeAverageCoercivityThreshold
      d s hs hs_lt
  refine ⟨c, hc, ?_⟩
  intro a delta n hdelta hgood hCauchy e q hnq
  let L : LocalGradientL2 d q :=
    (show LocalGradientL2 d q from
        constantGradientOnOriginCube e (q : ℤ)) +
      (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q
  let g : ℕ → LocalGradientL2 d q := fun k =>
    (finiteAffineSolutionInnerH1 a (q : ℤ)
      ((q + (k + 2) : ℕ) : ℤ) (by omega) e).gradToHilbertVectorL2
  have hgradBase :=
    finiteAffineSolutionInnerGradient_varyingSlope_tendsto_jointLocalGradient
      a hCauchy q (fun _k => e) e tendsto_const_nhds
  have hgrad : Tendsto g atTop (nhds L) := by
    have hshift := hgradBase.comp (tendsto_add_atTop_nat 2)
    simpa only [g, L, Function.comp_apply, add_assoc] using! hshift
  have havg : Tendsto (fun k => localGradientClassAverage (g k)) atTop
      (nhds (localGradientClassAverage L)) :=
    (continuous_localGradientClassAverage.tendsto L).comp hgrad
  have hnorm : Tendsto
      (fun k => 2 * euclideanNorm (localGradientClassAverage (g k))) atTop
      (nhds (2 * euclideanNorm (localGradientClassAverage L))) := by
    exact tendsto_const_nhds.mul
      ((continuous_euclideanNorm_local.tendsto _).comp havg)
  change euclideanNorm e ≤ 2 * euclideanNorm (localGradientClassAverage L)
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hnorm
  exact Eventually.of_forall fun k => by
    have hbound := hfinite a delta n hdelta hgood q k hnq e
    have havgEq : localGradientClassAverage (g k) =
        cubeAverageVec (originCube d (q : ℤ))
          (finiteAffineSolution a ((q + k + 2 : ℕ) : ℤ) e).toH1.grad := by
      dsimp only [g]
      apply localGradientClassAverage_eq_cubeAverageVec_of_ae
      exact (finiteAffineSolutionInnerH1 a (q : ℤ)
        ((q + (k + 2) : ℕ) : ℤ) (by omega) e).coeFn_gradToHilbertVectorL2
    simpa only [havgEq, add_assoc] using hbound

/-- Local injectivity: if the canonical full-gradient class vanishes on one
admissible cube, then its slope is zero. -/
theorem canonicalSlope_eq_zero_of_localFullGradient_eq_zero
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d} {n : ℤ}
    (hcoercive : ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
      (e : Vec d) (q : ℕ), n ≤ (q : ℤ) →
      euclideanNorm e ≤ 2 * euclideanNorm
        (localGradientClassAverage
          ((show LocalGradientL2 d q from
              constantGradientOnOriginCube e (q : ℤ)) +
            (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q)))
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (e : Vec d) (q : ℕ) (hnq : n ≤ (q : ℤ))
    (hzero : (show LocalGradientL2 d q from
        constantGradientOnOriginCube e (q : ℤ)) +
      (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q = 0) :
    e = 0 := by
  have h := hcoercive hCauchy e q hnq
  rw [hzero, localGradientClassAverage_zero, euclideanNorm_zero, mul_zero] at h
  exact euclideanNorm_eq_zero_iff.mp (le_antisymm h (euclideanNorm_nonneg e))

/-- Two canonical slopes whose full-gradient classes agree on one admissible
cube are equal. -/
theorem canonicalSlope_eq_of_localFullGradient_eq
    {d : ℕ} [NeZero d] {a : Book.Ch02.TriadicCoeffFamily d} {n : ℤ}
    (hcoercive : ∀ (hCauchy : FiniteAffineCorrectionLocalCauchy a)
      (e : Vec d) (q : ℕ), n ≤ (q : ℤ) →
      euclideanNorm e ≤ 2 * euclideanNorm
        (localGradientClassAverage
          ((show LocalGradientL2 d q from
              constantGradientOnOriginCube e (q : ℤ)) +
            (finiteAffineCorrectionJointLocalLimit a hCauchy e).gradientComponent q)))
    (hCauchy : FiniteAffineCorrectionLocalCauchy a)
    (e e' : Vec d) (q : ℕ) (hnq : n ≤ (q : ℤ))
    (heq : (jointAffineFullGradientLinearMap a hCauchy q) e =
      (jointAffineFullGradientLinearMap a hCauchy q) e') :
    e = e' := by
  have hzero : (jointAffineFullGradientLinearMap a hCauchy q) (e - e') = 0 := by
    rw [map_sub, heq, sub_self]
  have hdiff : e - e' = 0 :=
    canonicalSlope_eq_zero_of_localFullGradient_eq_zero hcoercive
      hCauchy (e - e') q hnq (by
        simpa only [jointAffineFullGradientLinearMap] using! hzero)
  exact sub_eq_zero.mp hdiff

end

end HighContrast
end HCPolySupport
