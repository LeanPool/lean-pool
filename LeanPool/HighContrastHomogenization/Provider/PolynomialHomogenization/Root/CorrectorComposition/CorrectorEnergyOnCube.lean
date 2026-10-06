/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorComposition.SlopeBoundedRow
public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicGrowthGoodTail

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorComposition.CorrectorEnergyOnCube

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The corrector's own energy, in the representative form the terminal uses

The `exists_scalarIdentityGoodTailJointWeightedGradientBoundConstant`
bounds the affine-plus-corrector energy on every cube above the good-tail start
by `B * euclideanNorm e`, with `B` law-free.  It is stated on the local `H¹`
object `finiteAffineCorrectionJointLocalH1 a hCauchy e q`; the large-scale C¹ slope approximation
terminal
speaks of `fun y ↦ e + (Phi e).globalGradientRepresentative y`.

The two agree a.e. on the cube — `finiteAffineCorrectionJointLocalH1` is by
definition the affine boundary function plus the carrier's local `H¹`
function, and `globalGradientRepresentative_ae_eq_localH1Gradient` identifies
the representative with that local gradient.  This module performs that one
`weightedGradNorm_congr_ae`, for an arbitrary joint-local-equation carrier
`Phi` (pinned to the canonical limit by
`isFiniteAffineCorrectionJointLocalLimit_iff_eq`).

Nothing here is an estimate.
-/

namespace HCPolySupport
namespace HighContrast
namespace Root

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- **The corrector energy bound, in representative form.**  Above the
good-tail start the affine-plus-corrector energy on every origin cube is at
most `B * euclideanNorm e`, with `B` depending only on `(d, s)`. -/
theorem exists_jointCorrectorRepresentativeEnergyBound (d : ℕ) [NeZero d]
    (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ B c : ℝ, 0 < B ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ (_hCauchy : FiniteAffineCorrectionLocalCauchy a)
          (Phi : Vec d → NormalizedLocalH1Carrier d),
          IsFiniteAffineCorrectionJointLocalEquation a Phi →
          ∀ (e : Vec d) (q : ℕ), n ≤ (q : ℤ) →
            weightedGradNorm (a.coeffOn (originCube d (q : ℤ))).toCoeffField
                (openCubeSet (originCube d (q : ℤ)))
                (fun y ↦ e + (Phi e).globalGradientRepresentative y) ≤
              ENNReal.ofReal (B * euclideanNorm e) := by
  obtain ⟨B, c, hB, hc, hbound⟩ :=
    exists_scalarIdentityGoodTailJointWeightedGradientBoundConstant d s hs hs_lt
  refine ⟨B, c, hB, hc, ?_⟩
  intro a delta n hdelta hgood hCauchy Phi hPhi e q hnq
  have hPhiLimit : IsFiniteAffineCorrectionJointLocalLimit a Phi := by
    simpa only [IsFiniteAffineCorrectionJointLocalLimit] using hPhi.1
  have hPhiEq : Phi = finiteAffineCorrectionJointLocalLimit a hCauchy :=
    (isFiniteAffineCorrectionJointLocalLimit_iff_eq a hCauchy Phi).mp hPhiLimit
  have hraw := hbound a delta n hdelta hgood hCauchy e q hnq
  have hboundary :
      (show H1Function (localGradientCube d q) from by
        simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using
          finiteAffineBoundaryH1 (q : ℤ) e).grad = fun _ ↦ e := by
    simpa only using! finiteAffineBoundaryH1_grad (m := (q : ℤ)) e
  have hjointField :
      (fun y ↦ e + (Phi e).globalGradientRepresentative y)
        =ᵐ[volumeMeasureOn (localGradientCube d q)]
        (finiteAffineCorrectionJointLocalH1 a hCauchy e q).grad := by
    rw [hPhiEq]
    have hae := (finiteAffineCorrectionJointLocalLimit a hCauchy
      e).globalGradientRepresentative_ae_eq_localH1Gradient q
    filter_upwards [hae] with x hx
    simp only [finiteAffineCorrectionJointLocalH1, H1Function.add_grad,
      hboundary, hx]
  have hcongr := weightedGradNorm_congr_ae
    (a.coeffOn (originCube d (q : ℤ))).toCoeffField
    (localGradientCube d q) hjointField
  have hstep : weightedGradNorm
      (a.coeffOn (originCube d (q : ℤ))).toCoeffField
      (localGradientCube d q)
      (fun y ↦ e + (Phi e).globalGradientRepresentative y) ≤
      ENNReal.ofReal (B * euclideanNorm e) := by
    rw [hcongr]
    exact hraw
  simpa only [localGradientCube, Book.Ch02.cubeDomain_coe] using hstep

end

end Root
end HighContrast
end HCPolySupport
