/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexFractionalChainScaleNormalization

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexFractionalChainMeanJumpScale

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Scale-normalized consecutive fractional-chain mean jumps
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Every consecutive chain-ball mean jump is bounded by a structural
constant times `scale^(s-d)` and the amplitude mass on the level-`n` ball. -/
theorem edist_convexFractionalChainMean_succ_le_scale_amplitude
    (hd : 1 ≤ d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {c x : Vec d} {rho Rad s : ℝ}
    (hrho : 0 < rho) (hRad : 0 ≤ Rad)
    (hinner : euclideanBallAt c rho ⊆ U)
    (houter : U ⊆ euclideanBallAt c Rad) (hx : x ∈ U)
    {G : Vec d → Vec d} (hGmeas : Measurable G)
    (hGint : Integrable G (volume.restrict U))
    (hs : 0 ≤ (d : ℝ) + 2 * s) (n : ℕ) :
    edist (HilbertVec.ofVec (convexFractionalChainMean c x rho G n))
        (HilbertVec.ofVec (convexFractionalChainMean c x rho G (n + 1))) ≤
      convexFractionalChainJumpConstant d rho Rad s *
        ENNReal.ofReal (convexFractionalChainScale n ^ (s - (d : ℝ))) *
          ∫⁻ z in convexFractionalChainBall c x rho n,
            fractionalGagliardoAmplitude U s G z ∂volume := by
  have hbase := edist_convexFractionalChainMean_succ_le_amplitude
    hU hrho hRad hinner houter hx hGmeas hGint hs n
  have hcoef := convexFractionalChainExactCoefficient_le_scale
    (s := s) (rho := rho) (Rad := Rad) hd c x hrho hRad n
  change _ ≤ convexFractionalChainExactCoefficient c x rho Rad s n *
    (∫⁻ z in convexFractionalChainBall c x rho n,
      fractionalGagliardoAmplitude U s G z ∂volume) at hbase
  apply hbase.trans
  simpa only [mul_comm] using mul_le_mul_right hcoef
    (∫⁻ z in convexFractionalChainBall c x rho n,
      fractionalGagliardoAmplitude U s G z ∂volume)

end

end HighContrast
end HCPolySupport
