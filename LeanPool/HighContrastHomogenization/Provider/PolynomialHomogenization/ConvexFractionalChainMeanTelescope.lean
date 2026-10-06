/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexFractionalChainPhysicalKernel
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalMeanJump

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexFractionalChainMeanTelescope

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Telescoping means on the infinite convex fractional chain
-/

namespace HCPolySupport
namespace HighContrast

open Filter
open scoped ENNReal Topology

noncomputable section

variable {d : ℕ}

/-- The volume average on the level-`n` ball of the infinite convex chain. -/
@[expose]
def convexFractionalChainMean (c x : Vec d) (rho : ℝ)
    (F : Vec d → Vec d) (n : ℕ) : Vec d :=
  volumeAverageVec (convexFractionalChainBall c x rho n) F

theorem convexFractionalChainMean_zero
    (c x : Vec d) (rho : ℝ) (F : Vec d → Vec d) :
    convexFractionalChainMean c x rho F 0 =
      volumeAverageVec (euclideanBallAt c rho) F := by
  rw [convexFractionalChainMean, convexFractionalChainBall_zero]

/-- Once the shrinking chain-ball means converge to the endpoint value,
their distance from the core-ball mean is bounded by the sum of all
successive mean jumps. -/
theorem edist_convexFractionalChainMean_zero_le_tsum_jumps
    {c x : Vec d} {rho : ℝ} {F : Vec d → Vec d}
    (hmean : Tendsto
      (fun n => HilbertVec.ofVec (convexFractionalChainMean c x rho F n))
      atTop (𝓝 (HilbertVec.ofVec (F x)))) :
    edist (HilbertVec.ofVec (convexFractionalChainMean c x rho F 0))
        (HilbertVec.ofVec (F x)) ≤
      ∑' n : ℕ, edist
        (HilbertVec.ofVec (convexFractionalChainMean c x rho F n))
        (HilbertVec.ofVec (convexFractionalChainMean c x rho F (n + 1))) := by
  exact edist_le_tsum_of_edist_le_of_tendsto₀
    (fun n => edist
      (HilbertVec.ofVec (convexFractionalChainMean c x rho F n))
      (HilbertVec.ofVec (convexFractionalChainMean c x rho F (n + 1))))
    (fun _ => le_rfl) hmean

end

end HighContrast
end HCPolySupport
