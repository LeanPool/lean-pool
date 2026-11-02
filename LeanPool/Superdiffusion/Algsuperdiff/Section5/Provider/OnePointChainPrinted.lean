/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.EarlyExitPrinted
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.OnePointChainLaplace

/-!
# OnePointChainPrinted

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The printed early-exit and displacement tails, on a carrier

The deterministic optimization of the early-exit exponent is arithmetic in the model constants and
does not see the process at all.  What does see the process is the two measure-theoretic steps
around it: the Chernoff conversion of the chained Laplace estimate, and the inclusion of the
displacement event in the early-exit event.

Both are restated here for a process of a carrier in which the state space is read by a map with a
left inverse.  The Chernoff step is an inequality between measures of one and the same event and
transfers verbatim.  The inclusion is deterministic: if the reading of the path's position at time
`t` has reached the cube radius, the path is no longer in the read cube, since the reading of a
point of the cube is retracted back to that point.  A path whose position is read outside the cube
has left the read cube by that time.

## Main results

* `measure_exitTime_le_exp_sub_of_canonicalChain_on` — the Chernoff step on a carrier.
* `measure_norm_ge_le_measure_exitTime_le_retract` — the displacement inclusion through a
  retraction.
* `measure_exitTime_le_exp_neg_displacementMinScale_on` — the printed form.

## References

* ABK26, the early-exit and displacement estimates of Section 5.3.
-/

namespace Algsuperdiff.Section5.Provider

open Algsuperdiff.Section3
open Algsuperdiff.Section5.Support
open HCPolySupport MarkovProcess MeasureTheory Set
open scoped ENNReal NNReal

noncomputable section

section Carrier

variable {d : ℕ} {alpha : Type*} [PseudoMetricSpace alpha]

/-! ## 1. The Chernoff step -/

/-- The chained estimate in its unconditional Chernoff-exponent form, for an arbitrary law on the
continuous paths of the carrier. -/
theorem measure_exitTime_le_exp_sub_of_canonicalChain_on
    (Q : Measure (ContinuousPath alpha)) (U : Set alpha) (t : NNReal) (lam kappa : ℝ)
    (rho : ℝ≥0∞) (N : ℕ)
    (hexit : Q {eta | ContinuousPath.exitTime U eta ≤ (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (lam * (t : ℝ))) * rho ^ N)
    (hrho : rho ≤ ENNReal.ofReal (Real.exp (-kappa))) :
    Q {eta | ContinuousPath.exitTime U eta ≤ (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (lam * (t : ℝ) - kappa * (N : ℝ))) := by
  have hbound := hexit.trans (ofReal_exp_mul_pow_le_of_budget
    (b := kappa * (N : ℝ) - lam * (t : ℝ)) hrho (by ring_nf; exact le_rfl))
  simpa only [neg_sub] using hbound

/-! ## 2. The displacement inclusion through a retraction -/

/-- **The displacement inclusion, read through a retraction.**  If the reading of the path's
position at time `t` has supremum norm at least the radius of `□_m`, the position is not the
reading of a point of `□_m`, so the path has left the read cube by time `t`. -/
theorem measure_norm_ge_le_measure_exitTime_le_retract
    (Q : Measure (ContinuousPath alpha)) (emb : Vec d → alpha) (ret : alpha → Vec d)
    (hret : ∀ z : Vec d, ret (emb z) = z) (m : ℤ) (t : NNReal) :
    Q {eta | (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ ‖ret (eta t)‖} ≤
      Q {eta | ContinuousPath.exitTime
        (emb '' openCubeSet (originCube d m)) eta ≤ (t : ℝ≥0∞)} := by
  apply measure_mono
  intro eta heta
  have hnormEta : (1 / 2 : ℝ) * (3 : ℝ) ^ m ≤ ‖ret (eta t)‖ := heta
  apply ContinuousPath.exitTime_le_of_notMem
  rintro ⟨z, hz, hze⟩
  have hnorm : ‖z‖ < (1 / 2 : ℝ) * (3 : ℝ) ^ m := by
    have hball : z ∈ Metric.ball (0 : Vec d) ((1 / 2 : ℝ) * (3 : ℝ) ^ m) := by
      rw [← cubeSetAt_eq_ball, cubeSetAt_zero_eq_openCubeSet]
      exact hz
    simpa only [Metric.mem_ball, dist_zero_right] using hball
  have hzret : ret (eta t) = z := by rw [← hze, hret]
  rw [hzret] at hnormEta
  exact absurd hnormEta (not_le_of_gt hnorm)

/-! ## 3. The printed forms -/

/-- **Printed early-exit probability on a carrier.**  The canonical-chain estimate and the full
auxiliary-scale straddle give the paper's exponential minimum for an arbitrary law on the
continuous paths of the carrier. -/
theorem measure_exitTime_le_exp_neg_displacementMinScale_on (M : ABKModel d)
    (Q : Measure (ContinuousPath alpha)) (U : Set alpha)
    {C delta kappa : ℝ} {m n : ℤ} (t : NNReal) (rho : ℝ≥0∞)
    (hC : 0 < C) (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (ht : 0 < (t : ℝ)) (hkappa : 0 < kappa) (hnm : n ≤ m)
    (hnLower : (3 : ℝ) ^ n ≤ auxiliaryScaleBound M.nu (Disorder.cstar M)
      M.gamma delta (t : ℝ) m)
    (hnUpper : auxiliaryScaleBound M.nu (Disorder.cstar M) M.gamma delta (t : ℝ) m <
      (3 : ℝ) ^ (n + 1))
    (hscale : lengthTimeScale M.nu (Disorder.cstar M) M.gamma ((3 : ℝ) ^ n) ≤
      2 * exitTimeScale M n)
    (hdeltaSmall : 128 * (3 : ℝ) ^ d * delta *
        earlyExitProfileCost (Disorder.cstar M) M.gamma ≤ C * kappa)
    (hlarge : earlyExitBaseScale d ≤ 3 ^ (m - n).toNat)
    (hchain : Q {eta | ContinuousPath.exitTime U eta ≤ (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp ((C * exitTimeScale M n)⁻¹ * (t : ℝ))) *
        rho ^ earlyExitChainLength d (m - n).toNat)
    (hrho : rho ≤ ENNReal.ofReal (Real.exp (-kappa))) :
    Q {eta | ContinuousPath.exitTime U eta ≤ (t : ℝ≥0∞)} ≤
      ENNReal.ofReal (Real.exp (-earlyExitDecayConstant d M.gamma delta kappa *
        displacementMinScale M.nu (Disorder.cstar M) M.gamma (t : ℝ) m)) := by
  have hexponent := earlyExit_exponent_le_of_auxiliaryScale_straddle M hC hdelta hdelta1 ht
    hkappa hnm hnLower hnUpper hscale hdeltaSmall hlarge
  have hchernoff := measure_exitTime_le_exp_sub_of_canonicalChain_on Q U t
    (C * exitTimeScale M n)⁻¹ kappa rho (earlyExitChainLength d (m - n).toNat) hchain hrho
  exact hchernoff.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent.2))

end Carrier

end

end Algsuperdiff.Section5.Provider
