/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalChainTonelli

/-!
# High-contrast homogenization: Provider.PolynomialHomogenization.ConvexFractionalChainPotential

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Riesz-potential aggregation of the infinite convex chain
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The explicit structural factor in the physical chain-membership kernel. -/
@[expose]
def convexFractionalChainRieszConstant
    (rho Rad a : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((2 * Rad) ^ a) +
    ENNReal.ofReal ((Rad + rho) ^ a) *
      ENNReal.ofReal (((2 : ℝ) ^ a) / ((2 : ℝ) ^ a - 1))

/-- The pointwise chain-membership series is bounded by the physical
order-`d-s` Riesz kernel away from the diagonal. -/
theorem tsum_convexFractionalChainBall_scaleWeight_le_rieszKernel
    {U : Set (Vec d)} {c x y : Vec d} {rho Rad s : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad)
    (houter : U ⊆ euclideanBallAt c Rad) (hx : x ∈ U) (hy : y ∈ U)
    (hxy : x ≠ y) (hsd : s < (d : ℝ)) :
    (∑' n : ℕ, (convexFractionalChainBall c x rho n).indicator
        (fun _ => ENNReal.ofReal
          (convexFractionalChainScale n ^ (s - (d : ℝ)))) y) ≤
      convexFractionalChainRieszConstant rho Rad ((d : ℝ) - s) *
        ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) := by
  let a := (d : ℝ) - s
  have ha : 0 < a := sub_pos.mpr hsd
  have hbase := tsum_convexFractionalChainBall_weight_le_rieszKernel
    hrho hRad houter hx hy hxy ha
  have hterm : ∀ n : ℕ,
      (convexFractionalChainBall c x rho n).indicator
          (fun _ => ENNReal.ofReal
            (convexFractionalChainScale n ^ (s - (d : ℝ)))) y =
        (convexFractionalChainBall c x rho n).indicator
          (fun _ => ENNReal.ofReal (((2 : ℝ) ^ a) ^ n)) y := by
    intro n
    by_cases hn : y ∈ convexFractionalChainBall c x rho n
    · rw [Set.indicator_of_mem hn, Set.indicator_of_mem hn]
      exact ofReal_convexFractionalChainScale_rpow_sub_eq d n s
    · rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hn]
  simp_rw [hterm]
  have hexp : s - (d : ℝ) = -((d : ℝ) - s) := by ring
  rw [hexp]
  dsimp only [a] at hbase ⊢
  calc
    _ ≤ ENNReal.ofReal ((2 * Rad) ^ a) *
          ENNReal.ofReal (euclideanDist x y ^ (-a)) +
        ENNReal.ofReal ((Rad + rho) ^ a) *
          ENNReal.ofReal (euclideanDist x y ^ (-a)) *
            ENNReal.ofReal (((2 : ℝ) ^ a) / ((2 : ℝ) ^ a - 1)) := hbase
    _ = convexFractionalChainRieszConstant rho Rad a *
        ENNReal.ofReal (euclideanDist x y ^ (-a)) := by
      rw [convexFractionalChainRieszConstant, add_mul]
      ac_rfl

/-- Summing the weighted amplitude masses of all chain balls gives a Riesz
potential of the global amplitude. -/
theorem tsum_scaleWeight_mul_chainAmplitude_le_rieszPotential
    (hd : 1 ≤ d) {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U)
    {c x : Vec d} {rho Rad s : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad)
    (hinner : euclideanBallAt c rho ⊆ U)
    (houter : U ⊆ euclideanBallAt c Rad) (hx : x ∈ U)
    {G : Vec d → Vec d} (hG : Measurable G) (hsd : s < (d : ℝ)) :
    (∑' n : ℕ, ENNReal.ofReal
        (convexFractionalChainScale n ^ (s - (d : ℝ))) *
          ∫⁻ y in convexFractionalChainBall c x rho n,
            fractionalGagliardoAmplitude U s G y ∂volume) ≤
      convexFractionalChainRieszConstant rho Rad ((d : ℝ) - s) *
        ∫⁻ y in U, ENNReal.ofReal
          (euclideanDist x y ^ (s - (d : ℝ))) *
            fractionalGagliardoAmplitude U s G y ∂volume := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  have hAmp := measurable_fractionalGagliardoAmplitude
    (U := U) (s := s) hG
  rw [tsum_scaleWeight_mul_setLIntegral_chainBall_eq hAmp]
  have hsupp : Function.support (fun y => ∑' n : ℕ,
      (convexFractionalChainBall c x rho n).indicator
        (fun y => ENNReal.ofReal
          (convexFractionalChainScale n ^ (s - (d : ℝ))) *
            fractionalGagliardoAmplitude U s G y) y) ⊆ U := by
    intro y hy
    by_contra hyU
    apply hy
    apply ENNReal.tsum_eq_zero.mpr
    intro n
    rw [Set.indicator_of_notMem]
    exact fun hyn => hyU
      (convexFractionalChainBall_subset hU hrho hinner hx n hyn)
  rw [← setLIntegral_eq_of_support_subset hsupp]
  have hCtop : convexFractionalChainRieszConstant
      rho Rad ((d : ℝ) - s) ≠ ∞ := by
    rw [convexFractionalChainRieszConstant]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top⟩
  rw [← lintegral_const_mul' _ _ hCtop]
  apply lintegral_mono_ae
  filter_upwards [ae_restrict_mem hU.1.measurableSet,
    ae_restrict_of_ae (Measure.ae_ne volume x)] with y hyU hyx
  have hseries := tsum_convexFractionalChainBall_scaleWeight_le_rieszKernel
    hrho hRad houter hx hyU (Ne.symm hyx) hsd
  have hfactor :
      (∑' n : ℕ, (convexFractionalChainBall c x rho n).indicator
          (fun y => ENNReal.ofReal
            (convexFractionalChainScale n ^ (s - (d : ℝ))) *
              fractionalGagliardoAmplitude U s G y) y) =
        (∑' n : ℕ, (convexFractionalChainBall c x rho n).indicator
          (fun _ => ENNReal.ofReal
            (convexFractionalChainScale n ^ (s - (d : ℝ)))) y) *
          fractionalGagliardoAmplitude U s G y := by
    rw [← ENNReal.tsum_mul_right]
    apply tsum_congr
    intro n
    by_cases hn : y ∈ convexFractionalChainBall c x rho n
    · simp only [Set.indicator_of_mem hn]
    · simp only [Set.indicator_of_notMem hn, zero_mul]
  rw [hfactor]
  calc
    _ = fractionalGagliardoAmplitude U s G y *
        (∑' n : ℕ, (convexFractionalChainBall c x rho n).indicator
          (fun _ => ENNReal.ofReal
            (convexFractionalChainScale n ^ (s - (d : ℝ)))) y) := by
      rw [mul_comm]
    _ ≤ fractionalGagliardoAmplitude U s G y *
        (convexFractionalChainRieszConstant rho Rad ((d : ℝ) - s) *
          ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ)))) :=
      mul_le_mul_right hseries _
    _ = (convexFractionalChainRieszConstant rho Rad ((d : ℝ) - s) *
          ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ)))) *
        fractionalGagliardoAmplitude U s G y := by ac_rfl
    _ = _ := by ac_rfl

end

end HighContrast
end HCPolySupport
