/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.FractionalAmplitudeCrossEstimate

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.ConvexFractionalChainMeanJumpAmplitude

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Consecutive convex-chain mean jumps against the Gagliardo amplitude
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem euclideanDist_triangle_le (x z y : Vec d) :
    euclideanDist x y ≤ euclideanDist x z + euclideanDist z y := by
  calc
    euclideanDist x y = dist (HilbertVec.ofVec x) (HilbertVec.ofVec y) := by
      rw [dist_eq_norm, ← euclideanDist_eq_norm_sub_ofVec]
    _ ≤ dist (HilbertVec.ofVec x) (HilbertVec.ofVec z) +
        dist (HilbertVec.ofVec z) (HilbertVec.ofVec y) := dist_triangle _ _ _
    _ = euclideanDist x z + euclideanDist z y := by
      rw [dist_eq_norm, dist_eq_norm, ← euclideanDist_eq_norm_sub_ofVec,
        ← euclideanDist_eq_norm_sub_ofVec]

private theorem volume_chainBall_pos (c x : Vec d) {rho : ℝ}
    (hrho : 0 < rho) (n : ℕ) :
    0 < volume (convexFractionalChainBall c x rho n) := by
  unfold convexFractionalChainBall
  exact IsOpen.measure_pos volume (isOpen_euclideanBallAt _ _)
    ⟨_, center_mem_euclideanBallAt _
      (mul_pos (convexFractionalChainScale_pos n) hrho)⟩

private theorem volume_chainBall_ne_top (c x : Vec d) {rho : ℝ}
    (hrho : 0 < rho) (n : ℕ) :
    volume (convexFractionalChainBall c x rho n) ≠ ⊤ := by
  exact (isOpenBoundedConvexDomain_euclideanBallAt _
    (mul_pos (convexFractionalChainScale_pos n) hrho)).volume_lt_top.ne

/-- A consecutive jump of chain-ball means is controlled by the integral of
the global Gagliardo amplitude on the larger ball, with exact geometric and
volume factors. -/
theorem edist_convexFractionalChainMean_succ_le_amplitude
    {U : Set (Vec d)} (hU : IsOpenBoundedConvexDomain U)
    {c x : Vec d} {rho Rad s : ℝ}
    (hrho : 0 < rho) (hRad : 0 ≤ Rad)
    (hinner : euclideanBallAt c rho ⊆ U)
    (houter : U ⊆ euclideanBallAt c Rad) (hx : x ∈ U)
    {G : Vec d → Vec d} (hGmeas : Measurable G)
    (hGint : Integrable G (volume.restrict U))
    (hs : 0 ≤ (d : ℝ) + 2 * s) (n : ℕ) :
    edist (HilbertVec.ofVec (convexFractionalChainMean c x rho G n))
        (HilbertVec.ofVec (convexFractionalChainMean c x rho G (n + 1))) ≤
      (volume (convexFractionalChainBall c x rho (n + 1)))⁻¹ *
        (volume (convexFractionalChainBall c x rho (n + 1)) *
          ENNReal.ofReal (((3 / 2 : ℝ) * convexFractionalChainScale n *
            (Rad + rho)) ^ ((d : ℝ) + 2 * s))) ^ (1 / 2 : ℝ) *
        (volume (convexFractionalChainBall c x rho n))⁻¹ *
          ∫⁻ z in convexFractionalChainBall c x rho n,
            fractionalGagliardoAmplitude U s G z ∂volume := by
  let E := convexFractionalChainBall c x rho n
  let F := convexFractionalChainBall c x rho (n + 1)
  let D := (3 / 2 : ℝ) * convexFractionalChainScale n * (Rad + rho)
  let K := ENNReal.ofReal (D ^ ((d : ℝ) + 2 * s))
  let C := (volume F)⁻¹ * (volume F * K) ^ (1 / 2 : ℝ)
  have hEsub : E ⊆ U :=
    convexFractionalChainBall_subset hU hrho hinner hx n
  have hFsub : F ⊆ U :=
    convexFractionalChainBall_subset hU hrho hinner hx (n + 1)
  have hEpos : 0 < volume E := volume_chainBall_pos c x hrho n
  have hFpos : 0 < volume F := volume_chainBall_pos c x hrho (n + 1)
  have hEtop : volume E ≠ ⊤ := volume_chainBall_ne_top c x hrho n
  have hFtop : volume F ≠ ⊤ := volume_chainBall_ne_top c x hrho (n + 1)
  have hGE : Integrable G (volume.restrict E) := hGint.mono_measure
    (Measure.restrict_mono hEsub le_rfl)
  have hGF : Integrable G (volume.restrict F) := hGint.mono_measure
    (Measure.restrict_mono hFsub le_rfl)
  have hDdist : ∀ z ∈ E, ∀ y ∈ F, euclideanDist z y ≤ D := by
    intro z hz y hy
    have hz' := euclideanDist_lt_scale_mul_add_of_mem_convexFractionalChainBall
      houter hx hRad hrho hz
    have hy' := euclideanDist_lt_scale_mul_add_of_mem_convexFractionalChainBall
      houter hx hRad hrho hy
    have htri := euclideanDist_triangle_le z x y
    have hsum : euclideanDist z x + euclideanDist x y < D := by
      rw [euclideanDist_comm z x]
      calc
        euclideanDist x z + euclideanDist x y <
            convexFractionalChainScale n * (Rad + rho) +
              convexFractionalChainScale (n + 1) * (Rad + rho) :=
          add_lt_add hz' hy'
        _ = D := by
          rw [convexFractionalChainScale_succ]
          dsimp only [D]
          ring
    exact (htri.trans_lt hsum).le
  have hcross : ∀ z ∈ E,
      (∫⁻ y in F, ENNReal.ofReal (euclideanDist (G z) (G y)) ∂volume) ≤
        volume F * C * fractionalGagliardoAmplitude U s G z := by
    intro z hz
    have hbase := setLIntegral_fieldDistance_le_fractionalAmplitude
      (U := U) (F := F) (x := z) (s := s) (D := D) (G := G)
      (isOpen_euclideanBallAt _ _).measurableSet hFsub hGmeas hs
      (fun y hy => hDdist z hz y hy)
    calc
      (∫⁻ y in F, ENNReal.ofReal (euclideanDist (G z) (G y)) ∂volume) ≤
          fractionalGagliardoAmplitude U s G z * (volume F * K) ^
            (1 / 2 : ℝ) := hbase
      _ = volume F * C * fractionalGagliardoAmplitude U s G z := by
        dsimp only [C]
        calc
          fractionalGagliardoAmplitude U s G z * (volume F * K) ^
              (1 / 2 : ℝ) =
              (volume F * (volume F)⁻¹) * (volume F * K) ^
                (1 / 2 : ℝ) * fractionalGagliardoAmplitude U s G z := by
            rw [ENNReal.mul_inv_cancel hFpos.ne' hFtop]
            simp only [one_mul]
            ac_rfl
          _ = volume F * ((volume F)⁻¹ * (volume F * K) ^
                (1 / 2 : ℝ)) * fractionalGagliardoAmplitude U s G z := by
            ac_rfl
  have hCtop : C ≠ ⊤ := by
    apply ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hFpos.ne')
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top hFtop ENNReal.ofReal_ne_top)
  simpa only [E, F, D, K, C, convexFractionalChainMean] using!
    edist_volumeAverageVec_le_amplitudeAverage_of_cross
      (U := U) (s := s) (G := G)
      (isOpen_euclideanBallAt _ _).measurableSet hEpos hEtop hFpos hFtop
      hGE hGF hCtop hcross

end

end HighContrast
end HCPolySupport
