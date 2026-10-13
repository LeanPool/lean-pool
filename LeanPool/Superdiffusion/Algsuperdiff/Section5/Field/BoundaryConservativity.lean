/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Field.BoundaryGrowth
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.LocalizedBoundaryAsymptotics
public import LeanPool.Superdiffusion.Algsuperdiff.StochasticProcess.Common.DivergenceForm.WholeSpace.ResolventIdentity

/-!
# BoundaryConservativity

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Conservativity of the stream-field analytic minimal resolvent

The split-skew constants on the active support of the cubic boundary cutoff
grow at most linearly in the exhaustion index.  The inward distance grows
like `3^m`, so the localized boundary defect still tends to zero.  This file
uses only the split datum of the model; no global small-contrast assumption is
made.
-/

namespace Algsuperdiff.Section5.Field

open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3
open Filter HCPolySupport MeasureTheory Topology
open DivergenceFormProcess.Decay DivergenceFormProcess.Form
open DivergenceFormProcess.Form.WholeSpaceAnalyticData
open Algsuperdiff.StochasticProcess.Common.Regularity.Ported
open MarkovProcess.Semigroup
open scoped ENNReal

noncomputable section

variable {d : ℕ} [NeZero d]

/-- A scale-independent upper coefficient for the localized Agmon constant
on the active support of the cubic boundary cutoff. -/
def streamBoundaryLocalizedUpperConst (M : ABKModel d)
    (omega : FullSample d M.gamma) (mu : PositiveShift) : ℝ :=
  Real.sqrt 2 * (M.nu + streamBoundaryRoughConst M omega +
    2 * streamBoundarySmoothDivConst M omega * Real.sqrt (M.nu / (mu : ℝ)))

omit [NeZero d] in
theorem streamBoundaryLocalizedUpperConst_pos (M : ABKModel d)
    (omega : FullSample d M.gamma) (mu : PositiveShift) :
    0 < streamBoundaryLocalizedUpperConst M omega mu := by
  unfold streamBoundaryLocalizedUpperConst
  have hrest : 0 ≤ streamBoundaryRoughConst M omega +
      2 * streamBoundarySmoothDivConst M omega * Real.sqrt (M.nu / (mu : ℝ)) :=
    add_nonneg (streamBoundaryRoughConst_nonneg M omega)
      (mul_nonneg
        (mul_nonneg (by norm_num) (streamBoundarySmoothDivConst_nonneg M omega))
        (Real.sqrt_nonneg _))
  exact mul_pos (Real.sqrt_pos.2 (by norm_num)) (by
    linarith only [M.nu_pos, hrest])

omit [NeZero d] in
/-- The effective localized upper constant grows at most linearly in the
exhaustion index. -/
theorem localizedInteriorUpper_streamBoundary_le (M : ABKModel d)
    (omega : FullSample d M.gamma) (mu : PositiveShift) (m : ℕ) :
    localizedInteriorUpper M.nu (mu : ℝ)
        (streamFieldSmallLocalConst M omega 0 ((3 : ℝ) ^ m))
        (streamFieldLargeDivLocalConst M omega 0 ((3 : ℝ) ^ m)) ≤
      streamBoundaryLocalizedUpperConst M omega mu * ((m : ℝ) + 1) := by
  let Ks := streamFieldSmallLocalConst M omega 0 ((3 : ℝ) ^ m)
  let Kl := streamFieldLargeDivLocalConst M omega 0 ((3 : ℝ) ^ m)
  let Cs := streamBoundaryRoughConst M omega
  let Cl := streamBoundarySmoothDivConst M omega
  have hm : 1 ≤ (m : ℝ) + 1 := by
    exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hKs : Ks ≤ Cs * ((m : ℝ) + 1) :=
    streamFieldSmallLocalConst_zero_triadic_le M omega m
  have hKl : Kl ≤ Cl * ((m : ℝ) + 1) :=
    streamFieldLargeDivLocalConst_zero_triadic_le M omega m
  have hCs : 0 ≤ Cs := streamBoundaryRoughConst_nonneg M omega
  have hCl : 0 ≤ Cl := streamBoundarySmoothDivConst_nonneg M omega
  have hsqrt : 0 ≤ Real.sqrt (M.nu / (mu : ℝ)) := Real.sqrt_nonneg _
  have hsqrtTwo : 1 ≤ Real.sqrt 2 := by norm_num
  unfold localizedInteriorUpper
  split_ifs with hzero
  · have hnu : M.nu ≤ M.nu * ((m : ℝ) + 1) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm M.nu_pos.le
    calc
      M.nu + Ks ≤ (M.nu + Cs) * ((m : ℝ) + 1) := by
        calc
          M.nu + Ks ≤ M.nu * ((m : ℝ) + 1) + Cs * ((m : ℝ) + 1) :=
            add_le_add hnu hKs
          _ = _ := by ring
      _ ≤ Real.sqrt 2 * (M.nu + Cs + 2 * Cl * Real.sqrt (M.nu / (mu : ℝ))) *
          ((m : ℝ) + 1) := by
        have hinside : M.nu + Cs ≤
            Real.sqrt 2 * (M.nu + Cs + 2 * Cl * Real.sqrt (M.nu / (mu : ℝ))) := by
          have hbase : 0 ≤ M.nu + Cs := add_nonneg M.nu_pos.le hCs
          have hsmooth : 0 ≤ 2 * Cl * Real.sqrt (M.nu / (mu : ℝ)) :=
            mul_nonneg (mul_nonneg (by norm_num) hCl) hsqrt
          calc
            M.nu + Cs ≤ M.nu + Cs + 2 * Cl * Real.sqrt (M.nu / (mu : ℝ)) :=
              le_add_of_nonneg_right hsmooth
            _ ≤ Real.sqrt 2 *
                (M.nu + Cs + 2 * Cl * Real.sqrt (M.nu / (mu : ℝ))) := by
              simpa only [one_mul] using mul_le_mul_of_nonneg_right hsqrtTwo
                (add_nonneg hbase hsmooth)
        exact mul_le_mul_of_nonneg_right hinside (by positivity)
      _ = streamBoundaryLocalizedUpperConst M omega mu * ((m : ℝ) + 1) := rfl
  · unfold localizedAgmonUpper
    have hnu : M.nu ≤ M.nu * ((m : ℝ) + 1) := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hm M.nu_pos.le
    have hsmooth : 2 * Kl * Real.sqrt (M.nu / (mu : ℝ)) ≤
        (2 * Cl * Real.sqrt (M.nu / (mu : ℝ))) * ((m : ℝ) + 1) := by
      calc
        2 * Kl * Real.sqrt (M.nu / (mu : ℝ)) ≤
            2 * (Cl * ((m : ℝ) + 1)) * Real.sqrt (M.nu / (mu : ℝ)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hKl (by norm_num)) hsqrt
        _ = _ := by ring
    have hinside : M.nu + Ks + 2 * Kl * Real.sqrt (M.nu / (mu : ℝ)) ≤
        (M.nu + Cs + 2 * Cl * Real.sqrt (M.nu / (mu : ℝ))) *
          ((m : ℝ) + 1) := by
      calc
        _ ≤ M.nu * ((m : ℝ) + 1) + Cs * ((m : ℝ) + 1) +
            (2 * Cl * Real.sqrt (M.nu / (mu : ℝ))) * ((m : ℝ) + 1) :=
          add_le_add (add_le_add hnu hKs) hsmooth
        _ = _ := by ring
    simpa only [Ks, Kl, Cs, Cl, streamBoundaryLocalizedUpperConst, mul_assoc] using
      mul_le_mul_of_nonneg_left hinside (Real.sqrt_nonneg 2)

omit [NeZero d] in
private theorem euclideanNorm_add_le (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  have hnorm : ∀ w : Vec d, euclideanNorm w = ‖HilbertVec.ofVecL d w‖ := by
    intro w
    rw [HilbertVec.ofVecL_apply, euclideanNorm_eq_norm_ofVec]
  rw [hnorm, hnorm x, hnorm y, map_add]
  exact norm_add_le _ _

private theorem natCast_add_one_le_three_pow (m : ℕ) :
    (m : ℝ) + 1 ≤ (3 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      norm_num only [Nat.cast_add, Nat.cast_one]
      have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      calc
        (m : ℝ) + 1 + 1 ≤ 3 * ((m : ℝ) + 1) := by
          linarith only [hm]
        _ ≤ 3 * (3 : ℝ) ^ m :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (3 : ℝ) ^ m * 3 := by ring

/-- The analytic boundary defect for the stream coefficient tends pointwise
to zero along the cubic exhaustion. -/
theorem tendsto_abs_streamAnalyticCubeBoundaryRemainder
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) (x : Vec d) :
    Tendsto (fun m ↦ |1 - (mu : ℝ) *
        (streamWholeSpaceAnalyticData M omega).analyticCubeResolvent mu
          (fun _ : Vec d ↦ (1 : ℝ)) measurable_const
          (D := 1) (fun _ ↦ by norm_num) m x|) atTop (nhds 0) := by
  let A := streamWholeSpaceAnalyticData M omega
  let L := streamLocalizedSplitData M omega
  let r₀ := L.freezingRadius x
  let U := streamBoundaryLocalizedUpperConst M omega mu
  let alpha : ℝ := 1 / 2
  let q : ℝ := alpha / (alpha + (d : ℝ) / 2)
  let c : ℝ := Real.sqrt (M.nu * (mu : ℝ)) / (2 * Real.sqrt 2 * U) * q / 4
  have hU : 0 < U := streamBoundaryLocalizedUpperConst_pos M omega mu
  have hr₀ : 0 < r₀ := L.freezingRadius_pos x
  have hq : 0 < q := by unfold q alpha; positivity
  have hc : 0 < c := by
    unfold c
    exact div_pos
      (mul_pos
        (div_pos (Real.sqrt_pos.2 (mul_pos M.nu_pos mu.property)) (by positivity)) hq)
      (by norm_num)
  let P : ℕ → ℝ := fun m : ℕ ↦
    localizedInteriorDecayConstant d M.nu (mu : ℝ)
      (L.roughBound 0 ((3 : ℝ) ^ m)) (L.smoothDivBound 0 ((3 : ℝ) ^ m)) 1
      (cubeBoundaryCutoffUniformGradientBudget (d := d))
      (volume (wholeSpaceCube d m)).toReal alpha
      ((mu : ℝ) * (min (mu : ℝ) M.nu)⁻¹ *
        (volume (wholeSpaceCube d m)).toReal) r₀
  have hPexists : ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ,
      P m ≤ C * ((m : ℝ) + 1) * ((3 : ℝ) ^ (d + 1)) ^ m := by
    let Ceta := cubeBoundaryCutoffUniformGradientBudget (d := d)
    let V0 : ℝ := (2 : ℝ) ^ d
    let Q : ℝ := 8 * U ^ 2 / (M.nu * (mu : ℝ)) * Ceta * V0
    let den : ℝ := Real.sqrt ((volume (smallContrastUnitBall d)).toReal) *
      Real.sqrt ((r₀ / 2) ^ d)
    let e : ℝ := (mu : ℝ) * (min (mu : ℝ) M.nu)⁻¹
    let C2 : ℝ := smallContrastZerothSchauderConstant d *
      (r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0 +
        r₀ ^ (2 - alpha) * ((mu : ℝ) / M.nu)) * (r₀ / 2) ^ alpha
    let C : ℝ := (Q + 1) / den + C2
    have hCeta : 0 ≤ Ceta := by
      unfold Ceta cubeBoundaryCutoffUniformGradientBudget
      positivity
    have hV0 : 0 ≤ V0 := by unfold V0; positivity
    have hQ : 0 ≤ Q := by
      unfold Q
      exact mul_nonneg
        (mul_nonneg
          (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg U))
            (mul_nonneg M.nu_pos.le mu.property.le)) hCeta) hV0
    have hden : 0 < den := by
      unfold den
      exact mul_pos (Real.sqrt_pos.2 unitBallVolume_pos)
        (Real.sqrt_pos.2 (pow_pos (half_pos hr₀) d))
    have he : 0 ≤ e := by
      unfold e
      exact mul_nonneg mu.property.le
        (inv_nonneg.mpr (le_of_lt (lt_min mu.property M.nu_pos)))
    have hC2 : 0 ≤ C2 := by
      unfold C2
      exact mul_nonneg
        (mul_nonneg (smallContrastZerothSchauderConstant_nonneg d)
          (add_nonneg
            (mul_nonneg
              (mul_nonneg (Real.rpow_nonneg hr₀.le _) he) hV0)
            (mul_nonneg (Real.rpow_nonneg hr₀.le _)
              (div_nonneg mu.property.le M.nu_pos.le))))
        (Real.rpow_nonneg (half_pos hr₀).le _)
    have hC : 0 ≤ C := by
      unfold C
      exact add_nonneg (div_nonneg (by linarith only [hQ]) hden.le) hC2
    refine ⟨C, hC, fun m ↦ ?_⟩
    let t : ℝ := (m : ℝ) + 1
    let B : ℝ := ((3 : ℝ) ^ d) ^ m
    let V : ℝ := (volume (wholeSpaceCube d m)).toReal
    let Lm := localizedInteriorUpper M.nu (mu : ℝ)
      (L.roughBound 0 ((3 : ℝ) ^ m)) (L.smoothDivBound 0 ((3 : ℝ) ^ m))
    let X : ℝ := 8 * Lm ^ 2 / (M.nu * (mu : ℝ)) * Ceta * V
    have ht : 1 ≤ t := by
      unfold t
      exact le_add_of_nonneg_left (Nat.cast_nonneg m)
    have hB : 1 ≤ B := by
      unfold B
      exact one_le_pow₀ (one_le_pow₀ (by norm_num))
    have hV : V = V0 * B := by
      unfold V V0 B
      rw [volume_wholeSpaceCube_toReal, mul_pow]
      congr 1
      rw [← pow_mul, Nat.mul_comm m d, pow_mul]
    have hLm : Lm ≤ U * t := by
      simpa only [Lm, U, t, A, L, streamLocalizedSplitData] using
        localizedInteriorUpper_streamBoundary_le M omega mu m
    have hLm0 : 0 < Lm := localizedInteriorUpper_pos M.nu_pos
      (L.roughBound_nonneg 0 ((3 : ℝ) ^ m) (pow_nonneg (by norm_num) m))
      (L.smoothDivBound_nonneg 0 ((3 : ℝ) ^ m) (pow_nonneg (by norm_num) m))
    have hX : 0 ≤ X := by
      unfold X
      exact mul_nonneg
        (mul_nonneg
          (div_nonneg (mul_nonneg (by norm_num) (sq_nonneg Lm))
            (mul_nonneg M.nu_pos.le mu.property.le)) hCeta) ENNReal.toReal_nonneg
    have hXbound : X ≤ Q * t ^ 2 * B := by
      have hsq : Lm ^ 2 ≤ (U * t) ^ 2 :=
        pow_le_pow_left₀ hLm0.le hLm 2
      have hK : 0 ≤ 8 / (M.nu * (mu : ℝ)) * Ceta * V0 := by
        exact mul_nonneg
          (mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 8)
            (mul_nonneg M.nu_pos.le mu.property.le)) hCeta) hV0
      have hB0 : 0 ≤ B := zero_le_one.trans hB
      unfold X
      rw [hV]
      unfold Q
      calc
        8 * Lm ^ 2 / (M.nu * (mu : ℝ)) * Ceta * (V0 * B) =
            (8 / (M.nu * (mu : ℝ)) * Ceta * V0) * Lm ^ 2 * B := by ring
        _ ≤ (8 / (M.nu * (mu : ℝ)) * Ceta * V0) * (U * t) ^ 2 * B :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hK) hB0
        _ = (8 * U ^ 2 / (M.nu * (mu : ℝ)) * Ceta * V0) * t ^ 2 * B := by ring
    have hsqrtX : Real.sqrt X ≤ X + 1 := by
      have hs := Real.sqrt_nonneg X
      have hs2 := Real.sq_sqrt hX
      nlinarith only [hs, hs2, sq_nonneg (Real.sqrt X - 1)]
    have hXone : X + 1 ≤ (Q + 1) * t ^ 2 * B := by
      have htb : 1 ≤ t ^ 2 * B := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ t ^ 2 * B := mul_le_mul (one_le_pow₀ ht) hB (by norm_num)
            (pow_nonneg (zero_le_one.trans ht) 2)
      calc
        X + 1 ≤ Q * t ^ 2 * B + 1 := by linarith only [hXbound]
        _ ≤ Q * t ^ 2 * B + 1 * (t ^ 2 * B) :=
          by simp only [one_mul]; linarith only [htb]
        _ = (Q + 1) * t ^ 2 * B := by ring
    have hfirst : Real.sqrt X /
          Real.sqrt ((volume (smallContrastUnitBall d)).toReal) /
          Real.sqrt ((r₀ / 2) ^ d) ≤
        ((Q + 1) / den) * t ^ 2 * B := by
      calc
        _ ≤ (X + 1) /
            Real.sqrt ((volume (smallContrastUnitBall d)).toReal) /
            Real.sqrt ((r₀ / 2) ^ d) := by gcongr
        _ ≤ ((Q + 1) * t ^ 2 * B) /
            Real.sqrt ((volume (smallContrastUnitBall d)).toReal) /
            Real.sqrt ((r₀ / 2) ^ d) := by gcongr
        _ = ((Q + 1) / den) * t ^ 2 * B := by
          unfold den
          field_simp
    have hsecond : smallContrastZerothSchauderConstant d *
          (r₀ ^ (1 - alpha - (d : ℝ) / 2) * (e * V) +
            r₀ ^ (2 - alpha) * ((mu : ℝ) / M.nu)) *
          (r₀ / 2) ^ alpha ≤ C2 * t ^ 2 * B := by
      have htb : 1 ≤ t ^ 2 * B :=
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ t ^ 2 * B := mul_le_mul (one_le_pow₀ ht) hB (by norm_num)
            (pow_nonneg (zero_le_one.trans ht) 2)
      rw [hV]
      unfold C2
      have hleft0 : 0 ≤ smallContrastZerothSchauderConstant d :=
        smallContrastZerothSchauderConstant_nonneg d
      have hrpow1 : 0 ≤ r₀ ^ (1 - alpha - (d : ℝ) / 2) :=
        Real.rpow_nonneg hr₀.le _
      have hrpow2 : 0 ≤ r₀ ^ (2 - alpha) := Real.rpow_nonneg hr₀.le _
      have hrpow3 : 0 ≤ (r₀ / 2) ^ alpha :=
        Real.rpow_nonneg (half_pos hr₀).le _
      have hmain :
          r₀ ^ (1 - alpha - (d : ℝ) / 2) * (e * (V0 * B)) +
              r₀ ^ (2 - alpha) * ((mu : ℝ) / M.nu) ≤
            (r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0 +
              r₀ ^ (2 - alpha) * ((mu : ℝ) / M.nu)) * (t ^ 2 * B) := by
        have hterm1 :
            r₀ ^ (1 - alpha - (d : ℝ) / 2) * (e * (V0 * B)) ≤
              (r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0) * (t ^ 2 * B) := by
          have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht
          have hBscale : B ≤ t ^ 2 * B := by
            simpa only [one_mul] using
              mul_le_mul_of_nonneg_right ht2 (zero_le_one.trans hB)
          have hcoef : 0 ≤ r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0 :=
            mul_nonneg (mul_nonneg hrpow1 he) hV0
          calc
            _ = (r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0) * B := by ring
            _ ≤ (r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0) * (t ^ 2 * B) :=
              mul_le_mul_of_nonneg_left hBscale hcoef
        have hterm2 := mul_le_mul_of_nonneg_left htb
          (mul_nonneg hrpow2 (div_nonneg mu.property.le M.nu_pos.le))
        calc
          _ ≤ (r₀ ^ (1 - alpha - (d : ℝ) / 2) * e * V0) * (t ^ 2 * B) +
              (r₀ ^ (2 - alpha) * ((mu : ℝ) / M.nu)) * (t ^ 2 * B) :=
            add_le_add hterm1 (by simpa only [mul_one] using hterm2)
          _ = _ := by ring
      convert mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hmain hleft0) hrpow3 using 1
      all_goals first | rfl | ring
    have hPquad : P m ≤ C * t ^ 2 * B := by
      calc
        P m ≤ ((Q + 1) / den) * t ^ 2 * B + C2 * t ^ 2 * B := by
          convert add_le_add hfirst hsecond using 1
          dsimp only [P, localizedInteriorDecayConstant, X, e, V, Lm, Ceta]
          simp only [one_mul, mul_one]
        _ = ((Q + 1) / den + C2) * t ^ 2 * B := by ring
        _ = C * t ^ 2 * B := by rfl
    have htThree : t ≤ (3 : ℝ) ^ m := by
      simpa only [t] using natCast_add_one_le_three_pow m
    calc
      P m ≤ C * t ^ 2 * B := hPquad
      _ ≤ C * t * ((3 : ℝ) ^ m) * B := by
        have hCt : 0 ≤ C * t := mul_nonneg hC (zero_le_one.trans ht)
        calc
          C * t ^ 2 * B = (C * t) * t * B := by ring
          _ ≤ (C * t) * ((3 : ℝ) ^ m) * B := by gcongr
      _ = C * ((m : ℝ) + 1) * ((3 : ℝ) ^ (d + 1)) ^ m := by
        unfold t B
        rw [pow_add, mul_pow]
        ring
  obtain ⟨C, hC, hPC⟩ := hPexists
  have hmajor := tendsto_triadicVolume_mul_exp_neg_triadic_div_linear
    (d + 1) hC hc
  refine squeeze_zero' (Filter.Eventually.of_forall fun m ↦ abs_nonneg _) ?_ hmajor
  filter_upwards [((tendsto_pow_atTop_atTop_of_one_lt
    (by norm_num : (1 : ℝ) < 3)).eventually_gt_atTop
      (4 * (euclideanNorm x + r₀ / 2 + 1)))] with m hm
  have hball : euclideanBall x r₀ ⊆ wholeSpaceCube d m := by
    intro y hy
    rw [mem_wholeSpaceCube_iff]
    have hdist := euclideanNorm_sub_lt_of_mem_euclideanBall hr₀.le hy
    have hnormy : euclideanNorm y ≤ euclideanNorm (y - x) + euclideanNorm x := by
      convert euclideanNorm_add_le (d := d) (y - x) x using 1
      ring_nf
    have hnormlt : euclideanNorm y < (3 : ℝ) ^ m := by
      exact lt_of_le_of_lt hnormy
        (by linarith only [hdist, hm, hr₀, euclideanNorm_nonneg x])
    intro i
    exact abs_lt.mp ((abs_coordinate_le_euclideanNorm y i).trans_lt hnormlt)
  have hinner : euclideanBall x (r₀ / 2) ⊆
      euclideanBall 0 (cubeBoundaryCutoffInnerRadius m) := by
    intro y hy
    have hdist := euclideanNorm_sub_lt_of_mem_euclideanBall
      (half_pos hr₀).le hy
    have hnormy : euclideanNorm y ≤ euclideanNorm (y - x) + euclideanNorm x := by
      convert euclideanNorm_add_le (d := d) (y - x) x using 1
      ring_nf
    have hhalf : euclideanNorm x + r₀ / 2 < (3 : ℝ) ^ m / 2 := by
      linarith only [hm, euclideanNorm_nonneg x, hr₀]
    have hnormlt : euclideanNorm (y - 0) < cubeBoundaryCutoffInnerRadius m := by
      simp only [sub_zero]
      unfold cubeBoundaryCutoffInnerRadius
      linarith only [hdist, hnormy, hhalf]
    change euclideanSqDist y 0 < cubeBoundaryCutoffInnerRadius m ^ 2
    rw [show euclideanSqDist y 0 = euclideanNorm (y - 0) ^ 2 by
      rw [euclideanNorm_sq]; rfl]
    exact (sq_lt_sq₀ (euclideanNorm_nonneg _)
      (by unfold cubeBoundaryCutoffInnerRadius; positivity)).2 hnormlt
  have hlayer : -cubeBoundaryCutoffInnerRadius m + 1 ≤
      -(euclideanNorm (x - 0) + r₀ / 2) := by
    simp only [sub_zero]
    unfold cubeBoundaryCutoffInnerRadius
    have hhalf : euclideanNorm x + r₀ / 2 + 1 ≤ (3 : ℝ) ^ m / 2 := by
      linarith only [hm, euclideanNorm_nonneg x, hr₀]
    linarith only [hhalf]
  have hdecay := A.abs_analyticCubeBoundaryRemainder_le_localized L mu m
    (x := x) hball hinner hlayer
  have hLupper := localizedInteriorUpper_streamBoundary_le M omega mu m
  have hLpos := localizedInteriorUpper_pos (mass := (mu : ℝ)) M.nu_pos
    (L.roughBound_nonneg 0 ((3 : ℝ) ^ m) (pow_nonneg (by norm_num) m))
    (L.smoothDivBound_nonneg 0 ((3 : ℝ) ^ m) (pow_nonneg (by norm_num) m))
  have hrate : c * 4 / ((m : ℝ) + 1) ≤
      agmonRate M.nu
        (localizedInteriorUpper M.nu (mu : ℝ)
          (L.roughBound 0 ((3 : ℝ) ^ m))
          (L.smoothDivBound 0 ((3 : ℝ) ^ m))) (mu : ℝ) * q := by
    unfold c agmonRate
    have hmpos : 0 < (m : ℝ) + 1 := by positivity
    have hden : 0 < 2 * Real.sqrt 2 *
        localizedInteriorUpper M.nu (mu : ℝ)
          (L.roughBound 0 ((3 : ℝ) ^ m))
          (L.smoothDivBound 0 ((3 : ℝ) ^ m)) := by positivity
    have hdenU : 2 * Real.sqrt 2 *
        localizedInteriorUpper M.nu (mu : ℝ)
          (L.roughBound 0 ((3 : ℝ) ^ m))
          (L.smoothDivBound 0 ((3 : ℝ) ^ m)) ≤
        (2 * Real.sqrt 2 * U) * ((m : ℝ) + 1) := by
      simpa only [mul_assoc, streamLocalizedSplitData] using!
        mul_le_mul_of_nonneg_left hLupper
          (mul_nonneg (by norm_num) (Real.sqrt_nonneg 2))
    have hnum : 0 ≤ Real.sqrt (M.nu * (mu : ℝ)) := Real.sqrt_nonneg _
    have hdiv := div_le_div_of_nonneg_left hnum hden hdenU
    have hq0 : 0 ≤ q := hq.le
    calc
      c * 4 / ((m : ℝ) + 1) =
          (Real.sqrt (M.nu * (mu : ℝ)) /
            ((2 * Real.sqrt 2 * U) * ((m : ℝ) + 1))) * q := by
        dsimp only [c]
        field_simp
      _ ≤ (Real.sqrt (M.nu * (mu : ℝ)) /
            (2 * Real.sqrt 2 *
              localizedInteriorUpper M.nu (mu : ℝ)
                (L.roughBound 0 ((3 : ℝ) ^ m))
                (L.smoothDivBound 0 ((3 : ℝ) ^ m)))) * q :=
        mul_le_mul_of_nonneg_right hdiv hq0
      _ = _ := by ring
  have hgap : (3 : ℝ) ^ m / 4 ≤
      -(euclideanNorm (x - 0) + r₀ / 2) -
        (-cubeBoundaryCutoffInnerRadius m + 1) := by
    simp only [sub_zero]
    unfold cubeBoundaryCutoffInnerRadius
    linarith only [hm]
  have hexp : Real.exp (-((agmonRate M.nu
      (localizedInteriorUpper M.nu (mu : ℝ)
        (L.roughBound 0 ((3 : ℝ) ^ m))
        (L.smoothDivBound 0 ((3 : ℝ) ^ m))) (mu : ℝ) * q) *
      (-(euclideanNorm (x - 0) + r₀ / 2) -
        (-cubeBoundaryCutoffInnerRadius m + 1)))) ≤
      Real.exp (-(c * (3 : ℝ) ^ m / ((m : ℝ) + 1))) := by
    apply Real.exp_le_exp.2
    apply neg_le_neg
    have hgap0 : 0 ≤ (3 : ℝ) ^ m / 4 := by positivity
    have hrate0 : 0 ≤ agmonRate M.nu
        (localizedInteriorUpper M.nu (mu : ℝ)
          (L.roughBound 0 ((3 : ℝ) ^ m))
          (L.smoothDivBound 0 ((3 : ℝ) ^ m))) (mu : ℝ) * q :=
      mul_nonneg (agmonRate_nonneg hLpos) hq.le
    have hmul := mul_le_mul hrate hgap hgap0 hrate0
    calc
      c * (3 : ℝ) ^ m / ((m : ℝ) + 1) =
          (c * 4 / ((m : ℝ) + 1)) * ((3 : ℝ) ^ m / 4) := by ring
      _ ≤ _ := hmul
  calc
    _ ≤ P m * Real.exp (-((agmonRate M.nu
          (localizedInteriorUpper M.nu (mu : ℝ)
            (L.roughBound 0 ((3 : ℝ) ^ m))
            (L.smoothDivBound 0 ((3 : ℝ) ^ m))) (mu : ℝ) * q) *
        (-(euclideanNorm (x - 0) + r₀ / 2) -
          (-cubeBoundaryCutoffInnerRadius m + 1)))) := by
      convert hdecay using 1
      simp only [A, L, r₀, P, alpha, q, streamWholeSpaceAnalyticData,
        streamLocalizedSplitData]
      ring_nf
    _ ≤ (C * ((m : ℝ) + 1) * ((3 : ℝ) ^ (d + 1)) ^ m) *
          Real.exp (-(c * (3 : ℝ) ^ m / ((m : ℝ) + 1))) := by
      exact mul_le_mul (hPC m) hexp (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg hC (by positivity)) (pow_nonneg (by norm_num) m))

/-- The analytic minimal resolvent of the stream coefficient has the exact
constant-one normalization. -/
theorem ofReal_mul_streamAnalyticMinimalResolvent_one_eq
    (M : ABKModel d) (omega : FullSample d M.gamma)
    (mu : PositiveShift) (x : Vec d) :
    ENNReal.ofReal (mu : ℝ) *
        (streamWholeSpaceAnalyticData M omega).analyticMinimalResolvent mu
          (fun _ : Vec d ↦ (1 : ℝ)) measurable_const
          (D := 1) (fun _ ↦ by norm_num) x = 1 := by
  let A := streamWholeSpaceAnalyticData M omega
  have ht := A.tendsto_analyticCubeResolvent mu
    (f := fun _ : Vec d ↦ (1 : ℝ)) measurable_const
    (fun _ ↦ by norm_num) (D := 1) (by norm_num) (fun _ ↦ by norm_num) x
  have htMul : Tendsto (fun m ↦ (mu : ℝ) *
      A.analyticCubeResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
        measurable_const (D := 1) (fun _ ↦ by norm_num) m x) atTop
      (nhds ((mu : ℝ) *
        (A.analyticMinimalResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
          measurable_const (D := 1) (fun _ ↦ by norm_num) x).toReal)) :=
    tendsto_const_nhds.mul ht
  have htSub : Tendsto (fun m ↦ 1 - (mu : ℝ) *
      A.analyticCubeResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
        measurable_const (D := 1) (fun _ ↦ by norm_num) m x) atTop
      (nhds (1 - (mu : ℝ) *
        (A.analyticMinimalResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
          measurable_const (D := 1) (fun _ ↦ by norm_num) x).toReal)) :=
    tendsto_const_nhds.sub htMul
  have htAbs := htSub.abs
  have hzero := tendsto_abs_streamAnalyticCubeBoundaryRemainder M omega mu x
  have habs : |1 - (mu : ℝ) *
      (A.analyticMinimalResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
        measurable_const (D := 1) (fun _ ↦ by norm_num) x).toReal| = 0 :=
    tendsto_nhds_unique htAbs hzero
  have hreal : (mu : ℝ) *
      (A.analyticMinimalResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
        measurable_const (D := 1) (fun _ ↦ by norm_num) x).toReal = 1 :=
    (sub_eq_zero.mp (abs_eq_zero.mp habs)).symm
  have hmin := A.analyticMinimalResolvent_ne_top mu
    (f := fun _ : Vec d ↦ (1 : ℝ)) measurable_const
    (fun _ ↦ by norm_num) (D := 1) (by norm_num) (fun _ ↦ by norm_num) x
  have hlhs : ENNReal.ofReal (mu : ℝ) *
      A.analyticMinimalResolvent mu (fun _ : Vec d ↦ (1 : ℝ))
        measurable_const (D := 1) (fun _ ↦ by norm_num) x ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmin
  apply (ENNReal.toReal_eq_toReal_iff' hlhs ENNReal.one_ne_top).mp
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal mu.property.le,
    ENNReal.toReal_one]
  simpa only [A] using hreal

end

end Algsuperdiff.Section5.Field
