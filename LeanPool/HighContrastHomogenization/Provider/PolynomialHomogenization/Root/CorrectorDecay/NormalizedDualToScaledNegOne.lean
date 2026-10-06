/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.OrderComparison
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.H1HsTestEmbedding
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.Root.CorrectorDecay.FiniteNegSobolevPrice

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.Root.CorrectorDecay.NormalizedDualToScaledNegOne

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

private theorem sqrt_mul_rpow_two
    {K : ℝ} (hK : 0 ≤ K) (t : ℝ) :
    Real.sqrt (K * (3 : ℝ) ^ (2 * t)) =
      Real.sqrt K * (3 : ℝ) ^ t := by
  rw [Real.sqrt_mul hK]
  congr 1
  rw [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  ring

private theorem originCube_orderEmbedding_sqrt
    {d : ℕ} [NeZero d] (s : FractionalOrder)
    {K : ℝ} (hK : 0 < K)
    (hTest : ∀ (n : ℤ) (psi : Vec d → Vec d),
      IsLocalVecTest (openCubeSet (originCube d n)) psi →
        hsNormSq (openCubeSet (originCube d n)) s.1 psi ≤
          ENNReal.ofReal
            (K * (3 : ℝ) ^ (2 * (1 - s.1) * (n : ℝ))) *
            h1NormSq (openCubeSet (originCube d n)) psi)
    (n : ℤ) (F G : Vec d → Vec d) :
    negOneNorm (openCubeSet (originCube d n)) F +
        negOneNorm (openCubeSet (originCube d n)) G ≤
      ENNReal.ofReal (Real.sqrt K) *
        ENNReal.ofReal ((3 : ℝ) ^ ((1 - s.1) * (n : ℝ))) *
        (negSobolevNorm (openCubeSet (originCube d n)) s.1 F +
          negSobolevNorm (openCubeSet (originCube d n)) s.1 G) := by
  let Kscale : ℝ := K *
    (3 : ℝ) ^ (2 * (1 - s.1) * (n : ℝ))
  have hKscale : 0 < Kscale := by
    dsimp only [Kscale]
    positivity
  have hraw := negOneNorm_pair_le_of_hsNormSq_le_h1NormSq
    hKscale (hTest n) F G
  calc
    negOneNorm (openCubeSet (originCube d n)) F +
          negOneNorm (openCubeSet (originCube d n)) G ≤
        ENNReal.ofReal (Real.sqrt Kscale) *
          (negSobolevNorm (openCubeSet (originCube d n)) s.1 F +
            negSobolevNorm (openCubeSet (originCube d n)) s.1 G) := hraw
    _ = ENNReal.ofReal (Real.sqrt K) *
          ENNReal.ofReal ((3 : ℝ) ^ ((1 - s.1) * (n : ℝ))) *
          (negSobolevNorm (openCubeSet (originCube d n)) s.1 F +
            negSobolevNorm (openCubeSet (originCube d n)) s.1 G) := by
      have hsqrt : Real.sqrt Kscale = Real.sqrt K *
          (3 : ℝ) ^ ((1 - s.1) * (n : ℝ)) := by
        dsimp only [Kscale]
        rw [show 2 * (1 - s.1) * (n : ℝ) =
          2 * ((1 - s.1) * (n : ℝ)) by ring]
        exact sqrt_mul_rpow_two hK.le _
      rw [hsqrt]
      rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _)]

private theorem two_fractional_rows_le
    {d : ℕ} [NeZero d] (s : FractionalOrder)
    (hsHalf : s.1 < 1 / 2)
    (n : ℤ) (F G : Vec d → Vec d)
    (hF : MemVectorL2 (cubeSet (originCube d n)) F)
    (hG : MemVectorL2 (cubeSet (originCube d n)) G)
    {B : ℝ}
    (hrowF : cubeScaleNormalizedDualNegativeBesovVectorNormTwo
      (originCube d n) s.1 F ≤ B)
    (hrowG : cubeScaleNormalizedDualNegativeBesovVectorNormTwo
      (originCube d n) s.1 G ≤ B) :
    negSobolevNorm (openCubeSet (originCube d n)) s.1 F +
        negSobolevNorm (openCubeSet (originCube d n)) s.1 G ≤
      2 * fractionalDualToBesovConstant d *
        ENNReal.ofReal
          ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B) := by
  have hbaseF := negSobolevNorm_le_inverseWeight_normalizedDual
    (originCube d n) s.2.1 hsHalf F hF
  have hbaseG := negSobolevNorm_le_inverseWeight_normalizedDual
    (originCube d n) s.2.1 hsHalf G hG
  have hweight : 0 ≤
      (cubeBesovScaleWeight s.1 (originCube d n))⁻¹ :=
    inv_nonneg.mpr (cubeBesovScaleWeight_nonneg _ _)
  have hmulF :
      (cubeBesovScaleWeight s.1 (originCube d n))⁻¹ *
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube d n) s.1 F ≤
        (cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B :=
    mul_le_mul_of_nonneg_left hrowF hweight
  have hmulG :
      (cubeBesovScaleWeight s.1 (originCube d n))⁻¹ *
          cubeScaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube d n) s.1 G ≤
        (cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B :=
    mul_le_mul_of_nonneg_left hrowG hweight
  have hBF : negSobolevNorm (openCubeSet (originCube d n)) s.1 F ≤
      fractionalDualToBesovConstant d * ENNReal.ofReal
        ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B) := by
    calc
      _ ≤ fractionalDualToBesovConstant d * ENNReal.ofReal
          ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ *
            cubeScaleNormalizedDualNegativeBesovVectorNormTwo
              (originCube d n) s.1 F) := hbaseF
      _ ≤ fractionalDualToBesovConstant d * ENNReal.ofReal
          ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B) := by
        calc
          _ = ENNReal.ofReal
                ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ *
                  cubeScaleNormalizedDualNegativeBesovVectorNormTwo
                    (originCube d n) s.1 F) *
              fractionalDualToBesovConstant d := mul_comm _ _
          _ ≤ ENNReal.ofReal
                ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B) *
              fractionalDualToBesovConstant d :=
            mul_le_mul_left (ENNReal.ofReal_le_ofReal hmulF) _
          _ = _ := mul_comm _ _
  have hBG : negSobolevNorm (openCubeSet (originCube d n)) s.1 G ≤
      fractionalDualToBesovConstant d * ENNReal.ofReal
        ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B) := by
    calc
      _ ≤ fractionalDualToBesovConstant d * ENNReal.ofReal
          ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ *
            cubeScaleNormalizedDualNegativeBesovVectorNormTwo
              (originCube d n) s.1 G) := hbaseG
      _ ≤ fractionalDualToBesovConstant d * ENNReal.ofReal
          ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B) := by
        calc
          _ = ENNReal.ofReal
                ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ *
                  cubeScaleNormalizedDualNegativeBesovVectorNormTwo
                    (originCube d n) s.1 G) *
              fractionalDualToBesovConstant d := mul_comm _ _
          _ ≤ ENNReal.ofReal
                ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B) *
              fractionalDualToBesovConstant d :=
            mul_le_mul_left (ENNReal.ofReal_le_ofReal hmulG) _
          _ = _ := mul_comm _ _
  calc
    negSobolevNorm (openCubeSet (originCube d n)) s.1 F +
          negSobolevNorm (openCubeSet (originCube d n)) s.1 G ≤
        fractionalDualToBesovConstant d *
            ENNReal.ofReal
              ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B) +
          fractionalDualToBesovConstant d *
            ENNReal.ofReal
              ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B) :=
      add_le_add hBF hBG
    _ = 2 * fractionalDualToBesovConstant d *
          ENNReal.ofReal
            ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B) := by ring

/-- At one origin-cube scale, two scale-normalized full-dual rows control the
inverse-side-length normalized negative-one pair with a finite constant that
depends only on dimension and fractional order. -/
private theorem memVectorL2_toVec_hilbertVectorL2
    {d : ℕ} {V : Set (Vec d)} (F : HilbertVectorL2 V) :
    MemVectorL2 V (fun x ↦ (F x).toVec) := by
  exact MemLp.ae_eq
    (coeFn_hilbertVectorL2ToVectorL2 (U := V) F)
    (Lp.memLp (hilbertVectorL2ToVectorL2 (U := V) F))

theorem exists_scaledNegOne_pair_le_normalizedDualRows
    (d : ℕ) [NeZero d] (s : FractionalOrder) (hsHalf : s.1 < 1 / 2) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ 0 < C ∧
      ∀ (n : ℤ)
        (F G : HilbertVectorL2 (openCubeSet (originCube d n)))
        (B : ℝ),
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube d n) s.1 (fun x ↦ (F x).toVec) ≤ B →
        cubeScaleNormalizedDualNegativeBesovVectorNormTwo
            (originCube d n) s.1 (fun x ↦ (G x).toVec) ≤ B →
        triadicScaledNegOneNorm n F + triadicScaledNegOneNorm n G ≤
          C * ENNReal.ofReal B := by
  obtain ⟨K, hK, hTest⟩ := exists_hsNormSq_le_h1NormSq d s
  let C₀ : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt K) *
    (2 * fractionalDualToBesovConstant d)
  let C : ℝ≥0∞ := 1 + C₀
  have hC₀top : C₀ < ∞ := by
    dsimp only [C₀]
    exact ENNReal.mul_lt_top (ENNReal.ofReal_lt_top)
      (ENNReal.mul_lt_top (by norm_num)
        (fractionalDualToBesovConstant_lt_top d))
  have hCtop : C < ∞ := by
    dsimp only [C]
    exact ENNReal.add_lt_top.2 ⟨ENNReal.one_lt_top, hC₀top⟩
  have hCpos : 0 < C := by
    dsimp only [C]
    exact zero_lt_one.trans_le (le_add_right le_rfl)
  refine ⟨C, hCtop, hCpos, ?_⟩
  intro n F G B hrowF hrowG
  let f : Vec d → Vec d := fun x ↦ (F x).toVec
  let hF : MemVectorL2 (cubeSet (originCube d n)) f := by
    simpa only [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
      memVectorL2_toVec_hilbertVectorL2 F
  let h : Vec d → Vec d := fun x ↦ (G x).toVec
  let hG : MemVectorL2 (cubeSet (originCube d n)) h := by
    simpa only [MemVectorL2, volumeMeasureOn,
      volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] using
      memVectorL2_toVec_hilbertVectorL2 G
  have hOrder := originCube_orderEmbedding_sqrt s hK hTest n f h
  have hFrac := two_fractional_rows_le s hsHalf n f h hF hG
    (by simpa only [f] using hrowF) (by simpa only [h] using hrowG)
  have hscale := printOrder_twoRow_feeds_v2_scale n s.1
    (ENNReal.ofReal (Real.sqrt K))
    (2 * fractionalDualToBesovConstant d *
      ENNReal.ofReal
        ((cubeBesovScaleWeight s.1 (originCube d n))⁻¹ * B))
    f h (by simpa only [mul_assoc] using hOrder) hFrac
  rw [inverse_originCubeBesovWeight] at hscale
  have hcancel :
      ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * (n : ℝ))) *
          ENNReal.ofReal
            (((3 : ℝ) ^ (s.1 * (n : ℝ))) * B) =
        ENNReal.ofReal B := by
    have hreal : (3 : ℝ) ^ (-s.1 * (n : ℝ)) *
        (((3 : ℝ) ^ (s.1 * (n : ℝ))) * B) = B := by
      calc
        _ = ((3 : ℝ) ^ (-s.1 * (n : ℝ)) *
            (3 : ℝ) ^ (s.1 * (n : ℝ))) * B := by ring
        _ = (3 : ℝ) ^
            (-s.1 * (n : ℝ) + s.1 * (n : ℝ)) * B := by
          rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
        _ = B := by norm_num
    rw [← ENNReal.ofReal_mul
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _)]
    exact congrArg ENNReal.ofReal hreal
  calc
    triadicScaledNegOneNorm n F + triadicScaledNegOneNorm n G =
        ENNReal.ofReal (((3 : ℝ) ^ n)⁻¹) *
          (negOneNorm (openCubeSet (originCube d n)) f +
            negOneNorm (openCubeSet (originCube d n)) h) := by
      unfold triadicScaledNegOneNorm localNegOneNorm
      rw [mul_add]
    _ ≤
        ENNReal.ofReal (Real.sqrt K) *
          ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * (n : ℝ))) *
          (2 * fractionalDualToBesovConstant d *
            ENNReal.ofReal
              (((3 : ℝ) ^ (s.1 * (n : ℝ))) * B)) := by
      simpa only [mul_add, mul_assoc] using! hscale
    _ = C₀ * ENNReal.ofReal B := by
      dsimp only [C₀]
      calc
        ENNReal.ofReal (Real.sqrt K) *
              ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * (n : ℝ))) *
              (2 * fractionalDualToBesovConstant d *
                ENNReal.ofReal
                  (((3 : ℝ) ^ (s.1 * (n : ℝ))) * B)) =
            ENNReal.ofReal (Real.sqrt K) *
              (2 * fractionalDualToBesovConstant d) *
              (ENNReal.ofReal ((3 : ℝ) ^ (-s.1 * (n : ℝ))) *
                ENNReal.ofReal
                  (((3 : ℝ) ^ (s.1 * (n : ℝ))) * B)) := by ac_rfl
        _ = ENNReal.ofReal (Real.sqrt K) *
              (2 * fractionalDualToBesovConstant d) * ENNReal.ofReal B := by
          rw [hcancel]
    _ ≤ C * ENNReal.ofReal B := by
      exact mul_le_mul_left (by
        dsimp only [C]
        exact le_add_left le_rfl) _

end

end HighContrast
end HCPolySupport
