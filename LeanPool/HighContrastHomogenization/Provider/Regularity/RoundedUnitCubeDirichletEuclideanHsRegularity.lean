/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.RoundedUnitCubeDirichletContinuousKIterationEnergyLimit
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ContinuousInterpolation.FullNormEquivalence

/-!
# High-contrast homogenization: Provider.Regularity.RoundedUnitCubeDirichletEuclideanHsRegularity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Rounded-reference Euclidean fractional regularity on the unit cube

The selected small positive order from the rounded affine iteration is
converted from its quadratic continuous-K energy to the exact Euclidean
fractional carrier and additive full norm.  The conversion keeps the datum
and solution membership statements internal to the proof: the caller
supplies only Euclidean `H^s` membership of the datum, while existence,
the weak equation, output membership, and the quantitative estimate are
all conclusions.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem unitCubeNormalizedEuclideanLpENorm_lt_top_roundedHs
    (F : UnitCubeEuclideanL2Field d) :
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm
        (2 : ℝ≥0∞) F < ∞ := by
  simpa only [BoundedMeasurableDomain.normalizedEuclideanLpENorm,
    BoundedMeasurableDomain.normalizedLpENorm] using
      F.euclideanMagnitudeMemL2.eLpNorm_lt_top

private theorem continuousKFullENorm_lt_top_of_memEuclideanHs_rounded
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d)
    (hF : MemEuclideanHs s F) :
    continuousKFullENorm s F < ∞ := by
  rw [continuousKFullENorm_eq, ENNReal.add_lt_top]
  exact ⟨unitCubeNormalizedEuclideanLpENorm_lt_top_roundedHs F,
    (memEuclideanHs_iff_continuousKSeminorm_lt_top s F).mp hF⟩

private theorem continuousKIntegral_rpow_half_sq
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    ((∫⁻ t in Set.Ioo (0 : ℝ) 1,
        continuousKSeminormIntegrand s.1 F t) ^ (1 / 2 : ℝ)) ^ 2 =
      ∫⁻ t in Set.Ioo (0 : ℝ) 1,
        continuousKSeminormIntegrand s.1 F t := by
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num

/-- When the selected scalar weight is at most one, the quadratic
continuous-K energy is controlled by twice the square of the additive
continuous-K full norm. -/
theorem unitCubeNormalizedContinuousKEnergy_le_two_mul_continuousKFullENorm_sq
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d)
    (hweight : ENNReal.ofReal (2 * s.1) ≤ 1) :
    unitCubeNormalizedContinuousKEnergy s F ≤
      2 * (continuousKFullENorm s F) ^ 2 := by
  let L : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm
      (2 : ℝ≥0∞) F
  let I : ℝ≥0∞ := ∫⁻ t in Set.Ioo (0 : ℝ) 1,
    continuousKSeminormIntegrand s.1 F t
  let K : ℝ≥0∞ := I ^ (1 / 2 : ℝ)
  have hKsq : K ^ 2 = I := by
    simpa only [K, I] using continuousKIntegral_rpow_half_sq s F
  have hLsq : L ^ 2 ≤ (L + K) ^ 2 := by
    exact pow_le_pow_left' (le_add_of_nonneg_right zero_le) 2
  have hI : I ≤ (L + K) ^ 2 := by
    rw [← hKsq]
    exact pow_le_pow_left' (le_add_of_nonneg_left zero_le) 2
  have hweightedI : ENNReal.ofReal (2 * s.1) * I ≤ (L + K) ^ 2 := by
    calc
      ENNReal.ofReal (2 * s.1) * I ≤ 1 * I := by
        simpa only [mul_comm] using mul_le_mul_right hweight I
      _ = I := one_mul I
      _ ≤ (L + K) ^ 2 := hI
  change L ^ 2 + ENNReal.ofReal (2 * s.1) * I ≤
    2 * (L + K) ^ 2
  calc
    L ^ 2 + ENNReal.ofReal (2 * s.1) * I ≤
        (L + K) ^ 2 + (L + K) ^ 2 :=
      add_le_add hLsq hweightedI
    _ = 2 * (L + K) ^ 2 := by ring

private theorem unitCubeNormalizedContinuousKEnergy_lt_top_of_memEuclideanHs
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d)
    (hweight : ENNReal.ofReal (2 * s.1) ≤ 1)
    (hF : MemEuclideanHs s F) :
    unitCubeNormalizedContinuousKEnergy s F < ∞ := by
  exact lt_of_le_of_lt
    (unitCubeNormalizedContinuousKEnergy_le_two_mul_continuousKFullENorm_sq
      s F hweight)
    (ENNReal.mul_lt_top (by norm_num)
      (ENNReal.pow_lt_top
        (continuousKFullENorm_lt_top_of_memEuclideanHs_rounded s F hF)))

/-- A positive continuous-K energy weight controls the additive
continuous-K full norm by the square root of the quadratic energy. -/
theorem continuousKFullENorm_le_mul_unitCubeNormalizedContinuousKEnergy_rpow
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d)
    (hweightZero : ENNReal.ofReal (2 * s.1) ≠ 0)
    (hweightTop : ENNReal.ofReal (2 * s.1) ≠ ∞) :
    continuousKFullENorm s F ≤
      (1 + (ENNReal.ofReal (2 * s.1))⁻¹ ^ (1 / 2 : ℝ)) *
        (unitCubeNormalizedContinuousKEnergy s F) ^ (1 / 2 : ℝ) := by
  let L : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm
      (2 : ℝ≥0∞) F
  let I : ℝ≥0∞ := ∫⁻ t in Set.Ioo (0 : ℝ) 1,
    continuousKSeminormIntegrand s.1 F t
  let p : ℝ≥0∞ := ENNReal.ofReal (2 * s.1)
  let E : ℝ≥0∞ := L ^ 2 + p * I
  have hLroot : (L ^ 2) ^ (1 / 2 : ℝ) = L := by
    simpa only [one_div] using!
      ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num) L
  have hL : L ≤ E ^ (1 / 2 : ℝ) := by
    calc
      L = (L ^ 2) ^ (1 / 2 : ℝ) := hLroot.symm
      _ ≤ E ^ (1 / 2 : ℝ) := by
        exact ENNReal.rpow_le_rpow (self_le_add_right (L ^ 2) (p * I))
          (by norm_num)
  have hIcancel : I = p⁻¹ * (p * I) := by
    symm
    exact ENNReal.inv_mul_cancel_left hweightZero hweightTop
  have hI : I ^ (1 / 2 : ℝ) ≤
      p⁻¹ ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) := by
    calc
      I ^ (1 / 2 : ℝ) = (p⁻¹ * (p * I)) ^ (1 / 2 : ℝ) := by
        exact congrArg (fun x : ℝ≥0∞ ↦ x ^ (1 / 2 : ℝ)) hIcancel
      _ = p⁻¹ ^ (1 / 2 : ℝ) * (p * I) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      _ ≤ p⁻¹ ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) := by
        gcongr
        exact self_le_add_left (p * I) (L ^ 2)
  change L + I ^ (1 / 2 : ℝ) ≤
    (1 + p⁻¹ ^ (1 / 2 : ℝ)) * E ^ (1 / 2 : ℝ)
  calc
    L + I ^ (1 / 2 : ℝ) ≤
        E ^ (1 / 2 : ℝ) +
          p⁻¹ ^ (1 / 2 : ℝ) * E ^ (1 / 2 : ℝ) :=
      add_le_add hL hI
    _ = (1 + p⁻¹ ^ (1 / 2 : ℝ)) * E ^ (1 / 2 : ℝ) := by
      ring

private theorem memEuclideanHs_of_unitCubeNormalizedContinuousKEnergy_lt_top
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d)
    (hweightPos : 0 < ENNReal.ofReal (2 * s.1))
    (henergy : unitCubeNormalizedContinuousKEnergy s F < ∞) :
    MemEuclideanHs s F := by
  have hweightZero : ENNReal.ofReal (2 * s.1) ≠ 0 := hweightPos.ne'
  have hweightTop : ENNReal.ofReal (2 * s.1) ≠ ∞ := ENNReal.ofReal_ne_top
  have hinvFinite : (ENNReal.ofReal (2 * s.1))⁻¹ < ∞ :=
    ENNReal.inv_lt_top.mpr hweightPos
  have hcoefficient :
      1 + (ENNReal.ofReal (2 * s.1))⁻¹ ^ (1 / 2 : ℝ) < ∞ :=
    ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top,
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hinvFinite.ne⟩
  have hfullFinite : continuousKFullENorm s F < ∞ :=
    lt_of_le_of_lt
      (continuousKFullENorm_le_mul_unitCubeNormalizedContinuousKEnergy_rpow
        s F hweightZero hweightTop)
      (ENNReal.mul_lt_top hcoefficient
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) henergy.ne))
  apply (memEuclideanHs_iff_continuousKSeminorm_lt_top s F).mpr
  apply lt_of_le_of_lt _ hfullFinite
  rw [continuousKFullENorm_eq]
  exact self_le_add_left _ _

/-- For one selected order below `1/12`, every rounded-reference
constant-coefficient divergence datum in exact Euclidean `H^s` has a
zero-trace weak response whose gradient remains in Euclidean `H^s`, with one
finite constant fixed before the matrix and datum. -/
theorem exists_roundedUnitCubeDirichletEuclideanHsRegularity
    (d : ℕ) [NeZero d] :
    ∃ s : FractionalOrder, s.1 < (1 : ℝ) / 12 ∧
      ∃ C : ℝ≥0∞, C < ∞ ∧
        ∀ (abar : Mat d) (hS : (symmPart abar).PosDef)
          (h : UnitCubeEuclideanL2Field d),
          MemEuclideanHs s h →
            ∃ u : H10Function (openCubeSet (originCube d 0)),
              IsZeroTraceDirichletRhsWeakSolution
                (constantCoeffField (roundedReferenceMatrix abar hS))
                (openCubeSet (originCube d 0)) u (fun x ↦ -h x) ∧
              MemEuclideanHs s (unitCubeGradientEuclideanL2Field u) ∧
              euclideanHsFullENorm s (unitCubeGradientEuclideanL2Field u) ≤
                C * euclideanHsFullENorm s h := by
  rcases exists_roundedUnitCubeDirichletContinuousKIterationEnergyLimit d with
    ⟨A, honeA, s, hs, hfactor, hcoefficient, honeCoefficient,
      B, honeB, hresponse⟩
  let p : ℝ≥0∞ := ENNReal.ofReal (2 * s.1)
  let D : ℝ≥0∞ := 8 * (ENNReal.ofReal B) ^ (2 * s.1)
  let R : ℝ≥0∞ := 1 + p⁻¹ ^ (1 / 2 : ℝ)
  let Kcmp : ℝ≥0∞ := continuousKEuclideanHsFullENormConstant s d
  let C : ℝ≥0∞ := Kcmp * (R * (2 * D) ^ (1 / 2 : ℝ)) * Kcmp
  have htwoSPos : 0 < 2 * s.1 := mul_pos (by norm_num) s.2.1
  have hpPos : 0 < p := by
    simpa only [p] using ENNReal.ofReal_pos.mpr htwoSPos
  have hpZero : p ≠ 0 := hpPos.ne'
  have hpTop : p ≠ ∞ := by
    simpa only [p] using ENNReal.ofReal_ne_top
  have htwoSLtOne : 2 * s.1 < 1 := by
    calc
      2 * s.1 < 2 * ((1 : ℝ) / 12) :=
        mul_lt_mul_of_pos_left hs (by norm_num)
      _ < 1 := by norm_num
  have hpLeOne : p ≤ 1 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal (1 : ℝ) by norm_num]
    simpa only [p] using ENNReal.ofReal_le_ofReal htwoSLtOne.le
  have hBpowFinite : (ENNReal.ofReal B) ^ (2 * s.1) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg
      (mul_nonneg (by norm_num) s.2.1.le) ENNReal.ofReal_ne_top
  have hDFinite : D < ∞ := by
    exact ENNReal.mul_lt_top (by norm_num) hBpowFinite
  have hpInvFinite : p⁻¹ < ∞ := ENNReal.inv_lt_top.mpr hpPos
  have hRFinite : R < ∞ := by
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.one_lt_top,
      ENNReal.rpow_lt_top_of_nonneg (by norm_num) hpInvFinite.ne⟩
  have hrootFinite : (2 * D) ^ (1 / 2 : ℝ) < ∞ :=
    ENNReal.rpow_lt_top_of_nonneg (by norm_num)
      (ENNReal.mul_lt_top (by norm_num) hDFinite).ne
  have hKcmpFinite : Kcmp < ∞ := by
    simpa only [Kcmp] using continuousKEuclideanHsFullENormConstant_lt_top s d
  have hCFinite : C < ∞ := by
    exact ENNReal.mul_lt_top
      (ENNReal.mul_lt_top hKcmpFinite (ENNReal.mul_lt_top hRFinite hrootFinite))
      hKcmpFinite
  refine ⟨s, hs, C, hCFinite, ?_⟩
  intro abar hS h hh
  have hhEnergy : unitCubeNormalizedContinuousKEnergy s h < ∞ :=
    unitCubeNormalizedContinuousKEnergy_lt_top_of_memEuclideanHs
      s h hpLeOne hh
  rcases hresponse abar hS h hhEnergy with
    ⟨u, hlimit, hweak, henergy, houtputEnergyFinite⟩
  let out : UnitCubeEuclideanL2Field d := unitCubeGradientEuclideanL2Field u
  have henergyD : unitCubeNormalizedContinuousKEnergy s out ≤
      D * unitCubeNormalizedContinuousKEnergy s h := by
    simpa only [out, D, mul_assoc] using henergy
  have henergyToFull : unitCubeNormalizedContinuousKEnergy s out ≤
      (2 * D) * (continuousKFullENorm s h) ^ 2 := by
    calc
      unitCubeNormalizedContinuousKEnergy s out ≤
          D * unitCubeNormalizedContinuousKEnergy s h := henergyD
      _ ≤ D * (2 * (continuousKFullENorm s h) ^ 2) := by
        gcongr
        exact
          unitCubeNormalizedContinuousKEnergy_le_two_mul_continuousKFullENorm_sq
            s h hpLeOne
      _ = (2 * D) * (continuousKFullENorm s h) ^ 2 := by ring
  have hfullK : continuousKFullENorm s out ≤
      (R * (2 * D) ^ (1 / 2 : ℝ)) * continuousKFullENorm s h := by
    have hrootSq : ((continuousKFullENorm s h) ^ 2) ^ (1 / 2 : ℝ) =
        continuousKFullENorm s h := by
      simpa only [one_div] using!
        ENNReal.pow_rpow_inv_natCast (n := 2) (by norm_num)
          (continuousKFullENorm s h)
    calc
      continuousKFullENorm s out ≤
          R * (unitCubeNormalizedContinuousKEnergy s out) ^ (1 / 2 : ℝ) := by
        simpa only [R, p] using
          continuousKFullENorm_le_mul_unitCubeNormalizedContinuousKEnergy_rpow
            s out hpZero hpTop
      _ ≤ R * (((2 * D) * (continuousKFullENorm s h) ^ 2) ^
          (1 / 2 : ℝ)) := by
        gcongr
      _ = R * ((2 * D) ^ (1 / 2 : ℝ) *
          ((continuousKFullENorm s h) ^ 2) ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      _ = (R * (2 * D) ^ (1 / 2 : ℝ)) * continuousKFullENorm s h := by
        rw [hrootSq]
        ring
  have hfinal : euclideanHsFullENorm s out ≤
      C * euclideanHsFullENorm s h := by
    calc
      euclideanHsFullENorm s out ≤ Kcmp * continuousKFullENorm s out := by
        simpa only [Kcmp] using
          euclideanHsFullENorm_le_mul_continuousKFullENorm s out
      _ ≤ Kcmp *
          ((R * (2 * D) ^ (1 / 2 : ℝ)) * continuousKFullENorm s h) := by
        gcongr
      _ ≤ Kcmp * ((R * (2 * D) ^ (1 / 2 : ℝ)) *
          (Kcmp * euclideanHsFullENorm s h)) := by
        gcongr
        simpa only [Kcmp] using
          continuousKFullENorm_le_mul_euclideanHsFullENorm s h
      _ = C * euclideanHsFullENorm s h := by
        simp only [C]
        ring
  refine ⟨u, hweak, ?_, ?_⟩
  · exact memEuclideanHs_of_unitCubeNormalizedContinuousKEnergy_lt_top
      s out hpPos (by simpa only [out] using houtputEnergyFinite)
  · simpa only [out] using hfinal

end

end HighContrast
end HCPolySupport
