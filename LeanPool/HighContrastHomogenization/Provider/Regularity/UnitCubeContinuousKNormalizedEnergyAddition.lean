/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CenteredCubeEuclideanHsFullNormAddition
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Fractional.ContinuousInterpolation.KInfimum

/-!
# High-contrast homogenization: Provider.Regularity.UnitCubeContinuousKNormalizedEnergyAddition

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Addition on the normalized unit-cube continuous K-energy

Pointwise addition is packaged on the proof-carrying unit-cube Euclidean
`L2` carrier.  Adding genuine coordinatewise `H1` competitors proves the
triangle inequality for the continuous `K`-functional.  Squaring that
inequality gives the dimension-free factor two for the normalized quadratic
energy.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The normalized quadratic continuous `K`-energy used by the unit-cube
Dirichlet estimates. -/
@[expose]
noncomputable def unitCubeNormalizedContinuousKEnergy
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F) ^ 2 +
    ENNReal.ofReal (2 * s.1) *
      ∫⁻ t in Set.Ioo (0 : ℝ) 1,
        continuousKSeminormIntegrand s.1 F t

/-- Evaluation formula for the normalized quadratic continuous `K`-energy. -/
theorem unitCubeNormalizedContinuousKEnergy_eq
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) :
    unitCubeNormalizedContinuousKEnergy s F =
      ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm
          (2 : ℝ≥0∞) F) ^ 2 +
        ENNReal.ofReal (2 * s.1) *
          ∫⁻ t in Set.Ioo (0 : ℝ) 1,
            continuousKSeminormIntegrand s.1 F t :=
  rfl

/-- Pointwise addition, packaged on the unit-cube Euclidean `L2` carrier. -/
@[expose]
noncomputable def unitCubeEuclideanL2FieldAdd
    (F G : UnitCubeEuclideanL2Field d) : UnitCubeEuclideanL2Field d where
  toField := fun x ↦ F x + G x
  euclideanMemL2 := by
    have h := F.euclideanMemL2.add G.euclideanMemL2
    convert h using 1
    funext x
    simpa only [HilbertVec.ofVecL_apply, Pi.add_apply] using
      (HilbertVec.ofVecL d).map_add (F.toField x) (G.toField x)

@[simp] theorem unitCubeEuclideanL2FieldAdd_apply
    (F G : UnitCubeEuclideanL2Field d) (x : Vec d) :
    unitCubeEuclideanL2FieldAdd F G x = F x + G x :=
  rfl

@[expose]
public noncomputable def continuousKCompetitorAdd
    (G V : ContinuousKCompetitor d) : ContinuousKCompetitor d where
  coord := fun i ↦ G.coord i + V.coord i

@[simp] private theorem continuousKCompetitorAdd_toField
    (G V : ContinuousKCompetitor d) (x : Vec d) :
    (continuousKCompetitorAdd G V).toField x = G.toField x + V.toField x := by
  ext i
  rfl

@[simp] private theorem continuousKCompetitorAdd_gradient
    (G V : ContinuousKCompetitor d) (x : Vec d) :
    (continuousKCompetitorAdd G V).gradient x = G.gradient x + V.gradient x := by
  ext i j
  rfl

private theorem euclideanNorm_add_le_continuousKAddition (x y : Vec d) :
    euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec]
  change ‖WithLp.toLp 2 (x + y)‖ ≤
    ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 y‖
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

private theorem matrixFrobeniusMagnitude_add_le_continuousKAddition
    (A B : Mat d) :
    matrixFrobeniusMagnitude (A + B) ≤
      matrixFrobeniusMagnitude A + matrixFrobeniusMagnitude B := by
  rw [matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat,
    matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat,
    matrixFrobeniusMagnitude_eq_norm_hilbertMat_ofMat]
  change ‖HilbertMat.ofMat A + HilbertMat.ofMat B‖ ≤
    ‖HilbertMat.ofMat A‖ + ‖HilbertMat.ofMat B‖
  exact norm_add_le (HilbertMat.ofMat A) (HilbertMat.ofMat B)

private theorem continuousKResidualNorm_add_le
    (F H : UnitCubeEuclideanL2Field d)
    (G V : ContinuousKCompetitor d) :
    continuousKResidualNorm (unitCubeEuclideanL2FieldAdd F H)
        (continuousKCompetitorAdd G V) ≤
      continuousKResidualNorm F G + continuousKResidualNorm H V := by
  let mu : Measure (Vec d) := (unitCenteredCubeDomain d).normalizedVolume
  let f : Vec d → ℝ := fun x ↦ euclideanNorm (F x - G.toField x)
  let h : Vec d → ℝ := fun x ↦ euclideanNorm (H x - V.toField x)
  have hfMem : MemLp f (2 : ℝ≥0∞) mu := by
    have hsub := F.euclideanMemL2.sub G.euclideanMemL2
    simpa only [f, mu, euclideanNorm_eq_norm_ofVec, HilbertVec.ofVec,
      PiLp.toLp_apply, Pi.sub_apply] using! hsub.norm
  have hhMem : MemLp h (2 : ℝ≥0∞) mu := by
    have hsub := H.euclideanMemL2.sub V.euclideanMemL2
    simpa only [h, mu, euclideanNorm_eq_norm_ofVec, HilbertVec.ofVec,
      PiLp.toLp_apply, Pi.sub_apply] using! hsub.norm
  have hENorm :
      eLpNorm
          (fun x ↦ euclideanNorm
            (unitCubeEuclideanL2FieldAdd F H x -
              (continuousKCompetitorAdd G V).toField x))
          (2 : ℝ≥0∞) mu ≤
        eLpNorm f (2 : ℝ≥0∞) mu + eLpNorm h (2 : ℝ≥0∞) mu := by
    calc
      eLpNorm
          (fun x ↦ euclideanNorm
            (unitCubeEuclideanL2FieldAdd F H x -
              (continuousKCompetitorAdd G V).toField x))
          (2 : ℝ≥0∞) mu ≤
        eLpNorm (f + h) (2 : ℝ≥0∞) mu := by
          refine eLpNorm_mono ?_ fun x ↦ ?_
          · have hsub := (unitCubeEuclideanL2FieldAdd F H).euclideanMemL2.sub
              (continuousKCompetitorAdd G V).euclideanMemL2
            simpa only [mu, euclideanNorm_eq_norm_ofVec, HilbertVec.ofVec,
              PiLp.toLp_apply, Pi.sub_apply] using! hsub.norm.aestronglyMeasurable
          simp only [unitCubeEuclideanL2FieldAdd_apply,
            continuousKCompetitorAdd_toField, Pi.add_apply, f, h,
            Real.norm_eq_abs, abs_of_nonneg (euclideanNorm_nonneg _),
            abs_of_nonneg
              (add_nonneg (euclideanNorm_nonneg _) (euclideanNorm_nonneg _))]
          have hsplit :
              (F x + H x) - (G.toField x + V.toField x) =
                (F x - G.toField x) + (H x - V.toField x) := by
            funext i
            simp only [Pi.add_apply, Pi.sub_apply]
            ring
          rw [hsplit]
          exact euclideanNorm_add_le_continuousKAddition _ _
      _ ≤ eLpNorm f (2 : ℝ≥0∞) mu +
          eLpNorm h (2 : ℝ≥0∞) mu :=
        eLpNorm_add_le (by norm_num)
  unfold continuousKResidualNorm
  change
    (eLpNorm
        (fun x ↦ euclideanNorm
          (unitCubeEuclideanL2FieldAdd F H x -
            (continuousKCompetitorAdd G V).toField x))
        (2 : ℝ≥0∞) mu).toReal ≤
      (eLpNorm f (2 : ℝ≥0∞) mu).toReal +
        (eLpNorm h (2 : ℝ≥0∞) mu).toReal
  calc
    (eLpNorm
        (fun x ↦ euclideanNorm
          (unitCubeEuclideanL2FieldAdd F H x -
            (continuousKCompetitorAdd G V).toField x))
        (2 : ℝ≥0∞) mu).toReal ≤
      (eLpNorm f (2 : ℝ≥0∞) mu +
        eLpNorm h (2 : ℝ≥0∞) mu).toReal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr
          ⟨hfMem.eLpNorm_ne_top, hhMem.eLpNorm_ne_top⟩) hENorm
    _ = (eLpNorm f (2 : ℝ≥0∞) mu).toReal +
        (eLpNorm h (2 : ℝ≥0∞) mu).toReal := by
      rw [ENNReal.toReal_add hfMem.eLpNorm_ne_top hhMem.eLpNorm_ne_top]

private theorem continuousKGradientNorm_add_le
    (G V : ContinuousKCompetitor d) :
    continuousKGradientNorm (continuousKCompetitorAdd G V) ≤
      continuousKGradientNorm G + continuousKGradientNorm V := by
  let mu : Measure (Vec d) := (unitCenteredCubeDomain d).normalizedVolume
  let g : Vec d → ℝ := fun x ↦ matrixFrobeniusMagnitude (G.gradient x)
  let v : Vec d → ℝ := fun x ↦ matrixFrobeniusMagnitude (V.gradient x)
  have hgMem : MemLp g (2 : ℝ≥0∞) mu := by
    simpa only [g, mu] using G.gradientFrobeniusMemL2
  have hvMem : MemLp v (2 : ℝ≥0∞) mu := by
    simpa only [v, mu] using V.gradientFrobeniusMemL2
  have hENorm :
      eLpNorm
          (fun x ↦ matrixFrobeniusMagnitude
            ((continuousKCompetitorAdd G V).gradient x))
          (2 : ℝ≥0∞) mu ≤
        eLpNorm g (2 : ℝ≥0∞) mu + eLpNorm v (2 : ℝ≥0∞) mu := by
    calc
      eLpNorm
          (fun x ↦ matrixFrobeniusMagnitude
            ((continuousKCompetitorAdd G V).gradient x))
          (2 : ℝ≥0∞) mu ≤
        eLpNorm (g + v) (2 : ℝ≥0∞) mu := by
          refine eLpNorm_mono ?_ fun x ↦ ?_
          · exact (continuousKCompetitorAdd G V).gradientFrobeniusMemL2.aestronglyMeasurable
          simp only [continuousKCompetitorAdd_gradient, Pi.add_apply, g, v,
            Real.norm_eq_abs,
            abs_of_nonneg (matrixFrobeniusMagnitude_nonneg _),
            abs_of_nonneg (add_nonneg
              (matrixFrobeniusMagnitude_nonneg _)
              (matrixFrobeniusMagnitude_nonneg _))]
          exact matrixFrobeniusMagnitude_add_le_continuousKAddition _ _
      _ ≤ eLpNorm g (2 : ℝ≥0∞) mu +
          eLpNorm v (2 : ℝ≥0∞) mu :=
        eLpNorm_add_le (by norm_num)
  unfold continuousKGradientNorm
    BoundedMeasurableDomain.normalizedLpNorm
    BoundedMeasurableDomain.normalizedLpFiniteENorm
    BoundedMeasurableDomain.normalizedLpENorm
  change
    (eLpNorm
        (fun x ↦ matrixFrobeniusMagnitude
          ((continuousKCompetitorAdd G V).gradient x))
        (2 : ℝ≥0∞) mu).toReal ≤
      (eLpNorm g (2 : ℝ≥0∞) mu).toReal +
        (eLpNorm v (2 : ℝ≥0∞) mu).toReal
  calc
    (eLpNorm
        (fun x ↦ matrixFrobeniusMagnitude
          ((continuousKCompetitorAdd G V).gradient x))
        (2 : ℝ≥0∞) mu).toReal ≤
      (eLpNorm g (2 : ℝ≥0∞) mu +
        eLpNorm v (2 : ℝ≥0∞) mu).toReal :=
      ENNReal.toReal_mono
        (ENNReal.add_ne_top.mpr
          ⟨hgMem.eLpNorm_ne_top, hvMem.eLpNorm_ne_top⟩) hENorm
    _ = (eLpNorm g (2 : ℝ≥0∞) mu).toReal +
        (eLpNorm v (2 : ℝ≥0∞) mu).toReal := by
      rw [ENNReal.toReal_add hgMem.eLpNorm_ne_top hvMem.eLpNorm_ne_top]

private theorem sqrt_sq_add_sq_add_le
    {a b c e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (he : 0 ≤ e) :
    Real.sqrt ((a + c) ^ 2 + (b + e) ^ 2) ≤
      Real.sqrt (a ^ 2 + b ^ 2) + Real.sqrt (c ^ 2 + e ^ 2) := by
  simpa [Real.sqrt_eq_rpow, Fin.sum_univ_two] using
    (Real.Lp_add_le_of_nonneg
      (s := Finset.univ)
      (f := ![a, b]) (g := ![c, e]) (p := (2 : ℝ))
      (by norm_num)
      (by intro i _hi; fin_cases i <;> assumption)
      (by intro i _hi; fin_cases i <;> assumption))

private theorem continuousKFunctionalCompetitorValue_add_le
    (t : ContinuousKScale) (F H : UnitCubeEuclideanL2Field d)
    (G V : ContinuousKCompetitor d) :
    continuousKFunctionalCompetitorValue t
        (unitCubeEuclideanL2FieldAdd F H)
        (continuousKCompetitorAdd G V) ≤
      continuousKFunctionalCompetitorValue t F G +
        continuousKFunctionalCompetitorValue t H V := by
  let rF : ℝ := continuousKResidualNorm F G
  let rH : ℝ := continuousKResidualNorm H V
  let gG : ℝ := continuousKGradientNorm G
  let gV : ℝ := continuousKGradientNorm V
  let rOut : ℝ := continuousKResidualNorm
    (unitCubeEuclideanL2FieldAdd F H) (continuousKCompetitorAdd G V)
  let gOut : ℝ := continuousKGradientNorm (continuousKCompetitorAdd G V)
  have hrF : 0 ≤ rF := continuousKResidualNorm_nonneg F G
  have hrH : 0 ≤ rH := continuousKResidualNorm_nonneg H V
  have hgG : 0 ≤ gG := continuousKGradientNorm_nonneg G
  have hgV : 0 ≤ gV := continuousKGradientNorm_nonneg V
  have hrOut : 0 ≤ rOut := continuousKResidualNorm_nonneg _ _
  have hgOut : 0 ≤ gOut := continuousKGradientNorm_nonneg _
  have hr : rOut ≤ rF + rH := by
    simpa only [rOut, rF, rH] using continuousKResidualNorm_add_le F H G V
  have hg : gOut ≤ gG + gV := by
    simpa only [gOut, gG, gV] using continuousKGradientNorm_add_le G V
  have ht : 0 ≤ t.1 := (ContinuousKScale.pos t).le
  unfold continuousKFunctionalCompetitorValue
  change Real.sqrt (rOut ^ 2 + t.1 ^ 2 * gOut ^ 2) ≤
    Real.sqrt (rF ^ 2 + t.1 ^ 2 * gG ^ 2) +
      Real.sqrt (rH ^ 2 + t.1 ^ 2 * gV ^ 2)
  calc
    Real.sqrt (rOut ^ 2 + t.1 ^ 2 * gOut ^ 2) ≤
        Real.sqrt ((rF + rH) ^ 2 +
          (t.1 * gG + t.1 * gV) ^ 2) := by
      apply Real.sqrt_le_sqrt
      calc
        rOut ^ 2 + t.1 ^ 2 * gOut ^ 2 ≤
            (rF + rH) ^ 2 + t.1 ^ 2 * (gG + gV) ^ 2 :=
          add_le_add
            ((sq_le_sq₀ hrOut (add_nonneg hrF hrH)).mpr hr)
            (mul_le_mul_of_nonneg_left
              ((sq_le_sq₀ hgOut (add_nonneg hgG hgV)).mpr hg)
              (sq_nonneg t.1))
        _ = (rF + rH) ^ 2 + (t.1 * gG + t.1 * gV) ^ 2 := by
          ring
    _ ≤ Real.sqrt (rF ^ 2 + (t.1 * gG) ^ 2) +
        Real.sqrt (rH ^ 2 + (t.1 * gV) ^ 2) :=
      sqrt_sq_add_sq_add_le hrF (mul_nonneg ht hgG)
        hrH (mul_nonneg ht hgV)
    _ = Real.sqrt (rF ^ 2 + t.1 ^ 2 * gG ^ 2) +
        Real.sqrt (rH ^ 2 + t.1 ^ 2 * gV ^ 2) := by
      ring_nf

/-- Pointwise addition obeys the triangle inequality for the continuous
`K`-functional. -/
theorem continuousKFunctional_add_le
    (t : ContinuousKScale) (F H : UnitCubeEuclideanL2Field d) :
    continuousKFunctional t (unitCubeEuclideanL2FieldAdd F H) ≤
      continuousKFunctional t F + continuousKFunctional t H := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hhalf : 0 < ε / 2 := div_pos hε (by norm_num)
  rcases exists_continuousKCompetitor_value_le_add t F hhalf with
    ⟨G, hG⟩
  rcases exists_continuousKCompetitor_value_le_add t H hhalf with
    ⟨V, hV⟩
  calc
    continuousKFunctional t (unitCubeEuclideanL2FieldAdd F H) ≤
        continuousKFunctionalCompetitorValue t
          (unitCubeEuclideanL2FieldAdd F H)
          (continuousKCompetitorAdd G V) :=
      continuousKFunctional_le_competitor _ _ _
    _ ≤ continuousKFunctionalCompetitorValue t F G +
        continuousKFunctionalCompetitorValue t H V :=
      continuousKFunctionalCompetitorValue_add_le t F H G V
    _ ≤ (continuousKFunctional t F + ε / 2) +
        (continuousKFunctional t H + ε / 2) := add_le_add hG hV
    _ = continuousKFunctional t F + continuousKFunctional t H + ε := by
      ring

/-- The continuous `K`-seminorm integrand of a pointwise sum is bounded by
twice the corresponding integrand of each summand. -/
theorem continuousKSeminormIntegrand_add_le
    (sigma : ℝ) (F H : UnitCubeEuclideanL2Field d) (t : ℝ) :
    continuousKSeminormIntegrand sigma
        (unitCubeEuclideanL2FieldAdd F H) t ≤
      2 * continuousKSeminormIntegrand sigma F t +
        2 * continuousKSeminormIntegrand sigma H t := by
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
  · let tau : ContinuousKScale := ⟨t, ⟨ht.1, ht.2.le⟩⟩
    let kOut : ℝ := continuousKFunctional tau
      (unitCubeEuclideanL2FieldAdd F H)
    let kF : ℝ := continuousKFunctional tau F
    let kH : ℝ := continuousKFunctional tau H
    have hkOut : 0 ≤ kOut := continuousKFunctional_nonneg _ _
    have hkF : 0 ≤ kF := continuousKFunctional_nonneg _ _
    have hkH : 0 ≤ kH := continuousKFunctional_nonneg _ _
    have hk : kOut ≤ kF + kH := by
      simpa only [kOut, kF, kH] using continuousKFunctional_add_le tau F H
    have hkSq : kOut ^ 2 ≤ 2 * kF ^ 2 + 2 * kH ^ 2 := by
      calc
        kOut ^ 2 ≤ (kF + kH) ^ 2 :=
          (sq_le_sq₀ hkOut (add_nonneg hkF hkH)).mpr hk
        _ ≤ 2 * (kF ^ 2 + kH ^ 2) := add_sq_le
        _ = 2 * kF ^ 2 + 2 * kH ^ 2 := by ring
    have hofReal : ENNReal.ofReal (kOut ^ 2) ≤
        2 * ENNReal.ofReal (kF ^ 2) + 2 * ENNReal.ofReal (kH ^ 2) := by
      calc
        ENNReal.ofReal (kOut ^ 2) ≤
            ENNReal.ofReal (2 * kF ^ 2 + 2 * kH ^ 2) :=
          ENNReal.ofReal_le_ofReal hkSq
        _ = ENNReal.ofReal (2 * kF ^ 2) +
            ENNReal.ofReal (2 * kH ^ 2) :=
          ENNReal.ofReal_add
            (mul_nonneg (by norm_num) (sq_nonneg kF))
            (mul_nonneg (by norm_num) (sq_nonneg kH))
        _ = 2 * ENNReal.ofReal (kF ^ 2) +
            2 * ENNReal.ofReal (kH ^ 2) := by
          rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
            ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
          norm_num
    unfold continuousKSeminormIntegrand continuousKFunctionalOnOpenScale
    simp only [dite_eq_left ht]
    change
      ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
          ENNReal.ofReal (kOut ^ 2) * ENNReal.ofReal t⁻¹ ≤
        2 * (ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
          ENNReal.ofReal (kF ^ 2) * ENNReal.ofReal t⁻¹) +
        2 * (ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
          ENNReal.ofReal (kH ^ 2) * ENNReal.ofReal t⁻¹)
    calc
      ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
          ENNReal.ofReal (kOut ^ 2) * ENNReal.ofReal t⁻¹ ≤
        ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
          (2 * ENNReal.ofReal (kF ^ 2) +
            2 * ENNReal.ofReal (kH ^ 2)) * ENNReal.ofReal t⁻¹ := by
          gcongr
      _ = 2 * (ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
          ENNReal.ofReal (kF ^ 2) * ENNReal.ofReal t⁻¹) +
        2 * (ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
          ENNReal.ofReal (kH ^ 2) * ENNReal.ofReal t⁻¹) := by
          ring
  · norm_num [continuousKSeminormIntegrand,
      continuousKFunctionalOnOpenScale, ht]

/-- The continuous `K`-seminorm integral of a pointwise sum is bounded by
twice the corresponding integral of each summand. -/
theorem continuousKSeminormIntegral_add_le
    (sigma : ℝ) (F H : UnitCubeEuclideanL2Field d) :
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        continuousKSeminormIntegrand sigma
          (unitCubeEuclideanL2FieldAdd F H) t) ≤
      2 * (∫⁻ t in Set.Ioo (0 : ℝ) 1,
          continuousKSeminormIntegrand sigma F t) +
        2 * (∫⁻ t in Set.Ioo (0 : ℝ) 1,
          continuousKSeminormIntegrand sigma H t) := by
  calc
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        continuousKSeminormIntegrand sigma
          (unitCubeEuclideanL2FieldAdd F H) t) ≤
      ∫⁻ t in Set.Ioo (0 : ℝ) 1,
        2 * continuousKSeminormIntegrand sigma F t +
          2 * continuousKSeminormIntegrand sigma H t :=
      lintegral_mono fun t ↦ continuousKSeminormIntegrand_add_le sigma F H t
    _ = 2 * (∫⁻ t in Set.Ioo (0 : ℝ) 1,
          continuousKSeminormIntegrand sigma F t) +
        2 * (∫⁻ t in Set.Ioo (0 : ℝ) 1,
          continuousKSeminormIntegrand sigma H t) := by
      rw [lintegral_add_left'
          ((continuousKSeminormIntegrand_aemeasurable sigma F).const_mul 2),
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞),
        lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]

@[expose]
public noncomputable def unitCubeEuclideanL2FieldToCenteredCubeZero
    (F : UnitCubeEuclideanL2Field d) : CenteredCubeEuclideanL2Field d 0 where
  toField := F
  euclideanMemL2 := by
    simpa only [centeredCubeDomain, unitCenteredCubeDomain] using F.euclideanMemL2

@[simp] private theorem unitCubeEuclideanL2FieldToCenteredCubeZero_apply
    (F : UnitCubeEuclideanL2Field d) (x : Vec d) :
    unitCubeEuclideanL2FieldToCenteredCubeZero F x = F x :=
  rfl

/-- Minkowski's inequality for pointwise addition on the normalized unit-cube
Euclidean `L2` term. -/
theorem unitCubeNormalizedEuclideanLpENorm_add_le
    (F H : UnitCubeEuclideanL2Field d) :
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        (unitCubeEuclideanL2FieldAdd F H) ≤
      (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F +
        (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) H := by
  have hbound := centeredCubeNormalizedEuclideanLpENorm_add_le
    (unitCubeEuclideanL2FieldToCenteredCubeZero F)
    (unitCubeEuclideanL2FieldToCenteredCubeZero H)
  simpa only [centeredCubeDomain, unitCenteredCubeDomain,
    centeredCubeEuclideanL2FieldAdd_apply,
    unitCubeEuclideanL2FieldToCenteredCubeZero_apply,
    unitCubeEuclideanL2FieldAdd_apply] using! hbound

private theorem ennreal_add_sq_le_two_sq_add_two_sq (a b : ℝ≥0∞) :
    (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  by_cases ha : a = ∞
  · subst a
    simp
  by_cases hb : b = ∞
  · subst b
    simp
  rw [← ENNReal.coe_toNNReal ha, ← ENNReal.coe_toNNReal hb]
  norm_cast
  calc
    (a.toNNReal + b.toNNReal) ^ 2 ≤
        2 * (a.toNNReal ^ 2 + b.toNNReal ^ 2) := add_sq_le
    _ = 2 * a.toNNReal ^ 2 + 2 * b.toNNReal ^ 2 := by ring

/-- Pointwise addition costs at most a factor two on each input in the
normalized quadratic continuous `K`-energy. -/
theorem unitCubeNormalizedContinuousKEnergy_add_le
    (s : FractionalOrder) (F H : UnitCubeEuclideanL2Field d) :
    unitCubeNormalizedContinuousKEnergy s
        (unitCubeEuclideanL2FieldAdd F H) ≤
      2 * unitCubeNormalizedContinuousKEnergy s F +
        2 * unitCubeNormalizedContinuousKEnergy s H := by
  let Lout : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
      (unitCubeEuclideanL2FieldAdd F H)
  let LF : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F
  let LH : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) H
  let Iout : ℝ≥0∞ :=
    ∫⁻ t in Set.Ioo (0 : ℝ) 1,
      continuousKSeminormIntegrand s.1
        (unitCubeEuclideanL2FieldAdd F H) t
  let IF : ℝ≥0∞ :=
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F t
  let IH : ℝ≥0∞ :=
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 H t
  let p : ℝ≥0∞ := ENNReal.ofReal (2 * s.1)
  have hL : Lout ≤ LF + LH := by
    simpa only [Lout, LF, LH] using unitCubeNormalizedEuclideanLpENorm_add_le F H
  have hLsq : Lout ^ 2 ≤ 2 * LF ^ 2 + 2 * LH ^ 2 := by
    calc
      Lout ^ 2 ≤ (LF + LH) ^ 2 := by gcongr
      _ ≤ 2 * LF ^ 2 + 2 * LH ^ 2 :=
        ennreal_add_sq_le_two_sq_add_two_sq LF LH
  have hI : Iout ≤ 2 * IF + 2 * IH := by
    simpa only [Iout, IF, IH] using continuousKSeminormIntegral_add_le s.1 F H
  change Lout ^ 2 + p * Iout ≤
    2 * (LF ^ 2 + p * IF) + 2 * (LH ^ 2 + p * IH)
  calc
    Lout ^ 2 + p * Iout ≤
        (2 * LF ^ 2 + 2 * LH ^ 2) + p * (2 * IF + 2 * IH) :=
      add_le_add hLsq (by
        simpa only [mul_comm] using mul_le_mul_left hI p)
    _ = 2 * (LF ^ 2 + p * IF) + 2 * (LH ^ 2 + p * IH) := by
      ring

end

end HighContrast
end HCPolySupport
