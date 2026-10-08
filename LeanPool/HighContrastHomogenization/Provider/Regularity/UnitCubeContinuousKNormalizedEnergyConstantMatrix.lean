/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CenteredCubeEuclideanHsFullNormConstantMatrix
public import LeanPool.HighContrastHomogenization.Provider.Regularity.UnitCubeDirichletContinuousKSmallOrder

/-!
# High-contrast homogenization:
Provider.Regularity.UnitCubeContinuousKNormalizedEnergyConstantMatrix

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Constant matrices on the normalized unit-cube continuous K-energy

Constant matrix multiplication acts on both the normalized Euclidean `L²`
term and every genuine `H¹` competitor in the continuous `K`-functional.
The resulting quadratic energy is bounded by the square of the Euclidean
matrix operator norm.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open scoped BigOperators ENNReal Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

/-- Pointwise constant-matrix multiplication, packaged on the unit-cube
Euclidean `L²` carrier. -/
@[expose]
noncomputable def unitCubeEuclideanL2FieldConstMatrixMul
    (A : Mat d) (F : UnitCubeEuclideanL2Field d) :
    UnitCubeEuclideanL2Field d where
  toField := fun x ↦ matVecMul A (F x)
  euclideanMemL2 := by
    have h := F.euclideanMemL2.continuousLinearMap_comp (HilbertVec.applyMat A)
    simpa only [Function.comp_apply, HilbertVec.applyMat_apply,
      HilbertVec.toVec_ofVec] using h

@[simp] theorem unitCubeEuclideanL2FieldConstMatrixMul_apply
    (A : Mat d) (F : UnitCubeEuclideanL2Field d) (x : Vec d) :
    unitCubeEuclideanL2FieldConstMatrixMul A F x = matVecMul A (F x) :=
  rfl

private theorem h1Function_finset_sum_toFun
    {iota : Type*} {U : Set (Vec d)} (s : Finset iota)
    (f : iota → H1Function U) :
    (∑ i ∈ s, f i).toFun = fun x ↦ ∑ i ∈ s, (f i).toFun x := by
  classical
  induction s using Finset.induction with
  | empty =>
      funext x
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      funext x
      simp only [H1Function.add_toFun, Finset.sum_insert ha, ih]

private theorem h1Function_finset_sum_grad
    {iota : Type*} {U : Set (Vec d)} (s : Finset iota)
    (f : iota → H1Function U) :
    (∑ i ∈ s, f i).grad = fun x ↦ ∑ i ∈ s, (f i).grad x := by
  classical
  induction s using Finset.induction with
  | empty =>
      funext x
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      funext x
      simp only [H1Function.add_grad, Finset.sum_insert ha, ih]

/-- Apply the constant matrix `A` to a continuous `K`-functional competitor by taking
linear combinations of its `H¹` coordinates. -/
@[expose]
public noncomputable def continuousKCompetitorConstMatrixMul
    (A : Mat d) (G : ContinuousKCompetitor d) : ContinuousKCompetitor d where
  coord := fun i ↦ ∑ j : Fin d, (A i j) • G.coord j

@[simp] private theorem continuousKCompetitorConstMatrixMul_toField
    (A : Mat d) (G : ContinuousKCompetitor d) (x : Vec d) :
    (continuousKCompetitorConstMatrixMul A G).toField x =
      matVecMul A (G.toField x) := by
  classical
  ext i
  change (∑ j : Fin d, (A i j) • G.coord j).toFun x = _
  rw [h1Function_finset_sum_toFun Finset.univ]
  simp only [H1Function.smul_toFun]
  rfl

@[simp] private theorem continuousKCompetitorConstMatrixMul_gradient
    (A : Mat d) (G : ContinuousKCompetitor d) (x : Vec d) :
    (continuousKCompetitorConstMatrixMul A G).gradient x =
      A * G.gradient x := by
  classical
  ext i j
  change (∑ k : Fin d, (A i k) • G.coord k).grad x j = _
  rw [h1Function_finset_sum_grad Finset.univ]
  simp only [H1Function.smul_grad, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Matrix.mul_apply,
    ContinuousKCompetitor.gradient_apply]

private theorem matrixFrobeniusMagnitude_matMul_le
    (A B : Mat d) :
    matrixFrobeniusMagnitude (A * B) ≤
      ‖A‖ * matrixFrobeniusMagnitude B := by
  apply (sq_le_sq₀ (matrixFrobeniusMagnitude_nonneg (A * B))
    (mul_nonneg (norm_nonneg A) (matrixFrobeniusMagnitude_nonneg B))).mp
  rw [sq_matrixFrobeniusMagnitude, mul_pow, sq_matrixFrobeniusMagnitude]
  calc
    (∑ i : Fin d, ∑ j : Fin d, ((A * B) i j) ^ 2) =
        ∑ j : Fin d, ∑ i : Fin d, ((A * B) i j) ^ 2 :=
      Finset.sum_comm
    _ ≤ ∑ j : Fin d, ‖A‖ ^ 2 * ∑ i : Fin d, (B i j) ^ 2 := by
      apply Finset.sum_le_sum
      intro j _hj
      simpa only [Matrix.mul_apply, matVecMul, vecNormSq, vecDot, pow_two] using
        vecNormSq_matVecMul_le A (fun i ↦ B i j)
    _ = ‖A‖ ^ 2 * ∑ j : Fin d, ∑ i : Fin d, (B i j) ^ 2 := by
      rw [Finset.mul_sum]
    _ = ‖A‖ ^ 2 * ∑ i : Fin d, ∑ j : Fin d, (B i j) ^ 2 := by
      congr 1
      exact Finset.sum_comm

private theorem continuousKResidualNorm_constMatrixMul_le
    (A : Mat d) (F : UnitCubeEuclideanL2Field d)
    (G : ContinuousKCompetitor d) :
    continuousKResidualNorm (unitCubeEuclideanL2FieldConstMatrixMul A F)
        (continuousKCompetitorConstMatrixMul A G) ≤
      ‖A‖ * continuousKResidualNorm F G := by
  let mu : Measure (Vec d) := (unitCenteredCubeDomain d).normalizedVolume
  have hinputMem : MemLp
      (fun x ↦ euclideanNorm (F x - G.toField x)) (2 : ℝ≥0∞) mu := by
    have hsub := F.euclideanMemL2.sub G.euclideanMemL2
    simpa only [mu, euclideanNorm_eq_norm_ofVec, HilbertVec.ofVec,
      PiLp.toLp_apply, Pi.sub_apply] using! hsub.norm
  have hpoint : ∀ x : Vec d,
      euclideanNorm
          (unitCubeEuclideanL2FieldConstMatrixMul A F x -
            (continuousKCompetitorConstMatrixMul A G).toField x) ≤
        ‖A‖ * euclideanNorm (F x - G.toField x) := by
    intro x
    simpa only [unitCubeEuclideanL2FieldConstMatrixMul_apply,
      continuousKCompetitorConstMatrixMul_toField, matVecMul_sub_vec] using
        euclideanNorm_matVecMul_le_l2_opNorm A (F x - G.toField x)
  have hENorm :
      eLpNorm
          (fun x ↦ euclideanNorm
            (unitCubeEuclideanL2FieldConstMatrixMul A F x -
              (continuousKCompetitorConstMatrixMul A G).toField x))
          (2 : ℝ≥0∞) mu ≤
        ENNReal.ofReal ‖A‖ *
          eLpNorm (fun x ↦ euclideanNorm (F x - G.toField x))
            (2 : ℝ≥0∞) mu := by
    have hmeas : AEStronglyMeasurable
        (fun x ↦ euclideanNorm
          (unitCubeEuclideanL2FieldConstMatrixMul A F x -
            (continuousKCompetitorConstMatrixMul A G).toField x)) mu := by
      have hsub := (unitCubeEuclideanL2FieldConstMatrixMul A F).euclideanMemL2.sub
        (continuousKCompetitorConstMatrixMul A G).euclideanMemL2
      simpa only [mu, euclideanNorm_eq_norm_ofVec, HilbertVec.ofVec,
        PiLp.toLp_apply, Pi.sub_apply] using! hsub.norm.aestronglyMeasurable
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul hmeas
    exact _root_.Filter.Eventually.of_forall fun x ↦ by
      simpa only [Real.norm_eq_abs,
        abs_of_nonneg (euclideanNorm_nonneg _)] using hpoint x
  unfold continuousKResidualNorm
  change
    (eLpNorm
        (fun x ↦ euclideanNorm
          (unitCubeEuclideanL2FieldConstMatrixMul A F x -
            (continuousKCompetitorConstMatrixMul A G).toField x))
        (2 : ℝ≥0∞) mu).toReal ≤
      ‖A‖ *
        (eLpNorm (fun x ↦ euclideanNorm (F x - G.toField x))
          (2 : ℝ≥0∞) mu).toReal
  calc
    (eLpNorm
        (fun x ↦ euclideanNorm
          (unitCubeEuclideanL2FieldConstMatrixMul A F x -
            (continuousKCompetitorConstMatrixMul A G).toField x))
        (2 : ℝ≥0∞) mu).toReal ≤
      (ENNReal.ofReal ‖A‖ *
        eLpNorm (fun x ↦ euclideanNorm (F x - G.toField x))
          (2 : ℝ≥0∞) mu).toReal :=
      ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hinputMem.eLpNorm_ne_top)
        hENorm
    _ = ‖A‖ *
        (eLpNorm (fun x ↦ euclideanNorm (F x - G.toField x))
          (2 : ℝ≥0∞) mu).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg A)]

private theorem continuousKGradientNorm_constMatrixMul_le
    (A : Mat d) (G : ContinuousKCompetitor d) :
    continuousKGradientNorm (continuousKCompetitorConstMatrixMul A G) ≤
      ‖A‖ * continuousKGradientNorm G := by
  let mu : Measure (Vec d) := (unitCenteredCubeDomain d).normalizedVolume
  have hENorm :
      eLpNorm
          (fun x ↦ matrixFrobeniusMagnitude
            ((continuousKCompetitorConstMatrixMul A G).gradient x))
          (2 : ℝ≥0∞) mu ≤
        ENNReal.ofReal ‖A‖ *
          eLpNorm (fun x ↦ matrixFrobeniusMagnitude (G.gradient x))
            (2 : ℝ≥0∞) mu := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul
      (continuousKCompetitorConstMatrixMul A G).gradientFrobeniusMemL2.aestronglyMeasurable
    exact _root_.Filter.Eventually.of_forall fun x ↦ by
      simpa only [continuousKCompetitorConstMatrixMul_gradient,
        Real.norm_eq_abs,
        abs_of_nonneg (matrixFrobeniusMagnitude_nonneg _)] using
          matrixFrobeniusMagnitude_matMul_le A (G.gradient x)
  unfold continuousKGradientNorm
    BoundedMeasurableDomain.normalizedLpNorm
    BoundedMeasurableDomain.normalizedLpFiniteENorm
    BoundedMeasurableDomain.normalizedLpENorm
  change
    (eLpNorm
        (fun x ↦ matrixFrobeniusMagnitude
          ((continuousKCompetitorConstMatrixMul A G).gradient x))
        (2 : ℝ≥0∞) mu).toReal ≤
      ‖A‖ *
        (eLpNorm (fun x ↦ matrixFrobeniusMagnitude (G.gradient x))
          (2 : ℝ≥0∞) mu).toReal
  calc
    (eLpNorm
        (fun x ↦ matrixFrobeniusMagnitude
          ((continuousKCompetitorConstMatrixMul A G).gradient x))
        (2 : ℝ≥0∞) mu).toReal ≤
      (ENNReal.ofReal ‖A‖ *
        eLpNorm (fun x ↦ matrixFrobeniusMagnitude (G.gradient x))
          (2 : ℝ≥0∞) mu).toReal :=
      ENNReal.toReal_mono
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
          G.gradientFrobeniusMemL2.eLpNorm_ne_top)
        hENorm
    _ = ‖A‖ *
        (eLpNorm (fun x ↦ matrixFrobeniusMagnitude (G.gradient x))
          (2 : ℝ≥0∞) mu).toReal := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (norm_nonneg A)]

private theorem continuousKFunctionalCompetitorValue_constMatrixMul_le
    (t : ContinuousKScale) (A : Mat d) (F : UnitCubeEuclideanL2Field d)
    (G : ContinuousKCompetitor d) :
    continuousKFunctionalCompetitorValue t
        (unitCubeEuclideanL2FieldConstMatrixMul A F)
        (continuousKCompetitorConstMatrixMul A G) ≤
      ‖A‖ * continuousKFunctionalCompetitorValue t F G := by
  have hresidual := continuousKResidualNorm_constMatrixMul_le A F G
  have hgradient := continuousKGradientNorm_constMatrixMul_le A G
  have hresidualSq :
      continuousKResidualNorm (unitCubeEuclideanL2FieldConstMatrixMul A F)
          (continuousKCompetitorConstMatrixMul A G) ^ 2 ≤
        (‖A‖ * continuousKResidualNorm F G) ^ 2 :=
    (sq_le_sq₀
      (continuousKResidualNorm_nonneg
        (unitCubeEuclideanL2FieldConstMatrixMul A F)
        (continuousKCompetitorConstMatrixMul A G))
      (mul_nonneg (norm_nonneg A) (continuousKResidualNorm_nonneg F G))).mpr
        hresidual
  have hgradientSq :
      continuousKGradientNorm (continuousKCompetitorConstMatrixMul A G) ^ 2 ≤
        (‖A‖ * continuousKGradientNorm G) ^ 2 :=
    (sq_le_sq₀
      (continuousKGradientNorm_nonneg
        (continuousKCompetitorConstMatrixMul A G))
      (mul_nonneg (norm_nonneg A) (continuousKGradientNorm_nonneg G))).mpr
        hgradient
  apply (sq_le_sq₀
    (continuousKFunctionalCompetitorValue_nonneg t
      (unitCubeEuclideanL2FieldConstMatrixMul A F)
      (continuousKCompetitorConstMatrixMul A G))
    (mul_nonneg (norm_nonneg A)
      (continuousKFunctionalCompetitorValue_nonneg t F G))).mp
  unfold continuousKFunctionalCompetitorValue
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg t.1) (sq_nonneg _))),
    mul_pow,
    Real.sq_sqrt (add_nonneg (sq_nonneg _)
      (mul_nonneg (sq_nonneg t.1) (sq_nonneg _)))]
  calc
    continuousKResidualNorm (unitCubeEuclideanL2FieldConstMatrixMul A F)
          (continuousKCompetitorConstMatrixMul A G) ^ 2 +
        t.1 ^ 2 *
          continuousKGradientNorm (continuousKCompetitorConstMatrixMul A G) ^ 2 ≤
      (‖A‖ * continuousKResidualNorm F G) ^ 2 +
        t.1 ^ 2 * (‖A‖ * continuousKGradientNorm G) ^ 2 :=
      add_le_add hresidualSq
        (mul_le_mul_of_nonneg_left hgradientSq (sq_nonneg t.1))
    _ = ‖A‖ ^ 2 *
        (continuousKResidualNorm F G ^ 2 +
          t.1 ^ 2 * continuousKGradientNorm G ^ 2) := by
      ring

private theorem continuousKFunctional_le_of_forall_competitorValue_le
    (t : ContinuousKScale) (C : ℝ) (F H : UnitCubeEuclideanL2Field d)
    (hC : 0 ≤ C)
    (hcompetitor : ∀ G : ContinuousKCompetitor d,
      ∃ V : ContinuousKCompetitor d,
        continuousKFunctionalCompetitorValue t F V ≤
          C * continuousKFunctionalCompetitorValue t H G) :
    continuousKFunctional t F ≤ C * continuousKFunctional t H := by
  by_cases hCzero : C = 0
  · rcases hcompetitor default with ⟨V, hV⟩
    have hout : continuousKFunctional t F ≤ 0 := by
      calc
        continuousKFunctional t F ≤
            continuousKFunctionalCompetitorValue t F V :=
          continuousKFunctional_le_competitor t F V
        _ ≤ 0 := by simpa only [hCzero, zero_mul] using hV
    simpa only [hCzero, zero_mul] using hout
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hCzero)
    have hdiv : continuousKFunctional t F / C ≤
        continuousKFunctional t H := by
      unfold continuousKFunctional
      refine le_csInf (continuousKFunctional_range_nonempty t H) ?_
      rintro y ⟨G, rfl⟩
      rcases hcompetitor G with ⟨V, hV⟩
      have hout :
          sInf (Set.range fun W : ContinuousKCompetitor d ↦
              continuousKFunctionalCompetitorValue t F W) ≤
            C * continuousKFunctionalCompetitorValue t H G :=
        (csInf_le (continuousKFunctional_range_bddBelow t F) ⟨V, rfl⟩).trans hV
      exact (div_le_iff₀ hCpos).2 (by simpa only [mul_comm] using hout)
    exact (div_le_iff₀ hCpos).1 hdiv |>.trans_eq (by ring)

/-- Constant matrix multiplication scales the continuous `K`-functional by
at most the Euclidean matrix operator norm. -/
theorem continuousKFunctional_constMatrixMul_le
    (t : ContinuousKScale) (A : Mat d) (F : UnitCubeEuclideanL2Field d) :
    continuousKFunctional t (unitCubeEuclideanL2FieldConstMatrixMul A F) ≤
      ‖A‖ * continuousKFunctional t F := by
  apply continuousKFunctional_le_of_forall_competitorValue_le
    t ‖A‖ (unitCubeEuclideanL2FieldConstMatrixMul A F) F (norm_nonneg A)
  intro G
  exact ⟨continuousKCompetitorConstMatrixMul A G,
    continuousKFunctionalCompetitorValue_constMatrixMul_le t A F G⟩

/-- The pointwise continuous `K`-seminorm integrand scales by the square of
the Euclidean matrix operator norm. -/
theorem continuousKSeminormIntegrand_constMatrixMul_le
    (sigma : ℝ) (A : Mat d) (F : UnitCubeEuclideanL2Field d) (t : ℝ) :
    continuousKSeminormIntegrand sigma
        (unitCubeEuclideanL2FieldConstMatrixMul A F) t ≤
      ENNReal.ofReal (‖A‖ ^ 2) * continuousKSeminormIntegrand sigma F t := by
  by_cases ht : t ∈ Set.Ioo (0 : ℝ) 1
  · let tau : ContinuousKScale := ⟨t, ⟨ht.1, ht.2.le⟩⟩
    have hK := continuousKFunctional_constMatrixMul_le tau A F
    have hKsq :
        continuousKFunctional tau
            (unitCubeEuclideanL2FieldConstMatrixMul A F) ^ 2 ≤
          ‖A‖ ^ 2 * continuousKFunctional tau F ^ 2 := by
      have hsquare := (sq_le_sq₀
        (continuousKFunctional_nonneg tau
          (unitCubeEuclideanL2FieldConstMatrixMul A F))
        (mul_nonneg (norm_nonneg A) (continuousKFunctional_nonneg tau F))).mpr hK
      simpa only [mul_pow] using hsquare
    have hofReal :
        ENNReal.ofReal
            (continuousKFunctional tau
              (unitCubeEuclideanL2FieldConstMatrixMul A F) ^ 2) ≤
          ENNReal.ofReal (‖A‖ ^ 2) *
            ENNReal.ofReal (continuousKFunctional tau F ^ 2) := by
      calc
        ENNReal.ofReal
            (continuousKFunctional tau
              (unitCubeEuclideanL2FieldConstMatrixMul A F) ^ 2) ≤
            ENNReal.ofReal
              (‖A‖ ^ 2 * continuousKFunctional tau F ^ 2) :=
          ENNReal.ofReal_le_ofReal hKsq
        _ = ENNReal.ofReal (‖A‖ ^ 2) *
            ENNReal.ofReal (continuousKFunctional tau F ^ 2) := by
          rw [ENNReal.ofReal_mul (sq_nonneg ‖A‖)]
    unfold continuousKSeminormIntegrand continuousKFunctionalOnOpenScale
    simp only [dite_eq_left ht]
    change
      ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
          ENNReal.ofReal
            (continuousKFunctional tau
              (unitCubeEuclideanL2FieldConstMatrixMul A F) ^ 2) *
          ENNReal.ofReal t⁻¹ ≤
        ENNReal.ofReal (‖A‖ ^ 2) *
          (ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
            ENNReal.ofReal (continuousKFunctional tau F ^ 2) *
            ENNReal.ofReal t⁻¹)
    calc
      ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
            ENNReal.ofReal
              (continuousKFunctional tau
                (unitCubeEuclideanL2FieldConstMatrixMul A F) ^ 2) *
            ENNReal.ofReal t⁻¹ ≤
          ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
              (ENNReal.ofReal (‖A‖ ^ 2) *
                ENNReal.ofReal (continuousKFunctional tau F ^ 2)) *
              ENNReal.ofReal t⁻¹ := by
        gcongr
      _ = ENNReal.ofReal (‖A‖ ^ 2) *
          (ENNReal.ofReal (Real.rpow t (-2 * sigma)) *
            ENNReal.ofReal (continuousKFunctional tau F ^ 2) *
            ENNReal.ofReal t⁻¹) := by
        ring
  · norm_num [continuousKSeminormIntegrand,
      continuousKFunctionalOnOpenScale, ht]

/-- The continuous `K`-seminorm integral scales by the square of the
Euclidean matrix operator norm. -/
theorem continuousKSeminormIntegral_constMatrixMul_le
    (sigma : ℝ) (A : Mat d) (F : UnitCubeEuclideanL2Field d) :
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        continuousKSeminormIntegrand sigma
          (unitCubeEuclideanL2FieldConstMatrixMul A F) t) ≤
      ENNReal.ofReal (‖A‖ ^ 2) *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          continuousKSeminormIntegrand sigma F t := by
  calc
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
        continuousKSeminormIntegrand sigma
          (unitCubeEuclideanL2FieldConstMatrixMul A F) t) ≤
      ∫⁻ t in Set.Ioo (0 : ℝ) 1,
        ENNReal.ofReal (‖A‖ ^ 2) * continuousKSeminormIntegrand sigma F t :=
      lintegral_mono fun t ↦
        continuousKSeminormIntegrand_constMatrixMul_le sigma A F t
    _ = ENNReal.ofReal (‖A‖ ^ 2) *
        ∫⁻ t in Set.Ioo (0 : ℝ) 1,
          continuousKSeminormIntegrand sigma F t := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private noncomputable def unitCubeEuclideanL2FieldToCenteredCubeZero
    (F : UnitCubeEuclideanL2Field d) : CenteredCubeEuclideanL2Field d 0 where
  toField := F
  euclideanMemL2 := by
    simpa only [centeredCubeDomain, unitCenteredCubeDomain] using F.euclideanMemL2

@[simp] private theorem unitCubeEuclideanL2FieldToCenteredCubeZero_apply
    (F : UnitCubeEuclideanL2Field d) (x : Vec d) :
    unitCubeEuclideanL2FieldToCenteredCubeZero F x = F x :=
  rfl

/-- Constant matrix multiplication scales the normalized unit-cube
Euclidean `L²` term by the Euclidean matrix operator norm. -/
theorem unitCubeNormalizedEuclideanLpENorm_constMatrixMul_le
    (A : Mat d) (F : UnitCubeEuclideanL2Field d) :
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
        (unitCubeEuclideanL2FieldConstMatrixMul A F) ≤
      ENNReal.ofReal ‖A‖ *
        (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F := by
  have hbound := centeredCubeNormalizedEuclideanLpENorm_constMatrixMul_le A
    (unitCubeEuclideanL2FieldToCenteredCubeZero F)
  simpa only [centeredCubeDomain, unitCenteredCubeDomain,
    centeredCubeEuclideanL2FieldConstMatrixMul_apply,
    unitCubeEuclideanL2FieldToCenteredCubeZero_apply,
    unitCubeEuclideanL2FieldConstMatrixMul_apply] using! hbound

/-- Constant matrix multiplication scales the normalized quadratic
continuous `K`-energy on the unit cube by the square of the Euclidean matrix
operator norm. -/
theorem unitCubeNormalizedContinuousKEnergy_constMatrixMul_le
    (s : FractionalOrder) (A : Mat d) (F : UnitCubeEuclideanL2Field d) :
    ((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
          (unitCubeEuclideanL2FieldConstMatrixMul A F)) ^ 2 +
        ENNReal.ofReal (2 * s.1) *
          (∫⁻ t in Set.Ioo (0 : ℝ) 1,
            continuousKSeminormIntegrand s.1
              (unitCubeEuclideanL2FieldConstMatrixMul A F) t) ≤
      ENNReal.ofReal (‖A‖ ^ 2) *
        (((unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
            F) ^ 2 +
          ENNReal.ofReal (2 * s.1) *
            ∫⁻ t in Set.Ioo (0 : ℝ) 1,
              continuousKSeminormIntegrand s.1 F t) := by
  let Lout : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞)
      (unitCubeEuclideanL2FieldConstMatrixMul A F)
  let Lin : ℝ≥0∞ :=
    (unitCenteredCubeDomain d).normalizedEuclideanLpENorm (2 : ℝ≥0∞) F
  let Iout : ℝ≥0∞ :=
    ∫⁻ t in Set.Ioo (0 : ℝ) 1,
      continuousKSeminormIntegrand s.1
        (unitCubeEuclideanL2FieldConstMatrixMul A F) t
  let Iin : ℝ≥0∞ :=
    ∫⁻ t in Set.Ioo (0 : ℝ) 1, continuousKSeminormIntegrand s.1 F t
  let p : ℝ≥0∞ := ENNReal.ofReal (2 * s.1)
  let c : ℝ≥0∞ := ENNReal.ofReal (‖A‖ ^ 2)
  have hL : Lout ≤ ENNReal.ofReal ‖A‖ * Lin := by
    simpa only [Lout, Lin] using
      unitCubeNormalizedEuclideanLpENorm_constMatrixMul_le A F
  have hLsq : Lout ^ 2 ≤ c * Lin ^ 2 := by
    calc
      Lout ^ 2 ≤ (ENNReal.ofReal ‖A‖ * Lin) ^ 2 := by
        gcongr
      _ = c * Lin ^ 2 := by
        rw [mul_pow]
        dsimp only [c]
        rw [ENNReal.ofReal_pow (norm_nonneg A)]
  have hI : Iout ≤ c * Iin := by
    simpa only [Iout, Iin, c] using
      continuousKSeminormIntegral_constMatrixMul_le s.1 A F
  change Lout ^ 2 + p * Iout ≤ c * (Lin ^ 2 + p * Iin)
  calc
    Lout ^ 2 + p * Iout ≤ c * Lin ^ 2 + p * (c * Iin) :=
      add_le_add hLsq (by
        simpa only [mul_comm] using mul_le_mul_left hI p)
    _ = c * (Lin ^ 2 + p * Iin) := by
      ring

end

end HighContrast
end HCPolySupport
