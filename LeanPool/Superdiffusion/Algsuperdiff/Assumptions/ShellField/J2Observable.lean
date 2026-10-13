/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.Basic
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMetric

/-!
# J2Observable

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The exact J2 shell observable

This module defines the three quantitative norms in ABK26 assumption J2 on the
literal open cube `cu₀ = (-1/2, 1/2)^d` and proves that their weighted sum is
Borel measurable on the approved compact-open `ShellField` carrier.

The matrix value norm is
`Homogenization.Book.Ch02.matrixOperatorNorm`.  Derivative inputs use
`Homogenization.Book.Ch02.vecNorm`.  The stored first and second derivatives
remain bundled with the frozen carrier's elementwise matrix norm; their exact
Euclidean induced norms are explicit scalar suprema, so no alternative
matrix-norm instance leaks into the carrier.  Every supremum includes zero
explicitly.
-/

open scoped BigOperators Matrix.Norms.Elementwise NNReal

namespace Algsuperdiff.Frozen.Assumptions.ShellField

open Set
open HCPolySupport
open HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

/-- The stored first-derivative type of a shell field.  Its bundle uses the
elementwise matrix norm fixed by the frozen carrier; exact Euclidean sizes are
measured separately by `matrixDerivativeNorm`. -/
abbrev MatrixDerivative (d : ℕ) := Vec d →L[ℝ] Mat d

/-- The closed Euclidean unit ball used to index induced derivative norms. -/
abbrev EuclideanUnitVector (d : ℕ) :=
  {v : Vec d // vecNorm v ≤ 1}

/-- Values used for the exact Euclidean induced norm.  The `none` branch
records zero explicitly, including in dimension zero. -/
def matrixDerivativeNormValue (D : MatrixDerivative d) :
    Option (EuclideanUnitVector d) → ℝ
  | none => 0
  | some v => matrixOperatorNorm (D v.1)

/-- The range of first-derivative norm samples, including the zero sample. -/
def matrixDerivativeNormValueSet (D : MatrixDerivative d) : Set ℝ :=
  Set.range (matrixDerivativeNormValue D)

/-- Euclidean-vector to Euclidean-matrix induced norm, evaluated on the
carrier's actual elementwise-norm continuous-linear-map bundle. -/
def matrixDerivativeNorm (D : MatrixDerivative d) : ℝ :=
  sSup (matrixDerivativeNormValueSet D)

theorem norm_vec_le_vecNorm (v : Vec d) : ‖v‖ ≤ vecNorm v := by
  rw [pi_norm_le_iff_of_nonneg (vecNorm_nonneg v)]
  intro i
  simpa only [vecNorm, PiLp.toLp_apply] using
    (PiLp.norm_apply_le (WithLp.toLp 2 v : EuclideanSpace ℝ (Fin d)) i)

private theorem sum_abs_entries_le (A : Mat d) :
    (∑ i, ∑ j, |A i j|) ≤ (d : ℝ) ^ 2 * ‖A‖ := by
  calc
    (∑ i, ∑ j, |A i j|) ≤ ∑ _i : Fin d, ∑ _j : Fin d, ‖A‖ :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => by
        simpa only [Real.norm_eq_abs] using Matrix.norm_entry_le_entrywise_sup_norm A
    _ = (d : ℝ) ^ 2 * ‖A‖ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul, pow_two]
      ring

private theorem matrixOperatorNorm_le_sq_mul_norm (A : Mat d) :
    matrixOperatorNorm A ≤ (d : ℝ) ^ 2 * ‖A‖ := by
  exact (matrixOperatorNorm_le_matrixFrobeniusNorm A).trans
    ((matrixFrobeniusNorm_le_sum_abs_entries A).trans (sum_abs_entries_le A))

private theorem norm_matrixOperatorNorm_sub_le_sq_mul_norm (A B : Mat d) :
    ‖matrixOperatorNorm A - matrixOperatorNorm B‖ ≤
      (d : ℝ) ^ 2 * ‖A - B‖ := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add]
    have h := matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries B A
    have hsum := sum_abs_entries_le (B - A)
    have hnorm : ‖B - A‖ = ‖A - B‖ := by
      rw [show B - A = -(A - B) by abel, norm_neg]
    calc
      matrixOperatorNorm B ≤ matrixOperatorNorm A +
          ∑ i, ∑ j, |B i j - A i j| := h
      _ ≤ matrixOperatorNorm A + (d : ℝ) ^ 2 * ‖A - B‖ :=
        add_le_add_right (by simpa only [hnorm, Matrix.sub_apply] using hsum) _
  · rw [sub_le_iff_le_add]
    have h := matrixOperatorNorm_le_matrixOperatorNorm_add_sum_abs_sub_entries A B
    calc
      matrixOperatorNorm A ≤ matrixOperatorNorm B +
          ∑ i, ∑ j, |A i j - B i j| := h
      _ ≤ matrixOperatorNorm B + (d : ℝ) ^ 2 * ‖A - B‖ :=
        add_le_add_right (sum_abs_entries_le (A - B)) _
      _ = (d : ℝ) ^ 2 * ‖A - B‖ + matrixOperatorNorm B := add_comm _ _

private theorem matrixOperatorNorm_lipschitz :
    LipschitzWith (Real.toNNReal ((d : ℝ) ^ 2))
      (matrixOperatorNorm : Mat d → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro A B
  rw [dist_eq_norm, dist_eq_norm]
  simpa only [Real.coe_toNNReal _ (sq_nonneg (d : ℝ))] using
    norm_matrixOperatorNorm_sub_le_sq_mul_norm A B

private theorem matrixOperatorNorm_continuous :
    Continuous (matrixOperatorNorm : Mat d → ℝ) :=
  matrixOperatorNorm_lipschitz.continuous

private theorem matrixDerivativeNormValueSet_nonempty (D : MatrixDerivative d) :
    (matrixDerivativeNormValueSet D).Nonempty := by
  exact ⟨0, none, rfl⟩

private theorem matrixDerivativeNormValue_le_sq_mul_norm (D : MatrixDerivative d)
    (o : Option (EuclideanUnitVector d)) :
    matrixDerivativeNormValue D o ≤ (d : ℝ) ^ 2 * ‖D‖ := by
  cases o with
  | none => positivity
  | some v =>
      calc
        matrixOperatorNorm (D v.1) ≤ (d : ℝ) ^ 2 * ‖D v.1‖ :=
          matrixOperatorNorm_le_sq_mul_norm _
        _ ≤ (d : ℝ) ^ 2 * (‖D‖ * ‖v.1‖) :=
          mul_le_mul_of_nonneg_left (D.le_opNorm _) (sq_nonneg _)
        _ ≤ (d : ℝ) ^ 2 * (‖D‖ * vecNorm v.1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_vec_le_vecNorm v.1) (norm_nonneg D))
            (sq_nonneg _)
        _ ≤ (d : ℝ) ^ 2 * (‖D‖ * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left v.2 (norm_nonneg D)) (sq_nonneg _)
        _ = (d : ℝ) ^ 2 * ‖D‖ := by ring

private theorem matrixDerivativeNormValueSet_bddAbove (D : MatrixDerivative d) :
    BddAbove (matrixDerivativeNormValueSet D) := by
  refine ⟨(d : ℝ) ^ 2 * ‖D‖, ?_⟩
  rintro r ⟨o, rfl⟩
  exact matrixDerivativeNormValue_le_sq_mul_norm D o

theorem matrixDerivativeNorm_nonneg (D : MatrixDerivative d) :
    0 ≤ matrixDerivativeNorm D := by
  exact le_csSup (matrixDerivativeNormValueSet_bddAbove D) ⟨none, rfl⟩

private theorem matrixDerivativeNormValue_le (D : MatrixDerivative d)
    (o : Option (EuclideanUnitVector d)) :
    matrixDerivativeNormValue D o ≤ matrixDerivativeNorm D := by
  exact le_csSup (matrixDerivativeNormValueSet_bddAbove D) ⟨o, rfl⟩

/-- The exact induced derivative norm controls every matrix value on the
`vecNorm` unit ball. -/
theorem matrixOperatorNorm_apply_le_matrixDerivativeNorm
    (D : MatrixDerivative d) (v : Vec d) (hv : vecNorm v ≤ 1) :
    matrixOperatorNorm (D v) ≤ matrixDerivativeNorm D :=
  matrixDerivativeNormValue_le D (some ⟨v, hv⟩)

theorem matrixDerivativeNorm_le_sq_mul_norm (D : MatrixDerivative d) :
    matrixDerivativeNorm D ≤ (d : ℝ) ^ 2 * ‖D‖ := by
  apply csSup_le (matrixDerivativeNormValueSet_nonempty D)
  rintro r ⟨o, rfl⟩
  exact matrixDerivativeNormValue_le_sq_mul_norm D o

theorem matrixDerivativeNorm_add_le (D E : MatrixDerivative d) :
    matrixDerivativeNorm (D + E) ≤ matrixDerivativeNorm D + matrixDerivativeNorm E := by
  apply csSup_le (matrixDerivativeNormValueSet_nonempty (D + E))
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact add_nonneg (matrixDerivativeNorm_nonneg D) (matrixDerivativeNorm_nonneg E)
  | some v =>
      calc
        matrixOperatorNorm ((D + E) v.1) =
            matrixOperatorNorm (D v.1 + E v.1) := rfl
        _ ≤ matrixOperatorNorm (D v.1) + matrixOperatorNorm (E v.1) := by
          simpa only [matrixOperatorNorm, map_add] using
            norm_add_le
              (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (D v.1))
              (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ) (E v.1))
        _ ≤ matrixDerivativeNorm D + matrixDerivativeNorm E :=
          add_le_add (matrixDerivativeNormValue_le D (some v))
            (matrixDerivativeNormValue_le E (some v))

@[simp] theorem matrixDerivativeNorm_neg (D : MatrixDerivative d) :
    matrixDerivativeNorm (-D) = matrixDerivativeNorm D := by
  unfold matrixDerivativeNorm matrixDerivativeNormValueSet
  refine congrArg sSup ?_
  ext r
  constructor
  · rintro ⟨o, rfl⟩
    refine ⟨o, ?_⟩
    cases o <;>
      simp only [matrixDerivativeNormValue, matrixOperatorNorm,
        neg_apply, map_neg, norm_neg]
  · rintro ⟨o, rfl⟩
    refine ⟨o, ?_⟩
    cases o <;>
      simp only [matrixDerivativeNormValue, matrixOperatorNorm,
        neg_apply, map_neg, norm_neg]

theorem norm_matrixDerivativeNorm_sub_le_sq_mul_norm (D E : MatrixDerivative d) :
    ‖matrixDerivativeNorm D - matrixDerivativeNorm E‖ ≤
      (d : ℝ) ^ 2 * ‖D - E‖ := by
  rw [Real.norm_eq_abs, abs_le]
  have hDE : matrixDerivativeNorm D ≤
      matrixDerivativeNorm (D - E) + matrixDerivativeNorm E := by
    simpa only [sub_add_cancel] using matrixDerivativeNorm_add_le (D - E) E
  have hED : matrixDerivativeNorm E ≤
      matrixDerivativeNorm (E - D) + matrixDerivativeNorm D := by
    simpa only [sub_add_cancel] using matrixDerivativeNorm_add_le (E - D) D
  constructor
  · rw [neg_le_sub_iff_le_add]
    calc
      matrixDerivativeNorm E ≤ matrixDerivativeNorm (E - D) + matrixDerivativeNorm D := hED
      _ = matrixDerivativeNorm (D - E) + matrixDerivativeNorm D := by
        rw [show E - D = -(D - E) by abel, matrixDerivativeNorm_neg]
      _ ≤ (d : ℝ) ^ 2 * ‖D - E‖ + matrixDerivativeNorm D :=
        add_le_add_left (matrixDerivativeNorm_le_sq_mul_norm (D - E)) _
      _ = matrixDerivativeNorm D + (d : ℝ) ^ 2 * ‖D - E‖ := add_comm _ _
  · rw [sub_le_iff_le_add]
    calc
      matrixDerivativeNorm D ≤
          matrixDerivativeNorm (D - E) + matrixDerivativeNorm E := hDE
      _ ≤ (d : ℝ) ^ 2 * ‖D - E‖ + matrixDerivativeNorm E :=
        add_le_add_left (matrixDerivativeNorm_le_sq_mul_norm (D - E)) _

theorem matrixDerivativeNorm_lipschitz :
    LipschitzWith (Real.toNNReal ((d : ℝ) ^ 2))
      (matrixDerivativeNorm : MatrixDerivative d → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro D E
  rw [dist_eq_norm, dist_eq_norm]
  simpa only [Real.coe_toNNReal _ (sq_nonneg (d : ℝ))] using!
    norm_matrixDerivativeNorm_sub_le_sq_mul_norm D E

theorem matrixDerivativeNorm_continuous :
    Continuous (matrixDerivativeNorm : MatrixDerivative d → ℝ) :=
  matrixDerivativeNorm_lipschitz.continuous

/-- The stored second-derivative type of a shell field.  It is a linear map
in the first derivative direction with values in `MatrixDerivative d`. -/
abbrev MatrixSecondDerivative (d : ℕ) :=
  Vec d →L[ℝ] MatrixDerivative d

/-- Migration cache (mathlib v4.33.1): blind instance search no longer reaches the
`ContinuousLinearMap` normed-group instance on the nested `Vec d →L[ℝ] MatrixDerivative d`
carrier, so `‖H‖`, `H.le_opNorm` and `dist_eq_norm` below would fail; name the direct
term once here. -/
instance matrixSecondDerivativeNormedAddCommGroup (d : ℕ) :
    NormedAddCommGroup (Vec d →L[ℝ] MatrixDerivative d) :=
  ContinuousLinearMap.toNormedAddCommGroup

/-- Values used for the exact twice-induced Euclidean norm.  The `none`
branch records zero explicitly, including in dimension zero. -/
def matrixSecondDerivativeNormValue (H : MatrixSecondDerivative d) :
    Option (EuclideanUnitVector d) → ℝ
  | none => 0
  | some u => matrixDerivativeNorm (H u.1)

/-- The range of second-derivative norm samples, including the zero sample. -/
def matrixSecondDerivativeNormValueSet (H : MatrixSecondDerivative d) : Set ℝ :=
  Set.range (matrixSecondDerivativeNormValue H)

/-- Exact twice-induced norm of a stored second derivative: first take the
exact induced norm of the resulting matrix derivative, then the supremum over
the first `vecNorm` unit ball. -/
def matrixSecondDerivativeNorm (H : MatrixSecondDerivative d) : ℝ :=
  sSup (matrixSecondDerivativeNormValueSet H)

private theorem matrixSecondDerivativeNormValueSet_nonempty
    (H : MatrixSecondDerivative d) :
    (matrixSecondDerivativeNormValueSet H).Nonempty := by
  exact ⟨0, none, rfl⟩

private theorem matrixSecondDerivativeNormValue_le_sq_mul_norm
    (H : MatrixSecondDerivative d) (o : Option (EuclideanUnitVector d)) :
    matrixSecondDerivativeNormValue H o ≤ (d : ℝ) ^ 2 * ‖H‖ := by
  cases o with
  | none => positivity
  | some u =>
      calc
        matrixDerivativeNorm (H u.1) ≤ (d : ℝ) ^ 2 * ‖H u.1‖ :=
          matrixDerivativeNorm_le_sq_mul_norm _
        _ ≤ (d : ℝ) ^ 2 * (‖H‖ * ‖u.1‖) :=
          mul_le_mul_of_nonneg_left (H.le_opNorm _) (sq_nonneg _)
        _ ≤ (d : ℝ) ^ 2 * (‖H‖ * vecNorm u.1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (norm_vec_le_vecNorm u.1) (norm_nonneg H))
            (sq_nonneg _)
        _ ≤ (d : ℝ) ^ 2 * (‖H‖ * 1) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left u.2 (norm_nonneg H)) (sq_nonneg _)
        _ = (d : ℝ) ^ 2 * ‖H‖ := by ring

private theorem matrixSecondDerivativeNormValueSet_bddAbove
    (H : MatrixSecondDerivative d) :
    BddAbove (matrixSecondDerivativeNormValueSet H) := by
  refine ⟨(d : ℝ) ^ 2 * ‖H‖, ?_⟩
  rintro r ⟨o, rfl⟩
  exact matrixSecondDerivativeNormValue_le_sq_mul_norm H o

theorem matrixSecondDerivativeNorm_nonneg (H : MatrixSecondDerivative d) :
    0 ≤ matrixSecondDerivativeNorm H := by
  exact le_csSup (matrixSecondDerivativeNormValueSet_bddAbove H) ⟨none, rfl⟩

private theorem matrixSecondDerivativeNormValue_le
    (H : MatrixSecondDerivative d) (o : Option (EuclideanUnitVector d)) :
    matrixSecondDerivativeNormValue H o ≤ matrixSecondDerivativeNorm H := by
  exact le_csSup (matrixSecondDerivativeNormValueSet_bddAbove H) ⟨o, rfl⟩

/-- The exact twice-induced norm controls the inner derivative norm for every
first input in the `vecNorm` unit ball. -/
theorem matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm
    (H : MatrixSecondDerivative d) (u : Vec d) (hu : vecNorm u ≤ 1) :
    matrixDerivativeNorm (H u) ≤ matrixSecondDerivativeNorm H :=
  matrixSecondDerivativeNormValue_le H (some ⟨u, hu⟩)

theorem matrixSecondDerivativeNorm_add_le
    (H K : MatrixSecondDerivative d) :
    matrixSecondDerivativeNorm (H + K) ≤
      matrixSecondDerivativeNorm H + matrixSecondDerivativeNorm K := by
  apply csSup_le (matrixSecondDerivativeNormValueSet_nonempty (H + K))
  rintro r ⟨o, rfl⟩
  cases o with
  | none =>
      exact add_nonneg
        (matrixSecondDerivativeNorm_nonneg H)
        (matrixSecondDerivativeNorm_nonneg K)
  | some u =>
      calc
        matrixDerivativeNorm ((H + K) u.1) =
            matrixDerivativeNorm (H u.1 + K u.1) := rfl
        _ ≤ matrixDerivativeNorm (H u.1) + matrixDerivativeNorm (K u.1) :=
          matrixDerivativeNorm_add_le _ _
        _ ≤ matrixSecondDerivativeNorm H + matrixSecondDerivativeNorm K :=
          add_le_add
            (matrixSecondDerivativeNormValue_le H (some u))
            (matrixSecondDerivativeNormValue_le K (some u))

private theorem matrixSecondDerivativeNorm_le_add_norm_sub
    (H K : MatrixSecondDerivative d) :
    matrixSecondDerivativeNorm H ≤
      matrixSecondDerivativeNorm K + (d : ℝ) ^ 2 * ‖H - K‖ := by
  apply csSup_le (matrixSecondDerivativeNormValueSet_nonempty H)
  rintro r ⟨o, rfl⟩
  cases o with
  | none =>
      exact add_nonneg (matrixSecondDerivativeNorm_nonneg K)
        (mul_nonneg (sq_nonneg (d : ℝ)) (norm_nonneg (H - K)))
  | some u =>
      calc
        matrixDerivativeNorm (H u.1) ≤
            matrixDerivativeNorm (H u.1 - K u.1) + matrixDerivativeNorm (K u.1) := by
          simpa only [sub_add_cancel] using
            matrixDerivativeNorm_add_le (H u.1 - K u.1) (K u.1)
        _ ≤ (d : ℝ) ^ 2 * ‖H u.1 - K u.1‖ + matrixSecondDerivativeNorm K :=
          add_le_add (matrixDerivativeNorm_le_sq_mul_norm _)
            (matrixSecondDerivativeNormValue_le K (some u))
        _ = (d : ℝ) ^ 2 * ‖(H - K) u.1‖ + matrixSecondDerivativeNorm K := rfl
        _ ≤ (d : ℝ) ^ 2 * (‖H - K‖ * ‖u.1‖) + matrixSecondDerivativeNorm K :=
          add_le_add_left
            (mul_le_mul_of_nonneg_left ((H - K).le_opNorm _) (sq_nonneg _)) _
        _ ≤ (d : ℝ) ^ 2 * (‖H - K‖ * vecNorm u.1) +
              matrixSecondDerivativeNorm K :=
          add_le_add_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (norm_vec_le_vecNorm u.1)
                (norm_nonneg (H - K))) (sq_nonneg _)) _
        _ ≤ (d : ℝ) ^ 2 * (‖H - K‖ * 1) + matrixSecondDerivativeNorm K :=
          add_le_add_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left u.2 (norm_nonneg (H - K)))
              (sq_nonneg _)) _
        _ = matrixSecondDerivativeNorm K + (d : ℝ) ^ 2 * ‖H - K‖ := by ring

theorem norm_matrixSecondDerivativeNorm_sub_le_sq_mul_norm
    (H K : MatrixSecondDerivative d) :
    ‖matrixSecondDerivativeNorm H - matrixSecondDerivativeNorm K‖ ≤
      (d : ℝ) ^ 2 * ‖H - K‖ := by
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · rw [neg_le_sub_iff_le_add]
    calc
      matrixSecondDerivativeNorm K ≤
          matrixSecondDerivativeNorm H + (d : ℝ) ^ 2 * ‖K - H‖ :=
        matrixSecondDerivativeNorm_le_add_norm_sub K H
      _ = matrixSecondDerivativeNorm H + (d : ℝ) ^ 2 * ‖H - K‖ := by
        have h : ‖K - H‖ = ‖H - K‖ := norm_sub_rev K H
        rw [h]
  · rw [sub_le_iff_le_add]
    simpa only [add_comm] using matrixSecondDerivativeNorm_le_add_norm_sub H K

theorem matrixSecondDerivativeNorm_lipschitz :
    LipschitzWith (Real.toNNReal ((d : ℝ) ^ 2))
      (matrixSecondDerivativeNorm : MatrixSecondDerivative d → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro H K
  rw [dist_eq_norm, dist_eq_norm]
  simpa only [Real.coe_toNNReal _ (sq_nonneg (d : ℝ))] using!
    norm_matrixSecondDerivativeNorm_sub_le_sq_mul_norm H K

theorem matrixSecondDerivativeNorm_continuous :
    Continuous (matrixSecondDerivativeNorm : MatrixSecondDerivative d → ℝ) :=
  matrixSecondDerivativeNorm_lipschitz.continuous

/-- Sharp characterization of the exact twice-induced norm. -/
theorem matrixSecondDerivativeNorm_le_iff
    (H : MatrixSecondDerivative d) (C : ℝ) :
    matrixSecondDerivativeNorm H ≤ C ↔
      0 ≤ C ∧ ∀ u : Vec d, vecNorm u ≤ 1 → matrixDerivativeNorm (H u) ≤ C := by
  constructor
  · intro h
    refine ⟨(matrixSecondDerivativeNorm_nonneg H).trans h, ?_⟩
    intro u hu
    exact (matrixDerivativeNorm_apply_le_matrixSecondDerivativeNorm H u hu).trans h
  · rintro ⟨hC, h⟩
    unfold matrixSecondDerivativeNorm
    apply csSup_le (matrixSecondDerivativeNormValueSet_nonempty H)
    rintro r ⟨o, rfl⟩
    cases o with
    | none => exact hC
    | some u => exact h u.1 u.2

/-- Points of the literal open manuscript cube `cu₀ = (-1/2, 1/2)^d`. -/
abbrev UnitOpenCubePoint (d : ℕ) :=
  {x : Vec d // x ∈ openCubeSet (originCube d 0)}

/-- Matrix-value norm samples on the open unit cube, with zero at `none`. -/
def unitCubeValueAtIndex (j : ShellField d) :
    Option (UnitOpenCubePoint d) → ℝ
  | none => 0
  | some x => matrixOperatorNorm (j x.1)

/-- First-derivative norm samples on the open unit cube, with zero at `none`. -/
def unitCubeDerivAtIndex (j : ShellField d) :
    Option (UnitOpenCubePoint d) → ℝ
  | none => 0
  | some x => matrixDerivativeNorm (ShellField.deriv j x.1)

/-- Second-derivative norm samples on the open unit cube, with zero at `none`. -/
def unitCubeSecondDerivAtIndex (j : ShellField d) :
    Option (UnitOpenCubePoint d) → ℝ
  | none => 0
  | some x => matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1)

/-- Exact Euclidean matrix-operator `L∞` norm of the shell values on the
literal open unit cube.  The defining range includes zero explicitly. -/
def unitCubeValueNorm (j : ShellField d) : ℝ :=
  sSup (Set.range (unitCubeValueAtIndex j))

/-- Exact induced `vecNorm → matrixOperatorNorm` `L∞` norm of the stored
first derivative on the literal open unit cube. -/
def unitCubeDerivNorm (j : ShellField d) : ℝ :=
  sSup (Set.range (unitCubeDerivAtIndex j))

/-- Exact twice-induced `vecNorm → vecNorm → matrixOperatorNorm` `L∞` norm of
the stored second derivative on the literal open unit cube. -/
def unitCubeSecondDerivNorm (j : ShellField d) : ℝ :=
  sSup (Set.range (unitCubeSecondDerivAtIndex j))

private theorem unitOpenCubePoint_mem_closedBall (x : UnitOpenCubePoint d) :
    x.1 ∈ Metric.closedBall
      (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0)) := by
  apply Metric.ball_subset_closedBall
  rw [ball_cubeCenter_eq_openCubeSet]
  exact x.2

private theorem unitCubeValueAtIndex_range_bddAbove (j : ShellField d) :
    BddAbove (Set.range (unitCubeValueAtIndex j)) := by
  let K : Set (Vec d) := Metric.closedBall
    (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))
  have hK : IsCompact K := by
    simpa only [K] using isCompact_closedBall
      (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))
  have hcont : Continuous (fun x : Vec d => matrixOperatorNorm (j x)) :=
    matrixOperatorNorm_continuous.comp j.1.1.continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some x =>
      have hx : x.1 ∈ K := unitOpenCubePoint_mem_closedBall x
      have h := hC x.1 hx
      have hop : matrixOperatorNorm (j x.1) ≤ C := by
        simpa only [Real.norm_eq_abs,
          abs_of_nonneg (matrixOperatorNorm_nonneg _)] using h
      exact hop.trans (le_max_right _ _)

private theorem unitCubeDerivAtIndex_range_bddAbove (j : ShellField d) :
    BddAbove (Set.range (unitCubeDerivAtIndex j)) := by
  let K : Set (Vec d) := Metric.closedBall
    (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))
  have hK : IsCompact K := by
    simpa only [K] using isCompact_closedBall
      (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))
  have hcont : Continuous
      (fun x : Vec d => matrixDerivativeNorm (ShellField.deriv j x)) :=
    matrixDerivativeNorm_continuous.comp (ShellField.deriv j).continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some x =>
      have hx : x.1 ∈ K := unitOpenCubePoint_mem_closedBall x
      have h := hC x.1 hx
      have hD : matrixDerivativeNorm (ShellField.deriv j x.1) ≤ C := by
        calc
          matrixDerivativeNorm (ShellField.deriv j x.1) =
              |matrixDerivativeNorm (ShellField.deriv j x.1)| :=
            (abs_of_nonneg (matrixDerivativeNorm_nonneg _)).symm
          _ = ‖matrixDerivativeNorm (ShellField.deriv j x.1)‖ :=
            (Real.norm_eq_abs _).symm
          _ ≤ C := h
      exact hD.trans (le_max_right _ _)

private theorem unitCubeSecondDerivAtIndex_range_bddAbove (j : ShellField d) :
    BddAbove (Set.range (unitCubeSecondDerivAtIndex j)) := by
  let K : Set (Vec d) := Metric.closedBall
    (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))
  have hK : IsCompact K := by
    simpa only [K] using isCompact_closedBall
      (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))
  have hcont : Continuous
      (fun x : Vec d => matrixSecondDerivativeNorm (ShellField.secondDeriv j x)) :=
    matrixSecondDerivativeNorm_continuous.comp (ShellField.secondDeriv j).continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨max 0 C, ?_⟩
  rintro r ⟨o, rfl⟩
  cases o with
  | none => exact le_max_left _ _
  | some x =>
      have hx : x.1 ∈ K := unitOpenCubePoint_mem_closedBall x
      have h := hC x.1 hx
      have hD : matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1) ≤ C := by
        calc
          matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1) =
              |matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1)| :=
            (abs_of_nonneg (matrixSecondDerivativeNorm_nonneg _)).symm
          _ = ‖matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1)‖ :=
            (Real.norm_eq_abs _).symm
          _ ≤ C := h
      exact hD.trans (le_max_right _ _)

theorem unitCubeValueNorm_nonneg (j : ShellField d) : 0 ≤ unitCubeValueNorm j := by
  exact le_csSup (unitCubeValueAtIndex_range_bddAbove j) ⟨none, rfl⟩

/-- The unit-cube value control bounds the matrix operator norm at every point
of the literal open unit cube. -/
theorem matrixOperatorNorm_apply_le_unitCubeValueNorm
    (j : ShellField d) (x : UnitOpenCubePoint d) :
    matrixOperatorNorm (j x.1) ≤ unitCubeValueNorm j := by
  exact le_csSup (unitCubeValueAtIndex_range_bddAbove j) ⟨some x, rfl⟩

/-- Continuity of the exact Euclidean matrix-operator norm used by the J2
observable. -/
theorem continuous_matrixOperatorNorm :
    Continuous (matrixOperatorNorm : Mat d → ℝ) :=
  matrixOperatorNorm_continuous

theorem unitCubeDerivNorm_nonneg (j : ShellField d) : 0 ≤ unitCubeDerivNorm j := by
  exact le_csSup (unitCubeDerivAtIndex_range_bddAbove j) ⟨none, rfl⟩

theorem unitCubeSecondDerivNorm_nonneg (j : ShellField d) :
    0 ≤ unitCubeSecondDerivNorm j := by
  exact le_csSup (unitCubeSecondDerivAtIndex_range_bddAbove j) ⟨none, rfl⟩

/-- Sharp characterization: the open-cube second-derivative norm is the least
nonnegative constant controlling the exact twice-induced norm at every point
of the literal open cube. -/
theorem unitCubeSecondDerivNorm_le_iff (j : ShellField d) (C : ℝ) :
    unitCubeSecondDerivNorm j ≤ C ↔
      0 ≤ C ∧
        ∀ x : UnitOpenCubePoint d,
          matrixSecondDerivativeNorm (ShellField.secondDeriv j x.1) ≤ C := by
  constructor
  · intro h
    refine ⟨(unitCubeSecondDerivNorm_nonneg j).trans h, ?_⟩
    intro x
    have hx : unitCubeSecondDerivAtIndex j (some x) ≤
        unitCubeSecondDerivNorm j :=
      le_csSup (unitCubeSecondDerivAtIndex_range_bddAbove j) ⟨some x, rfl⟩
    exact hx.trans h
  · rintro ⟨hC, h⟩
    unfold unitCubeSecondDerivNorm
    apply csSup_le (Set.range_nonempty (unitCubeSecondDerivAtIndex j))
    rintro r ⟨o, rfl⟩
    cases o with
    | none => exact hC
    | some x => exact h x

/-- The literal weighted observable in the manuscript's J2 tail bound:
`‖j₀‖∞ + √d ‖∇j₀‖∞ + d ‖∇²j₀‖∞`, all on the open cube `cu₀`. -/
def j2Observable (d : ℕ) (j : ShellField d) : ℝ :=
  unitCubeValueNorm j + Real.sqrt d * unitCubeDerivNorm j +
    (d : ℝ) * unitCubeSecondDerivNorm j

/-- The J2 observable is nonnegative. -/
theorem j2Observable_nonneg (d : ℕ) (j : ShellField d) :
    0 ≤ j2Observable d j := by
  exact add_nonneg
    (add_nonneg (unitCubeValueNorm_nonneg j)
      (mul_nonneg (Real.sqrt_nonneg _) (unitCubeDerivNorm_nonneg j)))
    (mul_nonneg (Nat.cast_nonneg d) (unitCubeSecondDerivNorm_nonneg j))

private theorem unitCubeValueAtIndex_continuous (o : Option (UnitOpenCubePoint d)) :
    Continuous (fun j : ShellField d => unitCubeValueAtIndex j o) := by
  cases o with
  | none => exact continuous_const
  | some x =>
      exact matrixOperatorNorm_continuous.comp
        (ShellField.continuous_eval x.1)

private theorem unitCubeDerivAtIndex_continuous (o : Option (UnitOpenCubePoint d)) :
    Continuous (fun j : ShellField d => unitCubeDerivAtIndex j o) := by
  cases o with
  | none => exact continuous_const
  | some x =>
      exact matrixDerivativeNorm_continuous.comp
        (ShellField.continuous_eval_deriv x.1)

private theorem unitCubeSecondDerivAtIndex_continuous
    (o : Option (UnitOpenCubePoint d)) :
    Continuous (fun j : ShellField d => unitCubeSecondDerivAtIndex j o) := by
  cases o with
  | none => exact continuous_const
  | some x =>
      exact matrixSecondDerivativeNorm_continuous.comp
        (ShellField.continuous_eval_secondDeriv x.1)

theorem unitCubeValueNorm_lowerSemicontinuous :
    LowerSemicontinuous (unitCubeValueNorm : ShellField d → ℝ) := by
  have h := lowerSemicontinuous_ciSup
    (fun j : ShellField d => unitCubeValueAtIndex_range_bddAbove j)
    (fun o => (unitCubeValueAtIndex_continuous o).lowerSemicontinuous)
  simpa only [unitCubeValueNorm, iSup] using! h

theorem unitCubeDerivNorm_lowerSemicontinuous :
    LowerSemicontinuous (unitCubeDerivNorm : ShellField d → ℝ) := by
  have h := lowerSemicontinuous_ciSup
    (fun j : ShellField d => unitCubeDerivAtIndex_range_bddAbove j)
    (fun o => (unitCubeDerivAtIndex_continuous o).lowerSemicontinuous)
  simpa only [unitCubeDerivNorm, iSup] using! h

theorem unitCubeSecondDerivNorm_lowerSemicontinuous :
    LowerSemicontinuous (unitCubeSecondDerivNorm : ShellField d → ℝ) := by
  have h := lowerSemicontinuous_ciSup
    (fun j : ShellField d => unitCubeSecondDerivAtIndex_range_bddAbove j)
    (fun o => (unitCubeSecondDerivAtIndex_continuous o).lowerSemicontinuous)
  simpa only [unitCubeSecondDerivNorm, iSup] using! h

theorem unitCubeValueNorm_measurable :
    Measurable (unitCubeValueNorm : ShellField d → ℝ) :=
  unitCubeValueNorm_lowerSemicontinuous.measurable

theorem unitCubeDerivNorm_measurable :
    Measurable (unitCubeDerivNorm : ShellField d → ℝ) :=
  unitCubeDerivNorm_lowerSemicontinuous.measurable

theorem unitCubeSecondDerivNorm_measurable :
    Measurable (unitCubeSecondDerivNorm : ShellField d → ℝ) :=
  unitCubeSecondDerivNorm_lowerSemicontinuous.measurable

theorem j2Observable_measurable (d : ℕ) :
    Measurable (j2Observable d) := by
  exact (unitCubeValueNorm_measurable.add
    (measurable_const.mul unitCubeDerivNorm_measurable)).add
      (measurable_const.mul unitCubeSecondDerivNorm_measurable)

end

end Algsuperdiff.Frozen.Assumptions.ShellField
