/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.ValueL2
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MultiscaleEllipticity.Basic
public import LeanPool.HighContrastHomogenization.Support.Geometry.CubeMeasure
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# ValueL2

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Characterization of the frozen `L²` value norm

`Algsuperdiff.Frozen.Section24.UnitCubeSkewW2Infinity.valueL2` is defined as an
`eLpNorm` of the pointwise Euclidean matrix norm of the frozen field over the
unit cube.  This module is the ordinary A sitting immediately beside that
frozen definition, in the same style as
`Algsuperdiff.Section24.UnitCubeMultiscale.*.Characterization`: it names the
pointwise norm field (`matrixNormField`), supplies its measurability and `L²`
membership on the carrier, and unfolds the frozen definition **exactly once**,
in `valueL2_sq_eq_integral`.

Every downstream consumer routes through `valueL2_sq_eq_integral`; no provider
module ever delta-unfolds `valueL2` again.

This module imports only Mathlib, `Homogenization`, and frozen definition
files.  In particular it imports no Section 2.4 provider module: that layering
is the point of keeping the characterization here.
-/

namespace Algsuperdiff.Section24.UnitCubeSkewW2Infinity

open Algsuperdiff.Frozen.Section24
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02 MeasureTheory
open scoped BigOperators ENNReal NNReal Matrix.Norms.Elementwise

noncomputable section

variable {d : ℕ}

/-! ## The unit cube carries a finite measure -/

/-- The volume measure of the frozen unit-cube carrier is finite. -/
private theorem isFiniteMeasure_valueCarrier (d : ℕ) :
    IsFiniteMeasure
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) := by
  let : Fact (MeasureTheory.volume (cubeSet (originCube d 0)) < ⊤) :=
    ⟨volume_cubeSet_lt_top (originCube d 0)⟩
  have h : IsFiniteMeasure (volumeMeasureOn (cubeSet (originCube d 0))) := by
    change IsFiniteMeasure (MeasureTheory.volume.restrict (cubeSet (originCube d 0)))
    infer_instance
  rwa [volumeMeasureOn, volume_restrict_cubeSet_eq_volume_restrict_openCubeSet] at h

/-! ## Measurability of the Euclidean matrix norm -/

/-- The sum of the absolute values of the entries is bounded by `d²` times the
entrywise supremum norm. -/
private theorem sum_abs_entries_le_sq_mul_norm (A : Mat d) :
    (∑ i : Fin d, ∑ j : Fin d, |A i j|) ≤ (d : ℝ) ^ 2 * ‖A‖ := by
  calc (∑ i : Fin d, ∑ j : Fin d, |A i j|)
      ≤ ∑ _i : Fin d, ∑ _j : Fin d, ‖A‖ := by
        gcongr with i _ j _
        simpa [Real.norm_eq_abs] using Matrix.norm_entry_le_entrywise_sup_norm A
    _ = (d : ℝ) ^ 2 * ‖A‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- The Chapter 2 matrix norm is Lipschitz for the entrywise supremum norm. -/
theorem lipschitzWith_matrixNorm :
    LipschitzWith ((d : ℝ≥0) ^ 2) (fun A : Mat d => Ch02.matrixNorm A) := by
  classical
  refine LipschitzWith.of_dist_le_mul fun A B => ?_
  have hentry : ∀ C D : Mat d,
      (∑ i : Fin d, ∑ j : Fin d, |C i j - D i j|) ≤ (d : ℝ) ^ 2 * ‖C - D‖ := by
    intro C D
    have hstep := sum_abs_entries_le_sq_mul_norm (C - D)
    simpa [Matrix.sub_apply] using hstep
  have hAB := hentry A B
  have hBA := hentry B A
  have hnorm : ‖B - A‖ = ‖A - B‖ := by
    rw [← norm_neg (B - A)]
    congr 1
    abel
  rw [hnorm] at hBA
  have h1 := Ch02.matrixNorm_le_matrixNorm_add_sum_abs_sub_entries A B
  have h2 := Ch02.matrixNorm_le_matrixNorm_add_sum_abs_sub_entries B A
  have hcast : (((d : ℝ≥0) ^ 2 : ℝ≥0) : ℝ) = (d : ℝ) ^ 2 := by push_cast; ring
  rw [Real.dist_eq, hcast, dist_eq_norm]
  rw [abs_sub_le_iff]
  constructor <;> linarith

theorem continuous_matrixNorm : Continuous (fun A : Mat d => Ch02.matrixNorm A) :=
  lipschitzWith_matrixNorm.continuous

/-- A matrix-valued function with a.e. strongly measurable entries is a.e.
strongly measurable. -/
theorem aestronglyMeasurable_of_entries {μ : Measure (Vec d)} {F : Vec d → Mat d}
    (hent : ∀ i j : Fin d, AEStronglyMeasurable (fun x => F x i j) μ) :
    AEStronglyMeasurable F μ := by
  classical
  have hfun : F = ∑ i : Fin d, ∑ j : Fin d,
      fun x : Vec d => (F x i j) • (Matrix.single i j (1 : ℝ)) := by
    funext x
    ext k l
    simp [Matrix.sum_apply, Matrix.single, ite_and, Finset.sum_ite_eq']
  rw [hfun]
  refine Finset.aestronglyMeasurable_sum _ fun i _ => ?_
  exact Finset.aestronglyMeasurable_sum _ fun j _ => (hent i j).smul_const _

/-! ## The pointwise Euclidean matrix norm of the frozen field -/

/-- The pointwise Euclidean matrix norm of the frozen field. -/
def matrixNormField (h : UnitCubeSkewW2Infinity d) : Vec d → ℝ :=
  fun x => Ch02.matrixNorm (h.toLInfSkewMatrixFieldOn.1.1 x)

theorem matrixNormField_nonneg (h : UnitCubeSkewW2Infinity d) (x : Vec d) :
    0 ≤ matrixNormField h x := Ch02.matrixNorm_nonneg _

theorem aestronglyMeasurable_matrixNormField_carrier (h : UnitCubeSkewW2Infinity d) :
    AEStronglyMeasurable (matrixNormField h)
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) := by
  have hent : ∀ i j : Fin d,
      AEStronglyMeasurable (fun x => h.toLInfSkewMatrixFieldOn.1.1 x i j)
        (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :=
    fun i j => (h.toLInfSkewMatrixFieldOn.1.2 i j).aestronglyMeasurable
  exact continuous_matrixNorm.comp_aestronglyMeasurable
    (aestronglyMeasurable_of_entries hent)

/-- The pointwise norm field is square integrable on the unit cube: it is
dominated by the sum of the absolute values of the frozen entries, and each
entry is in `L^∞` hence — the carrier being finite — in `L²`. -/
theorem memLp_matrixNormField_two_carrier (h : UnitCubeSkewW2Infinity d) :
    MemLp (matrixNormField h) 2
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) := by
  classical
  let := isFiniteMeasure_valueCarrier d
  have hentry : ∀ i : Fin d, ∀ j : Fin d,
      MemLp (fun x => |h.toLInfSkewMatrixFieldOn.1.1 x i j|) 2
        (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :=
    fun i j => ((h.toLInfSkewMatrixFieldOn.1.2 i j).mono_exponent le_top).abs
  have hsum : MemLp (fun x => ∑ i : Fin d, ∑ j : Fin d,
      |h.toLInfSkewMatrixFieldOn.1.1 x i j|) 2
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :=
    memLp_finsetSum _ fun i _ => memLp_finsetSum _ fun j _ => hentry i j
  refine hsum.of_le (aestronglyMeasurable_matrixNormField_carrier h)
    (Filter.Eventually.of_forall fun x => ?_)
  have hnn : (0 : ℝ) ≤ ∑ i : Fin d, ∑ j : Fin d,
      |h.toLInfSkewMatrixFieldOn.1.1 x i j| := by positivity
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (matrixNormField_nonneg h x),
    abs_of_nonneg hnn]
  exact (Ch02.matrixNorm_le_matNorm _).trans (Ch02.matNorm_le_sum_abs_entries _)

/-! ## The characterization of the frozen `L²` value norm -/

/-- **The frozen `L²` value norm is the mean square of `|h|` on the unit cube.**
This is the only place where `UnitCubeSkewW2Infinity.valueL2` is unfolded. -/
theorem valueL2_sq_eq_integral (h : UnitCubeSkewW2Infinity d) :
    h.valueL2 ^ 2 =
      ∫ x, matrixNormField h x ^ 2
        ∂ volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) := by
  classical
  have hmem : MemLp (matrixNormField h) 2
      (volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d))) :=
    memLp_matrixNormField_two_carrier h
  have hkey := MemLp.eLpNorm_eq_integral_rpow_norm (p := (2 : ℝ≥0∞))
    (by norm_num) (by norm_num) hmem
  have htoReal : ((2 : ℝ≥0∞).toReal) = (2 : ℝ) := by norm_num
  rw [htoReal] at hkey
  have hInt : ∫ x, ‖matrixNormField h x‖ ^ (2 : ℝ)
        ∂ volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) =
      ∫ x, matrixNormField h x ^ 2
        ∂ volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show ‖matrixNormField h x‖ ^ (2 : ℝ) = matrixNormField h x ^ (2 : ℕ)
    rw [Real.norm_eq_abs, abs_of_nonneg (matrixNormField_nonneg h x),
      ← Real.rpow_natCast (matrixNormField h x) 2]
    norm_num
  rw [hInt] at hkey
  have hIntnn : (0 : ℝ) ≤ ∫ x, matrixNormField h x ^ 2
      ∂ volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)) :=
    integral_nonneg fun x => by positivity
  have hval : h.valueL2 =
      (∫ x, matrixNormField h x ^ 2
        ∂ volumeMeasureOn ((cubeDomain (originCube d 0) : Domain d) : Set (Vec d)))
        ^ ((2 : ℝ)⁻¹) := by
    show (eLpNorm (matrixNormField h) 2 _).toReal = _
    rw [hkey, ENNReal.toReal_ofReal (Real.rpow_nonneg hIntnn _)]
  rw [hval, ← Real.rpow_natCast _ 2, ← Real.rpow_mul hIntnn]
  norm_num

end

end Algsuperdiff.Section24.UnitCubeSkewW2Infinity
