/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.SequenceLaw
public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.J2Observable
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.SubgaussianTail
public import LeanPool.Superdiffusion.Algsuperdiff.Probability.StationaryProjection
public import LeanPool.HighContrastHomogenization.Support.Ambient.CoefficientFieldHilbert
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# StationaryValueProjection

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Stationary projection on the CoarseGraining regular-coefficient carrier

This is the carrier-specific J4 bridge.  It uses CoarseGraining's
`RegCoeffField d` and its canonical sigma-algebra directly: no continuous-path
replacement carrier is introduced.  It pushes the canonical zero-shell marginal
through `forgetShell`.
-/

open MeasureTheory
open HCPolySupport
open scoped BigOperators Matrix.Norms.Elementwise

namespace Algsuperdiff.Frozen.Assumptions.ShellField

noncomputable section

variable {d : ℕ}

/-! ## The real translation action on CoarseGraining's carrier -/

/-- CoarseGraining's real translation maps form the manuscript action `(z +ᵥ a)(x)
= a(x + z)`. -/
noncomputable instance regCoeffFieldAddAction : AddAction (Vec d) (RegCoeffField d) where
  vadd := translateReg
  zero_vadd := by
    intro a
    apply RegCoeffField.ext
    intro x
    change a (x + 0) = a x
    rw [add_zero]
  add_vadd := by
    intro z w a
    apply RegCoeffField.ext
    intro x
    change a (x + (z + w)) = a ((x + z) + w)
    rw [add_assoc]

/-- Only fixed-shift measurability is needed for the stationary Hilbert-space
construction, and it is exactly CoarseGraining's proved `translateReg`
measurability. -/
noncomputable instance regCoeffFieldMeasurableConstVAdd :
    MeasurableConstVAdd (Vec d) (RegCoeffField d) where
  measurable_const_vadd := fun z ↦ by
    change Measurable (translateReg (d := d) z)
    exact measurable_translateReg z

/-! ## The CoarseGraining pushforward of the shell-zero law -/

/-- Measurability of the literal shell-zero map into CoarseGraining's regular-field
carrier. -/
theorem measurable_zeroShellRegMap :
    Measurable (forgetShell (d := d) ∘ fun F : ℤ → ShellField d ↦ F 0) :=
  measurable_forgetShell.comp measurable_zeroShellMap

/-- The probability law of the regular coefficient field in shell zero.  This
is precisely `map (forgetShell ∘ coord 0) P`; its construction requires the
proved measurable map above and therefore has no totalized-map fallback. -/
noncomputable def zeroShellRegLaw
    (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d)) :
    MeasureTheory.ProbabilityMeasure (RegCoeffField d) :=
  P.map (forgetShell (d := d) ∘ fun F : ℤ → ShellField d ↦ F 0)

/-- The direct regular-field zero-shell law is exactly the measurable
`forgetShell` pushforward of the literal zero-coordinate shell law. -/
theorem zeroShellRegLaw_toMeasure_eq_map_forgetShell
    (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d)) :
    (zeroShellRegLaw P).toMeasure =
      Measure.map forgetShell (zeroShellLaw P).toMeasure := by
  change
    Measure.map (forgetShell ∘ fun F : ℤ → ShellField d ↦ F 0) P.toMeasure =
      Measure.map forgetShell
        (Measure.map (fun F : ℤ → ShellField d ↦ F 0) P.toMeasure)
  exact (Measure.map_map measurable_forgetShell measurable_zeroShellMap).symm

/-- The shell-field and CoarseGraining regular-field translation conventions agree
literally: both send `a(x)` to `a(x + z)`. -/
theorem forgetShell_translateReg (z : Vec d) (j : ShellField d) :
    forgetShell (translate z j) = translateReg z (forgetShell j) :=
  forgetShell_translate z j

/-- Full real-translation invariance of the literal zero-shell law descends to the
CoarseGraining regular-field pushforward.  No stationarity hypothesis is added
on the target law. -/
theorem zeroShellRegLaw_stationary_of_zeroShellLaw_stationary
    (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d))
    (hstationary : ∀ z : Vec d,
      Measure.map (translate z) (zeroShellLaw P).toMeasure =
        (zeroShellLaw P).toMeasure) :
    ∀ z : Vec d,
      Measure.map (translateReg z) (zeroShellRegLaw P).toMeasure =
        (zeroShellRegLaw P).toMeasure := by
  intro z
  let μ := (zeroShellLaw P).toMeasure
  calc
    Measure.map (translateReg z) (zeroShellRegLaw P).toMeasure =
        Measure.map (translateReg z) (Measure.map forgetShell μ) := by
      rw [zeroShellRegLaw_toMeasure_eq_map_forgetShell]
    _ = Measure.map (translateReg z ∘ forgetShell) μ :=
      Measure.map_map (measurable_translateReg z) measurable_forgetShell
    _ = Measure.map (forgetShell ∘ translate z) μ := by
      apply congrArg (fun f : ShellField d → RegCoeffField d ↦ Measure.map f μ)
      funext j
      exact (forgetShell_translateReg z j).symm
    _ = Measure.map forgetShell (Measure.map (translate z) μ) :=
      (Measure.map_map measurable_forgetShell (measurable_translate z)).symm
    _ = Measure.map forgetShell μ := by rw [hstationary z]
    _ = (zeroShellRegLaw P).toMeasure :=
      (zeroShellRegLaw_toMeasure_eq_map_forgetShell P).symm

/-- Full real stationarity of the zero-shell law supplies the invariant measure
structure used by the stationary projection. -/
theorem zeroShellRegLaw_vaddInvariant
    (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d))
    (hstationary : ∀ z : Vec d,
      Measure.map (translateReg z) (zeroShellRegLaw P).toMeasure =
        (zeroShellRegLaw P).toMeasure) :
    VAddInvariantMeasure (Vec d) (RegCoeffField d) (zeroShellRegLaw P).toMeasure where
  measure_preimage_vadd := by
    intro z s hs
    change (zeroShellRegLaw P).toMeasure ((translateReg z) ⁻¹' s) =
      (zeroShellRegLaw P).toMeasure s
    rw [← Measure.map_apply (measurable_translateReg z) hs]
    exact congrArg (fun m : Measure (RegCoeffField d) ↦ m s) (hstationary z)

/-! ## The literal origin forcing and its `L²` projection -/

/-- Evaluate matrix-vector multiplication at a fixed vector as a linear map. -/
noncomputable def matVecMulLinear (e : Vec d) : Mat d →ₗ[ℝ] Vec d where
  toFun := fun A ↦ matVecMul A e
  map_add' := by
    intro A B
    ext i
    change ∑ j, (A i j + B i j) * e j =
      (∑ j, A i j * e j) + ∑ j, B i j * e j
    simp_rw [add_mul]
    exact Finset.sum_add_distrib
  map_smul' := by
    intro c A
    ext i
    simp [matVecMul, Finset.mul_sum, mul_assoc]

/-- The literal matrix-vector forcing at the spatial origin, promoted to
CoarseGraining's Euclidean Hilbert carrier. -/
def originForcing (e : Vec d) (a : RegCoeffField d) : HilbertVec d :=
  HilbertVec.ofVec (matVecMul (a 0) e)

theorem measurable_originForcing (e : Vec d) : Measurable (originForcing (d := d) e) := by
  have hEval : Measurable (fun a : RegCoeffField d ↦ a 0) :=
    measurable_matrix_of_entries fun i j ↦ measurable_apply_entry 0 i j
  change Measurable (fun a : RegCoeffField d ↦ HilbertVec.ofVec (matVecMul (a 0) e))
  exact (HilbertVec.ofVecL d).continuous.measurable.comp
    ((matVecMulLinear e).continuous_of_finiteDimensional.measurable.comp hEval)

theorem norm_sq_originForcing (e : Vec d) (a : RegCoeffField d) :
    ‖originForcing e a‖ ^ 2 =
      vecDot (matVecMul (a 0) e) (matVecMul (a 0) e) :=
  HilbertVec.norm_sq_ofVec _

/-- A unit input vector bounds the literal origin forcing by the Euclidean
operator norm of the coefficient matrix at the origin. -/
theorem norm_originForcing_le_matrixOperatorNorm (e : Vec d) (a : RegCoeffField d)
    (he : Book.Ch02.vecNorm e = 1) :
    ‖originForcing e a‖ ≤ Book.Ch02.matrixOperatorNorm (a 0) := by
  have hnorm : ‖originForcing e a‖ = Book.Ch02.vecNorm (matVecMul (a 0) e) := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (Book.Ch02.vecNorm_nonneg _)]
    rw [norm_sq_originForcing, Book.Ch02.vecNorm_sq_eq_vecNormSq]
    rfl
  rw [hnorm]
  calc
    Book.Ch02.vecNorm (matVecMul (a 0) e) ≤
        Book.Ch02.matrixOperatorNorm (a 0) * Book.Ch02.vecNorm e :=
      Book.Ch02.vecNorm_matVecMul_le_matrixOperatorNorm_mul_vecNorm _ _
    _ = Book.Ch02.matrixOperatorNorm (a 0) := by rw [he, mul_one]

private theorem matrixOperatorNorm_le_sq_mul_entrywiseNorm (A : Mat d) :
    Book.Ch02.matrixOperatorNorm A ≤ (d : ℝ) ^ 2 * ‖A‖ := by
  calc
    Book.Ch02.matrixOperatorNorm A ≤ Book.Ch02.matrixFrobeniusNorm A :=
      Book.Ch02.matrixOperatorNorm_le_matrixFrobeniusNorm A
    _ ≤ ∑ i, ∑ k, |A i k| :=
      Book.Ch02.matrixFrobeniusNorm_le_sum_abs_entries A
    _ ≤ ∑ _i : Fin d, ∑ _k : Fin d, ‖A‖ := by
      gcongr with i k
      simpa [Real.norm_eq_abs] using Matrix.norm_entry_le_entrywise_sup_norm A
    _ = (d : ℝ) ^ 2 * ‖A‖ := by
      simp [pow_two]
      ring

/-- The value part of the J2 cube observable controls the coefficient matrix
at the spatial origin. -/
theorem matrixOperatorNorm_zero_le_unitCubeValueNorm (j : ShellField d) :
    Book.Ch02.matrixOperatorNorm (j 0) ≤ unitCubeValueNorm j := by
  unfold unitCubeValueNorm
  apply le_csSup
  · let K : Set (Vec d) := Metric.closedBall
      (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))
    have hK : IsCompact K := by
      simpa [K] using isCompact_closedBall
        (cubeCenter (originCube d 0)) (cubeRadius (originCube d 0))
    obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn j.1.1.continuous.continuousOn
    refine ⟨max 0 ((d : ℝ) ^ 2 * C), ?_⟩
    rintro r ⟨o, rfl⟩
    cases o with
    | none => exact le_max_left _ _
    | some x =>
        have hx : x.1 ∈ K := by
          apply Metric.ball_subset_closedBall
          rw [ball_cubeCenter_eq_openCubeSet]
          exact x.2
        calc
          Book.Ch02.matrixOperatorNorm (j x.1) ≤
              (d : ℝ) ^ 2 * ‖j x.1‖ :=
            matrixOperatorNorm_le_sq_mul_entrywiseNorm _
          _ ≤ (d : ℝ) ^ 2 * C := by
            gcongr
            exact hC x.1 hx
          _ ≤ max 0 ((d : ℝ) ^ 2 * C) := le_max_right _ _
  · refine ⟨some ⟨0, ?_⟩, rfl⟩
    rw [mem_openCubeSet_originCube_iff]
    intro i
    norm_num

private theorem unitCubeValueNorm_le_j2Observable (j : ShellField d) :
    unitCubeValueNorm j ≤ j2Observable d j := by
  calc
    unitCubeValueNorm j ≤
        unitCubeValueNorm j + Real.sqrt d * unitCubeDerivNorm j :=
      le_add_of_nonneg_right
        (mul_nonneg (Real.sqrt_nonneg _) (unitCubeDerivNorm_nonneg j))
    _ ≤ unitCubeValueNorm j + Real.sqrt d * unitCubeDerivNorm j +
        (d : ℝ) * unitCubeSecondDerivNorm j :=
      le_add_of_nonneg_right
        (mul_nonneg (Nat.cast_nonneg d) (unitCubeSecondDerivNorm_nonneg j))
    _ = j2Observable d j := rfl

/-- The literal strict J2 Gaussian tail supplies the `L²` integrability of
the origin forcing required by the stationary projection.  Measurability,
nonnegativity, and domination are consequences, not hypotheses. -/
theorem memLp_originForcing_of_j2_tail
    (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d))
    (htail : ∀ t : ℝ, 1 ≤ t →
      P.toMeasure {F | t < j2Observable d (F 0)} ≤
        ENNReal.ofReal (Real.exp (-(t ^ 2))))
    (e : Vec d) (he : Book.Ch02.vecNorm e = 1) :
    MemLp (originForcing e) 2 (zeroShellRegLaw P).toMeasure := by
  let X : (ℤ → ShellField d) → ℝ := fun F ↦ j2Observable d (F 0)
  have hXmeas : Measurable X :=
    (j2Observable_measurable d).comp measurable_zeroShellMap
  have hXnonneg : ∀ F, 0 ≤ X F := fun F ↦ j2Observable_nonneg d (F 0)
  have hXmem : MemLp X 2 P.toMeasure :=
    Algsuperdiff.Probability.memLp_two_of_gaussian_tail hXmeas hXnonneg htail
  have hpull : MemLp
      (originForcing e ∘ (forgetShell ∘ fun F : ℤ → ShellField d ↦ F 0))
      2 P.toMeasure := by
    apply hXmem.mono'
    · exact ((measurable_originForcing e).comp
        (measurable_zeroShellRegMap (d := d))).aestronglyMeasurable
    · exact Filter.Eventually.of_forall fun F ↦ by
        calc
          ‖originForcing e (forgetShell (F 0))‖ ≤
              Book.Ch02.matrixOperatorNorm ((forgetShell (F 0)) 0) :=
            norm_originForcing_le_matrixOperatorNorm e (forgetShell (F 0)) he
          _ = Book.Ch02.matrixOperatorNorm ((F 0) 0) := rfl
          _ ≤ unitCubeValueNorm (F 0) :=
            matrixOperatorNorm_zero_le_unitCubeValueNorm (F 0)
          _ ≤ X F := unitCubeValueNorm_le_j2Observable (F 0)
  change MemLp (originForcing e) 2
    (Measure.map (forgetShell ∘ fun F : ℤ → ShellField d ↦ F 0) P.toMeasure)
  exact (memLp_map_measure_iff
    (measurable_originForcing e).aestronglyMeasurable
    (measurable_zeroShellRegMap (d := d)).aemeasurable).mpr hpull

/-- The canonical `L²` element represented by the source's origin forcing. -/
def zeroShellForcingL2 (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d)) (e : Vec d)
    (hmem : MemLp (originForcing e) 2 (zeroShellRegLaw P).toMeasure) :
    Algsuperdiff.Probability.Stationary.VectorL2 d (zeroShellRegLaw P).toMeasure :=
  hmem.toLp (originForcing e)

theorem coeFn_zeroShellForcingL2
    (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d)) (e : Vec d)
    (hmem : MemLp (originForcing e) 2 (zeroShellRegLaw P).toMeasure) :
    (zeroShellForcingL2 P e hmem : RegCoeffField d → HilbertVec d) =ᵐ[
      (zeroShellRegLaw P).toMeasure] originForcing e :=
  hmem.coeFn_toLp

/-- The stationary potential subspace for the zero-shell regular-field law. -/
noncomputable def zeroShellPotentialSubspace
    (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d))
    (hstationary : ∀ z : Vec d,
      Measure.map (translateReg z) (zeroShellRegLaw P).toMeasure =
        (zeroShellRegLaw P).toMeasure) :
    Submodule ℝ (Algsuperdiff.Probability.Stationary.VectorL2 d
      (zeroShellRegLaw P).toMeasure) := by
  letI := zeroShellRegLaw_vaddInvariant P hstationary
  exact Algsuperdiff.Probability.Stationary.stationaryPotentialSubspace
    (μ := (zeroShellRegLaw P).toMeasure) (d := d)

/-- The canonical potential part of the stationary origin forcing. -/
noncomputable def zeroShellProjectedForcing
    (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d))
    (hstationary : ∀ z : Vec d,
      Measure.map (translateReg z) (zeroShellRegLaw P).toMeasure =
        (zeroShellRegLaw P).toMeasure)
    (e : Vec d) (hmem : MemLp (originForcing e) 2 (zeroShellRegLaw P).toMeasure) :
    Algsuperdiff.Probability.Stationary.VectorL2 d (zeroShellRegLaw P).toMeasure := by
  letI := zeroShellRegLaw_vaddInvariant P hstationary
  exact Algsuperdiff.Probability.Stationary.stationaryPotentialProjection
    (zeroShellForcingL2 P e hmem)

/-- The canonical source-sign potential corrector.  ABK26 solves `-Δw =
div F` and requires `F + ∇w` to be stationary-solenoidal; therefore `∇w`
is the negative of the positive orthogonal projection of `F` onto the
stationary potential subspace. -/
noncomputable def zeroShellPotentialCorrector
    (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d))
    (hstationary : ∀ z : Vec d,
      Measure.map (translateReg z) (zeroShellRegLaw P).toMeasure =
        (zeroShellRegLaw P).toMeasure)
    (e : Vec d) (hmem : MemLp (originForcing e) 2 (zeroShellRegLaw P).toMeasure) :
    Algsuperdiff.Probability.Stationary.VectorL2 d
      (zeroShellRegLaw P).toMeasure :=
  -zeroShellProjectedForcing P hstationary e hmem

end

end Algsuperdiff.Frozen.Assumptions.ShellField
