/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.WholePlaneLocalCompactnessUnconditional
public import LeanPool.FastDynamo.Analysis.WholePlaneH2DenseEmbedding
public import LeanPool.FastDynamo.Analysis.WholePlaneL4FormPerturbationHolder
public import LeanPool.FastDynamo.Analysis.WholePlaneExteriorCutoff

/-!
# The two-component whole-plane substrate

The paper writes the local model on two-component horizontal fields
`b : ℝ² → ℂ²` (`eq:horizontal-induction`).
The whole-plane Sobolev layer of `FastDynamo/Analysis/WholePlane*.lean` is already generic
in the fibre, so this module is almost entirely re-instantiation at

`C2 = EuclideanSpace ℂ (Fin 2)`

(the fibre abbreviation introduced by the torus layer in `FastDynamo/Fourier/PeriodicH2.lean`).

Collected here are the facts that the two-component local seed uses: the graph norm of
`H¹(ℝ²; ℂ²)`, scalar coordinates on `L²`, on tempered distributions and on `H¹`, the
Plancherel layer, the Laplacian, density of the physical embeddings, the exterior cutoffs,
the local Rellich compactness of supported coefficient multiplication, and the
two-dimensional Gagliardo-Nirenberg-Sobolev embedding `H¹(ℝ²; ℂ²) ↪ L⁴(ℝ²; ℂ²)`.

The unit-circle slice layer (`Analysis/WholePlaneUnitCircleSlices`) is scalar geometry on
`ℝ`, and the piecewise weak-derivative layer (`Analysis/WholePlanePiecewiseSliceIBP`)
is already stated for a general fibre `F`; neither needs a `C2` instantiation.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal FourierTransform Laplacian LineDeriv SchwartzMap

/-! ## The spaces -/

/-- Two-component complex `L²(ℝ²; ℂ²)`, the pivot space of the horizontal operator. -/
abbrev WholePlaneC2L2 := WholePlaneL2 C2

/-- Two-component complex weak `H¹(ℝ²; ℂ²)`, the form domain of `eq:jump-sectorial-form`. -/
abbrev WholePlaneC2H1 := WholePlaneH1 C2

/-- Two-component complex weak `H²(ℝ²; ℂ²)`, the strong domain of `eq:horizontal-induction`. -/
abbrev WholePlaneC2H2 := WholePlaneH2 C2

/-- Essentially bounded two-component coefficients on the transverse plane. -/
abbrev WholePlaneC2LInf := WholePlaneLInf C2

/-- Two-component complex `L⁴(ℝ²; ℂ²)`. -/
abbrev WholePlaneC2L4 := Lp C2 4 (volume : Measure WholePlane)

/-- The squared whole-plane `H¹` graph norm is the sum of the squared `L²` norms of the field
and of its two weak coordinate derivatives.  The `H¹` jet is an `ℓ²` product, so this is the
definition unfolded; it is stated once here because every quantitative estimate below uses it. -/
theorem norm_sq_wholePlaneH1 (F : Type*) [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [CompleteSpace F] (u : WholePlaneH1 F) :
    ‖u‖ ^ 2 =
      ‖wholePlaneH1Embedding F u‖ ^ 2 +
        (‖wholePlaneH1FirstDerivative F 0 u‖ ^ 2 +
          ‖wholePlaneH1FirstDerivative F 1 u‖ ^ 2) := by
  have h : ‖u‖ = ‖u.1‖ := rfl
  rw [h, PiLp.norm_sq_eq_of_L2]
  simp [Fintype.sum_option, Fin.sum_univ_two]

/-- The squared `H¹(ℝ²; ℂ²)` graph norm, the two-component case of `norm_sq_wholePlaneH1`. -/
theorem norm_sq_wholePlaneC2H1 (u : WholePlaneC2H1) :
    ‖u‖ ^ 2 =
      ‖wholePlaneH1Embedding C2 u‖ ^ 2 +
        (‖wholePlaneH1FirstDerivative C2 0 u‖ ^ 2 +
          ‖wholePlaneH1FirstDerivative C2 1 u‖ ^ 2) :=
  norm_sq_wholePlaneH1 C2 u

/-! ## Scalar coordinates -/

/-- Extract one scalar coordinate from a two-component whole-plane `L²` field. -/
def wholePlaneC2CoordL2 (i : Fin 2) :
    WholePlaneC2L2 →L[ℂ] WholePlaneScalarL2 :=
  (EuclideanSpace.proj i).compLpL 2 volume

/-- Insert a scalar whole-plane `L²` field into one coordinate of a two-component field. -/
def wholePlaneScalarToC2CoordL2 (i : Fin 2) :
    WholePlaneScalarL2 →L[ℂ] WholePlaneC2L2 :=
  (scalarToVecPoint i).compLpL 2 volume

/-- A scalar coordinate projection is contractive on two-component `L²`. -/
theorem norm_wholePlaneC2CoordL2_apply_le (i : Fin 2) (f : WholePlaneC2L2) :
    ‖wholePlaneC2CoordL2 i f‖ ≤ ‖f‖ := by
  have hproj : ‖(EuclideanSpace.proj (𝕜 := ℂ) i)‖ ≤ 1 := by
    refine (EuclideanSpace.proj (𝕜 := ℂ) i).opNorm_le_bound zero_le_one ?_
    intro x
    simpa using PiLp.norm_apply_le x i
  have hcoord : ‖wholePlaneC2CoordL2 i‖ ≤ 1 :=
    (ContinuousLinearMap.norm_compLpL_le (EuclideanSpace.proj (𝕜 := ℂ) i)).trans hproj
  calc
    ‖wholePlaneC2CoordL2 i f‖ ≤ ‖wholePlaneC2CoordL2 i‖ * ‖f‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ 1 * ‖f‖ := mul_le_mul_of_nonneg_right hcoord (norm_nonneg _)
    _ = ‖f‖ := one_mul _

/-- Extracting a coordinate after scalar coordinate insertion gives the inserted field in the
matching coordinate and zero otherwise. -/
theorem wholePlaneC2CoordL2_scalarToC2CoordL2
    (j i : Fin 2) (a : WholePlaneScalarL2) :
    wholePlaneC2CoordL2 j (wholePlaneScalarToC2CoordL2 i a) =
      if i = j then a else 0 := by
  apply Lp.ext
  have hsingle := (scalarToVecPoint (ι := Fin 2) i).coeFn_compLpL (p := 2)
    (μ := (volume : Measure WholePlane)) a
  have hproj := (EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL (p := 2)
    (μ := (volume : Measure WholePlane)) (wholePlaneScalarToC2CoordL2 i a)
  filter_upwards [hsingle, hproj] with x hs hp
  change (((EuclideanSpace.proj (𝕜 := ℂ) j).compLp
    (wholePlaneScalarToC2CoordL2 i a) : WholePlaneScalarL2) : WholePlane → ℂ) x = _
  change (((EuclideanSpace.proj (𝕜 := ℂ) j).compLp
    (wholePlaneScalarToC2CoordL2 i a) : WholePlaneScalarL2) : WholePlane → ℂ) x = _ at hp
  change (((scalarToVecPoint (ι := Fin 2) i).compLp a : WholePlaneC2L2) :
    WholePlane → C2) x = _ at hs
  rw [hp]
  change (EuclideanSpace.proj (𝕜 := ℂ) j)
    ((((scalarToVecPoint (ι := Fin 2) i).compLp a : WholePlaneC2L2) :
      WholePlane → C2) x) = _
  rw [hs]
  by_cases hji : j = i
  · subst j
    simp [scalarToVecPoint]
  · simp [scalarToVecPoint, hji, Ne.symm hji]

/-- Equality of two-component whole-plane `L²` classes can be checked coordinatewise. -/
theorem wholePlaneC2L2_ext_coord {f g : WholePlaneC2L2}
    (h : ∀ i : Fin 2, wholePlaneC2CoordL2 i f = wholePlaneC2CoordL2 i g) :
    f = g := by
  apply Lp.ext
  have hf : ∀ i : Fin 2,
      (wholePlaneC2CoordL2 i f : WholePlane → ℂ) =ᵐ[volume]
        fun x => (EuclideanSpace.proj i) ((f : WholePlane → C2) x) := by
    intro i
    simpa only [wholePlaneC2CoordL2] using
      (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
        (p := 2) (μ := (volume : Measure WholePlane)) f
  have hg : ∀ i : Fin 2,
      (wholePlaneC2CoordL2 i g : WholePlane → ℂ) =ᵐ[volume]
        fun x => (EuclideanSpace.proj i) ((g : WholePlane → C2) x) := by
    intro i
    simpa only [wholePlaneC2CoordL2] using
      (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
        (p := 2) (μ := (volume : Measure WholePlane)) g
  have hfg : ∀ i : Fin 2,
      (wholePlaneC2CoordL2 i f : WholePlane → ℂ) =ᵐ[volume]
        (wholePlaneC2CoordL2 i g : WholePlane → ℂ) := by
    intro i
    rw [h i]
  filter_upwards [ae_all_iff.2 hf, ae_all_iff.2 hg, ae_all_iff.2 hfg] with x hfx hgx hfgx
  apply PiLp.ext
  intro i
  change (EuclideanSpace.proj i) ((f : WholePlane → C2) x) =
    (EuclideanSpace.proj i) ((g : WholePlane → C2) x)
  rw [← hfx i, hfgx i, hgx i]

/-! ## Coordinates on tempered distributions and on `H¹` -/

/-- Extract the `i`-th coordinate of a `C2`-valued tempered distribution. -/
def wholePlaneC2CoordTempered (i : Fin 2) :
    TemperedDistribution WholePlane C2 →L[ℂ] TemperedDistribution WholePlane ℂ :=
  WholePlaneHorizontalFibre.fibreTempered (EuclideanSpace.proj i)

/-- Coordinate extraction is applied after testing. -/
@[simp] theorem wholePlaneC2CoordTempered_apply_apply (i : Fin 2)
    (T : TemperedDistribution WholePlane C2) (f : SchwartzMap WholePlane ℂ) :
    wholePlaneC2CoordTempered i T f = (T f) i :=
  rfl

/-- Coordinate extraction commutes with distributional line differentiation. -/
theorem wholePlaneC2CoordTempered_lineDeriv (i : Fin 2) (e : WholePlane)
    (T : TemperedDistribution WholePlane C2) :
    wholePlaneC2CoordTempered i (∂_{e} T) = ∂_{e} (wholePlaneC2CoordTempered i T) :=
  WholePlaneHorizontalFibre.fibreTempered_lineDeriv (EuclideanSpace.proj i) e T

/-- Coordinate extraction commutes with the canonical `L² → tempered distribution` map. -/
theorem wholePlaneC2CoordTempered_l2 (i : Fin 2) (b : WholePlaneC2L2) :
    wholePlaneC2CoordTempered i (wholePlaneL2ToTempered C2 b) =
      wholePlaneL2ToTempered ℂ (wholePlaneC2CoordL2 i b) :=
  WholePlaneHorizontalFibre.fibreTempered_l2 (EuclideanSpace.proj i) b

/-- Continuous ambient scalar jet obtained by extracting one coordinate of a two-component
weak `H¹` jet. -/
def wholePlaneC2CoordH1Ambient (i : Fin 2) :
    WholePlaneC2H1 →L[ℂ] WholePlaneH1Ambient ℂ :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : WholePlaneJet1Index => WholePlaneScalarL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun q => q.elim
      ((wholePlaneC2CoordL2 i).comp (wholePlaneH1Embedding C2))
      (fun j => (wholePlaneC2CoordL2 i).comp (wholePlaneH1FirstDerivative C2 j)))

/-- The value slot of the coordinate jet is the `i`-th coordinate of the `L²` value. -/
@[simp] theorem wholePlaneC2CoordH1Ambient_none (i : Fin 2) (b : WholePlaneC2H1) :
    wholePlaneC2CoordH1Ambient i b none =
      wholePlaneC2CoordL2 i (wholePlaneH1Embedding C2 b) :=
  rfl

/-- The `j`-th derivative slot of the coordinate jet is the `i`-th coordinate of `∂_j b`. -/
@[simp] theorem wholePlaneC2CoordH1Ambient_some (i : Fin 2) (b : WholePlaneC2H1) (j : Fin 2) :
    wholePlaneC2CoordH1Ambient i b (some j) =
      wholePlaneC2CoordL2 i (wholePlaneH1FirstDerivative C2 j b) :=
  rfl

/-- Coordinate extraction as a bounded map from two-component weak `H¹` to scalar weak `H¹`. -/
def wholePlaneC2CoordH1 (i : Fin 2) :
    WholePlaneC2H1 →L[ℂ] WholePlaneScalarH1 :=
  (wholePlaneC2CoordH1Ambient i).codRestrict (wholePlaneH1Graph ℂ) (fun b => by
    rw [mem_wholePlaneH1Graph_iff]
    intro j
    simp only [wholePlaneC2CoordH1Ambient_none, wholePlaneC2CoordH1Ambient_some]
    rw [← wholePlaneC2CoordTempered_l2, ← wholePlaneC2CoordTempered_l2,
      ← wholePlaneC2CoordTempered_lineDeriv, wholePlaneH1_firstDerivative_distribution])

/-- The `L²` value of a scalar coordinate of a two-component `H¹` field. -/
theorem wholePlaneH1Embedding_c2CoordH1 (i : Fin 2) (b : WholePlaneC2H1) :
    wholePlaneH1Embedding ℂ (wholePlaneC2CoordH1 i b) =
      wholePlaneC2CoordL2 i (wholePlaneH1Embedding C2 b) :=
  rfl

/-- Scalar coordinate extraction on `H¹` commutes with the `j`-th weak derivative. -/
theorem wholePlaneH1FirstDerivative_c2CoordH1 (i j : Fin 2) (b : WholePlaneC2H1) :
    wholePlaneH1FirstDerivative ℂ j (wholePlaneC2CoordH1 i b) =
      wholePlaneC2CoordL2 i (wholePlaneH1FirstDerivative C2 j b) :=
  rfl

/-- Scalar coordinate extraction is contractive on the weak `H¹(ℝ²; ℂ²)` graph. -/
theorem norm_wholePlaneC2CoordH1_apply_le (i : Fin 2) (b : WholePlaneC2H1) :
    ‖wholePlaneC2CoordH1 i b‖ ≤ ‖b‖ := by
  have hsq : ‖wholePlaneC2CoordH1 i b‖ ^ 2 ≤ ‖b‖ ^ 2 := by
    rw [norm_sq_wholePlaneH1 ℂ (wholePlaneC2CoordH1 i b), norm_sq_wholePlaneC2H1 b,
      wholePlaneH1Embedding_c2CoordH1, wholePlaneH1FirstDerivative_c2CoordH1,
      wholePlaneH1FirstDerivative_c2CoordH1]
    have h0 := norm_wholePlaneC2CoordL2_apply_le i (wholePlaneH1Embedding C2 b)
    have h1 := norm_wholePlaneC2CoordL2_apply_le i (wholePlaneH1FirstDerivative C2 0 b)
    have h2 := norm_wholePlaneC2CoordL2_apply_le i (wholePlaneH1FirstDerivative C2 1 b)
    have e0 := norm_nonneg (wholePlaneC2CoordL2 i (wholePlaneH1Embedding C2 b))
    have e1 := norm_nonneg (wholePlaneC2CoordL2 i (wholePlaneH1FirstDerivative C2 0 b))
    have e2 := norm_nonneg (wholePlaneC2CoordL2 i (wholePlaneH1FirstDerivative C2 1 b))
    nlinarith [h0, h1, h2, e0, e1, e2]
  nlinarith [hsq, norm_nonneg (wholePlaneC2CoordH1 i b), norm_nonneg b]

/-! ## Gradient, Laplacian, and the canonical inclusions -/

/-- The canonical continuous inclusion `H²(ℝ²; ℂ²) → H¹(ℝ²; ℂ²)`. -/
abbrev wholePlaneC2H2ToH1 : WholePlaneC2H2 →L[ℂ] WholePlaneC2H1 :=
  wholePlaneH2ToH1 C2

/-! ## Density of the physical embeddings -/

/-- The physical projection `H²(ℝ²; ℂ²) → L²(ℝ²; ℂ²)` has dense range. -/
theorem denseRange_wholePlaneC2H2Embedding : DenseRange (wholePlaneH2Embedding C2) :=
  denseRange_wholePlaneH2Embedding C2

/-- The physical projection `H¹(ℝ²; ℂ²) → L²(ℝ²; ℂ²)` has dense range.  This is what makes
the form domain of `eq:jump-sectorial-form` an admissible Kato form domain. -/
theorem denseRange_wholePlaneC2H1Embedding : DenseRange (wholePlaneH1Embedding C2) := by
  have h := denseRange_wholePlaneC2H2Embedding
  have heq : wholePlaneH2Embedding C2 =
      (wholePlaneH1Embedding C2) ∘ (wholePlaneH2ToH1 C2) := by
    funext u
    exact (wholePlaneH1Embedding_H2ToH1 C2 u).symm
  rw [heq] at h
  exact DenseRange.of_comp h

/-- The physical projection `H¹(ℝ²; ℂ²) → L²(ℝ²; ℂ²)` is injective. -/
theorem wholePlaneC2H1Embedding_injective : Function.Injective (wholePlaneH1Embedding C2) :=
  wholePlaneH1Embedding_injective C2

/-! ## Exterior cutoffs -/

/-- Multiplication by the indicator of the exterior `{R < ‖y‖}` on `L²(ℝ²; ℂ²)`. -/
abbrev wholePlaneC2ExteriorCutoff (R : ℝ) : WholePlaneC2L2 →L[ℂ] WholePlaneC2L2 :=
  wholePlaneExteriorCutoff (E := C2) R

/-- Two-component exterior cutoffs converge strongly to zero as the radius grows. -/
theorem tendsto_wholePlaneC2ExteriorCutoff_apply_zero (f : WholePlaneC2L2) :
    Filter.Tendsto (fun R : ℝ ↦ wholePlaneC2ExteriorCutoff R f) Filter.atTop (nhds 0) :=
  tendsto_wholePlaneExteriorCutoff_apply_zero (E := C2) f

/-! ## Local Rellich compactness -/

/-- Multiplication `H¹(ℝ²; ℂ²) → L²(ℝ²; ℂ²)` by a bounded scalar coefficient. -/
def wholePlaneC2LocalizationH1 (a : WholePlaneScalarLInf) :
    WholePlaneC2H1 →L[ℂ] WholePlaneC2L2 :=
  (scalarVectorMulL2 (E := C2) volume a).comp (wholePlaneH1Embedding C2)

/-- Bounded scalar multiplication on `H¹` acts through the physical `L²` field. -/
@[simp] theorem wholePlaneC2LocalizationH1_apply (a : WholePlaneScalarLInf)
    (b : WholePlaneC2H1) :
    wholePlaneC2LocalizationH1 a b =
      scalarVectorMulL2 volume a (wholePlaneH1Embedding C2 b) :=
  rfl

/-- Taking a scalar coordinate commutes with multiplication of a two-component `L²` field by
a scalar `L∞` coefficient. -/
theorem wholePlaneC2CoordL2_scalarVectorMulL2
    (a : WholePlaneScalarLInf) (b : WholePlaneC2L2) (i : Fin 2) :
    wholePlaneC2CoordL2 i (scalarVectorMulL2 (E := C2) volume a b) =
      scalarVectorMulL2 (E := ℂ) volume a (wholePlaneC2CoordL2 i b) := by
  apply Lp.ext
  have hout :
      ((wholePlaneC2CoordL2 i
          (scalarVectorMulL2 (E := C2) volume a b) : WholePlaneScalarL2) :
          WholePlane → ℂ) =ᵐ[volume]
        fun x => (EuclideanSpace.proj i)
          ((scalarVectorMulL2 (E := C2) volume a b : WholePlane → C2) x) := by
    simpa only [wholePlaneC2CoordL2] using
      (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
        (p := 2) (μ := (volume : Measure WholePlane))
        (scalarVectorMulL2 (E := C2) volume a b)
  have hmul := scalarVectorMulL2_coe_ae (E := C2) volume a b
  have hb :
      (wholePlaneC2CoordL2 i b : WholePlane → ℂ) =ᵐ[volume]
        fun x => (EuclideanSpace.proj i) ((b : WholePlane → C2) x) := by
    simpa only [wholePlaneC2CoordL2] using
      (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL
        (p := 2) (μ := (volume : Measure WholePlane)) b
  have hrhs := scalarVectorMulL2_coe_ae (E := ℂ) volume a (wholePlaneC2CoordL2 i b)
  filter_upwards [hout, hmul, hb, hrhs] with x ho hm hbi hr
  rw [ho, hm, hr, hbi]
  simp

/-- A two-component `L²`-valued map is compact if both scalar coordinates are compact. -/
theorem isCompactOperator_wholePlaneC2L2_of_coord
    {E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℂ E]
    (T : E →L[ℂ] WholePlaneC2L2)
    (hT : ∀ i : Fin 2, IsCompactOperator ((wholePlaneC2CoordL2 i).comp T)) :
    IsCompactOperator T := by
  let P : E →L[ℂ] (Fin 2 → WholePlaneScalarL2) :=
    ContinuousLinearMap.pi fun i => (wholePlaneC2CoordL2 i).comp T
  have hP : IsCompactOperator P :=
    isCompactOperator_pi_of_fintype P (by
      intro i
      convert hT i using 1
      ext x
      rfl)
  let S : (Fin 2 → WholePlaneScalarL2) →L[ℂ] WholePlaneC2L2 :=
    ∑ i : Fin 2, (wholePlaneScalarToC2CoordL2 i).comp (ContinuousLinearMap.proj i)
  have hSP : IsCompactOperator (S.comp P) := hP.clm_comp S
  have hEq : S.comp P = T := by
    apply ContinuousLinearMap.ext
    intro x
    apply wholePlaneC2L2_ext_coord
    intro i
    simp only [S, P, ContinuousLinearMap.comp_apply, sum_apply,
      ContinuousLinearMap.pi_apply, ContinuousLinearMap.proj_apply, map_sum,
      wholePlaneC2CoordL2_scalarToC2CoordL2]
    fin_cases i <;> simp
  rw [← hEq]
  exact hSP

/-- Bounded scalar multiplication `H¹(ℝ²; ℂ²) → L²(ℝ²; ℂ²)` by a coefficient supported almost
everywhere in a measurable finite-volume set is compact.  This is the two-component form of
the local Rellich input of the compactness argument in §2.3 (compactness of the restriction
`H¹(ℝ²) → L²(D(0, R_w))`). -/
theorem isCompactOperator_wholePlaneC2LocalizationH1_of_ae_zero_off
    (s : Set WholePlane) (hs : MeasurableSet s) (hsm : volume s ≠ (∞ : ℝ≥0∞))
    (a : WholePlaneScalarLInf) (ha : ∀ᵐ x ∂volume, x ∉ s → a x = 0) :
    IsCompactOperator (wholePlaneC2LocalizationH1 a) := by
  have hscalar : IsCompactOperator (wholePlaneScalarLocalizationH1 a) :=
    isCompactOperator_wholePlaneScalarLocalizationH1_of_ae_zero_off s hs hsm a ha
  refine isCompactOperator_wholePlaneC2L2_of_coord _ ?_
  intro i
  have hEq : (wholePlaneC2CoordL2 i).comp (wholePlaneC2LocalizationH1 a) =
      (wholePlaneScalarLocalizationH1 a).comp (wholePlaneC2CoordH1 i) := by
    apply ContinuousLinearMap.ext
    intro b
    simp only [ContinuousLinearMap.comp_apply, wholePlaneC2LocalizationH1_apply,
      wholePlaneScalarLocalizationH1_apply, wholePlaneH1Embedding_c2CoordH1,
      wholePlaneC2CoordL2_scalarVectorMulL2]
  rw [hEq]
  exact hscalar.comp_clm (wholePlaneC2CoordH1 i)

/-! ## The two-dimensional Sobolev embedding `H¹ ↪ L⁴` -/

/-- Insert a scalar `L⁴` field into one coordinate of a two-component `L⁴` field. -/
def wholePlaneScalarToC2CoordL4 (i : Fin 2) :
    WholePlaneScalarL4 →L[ℂ] WholePlaneC2L4 :=
  (scalarToVecPoint i).compLpL 4 volume

/-- The continuous two-component embedding `H¹(ℝ²; ℂ²) → L⁴(ℝ²; ℂ²)`, assembled from the
scalar two-dimensional Gagliardo-Nirenberg-Sobolev estimate. -/
def wholePlaneC2H1ToL4 : WholePlaneC2H1 →L[ℂ] WholePlaneC2L4 :=
  ∑ i : Fin 2, (wholePlaneScalarToC2CoordL4 i).comp
    (wholePlaneScalarH1ToL4.comp (wholePlaneC2CoordH1 i))

/-- The bundled two-component `L⁴` field represents the original weak `H¹` field. -/
theorem wholePlaneC2H1ToL4_coe_ae (u : WholePlaneC2H1) :
    (wholePlaneC2H1ToL4 u : WholePlane → C2) =ᵐ[volume]
      (wholePlaneH1Embedding C2 u : WholePlane → C2) := by
  have hterm : ∀ i : Fin 2,
      ((wholePlaneScalarToC2CoordL4 i
        (wholePlaneScalarH1ToL4 (wholePlaneC2CoordH1 i u)) : WholePlaneC2L4) :
          WholePlane → C2) =ᵐ[volume]
        fun x => scalarToVecPoint i
          ((wholePlaneH1Embedding C2 u : WholePlane → C2) x i) := by
    intro i
    have hins := (scalarToVecPoint (ι := Fin 2) i).coeFn_compLpL (p := 4)
      (μ := (volume : Measure WholePlane))
      (wholePlaneScalarH1ToL4 (wholePlaneC2CoordH1 i u))
    have hscalar := wholePlaneScalarH1ToL4_coe_ae (wholePlaneC2CoordH1 i u)
    have hcoord :
        (wholePlaneH1Embedding ℂ (wholePlaneC2CoordH1 i u) : WholePlane → ℂ) =ᵐ[volume]
          fun x => (wholePlaneH1Embedding C2 u : WholePlane → C2) x i := by
      rw [wholePlaneH1Embedding_c2CoordH1]
      exact (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := 2)
        (μ := (volume : Measure WholePlane)) (wholePlaneH1Embedding C2 u)
    filter_upwards [hins, hscalar, hcoord] with x hx hs hc
    simpa [wholePlaneScalarToC2CoordL4] using
      hx.trans (congrArg (scalarToVecPoint (ι := Fin 2) i) (hs.trans hc))
  rw [show wholePlaneC2H1ToL4 u =
      ∑ i : Fin 2, wholePlaneScalarToC2CoordL4 i
        (wholePlaneScalarH1ToL4 (wholePlaneC2CoordH1 i u)) by
    simp [wholePlaneC2H1ToL4]]
  filter_upwards [Lp.coeFn_finsetSum Finset.univ
      (fun i : Fin 2 => wholePlaneScalarToC2CoordL4 i
        (wholePlaneScalarH1ToL4 (wholePlaneC2CoordH1 i u))),
    ae_all_iff.2 hterm] with x hsum ht
  rw [hsum]
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl (fun i _ => ht i)]
  apply PiLp.ext
  intro j
  simp only [Fin.sum_univ_two, PiLp.add_apply]
  fin_cases j <;> simp [scalarToVecPoint]

/-- The explicit constant in the two-component `H¹ → L⁴` estimate: the sum over the two
coordinates of the coordinate-insertion norm times the scalar Gagliardo-Nirenberg-Sobolev
operator norm. -/
def wholePlaneC2H1L4Bound : ℝ :=
  ∑ _i : Fin 2, ‖wholePlaneScalarH1ToL4‖

/-- The two-component `H¹ → L⁴` constant is nonnegative. -/
theorem wholePlaneC2H1L4Bound_nonneg : 0 ≤ wholePlaneC2H1L4Bound :=
  Finset.sum_nonneg fun _ _ => ContinuousLinearMap.opNorm_nonneg _

/-- Quantitative continuity of `H¹(ℝ²; ℂ²) → L⁴(ℝ²; ℂ²)`, the two-component form of the
two-dimensional Gagliardo-Nirenberg-Sobolev estimate used for the form perturbation
`eq:form-small` in the proof of `prop:local-seed`. -/
theorem norm_wholePlaneC2H1ToL4_le (u : WholePlaneC2H1) :
    ‖wholePlaneC2H1ToL4 u‖ ≤ wholePlaneC2H1L4Bound * ‖u‖ := by
  have hpoint : ∀ i : Fin 2, ‖wholePlaneScalarToC2CoordL4 i‖ ≤ 1 := by
    intro i
    refine (ContinuousLinearMap.norm_compLpL_le (scalarToVecPoint (ι := Fin 2) i)).trans ?_
    refine (scalarToVecPoint (ι := Fin 2) i).opNorm_le_bound zero_le_one ?_
    intro c
    rw [one_mul, EuclideanSpace.norm_eq]
    have hval : ∀ j : Fin 2,
        ‖(scalarToVecPoint (ι := Fin 2) i) c j‖ ^ 2 ≤ if i = j then ‖c‖ ^ 2 else 0 := by
      intro j
      by_cases hij : i = j
      · subst hij
        simp [scalarToVecPoint]
      · simp [scalarToVecPoint, hij, Ne.symm hij]
    have hsum : ∑ j : Fin 2, ‖(scalarToVecPoint (ι := Fin 2) i) c j‖ ^ 2 ≤ ‖c‖ ^ 2 := by
      refine (Finset.sum_le_sum fun j _ => hval j).trans ?_
      simp
    calc
      Real.sqrt (∑ j : Fin 2, ‖(scalarToVecPoint (ι := Fin 2) i) c j‖ ^ 2)
          ≤ Real.sqrt (‖c‖ ^ 2) := Real.sqrt_le_sqrt hsum
      _ = ‖c‖ := Real.sqrt_sq (norm_nonneg c)
  have hterm : ∀ i : Fin 2, ‖wholePlaneScalarToC2CoordL4 i
      (wholePlaneScalarH1ToL4 (wholePlaneC2CoordH1 i u))‖ ≤
        ‖wholePlaneScalarH1ToL4‖ * ‖u‖ := by
    intro i
    calc
      ‖wholePlaneScalarToC2CoordL4 i
          (wholePlaneScalarH1ToL4 (wholePlaneC2CoordH1 i u))‖
          ≤ ‖wholePlaneScalarToC2CoordL4 i‖ *
            ‖wholePlaneScalarH1ToL4 (wholePlaneC2CoordH1 i u)‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ 1 * (‖wholePlaneScalarH1ToL4‖ * ‖u‖) := by
        refine mul_le_mul (hpoint i) ?_ (norm_nonneg _) zero_le_one
        exact (ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_left (norm_wholePlaneC2CoordH1_apply_le i u)
            (ContinuousLinearMap.opNorm_nonneg _))
      _ = ‖wholePlaneScalarH1ToL4‖ * ‖u‖ := one_mul _
  calc
    ‖wholePlaneC2H1ToL4 u‖
        = ‖∑ i : Fin 2, wholePlaneScalarToC2CoordL4 i
            (wholePlaneScalarH1ToL4 (wholePlaneC2CoordH1 i u))‖ := by
      simp [wholePlaneC2H1ToL4]
    _ ≤ ∑ i : Fin 2, ‖wholePlaneScalarToC2CoordL4 i
            (wholePlaneScalarH1ToL4 (wholePlaneC2CoordH1 i u))‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin 2, ‖wholePlaneScalarH1ToL4‖ * ‖u‖ :=
      Finset.sum_le_sum fun i _ => hterm i
    _ = wholePlaneC2H1L4Bound * ‖u‖ := by
      simp [wholePlaneC2H1L4Bound, Finset.sum_const]
      ring

end

end FastDynamo
