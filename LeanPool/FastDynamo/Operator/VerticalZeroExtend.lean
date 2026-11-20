/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Operator.HorizontalSector

/-!
# The vertical zero-extension on transverse `L²` and `H²`

The zero-extension `ℂ² ↪ ℂ³` appends a vanishing axial component.  Unlike the horizontal
projection `horizontalProjPoint` of `Operator/HorizontalProjection.lean` it preserves the inner
product, so real parts are transported verbatim, and it commutes with every fibre-diagonal
operation (scalar multiplication, the transverse derivatives, the transverse Laplacian).

This module is generic in that sense: it knows nothing about a velocity field, a cell, a
cut-off or a spectral parameter, only about the fibre inclusion `Fin 2 ↪ Fin 3` and the
transverse `L²`/`H²` scale.  It is what `eq:background-operator`
needs in order to read a three-component identity such as the transport skewness in the proof
of `prop:background-resolvent` (just before `eq:background-testing`) on two components; the
application itself stays in `Global/HorizontalTransportSkewness.lean`.

The pointwise embedding `verticalZeroExtendPoint` and its inner-product invariance
`inner_verticalZeroExtendPoint` live in `Operator/HorizontalProjection.lean`, next to the
horizontal projection they invert; this module lifts them to `L²` and `H²`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## The zero-extension on the transverse `L²` and `H²` spaces -/

/-- The zero-extension `L²(T²; ℂ²) → L²(T²; ℂ³)`. -/
def verticalZeroExtendL2 : TransverseC2L2 →L[ℂ] TransverseC3L2 :=
  verticalZeroExtendPoint.compLpL 2 transverseMeasure

/-- An almost-everywhere representative of the `L²` zero-extension. -/
theorem verticalZeroExtendL2_coe_ae (f : TransverseC2L2) :
    (verticalZeroExtendL2 f : TransverseTorus → C3) =ᵐ[transverseMeasure]
      fun x ↦ verticalZeroExtendPoint ((f : TransverseTorus → C2) x) :=
  verticalZeroExtendPoint.coeFn_compLpL f

/-- The `L²` zero-extension preserves inner products. -/
theorem inner_verticalZeroExtendL2 (f g : TransverseC2L2) :
    (inner ℂ (verticalZeroExtendL2 f) (verticalZeroExtendL2 g) : ℂ) = inner ℂ f g := by
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [verticalZeroExtendL2_coe_ae f, verticalZeroExtendL2_coe_ae g]
    with x hf hg
  rw [hf, hg]
  exact inner_verticalZeroExtendPoint _ _

/-- The `L²` horizontal projection undoes the `L²` zero-extension. -/
@[simp] theorem horizontalProjL2_verticalZeroExtendL2 (f : TransverseC2L2) :
    horizontalProjL2 (verticalZeroExtendL2 f) = f := by
  apply Lp.ext
  filter_upwards [horizontalProjL2_coe_ae (verticalZeroExtendL2 f),
    verticalZeroExtendL2_coe_ae f] with x h1 h2
  rw [h1, h2, horizontalProjPoint_verticalZeroExtendPoint]

/-- The zero-extension commutes with multiplication by a scalar `L∞` coefficient. -/
theorem verticalZeroExtendL2_scalarVectorMulTransverse
    (a : TransverseScalarLInf) (f : TransverseC2L2) :
    verticalZeroExtendL2 (scalarVectorMulTransverseC2 a f) =
      scalarVectorMulTransverse a (verticalZeroExtendL2 f) :=
  compLpL_scalarVectorMulL2 verticalZeroExtendPoint a f

/-- The `i`-th Fourier coefficient of a zero-extended field, in the horizontal range. -/
theorem transverseCoeffCLM_verticalZeroExtendL2_castSucc
    (n : TransverseFrequency) (j : Fin 2) (f : TransverseC2L2) :
    transverseCoeffCLM n j.castSucc (verticalZeroExtendL2 f) =
      transverseCoeffCLM n j f := by
  have hcoord : transverseCoordL2 j.castSucc (verticalZeroExtendL2 f) =
      transverseCoordL2 j f := by
    ext1
    filter_upwards [(EuclideanSpace.proj (𝕜 := ℂ) j.castSucc).coeFn_compLpL
        (verticalZeroExtendL2 f),
      verticalZeroExtendL2_coe_ae f,
      (EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL f] with x hx1 hx2 hx3
    calc (transverseCoordL2 j.castSucc (verticalZeroExtendL2 f) :
            TransverseTorus → ℂ) x
        = EuclideanSpace.proj j.castSucc
            ((verticalZeroExtendL2 f : TransverseTorus → C3) x) := hx1
      _ = EuclideanSpace.proj j.castSucc
            (verticalZeroExtendPoint ((f : TransverseTorus → C2) x)) := by rw [hx2]
      _ = EuclideanSpace.proj j ((f : TransverseTorus → C2) x) :=
            verticalZeroExtendPoint_apply_castSucc _ _
      _ = (transverseCoordL2 j f : TransverseTorus → ℂ) x := hx3.symm
  change transverseScalarCoeffCLM n
    (transverseCoordL2 j.castSucc (verticalZeroExtendL2 f)) = _
  rw [hcoord]
  rfl

/-- The axial Fourier coefficient of a zero-extended field vanishes. -/
theorem transverseCoeffCLM_verticalZeroExtendL2_two
    (n : TransverseFrequency) (f : TransverseC2L2) :
    transverseCoeffCLM n 2 (verticalZeroExtendL2 f) = 0 := by
  have hcoord : transverseCoordL2 (2 : Fin 3) (verticalZeroExtendL2 f) = 0 := by
    ext1
    filter_upwards [(EuclideanSpace.proj (𝕜 := ℂ) (2 : Fin 3)).coeFn_compLpL
        (verticalZeroExtendL2 f),
      verticalZeroExtendL2_coe_ae f,
      Lp.coeFn_zero (E := ℂ) (p := 2) (μ := transverseMeasure)] with x hx1 hx2 hx3
    calc (transverseCoordL2 (2 : Fin 3) (verticalZeroExtendL2 f) :
            TransverseTorus → ℂ) x
        = EuclideanSpace.proj (2 : Fin 3)
            ((verticalZeroExtendL2 f : TransverseTorus → C3) x) := hx1
      _ = EuclideanSpace.proj (2 : Fin 3)
            (verticalZeroExtendPoint ((f : TransverseTorus → C2) x)) := by rw [hx2]
      _ = 0 := verticalZeroExtendPoint_apply_two ((f : TransverseTorus → C2) x)
      _ = ((0 : TransverseScalarL2) : TransverseTorus → ℂ) x := by rw [hx3]; rfl
  change transverseScalarCoeffCLM n
    (transverseCoordL2 (2 : Fin 3) (verticalZeroExtendL2 f)) = _
  rw [hcoord, map_zero]

/-! ## The zero-extension on the transverse `H²` Fourier graph -/

/-- Append a vanishing axial row to a stored weighted Fourier-coefficient array. -/
def verticalZeroExtendWeightedCoeffs :
    WeightedTransverseC2Coeffs →L[ℂ] WeightedTransverseC3Coeffs :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 3 ↦ TransverseScalarFourierL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun i : Fin 3 ↦
      if h : (i : ℕ) < 2 then
        PiLp.proj 2 (fun _ : Fin 2 ↦ TransverseScalarFourierL2) ⟨i, h⟩ else 0)

/-- The extended coefficient array keeps the two horizontal rows. -/
@[simp] theorem verticalZeroExtendWeightedCoeffs_apply_castSucc
    (a : WeightedTransverseC2Coeffs) (j : Fin 2) :
    verticalZeroExtendWeightedCoeffs a j.castSucc = a j := by
  fin_cases j <;> rfl

/-- The extended coefficient array has a vanishing axial row. -/
@[simp] theorem verticalZeroExtendWeightedCoeffs_apply_two
    (a : WeightedTransverseC2Coeffs) :
    verticalZeroExtendWeightedCoeffs a 2 = 0 :=
  rfl

/-- The zero-extended physical field and the zero-extended coefficient array again satisfy
the three-component `H²` graph equation. -/
theorem verticalZeroExtendH2_graph_mem (h : TransverseC2H2) :
    (verticalZeroExtendL2 (transverseH2Embedding h),
      verticalZeroExtendWeightedCoeffs (transverseH2WeightedCoeffs h)) ∈
        transverseH2Submodule (ι := Fin 3) := by
  rw [mem_transverseH2Submodule_iff]
  intro n i
  have hcast : ∀ j : Fin 2,
      (verticalZeroExtendWeightedCoeffs (transverseH2WeightedCoeffs h) j.castSucc) n =
        (transverseH2Weight n : ℂ) *
          transverseCoeffCLM n j.castSucc
            (verticalZeroExtendL2 (transverseH2Embedding h)) := by
    intro j
    rw [verticalZeroExtendWeightedCoeffs_apply_castSucc,
      transverseCoeffCLM_verticalZeroExtendL2_castSucc,
      transverseH2WeightedCoeffs_apply]
  have hlast :
      (verticalZeroExtendWeightedCoeffs (transverseH2WeightedCoeffs h) 2) n =
        (transverseH2Weight n : ℂ) *
          transverseCoeffCLM n 2
            (verticalZeroExtendL2 (transverseH2Embedding h)) := by
    rw [verticalZeroExtendWeightedCoeffs_apply_two,
      transverseCoeffCLM_verticalZeroExtendL2_two]
    simp
  fin_cases i
  · exact hcast 0
  · exact hcast 1
  · exact hlast

/-- The zero-extension `H²(T²; ℂ²) → H²(T²; ℂ³)` on the closed Fourier graphs. -/
def verticalZeroExtendH2 : TransverseC2H2 →L[ℂ] TransverseC3H2 :=
  ((verticalZeroExtendL2.comp transverseH2Embedding).prod
    (verticalZeroExtendWeightedCoeffs.comp transverseH2WeightedCoeffs)).codRestrict
      transverseH2Submodule verticalZeroExtendH2_graph_mem

/-- The `H²`-level zero-extension lies over the `L²`-level one. -/
theorem transverseH2Embedding_verticalZeroExtendH2 (h : TransverseC2H2) :
    transverseH2Embedding (verticalZeroExtendH2 h) =
      verticalZeroExtendL2 (transverseH2Embedding h) :=
  rfl

/-- Each transverse derivative candidate commutes with the zero-extension. -/
theorem verticalZeroExtendL2_transverseVecDerivFromH2
    (j : Fin 2) (h : TransverseC2H2) :
    verticalZeroExtendL2 (transverseVecDerivFromH2 (Fin 2) j h) =
      transverseDerivFromH2 j (verticalZeroExtendH2 h) := by
  apply transverseVecL2_ext_coeff
  intro n i
  rw [transverseCoeffCLM_transverseDerivFromH2,
    transverseH2Embedding_verticalZeroExtendH2]
  have hcast : ∀ k : Fin 2,
      transverseCoeffCLM n k.castSucc
          (verticalZeroExtendL2 (transverseVecDerivFromH2 (Fin 2) j h)) =
        (2 * Real.pi * Complex.I * (n j : ℂ)) *
          transverseCoeffCLM n k.castSucc
            (verticalZeroExtendL2 (transverseH2Embedding h)) := by
    intro k
    rw [transverseCoeffCLM_verticalZeroExtendL2_castSucc,
      transverseCoeffCLM_verticalZeroExtendL2_castSucc,
      transverseCoeffCLM_transverseDerivFromH2]
  have hlast :
      transverseCoeffCLM n 2
          (verticalZeroExtendL2 (transverseVecDerivFromH2 (Fin 2) j h)) =
        (2 * Real.pi * Complex.I * (n j : ℂ)) *
          transverseCoeffCLM n 2
            (verticalZeroExtendL2 (transverseH2Embedding h)) := by
    rw [transverseCoeffCLM_verticalZeroExtendL2_two,
      transverseCoeffCLM_verticalZeroExtendL2_two, mul_zero]
  fin_cases i
  · exact hcast 0
  · exact hcast 1
  · exact hlast

end

end FastDynamo
