/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Global.HorizontalCutoffCommutator
public import LeanPool.FastDynamo.Global.HorizontalTransportSkewness

/-!
# Two-component periodic cut-off multipliers from three-component ones

`FastDynamo/Analysis/TransverseVecCutoffMultiplier.lean` states the fibre-generic multiplier
interface `ParametrixCutoffs.TransverseVecSecondOrderCutoff ι` that Section 7
(`sec:parametrix`) consumes at
`ι = Fin 2`.  The repository's *construction*
of periodic second-order cut-off multipliers, the Fourier completion of
`FastDynamo/Analysis/TransverseSmoothH2CutoffMultiplier.lean`, is hard-wired to the
three-component fibre through `PeriodicSecondOrderCutoffs.PeriodicSecondOrderCutoff`.

Rather than retype that completion at `Fin 2`, this module transports it along the isometric
zero-extension `ℂ² ↪ ℂ³` of `FastDynamo/Global/HorizontalTransportSkewness.lean` and the
horizontal projection `ℂ³ ↠ ℂ²` of `FastDynamo/Operator/HorizontalSector.lean`:

`χ ↦ π_⊥ ∘ (χ ·) ∘ ι_⊥`.

A scalar cut-off acts diagonally in the fibre, so both transports commute with it, with the
transverse derivative candidates and with the transverse Laplacian candidate; the three Leibniz
identities therefore descend verbatim, and the descended multiplier carries *the same* value,
gradient and Laplacian coefficients.  Every `L∞` bound proved for the three-component cut-off is
consequently a bound for the two-component one, with no constant lost.

The module closes with the constant `1` and the complement `1 - χ`, which is how the
paper's background cut-off `χ_n` (`= 0` on `D(p_n, R_n/10)`, `= 1` off `D(p_n, R_n/6)`) is
obtained from a compactly supported bump: only the bump can be periodized by a lattice sum, the
cut-off itself being one near infinity.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

namespace HorizontalCutoffMultiplier

open ParametrixCutoffs PeriodicSecondOrderCutoffs

/-! ## The transports on the transverse `H²` graph -/

/-- The transverse Laplacian candidate commutes with the isometric zero-extension: it is a
scalar Fourier multiplier acting diagonally in the fibre. -/
theorem verticalZeroExtendL2_transverseVecLaplacianFromH2 (h : TransverseC2H2) :
    verticalZeroExtendL2 (transverseVecLaplacianFromH2 (Fin 2) h) =
      transverseLaplacianFromH2 (verticalZeroExtendH2 h) := by
  apply transverseVecL2_ext_coeff
  intro n i
  rw [transverseCoeffCLM_transverseLaplacianFromH2,
    transverseH2Embedding_verticalZeroExtendH2]
  have hcast : ∀ k : Fin 2,
      transverseCoeffCLM n k.castSucc
          (verticalZeroExtendL2 (transverseVecLaplacianFromH2 (Fin 2) h)) =
        -(transverseFrequencyEnergy n : ℂ) *
          transverseCoeffCLM n k.castSucc
            (verticalZeroExtendL2 (transverseH2Embedding h)) := by
    intro k
    rw [transverseCoeffCLM_verticalZeroExtendL2_castSucc,
      transverseCoeffCLM_verticalZeroExtendL2_castSucc,
      transverseCoeffCLM_transverseLaplacianFromH2]
  have hlast :
      transverseCoeffCLM n 2
          (verticalZeroExtendL2 (transverseVecLaplacianFromH2 (Fin 2) h)) =
        -(transverseFrequencyEnergy n : ℂ) *
          transverseCoeffCLM n 2
            (verticalZeroExtendL2 (transverseH2Embedding h)) := by
    rw [transverseCoeffCLM_verticalZeroExtendL2_two,
      transverseCoeffCLM_verticalZeroExtendL2_two, mul_zero]
  fin_cases i
  · exact hcast 0
  · exact hcast 1
  · exact hlast

/-- The horizontal projection undoes the zero-extension on the transverse `H²` graph. -/
@[simp] theorem horizontalProjH2_verticalZeroExtendH2 (h : TransverseC2H2) :
    horizontalProjH2 (verticalZeroExtendH2 h) = h := by
  apply transverseH2Embedding_injective
  rw [transverseH2Embedding_horizontalProjH2,
    transverseH2Embedding_verticalZeroExtendH2, horizontalProjL2_verticalZeroExtendL2]

/-! ## The three conjugated Leibniz identities -/

variable (chi : PeriodicSecondOrderCutoff)

/-- Conjugation of the three-component multiplier, before it is bundled. -/
def conjugate (chi : PeriodicSecondOrderCutoff) : TransverseC2H2 →L[ℂ] TransverseC2H2 :=
  horizontalProjH2.comp (chi.domainMul.comp verticalZeroExtendH2)

/-- The conjugated multiplier is multiplication by the same value on the physical field. -/
theorem embedding_conjugate (b : TransverseC2H2) :
    transverseH2Embedding (conjugate chi b) =
      scalarVectorMulTransverseVec (Fin 2) chi.value (transverseH2Embedding b) := by
  have h1 : transverseH2Embedding (conjugate chi b) =
      horizontalProjL2
        (transverseH2Embedding (chi.domainMul (verticalZeroExtendH2 b))) := rfl
  have h2 := chi.embedding_domainMul (verticalZeroExtendH2 b)
  rw [h1, h2, horizontalProjL2_scalarVectorMulTransverse,
    transverseH2Embedding_verticalZeroExtendH2, horizontalProjL2_verticalZeroExtendL2]

/-- First-order Leibniz rule for the conjugated multiplier. -/
theorem deriv_conjugate (j : Fin 2) (b : TransverseC2H2) :
    transverseVecDerivFromH2 (Fin 2) j (conjugate chi b) =
      scalarVectorMulTransverseVec (Fin 2) (chi.gradient j) (transverseH2Embedding b) +
        scalarVectorMulTransverseVec (Fin 2) chi.value
          (transverseVecDerivFromH2 (Fin 2) j b) := by
  have h1 : transverseVecDerivFromH2 (Fin 2) j (conjugate chi b) =
      horizontalProjL2
        (transverseDerivFromH2 j (chi.domainMul (verticalZeroExtendH2 b))) :=
    (horizontalProjL2_transverseDerivFromH2 j
      (chi.domainMul (verticalZeroExtendH2 b))).symm
  have h2 := chi.deriv_domainMul j (verticalZeroExtendH2 b)
  have h3 : horizontalProjL2 (scalarVectorMulTransverse (chi.gradient j)
      (transverseH2Embedding (verticalZeroExtendH2 b))) =
      scalarVectorMulTransverseVec (Fin 2) (chi.gradient j)
        (transverseH2Embedding b) := by
    rw [horizontalProjL2_scalarVectorMulTransverse,
      transverseH2Embedding_verticalZeroExtendH2, horizontalProjL2_verticalZeroExtendL2]
  have h4 : horizontalProjL2 (scalarVectorMulTransverse chi.value
      (transverseDerivFromH2 j (verticalZeroExtendH2 b))) =
      scalarVectorMulTransverseVec (Fin 2) chi.value
        (transverseVecDerivFromH2 (Fin 2) j b) := by
    rw [horizontalProjL2_scalarVectorMulTransverse,
      ← verticalZeroExtendL2_transverseVecDerivFromH2,
      horizontalProjL2_verticalZeroExtendL2]
  rw [h1, h2, map_add, h3, h4]

/-- Second-order Leibniz rule for the conjugated multiplier. -/
theorem laplacian_conjugate (b : TransverseC2H2) :
    transverseVecLaplacianFromH2 (Fin 2) (conjugate chi b) =
      scalarVectorMulTransverseVec (Fin 2) chi.value
          (transverseVecLaplacianFromH2 (Fin 2) b) +
        (2 : ℂ) • (∑ j : Fin 2, scalarVectorMulTransverseVec (Fin 2) (chi.gradient j)
          (transverseVecDerivFromH2 (Fin 2) j b)) +
        scalarVectorMulTransverseVec (Fin 2) chi.laplacian (transverseH2Embedding b) := by
  have h1 : transverseVecLaplacianFromH2 (Fin 2) (conjugate chi b) =
      horizontalProjL2
        (transverseLaplacianFromH2 (chi.domainMul (verticalZeroExtendH2 b))) :=
    (horizontalProjL2_transverseLaplacianFromH2
      (chi.domainMul (verticalZeroExtendH2 b))).symm
  have h2 := chi.laplacian_domainMul (verticalZeroExtendH2 b)
  have h3 : horizontalProjL2 (scalarVectorMulTransverse chi.value
      (transverseLaplacianFromH2 (verticalZeroExtendH2 b))) =
      scalarVectorMulTransverseVec (Fin 2) chi.value
        (transverseVecLaplacianFromH2 (Fin 2) b) := by
    rw [horizontalProjL2_scalarVectorMulTransverse,
      ← verticalZeroExtendL2_transverseVecLaplacianFromH2,
      horizontalProjL2_verticalZeroExtendL2]
  have h4 : ∀ j : Fin 2, horizontalProjL2 (scalarVectorMulTransverse (chi.gradient j)
      (transverseDerivFromH2 j (verticalZeroExtendH2 b))) =
      scalarVectorMulTransverseVec (Fin 2) (chi.gradient j)
        (transverseVecDerivFromH2 (Fin 2) j b) := by
    intro j
    rw [horizontalProjL2_scalarVectorMulTransverse,
      ← verticalZeroExtendL2_transverseVecDerivFromH2,
      horizontalProjL2_verticalZeroExtendL2]
  have h5 : horizontalProjL2 (scalarVectorMulTransverse chi.laplacian
      (transverseH2Embedding (verticalZeroExtendH2 b))) =
      scalarVectorMulTransverseVec (Fin 2) chi.laplacian
        (transverseH2Embedding b) := by
    rw [horizontalProjL2_scalarVectorMulTransverse,
      transverseH2Embedding_verticalZeroExtendH2, horizontalProjL2_verticalZeroExtendL2]
  rw [h1, h2]
  simp only [map_add, map_smul, map_sum, h3, h4, h5]

/-! ## Descent of a three-component periodic cut-off -/

/-- The two-component periodic second-order cut-off multiplier obtained from a three-component
one by conjugating with the zero-extension and the horizontal projection.  Value, gradient and
Laplacian are unchanged, so all `L∞` bounds transfer with no loss. -/
def ofPeriodic (chi : PeriodicSecondOrderCutoff) :
    TransverseVecSecondOrderCutoff (Fin 2) where
  value := chi.value
  gradient := chi.gradient
  laplacian := chi.laplacian
  domainMul := conjugate chi
  embedding_domainMul := embedding_conjugate chi
  deriv_domainMul := deriv_conjugate chi
  laplacian_domainMul := laplacian_conjugate chi

/-- The descended cut-off has the same `L∞` value. -/
@[simp] theorem ofPeriodic_value : (ofPeriodic chi).value = chi.value :=
  rfl

/-- The descended cut-off has the same `L∞` gradient. -/
@[simp] theorem ofPeriodic_gradient (j : Fin 2) :
    (ofPeriodic chi).gradient j = chi.gradient j :=
  rfl

/-- The descended cut-off has the same `L∞` Laplacian. -/
@[simp] theorem ofPeriodic_laplacian : (ofPeriodic chi).laplacian = chi.laplacian :=
  rfl

/-! ## The constant one and the complement -/

/-- The constant function `1` as a quotient-level `L∞` coefficient. -/
def constOneLInf : TransverseScalarLInf :=
  (MeasureTheory.memLp_top_const (1 : ℂ)).toLp (fun _ ↦ (1 : ℂ))

/-- The constant coefficient `1` is represented by the constant function `1`. -/
theorem constOneLInf_coe_ae :
    (constOneLInf : TransverseTorus → ℂ) =ᵐ[transverseMeasure] fun _ ↦ (1 : ℂ) :=
  MeasureTheory.MemLp.coeFn_toLp _

/-- Multiplication by the constant coefficient `1` is the identity of `L²`. -/
theorem scalarVectorMulTransverseVec_constOne {ι : Type*} [Fintype ι]
    (f : TransverseVecL2 ι) :
    scalarVectorMulTransverseVec ι constOneLInf f = f := by
  change scalarVectorMulL2 transverseMeasure constOneLInf f = f
  apply MeasureTheory.Lp.ext
  filter_upwards [scalarVectorMulL2_coe_ae transverseMeasure constOneLInf f,
    constOneLInf_coe_ae] with x hx hone
  rw [hx, hone, one_smul]

/-- Multiplication by `1 - a` subtracts multiplication by `a` from the identity. -/
theorem scalarVectorMulTransverseVec_constOne_sub {ι : Type*} [Fintype ι]
    (a : TransverseScalarLInf) (f : TransverseVecL2 ι) :
    scalarVectorMulTransverseVec ι (constOneLInf - a) f =
      f - scalarVectorMulTransverseVec ι a f := by
  rw [map_sub, sub_apply, scalarVectorMulTransverseVec_constOne]

/-- Multiplication by `-a` negates multiplication by `a`. -/
theorem scalarVectorMulTransverseVec_neg {ι : Type*} [Fintype ι]
    (a : TransverseScalarLInf) (f : TransverseVecL2 ι) :
    scalarVectorMulTransverseVec ι (-a) f = -scalarVectorMulTransverseVec ι a f := by
  rw [map_neg, neg_apply]

/-- The complement `1 - χ` of a two-component periodic cut-off, again a periodic cut-off.  This
is the shape of the paper's background cut-off `χ_n`, which equals `1` near
infinity and is therefore not itself a compactly supported periodized bump. -/
def complement (chi : TransverseVecSecondOrderCutoff (Fin 2)) :
    TransverseVecSecondOrderCutoff (Fin 2) where
  value := constOneLInf - chi.value
  gradient := fun j ↦ -chi.gradient j
  laplacian := -chi.laplacian
  domainMul := ContinuousLinearMap.id ℂ TransverseC2H2 - chi.domainMul
  embedding_domainMul := by
    intro b
    simp only [sub_apply, ContinuousLinearMap.id_apply, map_sub, chi.embedding_domainMul,
      scalarVectorMulTransverseVec_constOne]
  deriv_domainMul := by
    intro j b
    simp only [sub_apply, ContinuousLinearMap.id_apply, map_sub, chi.deriv_domainMul,
      scalarVectorMulTransverseVec_neg, scalarVectorMulTransverseVec_constOne]
    abel
  laplacian_domainMul := by
    intro b
    simp only [sub_apply, ContinuousLinearMap.id_apply, map_sub, chi.laplacian_domainMul,
      scalarVectorMulTransverseVec_constOne, scalarVectorMulTransverseVec_neg,
      Finset.sum_neg_distrib, smul_neg]
    abel

/-- The value of the complement is `1 - χ`. -/
@[simp] theorem complement_value (chi : TransverseVecSecondOrderCutoff (Fin 2)) :
    (complement chi).value = constOneLInf - chi.value :=
  rfl

/-- The gradient of the complement is `-∇χ`. -/
@[simp] theorem complement_gradient (chi : TransverseVecSecondOrderCutoff (Fin 2))
    (j : Fin 2) :
    (complement chi).gradient j = -chi.gradient j :=
  rfl

/-- The Laplacian of the complement is `-Δχ`. -/
@[simp] theorem complement_laplacian (chi : TransverseVecSecondOrderCutoff (Fin 2)) :
    (complement chi).laplacian = -chi.laplacian :=
  rfl

end HorizontalCutoffMultiplier

end

end FastDynamo
