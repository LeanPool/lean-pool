/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.ProductWeakDerivative
public import LeanPool.FastDynamo.Operator.FixedSector

/-!
# The induction operator on the product three-torus

This module constructs the all-frequency induction operator on the
complete Fourier-graph domain `ProductC3H2`.  The real velocity is independent
of the axial variable, so its value and transverse weak derivatives are pulled
back from the transverse torus.

Each term is defined separately.  The restriction theorems prove that the
all-frequency operator preserves every axial Fourier sector and that its
restriction is exactly `fixedSectorInductionOperator`.  Thus the fixed-sector
construction is not a separate formal model of the PDE.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## Full product-space action -/

/-- The product-torus Laplacian on the Fourier-graph `H²` domain. -/
def productInductionDiffusion : ProductC3H2 →L[ℂ] ProductC3L2 :=
  productLaplacianFromH2

/-- The transverse part `∑_{j<2} u_j ∂_j b` of transport. -/
def productInductionTransverseTransport (u : TransverseRealW1Inf) :
    ProductC3H2 →L[ℂ] ProductC3L2 :=
  ∑ j : Fin 2,
    (scalarVectorMulProduct
      (pullTransverseScalarLInf
        (transverseW1InfComplexValueCoordLInf j.castSucc u))).comp
          (productTransverseDerivFromH2 j)

/-- The axial part `u_3 ∂_3 b` of transport. -/
def productInductionAxialTransport (u : TransverseRealW1Inf) :
    ProductC3H2 →L[ℂ] ProductC3L2 :=
  (scalarVectorMulProduct
    (pullTransverseScalarLInf
      (transverseW1InfComplexValueCoordLInf 2 u))).comp
        productAxialDerivFromH2

/-- The stretching term `∑_{j<2} b_j ∂_j u`.  There is no `j = 3`
contribution because the velocity is independent of the axial variable. -/
def productInductionStretching (u : TransverseRealW1Inf) :
    ProductC3H2 →L[ℂ] ProductC3L2 :=
  ∑ j : Fin 2,
    (vectorScalarMulProduct
      (pullTransverseVectorLInf
        (transverseW1InfComplexDerivLInf j u))).comp
          ((productCoordL2 j.castSucc).comp productH2Embedding)

/-- The full induction action

`ε Δb - ∑_{j<2} u_j ∂_j b - u_3 ∂_3 b
  + ∑_{j<2} b_j ∂_j u`.
-/
def productInductionAction (u : TransverseRealW1Inf) (ε : ℝ) :
    ProductC3H2 →L[ℂ] ProductC3L2 :=
  (ε : ℂ) • productInductionDiffusion -
    productInductionTransverseTransport u -
      productInductionAxialTransport u + productInductionStretching u

/-- The all-frequency induction operator with complete product Fourier-graph
domain. -/
def productInductionOperator (u : TransverseRealW1Inf) (ε : ℝ) :
    DomainOperator ProductC3L2 ProductC3H2 where
  embedding := productH2Embedding
  embedding_injective := productH2Embedding_injective
  op := productInductionAction u ε

/-! ## Exact formulas -/

/--
Expanded form of the transverse transport term: the sum over `j < 2` of `u_j` times the `j`-th
transverse weak derivative of `B`.
-/
theorem productInductionTransverseTransport_apply
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    productInductionTransverseTransport u B =
      ∑ j : Fin 2, scalarVectorMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexValueCoordLInf j.castSucc u))
            (productTransverseDerivFromH2 j B) := by
  simp [productInductionTransverseTransport]

/-- Expanded form of the axial transport term: `u₃` times the axial weak derivative of `B`. -/
theorem productInductionAxialTransport_apply
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    productInductionAxialTransport u B =
      scalarVectorMulProduct
        (pullTransverseScalarLInf
          (transverseW1InfComplexValueCoordLInf 2 u))
            (productAxialDerivFromH2 B) :=
  rfl

/--
Expanded form of the stretching term: the sum over `j < 2` of the `j`-th component of `B` times
the transverse derivative `∂_j u` of the velocity.
-/
theorem productInductionStretching_apply
    (u : TransverseRealW1Inf) (B : ProductC3H2) :
    productInductionStretching u B =
      ∑ j : Fin 2, vectorScalarMulProduct
        (pullTransverseVectorLInf
          (transverseW1InfComplexDerivLInf j u))
            (productCoordL2 j.castSucc (productH2Embedding B)) := by
  simp [productInductionStretching]

/-- The full product action expanded into its four PDE terms. -/
theorem productInductionAction_apply
    (u : TransverseRealW1Inf) (ε : ℝ) (B : ProductC3H2) :
    productInductionAction u ε B =
      (ε : ℂ) • productLaplacianFromH2 B -
        (∑ j : Fin 2, scalarVectorMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf j.castSucc u))
              (productTransverseDerivFromH2 j B)) -
        scalarVectorMulProduct
          (pullTransverseScalarLInf
            (transverseW1InfComplexValueCoordLInf 2 u))
              (productAxialDerivFromH2 B) +
        (∑ j : Fin 2, vectorScalarMulProduct
          (pullTransverseVectorLInf
            (transverseW1InfComplexDerivLInf j u))
              (productCoordL2 j.castSucc (productH2Embedding B))) := by
  simp only [productInductionAction, add_apply, sub_apply, smul_apply, productInductionDiffusion,
    productInductionTransverseTransport_apply, productInductionAxialTransport_apply,
    productInductionStretching_apply]

/-! ## Restriction to a fixed axial Fourier sector -/

/--
The diffusion term preserves the `K`-th axial Fourier sector: on a lifted amplitude it agrees
with the fixed-sector diffusion `fixedSectorInductionDiffusion K`.
-/
theorem productInductionDiffusion_axialLiftH2
    (K : ℤ) (b : TransverseC3H2) :
    productInductionDiffusion (axialLiftH2 K b) =
      fixedSectorInductionDiffusion K b := by
  exact productLaplacianFromH2_axialLiftH2 K b

/--
The transverse transport term preserves the `K`-th axial sector, restricting to
`fixedSectorInductionTransport u K`.
-/
theorem productInductionTransverseTransport_axialLiftH2
    (u : TransverseRealW1Inf) (K : ℤ) (b : TransverseC3H2) :
    productInductionTransverseTransport u (axialLiftH2 K b) =
      fixedSectorInductionTransport u K b := by
  simp only [productInductionTransverseTransport,
    fixedSectorInductionTransport, sum_apply, ContinuousLinearMap.comp_apply,
    productTransverseDerivFromH2_axialLiftH2]

/--
The axial transport term preserves the `K`-th axial sector, restricting to
`fixedSectorInductionAxialTransport u K`.
-/
theorem productInductionAxialTransport_axialLiftH2
    (u : TransverseRealW1Inf) (K : ℤ) (b : TransverseC3H2) :
    productInductionAxialTransport u (axialLiftH2 K b) =
      fixedSectorInductionAxialTransport u K b := by
  simp only [productInductionAxialTransport,
    fixedSectorInductionAxialTransport, ContinuousLinearMap.comp_apply,
    productAxialDerivFromH2_axialLiftH2]

/--
The stretching term preserves the `K`-th axial sector, restricting to
`fixedSectorInductionStretching u K`; this uses that `u` is independent of the axial variable.
-/
theorem productInductionStretching_axialLiftH2
    (u : TransverseRealW1Inf) (K : ℤ) (b : TransverseC3H2) :
    productInductionStretching u (axialLiftH2 K b) =
      fixedSectorInductionStretching u K b := by
  simp only [productInductionStretching, fixedSectorInductionStretching,
    sum_apply, ContinuousLinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro j hj
  rw [productH2Embedding_axialLiftH2, axialLiftFromH2_apply,
    productCoordL2_axialLiftL2]

/-- The full product action restricted to the `K`-th axial sector is exactly
the previously constructed fixed-sector action. -/
theorem productInductionAction_axialLiftH2
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (b : TransverseC3H2) :
    productInductionAction u ε (axialLiftH2 K b) =
      fixedSectorInductionAction u ε K b := by
  simp only [productInductionAction, fixedSectorInductionAction,
    add_apply, sub_apply, smul_apply]
  rw [productInductionDiffusion_axialLiftH2,
    productInductionTransverseTransport_axialLiftH2,
    productInductionAxialTransport_axialLiftH2,
    productInductionStretching_axialLiftH2]

/-- Exact restriction of the all-frequency domain-to-ambient pencil. -/
theorem productInductionPencil_axialLiftH2
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (z : ℂ)
    (b : TransverseC3H2) :
    (productInductionOperator u ε).pencil z (axialLiftH2 K b) =
      (fixedSectorInductionOperator u ε K).pencil z b := by
  rw [DomainOperator.pencil]
  simp only [smul_apply, sub_apply]
  change z • productH2Embedding (axialLiftH2 K b) -
      productInductionAction u ε (axialLiftH2 K b) =
    z • axialLiftFromH2 K b - fixedSectorInductionAction u ε K b
  rw [productH2Embedding_axialLiftH2, productInductionAction_axialLiftH2]

/-! ## Eigenpairs -/

/-- On a lifted vector, the full operator eigenpair predicate is equivalent
to the fixed-sector predicate. -/
theorem productInductionEigenpair_axialLiftH2_iff_fixedSector
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (eigenvalue : ℂ)
    (b : TransverseC3H2) :
    (productInductionOperator u ε).IsEigenpair eigenvalue (axialLiftH2 K b) ↔
      (fixedSectorInductionOperator u ε K).IsEigenpair eigenvalue b := by
  constructor
  · rintro ⟨hnonzero, heigen⟩
    constructor
    · change axialLiftFromH2 K b ≠ 0
      change productH2Embedding (axialLiftH2 K b) ≠ 0 at hnonzero
      simpa only [productH2Embedding_axialLiftH2] using hnonzero
    · change fixedSectorInductionAction u ε K b =
          eigenvalue • axialLiftFromH2 K b
      rw [← productInductionAction_axialLiftH2,
        ← productH2Embedding_axialLiftH2]
      exact heigen
  · rintro ⟨hnonzero, heigen⟩
    constructor
    · change productH2Embedding (axialLiftH2 K b) ≠ 0
      change axialLiftFromH2 K b ≠ 0 at hnonzero
      simpa only [productH2Embedding_axialLiftH2] using hnonzero
    · change productInductionAction u ε (axialLiftH2 K b) =
          eigenvalue • productH2Embedding (axialLiftH2 K b)
      rw [productInductionAction_axialLiftH2,
        productH2Embedding_axialLiftH2]
      exact heigen

/-- A fixed-frequency full product eigenpair is equivalent directly to the
reduced two-dimensional eigenpair. -/
theorem productInductionEigenpair_axialLiftH2_iff_reduced
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (eigenvalue : ℂ)
    (b : TransverseC3H2) :
    (productInductionOperator u ε).IsEigenpair eigenvalue (axialLiftH2 K b) ↔
      (reducedInductionOperator u ε K).IsEigenpair eigenvalue b := by
  rw [productInductionEigenpair_axialLiftH2_iff_fixedSector,
    fixedSectorInductionEigenpair_iff]

end

end FastDynamo
