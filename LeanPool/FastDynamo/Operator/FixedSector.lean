/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Analysis.TransverseW1Inf

/-!
# The induction operator on one fixed axial Fourier sector

For a real transverse `W^{1,∞}` velocity `u` and axial frequency `K`, this
module constructs the reduced operator on transverse amplitudes and its exact
realization in the `K`-th axial sector of product `L²`.

The product-space operator below is called a *fixed-sector*
operator.  Its Banach domain is `TransverseC3H2`, embedded into product `L²`
by `axialLiftFromH2 K`; it is not an all-frequency operator on
`ProductC3H2`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## Reduced transverse action -/

/--
The Fourier multiplier `Δ⊥ - (2πK)²` on the transverse `H²` domain of a fibre `ℂ^ι`.

This term of the reduced action is fibre-blind: it involves no velocity coefficient, only the
scalar Fourier symbols.  The three-component `reducedInductionDiffusion` below is its
instantiation at `ι = Fin 3`, and the two-component horizontal operator of the
paper uses it at `ι = Fin 2`.
-/
def transverseVecDiffusion (ι : Type*) [Fintype ι] [DecidableEq ι] (K : ℤ) :
    TransverseVecH2 ι →L[ℂ] TransverseVecL2 ι :=
  transverseVecLaplacianFromH2 ι -
    (2 * Real.pi * K : ℂ) ^ 2 • transverseH2Embedding

/-- The Fourier multiplier `Δ⊥ - (2πK)²` on the transverse `H²` domain. -/
def reducedInductionDiffusion (K : ℤ) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  transverseLaplacianFromH2 -
    (2 * Real.pi * K : ℂ) ^ 2 • transverseH2Embedding

/-- The transverse transport term `∑_{j<2} u_j ∂_j b`. -/
def reducedInductionTransport (u : TransverseRealW1Inf) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  ∑ j : Fin 2,
    (scalarVectorMulTransverse
      (transverseW1InfComplexValueCoordLInf j.castSucc u)).comp
        (transverseDerivFromH2 j)

/-- The axial transport term `(2π i K) u_3 b`. -/
def reducedInductionAxialTransport (u : TransverseRealW1Inf) (K : ℤ) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  axialMultiplier K •
    (scalarVectorMulTransverse
      (transverseW1InfComplexValueCoordLInf 2 u)).comp
        transverseH2Embedding

/-- The stretching term `∑_{j<2} b_j ∂_j u`. -/
def reducedInductionStretching (u : TransverseRealW1Inf) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  ∑ j : Fin 2,
    (vectorScalarMulTransverse
      (transverseW1InfComplexDerivLInf j u)).comp
        ((transverseCoordL2 j.castSucc).comp transverseH2Embedding)

/-- The exact reduced induction action

`epsilon * (Δ⊥ - (2πK)²)b - ∑_{j<2} u_j ∂_j b
  - (2π i K) u_3 b + ∑_{j<2} b_j ∂_j u`.
-/
def reducedInductionAction (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    TransverseC3H2 →L[ℂ] TransverseC3L2 :=
  (ε : ℂ) • reducedInductionDiffusion K -
    reducedInductionTransport u - reducedInductionAxialTransport u K +
      reducedInductionStretching u

/-- The reduced induction operator with complete Fourier-graph domain. -/
def reducedInductionOperator (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    DomainOperator TransverseC3L2 TransverseC3H2 where
  embedding := transverseH2Embedding
  embedding_injective := transverseH2Embedding_injective
  op := reducedInductionAction u ε K

/-! ## Product-space realization of the fixed sector -/

/-- Diffusion in the `K`-th product-space sector. -/
def fixedSectorInductionDiffusion (K : ℤ) :
    TransverseC3H2 →L[ℂ] ProductC3L2 :=
  fixedAxialLaplacianFromH2 K

/-- Transverse transport in the `K`-th product-space sector. -/
def fixedSectorInductionTransport (u : TransverseRealW1Inf) (K : ℤ) :
    TransverseC3H2 →L[ℂ] ProductC3L2 :=
  ∑ j : Fin 2,
    (scalarVectorMulProduct
      (pullTransverseScalarLInf
        (transverseW1InfComplexValueCoordLInf j.castSucc u))).comp
          (axialTransverseDerivFromH2 K j)

/-- Axial transport in the `K`-th product-space sector. -/
def fixedSectorInductionAxialTransport
    (u : TransverseRealW1Inf) (K : ℤ) :
    TransverseC3H2 →L[ℂ] ProductC3L2 :=
  (scalarVectorMulProduct
    (pullTransverseScalarLInf
      (transverseW1InfComplexValueCoordLInf 2 u))).comp
        (axialDerivFromH2 K)

/-- Stretching in the `K`-th product-space sector. -/
def fixedSectorInductionStretching (u : TransverseRealW1Inf) (K : ℤ) :
    TransverseC3H2 →L[ℂ] ProductC3L2 :=
  ∑ j : Fin 2,
    (vectorScalarMulProduct
      (pullTransverseVectorLInf
        (transverseW1InfComplexDerivLInf j u))).comp
          ((productCoordL2 j.castSucc).comp (axialLiftFromH2 K))

/-- Product `L²` realization of the induction action in the single axial
sector `K`. -/
def fixedSectorInductionAction
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    TransverseC3H2 →L[ℂ] ProductC3L2 :=
  (ε : ℂ) • fixedSectorInductionDiffusion K -
    fixedSectorInductionTransport u K -
      fixedSectorInductionAxialTransport u K +
        fixedSectorInductionStretching u K

/-- The domain operator whose image and action both lie in the single
product-space axial sector `K`.  This is not a full `ProductC3H2` operator. -/
def fixedSectorInductionOperator
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    DomainOperator ProductC3L2 TransverseC3H2 where
  embedding := axialLiftFromH2 K
  embedding_injective := axialLiftFromH2_injective K
  op := fixedSectorInductionAction u ε K

/-! ## Exact formulas on amplitudes -/

/--
Expanded form of the diffusion term (the diffusion term of `eq:torus-sector`, here on three
components): the transverse Laplacian minus the axial symbol `(2πK)²`.
-/
theorem reducedInductionDiffusion_apply (K : ℤ) (b : TransverseC3H2) :
    reducedInductionDiffusion K b =
      transverseLaplacianFromH2 b -
        (2 * Real.pi * K : ℂ) ^ 2 • transverseH2Embedding b := by
  rfl

/--
Expanded form of the transverse transport term `u_⊥ · ∇_⊥ b` of `A_{ε,K}`, as a sum over the two
transverse directions.
-/
theorem reducedInductionTransport_apply
    (u : TransverseRealW1Inf) (b : TransverseC3H2) :
    reducedInductionTransport u b =
      ∑ j : Fin 2, scalarVectorMulTransverse
        (transverseW1InfComplexValueCoordLInf j.castSucc u)
          (transverseDerivFromH2 j b) := by
  simp [reducedInductionTransport]

/--
Expanded form of the axial transport term `2π i K u₃ b` of `A_{ε,K}`: the axial derivative has
become the multiplier `axialMultiplier K`.
-/
theorem reducedInductionAxialTransport_apply
    (u : TransverseRealW1Inf) (K : ℤ) (b : TransverseC3H2) :
    reducedInductionAxialTransport u K b =
      axialMultiplier K • scalarVectorMulTransverse
        (transverseW1InfComplexValueCoordLInf 2 u)
          (transverseH2Embedding b) := by
  rfl

/--
Expanded form of the stretching term `(b_⊥ · ∇_⊥) u` of `A_{ε,K}`; there is no axial
contribution because `u` does not depend on `x₃`.
-/
theorem reducedInductionStretching_apply
    (u : TransverseRealW1Inf) (b : TransverseC3H2) :
    reducedInductionStretching u b =
      ∑ j : Fin 2, vectorScalarMulTransverse
        (transverseW1InfComplexDerivLInf j u)
          (transverseCoordL2 j.castSucc (transverseH2Embedding b)) := by
  simp [reducedInductionStretching]

/-- The reduced action expanded into exactly the four terms of `eq:torus-sector`
(diffusion, transport, axial transport, stretching), here on three components. -/
theorem reducedInductionAction_apply
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (b : TransverseC3H2) :
    reducedInductionAction u ε K b =
      (ε : ℂ) •
          (transverseLaplacianFromH2 b -
            (2 * Real.pi * K : ℂ) ^ 2 • transverseH2Embedding b) -
        (∑ j : Fin 2, scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf j.castSucc u)
            (transverseDerivFromH2 j b)) -
        axialMultiplier K • scalarVectorMulTransverse
          (transverseW1InfComplexValueCoordLInf 2 u)
            (transverseH2Embedding b) +
        (∑ j : Fin 2, vectorScalarMulTransverse
          (transverseW1InfComplexDerivLInf j u)
            (transverseCoordL2 j.castSucc (transverseH2Embedding b))) := by
  simp only [reducedInductionAction, add_apply, sub_apply, smul_apply,
    reducedInductionDiffusion_apply, reducedInductionTransport_apply,
    reducedInductionAxialTransport_apply, reducedInductionStretching_apply]

/-! ## Exact reduced/fixed-sector intertwining -/

/--
The product-space diffusion term in the `K`-th sector is the axial lift of the reduced diffusion
term on transverse amplitudes.
-/
theorem fixedSectorInductionDiffusion_intertwines
    (K : ℤ) (b : TransverseC3H2) :
    fixedSectorInductionDiffusion K b =
      axialLiftL2 K (reducedInductionDiffusion K b) := by
  rfl

/--
The product-space transverse transport term in the `K`-th sector is the axial lift of the reduced
transport term, since multiplication by a velocity coefficient commutes with the lift.
-/
theorem fixedSectorInductionTransport_intertwines
    (u : TransverseRealW1Inf) (K : ℤ) (b : TransverseC3H2) :
    fixedSectorInductionTransport u K b =
      axialLiftL2 K (reducedInductionTransport u b) := by
  simp only [fixedSectorInductionTransport, reducedInductionTransport,
    sum_apply, ContinuousLinearMap.comp_apply,
    axialTransverseDerivFromH2_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  exact scalarVectorMul_axialLift
    (transverseW1InfComplexValueCoordLInf j.castSucc u) K
      (transverseDerivFromH2 j b)

/--
The product-space axial transport term in the `K`-th sector is the axial lift of the reduced
axial transport term.
-/
theorem fixedSectorInductionAxialTransport_intertwines
    (u : TransverseRealW1Inf) (K : ℤ) (b : TransverseC3H2) :
    fixedSectorInductionAxialTransport u K b =
      axialLiftL2 K (reducedInductionAxialTransport u K b) := by
  simp only [fixedSectorInductionAxialTransport,
    reducedInductionAxialTransport, ContinuousLinearMap.comp_apply,
    smul_apply, axialDerivFromH2_apply, map_smul]
  rw [scalarVectorMul_axialLift]
  rw [transverseH2Embedding_apply]

/--
The product-space stretching term in the `K`-th sector is the axial lift of the reduced
stretching term.
-/
theorem fixedSectorInductionStretching_intertwines
    (u : TransverseRealW1Inf) (K : ℤ) (b : TransverseC3H2) :
    fixedSectorInductionStretching u K b =
      axialLiftL2 K (reducedInductionStretching u b) := by
  simp only [fixedSectorInductionStretching, reducedInductionStretching,
    sum_apply, ContinuousLinearMap.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [axialLiftFromH2_apply, productCoordL2_axialLiftL2]
  exact vectorScalarMul_axialLift
    (transverseW1InfComplexDerivLInf j u) K
      (transverseCoordL2 j.castSucc (transverseH2Embedding b))

/-- The product-space fixed-sector action is exactly the axial lift of the
reduced action. -/
theorem fixedSectorInductionAction_intertwines
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (b : TransverseC3H2) :
    fixedSectorInductionAction u ε K b =
      axialLiftL2 K (reducedInductionAction u ε K b) := by
  simp only [fixedSectorInductionAction, reducedInductionAction,
    add_apply, sub_apply, smul_apply, map_add, map_sub, map_smul]
  rw [fixedSectorInductionDiffusion_intertwines,
    fixedSectorInductionTransport_intertwines,
    fixedSectorInductionAxialTransport_intertwines,
    fixedSectorInductionStretching_intertwines]

/-- The domain-to-ambient pencils intertwine on the nose in the fixed axial
sector. -/
theorem fixedSectorInductionPencil_intertwines
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (z : ℂ)
    (b : TransverseC3H2) :
    (fixedSectorInductionOperator u ε K).pencil z b =
      axialLiftL2 K ((reducedInductionOperator u ε K).pencil z b) := by
  rw [DomainOperator.pencil]
  simp only [smul_apply, sub_apply]
  change z • axialLiftFromH2 K b - fixedSectorInductionAction u ε K b =
    axialLiftL2 K
      (z • transverseH2Embedding b - reducedInductionAction u ε K b)
  rw [fixedSectorInductionAction_intertwines, map_sub, map_smul]
  rfl

/-! ## Eigenpair transport -/

/-- A reduced eigenpair gives a product-space eigenpair in the fixed axial
sector.  Nonvanishing of the lifted field follows from injectivity of the
sector embedding. -/
theorem reducedInductionEigenpair_to_fixedSector
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (eigenvalue : ℂ)
    (b : TransverseC3H2)
    (h : (reducedInductionOperator u ε K).IsEigenpair eigenvalue b) :
    (fixedSectorInductionOperator u ε K).IsEigenpair eigenvalue b := by
  rcases h with ⟨hnonzero, heigen⟩
  constructor
  · change axialLiftFromH2 K b ≠ 0
    intro hzero
    have hb : b = 0 := (axialLiftFromH2_injective K) (by simpa using hzero)
    apply hnonzero
    change transverseH2Embedding b = 0
    rw [hb]
    simp
  · change fixedSectorInductionAction u ε K b =
      eigenvalue • axialLiftFromH2 K b
    rw [fixedSectorInductionAction_intertwines]
    change reducedInductionAction u ε K b =
      eigenvalue • transverseH2Embedding b at heigen
    rw [heigen, map_smul]
    rfl

/-- Conversely, injectivity of the axial lift recovers the reduced eigenpair
from a fixed-sector product eigenpair. -/
theorem fixedSectorInductionEigenpair_to_reduced
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (eigenvalue : ℂ)
    (b : TransverseC3H2)
    (h : (fixedSectorInductionOperator u ε K).IsEigenpair eigenvalue b) :
    (reducedInductionOperator u ε K).IsEigenpair eigenvalue b := by
  rcases h with ⟨hnonzero, heigen⟩
  constructor
  · change transverseH2Embedding b ≠ 0
    intro hzero
    apply hnonzero
    change axialLiftFromH2 K b = 0
    change axialLiftL2 K (transverseH2Embedding b) = 0
    rw [hzero]
    simp
  · change reducedInductionAction u ε K b =
      eigenvalue • transverseH2Embedding b
    apply (axialLiftL2 K).injective
    calc
      axialLiftL2 K (reducedInductionAction u ε K b) =
          fixedSectorInductionAction u ε K b :=
        (fixedSectorInductionAction_intertwines u ε K b).symm
      _ = eigenvalue • axialLiftFromH2 K b := by
        exact heigen
      _ = axialLiftL2 K (eigenvalue • transverseH2Embedding b) := by
        rw [map_smul]
        rfl

/-- Reduced and product fixed-sector eigenpairs are equivalent, with the
nonzero condition transported between their respective ambient spaces. -/
theorem fixedSectorInductionEigenpair_iff
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (eigenvalue : ℂ)
    (b : TransverseC3H2) :
    (fixedSectorInductionOperator u ε K).IsEigenpair eigenvalue b ↔
      (reducedInductionOperator u ε K).IsEigenpair eigenvalue b :=
  ⟨fixedSectorInductionEigenpair_to_reduced u ε K eigenvalue b,
    reducedInductionEigenpair_to_fixedSector u ε K eigenvalue b⟩

end

end FastDynamo
