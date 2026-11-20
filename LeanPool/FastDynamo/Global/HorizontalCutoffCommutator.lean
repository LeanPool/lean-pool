/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Global.ParametrixCutoffs
public import LeanPool.FastDynamo.Global.PeriodicSecondOrderCutoffs
public import LeanPool.FastDynamo.Operator.HorizontalSector

/-!
# The cut-off commutator of the horizontal torus operator

The paper computes, in the proof of `lem:parametrix-error`,

`[A_{ε,K_n}, χ]h = ε(2∇_⊥χ · ∇_⊥h + (Δ_⊥χ)h)`,   `χ ∈ {χ_n, ψ_n}`,

for the **two-component** torus operator `A_{ε,K}` of `eq:torus-sector`.  Two facts make every
other term disappear: the transverse velocity vanishes on the transition region of both output
cut-offs, and every zeroth-order coefficient commutes with a scalar cut-off.

This module is the two-component counterpart of
`FastDynamo/Global/PeriodicSecondOrderCutoffs.lean`, whose fibre is hard-wired to `ℂ³`.
The route is identical: the second-order multiplier interface
`ParametrixCutoffs.TransverseVecSecondOrderCutoff` supplies the `H²` multiplication and its two
Leibniz identities, and the commutator formula is *derived*, not postulated.  Only the fibre and
the operator change:

* the diffusion term is `transverseVecDiffusion (Fin 2) K`, whose zeroth-order part `-(2πK)²`
  commutes with the cut-off, so only `2∇χ·∇h + (Δχ)h` survives;
* the transverse transport term contributes `(u_⊥·∇_⊥χ)h`, which vanishes under
  `VelocityVanishesOnGradient`;
* the axial transport term `2πiKu₃` is a multiplication operator and commutes;
* the stretching term `(h·∇_⊥)u_⊥` is zeroth order in `h` and commutes.

The module closes with the norm bounds in the form `lem:parametrix-error` consumes, with the
cut-off derivative norms replaced by their explicit `C₁/R` and `2C₂/R²` scale bounds
(`eq:parametrix-cutoff-bounds`), and the Cauchy–Schwarz step
`Σ_j‖∂_jh‖ ≤ √2‖∇_⊥h‖` that converts them into the gradient-energy form in which
`eq:bg-resolvent` and `eq:local-gradient` are stated.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace HorizontalCutoffCommutator

open ParametrixCutoffs PeriodicSecondOrderCutoffs LocalizedSummandAlgebra
open TransverseVecMultiplierAlgebra

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The compatible cut-off and its commutator -/

/-- The two-component periodic second-order cut-off multipliers of §7 of the paper. -/
abbrev HorizontalSecondOrderCutoff := TransverseVecSecondOrderCutoff (Fin 2)

/-- A periodic cut-off gives a compatible state/domain cut-off for the horizontal torus
operator `A_{ε,K}`. -/
def compatible (chi : HorizontalSecondOrderCutoff)
    (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ) :
    CompatibleCutoff (horizontalInductionOperator u epsilon K) where
  state := chi.stateMul
  domain := chi.domainMul
  embedding_comp := chi.embedding_comp_domainMul

/-- The literal same-operator commutator `[A_{ε,K}, χ] = A_{ε,K}χ - χA_{ε,K}`, through
`LocalizedSummandAlgebra.operatorCommutator`. -/
def commutator (chi : HorizontalSecondOrderCutoff)
    (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ) :
    TransverseC2H2 →L[ℂ] TransverseC2L2 :=
  operatorCommutator (horizontalInductionOperator u epsilon K) (compatible chi u epsilon K)

/-- The commutator is the exact localization defect consumed by the parametrix algebra, at
`B = A` and both extension maps given by the cut-off. -/
theorem commutator_eq_localizationCommutator
    (chi : HorizontalSecondOrderCutoff)
    (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ) :
    commutator chi u epsilon K =
      localizationCommutator (horizontalInductionOperator u epsilon K)
        (horizontalInductionOperator u epsilon K) chi.domainMul chi.stateMul :=
  operatorCommutator_eq_localizationCommutator
    (horizontalInductionOperator u epsilon K) (compatible chi u epsilon K)

/-- Unfolded action of the commutator. -/
theorem commutator_apply_eq
    (chi : HorizontalSecondOrderCutoff)
    (u : TransverseRealW1Inf) (epsilon : ℝ) (K : ℤ) (b : TransverseC2H2) :
    commutator chi u epsilon K b =
      horizontalInductionAction u epsilon K (chi.domainMul b) -
        chi.stateMul (horizontalInductionAction u epsilon K b) := by
  simp only [commutator, operatorCommutator, compatible, sub_apply,
    ContinuousLinearMap.comp_apply]
  rfl

/-! ## The three terms in the paper's formula -/

/-- `Σ_j (∂_jχ)(∂_jh)`. -/
def gradientInteraction (chi : HorizontalSecondOrderCutoff)
    (b : TransverseC2H2) : TransverseC2L2 :=
  ∑ j : Fin 2, scalarVectorMulTransverseC2 (chi.gradient j)
    (transverseVecDerivFromH2 (Fin 2) j b)

/-- `(Δχ)h`. -/
def laplacianInteraction (chi : HorizontalSecondOrderCutoff)
    (b : TransverseC2H2) : TransverseC2L2 :=
  scalarVectorMulTransverseC2 chi.laplacian (transverseH2Embedding b)

/-- `(u_⊥ · ∇_⊥χ)h`. -/
def transportInteraction (chi : HorizontalSecondOrderCutoff)
    (u : TransverseRealW1Inf) (b : TransverseC2H2) : TransverseC2L2 :=
  ∑ j : Fin 2,
    scalarVectorMulTransverseC2
      (transverseW1InfComplexValueCoordLInf j.castSucc u)
      (scalarVectorMulTransverseC2 (chi.gradient j) (transverseH2Embedding b))

/-- Commutator of the diffusion part with a scalar cut-off: the fixed-sector zeroth-order term
`-(2πK)²` commutes and cancels, leaving `Δ_⊥(χb) - χΔ_⊥b = 2∇χ·∇_⊥b + (Δ_⊥χ)b`. -/
theorem diffusion_commutator_apply
    (chi : HorizontalSecondOrderCutoff) (K : ℤ) (b : TransverseC2H2) :
    horizontalInductionDiffusion K (chi.domainMul b) -
        chi.stateMul (horizontalInductionDiffusion K b) =
      (2 : ℂ) • gradientInteraction chi b + laplacianInteraction chi b := by
  rw [horizontalInductionDiffusion_apply, horizontalInductionDiffusion_apply,
    chi.laplacian_domainMul, chi.embedding_domainMul]
  simp only [TransverseVecSecondOrderCutoff.stateMul, map_sub, map_smul,
    gradientInteraction, laplacianInteraction]
  abel

/-- Commutator of the transverse transport part with a scalar cut-off: only the term in which
the derivative falls on the cut-off survives, giving `(u_⊥·∇_⊥χ)b`. -/
theorem transport_commutator_apply
    (chi : HorizontalSecondOrderCutoff) (u : TransverseRealW1Inf) (b : TransverseC2H2) :
    horizontalInductionTransport u (chi.domainMul b) -
        chi.stateMul (horizontalInductionTransport u b) =
      transportInteraction chi u b := by
  rw [horizontalInductionTransport_apply, horizontalInductionTransport_apply,
    map_sum, ← Finset.sum_sub_distrib]
  unfold transportInteraction
  unfold TransverseVecSecondOrderCutoff.stateMul
  apply Finset.sum_congr rfl
  intro j _
  rw [chi.deriv_domainMul, map_add]
  rw [scalarVectorMulTransverseVec_commute
    (transverseW1InfComplexValueCoordLInf j.castSucc u) chi.value]
  abel

/-- The axial transport term `2πiKu₃·` is a multiplication operator, hence commutes exactly with
a scalar cut-off. -/
theorem axialTransport_commutes
    (chi : HorizontalSecondOrderCutoff) (u : TransverseRealW1Inf) (K : ℤ)
    (b : TransverseC2H2) :
    horizontalInductionAxialTransport u K (chi.domainMul b) =
      chi.stateMul (horizontalInductionAxialTransport u K b) := by
  rw [horizontalInductionAxialTransport_apply, horizontalInductionAxialTransport_apply,
    chi.embedding_domainMul, map_smul]
  unfold TransverseVecSecondOrderCutoff.stateMul
  rw [scalarVectorMulTransverseVec_commute]

/-- The stretching term `(h·∇_⊥)u_⊥` is zeroth order in `h`, hence commutes exactly with a
scalar cut-off. -/
theorem stretching_commutes
    (chi : HorizontalSecondOrderCutoff) (u : TransverseRealW1Inf) (b : TransverseC2H2) :
    horizontalInductionStretching u (chi.domainMul b) =
      chi.stateMul (horizontalInductionStretching u b) := by
  rw [horizontalInductionStretching_apply, horizontalInductionStretching_apply,
    chi.embedding_domainMul, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [transverseCoordL2_scalarVectorMulTransverseVec]
  unfold TransverseVecSecondOrderCutoff.stateMul
  rw [scalarVectorMulTransverseVec_vectorScalarMulTransverseVec]

/-- **The commutator formula** (proof of `lem:parametrix-error`), with the convention
`[A,χ] = Aχ - χA`:

`ε(2∇_⊥χ·∇_⊥h + (Δ_⊥χ)h) - (u_⊥·∇_⊥χ)h`.

Every zeroth-order term of `eq:torus-sector` cancels, as does the stretching term. -/
theorem commutator_apply
    (chi : HorizontalSecondOrderCutoff) (u : TransverseRealW1Inf)
    (epsilon : ℝ) (K : ℤ) (b : TransverseC2H2) :
    commutator chi u epsilon K b =
      (epsilon : ℂ) •
          ((2 : ℂ) • gradientInteraction chi b + laplacianInteraction chi b) -
        transportInteraction chi u b := by
  rw [commutator_apply_eq]
  simp only [horizontalInductionAction, add_apply, sub_apply, smul_apply,
    map_add, map_sub, map_smul]
  have hdiff := diffusion_commutator_apply chi K b
  have htransport := transport_commutator_apply chi u b
  have haxial := axialTransport_commutes chi u K b
  have hstretch := stretching_commutes chi u b
  have hdiff' :
      horizontalInductionDiffusion K (chi.domainMul b) =
        ((2 : ℂ) • gradientInteraction chi b + laplacianInteraction chi b) +
          chi.stateMul (horizontalInductionDiffusion K b) :=
    eq_add_of_sub_eq hdiff
  have htransport' :
      horizontalInductionTransport u (chi.domainMul b) =
        transportInteraction chi u b +
          chi.stateMul (horizontalInductionTransport u b) :=
    eq_add_of_sub_eq htransport
  rw [hdiff', htransport', haxial, hstretch]
  module

/-! ## Vanishing transverse velocity on the cut-off annulus -/

/-- The quotient-level statement that every transverse velocity component vanishes where the
corresponding cut-off derivative is nonzero.  For `ψ_n` and `χ_n` this is the
paper's "the horizontal velocity vanishes on the transition regions of both output
cut-offs" (proof of `lem:parametrix-error`). -/
def VelocityVanishesOnGradient (chi : HorizontalSecondOrderCutoff)
    (u : TransverseRealW1Inf) : Prop :=
  ∀ j : Fin 2,
    scalarMulTransverseLInf (transverseW1InfComplexValueCoordLInf j.castSucc u)
      (chi.gradient j) = 0

/-- Where the transverse velocity vanishes on the cut-off gradient, the transport contribution to
the commutator is identically zero. -/
theorem transportInteraction_eq_zero
    (chi : HorizontalSecondOrderCutoff) (u : TransverseRealW1Inf)
    (hvanish : VelocityVanishesOnGradient chi u) (b : TransverseC2H2) :
    transportInteraction chi u b = 0 := by
  unfold transportInteraction
  apply Finset.sum_eq_zero
  intro j _
  rw [← scalarVectorMulTransverseVec_mulLInf, hvanish j]
  simp

/-- **The diffusion-only commutator** of the proof of `lem:parametrix-error`: on an
annulus where `u_⊥ = 0`,

`[A_{ε,K}, χ]h = ε(2∇_⊥χ·∇_⊥h + (Δ_⊥χ)h)`. -/
theorem commutator_apply_of_velocityVanishesOnGradient
    (chi : HorizontalSecondOrderCutoff) (u : TransverseRealW1Inf)
    (epsilon : ℝ) (K : ℤ) (hvanish : VelocityVanishesOnGradient chi u)
    (b : TransverseC2H2) :
    commutator chi u epsilon K b =
      (epsilon : ℂ) •
        ((2 : ℂ) • gradientInteraction chi b + laplacianInteraction chi b) := by
  rw [commutator_apply, transportInteraction_eq_zero chi u hvanish b, sub_zero]

/-! ## Norm-ready bounds -/

/-- The gradient interaction is bounded by `Σ_j ‖∂_jχ‖_∞ ‖∂_jb‖_{L²}`. -/
theorem norm_gradientInteraction_le
    (chi : HorizontalSecondOrderCutoff) (b : TransverseC2H2) :
    ‖gradientInteraction chi b‖ ≤
      ∑ j : Fin 2, ‖chi.gradient j‖ * ‖transverseVecDerivFromH2 (Fin 2) j b‖ := by
  unfold gradientInteraction
  calc
    ‖∑ j : Fin 2, scalarVectorMulTransverseC2 (chi.gradient j)
        (transverseVecDerivFromH2 (Fin 2) j b)‖ ≤
        ∑ j : Fin 2, ‖scalarVectorMulTransverseC2 (chi.gradient j)
          (transverseVecDerivFromH2 (Fin 2) j b)‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin 2, ‖chi.gradient j‖ * ‖transverseVecDerivFromH2 (Fin 2) j b‖ := by
      gcongr with j
      exact norm_scalarVectorMulTransverseVec_apply_le _ _

/-- The zeroth-order interaction is bounded by `‖Δχ‖_∞ ‖b‖_{L²}`. -/
theorem norm_laplacianInteraction_le
    (chi : HorizontalSecondOrderCutoff) (b : TransverseC2H2) :
    ‖laplacianInteraction chi b‖ ≤ ‖chi.laplacian‖ * ‖transverseH2Embedding b‖ :=
  norm_scalarVectorMulTransverseVec_apply_le _ _

/-- Norm form of the diffusion-only commutator: with the cut-off derivative norms replaced by
their explicit scale bounds `‖∂_jχ‖_∞ ≤ C₁/R` and `‖Δχ‖_∞ ≤ 2C₂/R²`
(`eq:parametrix-cutoff-bounds`), this is the `ε/R` and `ε/R²` display in the proof of
`lem:parametrix-error`. -/
theorem norm_commutator_apply_le_explicitScale
    (chi : HorizontalSecondOrderCutoff) (u : TransverseRealW1Inf)
    (epsilon R C₁ C₂ : ℝ) (K : ℤ)
    (hvanish : VelocityVanishesOnGradient chi u)
    (hgradient : ∀ j, ‖chi.gradient j‖ ≤ C₁ / R)
    (hlaplacian : ‖chi.laplacian‖ ≤ 2 * C₂ / R ^ 2)
    (b : TransverseC2H2) :
    ‖commutator chi u epsilon K b‖ ≤
      |epsilon| *
        (2 * ((C₁ / R) * ∑ j : Fin 2, ‖transverseVecDerivFromH2 (Fin 2) j b‖) +
          (2 * C₂ / R ^ 2) * ‖transverseH2Embedding b‖) := by
  rw [commutator_apply_of_velocityVanishesOnGradient chi u epsilon K hvanish b]
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs]
  gcongr
  calc
    ‖(2 : ℂ) • gradientInteraction chi b + laplacianInteraction chi b‖ ≤
        ‖(2 : ℂ) • gradientInteraction chi b‖ + ‖laplacianInteraction chi b‖ :=
      norm_add_le _ _
    _ = 2 * ‖gradientInteraction chi b‖ + ‖laplacianInteraction chi b‖ := by
      simp [norm_smul]
    _ ≤ 2 * ((C₁ / R) * ∑ j : Fin 2, ‖transverseVecDerivFromH2 (Fin 2) j b‖) +
        (2 * C₂ / R ^ 2) * ‖transverseH2Embedding b‖ := by
      have hg : ‖gradientInteraction chi b‖ ≤
          (C₁ / R) * ∑ j : Fin 2, ‖transverseVecDerivFromH2 (Fin 2) j b‖ := by
        refine (norm_gradientInteraction_le chi b).trans ?_
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun j _ ↦
          mul_le_mul_of_nonneg_right (hgradient j) (norm_nonneg _)
      have hl : ‖laplacianInteraction chi b‖ ≤
          (2 * C₂ / R ^ 2) * ‖transverseH2Embedding b‖ :=
        (norm_laplacianInteraction_le chi b).trans
          (mul_le_mul_of_nonneg_right hlaplacian (norm_nonneg _))
      gcongr

end HorizontalCutoffCommutator

end

end FastDynamo
