/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.FixedSector
public import LeanPool.FastDynamo.Operator.HorizontalProjection
public import LeanPool.FastDynamo.Analysis.TransverseVecMultipliers
public import LeanPool.FastDynamo.Operator.RieszDomainCalculus

/-!
# The horizontal torus operator `A_{ε,K}` of the paper

Paper Section 5 (`sec:axial`) works with an operator acting on the **two horizontal components
only**; the axial magnetic component is recovered afterwards (`lem:axial-recovery`).  For a
real transverse `W^{1,∞}` velocity `u` and an axial Fourier index `K`, the paper defines
(`eq:torus-sector`)

`A_{ε,K} h = ε(Δ⊥ - (2πK)²)h - u⊥·∇⊥h - 2πiK u₃ h + (h·∇⊥)u⊥`,
`D(A_{ε,K}) = H²(T²; ℂ²)`.

No constraint is imposed on `h`, and the axial velocity enters only through the imaginary
multiplication operator `-2πiK u₃` (the paragraph after `eq:torus-sector`).

This module builds that operator on the fibre-generic torus Sobolev layer, with exactly the
sign and normalization conventions of `FastDynamo/Operator/FixedSector.lean`:

* `horizontalInductionDiffusion K` is the fibre-blind `transverseVecDiffusion (Fin 2) K`;
* `horizontalInductionTransport u` is `u⊥·∇⊥`, subtracted in the assembled action;
* `horizontalInductionAxialTransport u K` is `2πiK u₃`, also subtracted;
* `horizontalInductionStretching u` is `∑_{j<2} h_j (∂_j u)⊥`, added.

The pointwise projection `π⊥ : ℂ³ → ℂ²` itself is `horizontalProjPoint` of
`FastDynamo/Operator/HorizontalProjection.lean`, shared with the whole-plane chain.  The one
velocity coefficient not provided by `FastDynamo/Analysis/TransverseW1Inf.lean` is the
**horizontal projection of the derivative coefficients** `(∂_j u)⊥`, defined here as
`transverseW1InfHorizontalDerivLInf j`.

The second half of the module records the exact block relation between the
three-component `reducedInductionOperator` and `A_{ε,K}`: writing `ℂ³ = ℂ²_⊥ ⊕ ℂ₃` and
`π⊥ : ℂ³ → ℂ²` for the coordinate projection,

`π⊥ (A₃ b) = A₂ (π⊥ b)`,

i.e. **`A₂` is the quotient (horizontal compression) of `A₃`, not its restriction**: the
purely axial subspace is `A₃`-invariant, the horizontal one is not, because the third row of
`A₃` still carries `∑_{j<2} b_j ∂_j u₃`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal

/-! ## The horizontal projection on the transverse `L²` and `L∞` spaces -/

/-- The horizontal projection `π⊥ : L²(T²; ℂ³) → L²(T²; ℂ²)`. -/
def horizontalProjL2 : TransverseC3L2 →L[ℂ] TransverseC2L2 :=
  horizontalProjPoint.compLpL 2 transverseMeasure

/-- The horizontal projection `π⊥ : L∞(T²; ℂ³) → L∞(T²; ℂ²)`, used only on the velocity
gradient coefficients. -/
def horizontalProjLInf : TransverseC3LInf →L[ℂ] TransverseC2LInf :=
  horizontalProjPoint.compLpL ∞ transverseMeasure

/-- An almost-everywhere representative of the horizontal `L²` projection. -/
theorem horizontalProjL2_coe_ae (f : TransverseC3L2) :
    (horizontalProjL2 f : TransverseTorus → C2) =ᵐ[transverseMeasure]
      fun x ↦ horizontalProjPoint ((f : TransverseTorus → C3) x) :=
  horizontalProjPoint.coeFn_compLpL f

/-- An almost-everywhere representative of the horizontal `L∞` projection. -/
theorem horizontalProjLInf_coe_ae (a : TransverseC3LInf) :
    (horizontalProjLInf a : TransverseTorus → C2) =ᵐ[transverseMeasure]
      fun x ↦ horizontalProjPoint ((a : TransverseTorus → C3) x) :=
  horizontalProjPoint.coeFn_compLpL a

/-- The `j`-th coordinate of the horizontally projected field is the `j`-th coordinate of the
original field, for `j < 2`. -/
theorem transverseCoordL2_horizontalProjL2 (j : Fin 2) (f : TransverseC3L2) :
    transverseCoordL2 j (horizontalProjL2 f) = transverseCoordL2 j.castSucc f := by
  ext1
  have h1 := (EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL (horizontalProjL2 f)
  have h3 := (EuclideanSpace.proj (𝕜 := ℂ) j.castSucc).coeFn_compLpL f
  filter_upwards [h1, h3, horizontalProjL2_coe_ae f] with x hx1 hx3 hx2
  calc (transverseCoordL2 j (horizontalProjL2 f) : TransverseTorus → ℂ) x
      = EuclideanSpace.proj j ((horizontalProjL2 f : TransverseTorus → C2) x) := hx1
    _ = EuclideanSpace.proj j (horizontalProjPoint ((f : TransverseTorus → C3) x)) := by
        rw [hx2]
    _ = EuclideanSpace.proj j.castSucc ((f : TransverseTorus → C3) x) := rfl
    _ = (transverseCoordL2 j.castSucc f : TransverseTorus → ℂ) x := hx3.symm

/-- The `j`-th Fourier coefficient of the horizontally projected field is the `j`-th Fourier
coefficient of the original field, for `j < 2`. -/
theorem transverseCoeffCLM_horizontalProjL2
    (n : TransverseFrequency) (j : Fin 2) (f : TransverseC3L2) :
    transverseCoeffCLM n j (horizontalProjL2 f) =
      transverseCoeffCLM n j.castSucc f := by
  change transverseScalarCoeffCLM n (transverseCoordL2 j (horizontalProjL2 f)) =
    transverseScalarCoeffCLM n (transverseCoordL2 j.castSucc f)
  rw [transverseCoordL2_horizontalProjL2]

/-! ## The horizontal projection commutes with the lower-order multipliers -/

/-- The horizontal projection commutes with multiplication by a scalar `L∞` velocity
coefficient; this is what makes the transport and axial transport terms descend. -/
theorem horizontalProjL2_scalarVectorMulTransverse
    (a : TransverseScalarLInf) (f : TransverseC3L2) :
    horizontalProjL2 (scalarVectorMulTransverse a f) =
      scalarVectorMulTransverseC2 a (horizontalProjL2 f) :=
  compLpL_scalarVectorMulL2 horizontalProjPoint a f

/-- The horizontal projection turns multiplication by a `ℂ³`-valued `L∞` coefficient into
multiplication by its horizontal part; this is what makes the stretching term descend. -/
theorem horizontalProjL2_vectorScalarMulTransverse
    (a : TransverseC3LInf) (g : TransverseScalarL2) :
    horizontalProjL2 (vectorScalarMulTransverse a g) =
      vectorScalarMulTransverseC2 (horizontalProjLInf a) g :=
  compLpL_vectorScalarMulL2 horizontalProjPoint a g

/-! ## The horizontal projection on the transverse `H²` Fourier graph -/

/-- Drop the axial component of a stored weighted Fourier-coefficient array. -/
def horizontalProjWeightedCoeffs :
    WeightedTransverseC3Coeffs →L[ℂ] WeightedTransverseC2Coeffs :=
  (PiLp.continuousLinearEquiv 2 ℂ
      (fun _ : Fin 2 ↦ TransverseScalarFourierL2)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi fun j : Fin 2 ↦
      PiLp.proj 2 (fun _ : Fin 3 ↦ TransverseScalarFourierL2) j.castSucc)

/-- The projected coefficient array stores the first two components of the original array. -/
@[simp] theorem horizontalProjWeightedCoeffs_apply
    (a : WeightedTransverseC3Coeffs) (j : Fin 2) :
    horizontalProjWeightedCoeffs a j = a j.castSucc :=
  rfl

/-- The physical field and the coefficient array of a three-component `H²` element project to a
pair which again satisfies the two-component `H²` graph equation. -/
theorem horizontalProjH2_graph_mem (b : TransverseC3H2) :
    (horizontalProjL2 (transverseH2Embedding b),
      horizontalProjWeightedCoeffs (transverseH2WeightedCoeffs b)) ∈
        transverseH2Submodule (ι := Fin 2) := by
  rw [mem_transverseH2Submodule_iff]
  intro n j
  rw [horizontalProjWeightedCoeffs_apply, transverseH2WeightedCoeffs_apply,
    transverseCoeffCLM_horizontalProjL2]

/-- The horizontal projection `π⊥ : H²(T²; ℂ³) → H²(T²; ℂ²)` on the closed Fourier graphs. -/
def horizontalProjH2 : TransverseC3H2 →L[ℂ] TransverseC2H2 :=
  ((horizontalProjL2.comp transverseH2Embedding).prod
    (horizontalProjWeightedCoeffs.comp transverseH2WeightedCoeffs)).codRestrict
      transverseH2Submodule horizontalProjH2_graph_mem

/-- The `H²`-level horizontal projection lies over the `L²`-level one. -/
theorem transverseH2Embedding_horizontalProjH2 (b : TransverseC3H2) :
    transverseH2Embedding (horizontalProjH2 b) =
      horizontalProjL2 (transverseH2Embedding b) :=
  rfl

/-- The transverse Laplacian candidate commutes with the horizontal projection: it is a scalar
Fourier multiplier acting diagonally in the fibre. -/
theorem horizontalProjL2_transverseLaplacianFromH2 (b : TransverseC3H2) :
    horizontalProjL2 (transverseLaplacianFromH2 b) =
      transverseVecLaplacianFromH2 (Fin 2) (horizontalProjH2 b) := by
  apply transverseVecL2_ext_coeff
  intro n j
  rw [transverseCoeffCLM_horizontalProjL2, transverseCoeffCLM_transverseLaplacianFromH2,
    transverseCoeffCLM_transverseLaplacianFromH2, transverseH2Embedding_horizontalProjH2,
    transverseCoeffCLM_horizontalProjL2]

/-- Each transverse derivative candidate commutes with the horizontal projection. -/
theorem horizontalProjL2_transverseDerivFromH2 (j : Fin 2) (b : TransverseC3H2) :
    horizontalProjL2 (transverseDerivFromH2 j b) =
      transverseVecDerivFromH2 (Fin 2) j (horizontalProjH2 b) := by
  apply transverseVecL2_ext_coeff
  intro n i
  rw [transverseCoeffCLM_horizontalProjL2, transverseCoeffCLM_transverseDerivFromH2,
    transverseCoeffCLM_transverseDerivFromH2, transverseH2Embedding_horizontalProjH2,
    transverseCoeffCLM_horizontalProjL2]

/-! ## The horizontal velocity gradient coefficients -/

/--
The horizontal part `(∂_j u)⊥` of one essentially bounded velocity gradient coefficient.

This is the only velocity coefficient map required by `eq:torus-sector` that is defined in
this module: the transport coefficients `u₁, u₂` and the axial multiplier coefficient `u₃`
are the scalar components `transverseW1InfComplexValueCoordLInf`, whereas the
stretching term needs the two-component field `(∂_j u)⊥` rather than the full `∂_j u`.
-/
def transverseW1InfHorizontalDerivLInf (j : Fin 2) :
    TransverseRealW1Inf →L[ℝ] TransverseC2LInf :=
  (horizontalProjLInf.restrictScalars ℝ).comp (transverseW1InfComplexDerivLInf j)

/-- The horizontal velocity gradient coefficient is the horizontal projection of the full
complexified gradient coefficient. -/
@[simp] theorem transverseW1InfHorizontalDerivLInf_apply
    (j : Fin 2) (u : TransverseRealW1Inf) :
    transverseW1InfHorizontalDerivLInf j u =
      horizontalProjLInf (transverseW1InfComplexDerivLInf j u) :=
  rfl

/-! ## The horizontal torus operator `A_{ε,K}` -/

/--
The diffusion term `Δ⊥ - (2πK)²` of `A_{ε,K}` (`eq:torus-sector`).

It is the fibre-blind `transverseVecDiffusion` of `FastDynamo/Operator/FixedSector.lean` at the
two-component fibre; no velocity coefficient enters.
-/
def horizontalInductionDiffusion (K : ℤ) :
    TransverseC2H2 →L[ℂ] TransverseC2L2 :=
  transverseVecDiffusion (Fin 2) K

/--
The transverse transport term `u⊥·∇⊥ = ∑_{j<2} u_j ∂_j` of `A_{ε,K}` (`eq:torus-sector`).
It is subtracted in `horizontalInductionAction`.
-/
def horizontalInductionTransport (u : TransverseRealW1Inf) :
    TransverseC2H2 →L[ℂ] TransverseC2L2 :=
  ∑ j : Fin 2,
    (scalarVectorMulTransverseC2
      (transverseW1InfComplexValueCoordLInf j.castSucc u)).comp
        (transverseVecDerivFromH2 (Fin 2) j)

/--
The axial transport term `2π i K u₃` of `A_{ε,K}` (`eq:torus-sector`).  It is
subtracted in `horizontalInductionAction`, giving the paper's `-2π i K u₃ h`; the axial
velocity enters `A_{ε,K}` only through this imaginary multiplication operator.
-/
def horizontalInductionAxialTransport (u : TransverseRealW1Inf) (K : ℤ) :
    TransverseC2H2 →L[ℂ] TransverseC2L2 :=
  axialMultiplier K •
    (scalarVectorMulTransverseC2
      (transverseW1InfComplexValueCoordLInf 2 u)).comp
        (transverseH2Embedding (ι := Fin 2))

/--
The stretching term `(h·∇⊥)u⊥ = ∑_{j<2} h_j (∂_j u)⊥` of `A_{ε,K}` (`eq:torus-sector`).
Only the horizontal part of each velocity gradient coefficient appears; this is
exactly where the paper's operator differs from the three-component
`reducedInductionStretching`.
-/
def horizontalInductionStretching (u : TransverseRealW1Inf) :
    TransverseC2H2 →L[ℂ] TransverseC2L2 :=
  ∑ j : Fin 2,
    (vectorScalarMulTransverseC2
      (transverseW1InfHorizontalDerivLInf j u)).comp
        ((transverseCoordL2 (ι := Fin 2) j).comp (transverseH2Embedding (ι := Fin 2)))

/--
The exact horizontal induction action of `eq:torus-sector`:

`ε(Δ⊥ - (2πK)²)h - ∑_{j<2} u_j ∂_j h - 2π i K u₃ h + ∑_{j<2} h_j (∂_j u)⊥`.
-/
def horizontalInductionAction (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    TransverseC2H2 →L[ℂ] TransverseC2L2 :=
  (ε : ℂ) • horizontalInductionDiffusion K -
    horizontalInductionTransport u - horizontalInductionAxialTransport u K +
      horizontalInductionStretching u

/--
The horizontal torus operator `A_{ε,K}` of `eq:torus-sector`, on
`L²(T²; ℂ²)` with domain `D(A_{ε,K}) = H²(T²; ℂ²)` realized as the closed Fourier graph
`TransverseC2H2`.  No constraint is imposed on `h` (as in the paper).
-/
def horizontalInductionOperator (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    DomainOperator TransverseC2L2 TransverseC2H2 where
  embedding := transverseH2Embedding
  embedding_injective := transverseH2Embedding_injective
  op := horizontalInductionAction u ε K

/-- The domain embedding of `A_{ε,K}` is the transverse `H²` Fourier-graph inclusion. -/
theorem horizontalInductionOperator_embedding (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    (horizontalInductionOperator u ε K).embedding = transverseH2Embedding :=
  rfl

/-- The action of `A_{ε,K}` is `horizontalInductionAction`. -/
theorem horizontalInductionOperator_op (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) :
    (horizontalInductionOperator u ε K).op = horizontalInductionAction u ε K :=
  rfl

/-! ## Exact formulas on horizontal amplitudes -/

/-- Expanded form of the diffusion term of `A_{ε,K}`. -/
theorem horizontalInductionDiffusion_apply (K : ℤ) (h : TransverseC2H2) :
    horizontalInductionDiffusion K h =
      transverseVecLaplacianFromH2 (Fin 2) h -
        (2 * Real.pi * K : ℂ) ^ 2 • transverseH2Embedding h :=
  rfl

/-- Expanded form of the transport term `u⊥·∇⊥ h`. -/
theorem horizontalInductionTransport_apply
    (u : TransverseRealW1Inf) (h : TransverseC2H2) :
    horizontalInductionTransport u h =
      ∑ j : Fin 2, scalarVectorMulTransverseC2
        (transverseW1InfComplexValueCoordLInf j.castSucc u)
          (transverseVecDerivFromH2 (Fin 2) j h) := by
  simp [horizontalInductionTransport]

/-- Expanded form of the axial transport term `2π i K u₃ h`. -/
theorem horizontalInductionAxialTransport_apply
    (u : TransverseRealW1Inf) (K : ℤ) (h : TransverseC2H2) :
    horizontalInductionAxialTransport u K h =
      axialMultiplier K • scalarVectorMulTransverseC2
        (transverseW1InfComplexValueCoordLInf 2 u) (transverseH2Embedding h) :=
  rfl

/-- Expanded form of the stretching term `(h·∇⊥)u⊥`. -/
theorem horizontalInductionStretching_apply
    (u : TransverseRealW1Inf) (h : TransverseC2H2) :
    horizontalInductionStretching u h =
      ∑ j : Fin 2, vectorScalarMulTransverseC2
        (transverseW1InfHorizontalDerivLInf j u)
          (transverseCoordL2 j (transverseH2Embedding h)) := by
  simp [horizontalInductionStretching]

/-- The horizontal action expanded into exactly the four terms of `eq:torus-sector`. -/
theorem horizontalInductionAction_apply
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (h : TransverseC2H2) :
    horizontalInductionAction u ε K h =
      (ε : ℂ) •
          (transverseVecLaplacianFromH2 (Fin 2) h -
            (2 * Real.pi * K : ℂ) ^ 2 • transverseH2Embedding h) -
        (∑ j : Fin 2, scalarVectorMulTransverseC2
          (transverseW1InfComplexValueCoordLInf j.castSucc u)
            (transverseVecDerivFromH2 (Fin 2) j h)) -
        axialMultiplier K • scalarVectorMulTransverseC2
          (transverseW1InfComplexValueCoordLInf 2 u) (transverseH2Embedding h) +
        (∑ j : Fin 2, vectorScalarMulTransverseC2
          (transverseW1InfHorizontalDerivLInf j u)
            (transverseCoordL2 j (transverseH2Embedding h))) := by
  simp only [horizontalInductionAction, add_apply, sub_apply, smul_apply,
    horizontalInductionDiffusion_apply, horizontalInductionTransport_apply,
    horizontalInductionAxialTransport_apply, horizontalInductionStretching_apply]

/-! ## The block relation: `A₂` is the quotient of `A₃`

Write `ℂ³ = ℂ²_⊥ ⊕ ℂ₃`, `π⊥ : ℂ³ → ℂ²`.  In block form with respect to that splitting the
three-component operator of `FastDynamo/Operator/FixedSector.lean` is

```
        [ A₂   0 ]              S h = ∑_{j<2} h_j ∂_j u₃              (bounded, order 0)
A₃  =   [        ] ,   where    D   = ε(Δ⊥-(2πK)²) - u⊥·∇⊥ - 2πiK u₃  (scalar)
        [ S    D ]
```

so the horizontal block row does not see `b₃` and `π⊥ ∘ A₃ = A₂ ∘ π⊥`.  The horizontal
subspace is **not** `A₃`-invariant (the `(3,⊥)` block `S` is nonzero), which is why `A₂` is the
quotient of `A₃` rather than its restriction.
-/

/-- The diffusion term descends through the horizontal projection. -/
theorem horizontalProjL2_reducedInductionDiffusion (K : ℤ) (b : TransverseC3H2) :
    horizontalProjL2 (reducedInductionDiffusion K b) =
      horizontalInductionDiffusion K (horizontalProjH2 b) := by
  rw [reducedInductionDiffusion_apply, horizontalInductionDiffusion_apply,
    map_sub, map_smul, horizontalProjL2_transverseLaplacianFromH2,
    transverseH2Embedding_horizontalProjH2]

/-- The transverse transport term descends through the horizontal projection. -/
theorem horizontalProjL2_reducedInductionTransport
    (u : TransverseRealW1Inf) (b : TransverseC3H2) :
    horizontalProjL2 (reducedInductionTransport u b) =
      horizontalInductionTransport u (horizontalProjH2 b) := by
  rw [reducedInductionTransport_apply, horizontalInductionTransport_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [horizontalProjL2_scalarVectorMulTransverse,
    horizontalProjL2_transverseDerivFromH2]

/-- The axial transport term descends through the horizontal projection. -/
theorem horizontalProjL2_reducedInductionAxialTransport
    (u : TransverseRealW1Inf) (K : ℤ) (b : TransverseC3H2) :
    horizontalProjL2 (reducedInductionAxialTransport u K b) =
      horizontalInductionAxialTransport u K (horizontalProjH2 b) := by
  rw [reducedInductionAxialTransport_apply, horizontalInductionAxialTransport_apply,
    map_smul, horizontalProjL2_scalarVectorMulTransverse,
    transverseH2Embedding_horizontalProjH2]

/--
The stretching term descends through the horizontal projection: the horizontal block row of
`∑_{j<2} b_j ∂_j u` is `∑_{j<2} (π⊥ b)_j (∂_j u)⊥`, which no longer involves `b₃`.
-/
theorem horizontalProjL2_reducedInductionStretching
    (u : TransverseRealW1Inf) (b : TransverseC3H2) :
    horizontalProjL2 (reducedInductionStretching u b) =
      horizontalInductionStretching u (horizontalProjH2 b) := by
  rw [reducedInductionStretching_apply, horizontalInductionStretching_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  rw [horizontalProjL2_vectorScalarMulTransverse,
    transverseH2Embedding_horizontalProjH2, transverseCoordL2_horizontalProjL2,
    transverseW1InfHorizontalDerivLInf_apply]

/--
**The block relation.**  The horizontal projection of the three-component
fixed-sector action is the horizontal action applied to the projected field:
`π⊥ (A₃ b) = A₂ (π⊥ b)`.
-/
theorem horizontalProjL2_reducedInductionAction
    (u : TransverseRealW1Inf) (ε : ℝ) (K : ℤ) (b : TransverseC3H2) :
    horizontalProjL2 (reducedInductionAction u ε K b) =
      horizontalInductionAction u ε K (horizontalProjH2 b) := by
  simp only [reducedInductionAction, horizontalInductionAction, add_apply, sub_apply,
    smul_apply, map_add, map_sub, map_smul]
  rw [horizontalProjL2_reducedInductionDiffusion,
    horizontalProjL2_reducedInductionTransport,
    horizontalProjL2_reducedInductionAxialTransport,
    horizontalProjL2_reducedInductionStretching]

end

end FastDynamo
