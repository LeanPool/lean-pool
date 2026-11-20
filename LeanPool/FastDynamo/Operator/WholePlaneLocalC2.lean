/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Local.WholePlaneC2
public import LeanPool.FastDynamo.Operator.HorizontalProjection

/-!
# The two-component whole-plane induction operators

The paper writes both the local seed and the
selected cell on **two horizontal components**.  This module builds the corresponding strong
operators on `L²(ℝ²; ℂ²)` with domain the weak Fourier graph `H²(ℝ²; ℂ²)` of
`FastDynamo/Local/WholePlaneC2.lean`:

* the local generator (`eq:local-generator`)

  `𝓛_δ b = δ(Δ⊥ - N²)b - v⊥·∇⊥b - iNv₃b + (b·∇⊥)v⊥`,   `D(𝓛_δ) = H²(ℝ²; ℂ²)`,

  with the axial wavenumber `N` kept as a parameter (the paper's display has `N = 2π`:
  `4π²` and `2πi v₃`), assembled as `wholePlaneC2LocalOperator`, and also available as
  `horizontalLocalOperator N δ w`;

* the selected whole-plane operator (`eq:selected-whole-plane-operator`)

  `A^{(n)}_{ε,n}h = ε(Δ⊥ - (2πK_n)²)h - (u_n^loc)⊥·∇⊥h - 2πiK_n((u_n^loc)₃ + a_n)h
      + (h·∇⊥)(u_n^loc)⊥`,   `D = H²(ℝ²; ℂ²)`,

  assembled as `selectedWholePlaneC2InductionOperator`.

Both are the transplant to `ℝ²` of the torus operator `eq:torus-sector`
formalised by `FastDynamo/Operator/HorizontalSector.lean`, and the sign and normalisation
conventions are exactly those of that module and of the three-component whole-plane
`FastDynamo/Operator/WholePlaneLocal.lean`.

**What changes against the three-component version.**  Only the *stretching* term.  The
velocity data stays the three-component record `WholePlaneVelocityCoefficients` of
`FastDynamo/Operator/WholePlaneLocal.lean` — the paper's velocity is `ℝ³`-valued and its
axial component `v₃` is an input of the axial multiplier — but the stretching term of
`eq:local-generator` carries only the **horizontal part** `(∂_j v)⊥` of each gradient
coefficient.  That projection is `wholePlaneHorizontalProjLInf` here, the whole-plane twin of
`horizontalProjLInf` of `FastDynamo/Operator/HorizontalSector.lean`; the two live on different
`L∞` spaces, but both are built from the one pointwise map `horizontalProjPoint` of
`FastDynamo/Operator/HorizontalProjection.lean`.

The seed's *weak* form `𝔩_w` (`eq:jump-sectorial-form`) is built in
`FastDynamo/Local/HorizontalWeakForm.lean` on the form domain `H¹(ℝ²; ℂ²)` and integrates the
stretching term by parts, so it needs no gradient coefficient at all.  The identification of
the form operator `A_w` with the strong operator built here is the `L² → H²` domain step of
`prop:local-seed` (last paragraph of its proof); it is proved in
`FastDynamo/Local/HorizontalFormStrongIdentification.lean`, not in this module.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory
open scoped ENNReal LineDeriv SchwartzMap

/-! ## The horizontal projection of a three-component coefficient -/

/-- The horizontal projection `π⊥ : L∞(ℝ²; ℂ³) → L∞(ℝ²; ℂ²)`, applied only to the velocity
gradient coefficients. -/
def wholePlaneHorizontalProjLInf : WholePlaneC3LInf →L[ℂ] WholePlaneC2LInf :=
  horizontalProjPoint.compLpL ∞ volume

/-- An almost-everywhere representative of the horizontal `L∞` projection. -/
theorem wholePlaneHorizontalProjLInf_coe_ae (a : WholePlaneC3LInf) :
    (wholePlaneHorizontalProjLInf a : WholePlane → C2) =ᵐ[volume]
      fun y ↦ horizontalProjPoint ((a : WholePlane → C3) y) :=
  horizontalProjPoint.coeFn_compLpL a

namespace WholePlaneVelocityCoefficients

/--
The horizontal part `(∂_j v)⊥` of one essentially bounded velocity gradient coefficient.

This is the only coefficient map required by the two-component operators that is defined in
this module: the transport coefficients `v₁, v₂` and the axial multiplier coefficient `v₃` are
the scalar components `wholePlaneCoordLInf i v.value`, whereas the stretching term of
`eq:local-generator` needs the two-component field `(∂_j v)⊥` rather than the full
`∂_j v`.
-/
def horizontalDeriv (v : WholePlaneVelocityCoefficients) (j : Fin 2) : WholePlaneC2LInf :=
  wholePlaneHorizontalProjLInf (v.deriv j)

/-- The horizontal gradient coefficient is the horizontal projection of the stored gradient
coefficient. -/
@[simp] theorem horizontalDeriv_apply
    (v : WholePlaneVelocityCoefficients) (j : Fin 2) :
    v.horizontalDeriv j = wholePlaneHorizontalProjLInf (v.deriv j) :=
  rfl

end WholePlaneVelocityCoefficients

/-! ## The two-component local generator `𝓛_δ` -/

/-- The multiplier `Δ⊥ - N²` on the two-component weak whole-plane `H²` domain
(`eq:local-generator`). -/
def wholePlaneC2LocalDiffusion (N : ℝ) :
    WholePlaneC2H2 →L[ℂ] WholePlaneC2L2 :=
  wholePlaneLaplacian C2 -
    ((N : ℂ) ^ 2) • wholePlaneH2Embedding C2

/-- The transverse transport term `v⊥·∇⊥b = ∑_{j<2} v_j ∂_j b` (`eq:local-generator`).
It is subtracted in `wholePlaneC2LocalAction`. -/
def wholePlaneC2LocalTransport (v : WholePlaneVelocityCoefficients) :
    WholePlaneC2H2 →L[ℂ] WholePlaneC2L2 :=
  ∑ j : Fin 2,
    (scalarVectorMulL2 (E := C2) volume
      (wholePlaneCoordLInf j.castSucc v.value)).comp
        (wholePlaneH2FirstDerivative C2 j)

/-- The axial transport term `iNv₃b` (`eq:local-generator`, where `N = 2π`).  It is subtracted in
`wholePlaneC2LocalAction`; the axial velocity enters only through this imaginary
multiplication operator. -/
def wholePlaneC2LocalAxialTransport
    (v : WholePlaneVelocityCoefficients) (N : ℝ) :
    WholePlaneC2H2 →L[ℂ] WholePlaneC2L2 :=
  (Complex.I * (N : ℂ)) •
    (scalarVectorMulL2 (E := C2) volume
      (wholePlaneCoordLInf (2 : Fin 3) v.value)).comp
        (wholePlaneH2Embedding C2)

/-- The stretching term `(b·∇⊥)v⊥ = ∑_{j<2} b_j (∂_j v)⊥` (`eq:local-generator`).
Only the horizontal part of each velocity gradient coefficient appears; this is exactly where
the two-component operator differs from `wholePlaneLocalStretching`. -/
def wholePlaneC2LocalStretching (v : WholePlaneVelocityCoefficients) :
    WholePlaneC2H2 →L[ℂ] WholePlaneC2L2 :=
  ∑ j : Fin 2,
    (vectorScalarMulL2 (E := C2) volume (v.horizontalDeriv j)).comp
      ((wholePlaneC2CoordL2 j).comp (wholePlaneH2Embedding C2))

/-- The paper's local generator on two-component fields (`eq:local-generator`, with the
paper's `N = 2π`),

`𝓛_δ b = δ(Δ⊥ - N²)b - v⊥·∇⊥b - iNv₃b + (b·∇⊥)v⊥`.
-/
def wholePlaneC2LocalAction (v : WholePlaneVelocityCoefficients)
    (delta N : ℝ) : WholePlaneC2H2 →L[ℂ] WholePlaneC2L2 :=
  (delta : ℂ) • wholePlaneC2LocalDiffusion N -
    wholePlaneC2LocalTransport v - wholePlaneC2LocalAxialTransport v N +
      wholePlaneC2LocalStretching v

/-- The local generator `𝓛_δ` as a domain-aware unbounded operator on `L²(ℝ²; ℂ²)` with
domain `H²(ℝ²; ℂ²)` (`eq:local-generator`). -/
def wholePlaneC2LocalOperator (v : WholePlaneVelocityCoefficients)
    (delta N : ℝ) : DomainOperator WholePlaneC2L2 WholePlaneC2H2 where
  embedding := wholePlaneH2Embedding C2
  embedding_injective := wholePlaneH2Embedding_injective C2
  op := wholePlaneC2LocalAction v delta N

/--
The local seed operator `𝓛_δ` with its arguments in the order: axial wavenumber `N`
first, then the diffusivity `δ`, then the velocity.

The record `w` carries the paper's velocity (`w` in §2.1, `v = v_h` in `prop:local-seed`) as
`w.value` and its transverse
weak gradient as `w.deriv`; `WholePlaneVelocityCoefficients.HasWeakGradient` certifies the
latter.  The weak form `𝔩_w` of `eq:jump-sectorial-form`, built in
`FastDynamo/Local/HorizontalWeakForm.lean`, uses only `w.value`, because it integrates the
stretching term by parts (the display before `eq:jump-sectorial-form`).
-/
def horizontalLocalOperator (N delta : ℝ) (w : WholePlaneVelocityCoefficients) :
    DomainOperator WholePlaneC2L2 WholePlaneC2H2 :=
  wholePlaneC2LocalOperator w delta N

/-! ## The selected whole-plane operator `A^{(n)}_{ε,n}` -/

/-- The constant axial background contributes the scalar action `-(2πiKa)b`
(`eq:selected-whole-plane-operator`). -/
def selectedWholePlaneC2AxialShift (K : ℤ) (a : ℝ) :
    WholePlaneC2H2 →L[ℂ] WholePlaneC2L2 :=
  (axialMultiplier K * (a : ℂ)) • wholePlaneH2Embedding C2

/-- The selected whole-plane action of `eq:selected-whole-plane-operator`:
the local copy of the cell velocity at diffusivity `ε` and axial wavenumber `2πK`, minus the
constant axial spectral translation `2πiKa`. -/
def selectedWholePlaneC2InductionAction
    (uLoc : WholePlaneVelocityCoefficients) (ε : ℝ) (K : ℤ) (a : ℝ) :
    WholePlaneC2H2 →L[ℂ] WholePlaneC2L2 :=
  wholePlaneC2LocalAction uLoc ε (wholePlaneAxialWavenumber K) -
    selectedWholePlaneC2AxialShift K a

/-- The selected whole-plane operator `A^{(n)}_{ε,n}` of
`eq:selected-whole-plane-operator`, on `L²(ℝ²; ℂ²)` with domain
`H²(ℝ²; ℂ²)`.  No constraint is imposed on `h`. -/
def selectedWholePlaneC2InductionOperator
    (uLoc : WholePlaneVelocityCoefficients) (ε : ℝ) (K : ℤ) (a : ℝ) :
    DomainOperator WholePlaneC2L2 WholePlaneC2H2 where
  embedding := wholePlaneH2Embedding C2
  embedding_injective := wholePlaneH2Embedding_injective C2
  op := selectedWholePlaneC2InductionAction uLoc ε K a

/-! ## Exact expanded formulas -/

/-- The fixed-mode local diffusion is `Δ⊥b - N²b`: the transverse Laplacian minus the axial
symbol at wavenumber `N`. -/
theorem wholePlaneC2LocalDiffusion_apply (N : ℝ) (b : WholePlaneC2H2) :
    wholePlaneC2LocalDiffusion N b =
      wholePlaneLaplacian C2 b -
        ((N : ℂ) ^ 2) • wholePlaneH2Embedding C2 b :=
  rfl

/-- The named local diffusion operator represents the negative fixed-mode gradient pairing
against every weak `H¹` test field.  This is the diffusion half of the agreement between the
strong operator and the weak form `𝔩_w` of `eq:jump-sectorial-form`. -/
theorem wholePlaneC2LocalDiffusion_integrationByParts
    (N : ℝ) (b : WholePlaneC2H2) (phi : WholePlaneC2H1) :
    (∑ j : Fin 2,
        inner ℂ (wholePlaneH1FirstDerivative C2 j phi)
          (wholePlaneH2FirstDerivative C2 j b)) +
      inner ℂ
        ((Complex.I * (N : ℂ)) • wholePlaneH1Embedding C2 phi)
        ((Complex.I * (N : ℂ)) • wholePlaneH2Embedding C2 b) =
      -inner ℂ (wholePlaneH1Embedding C2 phi)
        (wholePlaneC2LocalDiffusion N b) := by
  rw [wholePlaneC2LocalDiffusion_apply]
  exact wholePlaneH2H1_fixedNGradientLaplacian_integrationByParts C2 N b phi

/-- Expanded form of the transverse transport term: the sum over `j < 2` of the `j`-th
velocity component times the `j`-th weak derivative of `b`. -/
theorem wholePlaneC2LocalTransport_apply
    (v : WholePlaneVelocityCoefficients) (b : WholePlaneC2H2) :
    wholePlaneC2LocalTransport v b =
      ∑ j : Fin 2,
        scalarVectorMulL2 (E := C2) volume
          (wholePlaneCoordLInf j.castSucc v.value)
            (wholePlaneH2FirstDerivative C2 j b) := by
  simp [wholePlaneC2LocalTransport]

/-- Expanded form of the axial transport term: `iN` times the third velocity component times
`b`, the axial derivative having become the multiplier `iN` on the fixed mode. -/
theorem wholePlaneC2LocalAxialTransport_apply
    (v : WholePlaneVelocityCoefficients) (N : ℝ) (b : WholePlaneC2H2) :
    wholePlaneC2LocalAxialTransport v N b =
      (Complex.I * (N : ℂ)) •
        scalarVectorMulL2 (E := C2) volume
          (wholePlaneCoordLInf (2 : Fin 3) v.value)
            (wholePlaneH2Embedding C2 b) :=
  rfl

/-- Expanded form of the stretching term: the sum over `j < 2` of the horizontal part of
`∂_j v` times the `j`-th component of `b`. -/
theorem wholePlaneC2LocalStretching_apply
    (v : WholePlaneVelocityCoefficients) (b : WholePlaneC2H2) :
    wholePlaneC2LocalStretching v b =
      ∑ j : Fin 2,
        vectorScalarMulL2 (E := C2) volume (v.horizontalDeriv j)
          (wholePlaneC2CoordL2 j (wholePlaneH2Embedding C2 b)) := by
  simp [wholePlaneC2LocalStretching]

/-- The selected-cell spectral translation acts as multiplication by the constant
`axialMultiplier K * a = 2πiKa`, the shift subtracted in the selected action. -/
theorem selectedWholePlaneC2AxialShift_apply
    (K : ℤ) (a : ℝ) (b : WholePlaneC2H2) :
    selectedWholePlaneC2AxialShift K a b =
      (axialMultiplier K * (a : ℂ)) • wholePlaneH2Embedding C2 b :=
  rfl

end

end FastDynamo
