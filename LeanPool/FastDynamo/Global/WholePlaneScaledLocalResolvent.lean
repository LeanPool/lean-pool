/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Reduction.ExactScalingC2
public import LeanPool.FastDynamo.Global.TorusBackgroundParameters

/-!
# The selected whole-plane resolvent `cor:scaled-local-resolvents`

This module proves `cor:scaled-local-resolvents`
for the two-component selected whole-plane operator.  The seed's uniform resolvent bound enters
as an interface hypothesis, so that the concrete local-seed record can discharge it without this
module depending on the seed construction.

## Statement

Let `w` be the local velocity coefficients, `Gamma` the local contour, and suppose the local
generator `cL_delta = horizontalLocalOperator N delta w` has a resolvent on `Gamma` with the
uniform `L² → H²` bound `‖R_delta(zeta)‖ ≤ C_*`.  Let `s` match the parameters exactly
(`delta = eps/ell^2`, `N = (2 pi K) ell`, `tau = (2 pi K) a`, `lem:exact-renormalization`).
Then the selected whole-plane operator `A^{(n)}_{eps,n}` has a resolvent on the
translated contour `Gamma_tau` given by

`cR_n(z) = U_n R_delta(z + i tau) U_n^{-1}`  (proof of `cor:scaled-local-resolvents`),

and it satisfies

`‖cR_n(z) f‖₂ ≤ C_* ‖f‖₂`,
`sqrt(eps) ‖∂_j cR_n(z) f‖₂ ≤ sqrt(delta) C_* ‖f‖₂ ≤ sqrt(delta_+) C_* ‖f‖₂`.

The gradient half is exactly the paper's computation: `U_n` is unitary on `L²` and
`‖∇_⊥ U_n f‖₂ = ell_n^{-1} ‖∇ f‖₂`, so the `ell_n^{-1}` produced by the rescaling combines with
`sqrt(eps)` into `sqrt(eps)/ell_n = sqrt(delta_n) ≤ sqrt(delta_+)` (proof of
`cor:scaled-local-resolvents`).

The constant `C_*` is the seed's resolvent bound (it is not the support radius `L_*` of the
paper's `prop:local-seed`).

## Main definitions and results

* `WholePlaneLocalResolventBound` — the interface: a resolvent family for `cL_delta` on a
  parameter set together with the uniform `L² → H²` operator-norm bound.
* `selectedScaledOperator` — `A^{(n)}_{eps,n}` at the matching parameters.
* `scaledLocalResolvent` — `HasResolventOn (A^{(n)}_{eps,n}) Gamma_tau`.
* `norm_embedding_scaledLocalResolventInv_le`,
  `sqrt_epsilon_mul_norm_deriv_scaledLocalResolventInv_le` — `eq:local-gradient`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Set

/-! ## The seed interface -/

/--
**The uniform local resolvent bound of `prop:local-seed`**, as an interface.

`resolvent` is the family `R_delta(zeta) : L²(ℝ²;ℂ²) → H²(ℝ²;ℂ²)` of `prop:local-seed`
(with domain `H²`, as identified at the end of the proof of `prop:local-seed`), and
`norm_inv_le` is its uniform `L² → H²` operator-norm bound `C_*`.  The paper's
`eq:local-continuation-bound` states the weaker `L² → H¹` bound; the `H²` form is what the
domain-valued resolvent carries, and only its `L²` and gradient halves are consumed below.
-/
structure WholePlaneLocalResolventBound (w : WholePlaneVelocityCoefficients)
    (N delta : ℝ) (S : Set ℂ) (bound : ℝ) where
  /-- The chosen domain-valued resolvent family of the local generator `cL_delta`. -/
  resolvent : HasResolventOn (horizontalLocalOperator N delta w) S
  /-- The uniform `L² → H²` bound `‖R_delta(zeta)‖ ≤ C_*` on the parameter set. -/
  norm_inv_le : ∀ z ∈ S, ‖resolvent.inv z‖ ≤ bound

namespace WholePlaneLocalResolventBound

variable {w : WholePlaneVelocityCoefficients} {N delta : ℝ} {S : Set ℂ} {bound : ℝ}

/-- The graph-norm bound, in applied form. -/
theorem norm_inv_apply_le (L : WholePlaneLocalResolventBound w N delta S bound) {z : ℂ}
    (hz : z ∈ S) (f : WholePlaneC2L2) : ‖L.resolvent.inv z f‖ ≤ bound * ‖f‖ :=
  le_trans ((L.resolvent.inv z).le_opNorm f)
    (mul_le_mul_of_nonneg_right (L.norm_inv_le z hz) (norm_nonneg f))

/-- The `L²` half of the seed bound: `‖R_delta(zeta) f‖₂ ≤ C_* ‖f‖₂`. -/
theorem norm_embedding_inv_apply_le (L : WholePlaneLocalResolventBound w N delta S bound)
    {z : ℂ} (hz : z ∈ S) (f : WholePlaneC2L2) :
    ‖wholePlaneH2Embedding C2 (L.resolvent.inv z f)‖ ≤ bound * ‖f‖ :=
  le_trans (norm_wholePlaneH2Embedding_le C2 _) (L.norm_inv_apply_le hz f)

/-- The gradient half of the seed bound: `‖∂_j R_delta(zeta) f‖₂ ≤ C_* ‖f‖₂`. -/
theorem norm_deriv_inv_apply_le (L : WholePlaneLocalResolventBound w N delta S bound)
    {z : ℂ} (hz : z ∈ S) (f : WholePlaneC2L2) (j : Fin 2) :
    ‖wholePlaneH2FirstDerivative C2 j (L.resolvent.inv z f)‖ ≤ bound * ‖f‖ :=
  le_trans (norm_wholePlaneH2FirstDerivative_le C2 _ j) (L.norm_inv_apply_le hz f)

end WholePlaneLocalResolventBound

/-! ## The vertically translated parameter set -/

/-- `S_tau = {z : z + i tau ∈ S}`, the paper's translation of the local spectral parameter
set (`Γ_τ`, `𝒢_τ`, defined after `lem:exact-renormalization`). -/
def verticallyShiftedSet (tau : ℝ) (S : Set ℂ) : Set ℂ :=
  (fun z : ℂ ↦ z + Complex.I * (tau : ℂ)) ⁻¹' S

/-- Membership in the translated set is membership in the original set after undoing the
shift. -/
@[simp] theorem mem_verticallyShiftedSet_iff (tau : ℝ) (S : Set ℂ) (z : ℂ) :
    z ∈ verticallyShiftedSet tau S ↔ z + Complex.I * (tau : ℂ) ∈ S := Iff.rfl

/-- For a spectral circle the translated parameter set is the boundary of the translated
circle: `Gamma_tau`. -/
theorem verticallyShiftedSet_boundary (Gamma : SpectralCircle) (tau : ℝ) :
    verticallyShiftedSet tau Gamma.boundary =
      (backgroundShiftedContour Gamma tau).boundary := by
  ext z
  rw [mem_verticallyShiftedSet_iff, mem_backgroundShiftedContour_boundary_iff]

/-- The same for the closed region: `cG_tau`. -/
theorem verticallyShiftedSet_closedRegion (Gamma : SpectralCircle) (tau : ℝ) :
    verticallyShiftedSet tau Gamma.closedRegion =
      (backgroundShiftedContour Gamma tau).closedRegion := by
  ext z
  rw [mem_verticallyShiftedSet_iff, mem_backgroundShiftedContour_closedRegion_iff]

/-! ## The conjugated selected resolvent -/

section Scaled

variable (v : WholePlaneVelocityCoefficients) (pt : WholePlane)
  (s : WholePlaneExactScalingParameters) {S : Set ℂ} {bound : ℝ}

/-- `A^{(n)}_{eps,n}`, the selected whole-plane operator at the matching parameters
(`eq:selected-whole-plane-operator`). -/
def selectedScaledOperator : DomainOperator WholePlaneC2L2 WholePlaneC2H2 :=
  selectedWholePlaneC2InductionOperator
    (rescaledWholePlaneVelocityCoefficients v pt s.ell s.ell_pos) s.epsilon s.K s.a

/-- **`cR_n(z) = U_n R_{delta_n}(z + i tau) U_n^{-1}`** (proof of
`cor:scaled-local-resolvents`). -/
def scaledLocalResolventInv (L : WholePlaneLocalResolventBound v s.N s.delta S bound)
    (z : ℂ) : WholePlaneC2L2 →L[ℂ] WholePlaneC2H2 :=
  (wholePlaneRescaleH2CLE C2 pt s.ell s.ell_pos).toContinuousLinearMap.comp
    ((L.resolvent.inv (z + Complex.I * (s.tau : ℂ))).comp
      (wholePlaneRescaleLinearIsometryEquiv C2 pt s.ell
        s.ell_pos).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The conjugated resolvent, applied. -/
@[simp] theorem scaledLocalResolventInv_apply
    (L : WholePlaneLocalResolventBound v s.N s.delta S bound) (z : ℂ) (f : WholePlaneC2L2) :
    scaledLocalResolventInv v pt s L z f =
      wholePlaneRescaleH2CLE C2 pt s.ell s.ell_pos
        (L.resolvent.inv (z + Complex.I * (s.tau : ℂ))
          ((wholePlaneRescaleLinearIsometryEquiv C2 pt s.ell s.ell_pos).symm f)) :=
  rfl

/--
**`cor:scaled-local-resolvents`, existence half**.

The scaling identity transports the local resolvent family to a two-sided resolvent of
the selected whole-plane operator on the translated parameter set.  The only input is the pencil
identity `eq:scaling` of `lem:exact-renormalization`.
-/
def scaledLocalResolvent (L : WholePlaneLocalResolventBound v s.N s.delta S bound) :
    HasResolventOn (selectedScaledOperator v pt s) (verticallyShiftedSet s.tau S) where
  inv := scaledLocalResolventInv v pt s L
  left_inv := by
    intro z hz
    apply ContinuousLinearMap.ext
    intro b
    have hzl : z + Complex.I * (s.tau : ℂ) ∈ S := hz
    have hpencil : (wholePlaneRescaleLinearIsometryEquiv C2 pt s.ell s.ell_pos).symm
          ((selectedScaledOperator v pt s).pencil z b) =
        (horizontalLocalOperator s.N s.delta v).pencil (z + Complex.I * (s.tau : ℂ))
          ((wholePlaneRescaleH2CLE C2 pt s.ell s.ell_pos).symm b) := by
      have hraw := exactScalingC2_pencil_translation v pt s z
        ((wholePlaneRescaleH2CLE C2 pt s.ell s.ell_pos).symm b)
      rw [(wholePlaneRescaleH2CLE C2 pt s.ell s.ell_pos).apply_symm_apply] at hraw
      exact hraw
    have hleft := DFunLike.congr_fun (L.resolvent.left_inv _ hzl)
      ((wholePlaneRescaleH2CLE C2 pt s.ell s.ell_pos).symm b)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.id_apply] at hleft ⊢
    rw [scaledLocalResolventInv_apply, hpencil, hleft]
    exact (wholePlaneRescaleH2CLE C2 pt s.ell s.ell_pos).apply_symm_apply b
  right_inv := by
    intro z hz
    apply ContinuousLinearMap.ext
    intro f
    have hzl : z + Complex.I * (s.tau : ℂ) ∈ S := hz
    have hpencil : (wholePlaneRescaleLinearIsometryEquiv C2 pt s.ell s.ell_pos).symm
          ((selectedScaledOperator v pt s).pencil z
            (wholePlaneRescaleH2CLE C2 pt s.ell s.ell_pos
              (L.resolvent.inv (z + Complex.I * (s.tau : ℂ))
                ((wholePlaneRescaleLinearIsometryEquiv C2 pt s.ell s.ell_pos).symm f)))) =
        (horizontalLocalOperator s.N s.delta v).pencil (z + Complex.I * (s.tau : ℂ))
          (L.resolvent.inv (z + Complex.I * (s.tau : ℂ))
            ((wholePlaneRescaleLinearIsometryEquiv C2 pt s.ell s.ell_pos).symm f)) :=
      exactScalingC2_pencil_translation v pt s z _
    have hright := DFunLike.congr_fun (L.resolvent.right_inv _ hzl)
      ((wholePlaneRescaleLinearIsometryEquiv C2 pt s.ell s.ell_pos).symm f)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.id_apply] at hright ⊢
    rw [hright] at hpencil
    apply (wholePlaneRescaleLinearIsometryEquiv C2 pt s.ell s.ell_pos).symm.injective
    rw [scaledLocalResolventInv_apply]
    exact hpencil
  continuousOn := by
    have hshift : ContinuousOn (fun z : ℂ ↦ z + Complex.I * (s.tau : ℂ))
        (verticallyShiftedSet s.tau S) := (continuous_id.add continuous_const).continuousOn
    have hmaps : MapsTo (fun z : ℂ ↦ z + Complex.I * (s.tau : ℂ))
        (verticallyShiftedSet s.tau S) S := fun _ hz ↦ hz
    have htrans : ContinuousOn
        (fun z : ℂ ↦ L.resolvent.inv (z + Complex.I * (s.tau : ℂ)))
        (verticallyShiftedSet s.tau S) := L.resolvent.continuousOn.comp hshift hmaps
    exact continuousOn_const.clm_comp (htrans.clm_comp continuousOn_const)

/-- The stored inverse of the transported family is the conjugated local one. -/
@[simp] theorem scaledLocalResolvent_inv
    (L : WholePlaneLocalResolventBound v s.N s.delta S bound) :
    (scaledLocalResolvent v pt s L).inv = scaledLocalResolventInv v pt s L :=
  rfl

/-! ## The uniform bounds `eq:local-gradient` -/

/-- The physical `L²` field of the conjugated resolvent is the rescaled local field. -/
theorem embedding_scaledLocalResolventInv
    (L : WholePlaneLocalResolventBound v s.N s.delta S bound) (z : ℂ) (f : WholePlaneC2L2) :
    wholePlaneH2Embedding C2 (scaledLocalResolventInv v pt s L z f) =
      wholePlaneRescale C2 pt s.ell s.ell_pos
        (wholePlaneH2Embedding C2 (L.resolvent.inv (z + Complex.I * (s.tau : ℂ))
          ((wholePlaneRescaleLinearIsometryEquiv C2 pt s.ell s.ell_pos).symm f))) := by
  rw [scaledLocalResolventInv_apply, wholePlaneRescaleH2CLE_apply,
    wholePlaneH2Embedding_rescaleH2]

/-- Each first weak derivative of the conjugated resolvent picks up the factor `ell_n^{-1}`:
this is the paper's `‖∇_⊥ U_n f‖₂ = ell_n^{-1} ‖∇ f‖₂` (proof of `cor:scaled-local-resolvents`). -/
theorem deriv_scaledLocalResolventInv
    (L : WholePlaneLocalResolventBound v s.N s.delta S bound) (z : ℂ) (f : WholePlaneC2L2)
    (j : Fin 2) :
    wholePlaneH2FirstDerivative C2 j (scaledLocalResolventInv v pt s L z f) =
      ((s.ell : ℂ))⁻¹ • wholePlaneRescale C2 pt s.ell s.ell_pos
        (wholePlaneH2FirstDerivative C2 j
          (L.resolvent.inv (z + Complex.I * (s.tau : ℂ))
            ((wholePlaneRescaleLinearIsometryEquiv C2 pt s.ell s.ell_pos).symm f))) := by
  rw [scaledLocalResolventInv_apply, wholePlaneRescaleH2CLE_apply,
    wholePlaneH2FirstDerivative_rescaleH2]

/-- **The `L²` half of `eq:local-gradient`**:
`‖cR_n(z) f‖₂ ≤ C_* ‖f‖₂`, with the seed's own constant.  The rescaling `U_n` is unitary on
`L²`, so no factor is picked up. -/
theorem norm_embedding_scaledLocalResolventInv_le
    (L : WholePlaneLocalResolventBound v s.N s.delta S bound) {z : ℂ}
    (hz : z ∈ verticallyShiftedSet s.tau S) (f : WholePlaneC2L2) :
    ‖wholePlaneH2Embedding C2 (scaledLocalResolventInv v pt s L z f)‖ ≤ bound * ‖f‖ := by
  have hzl : z + Complex.I * (s.tau : ℂ) ∈ S := hz
  rw [embedding_scaledLocalResolventInv, norm_wholePlaneRescale]
  refine le_trans (L.norm_embedding_inv_apply_le hzl _) ?_
  rw [(wholePlaneRescaleLinearIsometryEquiv C2 pt s.ell s.ell_pos).symm.norm_map]

/-- The transported gradient bound before the diffusivity is put in:
`‖∂_j cR_n(z) f‖₂ ≤ ell_n^{-1} C_* ‖f‖₂`. -/
theorem norm_deriv_scaledLocalResolventInv_le
    (L : WholePlaneLocalResolventBound v s.N s.delta S bound) {z : ℂ}
    (hz : z ∈ verticallyShiftedSet s.tau S) (f : WholePlaneC2L2) (j : Fin 2) :
    ‖wholePlaneH2FirstDerivative C2 j (scaledLocalResolventInv v pt s L z f)‖ ≤
      (s.ell)⁻¹ * (bound * ‖f‖) := by
  have hzl : z + Complex.I * (s.tau : ℂ) ∈ S := hz
  rw [deriv_scaledLocalResolventInv, norm_smul, norm_wholePlaneRescale]
  have hnorm : ‖((s.ell : ℂ))⁻¹‖ = (s.ell)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos s.ell_pos]
  rw [hnorm]
  refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr s.ell_pos.le)
  refine le_trans (L.norm_deriv_inv_apply_le hzl _ j) ?_
  rw [(wholePlaneRescaleLinearIsometryEquiv C2 pt s.ell s.ell_pos).symm.norm_map]

/-- `sqrt(eps) = sqrt(delta) ell`, the exact scaling relation `delta = eps/ell^2` in square-root
form (§5, the choice of `n = n(ε)`). -/
theorem sqrt_epsilon_eq (hdelta : 0 ≤ s.delta) :
    Real.sqrt s.epsilon = Real.sqrt s.delta * s.ell := by
  have hell : s.ell ≠ 0 := s.ell_pos.ne'
  have heps : s.epsilon = s.delta * s.ell ^ 2 := by
    rw [s.delta_eq]
    field_simp
  rw [heps, Real.sqrt_mul hdelta, Real.sqrt_sq s.ell_pos.le]

/--
**The gradient half of `eq:local-gradient`** (and the last step of the proof of
`cor:scaled-local-resolvents`): `sqrt(eps) ‖∂_j cR_n(z) f‖₂ ≤ sqrt(delta_n) C_* ‖f‖₂`.

The rescaling contributes `ell_n^{-1}` to the gradient, and `sqrt(eps)/ell_n = sqrt(delta_n)`.
-/
theorem sqrt_epsilon_mul_norm_deriv_scaledLocalResolventInv_le
    (L : WholePlaneLocalResolventBound v s.N s.delta S bound) (hdelta : 0 ≤ s.delta) {z : ℂ}
    (hz : z ∈ verticallyShiftedSet s.tau S) (f : WholePlaneC2L2) (j : Fin 2) :
    Real.sqrt s.epsilon *
        ‖wholePlaneH2FirstDerivative C2 j (scaledLocalResolventInv v pt s L z f)‖ ≤
      Real.sqrt s.delta * (bound * ‖f‖) := by
  have hbase := norm_deriv_scaledLocalResolventInv_le v pt s L hz f j
  have hstep : Real.sqrt s.epsilon *
      ‖wholePlaneH2FirstDerivative C2 j (scaledLocalResolventInv v pt s L z f)‖ ≤
      Real.sqrt s.epsilon * ((s.ell)⁻¹ * (bound * ‖f‖)) :=
    mul_le_mul_of_nonneg_left hbase (Real.sqrt_nonneg _)
  have hell : s.ell ≠ 0 := s.ell_pos.ne'
  have heq : Real.sqrt s.epsilon * ((s.ell)⁻¹ * (bound * ‖f‖)) =
      Real.sqrt s.delta * (bound * ‖f‖) := by
    rw [sqrt_epsilon_eq s hdelta]
    field_simp
  linarith [hstep, heq.le, heq.ge]

/-- The uniform form of the gradient half: once `delta_n ≤ delta_+`, the bound does not
involve the cell (proof of `cor:scaled-local-resolvents`). -/
theorem sqrt_epsilon_mul_norm_deriv_le_of_delta_le
    (L : WholePlaneLocalResolventBound v s.N s.delta S bound) (hdelta : 0 ≤ s.delta)
    {deltaUpper : ℝ} (hle : s.delta ≤ deltaUpper) (hbound : 0 ≤ bound) {z : ℂ}
    (hz : z ∈ verticallyShiftedSet s.tau S) (f : WholePlaneC2L2) (j : Fin 2) :
    Real.sqrt s.epsilon *
        ‖wholePlaneH2FirstDerivative C2 j (scaledLocalResolventInv v pt s L z f)‖ ≤
      Real.sqrt deltaUpper * (bound * ‖f‖) := by
  refine le_trans
    (sqrt_epsilon_mul_norm_deriv_scaledLocalResolventInv_le v pt s L hdelta hz f j) ?_
  exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hle)
    (mul_nonneg hbound (norm_nonneg f))

end Scaled

/-! ## The statement on the translated contour -/

/--
**`cor:scaled-local-resolvents`** on the
translated contour `Gamma_tau`: the selected whole-plane operator has a resolvent there, and the
two uniform bounds of `eq:local-gradient` hold with constants independent of `n`, `delta_n`
and `z`.
-/
def scaledLocalResolventOnShiftedContour (v : WholePlaneVelocityCoefficients)
    (pt : WholePlane) (s : WholePlaneExactScalingParameters) {Gamma : SpectralCircle}
    {bound : ℝ}
    (L : WholePlaneLocalResolventBound v s.N s.delta Gamma.boundary bound) :
    HasResolventOn (selectedScaledOperator v pt s)
      (backgroundShiftedContour Gamma s.tau).boundary :=
  (verticallyShiftedSet_boundary Gamma s.tau) ▸ scaledLocalResolvent v pt s L

end

end FastDynamo
