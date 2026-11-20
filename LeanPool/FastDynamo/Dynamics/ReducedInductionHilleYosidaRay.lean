/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Dynamics.HilleYosida.Generation
public import LeanPool.FastDynamo.Dynamics.MainGrowthFloor
public import LeanPool.FastDynamo.Global.ReducedInductionHalfPlaneResolvent

/-!
# The Hille–Yosida ray of the reduced induction operator

This module supplies, for the **reduced** induction operator

`A_{ε,K} := reducedInductionOperator u ε K : DomainOperator TransverseC3L2 TransverseC3H2`,

the input that the abstract Hille–Yosida machinery of `FastDynamo/Dynamics/HilleYosida/`
consumes: a `HilleYosidaRay`.  The operator is obtained from the induction equation by freezing
the axial Fourier index at a single `K : ℤ`.  Its ambient space `TransverseC3L2` is the complex
`L²` space of `ℂ³`-valued fields on the **transverse two-torus**, and its domain
`TransverseC3H2` is the corresponding `H²` space; no solenoidal constraint is imposed on either.
Writing `M_u := ‖transverseStretchingCoefficient u‖` for the `L^∞` norm of the transverse
velocity gradient, `FastDynamo/Global/ReducedInductionHalfPlaneResolvent.lean` supplies the
two-sided domain-valued resolvent on the open half-plane `{Re z > M_u}` together with the
Hille–Yosida estimate `‖(z - A_{ε,K})⁻¹‖_{L² → L²} ≤ (Re z - M_u)⁻¹` there.  Restricting it to
the real ray through `HilleYosidaRay.ofHalfPlane` gives `reducedInductionHilleYosidaRay`.  This
step uses `0 < ε` (the far reference point of the Neumann construction needs a diffusion).

## Main declarations

* `reducedInductionHilleYosidaRay` — the ray of `A_{ε,K}` with growth constant `M_u`;
* `reducedInductionHilleYosidaRay_spectralSet` — its spectral set is the whole coercive
  half-plane `{Re z > M_u}`, not merely the real ray;
* `norm_stateResolvent_reducedInductionHilleYosidaRay_le` — the real-ray estimate
  `‖(r - A_{ε,K})⁻¹‖ ≤ (r - M_u)⁻¹`.

The fibrewise resolvents carried by the ray are what
`FastDynamo/Dynamics/Assembly/ProductResolvent.lean` assembles, over all axial frequencies, into
the resolvent of the operator on `ProductC3L2`; the paper's growth rate
`γ(u, ε)` (`eq:semigroup-growth-rate`) of the full induction operator on `L²_σ(T³)` is the
business of the assembly modules under `FastDynamo/Dynamics/Assembly/`.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

/-! ## The Hille–Yosida ray of the reduced operator -/

/--
**The Hille–Yosida ray of the reduced induction operator.**  For a transversely
divergence-free `W^{1,∞}` velocity `u`, a positive diffusivity `ε` and an axial index `K`,
the operator `A_{ε,K} = reducedInductionOperator u ε K` has a two-sided domain-valued
resolvent at every complex `z` with `Re z > M_u := ‖transverseStretchingCoefficient u‖`,
obeying `‖(z - A_{ε,K})⁻¹‖ ≤ (Re z - M_u)⁻¹`; in particular at every real `r > M_u`, which is
the hypothesis `HilleYosidaRay` records.

The certificate is the chosen half-plane family
`reducedInductionRightHalfPlaneResolvent` and the estimate is
`norm_stateResolvent_reducedInductionOperator_rightHalfPlane_le`, restricted to the ray by
`HilleYosidaRay.ofHalfPlane`.  The constant `M_u` is the one produced by the energy
competition of the numerical range, uniformly in `ε` and `K`.
-/
def reducedInductionHilleYosidaRay (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) (ε : ℝ) (hε : 0 < ε) (K : ℤ) :
    HilleYosidaRay (reducedInductionOperator u ε K)
      ‖transverseStretchingCoefficient u‖ :=
  HilleYosidaRay.ofHalfPlane
    (reducedInductionRightHalfPlaneResolvent u hu ε hε K)
    (fun _z hz ↦
      norm_stateResolvent_reducedInductionOperator_rightHalfPlane_le u hu ε hε K hz)

/-- The spectral set of `reducedInductionHilleYosidaRay` is the whole coercive right
half-plane `{Re z > M_u}`, not merely the real ray: `HilleYosidaRay.ofHalfPlane` keeps the
half-plane certificate and only adds the ray estimate.  This is definitional. -/
theorem reducedInductionHilleYosidaRay_spectralSet (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) (ε : ℝ) (hε : 0 < ε) (K : ℤ) :
    (reducedInductionHilleYosidaRay u hu ε hε K).spectralSet =
      reducedInductionRightHalfPlane u :=
  rfl

/-- The real-ray estimate carried by `reducedInductionHilleYosidaRay`, restated on the real
parameter: `‖(r - A_{ε,K})⁻¹‖ ≤ (r - M_u)⁻¹` for every real `r > M_u`.  This is the field
`HilleYosidaRay.norm_stateResolvent_le` of the ray, and agrees with
`norm_stateResolvent_reducedInductionOperator_realRay_le`. -/
theorem norm_stateResolvent_reducedInductionHilleYosidaRay_le (u : TransverseRealW1Inf)
    (hu : IsTransverseDivergenceFree u) (ε : ℝ) (hε : 0 < ε) (K : ℤ) {r : ℝ}
    (hr : ‖transverseStretchingCoefficient u‖ < r) :
    ‖(reducedInductionHilleYosidaRay u hu ε hε K).resolvent.stateResolvent (r : ℂ)‖ ≤
      (r - ‖transverseStretchingCoefficient u‖)⁻¹ :=
  (reducedInductionHilleYosidaRay u hu ε hε K).norm_stateResolvent_le r hr

end

end FastDynamo
