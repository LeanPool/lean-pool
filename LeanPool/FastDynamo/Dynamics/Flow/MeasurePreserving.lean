/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Dynamics.Flow.TorusFlow

/-!
# The explicit particle flow preserves the volume of the three-torus

`FastDynamo/Dynamics/Flow/TorusFlow.lean` packages the plane flow of `prop:particle-flow` as the
datum `fullFlowData`, and `FastDynamo/Dynamics/Flow/PeriodizedFlowData.lean` proves, generically
over such a datum, that the flow `Φ_t : T³ → T³` preserves the volume.  This module reads that
off at `fullFlowData`, producing the measure-preservation clause of `IsIdealInductionGroup`
(`FastDynamo/Dynamics/ParticleFlow.lean`), namely the paper's

> Liouville's formula and `Div u = 0` give `det DΦ_t = 1` almost everywhere.  Since `Φ_t` is
> bi-Lipschitz, the area formula shows that it preserves Lebesgue measure.

(proof of `cor:ideal-growth`); it is what makes the upper bound `‖𝒯₀(t) B_in‖₂ ≤
C_L (1 + |t|) ‖B_in‖₂` of `cor:ideal-growth` (proved in the last paragraph of its proof) an
estimate about `‖DΦ_t‖_∞` alone.

Liouville's formula is *not* used (a deviation in the argument, not in the statement).  The flow
is explicit, so the Jacobian determinant is computed pointwise in
`FastDynamo/Dynamics/Flow/TorusFlow.lean` (`det_fderiv_planePeriodizedTransverseFlow`) from the
rank-one derivative formula of `FastDynamo/Dynamics/Flow/CellFlowMap.lean`, and it is the field
`det_fderiv_flow` of the datum that the generic three-step argument consumes: the plane, the
transverse two-torus through the invariant fundamental box `pairUnitIocBox`, and the axial shear
through `MeasureTheory.MeasurePreserving.skew_product`.

The transport corollary consumed downstream, `quasiMeasurePreserving_literalFlow` (pulling
almost-everywhere statements back along `Φ_t`, the device of `eq:ideal-cauchy-formula`), is the
generic one specialised here as well.
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open MeasureTheory

namespace ScaleFamily.TorusCellPlacement

variable {p : LocalSeedParameters} {r : ScaleRatios p}
variable (h : PonomarenkoSmoothingWidth)
variable (P : TorusCellPlacement (r := r) (1 + (h : ℝ)))
variable (angularSpeed axialSpeed tau : ℝ)

/-- **The particle flow preserves the volume of the literal three-torus.**  The flow is the skew
product of the transverse flow with the axial translations, read through the measure-preserving
identification `productToLiteral` of the product model with `Torus 3`.  This is the
`measurePreserving` field of `IsIdealInductionGroup` (proof of `cor:ideal-growth`). -/
theorem measurePreserving_literalFlow (t : ℝ) :
    MeasurePreserving (literalFlow h P angularSpeed axialSpeed tau t)
      (volume : Measure (Torus 3)) volume :=
  (fullFlowData h P angularSpeed axialSpeed tau).measurePreserving_literalFlow t

/-- The particle flow is quasi measure preserving.  This is the form in which almost-everywhere
statements are pulled back along `Φ_t` in the Cauchy formula `eq:ideal-cauchy-formula`. -/
theorem quasiMeasurePreserving_literalFlow (t : ℝ) :
    QuasiMeasurePreserving (literalFlow h P angularSpeed axialSpeed tau t)
      (volume : Measure (Torus 3)) volume :=
  (fullFlowData h P angularSpeed axialSpeed tau).quasiMeasurePreserving_literalFlow t

end ScaleFamily.TorusCellPlacement

end

end FastDynamo
