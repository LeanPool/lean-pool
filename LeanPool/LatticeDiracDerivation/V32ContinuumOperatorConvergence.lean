/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation at commit e2161e0936f181d4a5a9d49963a666f7cea42502.
Upstream source is dual-licensed under MIT or CC0 1.0; used here under MIT.
-/

module

public import LeanPool.LatticeDiracDerivation.V32NonrelativisticLimit
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumDiscreteTime
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumVerletTime

/-! # V3.2 Stage 10: separated spatial and centered-time defects -/

@[expose] public section



namespace LeanDirac.V2

noncomputable section
open Filter Topology

/-- The bundled V3.2 C on ti nu um Op er at or Co nv er ge nc eC er ti fi ca te. -/
structure V32ContinuumOperatorConvergenceCertificate : Prop where
  exactSpatialSplit : ∀ momentum,
    c19TransportSymbol momentum =
      c19QuadraticSymbol momentum + c19SpatialRemainder momentum
  spatialFourthOrderBound : ∀ momentum radius,
    0 ≤ radius → (∀ axis, |momentum axis| ≤ radius) →
      2 * radius ≤ 1 →
      |c19SpatialRemainder momentum| ≤ 40 * radius ^ 4
  centeredTimeDefectVanishes : ∀ r momentum phase component,
    Tendsto
      (fun dt : ℝ =>
        uniformActionToStandardDirac r momentum
          (uniformCenteredTemporalDefect r dt momentum phase) component)
      (nhds 0) (nhds 0)
  verletLocalErrorIsSecondOrder : ∀ r momentum phase component,
    Tendsto
      (fun dt : ℝ =>
        if dt = 0 then 0 else
          uniformActionToStandardDirac r momentum
              (uniformVerletLocalDefect r dt momentum phase) component /
            ((dt ^ 2 : ℝ) : ℂ))
      (nhds 0) (nhds 0)
  finiteC19CurrentRemainderVanishes : ∀
      (momentum : LatticeMomentum) (axis : Fin 3) (q : UniformCell2),
    Tendsto
      (fun scale : ℝ =>
        finiteC19CurrentRemainder
          (fun coordinate => scale * momentum coordinate) axis q)
      (nhds 0) (nhds 0)

theorem v32_continuum_operator_convergence :
    V32ContinuumOperatorConvergenceCertificate where
  exactSpatialSplit := c19_symbol_exact_quadratic_plus_remainder
  spatialFourthOrderBound := c19_spatial_remainder_bound
  centeredTimeDefectVanishes :=
    uniform_centered_temporal_defect_readout_tends_to_zero
  verletLocalErrorIsSecondOrder := uniform_verlet_local_defect_is_little_o_dt_sq
  finiteC19CurrentRemainderVanishes :=
    finite_c19_current_remainder_tends_to_zero


end
end LeanDirac.V2
