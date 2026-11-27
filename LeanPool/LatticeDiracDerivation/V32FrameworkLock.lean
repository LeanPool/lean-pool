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

public import LeanPool.LatticeDiracDerivation.V2.LorentzSpin

/-!
# V3.2 framework and claim lock

This module starts V3.2 from the two sealed V3.1 cumulative certificates.  It
adds no field, action term, stencil coefficient, physical unit, or particle
interpretation.
-/

@[expose] public section

namespace LeanDirac.V2



/-- The bundled V3.2 F ra me wo rk Lo ck Ce rt if ic at e. -/
structure V32FrameworkLockCertificate : Prop where
  freeDirac : CompleteFreeDiracCertificate
  lorentzSpin : LorentzSpinHalfCertificate
  nativeMass :
    (0 : ℝ) ≤ chi0 ∧ chi0 ^ 2 = chi0 ^ 2 ∧
      ∀ mass : ℝ, 0 ≤ mass → mass ^ 2 = chi0 ^ 2 → mass = chi0
  c19Speed : c19ContinuumSpeed ^ 2 = 12
  zeroMode : c19TransportSymbol (fun _ => 0) = 0
  spatialRemainderAtRest : c19SpatialRemainder (fun _ => 0) = 0

theorem v32_framework_lock : V32FrameworkLockCertificate where
  freeDirac := complete_first_principles_free_dirac
  lorentzSpin := lorentz_spin_half_from_native_action
  nativeMass := canonical_native_mass_is_chi0
  c19Speed := c19_continuum_speed_square
  zeroMode := c19_transport_symbol_zero
  spatialRemainderAtRest := c19_spatial_remainder_zero_at_origin

end LeanDirac.V2
