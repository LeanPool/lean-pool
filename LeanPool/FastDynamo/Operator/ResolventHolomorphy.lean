/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

-- Modified for Lean Pool.

module

public import LeanPool.FastDynamo.Operator.RieszResolventIdentity

/-!
# Holomorphy of bundled-domain resolvents

The two-parameter resolvent identity determines the complex derivative of the
ambient state resolvent.  On an open resolvent set, continuity upgrades the
divided-difference identity to operator-norm differentiability, with the usual
formula `R'(z) = -R(z)^2` (`stateResolvent_hasDerivAt`).
-/

@[expose] public section

namespace FastDynamo

noncomputable section

open Filter Set

namespace HasResolventOn

universe u v

variable {X : Type u} {D : Type v}
  [NormedAddCommGroup X] [NormedSpace ℂ X]
  [NormedAddCommGroup D] [NormedSpace ℂ D]
  {A : DomainOperator X D} {S : Set ℂ}

/-- On an open resolvent set, the ambient state resolvent has the usual
operator-norm derivative `R'(z) = -R(z)^2`. -/
theorem stateResolvent_hasDerivAt (h : HasResolventOn A S) (hS : IsOpen S)
    {z : ℂ} (hz : z ∈ S) :
    HasDerivAt h.stateResolvent
      (-((h.stateResolvent z).comp (h.stateResolvent z))) z := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hcontinuous : ContinuousAt h.stateResolvent z :=
    h.continuousOn_stateResolvent.continuousAt (hS.mem_nhds hz)
  have htendsto : Tendsto
      (fun w : ℂ ↦ -((h.stateResolvent z).comp (h.stateResolvent w)))
      (nhds z) (nhds (-((h.stateResolvent z).comp (h.stateResolvent z)))) := by
    have hcompose : ContinuousAt
        (fun w : ℂ ↦ (h.stateResolvent z).comp (h.stateResolvent w)) z :=
      (ContinuousLinearMap.compL ℂ X X X
        (h.stateResolvent z)).continuous.continuousAt.comp hcontinuous
    exact hcompose.neg
  apply htendsto.mono_left inf_le_left |>.congr'
  have hSeventually : ∀ᶠ w in nhds z, w ∈ S := hS.mem_nhds hz
  filter_upwards [hSeventually.filter_mono inf_le_left,
    self_mem_nhdsWithin] with w hwS hwne
  rw [slope]
  have hwnez : w ≠ z := by simpa using hwne
  have hres := h.stateResolvent_sub_stateResolvent hz hwS
  change -((h.stateResolvent z).comp (h.stateResolvent w)) =
    (w - z)⁻¹ • (h.stateResolvent w - h.stateResolvent z)
  rw [show h.stateResolvent w - h.stateResolvent z =
      -((w - z) • (h.stateResolvent z).comp (h.stateResolvent w)) by
    simpa only [neg_sub] using congrArg Neg.neg hres]
  simp [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hwnez)]

end HasResolventOn

end

end FastDynamo
