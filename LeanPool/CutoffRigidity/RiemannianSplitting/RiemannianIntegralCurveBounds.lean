/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.IntegralCurve.Basic
import TauCeti.Geometry.Manifold.IntegralCurve.Regularity
import TauCeti.Geometry.Manifold.Riemannian.Distance
public import Mathlib.Topology.UniformSpace.Cauchy

/-! # Bounds and finite limits for bounded-speed integral curves -/

@[expose] public section

open Bundle Set Filter Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal


namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [BoundarylessManifold I M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- The speed bound of a vector field gives a Lipschitz bound on each of its integral curves. -/
theorem IsMIntegralCurveOn.lipschitzOnWith_of_bounded
    {X : (x : M) → TangentSpace I x} {γ : ℝ → M} {a b : ℝ}
    (hγ : IsMIntegralCurveOn γ X (Ioo a b))
    (hX : Continuous (T% X)) {C : ℝ≥0}
    (hbound : ∀ t ∈ Ioo a b, ‖X (γ t)‖ₑ ≤ C) :
    LipschitzOnWith C γ (Ioo a b) := by
  have : IsManifold I ((0 + 1 : ℕ) : ℕ∞ω) M := by
    simpa using (inferInstance : IsManifold I 1 M)
  have hregular : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Ioo a b) := by
    simpa only [Nat.zero_add, Nat.cast_one] using
      (TauCeti.Manifold.contMDiffOn_succ_of_isMIntegralCurveOn 0 isOpen_Ioo.uniqueDiffOn hγ
        (fun _ _ ↦ BoundarylessManifold.isInteriorPoint)
        (fun _ _ ↦ (contMDiff_zero_iff.mpr hX).contMDiffAt))
  refine TauCeti.IsRiemannianManifold.lipschitzOnWith_of_norm_curveVelocity_le (I := I)
    ordConnected_Ioo (fun t ht ↦ (hregular t ht).contMDiffAt (isOpen_Ioo.mem_nhds ht))
    (fun t ht ↦ ?_)
  rw [TauCeti.Manifold.curveVelocity_apply,
    ((hγ t ht).hasMFDerivAt (isOpen_Ioo.mem_nhds ht)).mfderiv]
  change ‖(1 : ℝ) • X (γ t)‖ ≤ C
  rw [one_smul]
  exact eNorm_le_coe.mp (hbound t ht)

/-- A bounded-speed curve in a complete manifold tends to a limit at any finite
time approached from its interval of definition. -/
theorem IsMIntegralCurveOn.exists_tendsto_of_bounded [CompleteSpace M]
    {X : (x : M) → TangentSpace I x} {γ : ℝ → M} {a b t : ℝ}
    (hγ : IsMIntegralCurveOn γ X (Ioo a b)) (hX : Continuous (T% X)) {C : ℝ≥0}
    (hbound : ∀ s ∈ Ioo a b, ‖X (γ s)‖ₑ ≤ C) (hne : NeBot (𝓝[Ioo a b] t)) :
    ∃ x : M, Tendsto γ (𝓝[Ioo a b] t) (𝓝 x) := by
  have := hne
  apply cauchy_map_iff_exists_tendsto.mp
  exact (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le
    (IsMIntegralCurveOn.lipschitzOnWith_of_bounded hγ hX hbound).uniformContinuousOn inf_le_right

end CutoffRigidity
