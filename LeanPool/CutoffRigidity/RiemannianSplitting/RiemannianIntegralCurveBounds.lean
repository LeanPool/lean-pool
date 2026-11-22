/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import LeanPool.CutoffRigidity.RiemannianSplitting.IntegralCurveRegularity
public import Mathlib.Topology.UniformSpace.Cauchy

/-!
# Bounded-speed manifold curves have finite-time limits

The distance is the actual Riemannian path-length distance, as specified by
`IsRiemannianManifold`. A pointwise bound on the actual velocity gives a
Lipschitz estimate and, under completeness, a genuine finite-time endpoint.
No distance comparison or endpoint-existence conclusion is assumed.
-/

@[expose] public section

open Bundle Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal


namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [PseudoEMetricSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

omit [IsManifold I 1 M] [IsRiemannianManifold I M] in
/-- Integrating an actual pointwise speed bound controls Riemannian length. -/
theorem pathELength_le_of_speed_bound {γ : ℝ → M} {a b : ℝ} {C : ℝ≥0}
    (hbound : ∀ t ∈ Icc a b, ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ ≤ C) :
    pathELength I γ a b ≤ C * ENNReal.ofReal (b - a) := by
  rw [pathELength_eq_lintegral_mfderiv_Icc]
  calc
    _ ≤ ∫⁻ t in Icc a b, (C : ℝ≥0∞) :=
      setLIntegral_mono' measurableSet_Icc hbound
    _ = _ := by simp

omit [IsManifold I 1 M] [IsRiemannianManifold I M] in
/-- An actual bounded vector field controls the length of each of its actual
integral curves on the time interval. -/
theorem IsMIntegralCurveOn.pathELength_le
    {X : (x : M) → TangentSpace I x} {γ : ℝ → M} {s : Set ℝ}
    (hγ : IsMIntegralCurveOn γ X s) (hs : IsOpen s) {C : ℝ≥0}
    (hbound : ∀ t ∈ s, ‖X (γ t)‖ₑ ≤ C)
    {a b : ℝ} (hab : Icc a b ⊆ s) :
    pathELength I γ a b ≤ C * ENNReal.ofReal (b - a) := by
  apply pathELength_le_of_speed_bound
  intro t ht
  have hd := ((hγ t (hab ht)).hasMFDerivAt (hs.mem_nhds (hab ht))).mfderiv
  rw [hd]
  change ‖(1 : ℝ) • X (γ t)‖ₑ ≤ C
  simpa using hbound t (hab ht)

/-- A bounded-speed actual integral curve is Lipschitz on its open time interval.
Its `C¹` regularity is derived from continuity of the actual vector field. -/
theorem IsMIntegralCurveOn.lipschitzOnWith_of_bounded
    {X : (x : M) → TangentSpace I x} {γ : ℝ → M} {a b : ℝ}
    (hγ : IsMIntegralCurveOn γ X (Ioo a b))
    (hX : Continuous (T% X)) {C : ℝ≥0}
    (hbound : ∀ t ∈ Ioo a b, ‖X (γ t)‖ₑ ≤ C) :
    LipschitzOnWith C γ (Ioo a b) := by
  have hone {u v : ℝ} (hu : u ∈ Ioo a b) (hv : v ∈ Ioo a b) (huv : u ≤ v) :
      edist (γ u) (γ v) ≤ C * edist u v := by
    rw [IsRiemannianManifold.out (I := I)]
    have hsub : Icc u v ⊆ Ioo a b := fun t ht ↦
      ⟨hu.1.trans_le ht.1, ht.2.trans_lt hv.2⟩
    calc
      _ ≤ pathELength I γ u v :=
        riemannianEDist_le_pathELength ((IsMIntegralCurveOn.contMDiffOn_one hX hγ isOpen_Ioo).mono
          hsub) rfl rfl huv
      _ ≤ C * ENNReal.ofReal (v - u) :=
        IsMIntegralCurveOn.pathELength_le hγ isOpen_Ioo hbound hsub
      _ = C * edist u v := by rw [edist_dist, Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr huv),
        neg_sub]
  intro u hu v hv
  rcases le_total u v with huv | hvu
  · exact hone hu hv huv
  · simpa [edist_comm] using hone hv hu hvu

/-- Completeness supplies a genuine finite right endpoint for every actual
bounded-speed integral curve; an endpoint is not supplied as a hypothesis. -/
theorem IsMIntegralCurveOn.exists_tendsto_right_endpoint [CompleteSpace M]
    {X : (x : M) → TangentSpace I x} {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : IsMIntegralCurveOn γ X (Ioo a b))
    (hX : Continuous (T% X)) {C : ℝ≥0}
    (hbound : ∀ t ∈ Ioo a b, ‖X (γ t)‖ₑ ≤ C) :
    ∃ x : M, Tendsto γ (𝓝[Ioo a b] b) (𝓝 x) := by
  have hne : NeBot (𝓝[Ioo a b] b) := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    simpa [closure_Ioo hab.ne] using (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
  have := hne
  apply cauchy_map_iff_exists_tendsto.mp
  apply (cauchy_nhds.mono nhdsWithin_le_nhds).map_of_le
    (IsMIntegralCurveOn.lipschitzOnWith_of_bounded hγ hX hbound).uniformContinuousOn
  exact inf_le_right

end CutoffRigidity
