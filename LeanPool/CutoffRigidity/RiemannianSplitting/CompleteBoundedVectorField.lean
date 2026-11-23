/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianIntegralCurveBounds
import TauCeti.Geometry.Manifold.IntegralCurve.Maximal

/-! # Global integral curves of bounded fields on complete Riemannian manifolds
This proves the completeness step used in the splitting proof: a bounded C¹
field on a complete boundaryless Riemannian manifold has global integral curves.
Bounded speed gives a limit at any finite endpoint, so the maximal-curve
escape criterion forces the interval to extend in both directions.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 2 M] [BoundarylessManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- Completeness and actual bounded speed imply global existence, with no
assumed global flow or assumed continuation property. -/
theorem exists_global_integralCurve_of_bounded
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    {C : ℝ≥0} (hbound : ∀ x, ‖X x‖ₑ ≤ C) (x₀ : M) :
    ∃ γ : ℝ → M, γ 0 = x₀ ∧ IsMIntegralCurve γ X := by
  let interval := maximalIntegralCurveInterval X x₀
  let curve := maximalIntegralCurve X x₀
  have hcurve : IsMIntegralCurveOn curve X interval := isMIntegralCurveOn_maximalIntegralCurve hX
  have hnonempty : interval.Nonempty := ⟨0, zero_mem_maximalIntegralCurveInterval hX.contMDiffAt⟩
  have hlimit {a b t : ℝ} (hsub : Ioo a b ⊆ interval) (hne : NeBot (𝓝[Ioo a b] t)) :
      ∃ y : M, Tendsto curve (𝓝[Ioo a b] t) (𝓝 y) := by
    exact IsMIntegralCurveOn.exists_tendsto_of_bounded (hcurve.mono hsub)
      hX.continuous (fun s _ ↦ hbound (curve s)) hne
  have hupper : ¬ BddAbove interval := by
    intro hboundAbove
    have hsup := isLUB_csSup hnonempty hboundAbove
    obtain ⟨a, ha, hpos, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isLUB hsup
    have hle : 𝓝[<] sSup interval ≤ 𝓝[Ioo a (sSup interval)] (sSup interval) :=
      le_inf nhdsWithin_le_nhds (le_principal_iff.mpr (Ioo_mem_nhdsLT (ha.trans hpos)))
    obtain ⟨y, hy⟩ := hlimit hsub ((nhdsLT_neBot (sSup interval)).mono hle)
    exact not_mapClusterPt_nhdsLT_maximalIntegralCurve hX hsup y (hy.mono_left hle).mapClusterPt
  have hlower : ¬ BddBelow interval := by
    intro hboundBelow
    have hinf := isGLB_csInf hnonempty hboundBelow
    obtain ⟨b, hb, hneg, hsub⟩ := exists_Ioo_subset_maximalIntegralCurveInterval_of_isGLB hinf
    have hle : 𝓝[>] sInf interval ≤ 𝓝[Ioo (sInf interval) b] (sInf interval) :=
      le_inf nhdsWithin_le_nhds (le_principal_iff.mpr (Ioo_mem_nhdsGT (hneg.trans hb)))
    obtain ⟨y, hy⟩ := hlimit hsub ((nhdsGT_neBot (sInf interval)).mono hle)
    exact not_mapClusterPt_nhdsGT_maximalIntegralCurve hX hinf y (hy.mono_left hle).mapClusterPt
  exact (maximalIntegralCurveInterval_eq_univ_iff hX).mp
    (maximalIntegralCurveInterval_eq_univ_of_not_bddAbove_not_bddBelow hupper hlower)

end CutoffRigidity
