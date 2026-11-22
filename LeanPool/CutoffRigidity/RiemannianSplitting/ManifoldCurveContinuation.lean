/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldUniformLocalFlow
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianIntegralCurveBounds
public import Mathlib.Geometry.Manifold.IntegralCurve.UniformTime
public import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-! # Complete Riemannian bounded fields cannot have a finite terminal time
The endpoint is obtained from genuine bounded speed and completeness. A locally
uniform coordinate Picard flow near that endpoint extends the actual curve,
using actual manifold ODE uniqueness to glue the overlap.
-/

@[expose] public section
open Bundle Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M]
  [IsManifold I 1 M] [BoundarylessManifold I M] [CompleteSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M]

/-- Every actual integral curve of bounded speed on a finite open interval
extends strictly beyond its right endpoint. -/
theorem exists_isMIntegralCurveOn_extension_right
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : IsMIntegralCurveOn γ X (Ioo a b)) {C : ℝ≥0}
    (hbound : ∀ t ∈ Ioo a b, ‖X (γ t)‖ₑ ≤ C) :
    ∃ c > b, ∃ γ' : ℝ → M,
      IsMIntegralCurveOn γ' X (Ioo a c) ∧ EqOn γ' γ (Ioo a b) := by
  classical
  obtain ⟨x, hlim⟩ := IsMIntegralCurveOn.exists_tendsto_right_endpoint
    hab hγ hX.continuous hbound
  obtain ⟨δ, hδ, hlocal⟩ := exists_eventually_isMIntegralCurveOn (hX.contMDiffAt (x := x))
  have hne : NeBot (𝓝[Ioo a b] b) := by
    rw [← mem_closure_iff_nhdsWithin_neBot]
    simpa [closure_Ioo hab.ne] using (show b ∈ Icc a b from ⟨hab.le, le_rfl⟩)
  have := hne
  have htime : ∀ᶠ t in 𝓝[Ioo a b] b, b - δ / 2 < t :=
    nhdsWithin_le_nhds (Ioi_mem_nhds (by linarith : b - δ / 2 < b))
  have hmem : ∀ᶠ t in 𝓝[Ioo a b] b, t ∈ Ioo a b := self_mem_nhdsWithin
  obtain ⟨t, ht, htnear, η, hηzero, hη⟩ :=
    (hmem.and (htime.and (hlim.eventually hlocal))).exists
  let ηt : ℝ → M := η ∘ (· - t)
  have hηt : IsMIntegralCurveOn ηt X (Ioo (t - δ) (t + δ)) := by
    rw [← isMIntegralCurveOn_comp_sub (dt := t)] at hη
    convert! hη using 1
    ext s
    simp only [Set.mem_Ioo]
    constructor <;> intro hs <;> constructor <;> linarith [hs.1, hs.2]
  have heq : γ t = ηt t := by simpa [ηt] using hηzero.symm
  let γ' := piecewise (Ioo a b) γ ηt
  refine ⟨t + δ, by linarith, γ', ?_, ?_⟩
  · apply (isMIntegralCurveOn_piecewise hX hγ hηt
      ⟨ht, ⟨by linarith, by linarith⟩⟩ heq).mono
    intro s hs
    by_cases hsb : s < b
    · exact Or.inl ⟨hs.1, hsb⟩
    · exact Or.inr ⟨by linarith [ht.2], hs.2⟩
  · exact piecewise_eqOn _ _ _

omit [CompleteSpace E] [IsManifold I 1 M] [BoundarylessManifold I M]
  [CompleteSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsRiemannianManifold I M] in
/-- Time reversal changes an actual integral curve into a curve of the negative
field on the reflected interval. -/
theorem IsMIntegralCurveOn.reflect
    {X : (x : M) → TangentSpace I x} {γ : ℝ → M} {a b : ℝ}
    (hγ : IsMIntegralCurveOn γ X (Ioo a b)) :
    IsMIntegralCurveOn (fun t ↦ γ (-t)) (-X) (Ioo (-b) (-a)) := by
  have h := hγ.comp_mul (-1)
  convert! h using 1
  · ext t; simp
  · ext x; simp
  · ext t
    simp only [Set.mem_Ioo, Set.mem_ofPred_eq, mul_neg_one]
    constructor <;> intro ht <;> constructor <;> linarith [ht.1, ht.2]

/-- Every finite left endpoint can likewise be extended. -/
theorem exists_isMIntegralCurveOn_extension_left
    {X : (x : M) → TangentSpace I x} (hX : ContMDiff I I.tangent 1 (T% X))
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : IsMIntegralCurveOn γ X (Ioo a b)) {C : ℝ≥0}
    (hbound : ∀ t ∈ Ioo a b, ‖X (γ t)‖ₑ ≤ C) :
    ∃ c < a, ∃ γ' : ℝ → M,
      IsMIntegralCurveOn γ' X (Ioo c b) ∧ EqOn γ' γ (Ioo a b) := by
  have hneg : ContMDiff I I.tangent 1 (T% (-X)) := hX.neg_section
  have hb : ∀ t ∈ Ioo (-b) (-a), ‖(-X) (γ (-t))‖ₑ ≤ C := by
    intro t ht
    simpa using hbound (-t) ⟨by linarith [ht.2], by linarith [ht.1]⟩
  obtain ⟨c, hc, Γ, hΓ, heq⟩ := exists_isMIntegralCurveOn_extension_right
    hneg (neg_lt_neg hab) (IsMIntegralCurveOn.reflect hγ) hb
  refine ⟨-c, by linarith, fun t ↦ Γ (-t), ?_, ?_⟩
  · convert! IsMIntegralCurveOn.reflect hΓ using 1 <;> simp
  · intro t ht
    have htn : -t ∈ Ioo (-b) (-a) := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    simpa using heq htn

end CutoffRigidity
