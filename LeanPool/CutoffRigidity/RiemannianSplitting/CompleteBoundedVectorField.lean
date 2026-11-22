/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldCurveContinuation
public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldCurveGluing

/-! # Global integral curves of bounded fields on complete Riemannian manifolds
This proves the completeness step used in the splitting proof: a bounded C¹
field on a complete boundaryless Riemannian manifold has global integral curves.
The proof glues all local lifetimes, derives both finite endpoints from actual
Riemannian speed estimates, and extends using actual coordinate Picard flows.
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
  classical
  let A : Set ℝ := {r | 0 < r ∧ ∃ γ : ℝ → M,
    γ 0 = x₀ ∧ IsMIntegralCurveOn γ X (Ioo (-r) r)}
  obtain ⟨ε, hε, hlocal⟩ := exists_eventually_isMIntegralCurveOn
    (hX.contMDiffAt (x := x₀))
  have hεA : ε ∈ A := ⟨hε, hlocal.self_of_nhds⟩
  have hAne : A.Nonempty := ⟨ε, hεA⟩
  have hUnbounded : ¬ BddAbove A := by
    intro hbdd
    let T := sSup A
    have hT : 0 < T := hε.trans_le (le_csSup hbdd hεA)
    have hcurves (r : A) : ∃ γ : ℝ → M,
        γ 0 = x₀ ∧ IsMIntegralCurveOn γ X (Ioo (-r.val) r.val) := r.property.2
    choose γ hzero hγ using hcurves
    have : Nonempty A := ⟨⟨ε, hεA⟩⟩
    obtain ⟨Γ, hΓzero, hΓ, _⟩ := exists_isMIntegralCurveOn_iUnion
      hX (fun r : A ↦ r.val) (fun r ↦ r.property.1) γ hzero hγ
    have hU : (⋃ r : A, Ioo (-r.val) r.val) = Ioo (-T) T := by
      ext t
      constructor
      · intro ht
        obtain ⟨r, hr⟩ := mem_iUnion.mp ht
        have hrT : r.val ≤ T := le_csSup hbdd r.property
        exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
      · intro ht
        have habs : |t| < T := abs_lt.mpr ht
        obtain ⟨r, hrA, htr⟩ := exists_lt_of_lt_csSup hAne habs
        exact mem_iUnion.mpr ⟨⟨r, hrA⟩, abs_lt.mp htr⟩
    rw [hU] at hΓ
    obtain ⟨c, hc, Γ₁, hΓ₁, heq₁⟩ := exists_isMIntegralCurveOn_extension_right
      hX (by linarith : -T < T) hΓ (fun t _ ↦ hbound (Γ t))
    obtain ⟨d, hd, Γ₂, hΓ₂, heq₂⟩ := exists_isMIntegralCurveOn_extension_left
      hX (by linarith : -T < c) hΓ₁ (fun t _ ↦ hbound (Γ₁ t))
    let r := min c (-d)
    have hrT : T < r := lt_min hc (by linarith)
    have hrA : r ∈ A := by
      refine ⟨hT.trans hrT, Γ₂, ?_, ?_⟩
      · calc
          Γ₂ 0 = Γ₁ 0 := heq₂ ⟨by linarith, by linarith⟩
          _ = Γ 0 := heq₁ ⟨by linarith, hT⟩
          _ = x₀ := hΓzero
      · apply hΓ₂.mono
        intro t ht
        have hrc : r ≤ c := min_le_left _ _
        have hrd : r ≤ -d := min_le_right _ _
        exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    exact (not_lt_of_ge (le_csSup hbdd hrA)) hrT
  apply (exists_isMIntegralCurve_iff_exists_isMIntegralCurveOn_Ioo hX x₀).mpr
  intro a
  obtain ⟨r, hrA, har⟩ := not_bddAbove_iff.mp hUnbounded a
  obtain ⟨γ, hzero, hγ⟩ := hrA.2
  exact ⟨γ, hzero, hγ.mono (Ioo_subset_Ioo (neg_le_neg har.le) har.le)⟩

end CutoffRigidity
