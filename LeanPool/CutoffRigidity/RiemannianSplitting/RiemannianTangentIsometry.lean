/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Topology.MetricSpace.Isometry

/-! # Actual tangent norm preservation implies actual Riemannian distance control
C¹ paths are mapped to C¹ paths. The actual derivative chain rule preserves
their genuine lengths, and the genuine path-length definition controls distance.
-/

@[expose] public section
open Bundle Set Filter MeasureTheory Manifold
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)] [IsRiemannianManifold I M]

omit [IsManifold I 1 M] [IsRiemannianManifold I M] in
/-- A genuine tangent-norm-preserving C¹ map preserves the actual length of
every actual C¹ path. -/
theorem pathELength_comp_eq_of_norm_mfderiv_eq
    {φ : M → M} (hφ : ContMDiff I I 1 φ)
    (hNorm : ∀ x (v : TangentSpace I x), ‖(mfderiv I I φ x) v‖ = ‖v‖)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    pathELength I (φ ∘ γ) a b = pathELength I γ a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [mfderiv_comp t ((hφ.mdifferentiable one_ne_zero) _) ((hγ.mdifferentiable one_ne_zero) _)]
  change ‖(mfderiv I I φ (γ t)) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)‖ₑ =
    ‖(mfderiv 𝓘(ℝ, ℝ) I γ t) 1‖ₑ
  change (‖(mfderiv I I φ (γ t)) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)‖₊ : ℝ≥0∞) =
    (‖(mfderiv 𝓘(ℝ, ℝ) I γ t) 1‖₊ : ℝ≥0∞)
  apply congrArg ((↑) : ℝ≥0 → ℝ≥0∞)
  exact NNReal.eq (hNorm (γ t) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1))

omit [IsManifold I 1 M] in
/-- Actual tangent-norm-preserving C¹ maps cannot increase the actual
Riemannian distance; this is derived from actual C¹ path lengths. -/
theorem edist_le_of_norm_mfderiv_eq
    {φ : M → M} (hφ : ContMDiff I I 1 φ)
    (hNorm : ∀ x (v : TangentSpace I x), ‖(mfderiv I I φ x) v‖ = ‖v‖)
    (x y : M) : edist (φ x) (φ y) ≤ edist x y := by
  simp only [IsRiemannianManifold.out (I := I)]
  by_contra! hlt
  obtain ⟨γ, hγx, hγy, hγ, hlen, _, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hlt zero_lt_one
  have hle : riemannianEDist I (φ x) (φ y) ≤ pathELength I (φ ∘ γ) 0 1 := by
    apply riemannianEDist_le_pathELength (hφ.comp hγ).contMDiffOn
      (by simp only [Function.comp_apply, hγx]) (by simp only [Function.comp_apply, hγy])
        zero_le_one
  rw [pathELength_comp_eq_of_norm_mfderiv_eq hφ hNorm hγ] at hle
  exact (not_lt_of_ge hle) hlen

end CutoffRigidity
