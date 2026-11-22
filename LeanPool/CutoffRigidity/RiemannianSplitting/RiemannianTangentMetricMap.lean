/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Topology.MetricSpace.Isometry
public import Mathlib.Geometry.Manifold.Diffeomorph

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
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [EMetricSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsRiemannianManifold J N]

omit [IsManifold I 1 M] [IsRiemannianManifold I M] [IsManifold J 1 N] [IsRiemannianManifold J N] in
/-- A genuine tangent-norm-preserving C¹ map preserves the actual length of
every actual C¹ path. -/
theorem pathELength_comp_eq_of_norm_mfderiv_eq_between
    {φ : M → N} (hφ : ContMDiff I J 1 φ)
    (hNorm : ∀ x (v : TangentSpace I x), ‖(mfderiv I J φ x) v‖ = ‖v‖)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    pathELength J (φ ∘ γ) a b = pathELength I γ a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc]
  apply setLIntegral_congr_fun measurableSet_Icc
  intro t ht
  dsimp only
  rw [mfderiv_comp t ((hφ.mdifferentiable one_ne_zero) _) ((hγ.mdifferentiable one_ne_zero) _)]
  change ‖(mfderiv I J φ (γ t)) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)‖ₑ =
    ‖(mfderiv 𝓘(ℝ, ℝ) I γ t) 1‖ₑ
  change (‖(mfderiv I J φ (γ t)) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)‖₊ : ℝ≥0∞) =
    (‖(mfderiv 𝓘(ℝ, ℝ) I γ t) 1‖₊ : ℝ≥0∞)
  apply congrArg ((↑) : ℝ≥0 → ℝ≥0∞)
  exact NNReal.eq (hNorm (γ t) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1))

omit [IsManifold I 1 M] [IsManifold J 1 N] in
/-- Actual tangent-norm-preserving C¹ maps cannot increase the actual
Riemannian distance; this is derived from actual C¹ path lengths. -/
theorem edist_le_of_norm_mfderiv_eq_between
    {φ : M → N} (hφ : ContMDiff I J 1 φ)
    (hNorm : ∀ x (v : TangentSpace I x), ‖(mfderiv I J φ x) v‖ = ‖v‖)
    (x y : M) : edist (φ x) (φ y) ≤ edist x y := by
  simp only [IsRiemannianManifold.out (I := I),IsRiemannianManifold.out (I := J)]
  by_contra! hlt
  obtain ⟨γ, hγx, hγy, hγ, hlen, _, _⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hlt zero_lt_one
  have hle : riemannianEDist J (φ x) (φ y) ≤ pathELength J (φ ∘ γ) 0 1 := by
    apply riemannianEDist_le_pathELength (hφ.comp hγ).contMDiffOn
      (by simp only [Function.comp_apply, hγx]) (by simp only [Function.comp_apply, hγy])
        zero_le_one
  rw [pathELength_comp_eq_of_norm_mfderiv_eq_between hφ hNorm hγ] at hle
  exact (not_lt_of_ge hle) hlen

omit [IsManifold I 1 M] [IsManifold J 1 N]
  [IsRiemannianManifold I M] [IsRiemannianManifold J N] in
theorem pathELength_comp_le_of_norm_mfderiv_le_between
    {φ : M → N} (hφ : ContMDiff I J 1 φ)
    (hNorm : ∀ x (v : TangentSpace I x), ‖(mfderiv I J φ x) v‖ ≤ ‖v‖)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) I 1 γ) (a b : ℝ) :
    pathELength J (φ ∘ γ) a b ≤ pathELength I γ a b := by
  rw [pathELength_eq_lintegral_mfderiv_Icc, pathELength_eq_lintegral_mfderiv_Icc]
  apply lintegral_mono
  intro t
  dsimp only
  rw [mfderiv_comp t ((hφ.mdifferentiable one_ne_zero) _) ((hγ.mdifferentiable one_ne_zero) _)]
  change ‖(mfderiv I J φ (γ t)) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)‖ₑ ≤
    ‖(mfderiv 𝓘(ℝ, ℝ) I γ t) 1‖ₑ
  change (‖(mfderiv I J φ (γ t)) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)‖₊ : ℝ≥0∞) ≤
    (‖(mfderiv 𝓘(ℝ, ℝ) I γ t) 1‖₊ : ℝ≥0∞)
  exact_mod_cast hNorm (γ t) ((mfderiv 𝓘(ℝ, ℝ) I γ t) 1)



omit [IsManifold I 1 M] [IsManifold J 1 N] [IsRiemannianManifold J N] in
/-- A C¹ tangent contraction controls the target's genuine intrinsic
Riemannian distance even before a target distance instance is identified. -/
theorem riemannianEDist_le_edist_of_norm_mfderiv_le_between
    {φ : M → N} (hφ : ContMDiff I J 1 φ)
    (hNorm : ∀ x (v : TangentSpace I x), ‖(mfderiv I J φ x) v‖ ≤ ‖v‖)
    (x y : M) : riemannianEDist J (φ x) (φ y) ≤ edist x y := by
  rw [IsRiemannianManifold.out (I := I)]
  by_contra! hlt
  obtain ⟨γ,hγx,hγy,hγ,hlen,_,_⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hlt zero_lt_one
  have hle : riemannianEDist J (φ x) (φ y) ≤ pathELength J (φ ∘ γ) 0 1 := by
    apply riemannianEDist_le_pathELength (hφ.comp hγ).contMDiffOn
      (by simp only [Function.comp_apply,hγx]) (by simp only [Function.comp_apply,hγy]) zero_le_one
  have hh := pathELength_comp_le_of_norm_mfderiv_le_between hφ hNorm hγ (0:ℝ) 1
  exact (not_lt_of_ge (hle.trans hh)) hlen

omit [IsManifold I 1 M] [IsManifold J 1 N] in
/-- A genuine C¹ diffeomorphism preserving actual tangent norms is an
isometry for the actual Riemannian distances. -/
theorem isometry_diffeomorph_of_norm_mfderiv_eq_between
    (e : Diffeomorph I J M N 1)
    (hNorm : ∀ x (v : TangentSpace I x), ‖(mfderiv I J e x) v‖ = ‖v‖) : Isometry e := by
  have hInv (y : N) (v : TangentSpace J y) : ‖(mfderiv J I e.symm y) v‖ = ‖v‖ := by
    have hh : mfderiv J J ((e : M → N) ∘ (e.symm : N → M)) y =
        (mfderiv I J e (e.symm y)).comp (mfderiv J I e.symm y) := by
      convert! mfderiv_comp y ((e.contMDiff_toFun.mdifferentiable one_ne_zero) _)
        ((e.contMDiff_invFun.mdifferentiable one_ne_zero) _) using 1
    have he : ((e : M → N) ∘ (e.symm : N → M)) = id := by funext z; exact e.apply_symm_apply z
    rw [he,mfderiv_id] at hh
    have hv := congrArg (fun A => A v) hh
    have hn := hNorm (e.symm y) ((mfderiv J I e.symm y) v)
    have hCan : (mfderiv I J e (e.symm y)) ((mfderiv J I e.symm y) v) = v := by
      convert! hv.symm using 1
    rw [hCan] at hn
    have hBase := congrArg (fun z : N =>
      @norm (TangentSpace J z)
        (instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
          z).toNorm v)
      (e.apply_symm_apply y)
    exact hn.symm.trans hBase
  intro x y
  apply le_antisymm
  · exact edist_le_of_norm_mfderiv_eq_between e.contMDiff_toFun hNorm x y
  · have hh := edist_le_of_norm_mfderiv_eq_between e.contMDiff_invFun hInv (e x) (e y)
    convert! hh using 1; simp


omit [IsManifold I 1 M]
  [IsManifold J 1 N]
  [IsRiemannianManifold I M]
  [IsRiemannianManifold J N] in
theorem riemannianEDist_le_riemannianEDist_of_norm_mfderiv_le_between
    {φ : M → N} (hφ : ContMDiff I J 1 φ)
    (hNorm : ∀ x (v : TangentSpace I x), ‖(mfderiv I J φ x) v‖ ≤ ‖v‖)
    (x y : M) : riemannianEDist J (φ x) (φ y) ≤ riemannianEDist I x y := by
  by_contra! hlt
  obtain ⟨γ,hγx,hγy,hγ,hlen,_,_⟩ :=
    exists_lt_locally_constant_of_riemannianEDist_lt hlt zero_lt_one
  have hle : riemannianEDist J (φ x) (φ y) ≤ pathELength J (φ ∘ γ) 0 1 := by
    apply riemannianEDist_le_pathELength (hφ.comp hγ).contMDiffOn
      (by simp only [Function.comp_apply,hγx]) (by simp only [Function.comp_apply,hγy]) zero_le_one
  have hh := pathELength_comp_le_of_norm_mfderiv_le_between hφ hNorm hγ (0:ℝ) 1
  exact (not_lt_of_ge (hle.trans hh)) hlen


end CutoffRigidity
