/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitFrame
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.EigenFinite
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianParallelPairing

/-! # From the orthonormal eigenbasis to an orthonormal parallel frame

At curvature equality, weighted integration by parts identifies the gradient pairing
of `L²`-orthonormal eigenfunctions as `ρ` times their `L²` pairing. Scaling the basis by
`1 / √ρ` gives a parallel orthonormal frame.
-/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal

namespace CutCur

section EigenFrame

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

variable {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsProbabilityMeasure μ]
  (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ) (hCD : CD F ρ V)
  (hgap : mSpectralGap F μ = ρ)

include hV hμ hρ hCD hgap in
/-- **Frame from the eigenbasis**: a frame `s` of size `k₁ = mFirstEigenDim` of eigenfunctions
such that every eigenfunction is a linear combination of the `sᵢ`. -/
theorem exists_frame_of_eigen :
    ∃ fr : Frame F M (mFirstEigenDim F μ V),
      (∀ i, IsMEigenfunction F μ V ρ (fr.s i)) ∧
      (∀ i j, ∫ x, (Real.sqrt ρ * fr.s i x) * (Real.sqrt ρ * fr.s j x) ∂μ =
        if i = j then 1 else 0) ∧
      ∀ f, IsMEigenfunction F μ V ρ f →
        ∃ c : Fin (mFirstEigenDim F μ V) → ℝ, ∀ x, f x = ∑ i, c i * fr.s i x := by
  classical
  have : Nonempty M := inferInstance
  have := isOpenPosMeasure_of_weighted F hV hμ
  obtain ⟨b, T, hT, hTb, hTo⟩ :=
    exists_orthonormal_eigenbasis_with_representatives F hV hμ hρ hCD hgap
  have hpar : ∀ f, IsMEigenfunction F μ V ρ f → ∀ x,
      CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x = 0 :=
    fun f hf x => manifold_eigenfunction_parallel_gradient F hV hμ hρ hCD hgap hf x
  have hTs : ∀ i, MSmooth F (T i) := fun i => (hT i).1
  generalize hK : mFirstEigenDim F μ V = K at b T hT hTb hTo hTs ⊢
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  have hX1 : ∀ i, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent 1 (T% (mgrad F (T i))) := fun i =>
    (WReg.contMDiff_mgrad (hTs i)).of_le (by simp)
  have hconstant i j x : carre F (T i) (T j) x = carre F (T i) (T j) x₀ :=
    CutoffRigidity.inner_parallel_eq_of_preconnected (hX1 i) (hX1 j)
      (hpar _ (hT i)) (hpar _ (hT j)) x x₀
  have hbound j x : ‖mgrad F (T j) x‖ ≤ ‖mgrad F (T j) x₀‖ := by
    rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner]
    exact (congrArg Real.sqrt (hconstant j j x)).le
  let : SigmaCompactSpace M := sigmaCompactSpace_of_complete_riemannian (F := F) (M := M)
  have hpairing i j x : carre F (T i) (T j) x = ρ * (if i = j then 1 else 0) := by
    rw [hconstant i j x, constant_carre_eq_eigenfunction_pairing F (norm_nonneg _)
      (weightedIBP_of_isWeightedVolume_of_sigmaCompact F hV hμ) (weightedRegular V hV)
      (weightedCutoffs_of_complete F) (hT i) (hT j) (hconstant i j) (hbound j), hTo i j]
  let s : Fin K → M → ℝ := fun i x => (Real.sqrt ρ)⁻¹ * T i x
  have hs : ∀ i, IsMEigenfunction F μ V ρ (s i) :=
    fun i => (eigenSub F μ V ρ).smul_mem ((Real.sqrt ρ)⁻¹) (hT i)
  have hsquare : (Real.sqrt ρ)⁻¹ ^ 2 * ρ = 1 := by
    rw [inv_pow, Real.sq_sqrt hρ.le, inv_mul_cancel₀ hρ.ne']
  have hgram : ∀ i j x, carre F (s i) (s j) x = if i = j then 1 else 0 := by
    intro i j x
    change inner ℝ (mgrad F (s i) x) (mgrad F (s j) x) = _
    simp only [s, mgrad_const_mul F,
      real_inner_smul_left, real_inner_smul_right]
    change (Real.sqrt ρ)⁻¹ * ((Real.sqrt ρ)⁻¹ * carre F (T i) (T j) x) = _
    rw [hpairing]
    calc _ = ((Real.sqrt ρ)⁻¹ ^ 2 * ρ) * (if i = j then 1 else 0) := by ring
      _ = _ := by rw [hsquare, one_mul]
  let fr : Frame F M K :=
    { s := s
      smooth := fun i => (hs i).1
      parallel := fun i x => hpar _ (hs i) x
      gram := hgram }
  have hn i x : Real.sqrt ρ * fr.s i x = T i x := by
    change Real.sqrt ρ * ((Real.sqrt ρ)⁻¹ * T i x) = _
    rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_pos.mpr hρ).ne', one_mul]
  refine ⟨fr, hs, fun i j => ?_, fun f hf => ?_⟩
  · simp_rw [hn]
    exact hTo i j
  let u : eigenClasses F μ V ρ :=
    ⟨hf.2.1.toLp f, f, hf, (MemLp.coeFn_toLp hf.2.1).symm⟩
  let c : Fin K → ℝ := fun i => b.repr u i
  have hfu : f =ᵐ[μ] (u : M →₂[μ] ℝ) := (MemLp.coeFn_toLp hf.2.1).symm
  have e1 : ∀ x, f x = ∑ i, c i * T i x := by
    have hsum : ∑ i, c i • (b i : M →₂[μ] ℝ) = (u : M →₂[μ] ℝ) := by
      change ∑ i, b.repr u i • (eigenClasses F μ V ρ).subtype (b i) =
        (eigenClasses F μ V ρ).subtype u
      simpa only [map_sum, map_smul] using congrArg (eigenClasses F μ V ρ).subtype (b.sum_repr u)
    refine congrFun ((hf.1.continuous.ae_eq_iff_eq μ (continuous_finsetSum _ fun i _ =>
      continuous_const.mul (hTs i).continuous)).mp ?_)
    refine hfu.trans ?_
    rw [← hsum]
    refine (Lp.coeFn_fun_finsetSum _ _).trans ?_
    have hterm (i : Fin K) : ⇑(c i • (b i : M →₂[μ] ℝ)) =ᵐ[μ]
        fun x => c i * T i x := by
      refine (Lp.coeFn_smul _ _).trans ?_
      filter_upwards [hTb i] with x hx
      simp only [Pi.smul_apply, smul_eq_mul, hx]
    filter_upwards [ae_all_iff.2 hterm] with x hx
    exact Finset.sum_congr rfl fun i _ => hx i
  refine ⟨fun i => c i * Real.sqrt ρ, fun x => ?_⟩
  rw [e1 x]
  exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, hn]

end EigenFrame

end CutCur
