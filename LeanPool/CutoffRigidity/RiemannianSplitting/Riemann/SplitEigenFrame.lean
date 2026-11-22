/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitFrame
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.EigenFinite
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.SplitEigen
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianParallelFlow
import Mathlib.Analysis.Matrix.Order

/-! # From the orthonormal eigenbasis to an orthonormal parallel frame

Under the hypotheses of `riemannian_gaussian_splitting`, the `L²`-orthonormal eigenbasis `T` of `E₁`
has parallel gradients (workstream A), constant positive definite Gram matrix `G = (Γ(Tᵢ,Tⱼ))`, and
`s = A T` with `A G Aᵀ = 1` is an orthonormal parallel frame.
-/

@[expose] public section

open Bundle MeasureTheory Set
open scoped Manifold ContDiff ENNReal Matrix

namespace CutCur

open Matrix in
open scoped MatrixOrder in
theorem exists_orthonormalizer {k : ℕ} (G : Matrix (Fin k) (Fin k) ℝ) (hsymm : Gᵀ = G)
    (hpos : ∀ x : Fin k → ℝ, x ≠ 0 → 0 < x ⬝ᵥ (G *ᵥ x)) :
    ∃ A B : Matrix (Fin k) (Fin k) ℝ, A * G * Aᵀ = 1 ∧ A * B = 1 ∧ B * A = 1 := by
  have hsd : G.PosSemidef := by
    refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
    · have : Gᴴ = G := by rw [conjTranspose_eq_transpose_of_trivial]; exact hsymm
      exact this
    · intro x
      by_cases hx : x = 0
      · simp [hx]
      · simpa using (hpos x hx).le
  have hdet : G.det ≠ 0 := by
    intro h
    obtain ⟨v, hv, hGv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h
    have := hpos v hv
    rw [hGv] at this
    simp at this
  set R := CFC.sqrt G with hR
  have hnn : 0 ≤ G := by
    exact Matrix.nonneg_iff_posSemidef.mpr hsd
  have hRR : R * R = G := CFC.sqrt_mul_sqrt_self G hnn
  have hRT : Rᵀ = R := by
    have : IsSelfAdjoint R := (CFC.sqrt_nonneg G).isSelfAdjoint
    simpa [IsSelfAdjoint, star, conjTranspose] using this
  have hdR : IsUnit R.det := by
    have : R.det * R.det = G.det := by rw [← det_mul, hRR]
    refine isUnit_iff_ne_zero.mpr fun h => hdet ?_
    rw [← this, h]; ring
  refine ⟨R⁻¹, R, ?_, nonsing_inv_mul R hdR, mul_nonsing_inv R hdR⟩
  rw [transpose_nonsing_inv, hRT, ← hRR]
  calc R⁻¹ * (R * R) * R⁻¹ = (R⁻¹ * R) * (R * R⁻¹) := by simp [Matrix.mul_assoc]
    _ = 1 := by rw [nonsing_inv_mul R hdR, mul_nonsing_inv R hdR, Matrix.one_mul]

section EigenFrame

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M]
  [MeasurableSpace M] [BorelSpace M]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [MeasurableSpace F]
  [BorelSpace F]
  [IsRiemannianManifold 𝓘(ℝ, F) M]
  [ConnectedSpace M]
  [CompleteSpace M]
  [MeasurableSpace M]
  [BorelSpace M] in
/-- The gradient of a linear combination of smooth functions. -/
theorem mgrad_lincomb {ι : Type*} (T : ι → M → ℝ) (hT : ∀ i, MSmooth F (T i)) (c : ι → ℝ)
    (s : Finset ι) (x : M) :
    mgrad F (fun y => ∑ j ∈ s, c j * T j y) x = ∑ j ∈ s, c j • mgrad F (T j) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact mgrad_const F 0 x
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    have h1 : MSmooth F (fun y => c a * T a y) := contMDiff_const.mul (hT a)
    have h2 : MSmooth F (fun y => ∑ j ∈ s, c j * T j y) :=
      ContMDiff.sum fun j _ => contMDiff_const.mul (hT j)
    rw [mgrad_add' F h1 h2, mgrad_const_mul F (c a) (hT a), ih]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [MeasurableSpace F]
  [BorelSpace F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [IsRiemannianManifold 𝓘(ℝ, F) M]
  [ConnectedSpace M]
  [CompleteSpace M]
  [MeasurableSpace M]
  [BorelSpace M] in
theorem smooth_lincomb {ι : Type*} (T : ι → M → ℝ) (hT : ∀ i, MSmooth F (T i)) (c : ι → ℝ)
    (s : Finset ι) : MSmooth F (fun y => ∑ j ∈ s, c j * T j y) :=
  ContMDiff.sum fun j _ => contMDiff_const.mul (hT j)

variable {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsProbabilityMeasure μ]
  (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ) (hCD : CD F ρ V)
  (hgap : mSpectralGap F μ = ρ)

include hV hμ in
omit [IsRiemannianManifold 𝓘(ℝ, F) M]
  [ConnectedSpace M]
  [CompleteSpace M]
  [IsProbabilityMeasure μ] in
/-- `μ` charges nonempty open sets. -/
theorem isOpenPosMeasure_of_weighted : μ.IsOpenPosMeasure :=
  ⟨fun _U hU hne => (measure_pos_of_isWeightedVolume F hV hμ (continuousOn_chartVolumeDensity F)
    (fun x₀ _z hz => chartVolumeDensity_pos F x₀ hz) hU hne).ne'⟩

include hV hμ hρ hCD hgap in
/-- **Frame from the eigenbasis**: a frame `s` of size `k₁ = mFirstEigenDim` of eigenfunctions
such that every eigenfunction is a linear combination of the `sᵢ`. -/
theorem exists_frame_of_eigen :
    ∃ fr : Frame F M (mFirstEigenDim F μ V),
      (∀ i, IsMEigenfunction F μ V ρ (fr.s i)) ∧
      ∀ f, IsMEigenfunction F μ V ρ f →
        ∃ c : Fin (mFirstEigenDim F μ V) → ℝ, ∀ x, f x = ∑ i, c i * fr.s i x := by
  classical
  have : Nonempty M := inferInstance
  have := isOpenPosMeasure_of_weighted F hV hμ
  obtain ⟨T, hT, hTo⟩ := exists_orthonormal_eigenbasis F hV hμ hρ hCD hgap
  have hpar : ∀ f, IsMEigenfunction F μ V ρ f → ∀ x,
      CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x = 0 :=
    fun f hf x => manifold_eigenfunction_parallel_gradient F hV hμ hρ hCD hgap hf x
  have hTs : ∀ i, MSmooth F (T i) := fun i => (hT i).1
  -- linear combinations of the basis are eigenfunctions
  have hcomb : ∀ c : Fin (mFirstEigenDim F μ V) → ℝ, IsMEigenfunction F μ V ρ (fun y => ∑ j, c j *
      T j y) := by
    intro c
    have : (fun y => ∑ j, c j * T j y) ∈ eigenSub F μ V ρ := by
      have h := Submodule.sum_mem (eigenSub F μ V ρ) (t := Finset.univ)
        (f := fun j => c j • T j) (fun j _ => (eigenSub F μ V ρ).smul_mem (c j) (hT j))
      convert h using 1
      funext y
      simp
    exact this
  have hmem : ∀ i, MemLp (T i) 2 μ := fun i => (hT i).2.1
  generalize hK : mFirstEigenDim F μ V = K at T hT hTo hTs hcomb hmem ⊢
  obtain ⟨x₀⟩ := (inferInstance : Nonempty M)
  set G : Matrix (Fin K) (Fin K) ℝ := fun i j => carre F (T i) (T j) x₀ with hG
  have hX1 : ∀ i, ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent 1 (T% (mgrad F (T i))) := fun i =>
    (WReg.contMDiff_mgrad (hTs i)).of_le (by simp)
  have hGconst : ∀ i j x, carre F (T i) (T j) x = G i j := fun i j x =>
    CutoffRigidity.inner_parallel_eq_of_preconnected (hX1 i) (hX1 j)
      (hpar _ (hT i)) (hpar _ (hT j)) x x₀
  have hGsymm : Gᵀ = G := by
    ext i j
    change inner ℝ (mgrad F (T j) x₀) (mgrad F (T i) x₀) = _
    exact real_inner_comm _ _
  -- the quadratic form is the squared norm of the gradient of a combination
  have hquad : ∀ a : Fin K → ℝ, a ⬝ᵥ (G *ᵥ a) =
      ‖mgrad F (fun y => ∑ j, a j * T j y) x₀‖ ^ 2 := by
    intro a
    rw [← real_inner_self_eq_norm_sq, mgrad_lincomb F T hTs a Finset.univ x₀]
    simp only [inner_sum, sum_inner, real_inner_smul_left, real_inner_smul_right]
    simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hG]
    simp only [carre]
    rw [real_inner_comm (mgrad F (T i) x₀) (mgrad F (T j) x₀)]
    ring
  have hGpos : ∀ a : Fin K → ℝ, a ≠ 0 → 0 < a ⬝ᵥ (G *ᵥ a) := by
    intro a ha
    rw [hquad]
    refine lt_of_le_of_ne (sq_nonneg _) fun h0 => ha ?_
    have h1 : mgrad F (fun y => ∑ j, a j * T j y) x₀ = 0 :=
      norm_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h0.symm)
    have h2 : (fun y => ∑ j, a j * T j y) = 0 :=
      eigenfunction_eq_zero_of_grad_zero F hρ.ne' (hcomb a) (hpar _ (hcomb a)) x₀ h1
    funext j
    have h3 := CutoffRigidity.Riemann.integral_sum_mul_orthonormal T hmem hTo a j
    have h4 : ∀ y, (∑ i, a i * T i y) = 0 := fun y => congrFun h2 y
    simp only [h4, zero_mul, integral_zero] at h3
    simpa using h3.symm
  obtain ⟨A, B, hAGA, hAB, hBA⟩ := exists_orthonormalizer G hGsymm hGpos
  let s : Fin K → M → ℝ := fun i x => ∑ j, A i j * T j x
  have hs : ∀ i, IsMEigenfunction F μ V ρ (s i) := fun i => hcomb (A i)
  have hgram : ∀ i j x, carre F (s i) (s j) x = if i = j then 1 else 0 := by
    intro i j x
    change inner ℝ (mgrad F (s i) x) (mgrad F (s j) x) = _
    have e1 : mgrad F (s i) x = ∑ a, A i a • mgrad F (T a) x :=
      mgrad_lincomb F T hTs (A i) Finset.univ x
    have e2 : mgrad F (s j) x = ∑ b, A j b • mgrad F (T b) x :=
      mgrad_lincomb F T hTs (A j) Finset.univ x
    rw [e1, e2]
    simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
    have h1 := congrFun (congrFun hAGA i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at h1
    rw [← h1]
    simp only [Finset.sum_mul]
    refine Finset.sum_congr rfl fun x1 _ => Finset.sum_congr rfl fun x2 _ => ?_
    have : inner ℝ (mgrad F (T x2) x) (mgrad F (T x1) x) = G x2 x1 := hGconst x2 x1 x
    rw [this]
    ring
  let fr : Frame F M K :=
    { s := s
      smooth := fun i => (hs i).1
      parallel := fun i x => hpar _ (hs i) x
      gram := hgram }
  refine ⟨fr, hs, fun f hf => ?_⟩
  have hfmem : MemLp f 2 μ := hf.2.1
  set c : Fin K → ℝ := fun j => ∫ y, f y * T j y ∂μ with hc
  set h : M → ℝ := fun y => f y - ∑ j, c j * T j y with hh
  have hheig : IsMEigenfunction F μ V ρ h := by
    have := (eigenSub F μ V ρ).sub_mem hf (hcomb c)
    exact this
  have hhmem : MemLp h 2 μ := hheig.2.1
  have horth : ∀ j, ∫ y, h y * T j y ∂μ = 0 := by
    intro j
    have i1 : Integrable (fun y => f y * T j y) μ := hfmem.integrable_mul (hmem j)
    have i2 : Integrable (fun y => (∑ i, c i * T i y) * T j y) μ :=
      (hcomb c).2.1.integrable_mul (hmem j)
    have e : (fun y => h y * T j y) = fun y => f y * T j y - (∑ i, c i * T i y) * T j y := by
      funext y; simp only [hh]; ring
    rw [e, integral_sub i1 i2, CutoffRigidity.Riemann.integral_sum_mul_orthonormal T hmem hTo c j]
    simp [hc]
  -- `h` vanishes: its class is orthogonal to the classes of the basis, which span the eigenspace
  have hfin := finiteDimensional_eigenClasses F hV hμ hρ hCD hgap
  have hfr : Module.finrank ℝ (eigenClasses F μ V ρ) = K := by
    rw [← mFirstEigenDim_eq_finrank F (V := V) hgap, hK]
  let u : Fin K → eigenClasses F μ V ρ := fun i =>
    ⟨(hmem i).toLp (T i), T i, hT i, (MemLp.coeFn_toLp (hmem i)).symm⟩
  have hinner : ∀ (g₁ g₂ : M → ℝ) (h₁ : MemLp g₁ 2 μ) (h₂ : MemLp g₂ 2 μ),
      inner ℝ (h₁.toLp g₁) (h₂.toLp g₂) = ∫ y, g₁ y * g₂ y ∂μ := by
    intro g₁ g₂ h₁ h₂
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp h₁, MemLp.coeFn_toLp h₂] with x e1 e2
    rw [e1, e2]
    simp [mul_comm]
  have hun : Orthonormal ℝ u := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Submodule.coe_inner]
    change inner ℝ ((hmem i).toLp (T i)) ((hmem j).toLp (T j)) = _
    rw [hinner _ _ (hmem i) (hmem j)]
    exact hTo i j
  have hspan : Submodule.span ℝ (Set.range u) = ⊤ :=
    hun.linearIndependent.span_eq_top_of_card_eq_finrank' (by simpa using hfr.symm)
  have hw : (hhmem).toLp h ∈ eigenClasses F μ V ρ :=
    ⟨h, hheig, (MemLp.coeFn_toLp hhmem).symm⟩
  have hwmem : (⟨(hhmem).toLp h, hw⟩ : eigenClasses F μ V ρ) ∈ Submodule.span ℝ (Set.range u) :=
    hspan ▸ Submodule.mem_top
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hwmem
  have hww : inner ℝ ((hhmem).toLp h) ((hhmem).toLp h) = 0 := by
    have h1 : inner ℝ (∑ i, d i • u i)
        (⟨(hhmem).toLp h, hw⟩ : eigenClasses F μ V ρ) = 0 := by
      rw [sum_inner]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Submodule.coe_inner, Submodule.coe_smul, real_inner_smul_left]
      change d i * inner ℝ ((hmem i).toLp (T i)) ((hhmem).toLp h) = 0
      rw [hinner _ _ (hmem i) hhmem]
      have : ∫ y, T i y * h y ∂μ = ∫ y, h y * T i y ∂μ := by
        congr 1; funext y; ring
      rw [this, horth i]; simp
    rw [hd] at h1
    simpa [Submodule.coe_inner] using h1
  have hw0 : (hhmem).toLp h = 0 := inner_self_eq_zero.mp hww
  have hae : h =ᵐ[μ] 0 := by
    have := (MemLp.coeFn_toLp hhmem).symm.trans
      ((Lp.ext_iff.mp hw0 |> fun h => h))
    exact this.trans (Lp.coeFn_zero _ _ _)
  have hh0 : h = 0 :=
    (Continuous.ae_eq_iff_eq μ hheig.1.continuous continuous_const).mp hae
  refine ⟨fun i => ∑ j, c j * B j i, fun x => ?_⟩
  have e1 : f x = ∑ j, c j * T j x := by
    have := congrFun hh0 x
    simp only [hh, Pi.zero_apply] at this
    linarith
  have e2 : ∀ j, ∑ i, B j i * s i x = T j x := by
    intro j
    have h1 : ∑ i, B j i * s i x = ∑ a, (B * A) j a * T a x := by
      simp only [s, Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => by ring
    rw [h1, hBA]
    simp [Matrix.one_apply]
  rw [e1]
  calc ∑ j, c j * T j x = ∑ j, c j * ∑ i, B j i * s i x := by simp only [e2]
    _ = ∑ i, (∑ j, c j * B j i) * s i x := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = ∑ i, (∑ j, c j * B j i) * fr.s i x := rfl

end EigenFrame

end CutCur
