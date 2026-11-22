/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedInterface
public import LeanPool.CutoffRigidity.RiemannianSplitting.RiemannianGradientCalculus

/-! # Pointwise calculus for the Challenge operators `mgrad`, `carre`

Product rule for `Γ`, the identity `d Γ(f,f) (v) = 2 Hess f (v, ∇f)` and the pointwise bound
`|Γ(χ, Γ(f,f))| ≤ 2 ‖∇χ‖ ‖Hess f‖_HS ‖∇f‖` used in the cutoff argument for rigidity.
-/

@[expose] public section

open Bundle MeasureTheory Filter
open scoped Manifold ContDiff ENNReal Topology

namespace CutCur

/-- A linear endomorphism of a finite dimensional Euclidean space is bounded by its
Hilbert–Schmidt norm. -/
theorem clm_norm_sq_le {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
    [FiniteDimensional ℝ T] (A : T →L[ℝ] T) (v : T) :
    ‖A v‖ ^ 2 ≤ ‖v‖ ^ 2 * ∑ i, ‖A (stdOrthonormalBasis ℝ T i)‖ ^ 2 := by
  set b := stdOrthonormalBasis ℝ T
  have hv : v = ∑ i, b.repr v i • b i := (b.sum_repr v).symm
  have h1 : A v = ∑ i, b.repr v i • A (b i) := by
    conv_lhs => rw [hv]
    simp [map_sum]
  have h2 : ‖A v‖ ≤ ∑ i, |b.repr v i| * ‖A (b i)‖ := by
    rw [h1]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun i _ => ?_
    rw [norm_smul, Real.norm_eq_abs]
  have h3 : (∑ i, |b.repr v i| * ‖A (b i)‖) ^ 2 ≤
      (∑ i, |b.repr v i| ^ 2) * ∑ i, ‖A (b i)‖ ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have h4 : ‖v‖ ^ 2 = ∑ i, |b.repr v i| ^ 2 := by
    have := b.sum_sq_norm_inner_right v
    rw [← this]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [sq_abs, b.repr_apply_apply, real_inner_comm]
  calc ‖A v‖ ^ 2 ≤ (∑ i, |b.repr v i| * ‖A (b i)‖) ^ 2 := by
        gcongr
    _ ≤ _ := h3
    _ = _ := by rw [h4]

section Pointwise

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]

theorem contMDiff_mgrad_one {f : M → ℝ} (hf : MSmooth F f) :
    ContMDiff 𝓘(ℝ, F) 𝓘(ℝ, F).tangent 1 (T% (mgrad F f)) :=
  CutoffRigidity.contMDiff_manifoldGradient (hf.of_le (by norm_num))

theorem mgrad_mdiffAt {f : M → ℝ} (hf : MSmooth F f) (x : M) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, F).tangent
      (fun y => (⟨y, mgrad F f y⟩ : TangentBundle 𝓘(ℝ, F) M)) x :=
  ((contMDiff_mgrad_one F hf) x).mdifferentiableAt one_ne_zero

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x]
  [FiniteDimensional ℝ F]
  [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mdiffAt_of_smooth {f : M → ℝ} (hf : MSmooth F f) (x : M) :
    MDifferentiableAt 𝓘(ℝ, F) 𝓘(ℝ, ℝ) f x :=
  (hf x).mdifferentiableAt (by simp)

theorem mvfderiv_carre_self {f : M → ℝ} (hf : MSmooth F f) (x : M)
    (v : TangentSpace 𝓘(ℝ, F) x) :
    mvfderiv 𝓘(ℝ, F) (fun y => carre F f f y) x v =
      2 * CutoffRigidity.manifoldHessian 𝓘(ℝ, F) f x v (mgrad F f x) := by
  have := CutoffRigidity.mvfderiv_manifoldGradient_norm_sq (I := 𝓘(ℝ, F)) (f := f) (x := x)
    (mgrad_mdiffAt F hf x) v
  simp only [carre, real_inner_self_eq_norm_sq]
  exact this

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- `Γ(χ, f) = df(∇χ)`. -/
theorem carre_eq_mvfderiv (χ f : M → ℝ) (x : M) :
    carre F χ f x = mvfderiv 𝓘(ℝ, F) f x (mgrad F χ x) := by
  rw [carre, real_inner_comm]
  exact CutoffRigidity.inner_manifoldGradient (I := 𝓘(ℝ, F)) f x (mgrad F χ x)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem carre_nonneg (f : M → ℝ) (x : M) : 0 ≤ carre F f f x := by
  rw [carre]; exact real_inner_self_nonneg

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem carre_self_eq (f : M → ℝ) (x : M) : carre F f f x = ‖mgrad F f x‖ ^ 2 := by
  rw [carre, real_inner_self_eq_norm_sq]

theorem mHessNormSq_nonneg (f : M → ℝ) (x : M) : 0 ≤ mHessNormSq F f x :=
  CutoffRigidity.manifoldHessianNormSq_nonneg 𝓘(ℝ, F) f x

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- Product rule for the gradient. -/
theorem mgrad_mul {f g : M → ℝ} (hf : MSmooth F f) (hg : MSmooth F g) (x : M) :
    mgrad F (f * g) x = f x • mgrad F g x + g x • mgrad F f x :=
  CutoffRigidity.manifoldGradient_mul (I := 𝓘(ℝ, F)) (mdiffAt_of_smooth F hf x) (mdiffAt_of_smooth
      F hg x)

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- Product rule for `Γ` in the first slot. -/
theorem carre_mul_left {f g h : M → ℝ} (hf : MSmooth F f) (hg : MSmooth F g) (x : M) :
    carre F (f * g) h x = f x * carre F g h x + g x * carre F f h x := by
  simp only [carre, mgrad_mul F hf hg, inner_add_left, real_inner_smul_left]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
/-- Cauchy–Schwarz: `|Γ(f,g)| ≤ ‖∇f‖ ‖∇g‖`. -/
theorem abs_carre_le (f g : M → ℝ) (x : M) :
    |carre F f g x| ≤ ‖mgrad F f x‖ * ‖mgrad F g x‖ :=
  abs_real_inner_le_norm _ _

/-- `|Γ(χ, Γ(f,f))| ≤ 2 ‖∇χ‖ ‖Hess f‖_HS ‖∇f‖`. -/
theorem abs_carre_carre_le {f : M → ℝ} (hf : MSmooth F f) (χ : M → ℝ) (x : M) :
    |carre F χ (carre F f f) x| ≤
      2 * ‖mgrad F χ x‖ * Real.sqrt (mHessNormSq F f x) * Real.sqrt (carre F f f x) := by
  set A := CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F f) x with hA
  have h1 : carre F χ (carre F f f) x = 2 * inner ℝ (A (mgrad F χ x)) (mgrad F f x) := by
    rw [carre_eq_mvfderiv, mvfderiv_carre_self F hf]
    rfl
  have h2 : ‖A (mgrad F χ x)‖ ≤ ‖mgrad F χ x‖ * Real.sqrt (mHessNormSq F f x) := by
    have := clm_norm_sq_le A (mgrad F χ x)
    have h3 : ‖A (mgrad F χ x)‖ ^ 2 ≤
        (‖mgrad F χ x‖ * Real.sqrt (mHessNormSq F f x)) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (mHessNormSq_nonneg F f x)]
      exact this
    exact le_of_sq_le_sq h3 (by positivity)
  have h4 : ‖mgrad F f x‖ = Real.sqrt (carre F f f x) := by
    rw [carre_self_eq, Real.sqrt_sq (norm_nonneg _)]
  rw [h1, abs_mul, abs_two]
  calc 2 * |inner ℝ (A (mgrad F χ x)) (mgrad F f x)|
      ≤ 2 * (‖A (mgrad F χ x)‖ * ‖mgrad F f x‖) := by
        gcongr; exact abs_real_inner_le_norm _ _
    _ ≤ 2 * ((‖mgrad F χ x‖ * Real.sqrt (mHessNormSq F f x)) * ‖mgrad F f x‖) := by
        gcongr
    _ = _ := by rw [h4]; ring

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem mgrad_eq_zero_of_notMem_tsupport {u : M → ℝ} {x : M} (hx : x ∉ tsupport u) :
    mgrad F u x = 0 := by
  have h : u =ᶠ[𝓝 x] (fun _ => (0:ℝ)) := by
    have := notMem_tsupport_iff_eventuallyEq.mp hx
    exact this
  have h2 : mvfderiv 𝓘(ℝ, F) u x = 0 := by
    unfold mvfderiv
    rw [h.mfderiv_eq, mfderiv_const]
    simp
  simp [mgrad, h2]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem carre_eq_zero_off_tsupport {u : M → ℝ} (g : M → ℝ) {x : M} (hx : x ∉ tsupport u) :
    carre F u g x = 0 := by
  simp [carre, mgrad_eq_zero_of_notMem_tsupport F hx]

omit [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F fun x : M ↦ TangentSpace 𝓘(ℝ, F) x] in
theorem hasCompactSupport_carre {u : M → ℝ} (g : M → ℝ) (hu : HasCompactSupport u) :
    HasCompactSupport (fun x => carre F u g x) := by
  refine hu.mono' ?_
  intro x hx
  by_contra h
  exact hx (carre_eq_zero_off_tsupport F g h)

end Pointwise

end CutCur
