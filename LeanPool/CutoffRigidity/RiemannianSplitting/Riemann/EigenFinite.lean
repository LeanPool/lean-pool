/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.EigenLinear
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedFinal
public import LeanPool.CutoffRigidity.RiemannianSplitting.ManifoldZeroDifferential
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedSupport
public import LeanPool.CutoffRigidity.RiemannianSplitting.Riemann.WeightedIBPDensity

/-! # The first eigenspace is finite dimensional; orthonormal eigenbasis; `k₁ > 0` iff an
eigenfunction exists

Under the hypotheses of `riemannian_gaussian_splitting`:

* `eigenSub`: smooth `L²` eigenfunctions of `-𝓛` with eigenvalue `ρ` form a vector space;
* `eigenfunction_eq_zero_of_grad_zero`: an eigenfunction whose gradient vanishes at one point is `0`
  (parallel gradient + connectedness);
* `finiteDimensional_eigenClasses`: the span of the `L²` classes is finite dimensional,
  so `mFirstEigenDim` is the true dimension;
* `exists_orthonormal_eigenbasis`: the orthonormal eigenbasis (`EigenSplitting.basis`);
* `mFirstEigenDim_pos_iff`: `0 < k₁` iff there is a nonzero eigenfunction.

Attainment of the spectral gap (existence of a nonzero eigenfunction) is NOT proved here, see
`riemann-status/gap.md`.
-/

@[expose] public section

open Bundle MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace CutCur

section EigenFinite

variable (F : Type) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]
  {M : Type} [EMetricSpace M] [ChartedSpace F M] [IsManifold 𝓘(ℝ, F) ∞ M]
  [RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [IsContMDiffRiemannianBundle 𝓘(ℝ, F) ∞ F (fun x : M => TangentSpace 𝓘(ℝ, F) x)]
  [MeasurableSpace M]

/-- Smooth `L²` eigenfunctions with eigenvalue `lam` form a subspace of `M → ℝ`. -/
def eigenSub (μ : Measure M) (V : M → ℝ) (lam : ℝ) : Submodule ℝ (M → ℝ) where
  carrier := {f | IsMEigenfunction F μ V lam f}
  zero_mem' := by
    refine ⟨contMDiff_const, ?_, fun x => ?_⟩
    · exact MemLp.zero
    · simp only [Pi.zero_apply, mul_zero]
      exact mgenerator_zero F x
  add_mem' := by
    rintro f g ⟨hf1, hf2, hf3⟩ ⟨hg1, hg2, hg3⟩
    refine ⟨hf1.add hg1, hf2.add hg2, fun x => ?_⟩
    have := mgenerator_add F (V := V) hf1 hg1 x
    simp only [Pi.add_apply]
    rw [show (f + g) = fun y => f y + g y from rfl, this, hf3, hg3]; ring
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    refine ⟨(contMDiff_const (c := c)).mul hf1, hf2.const_smul c, fun x => ?_⟩
    have := mgenerator_const_mul F (V := V) c hf1 x
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [show (c • f) = fun y => c * f y from rfl, this, hf3]; ring

omit [MeasurableSpace F] [BorelSpace F] in
theorem mem_eigenSub {μ : Measure M} {V : M → ℝ} {lam : ℝ} {f : M → ℝ} :
    f ∈ eigenSub F μ V lam ↔ IsMEigenfunction F μ V lam f := Iff.rfl

variable [IsRiemannianManifold 𝓘(ℝ, F) M] [ConnectedSpace M] [CompleteSpace M] [BorelSpace M]

omit [MeasurableSpace F]
  [BorelSpace F]
  [IsRiemannianManifold 𝓘(ℝ, F) M]
  [CompleteSpace M]
  [BorelSpace M] in
/-- An eigenfunction (eigenvalue `ρ ≠ 0`) with parallel gradient and vanishing gradient at one
point is identically zero. -/
theorem eigenfunction_eq_zero_of_grad_zero {V : M → ℝ} {μ : Measure M} {ρ : ℝ} (hρ : ρ ≠ 0)
    {h : M → ℝ} (hh : IsMEigenfunction F μ V ρ h)
    (hpar : ∀ x, CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F h) x = 0)
    (x₀ : M) (h0 : mgrad F h x₀ = 0) : h = 0 := by
  have hsm : MSmooth F h := hh.1
  have hcar : ∀ x, carre F h h x = carre F h h x₀ := by
    intro x
    refine CutoffRigidity.eq_of_mvfderiv_eq_zero (I := 𝓘(ℝ, F))
      (f := fun y => carre F h h y) ((WReg.msmooth_carre hsm hsm).mdifferentiable (by simp))
      (fun y => ?_) x x₀
    ext v
    rw [mvfderiv_carre_self F hsm y v]
    have : CutoffRigidity.manifoldHessian 𝓘(ℝ, F) h y v (mgrad F h y) = 0 := by
      unfold CutoffRigidity.manifoldHessian
      have := hpar y
      change inner ℝ (CovariantDerivative.leviCivitaConnection 𝓘(ℝ, F) M (mgrad F h) y v) _ = 0
      rw [this]; simp
    simp [this]
  have hg : ∀ x, mgrad F h x = 0 := by
    intro x
    have h1 := hcar x
    rw [carre_self_eq, carre_self_eq, h0] at h1
    simpa using h1
  funext x
  have e := hh.2.2 x
  have : mgenerator F V h x = 0 := by
    unfold mgenerator mlaplacian
    rw [hpar x, hg x]; simp
  rw [this] at e
  have : ρ * h x = 0 := by linarith
  simpa [hρ] using this

variable {V : M → ℝ} (hV : MSmooth F V) {μ : Measure M} [IsProbabilityMeasure μ]
  (hμ : IsWeightedVolume F μ V) {ρ : ℝ} (hρ : 0 < ρ) (hCD : CD F ρ V)
  (hgap : mSpectralGap F μ = ρ)

include hV hμ hρ hCD hgap in
/-- The space of smooth `L²` eigenfunctions with eigenvalue `ρ` is finite dimensional
(its dimension is at most `dim F`). -/
theorem finiteDimensional_eigenSub [Nonempty M] :
    FiniteDimensional ℝ (eigenSub F μ V ρ) := by
  classical
  obtain ⟨x₀⟩ := ‹Nonempty M›
  have hE : ∀ f : eigenSub F μ V ρ, IsMEigenfunction F μ V ρ f.1 := fun f => f.2
  let Φ : eigenSub F μ V ρ →ₗ[ℝ] TangentSpace 𝓘(ℝ, F) x₀ :=
    { toFun := fun f => mgrad F f.1 x₀
      map_add' := fun f g => by
        have := mgrad_add' F (hE f).1 (hE g).1 x₀
        exact this
      map_smul' := fun c f => by
        have := mgrad_const_mul F c (hE f).1 x₀
        exact this }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro f hf
    apply Subtype.ext
    exact eigenfunction_eq_zero_of_grad_zero F hρ.ne' f.2
      (fun x => manifold_eigenfunction_parallel_gradient F hV hμ hρ hCD hgap f.2 x) x₀ hf
  exact Module.Finite.of_injective Φ hinj

/-- The `L²`-classes of eigenfunctions, as a subspace of `L²(μ)`. -/
def eigenClasses (μ : Measure M) (V : M → ℝ) (lam : ℝ) : Submodule ℝ (M →₂[μ] ℝ) where
  carrier := {u | ∃ f, IsMEigenfunction F μ V lam f ∧ f =ᵐ[μ] u}
  zero_mem' := ⟨0, (eigenSub F μ V lam).zero_mem, (Lp.coeFn_zero _ _ _).symm⟩
  add_mem' := by
    rintro u v ⟨f, hf, hfu⟩ ⟨g, hg, hgv⟩
    refine ⟨f + g, (eigenSub F μ V lam).add_mem hf hg, ?_⟩
    filter_upwards [hfu, hgv, Lp.coeFn_add u v] with x h1 h2 h3
    simp only [Pi.add_apply]
    rw [h1, h2]; exact h3.symm
  smul_mem' := by
    rintro c u ⟨f, hf, hfu⟩
    refine ⟨c • f, (eigenSub F μ V lam).smul_mem c hf, ?_⟩
    filter_upwards [hfu, Lp.coeFn_smul c u] with x h1 h3
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [h1]; exact h3.symm

include hV hμ hρ hCD hgap in
theorem finiteDimensional_eigenClasses [Nonempty M] :
    FiniteDimensional ℝ (eigenClasses F μ V ρ) := by
  have := finiteDimensional_eigenSub F hV hμ hρ hCD hgap
  have hE : ∀ f : eigenSub F μ V ρ, IsMEigenfunction F μ V ρ f.1 := fun f => f.2
  let ψ : eigenSub F μ V ρ →ₗ[ℝ] (M →₂[μ] ℝ) :=
    { toFun := fun f => (hE f).2.1.toLp f.1
      map_add' := fun f g => by
        exact (MemLp.toLp_add (hE f).2.1 (hE g).2.1)
      map_smul' := fun c f => by
        exact (MemLp.toLp_const_smul c (hE f).2.1) }
  have : eigenClasses F μ V ρ = LinearMap.range ψ := by
    ext u
    constructor
    · rintro ⟨f, hf, hfu⟩
      refine ⟨⟨f, hf⟩, ?_⟩
      change (hf.2.1).toLp f = u
      refine Lp.ext ?_
      filter_upwards [MemLp.coeFn_toLp hf.2.1, hfu] with x h1 h2
      rw [h1, h2]
    · rintro ⟨f, rfl⟩
      exact ⟨f.1, hE f, (MemLp.coeFn_toLp (hE f).2.1).symm⟩
  rw [this]
  infer_instance

include hgap in
omit [MeasurableSpace F]
  [BorelSpace F]
  [IsRiemannianManifold 𝓘(ℝ, F) M]
  [ConnectedSpace M]
  [CompleteSpace M]
  [BorelSpace M]
  [IsProbabilityMeasure μ] in
/-- `mFirstEigenDim` is the genuine dimension of the eigenspace of classes (which is finite
dimensional). -/
theorem mFirstEigenDim_eq_finrank :
    mFirstEigenDim F μ V = Module.finrank ℝ (eigenClasses F μ V ρ) := by
  unfold mFirstEigenDim
  rw [hgap]
  rw [show Submodule.span ℝ {u : M →₂[μ] ℝ | ∃ f, IsMEigenfunction F μ V ρ f ∧ f =ᵐ[μ] u} =
    eigenClasses F μ V ρ from Submodule.span_eq (eigenClasses F μ V ρ)]


include hV hμ hρ hCD hgap in
/-- An orthonormal basis of the `L²` eigenspace, with smooth representatives. -/
theorem exists_orthonormal_eigenbasis_with_representatives :
    ∃ b : OrthonormalBasis (Fin (mFirstEigenDim F μ V)) ℝ (eigenClasses F μ V ρ),
      ∃ T : Fin (mFirstEigenDim F μ V) → M → ℝ,
        (∀ i, IsMEigenfunction F μ V ρ (T i)) ∧
        (∀ i, T i =ᵐ[μ] (b i : M →₂[μ] ℝ)) ∧
        ∀ i j, ∫ y, T i y * T j y ∂μ = if i = j then 1 else 0 := by
  have hfin := finiteDimensional_eigenClasses F hV hμ hρ hCD hgap
  have hk := mFirstEigenDim_eq_finrank F (V := V) hgap
  let b : OrthonormalBasis (Fin (mFirstEigenDim F μ V)) ℝ (eigenClasses F μ V ρ) :=
    (stdOrthonormalBasis ℝ (eigenClasses F μ V ρ)).reindex (finCongr hk.symm)
  have hmem : ∀ i, ∃ f, IsMEigenfunction F μ V ρ f ∧ f =ᵐ[μ] ((b i : eigenClasses F μ V ρ) :
      M →₂[μ] ℝ) := fun i => (b i).2
  choose T hT hTb using hmem
  refine ⟨b, T, hT, hTb, fun i j => ?_⟩
  have h1 : ∫ y, T i y * T j y ∂μ = inner ℝ (b i : M →₂[μ] ℝ) (b j : M →₂[μ] ℝ) := by
    rw [MeasureTheory.L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hTb i, hTb j] with x h1 h2
    rw [h1, h2]
    simp [mul_comm]
  rw [h1]
  have := orthonormal_iff_ite.mp b.orthonormal i j
  rw [Submodule.coe_inner] at this
  exact this

include hV hμ hρ hCD hgap in
/-- An integral-orthonormal family of smooth eigenfunctions indexed by the eigenspace dimension. -/
theorem exists_orthonormal_eigenbasis :
    ∃ T : Fin (mFirstEigenDim F μ V) → M → ℝ, (∀ i, IsMEigenfunction F μ V ρ (T i)) ∧
      ∀ i j, ∫ y, T i y * T j y ∂μ = if i = j then 1 else 0 := by
  obtain ⟨_, T, hT, _, hTo⟩ :=
    exists_orthonormal_eigenbasis_with_representatives F hV hμ hρ hCD hgap
  exact ⟨T, hT, hTo⟩

include hV hμ hρ hCD hgap in
/-- `0 < k₁` iff there is a (smooth, `L²`) eigenfunction for `ρ` which is not identically zero.
This is the only missing piece (attainment of the spectral gap); see `riemann-status/gap.md`. -/
theorem mFirstEigenDim_pos_iff :
    0 < mFirstEigenDim F μ V ↔
      ∃ f, IsMEigenfunction F μ V ρ f ∧ ∃ x, f x ≠ 0 := by
  have hfin := finiteDimensional_eigenClasses F hV hμ hρ hCD hgap
  rw [mFirstEigenDim_eq_finrank F (V := V) hgap, Module.finrank_pos_iff_exists_ne_zero]
  constructor
  · rintro ⟨⟨u, f, hf, hfu⟩, hne⟩
    refine ⟨f, hf, ?_⟩
    by_contra hall
    push Not at hall
    apply hne
    apply Subtype.ext
    apply Lp.ext
    have : f = 0 := funext hall
    filter_upwards [hfu] with x hx
    rw [← hx, this]; simp
  · rintro ⟨f, hf, x, hx⟩
    have hcont : Continuous f := hf.1.continuous
    have hopen : IsOpen {y | f y ≠ 0} := isOpen_ne_fun hcont continuous_const
    have hpos : 0 < μ {y | f y ≠ 0} :=
      measure_pos_of_isWeightedVolume F hV hμ (continuousOn_chartVolumeDensity F)
        (fun x₀ z hz => chartVolumeDensity_pos F x₀ hz) hopen ⟨x, hx⟩
    refine ⟨⟨hf.2.1.toLp f, f, hf, (MemLp.coeFn_toLp hf.2.1).symm⟩, ?_⟩
    intro h0
    have h1 : hf.2.1.toLp f = 0 := congrArg Subtype.val h0
    have h2 : f =ᵐ[μ] 0 := by
      have := (MemLp.coeFn_toLp hf.2.1).symm.trans
        ((Lp.ext_iff.mp h1 |> fun h => h))
      exact this.trans (Lp.coeFn_zero _ _ _)
    have h3 : μ {y | f y ≠ 0} = 0 := by
      have := ae_iff.mp h2
      simpa using this
    exact hpos.ne' h3

end EigenFinite

end CutCur
