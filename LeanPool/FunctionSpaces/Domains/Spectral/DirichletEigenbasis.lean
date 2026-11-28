/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Spectral.CompactEmbedding
public import LeanPool.FunctionSpaces.Domains.Sobolev.SobolevRestrictionSpaces

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Dirichlet Laplacian on bounded open sets

Let `V` be a finite-dimensional real inner product space, such as `ℝ^d`, with Lebesgue measure,
and `Ω ⊆ V` a bounded open set. The embedding `H^1_0(Ω) ↪ L_2(Ω)` is a compact dense embedding
of Hilbert spaces, so its spectral scheme is a Hilbert basis of `L_2(Ω)` of eigenfunctions of the
Dirichlet Laplacian, in weak form.

* **Polarization**: a norm identity `‖x‖² = ‖T x‖² + c ∑_i ‖S_i x‖²` for linear maps `T`, `S_i`
  between inner product spaces gives the same identity for the inner products
  (`inner_eq_of_forall_sq_norm_eq`).
* **The inner product of `H^1(V)`** is
  `⟨U, W⟩ = ⟨ι U, ι W⟩_2 + (2π)⁻² ∑_k ⟨∂_{b_k} ι U, ∂_{b_k} ι W⟩_2` for every orthonormal basis
  `(b_k)` of `V`, by polarization of the norm identity (`inner_eq_of_forall_sq_norm_eq`,
  `Rd.inner_eq_of_hasWeakLineDeriv`).
* **The Dirichlet embedding** `Rd.dirichletEmbedding Ω : H^1_0(Ω) → L_2(Ω)` is injective, of norm
  at most `1`, has dense range since the test functions of `Ω` are dense in `L_2(Ω)`
  (`Rd.orthogonal_range_dirichletEmbedding`), and is compact for bounded `Ω` (Rellich's theorem);
  for `u, w ∈ H^1_0(Ω)` the inner product of `L_2(Ω)` is that of `L_2(V)`
  (`Rd.inner_dirichletEmbedding`).
* **The Dirichlet eigenbasis**: `Rd.dirichletScheme hΩ` is the spectral scheme of this embedding,
  a Hilbert basis `(e_i)` of `L_2(Ω)` with levels `⌊√(1 + λ_i/(4π²))⌋₊`
  (`Rd.dirichletScheme_level`), where `λ_i ≥ 0` is the Dirichlet eigenvalue
  (`Rd.dirichletEigenvalue`). The eigenfunction `φ_i ∈ H^1_0(Ω)` with `φ_i = e_i` on `Ω`
  (`Rd.dirichletEigenfunction`) satisfies `∑_k ⟨∂_{b_k} φ_i, ∂_{b_k} w⟩_2 = λ_i ⟨φ_i, w⟩_2` for
  every `w ∈ H^1_0(Ω)`, inner products conjugate-linear in the first argument as in Mathlib
  (`Rd.dirichletEigenfunction_weak`), the weak form of `-Δ φ_i = λ_i φ_i`, `φ_i = 0` on `∂Ω`.
* **`H^1_0(Ω)` as a spectral Sobolev space**: `f ∈ L_2(Ω)` lies in `H^1_0(Ω)` iff
  `∑_i (1 + ⌊σ_i⁻¹⌋₊)² |⟨e_i, f⟩|² < ∞` (`Rd.exists_dirichletEmbedding_eq_iff`), and the real
  interpolation spaces `(L_2(Ω), H^1_0(Ω))_{θ,q}` are the approximation spaces of the Dirichlet
  scheme (`Rd.memKMethod_dirichlet_iff`, `Rd.memKMethod_dirichlet_iff_blockNorm_lt_top`).
-/

@[expose] public section

open MeasureTheory Filter Topology TopologicalSpace
open scoped ENNReal Real InnerProductSpace BesselPotentialSpace Distributions

/-! ### Polarization of a norm identity -/

section Polarization

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]

/-- **Polarization of a norm identity**: let `T : E → F` and `S_i : E → G` (`i` in a finite
index set) be linear maps between inner product spaces over `𝕜 = ℝ` or `ℂ`, and `c` real with
`‖x‖² = ‖T x‖² + c ∑_i ‖S_i x‖²` for every `x`. Then
`⟨x, y⟩ = ⟨T x, T y⟩ + c ∑_i ⟨S_i x, S_i y⟩` for all `x, y`, as both sides are given by the
polarization identity (Mathlib's `inner_eq_sum_norm_sq_div_four`). -/
theorem inner_eq_of_forall_sq_norm_eq {F G ι : Type*} [Fintype ι]
    [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
    [NormedAddCommGroup G] [InnerProductSpace 𝕜 G] (T : E →ₗ[𝕜] F) (S : ι → E →ₗ[𝕜] G) (c : ℝ)
    (h : ∀ x, ‖x‖ ^ 2 = ‖T x‖ ^ 2 + c * ∑ i, ‖S i x‖ ^ 2) (x y : E) :
    ⟪x, y⟫_𝕜 = ⟪T x, T y⟫_𝕜 + (c : 𝕜) * ∑ i, ⟪S i x, S i y⟫_𝕜 := by
  have key : ∀ z, (‖z‖ : 𝕜) ^ 2 = (‖T z‖ : 𝕜) ^ 2 + (c : 𝕜) * ∑ i, (‖S i z‖ : 𝕜) ^ 2 :=
    fun z => by
      have hz := congrArg (fun r : ℝ => (r : 𝕜)) (h z)
      push_cast at hz
      exact hz
  rw [inner_eq_sum_norm_sq_div_four x y, inner_eq_sum_norm_sq_div_four (T x) (T y)]
  simp only [inner_eq_sum_norm_sq_div_four (S _ x) (S _ y)]
  rw [key, key, key, key]
  simp only [map_add, map_sub, map_smul, ← Finset.sum_div, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.sum_mul]
  ring

end Polarization

namespace Rd

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-! ### The inner product of `H^1(V)` -/

/-- **The inner product of `H^1(V)` by the weak gradient**: let `(b_k)` be an orthonormal basis
of `V` and `U, W ∈ H^1(V)` whose `L_2` functions have the weak derivatives `g_k = ∂_{b_k} ι U`
and `h_k = ∂_{b_k} ι W` on `V`. Then `⟨U, W⟩ = ⟨ι U, ι W⟩_2 + (2π)⁻² ∑_k ⟨g_k, h_k⟩_2`, the
polarization (`inner_eq_of_forall_sq_norm_eq`) of
`‖U‖² = ‖ι U‖_2² + (2π)⁻² ∑_k ‖∂_{b_k} ι U‖_2²` (`Rd.sq_norm_eq_of_hasWeakLineDeriv`). -/
theorem inner_eq_of_hasWeakLineDeriv {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    {U W : H^{1}(V)} {g h : ι → Lp ℂ 2 (volume : Measure V)}
    (hg : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => b i) (toL2 U) (g i))
    (hh : ∀ i, HasWeakLineDeriv ⊤ (fun _ : Fin 1 => b i) (toL2 W) (h i)) :
    ⟪U, W⟫_ℂ = ⟪toL2 U, toL2 W⟫_ℂ + (((2 * π)⁻¹ ^ 2 : ℝ) : ℂ) * ∑ i, ⟪g i, h i⟫_ℂ := by
  have hgU : g = fun i => weakDerivL2 (b i) U := funext fun i => (weakDerivL2_eq (hg i)).symm
  have hhW : h = fun i => weakDerivL2 (b i) W := funext fun i => (weakDerivL2_eq (hh i)).symm
  subst hgU hhW
  exact inner_eq_of_forall_sq_norm_eq (toL2 : H^{1}(V) →L[ℂ] _).toLinearMap
    (fun i => (weakDerivL2 (b i)).toLinearMap) _
    (fun x => sq_norm_eq_of_hasWeakLineDeriv b x fun i => hasWeakLineDeriv_weakDerivL2 _ _) U W

/-! ### The Dirichlet embedding -/

variable {Ω : Opens V}

variable (Ω) in
/-- **The Dirichlet embedding** `H^1_0(Ω) → L_2(Ω)`, `u ↦ u|_Ω`: the restriction to `L_2(Ω)`
(`Rd.restrictL2`) on the closed subspace `H^1_0(Ω)` of `H^1(Ω)`. -/
noncomputable def dirichletEmbedding :
    zeroBoundarySpace 1 Ω →L[ℂ] Lp ℂ 2 (volume.restrict (Ω : Set V)) :=
  restrictL2 Ω ∘L (zeroBoundarySpace 1 Ω).subtypeL

/-- `dirichletEmbedding Ω u` is the restriction to `Ω` of the `L_2` function of `u`. -/
theorem dirichletEmbedding_apply (u : zeroBoundarySpace 1 Ω) :
    dirichletEmbedding Ω u = restrictL2 Ω u :=
  rfl

/-- The Dirichlet embedding is injective (`Rd.restrictL2_injective`). -/
theorem dirichletEmbedding_injective : Function.Injective (dirichletEmbedding Ω) :=
  restrictL2_injective.comp Subtype.val_injective

/-- The Dirichlet embedding has norm at most `1` (`Rd.norm_restrictL2_apply_le`). -/
theorem norm_dirichletEmbedding_le : ‖dirichletEmbedding Ω‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    rw [one_mul]
    exact norm_restrictL2_apply_le _

/-- **Rellich's theorem for `H^1_0(Ω)`**: for every bounded open set `Ω`, the Dirichlet embedding
is compact, as the restriction of the compact embedding `H^1(Ω) → L_2(Ω)`
(`Rd.isCompactOperator_restrictL2`). -/
theorem isCompactOperator_dirichletEmbedding (hΩ : Bornology.IsBounded (Ω : Set V)) :
    IsCompactOperator (dirichletEmbedding Ω) :=
  (isCompactOperator_restrictL2 hΩ).comp_clm _

/-- The elements of `H^1_0(Ω)` vanish outside `Ω`: inside `H^1(V)` they are elements of
`HTilde^1(Ω)` (`Rd.coe_tildeEquivZeroBoundary_symm_apply`), whose `L_2` functions vanish almost
everywhere outside `Ω` (`Rd.toL2_ae_eq_zero_of_mem_tildeSpace`). -/
theorem toL2_ae_eq_zero_of_mem_zeroBoundarySpace (u : zeroBoundarySpace 1 Ω) :
    ∀ᵐ x ∂volume, x ∉ (Ω : Set V) → toL2 ((u : RestrictionSpace 1 Ω) : H^{1}(V)) x = 0 := by
  rw [← coe_tildeEquivZeroBoundary_symm_apply]
  exact toL2_ae_eq_zero_of_mem_tildeSpace ((tildeEquivZeroBoundary Ω).symm u).2

/-- **The `L_2(Ω)` inner product of elements of `H^1_0(Ω)`** is the `L_2(V)` inner product of
their `L_2` functions, since these vanish outside `Ω`
(`Rd.toL2_ae_eq_zero_of_mem_zeroBoundarySpace`). -/
theorem inner_dirichletEmbedding (u w : zeroBoundarySpace 1 Ω) :
    ⟪dirichletEmbedding Ω u, dirichletEmbedding Ω w⟫_ℂ =
      ⟪toL2 ((u : RestrictionSpace 1 Ω) : H^{1}(V)),
        toL2 ((w : RestrictionSpace 1 Ω) : H^{1}(V))⟫_ℂ := by
  rw [L2.inner_def, L2.inner_def]
  have hu := LpToLpRestrictCLM_coeFn ℂ (Ω : Set V) (toL2 ((u : RestrictionSpace 1 Ω) : H^{1}(V)))
  have hw := LpToLpRestrictCLM_coeFn ℂ (Ω : Set V) (toL2 ((w : RestrictionSpace 1 Ω) : H^{1}(V)))
  rw [dirichletEmbedding_apply, dirichletEmbedding_apply, restrictL2_apply, restrictL2_apply]
  rw [integral_congr_ae (hu.mono fun x hx => by rw [hx]), integral_congr_ae
    (hw.mono fun x hx => by rw [hx])]
  refine setIntegral_eq_integral_of_ae_compl_eq_zero ?_
  filter_upwards [toL2_ae_eq_zero_of_mem_zeroBoundarySpace u] with x hx hxΩ
  rw [hx hxΩ, inner_zero_left]

/-- The restriction of a test function `φ` of `Ω` lies in `H^1_0(Ω)`. -/
theorem restrictProj_ofTest_mem (φ : 𝓓(Ω, ℝ)) :
    restrictProj 1 Ω (ofTest 1 φ) ∈ zeroBoundarySpace 1 Ω :=
  Submodule.le_topologicalClosure _ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨φ, rfl⟩))

/-- **Integrals against test functions as inner products**: for a real test function `φ` of `Ω`
and `f ∈ L_2(Ω)`, `⟨φ|_Ω, f⟩_{L_2(Ω)} = ∫_Ω φ f`, where `φ|_Ω ∈ H^1_0(Ω)`
(`Rd.restrictProj_ofTest_mem`, `Rd.restrictL2_restrictProj`, `Rd.toL2_ofTest_ae`). -/
theorem inner_dirichletEmbedding_ofTest (φ : 𝓓(Ω, ℝ))
    (f : Lp ℂ 2 (volume.restrict (Ω : Set V))) :
    ⟪dirichletEmbedding Ω ⟨_, restrictProj_ofTest_mem φ⟩, f⟫_ℂ =
      ∫ x, φ x • f x ∂volume.restrict (Ω : Set V) := by
  rw [L2.inner_def, dirichletEmbedding_apply]
  change ∫ x, ⟪restrictL2 Ω (restrictProj 1 Ω (ofTest 1 φ)) x, f x⟫_ℂ ∂_ = _
  rw [restrictL2_restrictProj]
  refine integral_congr_ae ?_
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ (Ω : Set V) (toL2 (ofTest 1 φ)),
    ae_restrict_of_ae (toL2_ofTest_ae φ)] with x hx hφ
  rw [hx, hφ, testSchwartz_apply, RCLike.inner_apply, Complex.conj_ofReal, Complex.real_smul,
    mul_comm]

/-- **The test functions are dense in `L_2(Ω)`**: the range of the Dirichlet embedding has trivial
orthogonal complement. If `f ∈ L_2(Ω)` is orthogonal to all `φ|_Ω`, then `∫_Ω φ f = 0` for every
real test function `φ` of `Ω` (`Rd.inner_dirichletEmbedding_ofTest`), so `f = 0` almost everywhere
on `Ω` (Mathlib's `IsOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero`). -/
theorem orthogonal_range_dirichletEmbedding :
    (LinearMap.range (dirichletEmbedding Ω :
      zeroBoundarySpace 1 Ω →ₗ[ℂ] Lp ℂ 2 (volume.restrict (Ω : Set V))))ᗮ = ⊥ := by
  refine le_antisymm (fun f hf => ?_) bot_le
  have h0 : ∀ φ : 𝓓(Ω, ℝ), ∫ x, φ x • f x ∂volume.restrict (Ω : Set V) = 0 := fun φ => by
    rw [← inner_dirichletEmbedding_ofTest]
    exact (Submodule.mem_orthogonal _ f).1 hf _ (LinearMap.mem_range_self _ _)
  have hae := Ω.isOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := volume.restrict (Ω : Set V))
    (((Lp.memLp f).locallyIntegrable (by norm_num)).locallyIntegrableOn _)
    fun g hg hgc hgs => h0 ⟨g, hg, hgc, hgs⟩
  rw [Submodule.mem_bot, Lp.eq_zero_iff_ae_eq_zero]
  filter_upwards [hae, ae_restrict_mem Ω.isOpen.measurableSet] with x hx hxΩ
  exact hx hxΩ

/-- The Dirichlet embedding has dense range (`Rd.orthogonal_range_dirichletEmbedding`). -/
theorem denseRange_dirichletEmbedding : DenseRange (dirichletEmbedding Ω) := by
  have h := Submodule.topologicalClosure_eq_top_iff.2
    (orthogonal_range_dirichletEmbedding (Ω := Ω))
  rw [← Submodule.dense_iff_topologicalClosure_eq_top, LinearMap.coe_range] at h
  exact h

/-! ### The Dirichlet eigenbasis -/

/-- **`H^1_0(Ω) ↪ L_2(Ω)` as a compact dense embedding**, for every bounded open set `Ω`
(`Rd.isCompactOperator_dirichletEmbedding`, `Rd.dirichletEmbedding_injective`,
`Rd.denseRange_dirichletEmbedding`). -/
noncomputable def dirichletCompactEmbedding (hΩ : Bornology.IsBounded (Ω : Set V)) :
    CompactDenseEmbedding (zeroBoundarySpace 1 Ω) (Lp ℂ 2 (volume.restrict (Ω : Set V))) where
  toCLM := dirichletEmbedding Ω
  isCompact := isCompactOperator_dirichletEmbedding hΩ
  injective := dirichletEmbedding_injective
  denseRange := denseRange_dirichletEmbedding

variable (hΩ : Bornology.IsBounded (Ω : Set V))

/-- The embedding of `Rd.dirichletCompactEmbedding` is the Dirichlet embedding. -/
@[simp]
theorem dirichletCompactEmbedding_toCLM :
    (dirichletCompactEmbedding hΩ).toCLM = dirichletEmbedding Ω :=
  rfl

/-- **The Dirichlet eigenbasis as a spectral scheme**: for a bounded open set `Ω`, the Hilbert
basis `(e_i)` of `L_2(Ω)` of eigenvectors of `J J†`, `J` the Dirichlet embedding, with the levels
`⌊σ_i⁻¹⌋₊` of the singular values (`CompactDenseEmbedding.spectralScheme`). With Mathlib's inner
product of `H^1`, `σ_i⁻² = 1 + λ_i/(4π²)` for the Dirichlet eigenvalue `λ_i`
(`Rd.one_add_dirichletEigenvalue_div`), so the level is `⌊√(1 + λ_i/(4π²))⌋₊`
(`Rd.dirichletScheme_level`), the frequency in the units of the Fourier scheme of the torus. The
factor `2π` rescales the levels only and changes no approximation space. -/
noncomputable def dirichletScheme :
    SpectralScheme (dirichletCompactEmbedding hΩ).index (Lp ℂ 2 (volume.restrict (Ω : Set V))) :=
  (dirichletCompactEmbedding hΩ).spectralScheme

/-- The singular values of the Dirichlet embedding are at most `1`
(`Rd.norm_dirichletEmbedding_le`). -/
theorem singularValue_dirichletCompactEmbedding_le_one
    (i : (dirichletCompactEmbedding hΩ).index) :
    (dirichletCompactEmbedding hΩ).singularValue i ≤ 1 :=
  ((dirichletCompactEmbedding hΩ).singularValue_le_norm i).trans norm_dirichletEmbedding_le

/-- **The Dirichlet eigenvalue** `λ_i = 4π² (σ_i⁻² - 1)` of the index `i`, `σ_i` the singular value
of the Dirichlet embedding; `-Δ φ_i = λ_i φ_i` weakly (`Rd.dirichletEigenfunction_weak`). These
are the eigenvalues `λ_n` of Brezis (Theorem 9.31). -/
noncomputable def dirichletEigenvalue (i : (dirichletCompactEmbedding hΩ).index) : ℝ :=
  4 * π ^ 2 * (((dirichletCompactEmbedding hΩ).singularValue i)⁻¹ ^ 2 - 1)

/-- The Dirichlet eigenvalues are nonnegative, since `σ_i ≤ 1`
(`Rd.singularValue_dirichletCompactEmbedding_le_one`). -/
theorem dirichletEigenvalue_nonneg (i : (dirichletCompactEmbedding hΩ).index) :
    0 ≤ dirichletEigenvalue hΩ i := by
  have hσ := (dirichletCompactEmbedding hΩ).singularValue_pos i
  have h1 : 1 ≤ ((dirichletCompactEmbedding hΩ).singularValue i)⁻¹ :=
    one_le_inv_iff₀.2 ⟨hσ, singularValue_dirichletCompactEmbedding_le_one hΩ i⟩
  have h2 : 1 ≤ ((dirichletCompactEmbedding hΩ).singularValue i)⁻¹ ^ 2 := one_le_pow₀ h1
  unfold dirichletEigenvalue
  have : 0 ≤ ((dirichletCompactEmbedding hΩ).singularValue i)⁻¹ ^ 2 - 1 := by linarith
  positivity

/-- `1 + λ_i/(4π²) = σ_i⁻²`. -/
theorem one_add_dirichletEigenvalue_div (i : (dirichletCompactEmbedding hΩ).index) :
    1 + dirichletEigenvalue hΩ i / (4 * π ^ 2) =
      ((dirichletCompactEmbedding hΩ).singularValue i)⁻¹ ^ 2 := by
  unfold dirichletEigenvalue
  field_simp
  ring

/-- **The level of a Dirichlet eigenfunction** is `⌊√(1 + λ_i/(4π²))⌋₊`. -/
theorem dirichletScheme_level (i : (dirichletCompactEmbedding hΩ).index) :
    (dirichletScheme hΩ).level i = ⌊Real.sqrt (1 + dirichletEigenvalue hΩ i / (4 * π ^ 2))⌋₊ := by
  rw [one_add_dirichletEigenvalue_div, Real.sqrt_sq
    (inv_nonneg.2 ((dirichletCompactEmbedding hΩ).singularValue_pos i).le)]
  rfl

/-- **The Dirichlet eigenfunction** `φ_i = σ_i⁻¹ v_i ∈ H^1_0(Ω)`, `v_i` the singular basis of the
Dirichlet embedding; its restriction to `Ω` is the basis vector `e_i` of `L_2(Ω)`
(`Rd.dirichletEmbedding_dirichletEigenfunction`). -/
noncomputable def dirichletEigenfunction (i : (dirichletCompactEmbedding hΩ).index) :
    zeroBoundarySpace 1 Ω :=
  ((((dirichletCompactEmbedding hΩ).singularValue i)⁻¹ : ℝ) : ℂ) •
    (dirichletCompactEmbedding hΩ).singularBasis i

/-- **`φ_i = e_i` on `Ω`**: the Dirichlet embedding maps the eigenfunction `φ_i` to the basis
vector `e_i` of the Dirichlet scheme, since `J v_i = σ_i e_i`
(`CompactDenseEmbedding.apply_singularBasis`). -/
theorem dirichletEmbedding_dirichletEigenfunction
    (i : (dirichletCompactEmbedding hΩ).index) :
    dirichletEmbedding Ω (dirichletEigenfunction hΩ i) = (dirichletScheme hΩ).basis i := by
  have h := (dirichletCompactEmbedding hΩ).apply_singularBasis i
  rw [dirichletCompactEmbedding_toCLM] at h
  rw [dirichletEigenfunction, map_smul, h, smul_smul, ← Complex.ofReal_mul,
    inv_mul_cancel₀ ((dirichletCompactEmbedding hΩ).singularValue_pos i).ne', Complex.ofReal_one,
    one_smul]
  rfl

/-! ### The weak Dirichlet eigenvalue equation -/

/-- **The inner product of `H^1_0(Ω)`**: for an orthonormal basis `(b_k)` of `V` and
`u, w ∈ H^1_0(Ω)`,
`⟨u, w⟩ = ⟨J u, J w⟩_{L_2(Ω)} + (2π)⁻² ∑_k ⟨∂_{b_k} ι u, ∂_{b_k} ι w⟩_{L_2(V)}`
(`Rd.inner_eq_of_hasWeakLineDeriv`, `Rd.inner_dirichletEmbedding`). -/
theorem inner_zeroBoundarySpace_eq {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (u w : zeroBoundarySpace 1 Ω) :
    ⟪u, w⟫_ℂ = ⟪dirichletEmbedding Ω u, dirichletEmbedding Ω w⟫_ℂ +
      (((2 * π)⁻¹ ^ 2 : ℝ) : ℂ) * ∑ k, ⟪weakDerivL2 (b k) ((u : RestrictionSpace 1 Ω) : H^{1}(V)),
        weakDerivL2 (b k) ((w : RestrictionSpace 1 Ω) : H^{1}(V))⟫_ℂ := by
  rw [inner_dirichletEmbedding]
  exact inner_eq_of_hasWeakLineDeriv b (fun k => hasWeakLineDeriv_weakDerivL2 _ _)
    (fun k => hasWeakLineDeriv_weakDerivL2 _ _)

/-- **The weak Dirichlet eigenvalue equation**: for every bounded open `Ω`, every orthonormal
basis `(b_k)` of `V`, every index `i` and every `w ∈ H^1_0(Ω)`,
`∑_k ⟨∂_{b_k} ι φ_i, ∂_{b_k} ι w⟩_{L_2(V)} = λ_i ⟨ι φ_i, ι w⟩_{L_2(V)}`, the weak form of
`-Δ φ_i = λ_i φ_i` with `φ_i = 0` on `∂Ω`. It is the weak eigenvalue equation
`⟨v_i, w⟩ = σ_i⁻² ⟨J v_i, J w⟩` of the singular basis
(`CompactDenseEmbedding.inner_singularBasis`) with the inner product of `H^1_0(Ω)`
(`Rd.inner_zeroBoundarySpace_eq`). -/
theorem dirichletEigenfunction_weak {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ V)
    (i : (dirichletCompactEmbedding hΩ).index) (w : zeroBoundarySpace 1 Ω) :
    ∑ k, ⟪weakDerivL2 (b k) ((dirichletEigenfunction hΩ i : RestrictionSpace 1 Ω) : H^{1}(V)),
        weakDerivL2 (b k) ((w : RestrictionSpace 1 Ω) : H^{1}(V))⟫_ℂ =
      (dirichletEigenvalue hΩ i : ℂ) *
        ⟪toL2 ((dirichletEigenfunction hΩ i : RestrictionSpace 1 Ω) : H^{1}(V)),
          toL2 ((w : RestrictionSpace 1 Ω) : H^{1}(V))⟫_ℂ := by
  have hφ : ⟪dirichletEigenfunction hΩ i, w⟫_ℂ =
      ((((dirichletCompactEmbedding hΩ).singularValue i)⁻¹ ^ 2 : ℝ) : ℂ) *
        ⟪dirichletEmbedding Ω (dirichletEigenfunction hΩ i), dirichletEmbedding Ω w⟫_ℂ := by
    -- the scalar multiplication of the subspace `H^1_0(Ω)` matches `inner_smul_left` up to
    -- unfolding instances, so the lemma is applied by unification instead of rewriting
    refine (inner_smul_left (𝕜 := ℂ) (E := zeroBoundarySpace 1 Ω)
      ((dirichletCompactEmbedding hΩ).singularBasis i) w _).trans ?_
    rw [dirichletEigenfunction, map_smul, inner_smul_left,
      (dirichletCompactEmbedding hΩ).inner_singularBasis i w,
      dirichletCompactEmbedding_toCLM]
    ring
  rw [inner_zeroBoundarySpace_eq b, inner_dirichletEmbedding] at hφ
  have hσ := (dirichletCompactEmbedding hΩ).ofReal_singularValue_ne_zero i
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  unfold dirichletEigenvalue
  push_cast at hφ ⊢
  field_simp at hφ ⊢
  linear_combination hφ

/-! ### `H^1_0(Ω)` as a spectral Sobolev space -/

/-- **`H^1_0(Ω)` in the Dirichlet eigenbasis**: `f ∈ L_2(Ω)` is the restriction of some
`w ∈ H^1_0(Ω)` iff `∑_i (1 + ⌊σ_i⁻¹⌋₊)² |⟨e_i, f⟩|² < ∞`, the Sobolev space of order `1` of the
Dirichlet scheme (`CompactDenseEmbedding.range_eq_range_sobolevEmbed`,
`SpectralScheme.mem_range_sobolevEmbed_iff`). -/
theorem exists_dirichletEmbedding_eq_iff (f : Lp ℂ 2 (volume.restrict (Ω : Set V))) :
    (∃ w, dirichletEmbedding Ω w = f) ↔
      Memℓp (fun i => ((1 + (dirichletScheme hΩ).level i : ℕ) : ℂ) *
        (dirichletScheme hΩ).basis.repr f i) 2 := by
  have h : (∃ w, dirichletEmbedding Ω w = f) ↔ f ∈ Set.range (dirichletCompactEmbedding hΩ).toCLM :=
    Iff.rfl
  rw [h, (dirichletCompactEmbedding hΩ).range_eq_range_sobolevEmbed,
    SpectralScheme.mem_range_sobolevEmbed_iff]
  have hw : ∀ i, (((dirichletCompactEmbedding hΩ).spectralScheme.weight 1 i : ℝ) : ℂ) =
      ((1 + (dirichletScheme hΩ).level i : ℕ) : ℂ) := fun i => by
    simp [SpectralScheme.weight, dirichletScheme]
  simp only [hw]
  rfl

/-- **The interpolation spaces between `L_2(Ω)` and `H^1_0(Ω)`**: for every bounded open `Ω`,
`0 < θ < 1` and `1 ≤ q ≤ ∞`, `(L_2(Ω), H^1_0(Ω))_{θ,q}` is the approximation space `A^θ_q` of the
Dirichlet scheme (`CompactDenseEmbedding.memKMethod_iff_memApprox`). -/
theorem memKMethod_dirichlet_iff {θ : ℝ} {q : ℝ≥0∞} (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q)
    {f : Lp ℂ 2 (volume.restrict (Ω : Set V))} :
    (InterpCouple.ofMap ((dirichletEmbedding Ω).restrictScalars ℝ)).MemKMethod θ q f ↔
      (dirichletScheme hΩ).toScheme.MemApprox θ q f :=
  (dirichletCompactEmbedding hΩ).memKMethod_iff_memApprox hθ hθ' hq

/-- **The interpolation spaces between `L_2(Ω)` and `H^1_0(Ω)` by dyadic blocks**: for every
bounded open `Ω`, `0 < θ < 1` and `1 ≤ q ≤ ∞`, `f ∈ (L_2(Ω), H^1_0(Ω))_{θ,q}` iff the dyadic
blocks of the expansion of `f` in the Dirichlet eigenbasis have finite `B^θ_{2,q}` norm
(`Rd.memKMethod_dirichlet_iff`, `SpectralScheme.memApprox_iff_blockNorm_lt_top`). -/
theorem memKMethod_dirichlet_iff_blockNorm_lt_top {θ : ℝ} {q : ℝ≥0∞} (hθ : 0 < θ) (hθ' : θ < 1)
    (hq : 1 ≤ q) {f : Lp ℂ 2 (volume.restrict (Ω : Set V))} :
    (InterpCouple.ofMap ((dirichletEmbedding Ω).restrictScalars ℝ)).MemKMethod θ q f ↔
      (dirichletScheme hΩ).projectionScheme.blockNorm θ q f < ∞ := by
  rw [memKMethod_dirichlet_iff hΩ hθ hθ' hq,
    (dirichletScheme hΩ).memApprox_iff_blockNorm_lt_top hθ hq]

end Rd
