/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Spectral.Blocks
public import LeanPool.FunctionSpaces.MeasureSpaces.Spectral.CompactEigenbasis
public import LeanPool.FunctionSpaces.ApproximationSpaces.Interpolation.ApproxSpaces
public import Mathlib.Analysis.InnerProductSpace.Positive

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Spectral schemes of compact dense embeddings

Let `J : V → H` be a compact, injective linear map with dense range between complex Hilbert
spaces (`CompactDenseEmbedding`), the model being `H^1_0(Ω) ↪ L_2(Ω)`.  The operator
`T = J J†` on `H` is compact, positive and injective (`CompactDenseEmbedding.gram`,
`CompactDenseEmbedding.isPositive_gram`), so it has a
Hilbert basis `(e_i)` of eigenvectors with eigenvalues `μ_i ≠ 0`
(`CompactDenseEmbedding.eigenBasis`, from `ContinuousLinearMap.eigenHilbertBasis`).  With the
**singular values** `σ_i = ‖J† e_i‖ > 0` one has `σ_i² = μ_i`, and
`v_i = σ_i⁻¹ J† e_i` is a Hilbert basis of `V` with `J v_i = σ_i e_i`
(`CompactDenseEmbedding.singularBasis`).  Consequently:

* the coefficients satisfy `⟨e_i, J u⟩ = σ_i ⟨v_i, u⟩`, so `f ∈ J(V)` iff
  `∑_i σ_i⁻² |⟨e_i, f⟩|² < ∞`, and `⟨v_i, w⟩_V = σ_i⁻² ⟨J v_i, J w⟩_H`, the weak form of the
  eigenvalue problem of the form `⟨·, ·⟩_V`;
* for every `ε > 0` only finitely many `σ_i` are at least `ε`, by compactness;
* the level `⌊σ_i⁻¹⌋₊` makes `(e_i)` a spectral scheme in `H`
  (`CompactDenseEmbedding.spectralScheme`), for which `J` satisfies Jackson's and Bernstein's
  inequalities of order `1` with constant `1`;
* hence `(H, J(V))_{θ,q} = A^θ_q` for `0 < θ < 1`, and `J(V)` is the Sobolev space of order `1`
  of the scheme; for `s > 0`, `f ∈ A^s_2` iff `∑_i σ_i^(-2s) |⟨e_i, f⟩|² < ∞`
  (`CompactDenseEmbedding.memApprox_two_iff`).

Every eigenvalue of `J J†` is some `μ_i`; in particular a nonzero `u ∈ V` with
`⟨u, w⟩_V = ⟨J u, J w⟩_H` for all `w` gives a singular value `1`
(`CompactDenseEmbedding.exists_singularValue_eq_one`).
-/

@[expose] public section

open Module.End Filter Topology
open scoped InnerProductSpace lp ENNReal

/-- A **compact dense embedding** of a complex Hilbert space `V` into a complex Hilbert space
`H`: a bounded linear map `V → H` that is compact, injective and has dense range, as
`H^1_0(Ω) ↪ L_2(Ω)` for a bounded open set `Ω`. -/
structure CompactDenseEmbedding (V H : Type*) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The embedding as a bounded linear map. -/
  toCLM : V →L[ℂ] H
  /-- The embedding is a compact operator. -/
  isCompact : IsCompactOperator toCLM
  /-- The embedding is injective. -/
  injective : Function.Injective toCLM
  /-- The embedding has dense range. -/
  denseRange : DenseRange toCLM

namespace CompactDenseEmbedding

variable {V H : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (J : CompactDenseEmbedding V H)

/-- The adjoint `J†` of a bounded operator, written as a postfix. -/
local postfix:max "†" => ContinuousLinearMap.adjoint

omit [CompleteSpace V] in
/-- The range of a compact dense embedding has trivial orthogonal complement. -/
theorem orthogonal_range_eq_bot : (LinearMap.range (J.toCLM : V →ₗ[ℂ] H))ᗮ = ⊥ := by
  rw [← Submodule.topologicalClosure_eq_top_iff, ← Submodule.dense_iff_topologicalClosure_eq_top,
    LinearMap.coe_range]
  exact J.denseRange

/-- The adjoint `J†` has trivial kernel, the orthogonal complement of the range of `J`. -/
theorem ker_adjoint : LinearMap.ker ((J.toCLM)† : H →ₗ[ℂ] V) = ⊥ := by
  rw [← J.toCLM.orthogonal_range, J.orthogonal_range_eq_bot]

/-- The adjoint `J†` is injective. -/
theorem adjoint_injective : Function.Injective (J.toCLM)† := by
  simpa using LinearMap.ker_eq_bot.1 J.ker_adjoint

/-! ### The operator `J J†` -/

/-- The operator `T = J J†` on `H`. -/
noncomputable def gram : H →L[ℂ] H := J.toCLM ∘L (J.toCLM)†

/-- `J J†` is compact, as `J` is. -/
theorem isCompactOperator_gram : IsCompactOperator J.gram :=
  J.isCompact.comp_clm _

/-- `J J†` is a positive operator: `⟨J J† f, f⟩ = ‖J† f‖² ≥ 0`
(`ContinuousLinearMap.isPositive_self_comp_adjoint`). -/
theorem isPositive_gram : J.gram.IsPositive :=
  ContinuousLinearMap.isPositive_self_comp_adjoint J.toCLM

/-- `J J†` is symmetric, being positive. -/
theorem isSymmetric_gram : (J.gram : H →ₗ[ℂ] H).IsSymmetric :=
  J.isPositive_gram.isSymmetric

/-- `J J†` is injective: its kernel is the kernel of `J†`. -/
theorem ker_gram : LinearMap.ker (J.gram : H →ₗ[ℂ] H) = ⊥ := by
  have h := J.toCLM.ker_self_comp_adjoint
  change LinearMap.ker (J.gram : H →ₗ[ℂ] H) = LinearMap.ker ((J.toCLM)† : H →ₗ[ℂ] V) at h
  rw [h, LinearMap.ker_eq_bot]
  exact J.adjoint_injective

/-! ### The eigenvector basis of `J J†` -/

/-- The index set of the eigenvector basis of `J J†`: pairs `⟨μ, j⟩` of an eigenvalue and an
index of a Hilbert basis of its eigenspace. -/
abbrev index : Type _ := J.gram.eigenIndex

/-- **The Hilbert basis of `H` of eigenvectors of `J J†`**, from Mathlib's spectral theorem
for compact self-adjoint operators (`ContinuousLinearMap.eigenHilbertBasis`). -/
noncomputable def eigenBasis : HilbertBasis J.index ℂ H :=
  ContinuousLinearMap.eigenHilbertBasis J.isSymmetric_gram
    (ContinuousLinearMap.orthogonalComplement_iSup_eigenspaces_eq_bot J.isCompactOperator_gram
      J.isSymmetric_gram)

/-- The basis vectors are the eigenvectors of `J J†`. -/
theorem coe_eigenBasis : ⇑J.eigenBasis = J.gram.eigenvector :=
  ContinuousLinearMap.coe_eigenHilbertBasis _ _

/-- `J J† e_i = μ_i e_i`, where the eigenvalue `μ_i` is the first component of the index. -/
theorem gram_eigenBasis (i : J.index) : J.gram (J.eigenBasis i) = i.1 • J.eigenBasis i := by
  rw [coe_eigenBasis]
  exact J.gram.apply_eigenvector i

/-- The eigenvalues of `J J†` in the index are nonzero, as `J J†` is injective. -/
theorem index_fst_ne_zero (i : J.index) : i.1 ≠ 0 :=
  J.gram.eigenIndex_fst_ne_zero J.ker_gram i

/-! ### Singular values and the singular basis -/

/-- The **singular value** `σ_i = ‖J† e_i‖`. -/
noncomputable def singularValue (i : J.index) : ℝ := ‖(J.toCLM)† (J.eigenBasis i)‖

/-- `⟨J† e_i, J† e_j⟩ = μ_j ⟨e_i, e_j⟩`. -/
theorem inner_adjoint_eigenBasis (i j : J.index) :
    ⟪(J.toCLM)† (J.eigenBasis i), (J.toCLM)† (J.eigenBasis j)⟫_ℂ =
      j.1 * ⟪J.eigenBasis i, J.eigenBasis j⟫_ℂ := by
  rw [ContinuousLinearMap.adjoint_inner_left, ← inner_smul_right, ← J.gram_eigenBasis]
  rfl

/-- **`σ_i² = μ_i`**: the eigenvalues of `J J†` are the squares of the singular values; in
particular they are real and positive. -/
theorem sq_singularValue (i : J.index) : (((J.singularValue i) ^ 2 : ℝ) : ℂ) = i.1 := by
  have h := J.inner_adjoint_eigenBasis i i
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, J.eigenBasis.orthonormal.1 i] at h
  simpa [singularValue] using h

/-- The singular values are positive. -/
theorem singularValue_pos (i : J.index) : 0 < J.singularValue i := by
  refine (norm_nonneg _).lt_of_ne fun h => J.index_fst_ne_zero i ?_
  rw [← J.sq_singularValue i, singularValue, ← h]
  simp

/-- The singular values are nonzero as complex numbers. -/
theorem ofReal_singularValue_ne_zero (i : J.index) : ((J.singularValue i : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.2 (J.singularValue_pos i).ne'

/-- `‖σ_i⁻¹ z‖ = σ_i⁻¹ ‖z‖` for every complex number `z`. -/
theorem norm_inv_singularValue_mul (i : J.index) (z : ℂ) :
    ‖((J.singularValue i)⁻¹ : ℂ) * z‖ = (J.singularValue i)⁻¹ * ‖z‖ := by
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (J.singularValue_pos i)]

/-- The singular values are at most `‖J‖`. -/
theorem singularValue_le_norm (i : J.index) : J.singularValue i ≤ ‖J.toCLM‖ := by
  refine ((J.toCLM)†.le_opNorm _).trans ?_
  rw [J.eigenBasis.orthonormal.1 i, mul_one, LinearIsometryEquiv.norm_map]

/-- The singular vector `v_i = σ_i⁻¹ J† e_i` in `V`. -/
noncomputable def singularVector (i : J.index) : V :=
  (((J.singularValue i)⁻¹ : ℝ) : ℂ) • (J.toCLM)† (J.eigenBasis i)

/-- `J† e_i = σ_i v_i`. -/
theorem adjoint_eigenBasis_eq (i : J.index) :
    (J.toCLM)† (J.eigenBasis i) = ((J.singularValue i : ℝ) : ℂ) • J.singularVector i := by
  rw [singularVector, smul_smul, ← Complex.ofReal_mul, mul_inv_cancel₀ (J.singularValue_pos i).ne',
    Complex.ofReal_one, one_smul]

/-- The singular vectors are orthonormal, since `⟨v_i, v_j⟩ = σ_i⁻¹ σ_j⁻¹ μ_j ⟨e_i, e_j⟩` and
`σ_i² = μ_i`. -/
theorem orthonormal_singularVector : Orthonormal ℂ J.singularVector := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  simp only [singularVector, inner_smul_left, inner_smul_right, J.inner_adjoint_eigenBasis,
    orthonormal_iff_ite.1 J.eigenBasis.orthonormal, Complex.conj_ofReal]
  split_ifs with h
  · subst h
    rw [← J.sq_singularValue i]
    have := J.ofReal_singularValue_ne_zero i
    push_cast
    field_simp
  · simp

/-- A vector `y ∈ H` orthogonal to every `e_i` is zero. -/
theorem eq_zero_of_forall_inner_eigenBasis {y : H} (hy : ∀ i, ⟪J.eigenBasis i, y⟫_ℂ = 0) :
    y = 0 := by
  refine J.eigenBasis.repr.map_eq_zero_iff.1 (lp.ext (funext fun i => ?_))
  rw [J.eigenBasis.repr_apply_apply, hy]
  rfl

/-- The span of the singular vectors has trivial orthogonal complement: if `w ⊥ v_i` for all
`i`, then `⟨e_i, J w⟩ = σ_i ⟨v_i, w⟩ = 0` for all `i`, so `J w = 0` and `w = 0`. -/
theorem orthogonal_span_singularVector_eq_bot :
    (Submodule.span ℂ (Set.range J.singularVector))ᗮ = ⊥ := by
  refine le_antisymm (fun w hw => ?_) bot_le
  have hv : ∀ i, ⟪J.singularVector i, w⟫_ℂ = 0 := fun i =>
    (Submodule.mem_orthogonal _ w).1 hw _ (Submodule.subset_span ⟨i, rfl⟩)
  have hJw : J.toCLM w = 0 := J.eq_zero_of_forall_inner_eigenBasis fun i => by
    rw [← ContinuousLinearMap.adjoint_inner_left, J.adjoint_eigenBasis_eq, inner_smul_left, hv,
      mul_zero]
  rw [Submodule.mem_bot]
  exact J.injective (by rw [hJw, map_zero])

/-- **The singular basis**: the Hilbert basis `v_i = σ_i⁻¹ J† e_i` of `V`. -/
noncomputable def singularBasis : HilbertBasis J.index ℂ V :=
  HilbertBasis.mkOfOrthogonalEqBot J.orthonormal_singularVector
    J.orthogonal_span_singularVector_eq_bot

/-- The vectors of the singular basis are the singular vectors. -/
theorem coe_singularBasis : ⇑J.singularBasis = J.singularVector :=
  HilbertBasis.coe_mkOfOrthogonalEqBot _ _

/-- `J† e_i = σ_i v_i`. -/
theorem adjoint_eigenBasis (i : J.index) :
    (J.toCLM)† (J.eigenBasis i) = ((J.singularValue i : ℝ) : ℂ) • J.singularBasis i := by
  rw [coe_singularBasis, J.adjoint_eigenBasis_eq]

/-- `J v_i = σ_i e_i`. -/
theorem apply_singularBasis (i : J.index) :
    J.toCLM (J.singularBasis i) = ((J.singularValue i : ℝ) : ℂ) • J.eigenBasis i := by
  have h : J.toCLM ((J.toCLM)† (J.eigenBasis i)) = i.1 • J.eigenBasis i := J.gram_eigenBasis i
  rw [J.adjoint_eigenBasis, map_smul, ← J.sq_singularValue i] at h
  refine smul_right_injective H (J.ofReal_singularValue_ne_zero i) ?_
  simp only
  rw [h, smul_smul, Complex.ofReal_pow, sq]

/-- **Every eigenvalue of `J J†` occurs in the index**: if `J J† y = μ y` for some `y ≠ 0`, then
`μ = μ_i` for some `i`. Otherwise `y` is orthogonal to every `e_i`, since
`μ_i ⟨e_i, y⟩ = ⟨J J† e_i, y⟩ = ⟨e_i, J J† y⟩ = μ ⟨e_i, y⟩` with `μ_i = σ_i²` real. -/
theorem exists_index_fst_eq_of_gram_apply_eq_smul {μ : ℂ} {y : H} (hy : J.gram y = μ • y)
    (hy0 : y ≠ 0) : ∃ i : J.index, i.1 = μ := by
  by_contra h
  push Not at h
  refine hy0 (J.eq_zero_of_forall_inner_eigenBasis fun i => ?_)
  have hs : ⟪J.gram (J.eigenBasis i), y⟫_ℂ = ⟪J.eigenBasis i, J.gram y⟫_ℂ :=
    J.isSymmetric_gram (J.eigenBasis i) y
  have hr : (starRingEnd ℂ) i.1 = i.1 := by rw [← J.sq_singularValue i, Complex.conj_ofReal]
  rw [J.gram_eigenBasis, hy, inner_smul_left, inner_smul_right, hr] at hs
  have h0 : (i.1 - μ) * ⟪J.eigenBasis i, y⟫_ℂ = 0 := by rw [sub_mul, hs, sub_self]
  exact (mul_eq_zero.1 h0).resolve_left (sub_ne_zero.2 (h i))

/-- **A singular value `1`**: if some `u ≠ 0` in `V` satisfies `⟨u, w⟩_V = ⟨J u, J w⟩_H` for
every `w ∈ V`, then `σ_i = 1` for some `i`. Indeed `J† J u = u`, so `J u ≠ 0` is an eigenvector
of `J J†` with eigenvalue `1 = σ_i²`
(`CompactDenseEmbedding.exists_index_fst_eq_of_gram_apply_eq_smul`). -/
theorem exists_singularValue_eq_one {u : V} (hu0 : u ≠ 0)
    (hu : ∀ w, ⟪u, w⟫_ℂ = ⟪J.toCLM u, J.toCLM w⟫_ℂ) : ∃ i : J.index, J.singularValue i = 1 := by
  have hadj : (J.toCLM)† (J.toCLM u) = u :=
    ext_inner_right ℂ fun w => by rw [ContinuousLinearMap.adjoint_inner_left, hu]
  have hg : J.gram (J.toCLM u) = (1 : ℂ) • J.toCLM u := by
    rw [one_smul]
    exact congrArg J.toCLM hadj
  have hJu : J.toCLM u ≠ 0 := fun h0 => hu0 (J.injective (by rw [h0, map_zero]))
  obtain ⟨i, hi⟩ := J.exists_index_fst_eq_of_gram_apply_eq_smul hg hJu
  refine ⟨i, (pow_eq_one_iff_of_nonneg (J.singularValue_pos i).le two_ne_zero).1 ?_⟩
  rw [← Complex.ofReal_eq_one, J.sq_singularValue i, hi]

/-! ### Coefficients -/

/-- **`⟨e_i, J u⟩ = σ_i ⟨v_i, u⟩`**: the coefficients of `J u` in the eigenvector basis are
`σ_i` times those of `u` in the singular basis. -/
theorem repr_apply (u : V) (i : J.index) :
    J.eigenBasis.repr (J.toCLM u) i = (J.singularValue i : ℂ) * J.singularBasis.repr u i := by
  rw [J.eigenBasis.repr_apply_apply, J.singularBasis.repr_apply_apply,
    ← ContinuousLinearMap.adjoint_inner_left, J.adjoint_eigenBasis, inner_smul_left,
    Complex.conj_ofReal]

/-- The coefficients of `J (∑ c_i v_i)` are `σ_i c_i`. -/
theorem repr_apply_repr_symm (c : ℓ²(J.index, ℂ)) (i : J.index) :
    J.eigenBasis.repr (J.toCLM (J.singularBasis.repr.symm c)) i =
      (J.singularValue i : ℂ) * c i := by
  rw [repr_apply, LinearIsometryEquiv.apply_symm_apply]

/-- The singular coefficients of a preimage: if `J u = f`, then
`⟨v_i, u⟩ = σ_i⁻¹ ⟨e_i, f⟩`. -/
theorem repr_singularBasis_eq {u : V} {f : H} (h : J.toCLM u = f) (i : J.index) :
    J.singularBasis.repr u i = ((J.singularValue i)⁻¹ : ℂ) * J.eigenBasis.repr f i := by
  rw [← h, repr_apply, ← mul_assoc, inv_mul_cancel₀ (J.ofReal_singularValue_ne_zero i), one_mul]

/-- **The range of `J`**: `f ∈ J(V)` if and only if `∑_i σ_i⁻² |⟨e_i, f⟩|² < ∞`. -/
theorem mem_range_iff (f : H) :
    f ∈ Set.range J.toCLM ↔
      Memℓp (fun i => ((J.singularValue i)⁻¹ : ℂ) * J.eigenBasis.repr f i) 2 := by
  constructor
  · rintro ⟨u, rfl⟩
    convert lp.memℓp (J.singularBasis.repr u) using 1
    funext i
    exact (J.repr_singularBasis_eq rfl i).symm
  · intro h
    refine ⟨J.singularBasis.repr.symm ⟨_, h⟩, J.eigenBasis.repr.injective
      (lp.ext (funext fun i => ?_))⟩
    rw [repr_apply_repr_symm]
    change (J.singularValue i : ℂ) * (((J.singularValue i)⁻¹ : ℂ) * J.eigenBasis.repr f i) = _
    rw [← mul_assoc, mul_inv_cancel₀ (J.ofReal_singularValue_ne_zero i), one_mul]

/-- **The norm of the preimage**: if `J u = f`, then `‖u‖² = ∑_i σ_i⁻² |⟨e_i, f⟩|²`. -/
theorem norm_sq_eq_of_apply_eq {u : V} {f : H} (h : J.toCLM u = f) :
    ‖u‖ ^ 2 = ∑' i, (J.singularValue i)⁻¹ ^ 2 * ‖J.eigenBasis.repr f i‖ ^ 2 := by
  have hP := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (J.singularBasis.repr u)
  simp only [ENNReal.toReal_ofNat, Real.rpow_two, LinearIsometryEquiv.norm_map] at hP
  rw [hP]
  congr 1; funext i
  rw [← h, repr_apply, norm_mul, mul_pow, ← mul_assoc, Complex.norm_real, Real.norm_eq_abs,
    sq_abs, ← mul_pow, inv_mul_cancel₀ (J.singularValue_pos i).ne', one_pow, one_mul]

/-- **The weak eigenvalue equation**: `⟨v_i, w⟩_V = σ_i⁻² ⟨J v_i, J w⟩_H` for every `w ∈ V`.
For `V = H^1_0(Ω)` with the inner product `⟨u, w⟩ + (2π)⁻²⟨∇u, ∇w⟩` and `H = L_2(Ω)`, this is
the weak form of `-Δ v_i = λ_i v_i` for the Dirichlet eigenvalue `λ_i`, with
`σ_i⁻² = 1 + λ_i/(4π²)`. -/
theorem inner_singularBasis (i : J.index) (w : V) :
    ⟪J.singularBasis i, w⟫_ℂ =
      (((J.singularValue i)⁻¹ ^ 2 : ℝ) : ℂ) * ⟪J.toCLM (J.singularBasis i), J.toCLM w⟫_ℂ := by
  have := J.ofReal_singularValue_ne_zero i
  rw [J.apply_singularBasis, inner_smul_left, Complex.conj_ofReal,
    ← ContinuousLinearMap.adjoint_inner_left, J.adjoint_eigenBasis, inner_smul_left,
    Complex.conj_ofReal]
  push_cast
  field_simp

/-! ### Finitely many large singular values -/

/-- For `i ≠ j`, `‖J v_i - J v_j‖ ≥ σ_i`, since the coefficient of
`J v_i - J v_j = σ_i e_i - σ_j e_j` at `e_i` is `σ_i`. -/
theorem singularValue_le_norm_sub {i j : J.index} (hij : i ≠ j) :
    J.singularValue i ≤ ‖J.toCLM (J.singularBasis i) - J.toCLM (J.singularBasis j)‖ := by
  have h := norm_inner_le_norm (𝕜 := ℂ) (J.eigenBasis i)
    (J.toCLM (J.singularBasis i) - J.toCLM (J.singularBasis j))
  have hii : ⟪J.eigenBasis i, J.eigenBasis i⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, J.eigenBasis.orthonormal.1 i]; simp
  rw [inner_sub_right, J.apply_singularBasis, J.apply_singularBasis, inner_smul_right,
    inner_smul_right, hii, J.eigenBasis.orthonormal.2 hij, mul_zero, sub_zero, mul_one,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (J.singularValue_pos i),
    J.eigenBasis.orthonormal.1 i, one_mul] at h
  rwa [J.apply_singularBasis, J.apply_singularBasis]

/-- **Only finitely many singular values are at least `ε > 0`.**  Otherwise there are
infinitely many `v_i` in the unit ball whose images `J v_i` are `ε`-separated
(`CompactDenseEmbedding.singularValue_le_norm_sub`), against the compactness of the closure of
the image of the unit ball (`IsCompactOperator.isCompact_closure_image_closedBall`,
`IsCompact.tendsto_subseq`). -/
theorem finite_setOf_le_singularValue {ε : ℝ} (hε : 0 < ε) :
    {i | ε ≤ J.singularValue i}.Finite := by
  by_contra hinf
  let e := Set.Infinite.natEmbedding _ hinf
  obtain ⟨y, -, φ, hφ, hlim⟩ := (IsCompactOperator.isCompact_closure_image_closedBall
    (f := (J.toCLM : V →ₗ[ℂ] H)) J.isCompact 1).tendsto_subseq
    (x := fun n => J.toCLM (J.singularBasis (e n)))
    (fun n => subset_closure ⟨J.singularBasis (e n),
      mem_closedBall_zero_iff.2 (J.singularBasis.orthonormal.1 _).le, rfl⟩)
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 hlim.cauchySeq ε hε
  have h1 := hN (N + 1) (Nat.le_succ N)
  rw [Function.comp_apply, Function.comp_apply, dist_eq_norm] at h1
  have hne : (e (φ (N + 1)) : J.index) ≠ e (φ N) := fun h =>
    Nat.succ_ne_self N (hφ.injective (e.injective (Subtype.ext h)))
  exact absurd ((e (φ (N + 1))).2.trans (J.singularValue_le_norm_sub hne)) (not_le.2 h1)

/-! ### The spectral scheme of the embedding -/

/-- The **level** `⌊σ_i⁻¹⌋₊` of the eigenvector `e_i`. -/
noncomputable def level (i : J.index) : ℕ := ⌊(J.singularValue i)⁻¹⌋₊

/-- `⌊σ_i⁻¹⌋₊ ≤ σ_i⁻¹`. -/
theorem level_le_inv_singularValue (i : J.index) : (J.level i : ℝ) ≤ (J.singularValue i)⁻¹ :=
  Nat.floor_le (inv_nonneg.2 (J.singularValue_pos i).le)

/-- `σ_i⁻¹ < ⌊σ_i⁻¹⌋₊ + 1`. -/
theorem inv_singularValue_lt_level_add_one (i : J.index) :
    (J.singularValue i)⁻¹ < J.level i + 1 :=
  Nat.lt_floor_add_one _

/-- A level below `n` means `σ_i⁻¹ < n`. -/
theorem inv_singularValue_lt_of_level_lt {n : ℕ} {i : J.index} (h : J.level i < n) :
    (J.singularValue i)⁻¹ < n :=
  (Nat.floor_lt (inv_nonneg.2 (J.singularValue_pos i).le)).1 h

/-- A level at least `n ≥ 1` means `σ_i ≤ n⁻¹`. -/
theorem singularValue_le_of_le_level {n : ℕ} (hn : 1 ≤ n) {i : J.index} (h : n ≤ J.level i) :
    J.singularValue i ≤ (n : ℝ)⁻¹ := by
  have hle : (n : ℝ) ≤ (J.singularValue i)⁻¹ :=
    (Nat.cast_le.2 h).trans (J.level_le_inv_singularValue i)
  exact (le_inv_comm₀ (by exact_mod_cast hn) (J.singularValue_pos i)).1 hle

/-- The levels have finite level sets: `level i < n` gives `σ_i⁻¹ < n`, so
`σ_i ≥ (n + 1)⁻¹`, which holds for finitely many `i`
(`CompactDenseEmbedding.finite_setOf_le_singularValue`). -/
theorem finite_level (n : ℕ) : {i | J.level i < n}.Finite :=
  (J.finite_setOf_le_singularValue (ε := ((n : ℝ) + 1)⁻¹) (by positivity)).subset fun i hi => by
    have h := J.inv_singularValue_lt_of_level_lt hi
    change ((n : ℝ) + 1)⁻¹ ≤ J.singularValue i
    exact (inv_le_comm₀ (by positivity) (J.singularValue_pos i)).2 (by linarith)

/-- **The spectral scheme of a compact dense embedding**: the eigenvector basis `(e_i)` of
`J J†` with the levels `⌊σ_i⁻¹⌋₊`. -/
noncomputable def spectralScheme : SpectralScheme J.index H where
  basis := J.eigenBasis
  level := J.level
  finite_level := J.finite_level

/-- The basis of the spectral scheme is the eigenvector basis. -/
@[simp]
theorem spectralScheme_basis : J.spectralScheme.basis = J.eigenBasis := rfl

/-- The levels of the spectral scheme are `⌊σ_i⁻¹⌋₊`. -/
@[simp]
theorem spectralScheme_level : J.spectralScheme.level = J.level := rfl

/-- **The truncation error of `J u`**: `‖J u - P_n J u‖ ≤ n⁻¹ ‖u‖` for `n ≥ 1`, by Parseval's
identity, since only coefficients `σ_i ⟨v_i, u⟩` of level `≥ n` remain and `σ_i ≤ n⁻¹`
there. -/
theorem norm_sub_truncate_le {n : ℕ} (hn : 1 ≤ n) (u : V) :
    ‖J.toCLM u - J.spectralScheme.truncate n (J.toCLM u)‖ ≤ (n : ℝ)⁻¹ * ‖u‖ := by
  rw [← J.eigenBasis.repr.norm_map, ← J.singularBasis.repr.norm_map u]
  calc ‖J.eigenBasis.repr (J.toCLM u - J.spectralScheme.truncate n (J.toCLM u))‖
      ≤ ‖((((n : ℝ)⁻¹ : ℝ)) : ℂ) • J.singularBasis.repr u‖ := by
        refine lp.norm_mono (by norm_num) fun i => ?_
        have h := J.spectralScheme.repr_sub_truncate n (J.toCLM u) i
        rw [spectralScheme_basis, spectralScheme_level] at h
        rw [h, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
        split_ifs with hi
        · simp only [norm_zero]; positivity
        · rw [repr_apply, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
            Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (J.singularValue_pos i),
            abs_of_pos (by positivity)]
          gcongr
          exact J.singularValue_le_of_le_level hn (not_lt.1 hi)
    _ = (n : ℝ)⁻¹ * ‖J.singularBasis.repr u‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- **Jackson's inequality** for `J(V)`: `E_n(J u) ≤ n⁻¹ ‖u‖`, constant `1`. -/
theorem jacksonBound :
    ApproximationScheme.JacksonBound (J.toCLM.restrictScalars ℝ) J.spectralScheme.toScheme 1 1 := by
  intro n hn u
  refine (ENNReal.toReal_mono eNorm_ne_top (ApproximationScheme.approxError_le_of_mem
    (J.spectralScheme.truncate_mem_span n (J.toCLM u)) _)).trans ?_
  rw [toReal_eNorm, one_mul, Real.rpow_neg_one]
  exact J.norm_sub_truncate_le hn u

/-- **Bernstein's inequality** for `J(V)`: every `a ∈ A_n` is `J u` with `‖u‖ ≤ n ‖a‖`, since
`a` has only coefficients of level `< n`, where `σ_i⁻¹ < n`. -/
theorem liftBound :
    ApproximationScheme.LiftBound (J.toCLM.restrictScalars ℝ) J.spectralScheme.toScheme 1 1 := by
  intro n hn a ha
  have hle : ∀ i, ‖((J.singularValue i)⁻¹ : ℂ) * J.eigenBasis.repr a i‖ ≤
      (n : ℝ) * ‖J.eigenBasis.repr a i‖ := fun i => by
    rw [J.norm_inv_singularValue_mul]
    by_cases hi : J.level i < n
    · gcongr; exact (J.inv_singularValue_lt_of_level_lt hi).le
    · have h0 := J.spectralScheme.repr_eq_zero_of_mem_span ha (i := i) (not_lt.1 hi)
      rw [spectralScheme_basis] at h0
      rw [h0]; simp
  have hmem : Memℓp (fun i => ((J.singularValue i)⁻¹ : ℂ) * J.eigenBasis.repr a i) 2 :=
    (((lp.memℓp (J.eigenBasis.repr a)).norm).const_mul (n : ℝ)).mono hle
  obtain ⟨u, hu⟩ := (J.mem_range_iff a).2 hmem
  refine ⟨u, hu, ?_⟩
  rw [Real.rpow_one, one_mul, ← J.singularBasis.repr.norm_map, ← J.eigenBasis.repr.norm_map a]
  calc ‖J.singularBasis.repr u‖ ≤ ‖((n : ℝ) : ℂ) • J.eigenBasis.repr a‖ := by
        refine lp.norm_mono (by norm_num) fun i => ?_
        change ‖J.singularBasis.repr u i‖ ≤ ‖(((n : ℝ) : ℂ) • J.eigenBasis.repr a) i‖
        rw [J.repr_singularBasis_eq hu, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
          norm_mul ((n : ℝ) : ℂ), Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (Nat.cast_nonneg n)]
        exact hle i
    _ = (n : ℝ) * ‖J.eigenBasis.repr a‖ := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg n)]

/-! ### Interpolation and the Sobolev space of order one -/

/-- **The interpolation spaces of a compact dense embedding**: for `0 < θ < 1` and
`1 ≤ q ≤ ∞`, `(H, J(V))_{θ,q} = A^θ_q` for the spectral scheme, from Jackson's and Bernstein's
inequalities (`ApproximationScheme.memKMethod_ofMap_iff_memApprox`). -/
theorem memKMethod_iff_memApprox {θ : ℝ} {q : ℝ≥0∞} (hθ : 0 < θ) (hθ' : θ < 1) (hq : 1 ≤ q)
    {f : H} :
    (InterpCouple.ofMap (J.toCLM.restrictScalars ℝ)).MemKMethod θ q f ↔
      J.spectralScheme.toScheme.MemApprox θ q f := by
  have h := ApproximationScheme.memKMethod_ofMap_iff_memApprox J.jacksonBound zero_le_one
    J.liftBound zero_le_one one_pos hθ hθ' hq (f := f)
  rwa [mul_one] at h

/-- `σ_i⁻¹ ≤ 1 + ⌊σ_i⁻¹⌋₊`. -/
theorem inv_singularValue_le_one_add_level (i : J.index) :
    (J.singularValue i)⁻¹ ≤ 1 + J.level i := by
  linarith [J.inv_singularValue_lt_level_add_one i]

/-- `1 + ⌊σ_i⁻¹⌋₊ ≤ (1 + ‖J‖) σ_i⁻¹`, since `1 = σ_i σ_i⁻¹ ≤ ‖J‖ σ_i⁻¹`. -/
theorem one_add_level_le (i : J.index) :
    1 + (J.level i : ℝ) ≤ (1 + ‖J.toCLM‖) * (J.singularValue i)⁻¹ := by
  have hσ := J.singularValue_pos i
  have h1 : 1 ≤ ‖J.toCLM‖ * (J.singularValue i)⁻¹ := by
    rw [← mul_inv_cancel₀ hσ.ne']
    exact mul_le_mul_of_nonneg_right (J.singularValue_le_norm i) (inv_nonneg.2 hσ.le)
  linarith [J.level_le_inv_singularValue i]

/-- **`J(V)` is the Sobolev space of order `1` of the spectral scheme**:
`J(V) = {f : ∑_i (1 + ⌊σ_i⁻¹⌋₊)² |⟨e_i, f⟩|² < ∞}`, by
`σ_i⁻¹ ≤ 1 + ⌊σ_i⁻¹⌋₊ ≤ (1 + ‖J‖) σ_i⁻¹` and `CompactDenseEmbedding.mem_range_iff`. -/
theorem range_eq_range_sobolevEmbed :
    Set.range J.toCLM = Set.range (J.spectralScheme.sobolevEmbed 1 zero_le_one) := by
  ext f
  have hw : ∀ i, J.spectralScheme.weight 1 i = 1 + J.level i := fun i => by
    simp [SpectralScheme.weight]
  rw [J.mem_range_iff, SpectralScheme.mem_range_sobolevEmbed_iff, spectralScheme_basis]
  constructor
  · intro h
    refine ((h.norm).const_mul (1 + ‖J.toCLM‖)).mono fun i => ?_
    rw [J.norm_inv_singularValue_mul, norm_mul, hw, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show (0 : ℝ) < 1 + J.level i by positivity), ← mul_assoc]
    gcongr
    exact J.one_add_level_le i
  · intro h
    refine h.mono' fun i => ?_
    rw [J.norm_inv_singularValue_mul, norm_mul, hw, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (show (0 : ℝ) < 1 + J.level i by positivity)]
    gcongr
    exact J.inv_singularValue_le_one_add_level i

/-- **`A^s_2` by the singular values**: for `s > 0`, `f ∈ H` lies in the approximation space
`A^s_2` of the spectral scheme iff `∑_i σ_i^(-2s) |⟨e_i, f⟩|² < ∞`, that is,
`(σ_i^(-s) ⟨e_i, f⟩)_i ∈ ℓ_2`: by
`SpectralScheme.memApprox_two_iff` the weights are `(1 + ⌊σ_i⁻¹⌋₊)^s`, and
`σ_i⁻¹ ≤ 1 + ⌊σ_i⁻¹⌋₊ ≤ (1 + ‖J‖) σ_i⁻¹`. -/
theorem memApprox_two_iff {s : ℝ} (hs : 0 < s) (f : H) :
    J.spectralScheme.toScheme.MemApprox s 2 f ↔
      Memℓp (fun i => (((J.singularValue i)⁻¹ ^ s : ℝ) : ℂ) * J.eigenBasis.repr f i) 2 := by
  have hw : ∀ i, J.spectralScheme.weight s i = (1 + J.level i) ^ s := fun i => by
    simp [SpectralScheme.weight]
  have hσ : ∀ i, 0 ≤ (J.singularValue i)⁻¹ := fun i => inv_nonneg.2 (J.singularValue_pos i).le
  rw [J.spectralScheme.memApprox_two_iff hs f, spectralScheme_basis]
  constructor
  · intro h
    refine h.mono' fun i => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hσ i) s), hw,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) s)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (hσ i) (J.inv_singularValue_le_one_add_level i) hs.le) (norm_nonneg _)
  · intro h
    refine ((h.norm).const_mul ((1 + ‖J.toCLM‖) ^ s)).mono fun i => ?_
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (hσ i) s), hw,
      abs_of_nonneg (Real.rpow_nonneg (by positivity) s), ← mul_assoc,
      ← Real.mul_rpow (by positivity) (hσ i)]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (by positivity) (J.one_add_level_le i) hs.le) (norm_nonneg _)

end CompactDenseEmbedding
