/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.MeasureSpaces.Spectral.Blocks
public import LeanPool.FunctionSpaces.MeasureSpaces.Sobolev.Embeddings
public import Mathlib.MeasureTheory.Function.L2Space

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Continuous spectral bases

Let `M` be a topological space with a finite Borel measure `μ`. A **continuous spectral basis**
of `L_2(μ)` (`ContinuousSpectralBasis`) is a spectral scheme in `L_2(μ)`, a Hilbert basis `(e_i)`
with a level `λ : ι → ℕ` and finitely many basis elements of each level, whose elements are the
`L_2` classes of bounded continuous functions `eTilde_i` (`ContinuousSpectralBasis.basisFun`). The
model is the eigenbasis of the Laplace–Beltrami operator of a compact Riemannian manifold,
continuous by elliptic regularity, with `λ(i) = ⌊√λ_i⌋`. The Dirichlet eigenbasis of a bounded
open set, the Neumann eigenbasis of a bounded Lipschitz domain and the eigenbasis of the chart
form of a compact manifold are spectral schemes (`Rd.dirichletScheme`,
`Rd.BoundedLipschitzDomain.neumannScheme`, `Manifold.BesovAtlas.chartScheme`); the boundedness
and continuity of their elements is elliptic regularity, a later goal. The Fourier basis of the
torus is a continuous spectral basis (`Torus.fourierEigenbasis`).

The functions `eTilde_i` of level `< n` span the space `basisSpan n` of bounded continuous functions
(`ContinuousSpectralBasis.basisSpan`), and these spaces form a scheme of functions
(`ContinuousSpectralBasis.basisScheme`). Its classes in `L_2` are the spectral scheme
(`ContinuousSpectralBasis.toLp_basisScheme_eq`), so the spectral theory applies:

* **`B^s_{2,2} = H^s`** (`ContinuousSpectralBasis.memBesov_two_two_iff`): for `s > 0`,
  `f ∈ L_2(μ)` lies in `B^s_{2,2}` iff `∑_i (1 + λ(i))^(2s) |⟨e_i, f⟩|² < ∞`;
* **Littlewood–Paley blocks** (`ContinuousSpectralBasis.memBesov_two_iff_blockNorm_lt_top`) with
  sharp cut-offs at the levels `2^k`;
* **the Sobolev space** `H^s` as a Sobolev space for the scheme in `L_2`
  (`ContinuousSpectralBasis.sobolevSpace`), with Jackson's and Bernstein's inequalities of
  constant `1`.

The Besov spaces `B^s_{p,q}` of the scheme are defined for every `1 ≤ p ≤ ∞` by
`FunctionScheme.MemBesov`; their embeddings need the Nikolskii property
`FunctionScheme.HasNikolskii`, which the torus has (`Torus.hasNikolskii_fourierEigenbasis`).
-/

@[expose] public section

open MeasureTheory FunctionScheme
open scoped ENNReal BoundedContinuousFunction lp

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]

/-- A **continuous spectral basis** of `L_2(μ)`: a Hilbert basis `(e_i)` of `L_2(μ)` with a level
`λ : ι → ℕ` that takes each value finitely often (a spectral scheme), together with bounded
continuous functions `eTilde_i` whose `L_2` classes are the `e_i`. The eigenfunctions of the
Laplace–Beltrami operator of a compact Riemannian manifold, with the level `⌊√λ⌋` of the
eigenvalue `λ`, are the model; their continuity is elliptic regularity. On a bounded open set of
`ℝ^d` the Dirichlet eigenbasis is a spectral scheme (`Rd.dirichletScheme`), and so are the Neumann
eigenbasis of a bounded Lipschitz domain (`Rd.BoundedLipschitzDomain.neumannScheme`) and the
eigenbasis of the chart form of a compact manifold (`Manifold.BesovAtlas.chartScheme`). The data of
the structure are the basis, its levels and its continuous representatives; it enters the
theorems as a hypothesis, and the Fourier basis of the torus is an instance
(`Torus.fourierEigenbasis`). -/
structure ContinuousSpectralBasis (ι : Type*) (μ : Measure M) [IsFiniteMeasure μ]
    extends SpectralScheme ι (Lp ℂ 2 μ) where
  /-- The continuous representatives of the basis elements. -/
  basisFun : ι → (M →ᵇ ℂ)
  /-- The `L_2` class of `eTilde_i` is the basis element `e_i`. -/
  toLp_basisFun : ∀ i, BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ (basisFun i) = basis i

namespace ContinuousSpectralBasis

variable {ι : Type*} {μ : Measure M} [IsFiniteMeasure μ] (B : ContinuousSpectralBasis ι μ)

/-- The **span of the continuous basis functions `eTilde_i` of level `< n`**, a space of bounded
continuous functions. -/
noncomputable def basisSpan (n : ℕ) : Submodule ℂ (M →ᵇ ℂ) :=
  Submodule.span ℂ (B.basisFun '' {i | B.level i < n})

/-- No basis function has level `< 0`. -/
@[simp]
theorem basisSpan_zero : B.basisSpan 0 = ⊥ := by simp [basisSpan]

/-- The spans increase with the level. -/
theorem basisSpan_mono : Monotone B.basisSpan := fun _ _ h =>
  Submodule.span_mono (Set.image_mono fun _ hi => lt_of_lt_of_le hi h)

/-- A basis function `eTilde_i` of level `< n` lies in the span of level `< n`. -/
theorem basisFun_mem_basisSpan {n : ℕ} {i : ι} (hi : B.level i < n) :
    B.basisFun i ∈ B.basisSpan n :=
  Submodule.subset_span ⟨i, hi, rfl⟩

/-- The **scheme of the basis functions**: the approximants of complexity `n` are the
combinations of the continuous basis functions `eTilde_i` of level `< n`. -/
noncomputable def basisScheme : FunctionScheme M :=
  ApproximationScheme.ofSubmodules (fun n => (B.basisSpan n).restrictScalars ℝ)
    (by simp) (fun _ _ h => B.basisSpan_mono h)

/-- The approximants of the scheme of the basis functions are their spans. -/
@[simp]
theorem mem_basisScheme {n : ℕ} {a : M →ᵇ ℂ} : a ∈ B.basisScheme n ↔ a ∈ B.basisSpan n :=
  Iff.rfl

/-- **The scheme in `L_2` is the spectral scheme**: the `L_2` classes of the combinations of
the continuous basis functions of level `< n` are the combinations of the basis elements of
level `< n`. -/
theorem toLp_basisScheme_eq : B.basisScheme.toLp μ 2 = B.toScheme := by
  ext n f
  change f ∈ (BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℝ) '' (B.basisSpan n : Set _) ↔
    f ∈ (B.span n : Set _)
  have hmap : (BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℝ : _ → _) '' (B.basisSpan n : Set _)
      = SetLike.coe ((B.basisSpan n).map
          (BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ).toLinearMap) := by
    rw [Submodule.map_coe]; rfl
  rw [hmap, basisSpan, Submodule.map_span, ← Set.image_comp]
  have hset : ((BoundedContinuousFunction.toLp (E := ℂ) 2 μ ℂ).toLinearMap ∘ B.basisFun) ''
      {i | B.level i < n} = B.basis '' {i | B.level i < n} := by
    ext g
    simp only [Set.mem_image, Function.comp_apply, ContinuousLinearMap.coe_coe, B.toLp_basisFun]
  rw [hset]
  rfl

/-! ### The spectral theory in `L_2` -/

variable {s : ℝ} {q : ℝ≥0∞}

/-- **`B^s_{2,2} = H^s`** for a continuous spectral basis: for `s > 0`, `f ∈ L_2(μ)` lies in
`B^s_{2,2}` iff `∑_i (1 + λ(i))^(2s) |⟨e_i, f⟩|² < ∞`. -/
theorem memBesov_two_two_iff (hs : 0 < s) (f : Lp ℂ 2 μ) :
    B.basisScheme.MemBesov μ 2 s 2 f ↔
      Memℓp (fun i => ((((1 + B.level i : ℕ) : ℝ) ^ s : ℝ) : ℂ) * B.basis.repr f i) 2 := by
  change (B.basisScheme.toLp μ 2).MemApprox s 2 f ↔ _
  rw [toLp_basisScheme_eq]
  exact B.memApprox_two_iff hs f

/-- **The Littlewood–Paley characterisation of `B^s_{2,q}`** for a continuous spectral basis,
with sharp cut-offs at the levels `2^k`: for `s > 0` and `1 ≤ q ≤ ∞`, `f ∈ B^s_{2,q}` iff
`‖P_1 f‖ + ‖(2^(ks) ‖Δ_k f‖_2)_k‖_{ℓ_q} < ∞`, with
`‖Δ_k f‖_2² = ∑_{2^k ≤ λ(i) < 2^(k+1)} |⟨e_i, f⟩|²`. -/
theorem memBesov_two_iff_blockNorm_lt_top (hs : 0 < s) (hq : 1 ≤ q) (f : Lp ℂ 2 μ) :
    B.basisScheme.MemBesov μ 2 s q f ↔ B.projectionScheme.blockNorm s q f < ∞ := by
  change (B.basisScheme.toLp μ 2).MemApprox s q f ↔ _
  rw [toLp_basisScheme_eq]
  exact B.memApprox_iff_blockNorm_lt_top hs hq

/-- The **Sobolev space `H^s`** of a continuous spectral basis, `s > 0`, as a Sobolev space for
the scheme of the basis functions in `L_2`: the image of `ℓ²(ι)` under
`c ↦ ∑_i (1 + λ(i))^(-s) c_i e_i`, with Jackson's and Bernstein's inequalities of order `s` and
constant `1`. -/
noncomputable def sobolevSpace (s : ℝ) (hs : 0 < s) : B.basisScheme.SobolevSpace μ 2 ℓ²(ι, ℂ) :=
  ApproximationScheme.SmoothnessSpace.congr B.toLp_basisScheme_eq.symm
    (B.toSmoothnessSpace s hs)

/-- `H^s` has order `s`. -/
@[simp]
theorem sobolevSpace_order (hs : 0 < s) : (B.sobolevSpace s hs).order = s := rfl

/-- The embedding of `H^s` is `J_s`. -/
theorem sobolevSpace_incl (hs : 0 < s) (c : ℓ²(ι, ℂ)) :
    (B.sobolevSpace s hs).incl c = B.sobolevEmbed s hs.le c := rfl

/-- **Membership in `H^s`** through the coefficients: `f ∈ L_2(μ)` lies in the range of the
Sobolev embedding iff `∑_i (1 + λ(i))^(2s) |⟨e_i, f⟩|² < ∞`. -/
theorem mem_range_sobolev_iff (hs : 0 < s) (f : Lp ℂ 2 μ) :
    f ∈ Set.range (B.sobolevSpace s hs).incl ↔
      Memℓp (fun i => ((((1 + B.level i : ℕ) : ℝ) ^ s : ℝ) : ℂ) * B.basis.repr f i) 2 :=
  B.mem_range_sobolevEmbed_iff s hs.le f

/-- **`H^s ⊆ B^s_{2,∞}`**, from Jackson's inequality. -/
theorem sobolev_memBesov_top (hs : 0 < s) (c : ℓ²(ι, ℂ)) :
    B.basisScheme.MemBesov μ 2 s ∞ ((B.sobolevSpace s hs).incl c) :=
  (B.sobolevSpace s hs).memApprox_top c

/-- **`B^t_{2,q} ⊆ H^s` for `t > s`**, from Bernstein's inequality. -/
theorem exists_sobolev_of_memBesov (hs : 0 < s) {t : ℝ} (hst : s < t) (hq : 1 ≤ q)
    {f : Lp ℂ 2 μ} (hf : B.basisScheme.MemBesov μ 2 t q f) :
    ∃ c : ℓ²(ι, ℂ), (B.sobolevSpace s hs).incl c = f :=
  (B.sobolevSpace s hs).exists_eq_of_lt hst hq hf

end ContinuousSpectralBasis
