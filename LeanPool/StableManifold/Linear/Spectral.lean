/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Linear.PowerDecay
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Spectral decay for finite-dimensional real linear operators

If the complex roots of the characteristic polynomial all have modulus less than one,
the powers of the operator tend to zero in norm. Complexify the matrix of the operator in
a basis and apply the pinned Mathlib limit theorem
`spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius` to bound its entries.
The same conclusion follows from an annihilating polynomial with all complex roots of
modulus less than one, since every eigenvalue is a root of the annihilator.
-/

@[expose] public section

open Filter Topology

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open scoped Matrix.Norms.Operator in
/-- Gelfand's formula for a complex matrix whose spectrum lies in the open unit disk: its powers
decay geometrically, entry by entry. (The matrix is normed by the `L∞`-operator norm, a Banach
algebra norm.) -/
private lemma eventually_entry_bound {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ z ∈ spectrum ℂ M, ‖z‖ < 1) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∀ᶠ n : ℕ in atTop, ∀ i j : Fin d, ‖(M ^ n) i j‖ ≤ r ^ n := by
  have : CompleteSpace (Matrix (Fin d) (Fin d) ℂ) := FiniteDimensional.complete ℂ _
  have hrad : spectralRadius ℂ M < 1 := by
    rcases (spectrum ℂ M).eq_empty_or_nonempty with h | h
    · simp [spectralRadius_eq_of_unital, h]
    · obtain ⟨z, hz, hzr⟩ := spectrum.exists_nnnorm_eq_spectralRadius_of_nonempty h
      rw [← hzr]
      have hz1 : ‖z‖ < 1 := hM z hz
      exact_mod_cast hz1
  have hfinite : spectralRadius ℂ M ≠ ⊤ := (hrad.trans_le le_top).ne
  have hreal : (spectralRadius ℂ M).toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hfinite ENNReal.one_ne_top).2 hrad
  obtain ⟨r, hr, hr1⟩ := exists_between hreal
  have hr0 : 0 < r := ENNReal.toReal_nonneg.trans_lt hr
  have hrad' : spectralRadius ℂ M < ENNReal.ofReal r := by
    rwa [← ENNReal.ofReal_toReal hfinite, ENNReal.ofReal_lt_ofReal_iff hr0]
  refine ⟨r, hr0, hr1, ?_⟩
  filter_upwards [(spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius M).eventually
    (gt_mem_nhds hrad'), eventually_gt_atTop (0 : ℕ)] with n hn hn0 i j
  have hn' : ‖M ^ n‖ ^ (1 / n : ℝ) < r := (ENNReal.ofReal_lt_ofReal_iff hr0).1 hn
  have hnreal : 0 < (n : ℝ) := Nat.cast_pos.2 hn0
  have hpow := Real.rpow_lt_rpow (Real.rpow_nonneg (norm_nonneg (M ^ n)) _) hn' hnreal
  rw [← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hnreal.ne', Real.rpow_one,
    Real.rpow_natCast] at hpow
  have hentry : ‖(M ^ n) i j‖₊ ≤ ‖M ^ n‖₊ := by
    rw [Matrix.linfty_opNNNorm_def]
    exact (Finset.single_le_sum (fun _ _ ↦ zero_le) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun row ↦ ∑ col, ‖(M ^ n) row col‖₊) (Finset.mem_univ i))
  exact (show ‖(M ^ n) i j‖ ≤ ‖M ^ n‖ from hentry).trans hpow.le

private lemma mem_spectrum_complexified_iff {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (z : ℂ) :
    z ∈ spectrum ℂ (M.map (algebraMap ℝ ℂ)) ↔ Polynomial.aeval z M.charpoly = 0 := by
  rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Polynomial.IsRoot.def, Matrix.charpoly_map,
    Polynomial.eval_map_algebraMap]

/-- If every complex eigenvalue of a linear operator `A` of a finite-dimensional real normed space
(every root in `ℂ` of its characteristic polynomial) has modulus `< 1`, then the powers of
`A` tend to zero in operator norm.

Proof: complexify. Choose a basis (`Module.finBasis`), so that `A` is a real matrix `M`, and view
`M` as a complex matrix, normed by the `L∞`-operator norm (a complex Banach algebra). The spectrum
of the complex matrix is the set of roots of its characteristic polynomial
(`Matrix.mem_spectrum_iff_isRoot_charpoly`), which are the complex roots of the characteristic
polynomial of `A` (`Matrix.charpoly_map`, `LinearMap.charpoly_toMatrix`), so its spectral radius
is `< 1`. By Gelfand's formula, `‖Mⁿ‖ ≤ rⁿ` eventually for some `0 < r < 1`, so the entries
of `Mⁿ` tend to `0`. The linear map from matrices to `E →L[ℝ] E` is continuous, so
`Aⁿ → 0`. -/
theorem tendsto_pow_of_charpoly_roots (A : E →L[ℝ] E)
    (hA : ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (A : E →ₗ[ℝ] E)) = 0 → ‖μ‖ < 1) :
    Tendsto (fun n : ℕ ↦ A ^ n) atTop (𝓝 0) := by
  classical
  let b := Module.finBasis ℝ E
  let M := LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)
  -- The complexified matrix: its eigenvalues are the complex roots of the charpoly of `A`.
  obtain ⟨r, hr0, hr1, hbound⟩ := eventually_entry_bound (M.map (algebraMap ℝ ℂ)) fun z hz ↦
    hA z (by simpa only [M, LinearMap.charpoly_toMatrix] using
      (mem_spectrum_complexified_iff M z).1 hz)
  -- Hence the real matrices `M ^ n` tend to `0`, entry by entry.
  have hM : Tendsto (fun n : ℕ ↦ M ^ n) atTop (𝓝 0) := by
    refine tendsto_pi_nhds.2 fun i ↦ tendsto_pi_nhds.2 fun j ↦ ?_
    refine squeeze_zero_norm' ?_ (tendsto_pow_atTop_nhds_zero_of_lt_one hr0.le hr1)
    filter_upwards [hbound] with n hn
    have h := hn i j
    rwa [← Matrix.map_pow, Matrix.map_apply, Complex.coe_algebraMap, Complex.norm_real] at h
  -- Transfer to `E →L[ℝ] E` through the linear map `Matrix → (E →L[ℝ] E)`, which is continuous
  -- since the space of matrices is finite-dimensional.
  let Ψ : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ →ₗ[ℝ] (E →L[ℝ] E) :=
    (LinearMap.toContinuousLinearMap : (E →ₗ[ℝ] E) ≃ₗ[ℝ] (E →L[ℝ] E)).toLinearMap ∘ₗ
      (Matrix.toLin b b).toLinearMap
  have hΨ : ∀ n : ℕ, Ψ (M ^ n) = A ^ n := by
    intro n
    ext x
    simp [Ψ, M, LinearMap.toMatrix_pow, ← ContinuousLinearMap.toLinearMap_pow]
  have h := (Ψ.continuous_of_finiteDimensional.tendsto 0).comp hM
  simpa [Function.comp_def, hΨ] using h

/-- Eigenvalues of modulus less than one give a power of operator norm less than one. -/
theorem exists_norm_pow_lt_one (A : E →L[ℝ] E)
    (hA : ∀ μ : ℂ, Polynomial.aeval μ (LinearMap.charpoly (A : E →ₗ[ℝ] E)) = 0 → ‖μ‖ < 1) :
    ∃ N : ℕ, 0 < N ∧ ‖A ^ N‖ < 1 :=
  A.exists_norm_pow_lt_one_of_norm_tendsto
    (by simpa using (A.tendsto_pow_of_charpoly_roots hA).norm)

/-- The complex eigenvalues of `A` (the complex roots of its characteristic polynomial) are roots
of every real polynomial annihilating `A`.

Proof: such a root `μ` lies in the spectrum of the complexified matrix `M` of `A`
(`Matrix.mem_spectrum_iff_isRoot_charpoly`), so `q(μ)` lies in the spectrum of `aeval M q`
(`spectrum.subset_polynomial_aeval`); and `aeval M q = 0`, since the matrix of a linear map
(`LinearMap.toMatrixAlgEquiv`) and the entrywise map `ℝ → ℂ` (`AlgHom.mapMatrix`) are algebra
homomorphisms. The spectrum of `0` is contained in `{0}`. -/
private lemma aeval_eq_zero_of_aeval_charpoly_eq_zero (A : E →L[ℝ] E) {q : Polynomial ℝ}
    (hq : Polynomial.aeval (A : E →ₗ[ℝ] E) q = 0) {μ : ℂ}
    (hμ : Polynomial.aeval μ (LinearMap.charpoly (A : E →ₗ[ℝ] E)) = 0) :
    Polynomial.aeval μ q = 0 := by
  classical
  let b := Module.finBasis ℝ E
  let M := (LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)).map (algebraMap ℝ ℂ)
  have hz : μ ∈ spectrum ℂ M :=
    (mem_spectrum_complexified_iff (LinearMap.toMatrix b b (A : E →ₗ[ℝ] E)) μ).2
      (by simpa only [LinearMap.charpoly_toMatrix] using hμ)
  have h0 : Polynomial.aeval M q = 0 := by
    have hM : M = (Algebra.ofId ℝ ℂ).mapMatrix (LinearMap.toMatrixAlgEquiv b A) := rfl
    rw [hM, Polynomial.aeval_algHom_apply, Polynomial.aeval_algEquiv, AlgHom.comp_apply, hq]
    simp [Matrix.map_zero _ (map_zero _)]
  have h := spectrum.subset_polynomial_aeval _ (q.map (algebraMap ℝ ℂ)) ⟨μ, hz, rfl⟩
  rw [Polynomial.aeval_map_algebraMap, h0] at h
  rw [← Polynomial.eval_map_algebraMap]
  obtain hs | hs :=
    subsingleton_or_nontrivial (Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℂ)
  · simp [spectrum.of_subsingleton] at h
  · rwa [spectrum.zero_eq, Set.mem_singleton_iff] at h

/-- If every complex root of an annihilating polynomial has modulus less than one, the
powers of the operator tend to zero in norm. -/
theorem tendsto_pow_of_aeval_eq_zero (A : E →L[ℝ] E) {q : Polynomial ℝ}
    (hq : Polynomial.aeval (A : E →ₗ[ℝ] E) q = 0)
    (hroots : ∀ μ : ℂ, Polynomial.aeval μ q = 0 → ‖μ‖ < 1) :
    Tendsto (fun n : ℕ ↦ A ^ n) atTop (𝓝 0) :=
  A.tendsto_pow_of_charpoly_roots fun _ hμ ↦
    hroots _ (aeval_eq_zero_of_aeval_charpoly_eq_zero A hq hμ)

/-- If a linear operator `A` of a finite-dimensional real normed space is annihilated by a real
polynomial `q` whose complex roots all have modulus `< 1`, then some power `A ^ N`, `N ≥ 1`, has
operator norm `< 1`. (The hypothesis on the roots forces `q ≠ 0`.)

Proof: `tendsto_pow_of_aeval_eq_zero`. -/
theorem exists_norm_pow_lt_one_of_aeval_eq_zero (A : E →L[ℝ] E) {q : Polynomial ℝ}
    (hq : Polynomial.aeval (A : E →ₗ[ℝ] E) q = 0)
    (hroots : ∀ μ : ℂ, Polynomial.aeval μ q = 0 → ‖μ‖ < 1) :
    ∃ N : ℕ, 0 < N ∧ ‖A ^ N‖ < 1 :=
  A.exists_norm_pow_lt_one_of_norm_tendsto
    (by simpa using (A.tendsto_pow_of_aeval_eq_zero hq hroots).norm)

/-- If `A` is annihilated by a real polynomial whose complex roots all have modulus `< 1`, then
every orbit `Aⁿ v` tends to `0`.

Proof: use operator-norm convergence and `‖Aⁿ v‖ ≤ ‖Aⁿ‖ ‖v‖`. -/
theorem tendsto_pow_apply_of_aeval_eq_zero (A : E →L[ℝ] E) {q : Polynomial ℝ}
    (hq : Polynomial.aeval (A : E →ₗ[ℝ] E) q = 0)
    (hroots : ∀ μ : ℂ, Polynomial.aeval μ q = 0 → ‖μ‖ < 1) (v : E) :
    Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0) := by
  refine squeeze_zero_norm (fun n ↦ (A ^ n).le_opNorm v) ?_
  simpa using (A.tendsto_pow_of_aeval_eq_zero hq hroots).norm.mul_const ‖v‖

end ContinuousLinearMap
