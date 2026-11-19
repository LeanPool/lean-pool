/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Analysis.Normed.Algebra.GelfandFormula
public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs

/-!
# Powers of a linear operator with spectrum in the open unit disk

For a linear operator `A` of a finite-dimensional real normed space, the eigenvalues are the complex
roots of its characteristic polynomial `LinearMap.charpoly` (a real operator may have non-real
eigenvalues, and `spectrum ℝ` would miss them, so hypotheses are stated with `Polynomial.aeval μ`
for `μ : ℂ`).

* `ContinuousLinearMap.exists_norm_pow_lt_one`: if every complex root of the characteristic
  polynomial of `A` has modulus `< 1`, then `‖A ^ N‖ < 1` for some `N ≥ 1` (Gelfand's formula);
* `ContinuousLinearMap.exists_norm_pow_lt_one_of_aeval_eq_zero`: the same when `A` is annihilated
  by a real polynomial whose complex roots all have modulus `< 1`;
* `ContinuousLinearMap.exists_norm_pow_lt_one_of_tendsto`: if every orbit `Aⁿ v` tends to `0`,
  then `‖A ^ N‖ < 1` for some `N ≥ 1` (finite dimension);
* `ContinuousLinearMap.exists_norm_pow_le_mul_pow`: if `‖A ^ N‖ < 1` with `N ≥ 1`, then
  `‖Aⁿ‖ ≤ C rⁿ` for all `n`, with `r < 1` (any normed space);
* `ContinuousLinearMap.exists_norm_pow_le_mul_pow_of_tendsto`,
  `ContinuousLinearMap.tendsto_pow_apply_of_aeval_eq_zero`: the two combinations used later.

Mathlib has Gelfand's formula (`spectrum.pow_nnnorm_pow_one_div_tendsto_nhds_spectralRadius`, in
the form `spectrum.spectralRadius_eq_gelfandRadius`) for complex Banach algebras.

## Proofs

* `exists_norm_pow_lt_one`: complexify the matrix of `A` in a basis and apply Gelfand's formula
  to it (private lemma `exists_entry_bound`).
* `exists_norm_pow_lt_one_of_aeval_eq_zero` reduces to `exists_norm_pow_lt_one`: a complex root
  `μ` of the characteristic polynomial lies in the spectrum of the complexified matrix `M` of `A`,
  so `q(μ) ∈ spectrum ℂ (aeval M q)` (`spectrum.subset_polynomial_aeval`); and `aeval M q = 0`,
  since `LinearMap.toMatrixAlgEquiv` and the entrywise map `ℝ → ℂ` (`AlgHom.mapMatrix`) are
  algebra homomorphisms (`Polynomial.aeval_algHom_apply`, `Polynomial.aeval_algEquiv`). The
  spectrum of `0` lies in `{0}`, so `q(μ) = 0` and `‖μ‖ < 1`.
* `exists_norm_pow_lt_one_of_tendsto`: with a basis `b` (`Module.finBasis`),
  `Module.Basis.exists_opNorm_le` bounds `‖Aⁿ‖` by a constant times `∑ᵢ ‖Aⁿ (b i)‖ → 0`.
* `exists_norm_pow_le_mul_pow`: let `ρ = max (1/2) ‖A ^ N‖ < 1` and `r = ρ ^ (1 / N)` (real
  power), so that `r ^ N = ρ`. Write `n = N q + j` with `j < N` (`Nat.div_add_mod`); then
  `‖Aⁿ‖ ≤ ρ ^ q ‖A ^ j‖ ≤ ρ ^ q K ≤ (K / ρ) rⁿ` with `K = 1 + ∑_{j < N} ‖A ^ j‖`.
* The two combinations compose the lemmas above.
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

omit [FiniteDimensional ℝ E] in
private theorem exists_norm_pow_lt_one_of_norm_tendsto (A : E →L[ℝ] E)
    (h : Tendsto (fun n : ℕ ↦ ‖A ^ n‖) atTop (𝓝 0)) : ∃ N : ℕ, 0 < N ∧ ‖A ^ N‖ < 1 := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds (a := (1 : ℝ)) (by simp)))
  exact ⟨N + 1, N.succ_pos, hN (N + 1) (Nat.le_succ _)⟩

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

/-- In finite dimension, if every orbit `Aⁿ v` tends to `0`, then some power `A ^ N`, `N ≥ 1`, has
operator norm `< 1`.

Proof: with a basis `b`, `Module.Basis.exists_opNorm_le` gives `‖Aⁿ‖ ≤ K ∑ᵢ ‖Aⁿ (b i)‖ → 0`. -/
theorem exists_norm_pow_lt_one_of_tendsto (A : E →L[ℝ] E)
    (hA : ∀ v, Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0)) :
    ∃ N : ℕ, 0 < N ∧ ‖A ^ N‖ < 1 := by
  let b := Module.finBasis ℝ E
  obtain ⟨C, -, hC⟩ := b.exists_opNorm_le (F := E)
  -- `‖Aⁿ‖ ≤ C ∑ᵢ ‖Aⁿ (b i)‖ → 0`
  have hs : Tendsto (fun n : ℕ ↦ ∑ i, ‖(A ^ n) (b i)‖) atTop (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ fun i _ ↦ (hA (b i)).norm
  have hT : Tendsto (fun n : ℕ ↦ ‖A ^ n‖) atTop (𝓝 0) := by
    refine squeeze_zero (fun n ↦ norm_nonneg _)
      (fun n ↦ hC (Finset.sum_nonneg fun i _ ↦ norm_nonneg _) fun i ↦
        Finset.single_le_sum (f := fun i ↦ ‖(A ^ n) (b i)‖) (fun i _ ↦ norm_nonneg _)
          (Finset.mem_univ i)) ?_
    simpa using hs.const_mul C
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hT.eventually (gt_mem_nhds (a := (1 : ℝ)) (by simp)))
  exact ⟨N + 1, N.succ_pos, hN (N + 1) (by omega)⟩

omit [FiniteDimensional ℝ E] in
/-- **Geometric decay** from one contracting power: if `‖A ^ N‖ < 1` with `N ≥ 1`, then
`‖Aⁿ‖ ≤ C rⁿ` for all `n`, with `1 ≤ C` and `0 < r < 1`.

Proof: with `ρ = max (1/2) ‖A ^ N‖` and `r = ρ ^ (1 / N)`, write `n = N q + j`, `j < N`; then
`‖Aⁿ‖ ≤ ρ ^ q K ≤ (K / ρ) rⁿ`, where `K` bounds `‖A ^ j‖` for `j < N`. -/
theorem exists_norm_pow_le_mul_pow (A : E →L[ℝ] E) {N : ℕ} (hN : 0 < N) (hA : ‖A ^ N‖ < 1) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ n : ℕ, ‖A ^ n‖ ≤ C * r ^ n := by
  set ρ := max (1 / 2) ‖A ^ N‖
  have hρ0 : 0 < ρ := lt_max_of_lt_left (by norm_num)
  have hρ1 : ρ < 1 := max_lt (by norm_num) hA
  set K := 1 + ∑ j ∈ Finset.range N, ‖A ^ j‖
  have hK1 : 1 ≤ K := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ ↦ norm_nonneg _)
  have hKj : ∀ j < N, ‖A ^ j‖ ≤ K := fun j hj ↦
    (Finset.single_le_sum (f := fun j ↦ ‖A ^ j‖) (fun j _ ↦ norm_nonneg _)
      (Finset.mem_range.2 hj)).trans (le_add_of_nonneg_left zero_le_one)
  set r := ρ ^ (1 / (N : ℝ))
  have hr0 : 0 < r := Real.rpow_pos_of_pos hρ0 _
  have hr1 : r < 1 := Real.rpow_lt_one hρ0.le hρ1 (by positivity)
  have hrN : r ^ N = ρ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le, one_div_mul_cancel (by positivity),
      Real.rpow_one]
  -- along the multiples of `N`
  have hq : ∀ q j : ℕ, ‖A ^ (N * q + j)‖ ≤ ρ ^ q * ‖A ^ j‖ := by
    intro q j
    induction q with
    | zero => simp
    | succ q ih =>
      calc ‖A ^ (N * (q + 1) + j)‖ = ‖A ^ N * A ^ (N * q + j)‖ := by
            rw [← pow_add]; congr 2; ring
        _ ≤ ‖A ^ N‖ * ‖A ^ (N * q + j)‖ := norm_mul_le _ _
        _ ≤ ρ * (ρ ^ q * ‖A ^ j‖) := by gcongr; exact le_max_right _ _
        _ = ρ ^ (q + 1) * ‖A ^ j‖ := by ring
  refine ⟨K / ρ, r, (one_le_div hρ0).2 (by linarith), hr0, hr1, fun n ↦ ?_⟩
  obtain ⟨q, j, hj, rfl⟩ : ∃ q j, j < N ∧ n = N * q + j :=
    ⟨n / N, n % N, Nat.mod_lt _ hN, (Nat.div_add_mod n N).symm⟩
  calc ‖A ^ (N * q + j)‖ ≤ ρ ^ q * K := (hq q j).trans (by gcongr; exact hKj j hj)
    _ = K / ρ * (ρ ^ q * r ^ N) := by rw [hrN]; field_simp
    _ ≤ K / ρ * (ρ ^ q * r ^ j) := by
      have := pow_le_pow_of_le_one hr0.le hr1.le hj.le
      gcongr
    _ = K / ρ * r ^ (N * q + j) := by rw [pow_add, pow_mul, hrN]

/-- In finite dimension, if every orbit `Aⁿ v` tends to `0`, then `‖Aⁿ‖ ≤ C rⁿ` for all `n`, with
`1 ≤ C` and `0 < r < 1`.

Proof: `exists_norm_pow_lt_one_of_tendsto` and `exists_norm_pow_le_mul_pow`. -/
theorem exists_norm_pow_le_mul_pow_of_tendsto (A : E →L[ℝ] E)
    (hA : ∀ v, Tendsto (fun n : ℕ ↦ (A ^ n) v) atTop (𝓝 0)) :
    ∃ C r : ℝ, 1 ≤ C ∧ 0 < r ∧ r < 1 ∧ ∀ n : ℕ, ‖A ^ n‖ ≤ C * r ^ n :=
  let ⟨_, hN, hAN⟩ := A.exists_norm_pow_lt_one_of_tendsto hA
  A.exists_norm_pow_le_mul_pow hN hAN

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
