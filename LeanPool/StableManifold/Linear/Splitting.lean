/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Adapted for Lean Pool.

public import LeanPool.StableManifold.Defs
public import LeanPool.StableManifold.Linear.Spectral
public import LeanPool.StableManifold.Linear.FiniteDimensionalSubspaces
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# The hyperbolic splitting

For a hyperbolic linear map `A` of a finite-dimensional real normed space, the stable and unstable
subspaces are complementary, `E = Eₛ ⊕ Eᵤ`
(`ContinuousLinearMap.isCompl_stableSubspace_unstableSubspace`); a zero eigenvalue is allowed.
They are `Eₛ = ker pₛ(A)` and `Eᵤ = ker pᵤ(A)`, for the coprime factors `pₛ`, `pᵤ` of the
characteristic polynomial with all complex roots inside, resp. outside, the unit circle
(`ContinuousLinearMap.exists_stableSubspace_unstableSubspace_eq_ker_aeval`); by the primary
decomposition, these are the sums of the generalized eigenspaces of the eigenvalues of modulus
`< 1`, resp. `> 1`.

* `Polynomial.norm_eq_of_irreducible`: the complex roots of an irreducible real polynomial all
  have the same modulus;
* `Polynomial.exists_isCoprime_roots_lt_one_one_lt`: a real polynomial without complex roots on
  the unit circle is, up to a unit, a product `pₛ pᵤ` of coprime factors with all roots inside,
  resp. outside, the unit circle;
* `Polynomial.norm_lt_one_of_aeval_reverse_eq_zero`: the roots of the reverse of a polynomial with
  roots outside the unit circle lie inside;
* `ContinuousLinearMap.aeval_symm_reverse_eq_zero`: if `q(T) = 0` for an invertible `T`, then
  `q.reverse (T⁻¹) = 0`;
* `ContinuousLinearMap.ker_aeval_le_stableSubspace`, `ker_aeval_le_unstableSubspace`: the kernel of
  `pₛ(A)` lies in the stable subspace, the kernel of `pᵤ(A)` in the unstable one;
* `ContinuousLinearMap.codisjoint_stableSubspace_unstableSubspace`: for a hyperbolic `A`,
  `Eₛ ⊔ Eᵤ = ⊤`;
* `ContinuousLinearMap.exists_stableSubspace_unstableSubspace_eq_ker_aeval`: for a hyperbolic `A`,
  `Eₛ = ker pₛ(A)` and `Eᵤ = ker pᵤ(A)`.

## Proofs

* `norm_eq_of_irreducible`: let `Q = q.map ofReal`. If the root `μ` is real, `q` has degree `1`
  (`Polynomial.degree_eq_one_of_irreducible_of_root`), so `X - μ ∣ Q` with the same degree. If
  not, `(X - conj μ) (X - μ) ∣ Q` (`Polynomial.mul_star_dvd_of_aeval_eq_zero_im_ne_zero`), of
  degree `2 ≥ deg Q` (`Irreducible.natDegree_le_two`). In both cases the cofactor is a nonzero
  constant, so every root `ν` of `Q` is `μ` or `conj μ`, of modulus `‖μ‖` (`Complex.norm_conj`).
* `exists_isCoprime_roots_lt_one_one_lt`: split the normalized factors
  (`UniqueFactorizationMonoid.normalizedFactors p`) by the predicate "all complex roots have
  modulus `< 1`": `pₛ` is the product of those that satisfy it, `pᵤ` of the others
  (`Multiset.prod_filter_mul_prod_filter_not`), and `Associated (pₛ * pᵤ) p`
  (`UniqueFactorizationMonoid.prod_normalizedFactors`). A complex root of a product is a root of a
  factor (`map_multiset_prod`, `Multiset.prod_eq_zero_iff`). A factor `f` of `pᵤ` has a root `ν`
  with `‖ν‖ ≥ 1`, so each root `μ` of `f` has `‖μ‖ = ‖ν‖ ≥ 1` (`norm_eq_of_irreducible`), and
  `‖μ‖ ≠ 1` since `μ` is a root of `p`. Coprimality: no common complex root
  (`Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed` with `K = ℂ`).
* `norm_lt_one_of_aeval_reverse_eq_zero`: `q ≠ 0` (else `0` is a root), and
  `aeval 0 q.reverse = q.leadingCoeff ≠ 0` (`Polynomial.coeff_zero_reverse`), so `ν ≠ 0`;
  `Polynomial.eval₂_reverse_eq_zero_iff` at `x = ν⁻¹` gives `aeval ν⁻¹ q = 0`, so `1 < ‖ν⁻¹‖`.
* `aeval_symm_reverse_eq_zero`: with `S = T⁻¹`, `d = natDegree q` and `S ^ i T ^ d = T ^ (d - i)`
  for `i ≤ d`, `q.reverse (S) T ^ d = ∑ᵢ q.coeff (d - i) T ^ (d - i) = q(T) = 0`
  (`Polynomial.aeval_eq_sum_range'`, `Polynomial.coeff_reverse`, `Finset.sum_range_reflect`);
  multiply on the right by `S ^ d`.
* `ker_aeval_le_stableSubspace`: `K = ker q(A)` is `A`-invariant (`q X = X q`); the restriction
  `Aₖ : K →L[ℝ] K` (`ContinuousLinearMap.restrict`) satisfies `q(Aₖ) = 0` (a polynomial in a
  restriction is the restriction of the polynomial, by induction on `q`, `Module.End.pow_restrict`);
  then `tendsto_pow_apply_of_aeval_eq_zero` gives `Aₖⁿ v → 0`, that is `Aⁿ v → 0`.
* `ker_aeval_le_unstableSubspace`: `q.coeff 0 ≠ 0` (`0` is not a root), so `Aₖ` is injective
  (`q(Aₖ) v = q.divX (Aₖ) (Aₖ v) + q.coeff 0 • v`, `Polynomial.divX_mul_X_add`), hence a
  continuous linear equivalence `T` of `K` (`LinearEquiv.ofInjectiveEndo`, finite dimension). By
  `aeval_symm_reverse_eq_zero` and `norm_lt_one_of_aeval_reverse_eq_zero`,
  `tendsto_pow_apply_of_aeval_eq_zero` applies to `T⁻¹`: `w n = T⁻ⁿ v → 0` is a backward orbit of
  `v`.
* `codisjoint_stableSubspace_unstableSubspace`: with `χ = charpoly A` (monic, so nonzero) and
  `pₛ pᵤ` from `exists_isCoprime_roots_lt_one_one_lt`,
  `ker pₛ(A) ⊔ ker pᵤ(A) = ker (pₛ pᵤ)(A) = ⊤`
  (`Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime`; `χ ∣ pₛ pᵤ` and Cayley–Hamilton,
  `LinearMap.aeval_self_charpoly`), and the two kernels lie in `Eₛ` and `Eᵤ`.
* `exists_stableSubspace_unstableSubspace_eq_ker_aeval`: the same `pₛ`, `pᵤ`. A `v ∈ Eₛ` is
  `a + b` with `a ∈ ker pₛ(A) ≤ Eₛ` and `b ∈ ker pᵤ(A) ≤ Eᵤ` (`Submodule.mem_sup`); then
  `b = v - a ∈ Eₛ ⊓ Eᵤ = 0` (`disjoint_stableSubspace_unstableSubspace`), so `v = a`. The same
  argument, with the roles exchanged, gives `Eᵤ ≤ ker pᵤ(A)`.
-/

@[expose] public section


open Filter Topology Polynomial

namespace Polynomial

/-- If `D ∣ Q` with `Q ≠ 0` and `natDegree Q ≤ natDegree D`, every root of `Q` is a root of `D`:
the two polynomials are associated. -/
private lemma eval_eq_zero_of_dvd_of_natDegree_le {Q D : ℂ[X]} (hQ : Q ≠ 0) (hD : D ∣ Q)
    (hdeg : Q.natDegree ≤ D.natDegree) {ν : ℂ} (hν : Q.eval ν = 0) : D.eval ν = 0 := by
  exact IsRoot.dvd hν (associated_of_dvd_of_natDegree_le hD hQ hdeg).dvd'

/-- The complex roots of an irreducible real polynomial all have the **same modulus**: an
irreducible real polynomial has degree `1` (one real root) or `2` (a pair of conjugate roots).

Proof: `Irreducible.natDegree_le_two`; in degree `2` the roots are `μ` and `conj μ`. -/
theorem norm_eq_of_irreducible {q : ℝ[X]} (hq : Irreducible q) {μ ν : ℂ} (hμ : aeval μ q = 0)
    (hν : aeval ν q = 0) : ‖μ‖ = ‖ν‖ := by
  have hQ0 : q.map (algebraMap ℝ ℂ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).2 hq.ne_zero
  have hQdeg : (q.map (algebraMap ℝ ℂ)).natDegree = q.natDegree := natDegree_map _
  have hνQ : (q.map (algebraMap ℝ ℂ)).eval ν = 0 := by rwa [eval_map_algebraMap]
  by_cases him : μ.im = 0
  · -- a real root: `q` has degree `1`, and its only root is `μ`
    have hμr : ((μ.re : ℝ) : ℂ) = μ := Complex.ext rfl (by simp [him])
    have hroot : q.IsRoot μ.re := by
      rw [← hμr, ← Complex.coe_algebraMap, aeval_algebraMap_apply_eq_algebraMap_eval] at hμ
      exact (algebraMap ℝ ℂ).injective (hμ.trans (map_zero _).symm)
    have h1 : q.natDegree = 1 :=
      natDegree_eq_of_degree_eq_some (degree_eq_one_of_irreducible_of_root hq hroot)
    have hD : X - C μ ∣ q.map (algebraMap ℝ ℂ) := by
      rwa [dvd_iff_isRoot, IsRoot.def, eval_map_algebraMap]
    have := eval_eq_zero_of_dvd_of_natDegree_le hQ0 hD (by rw [hQdeg, h1, natDegree_X_sub_C]) hνQ
    rw [eval_sub, eval_X, eval_C, sub_eq_zero] at this
    rw [this]
  · -- a non-real root: `q.map ofReal = c (X - conj μ) (X - μ)`
    have hD := q.mul_star_dvd_of_aeval_eq_zero_im_ne_zero hμ him
    have hdeg : (q.map (algebraMap ℝ ℂ)).natDegree ≤
        ((X - C ((starRingEnd ℂ) μ)) * (X - C μ)).natDegree := by
      rw [hQdeg, natDegree_mul (X_sub_C_ne_zero _) (X_sub_C_ne_zero _), natDegree_X_sub_C,
        natDegree_X_sub_C]
      exact hq.natDegree_le_two
    have := eval_eq_zero_of_dvd_of_natDegree_le hQ0 hD hdeg hνQ
    rw [eval_mul, eval_sub, eval_sub, eval_X, eval_C, eval_C, mul_eq_zero, sub_eq_zero,
      sub_eq_zero] at this
    rcases this with h | h
    · rw [h, Complex.norm_conj]
    · rw [h]

/-- A real polynomial `p ≠ 0` without complex roots on the unit circle is, up to a unit, a product
`pₛ pᵤ` of **coprime factors** with all complex roots inside, resp. outside, the unit circle.

Proof: split the normalized factors of `p` by the modulus of their roots (all roots of an
irreducible factor have the same modulus, `norm_eq_of_irreducible`); the two products have no
common complex root, so they are coprime. -/
theorem exists_isCoprime_roots_lt_one_one_lt {p : ℝ[X]} (hp : p ≠ 0)
    (h : ∀ μ : ℂ, aeval μ p = 0 → ‖μ‖ ≠ 1) :
    ∃ ps pu : ℝ[X], Associated (ps * pu) p ∧ IsCoprime ps pu ∧
      (∀ μ : ℂ, aeval μ ps = 0 → ‖μ‖ < 1) ∧ (∀ μ : ℂ, aeval μ pu = 0 → 1 < ‖μ‖) := by
  classical
  let P : ℝ[X] → Prop := fun f ↦ ∀ μ : ℂ, aeval μ f = 0 → ‖μ‖ < 1
  let F := UniqueFactorizationMonoid.normalizedFactors p
  -- a complex root of the product of a multiset of polynomials is a root of one of them
  have hroot (s : Multiset ℝ[X]) (μ : ℂ) (hμ : aeval μ s.prod = 0) : ∃ f ∈ s, aeval μ f = 0 := by
    rw [map_multiset_prod, Multiset.prod_eq_zero_iff, Multiset.mem_map] at hμ
    exact hμ
  have hs (μ : ℂ) (hμ : aeval μ (F.filter P).prod = 0) : ‖μ‖ < 1 := by
    obtain ⟨f, hf, hfμ⟩ := hroot _ μ hμ
    exact (Multiset.mem_filter.1 hf).2 μ hfμ
  have hu (μ : ℂ) (hμ : aeval μ (F.filter fun f ↦ ¬P f).prod = 0) : 1 < ‖μ‖ := by
    obtain ⟨f, hf, hfμ⟩ := hroot _ μ hμ
    obtain ⟨hfF, hfP⟩ := Multiset.mem_filter.1 hf
    obtain ⟨ν, hν, hν1⟩ : ∃ ν : ℂ, aeval ν f = 0 ∧ 1 ≤ ‖ν‖ := by
      simpa [P] using hfP
    have hpμ : aeval μ p = 0 := by
      obtain ⟨g, hg⟩ := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hfF
      rw [hg, map_mul, hfμ, zero_mul]
    have hμν := norm_eq_of_irreducible
      (UniqueFactorizationMonoid.irreducible_of_normalized_factor f hfF) hfμ hν
    exact lt_of_le_of_ne (hμν ▸ hν1) (h μ hpμ).symm
  refine ⟨(F.filter P).prod, (F.filter fun f ↦ ¬P f).prod, ?_, ?_, hs, hu⟩
  · rw [Multiset.prod_filter_mul_prod_filter_not]
    exact UniqueFactorizationMonoid.prod_normalizedFactors hp
  · refine (isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℝ ℂ _ _).2 fun μ ↦
      or_iff_not_imp_left.2 fun h₁ h₂ ↦ lt_asymm (hs μ (not_not.1 h₁)) (hu μ h₂)

/-- If every complex root of `q` has modulus `> 1`, every complex root of `q.reverse` has modulus
`< 1`: the roots of the reverse are the inverses of the nonzero roots.

Proof: `q ≠ 0`, `aeval 0 q.reverse = q.leadingCoeff ≠ 0`, and
`Polynomial.eval₂_reverse_eq_zero_iff` at `ν⁻¹`. -/
theorem norm_lt_one_of_aeval_reverse_eq_zero {q : ℝ[X]} (hq : ∀ μ : ℂ, aeval μ q = 0 → 1 < ‖μ‖)
    {ν : ℂ} (hν : aeval ν q.reverse = 0) : ‖ν‖ < 1 := by
  have hq0 : q ≠ 0 := by
    rintro rfl
    exact absurd (hq 0 (by simp)) (by simp)
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [← coeff_zero_eq_aeval_zero', coeff_zero_reverse] at hν
    exact leadingCoeff_ne_zero.2 hq0 ((algebraMap ℝ ℂ).injective (hν.trans (map_zero _).symm))
  let : Invertible ν⁻¹ := invertibleOfNonzero (inv_ne_zero hν0)
  have h : aeval ν⁻¹ q = 0 := by
    rw [aeval_def, ← eval₂_reverse_eq_zero_iff, invOf_eq_inv, inv_inv, ← aeval_def]
    exact hν
  have h1 := hq _ h
  rw [norm_inv] at h1
  exact (one_lt_inv₀ (norm_pos_iff.2 hν0)).1 h1

end Polynomial

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If an invertible operator `T` is annihilated by `q`, its inverse is annihilated by the reverse
of `q`.

Proof: `q.reverse (T⁻¹) ∘ T ^ q.natDegree = q(T) = 0` (`Polynomial.coeff_reverse`), and
`T ^ q.natDegree` is invertible. -/
theorem aeval_symm_reverse_eq_zero (T : E ≃L[ℝ] E) {q : ℝ[X]}
    (hq : aeval ((T : E →L[ℝ] E) : E →ₗ[ℝ] E) q = 0) :
    aeval ((T.symm : E →L[ℝ] E) : E →ₗ[ℝ] E) q.reverse = 0 := by
  set S : Module.End ℝ E := ((T.symm : E →L[ℝ] E) : E →ₗ[ℝ] E)
  set U : Module.End ℝ E := ((T : E →L[ℝ] E) : E →ₗ[ℝ] E)
  have hSU : S * U = 1 := LinearMap.ext fun x ↦ by simp [S, U]
  have hUS : U * S = 1 := LinearMap.ext fun x ↦ by simp [S, U]
  have hcomm : Commute S U := hSU.trans hUS.symm
  set d := q.natDegree
  have hpow (i : ℕ) (hi : i ≤ d) : S ^ i * U ^ d = U ^ (d - i) := by
    calc S ^ i * U ^ d = S ^ i * (U ^ i * U ^ (d - i)) := by rw [← pow_add, Nat.add_sub_cancel' hi]
      _ = (S * U) ^ i * U ^ (d - i) := by rw [hcomm.mul_pow, mul_assoc]
      _ = U ^ (d - i) := by rw [hSU, one_pow, one_mul]
  have key : aeval S q.reverse * U ^ d = aeval U q := by
    rw [aeval_eq_sum_range' (n := d + 1) (Nat.lt_succ_of_le (reverse_natDegree_le q)),
      aeval_eq_sum_range, Finset.sum_mul,
      ← Finset.sum_range_reflect (fun j ↦ q.coeff j • U ^ j) (d + 1)]
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    have hi : i ≤ d := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    rw [smul_mul_assoc, hpow i hi, coeff_reverse, revAt_le hi, Nat.add_sub_cancel]
  calc aeval S q.reverse = aeval S q.reverse * U ^ d * S ^ d := by
        rw [mul_assoc, ← hcomm.symm.mul_pow, hUS, one_pow, mul_one]
    _ = 0 := by rw [key, hq, zero_mul]

/-- The kernel of `q(A)` is `A`-invariant. -/
private lemma map_mem_ker_aeval (A : E →L[ℝ] E) (q : ℝ[X]) {v : E}
    (hv : v ∈ LinearMap.ker (aeval (A : E →ₗ[ℝ] E) q)) :
    A v ∈ LinearMap.ker (aeval (A : E →ₗ[ℝ] E) q) := by
  have h := congrArg (aeval (A : E →ₗ[ℝ] E)) (mul_comm q X)
  rw [aeval_mul, aeval_mul, aeval_X] at h
  have h' := LinearMap.congr_fun h v
  rw [Module.End.mul_apply, Module.End.mul_apply, LinearMap.mem_ker.1 hv, map_zero] at h'
  exact h'

/-- A polynomial in the restriction of `f` to an invariant subspace is the restriction of the
polynomial in `f`. -/
private lemma coe_aeval_restrict_apply {F : Type*} [AddCommGroup F] [Module ℝ F] {f : F →ₗ[ℝ] F}
    {p : Submodule ℝ F} (h : ∀ x ∈ p, f x ∈ p) (q : ℝ[X]) (x : p) :
    ((aeval (f.restrict h) q x : p) : F) = aeval f q x := by
  induction q using Polynomial.induction_on' with
  | add p₁ p₂ h₁ h₂ => simp [h₁, h₂]
  | monomial n a =>
    simp only [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply,
      Submodule.coe_smul, Module.End.pow_restrict n h, LinearMap.restrict_apply]

/-- The restriction of `A` to an invariant subspace contained in `ker q(A)` is annihilated by
`q`. -/
private lemma aeval_restrict_eq_zero {A : E →L[ℝ] E} {q : ℝ[X]} {p : Submodule ℝ E}
    (h : ∀ x ∈ p, A x ∈ p) (hp : p ≤ LinearMap.ker (aeval (A : E →ₗ[ℝ] E) q)) :
    aeval ((A.restrict h : p →L[ℝ] p) : p →ₗ[ℝ] p) q = 0 := by
  ext x
  rw [toLinearMap_restrict, coe_aeval_restrict_apply]
  simpa using hp x.2

variable [FiniteDimensional ℝ E]

/-- The kernel of `q(A)`, for a real polynomial `q` with all complex roots of modulus `< 1`, lies
in the **stable subspace**.

Proof: the restriction of `A` to the invariant subspace `ker q(A)` is annihilated by `q`, so its
powers tend to `0` (`tendsto_pow_apply_of_aeval_eq_zero`). -/
theorem ker_aeval_le_stableSubspace (A : E →L[ℝ] E) {q : ℝ[X]}
    (hq : ∀ μ : ℂ, aeval μ q = 0 → ‖μ‖ < 1) :
    LinearMap.ker (aeval (A : E →ₗ[ℝ] E) q) ≤ A.stableSubspace := by
  intro v hv
  have hK : ∀ x ∈ LinearMap.ker (aeval (A : E →ₗ[ℝ] E) q), A x ∈ _ :=
    fun _ hx ↦ map_mem_ker_aeval A q hx
  have ht := (continuous_subtype_val.tendsto 0).comp
    (tendsto_pow_apply_of_aeval_eq_zero _ (aeval_restrict_eq_zero hK le_rfl) hq ⟨v, hv⟩)
  refine mem_stableSubspace.2 ?_
  simpa only [Function.comp_def, Submodule.coe_zero, coe_restrict_pow_apply] using ht

/-- The kernel of `q(A)`, for a real polynomial `q` with all complex roots of modulus `> 1`, lies
in the **unstable subspace**.

Proof: the restriction `T` of `A` to `ker q(A)` is invertible (`0` is not a root of `q`), and
`T⁻¹` is annihilated by `q.reverse`, whose roots have modulus `< 1`
(`aeval_symm_reverse_eq_zero`, `norm_lt_one_of_aeval_reverse_eq_zero`); so `n ↦ T⁻ⁿ v` is a
backward orbit tending to `0` (`tendsto_pow_apply_of_aeval_eq_zero`). -/
theorem ker_aeval_le_unstableSubspace (A : E →L[ℝ] E) {q : ℝ[X]}
    (hq : ∀ μ : ℂ, aeval μ q = 0 → 1 < ‖μ‖) :
    LinearMap.ker (aeval (A : E →ₗ[ℝ] E) q) ≤ A.unstableSubspace := by
  intro v hv
  set K := LinearMap.ker (aeval (A : E →ₗ[ℝ] E) q)
  set Ak : K →L[ℝ] K := A.restrict fun _ hv ↦ map_mem_ker_aeval A q hv
  have hAk : aeval (Ak : K →ₗ[ℝ] K) q = 0 := aeval_restrict_eq_zero _ le_rfl
  -- `0` is not a root of `q`, so `Ak` is injective
  have hc : q.coeff 0 ≠ 0 := by
    intro h0
    have h0' : aeval (0 : ℂ) q = 0 := by rw [← coeff_zero_eq_aeval_zero', h0, map_zero]
    exact absurd (hq 0 h0') (by simp)
  have hinj : Function.Injective (Ak : K →ₗ[ℝ] K) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have h1 := LinearMap.congr_fun hAk x
    rw [← divX_mul_X_add q, aeval_add, aeval_mul, aeval_X, aeval_C, LinearMap.add_apply,
      Module.End.mul_apply, hx, map_zero, zero_add, Module.algebraMap_end_apply,
      LinearMap.zero_apply] at h1
    exact (smul_eq_zero.1 h1).resolve_left hc
  -- so it is a continuous linear equivalence `T`, and `T⁻¹` is annihilated by `q.reverse`
  set T : K ≃L[ℝ] K := (LinearEquiv.ofInjectiveEndo _ hinj).toContinuousLinearEquiv
  have hT : ((T : K →L[ℝ] K) : K →ₗ[ℝ] K) = (Ak : K →ₗ[ℝ] K) := LinearMap.ext fun _ ↦ rfl
  have hrev := aeval_symm_reverse_eq_zero T (hT ▸ hAk)
  have ht := (continuous_subtype_val.tendsto 0).comp
    (tendsto_pow_apply_of_aeval_eq_zero _ hrev
      (fun μ hμ ↦ norm_lt_one_of_aeval_reverse_eq_zero hq hμ) ⟨v, hv⟩)
  -- `n ↦ T⁻ⁿ v` is a backward orbit of `v` tending to `0`
  have hTy (y : K) : (T y : E) = A y := rfl
  refine ⟨fun n ↦ (((T.symm : K →L[ℝ] K) ^ n) ⟨v, hv⟩ : E), by simp, fun n ↦ ?_,
    by simpa [Function.comp_def] using ht⟩
  dsimp only
  rw [pow_succ', mul_apply_eq_comp, ← hTy, ContinuousLinearEquiv.coe_coe,
    T.apply_symm_apply]

/-- For a hyperbolic `A`, the characteristic polynomial is, up to a unit, a product `pₛ pᵤ` of
coprime factors with all complex roots inside, resp. outside, the unit circle, whose kernels at `A`
span the space (Cayley–Hamilton). -/
private lemma exists_factors_sup_ker_aeval_eq_top {A : E →L[ℝ] E} (hA : A.IsHyperbolic) :
    ∃ ps pu : ℝ[X], Associated (ps * pu) (LinearMap.charpoly (A : E →ₗ[ℝ] E)) ∧
      IsCoprime ps pu ∧ (∀ μ : ℂ, aeval μ ps = 0 → ‖μ‖ < 1) ∧
      (∀ μ : ℂ, aeval μ pu = 0 → 1 < ‖μ‖) ∧
      LinearMap.ker (aeval (A : E →ₗ[ℝ] E) ps) ⊔ LinearMap.ker (aeval (A : E →ₗ[ℝ] E) pu) = ⊤ := by
  obtain ⟨ps, pu, hassoc, hcop, hs, hu⟩ :=
    exists_isCoprime_roots_lt_one_one_lt (LinearMap.charpoly_monic (A : E →ₗ[ℝ] E)).ne_zero hA
  refine ⟨ps, pu, hassoc, hcop, hs, hu, ?_⟩
  rw [sup_ker_aeval_eq_ker_aeval_mul_of_coprime _ hcop, LinearMap.ker_eq_top]
  obtain ⟨r, hr⟩ := hassoc.symm.dvd
  rw [hr, aeval_mul, LinearMap.aeval_self_charpoly, zero_mul]

/-- For a hyperbolic `A`, the stable and unstable subspaces **span** the space.

Proof: factor the characteristic polynomial `χ` as `pₛ pᵤ` (up to a unit) with coprime factors
(`Polynomial.exists_isCoprime_roots_lt_one_one_lt`); then
`ker pₛ(A) ⊔ ker pᵤ(A) = ker χ(A) = ⊤` (`Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime`,
`LinearMap.aeval_self_charpoly`), and `ker pₛ(A) ≤ Eₛ`, `ker pᵤ(A) ≤ Eᵤ`. -/
theorem codisjoint_stableSubspace_unstableSubspace {A : E →L[ℝ] E} (hA : A.IsHyperbolic) :
    Codisjoint A.stableSubspace A.unstableSubspace := by
  obtain ⟨ps, pu, -, -, hs, hu, htop⟩ := exists_factors_sup_ker_aeval_eq_top hA
  rw [codisjoint_iff, eq_top_iff, ← htop]
  exact sup_le_sup (ker_aeval_le_stableSubspace A hs) (ker_aeval_le_unstableSubspace A hu)

omit [FiniteDimensional ℝ E] in
/-- If `K' ≤ K` and `L' ≤ L` with `K' ⊔ L' = ⊤` and `K ⊓ L = 0`, then `K = K'`. -/
private lemma eq_of_le_of_sup_eq_top {K L K' L' : Submodule ℝ E} (hK : K' ≤ K) (hL : L' ≤ L)
    (htop : K' ⊔ L' = ⊤) (hdis : Disjoint K L) : K = K' := by
  have hcodis : Codisjoint K' L' := codisjoint_iff.2 htop
  exact ((le_iff_eq_of_codisjoint_of_disjoint hcodis
    (hdis.symm.mono_left hL)).1 hK).symm

/-- **The stable and unstable subspaces as kernels**: for a hyperbolic `A`, the characteristic
polynomial is, up to a unit, a product `pₛ pᵤ` of coprime real polynomials with all complex roots
inside, resp. outside, the unit circle, and `Eₛ = ker pₛ(A)`, `Eᵤ = ker pᵤ(A)`. By the primary
decomposition, these kernels are the sums of the generalized eigenspaces of the eigenvalues of
modulus `< 1`, resp. `> 1`.

Proof: `ker pₛ(A) ⊔ ker pᵤ(A) = ⊤`, `ker pₛ(A) ≤ Eₛ`, `ker pᵤ(A) ≤ Eᵤ`, and `Eₛ ⊓ Eᵤ = 0`
(`disjoint_stableSubspace_unstableSubspace`). The modular-lattice law gives equality in both
submodule inclusions. -/
theorem exists_stableSubspace_unstableSubspace_eq_ker_aeval {A : E →L[ℝ] E}
    (hA : A.IsHyperbolic) :
    ∃ ps pu : ℝ[X], Associated (ps * pu) (LinearMap.charpoly (A : E →ₗ[ℝ] E)) ∧
      IsCoprime ps pu ∧ (∀ μ : ℂ, aeval μ ps = 0 → ‖μ‖ < 1) ∧
      (∀ μ : ℂ, aeval μ pu = 0 → 1 < ‖μ‖) ∧
      A.stableSubspace = LinearMap.ker (aeval (A : E →ₗ[ℝ] E) ps) ∧
      A.unstableSubspace = LinearMap.ker (aeval (A : E →ₗ[ℝ] E) pu) := by
  obtain ⟨ps, pu, hassoc, hcop, hs, hu, htop⟩ := exists_factors_sup_ker_aeval_eq_top hA
  have hKs := ker_aeval_le_stableSubspace A hs
  have hKu := ker_aeval_le_unstableSubspace A hu
  have hdis := A.disjoint_stableSubspace_unstableSubspace
  exact ⟨ps, pu, hassoc, hcop, hs, hu, eq_of_le_of_sup_eq_top hKs hKu htop hdis,
    eq_of_le_of_sup_eq_top hKu hKs (by rwa [sup_comm] at htop) hdis.symm⟩

/-- **The hyperbolic splitting**: for a hyperbolic linear map the stable and unstable subspaces are
complementary, `E = Eₛ ⊕ Eᵤ`. -/
theorem isCompl_stableSubspace_unstableSubspace {A : E →L[ℝ] E} (hA : A.IsHyperbolic) :
    IsCompl (stableSubspace A) (unstableSubspace A) :=
  ⟨A.disjoint_stableSubspace_unstableSubspace, codisjoint_stableSubspace_unstableSubspace hA⟩

end ContinuousLinearMap
