/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# The coefficient `ℓ¹`-norm of integer multivariate polynomials

`MvPolynomial.l1Norm f` is the sum of the absolute values of the coefficients of an integer
polynomial `f`, as a natural number.

## Main results

* `MvPolynomial.l1Norm_add_le`, `MvPolynomial.l1Norm_mul_le`, `MvPolynomial.l1Norm_sum_le`,
  `MvPolynomial.l1Norm_prod_le`, `MvPolynomial.l1Norm_pow_le`: the norm is subadditive and
  submultiplicative.
* `MvPolynomial.l1Norm_det_le`: the norm of a determinant is at most `n! * L ^ n` when every
  entry has norm at most `L`.
* `MvPolynomial.l1Norm_rename_le`: renaming variables does not increase the norm.
* `MvPolynomial.l1Norm_coeff_le_l1Norm_sumAlgEquiv_symm`: a coefficient of a polynomial with
  polynomial coefficients has norm at most that of the flattened polynomial.
-/

@[expose] public section

namespace MvPolynomial

variable {σ : Type*}

/-- The sum of the absolute values of all coefficients of an integer polynomial. -/
def l1Norm (f : MvPolynomial σ ℤ) : ℕ :=
  f.support.sum fun m => (f.coeff m).natAbs

/-- The zero polynomial has `ℓ¹`-norm zero. -/
@[simp] lemma l1Norm_zero : l1Norm (0 : MvPolynomial σ ℤ) = 0 := by
  simp [l1Norm]

/-- The `ℓ¹`-norm of `f` is the sum of the absolute values of its coefficients over any finite set
`s` of exponents containing the support of `f`. -/
lemma l1Norm_eq_sum_of_support_subset (f : MvPolynomial σ ℤ)
    (s : Finset (σ →₀ ℕ)) (hs : f.support ⊆ s) :
    l1Norm f = ∑ m ∈ s, (f.coeff m).natAbs := by
  classical
  apply Finset.sum_subset hs
  intro m _ hm
  simp [notMem_support_iff.mp hm]

/-- Each coefficient of `f` has absolute value at most the `ℓ¹`-norm of `f`. -/
lemma natAbs_coeff_le_l1Norm (f : MvPolynomial σ ℤ) (m : σ →₀ ℕ) :
    (f.coeff m).natAbs ≤ l1Norm f := by
  classical
  by_cases hm : m ∈ f.support
  · exact Finset.single_le_sum (fun j _ => Nat.zero_le (f.coeff j).natAbs) hm
  · simp [notMem_support_iff.mp hm]

/-- The `ℓ¹`-norm of the monomial `monomial m c` is the absolute value of `c`. -/
@[simp] lemma l1Norm_monomial (m : σ →₀ ℕ) (c : ℤ) :
    l1Norm (monomial m c) = c.natAbs := by
  classical
  rw [l1Norm_eq_sum_of_support_subset _ {m} support_monomial_subset]
  simp

/-- The `ℓ¹`-norm of the constant polynomial `C c` is the absolute value of `c`. -/
lemma l1Norm_C (c : ℤ) :
    l1Norm (C c : MvPolynomial σ ℤ) = c.natAbs := by
  exact l1Norm_monomial 0 c

/-- An integer cast has `ℓ¹`-norm equal to its absolute value. -/
@[simp] lemma l1Norm_intCast (c : ℤ) :
    l1Norm (c : MvPolynomial σ ℤ) = c.natAbs := by
  simpa only [eq_intCast] using l1Norm_C (σ := σ) c

/-- The constant polynomial `1` has `ℓ¹`-norm one. -/
@[simp] lemma l1Norm_one : l1Norm (1 : MvPolynomial σ ℤ) = 1 := by
  simpa using l1Norm_C (σ := σ) 1

/-- The `ℓ¹`-norm is subadditive. -/
lemma l1Norm_add_le (f g : MvPolynomial σ ℤ) :
    l1Norm (f + g) ≤ l1Norm f + l1Norm g := by
  classical
  rw [l1Norm_eq_sum_of_support_subset (f + g) (f.support ∪ g.support)
    support_add,
    l1Norm_eq_sum_of_support_subset f (f.support ∪ g.support)
      Finset.subset_union_left,
    l1Norm_eq_sum_of_support_subset g (f.support ∪ g.support)
      Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun m _ => by simpa using Int.natAbs_add_le (f.coeff m) (g.coeff m)

/-- The `ℓ¹`-norm of a finite sum is at most the sum of the `ℓ¹`-norms of the summands. -/
lemma l1Norm_sum_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1Norm (∑ i ∈ s, f i) ≤ ∑ i ∈ s, l1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simpa only [Finset.sum_insert hi] using
        (l1Norm_add_le (f i) (∑ j ∈ s, f j)).trans (Nat.add_le_add_left ih _)

/-- The `ℓ¹`-norm is submultiplicative. -/
lemma l1Norm_mul_le (f g : MvPolynomial σ ℤ) :
    l1Norm (f * g) ≤ l1Norm f * l1Norm g := by
  classical
  calc
    l1Norm (f * g) = l1Norm
        (∑ m ∈ f.support, ∑ n ∈ g.support, monomial m (f.coeff m) *
          monomial n (g.coeff n)) := by
      congr 1
      conv_lhs => rw [f.as_sum, g.as_sum]
      rw [Finset.sum_mul]
      simp only [Finset.mul_sum]
    _ ≤ ∑ m ∈ f.support, ∑ n ∈ g.support,
        l1Norm (monomial m (f.coeff m) * monomial n (g.coeff n)) :=
      (l1Norm_sum_le _ _).trans (Finset.sum_le_sum fun _ _ => l1Norm_sum_le _ _)
    _ = l1Norm f * l1Norm g := by
      simp only [monomial_mul_monomial, l1Norm_monomial, Int.natAbs_mul]
      simp only [← Finset.mul_sum, ← Finset.sum_mul, l1Norm]

/-- The `ℓ¹`-norm of a finite product is at most the product of the `ℓ¹`-norms of the factors. -/
lemma l1Norm_prod_le {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ ℤ) :
    l1Norm (∏ i ∈ s, f i) ≤ ∏ i ∈ s, l1Norm (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using
        (l1Norm_mul_le (f i) (∏ j ∈ s, f j)).trans (Nat.mul_le_mul_left _ ih)

/-- The `ℓ¹`-norm of `f ^ n` is at most the `n`-th power of the `ℓ¹`-norm of `f`. -/
lemma l1Norm_pow_le {σ : Type*} (f : MvPolynomial σ ℤ) (n : ℕ) :
    l1Norm (f ^ n) ≤ l1Norm f ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (l1Norm_mul_le _ _).trans (Nat.mul_le_mul_right _ ih)

/-- Negation preserves the `ℓ¹`-norm. -/
@[simp] lemma l1Norm_neg (f : MvPolynomial σ ℤ) :
    l1Norm (-f) = l1Norm f := by
  classical
  simp [l1Norm]

/-- Multiplication by an integer unit, that is by `±1`, preserves the `ℓ¹`-norm. -/
@[simp] lemma l1Norm_units_smul (u : ℤˣ) (f : MvPolynomial σ ℤ) :
    l1Norm (u • f) = l1Norm f := by
  rcases Int.units_eq_one_or u with h | h <;> simp [h]

/-- If every entry of a square matrix `M` of integer polynomials has `ℓ¹`-norm at most `L`, then the
determinant of `M` has `ℓ¹`-norm at most `n! * L ^ n`, where `n` is the size of `M`. -/
lemma l1Norm_det_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι (MvPolynomial σ ℤ)) (L : ℕ)
    (hM : ∀ i j, l1Norm (M i j) ≤ L) :
    l1Norm M.det ≤ (Fintype.card ι).factorial * L ^ Fintype.card ι := by
  classical
  rw [Matrix.det_apply]
  calc
    l1Norm (∑ p : Equiv.Perm ι, p.sign • ∏ i, M (p i) i) ≤
        ∑ p : Equiv.Perm ι, l1Norm (p.sign • ∏ i, M (p i) i) :=
      l1Norm_sum_le _ _
    _ ≤ ∑ _p : Equiv.Perm ι, L ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro p _
      rw [l1Norm_units_smul]
      exact (l1Norm_prod_le _ _).trans (by
        simpa using Finset.prod_le_prod (fun i (_ : i ∈ Finset.univ) => hM (p i) i))
    _ = (Fintype.card ι).factorial * L ^ Fintype.card ι := by
      simp [Fintype.card_perm]


/-- Renaming the variables along any map `v` does not increase the `ℓ¹`-norm. -/
lemma l1Norm_rename_le {σ τ : Type*} (v : σ → τ) (f : MvPolynomial σ ℤ) :
    l1Norm (rename v f) ≤ l1Norm f := by
  classical
  calc
    l1Norm (rename v f) = l1Norm
        (∑ m ∈ f.support, monomial (m.mapDomain v) (f.coeff m)) := by
      congr 1
      conv_lhs => rw [f.as_sum]
      simp only [map_sum, rename_monomial]
    _ ≤ ∑ m ∈ f.support, l1Norm (monomial (m.mapDomain v) (f.coeff m)) :=
      l1Norm_sum_le _ _
    _ = l1Norm f := by
      simp only [l1Norm_monomial]
      rfl

/-- The coefficient of the flattened polynomial `(sumAlgEquiv ℤ σ τ).symm f` at the exponent on
`σ ⊕ τ` assembled from `m` and `n` is the coefficient at `n` of the coefficient of `f` at `m`. -/
lemma coeff_sumAlgEquiv_symm {σ τ : Type*}
    (f : MvPolynomial σ (MvPolynomial τ ℤ)) (m : σ →₀ ℕ) (n : τ →₀ ℕ) :
    ((sumAlgEquiv ℤ σ τ).symm f).coeff
      (Finsupp.sumFinsuppAddEquivProdFinsupp.symm (m,n)) = (f.coeff m).coeff n := by
  simp [sumAlgEquiv, AddMonoidAlgebra.curryAlgEquiv,
    AddMonoidAlgebra.curryRingEquiv, AddMonoidAlgebra.curryAddEquiv]
  rfl

/-- Extracting one outer coefficient never increases the total coefficient
sum after flattening the two variable families. -/
theorem l1Norm_coeff_le_l1Norm_sumAlgEquiv_symm {σ τ : Type*}
    (f : MvPolynomial σ (MvPolynomial τ ℤ)) (m : σ →₀ ℕ) :
    l1Norm (f.coeff m) ≤ l1Norm ((sumAlgEquiv ℤ σ τ).symm f) := by
  classical
  let e : (τ →₀ ℕ) → (σ ⊕ τ →₀ ℕ) :=
    fun n => Finsupp.sumFinsuppAddEquivProdFinsupp.symm (m,n)
  have hinj : Function.Injective e := by
    intro n n' h
    exact congrArg Prod.snd (Finsupp.sumFinsuppAddEquivProdFinsupp.symm.injective h)
  have hs : (f.coeff m).support.image e ⊆ ((sumAlgEquiv ℤ σ τ).symm f).support := by
    intro a ha
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp ha
    rw [mem_support_iff, coeff_sumAlgEquiv_symm]
    exact mem_support_iff.mp hn
  calc
    l1Norm (f.coeff m) =
        ∑ a ∈ (f.coeff m).support.image e,
          (((sumAlgEquiv ℤ σ τ).symm f).coeff a).natAbs := by
      rw [Finset.sum_image (fun a _ b _ h => hinj h)]
      simp only [e, coeff_sumAlgEquiv_symm, l1Norm]
    _ ≤ l1Norm ((sumAlgEquiv ℤ σ τ).symm f) :=
      Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => Nat.zero_le _)

/-- Flattening a polynomial whose coefficients are constants of `MvPolynomial τ ℤ` renames its
variables into the left summand of `σ ⊕ τ`. -/
lemma sumAlgEquiv_symm_map_C {σ τ : Type*} (p : MvPolynomial σ ℤ) :
    (sumAlgEquiv ℤ σ τ).symm (map (C : ℤ →+* MvPolynomial τ ℤ) p) =
      rename Sum.inl p := by
  rw [AlgEquiv.symm_apply_eq]
  exact (DFunLike.congr_fun
    (sumAlgEquiv_comp_rename_inl (R := ℤ) (S₁ := σ) (S₂ := τ)) p).symm

/-- One original coefficient variable multiplying an integer parameter
polynomial has no coefficient-norm cost beyond that parameter polynomial. -/
theorem l1Norm_sumAlgEquiv_symm_C_X_mul_map_C_le {σ τ : Type*}
    (p : MvPolynomial σ ℤ) (i : τ) :
    l1Norm ((sumAlgEquiv ℤ σ τ).symm
      (C (X i) * map (C : ℤ →+* MvPolynomial τ ℤ) p)) ≤ l1Norm p := by
  rw [map_mul, sumAlgEquiv_symm_C_X, sumAlgEquiv_symm_map_C]
  apply (l1Norm_mul_le _ _).trans
  simpa only [X, l1Norm_monomial, Int.natAbs_one, one_mul] using
    l1Norm_rename_le Sum.inl p

end MvPolynomial
