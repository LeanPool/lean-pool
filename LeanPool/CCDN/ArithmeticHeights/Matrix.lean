/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.Extension
public import LeanPool.CCDN.ArithmeticHeights.LinearForm
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import all Mathlib.NumberTheory.Height.Basic

/-!
# The height of a matrix

The height of a matrix here is the sup-norm height of the tuple of its **entries**.
Row-space heights instead use the tuple of maximal minors and belong to Layer 3.
Bombieri–Vaaler's `H(A)` is the absolute Arakelov height of those minors, using Euclidean norms
at infinity. This file uses `Matrix.mulHeight` for the sup-norm entry height.

The content of the file is four bounds.

* The **product bound** `Matrix.mulHeight_mul_le`, with the constant `Fintype.card n ^ totalWeight
  K` for the inner index type `n`. It is the tuple sum bound of Layer 2.4 applied to the
  multiplication table of the entries of `A` and of `B`: an entry of `A * B` is a sum of
  `Fintype.card n` entries of that one table, and the Segre relation evaluates its height.
* The **Arakelov product bound** `Matrix.arakelovMulHeight_mul_le`, with constant exactly `1`.
  Cauchy–Schwarz entry by entry produces the Frobenius norm, which is submultiplicative; the
  cardinality of the inner index type is not paid at all. This is the matrix form of
  `NumberField.arakelovMulHeight_linearMap_apply_le` and the reason Layer 0 carries two
  normalizations.
* The **determinant bound** `Matrix.mulHeight₁_det_le`. It cannot be stated with `mulHeight A` on
  the right: `A ↦ c • A` fixes the projective height of the matrix and multiplies the determinant
  by `c ^ n`, which `Matrix.exists_not_mulHeight₁_det_le` records. What is true uses the *affine*
  height of Layer 0.5, and the sharp form of it is columnwise, one affine column height per column,
  with the constant `(Fintype.card n)! ^ totalWeight K` from the Leibniz expansion.
* The action on tuples, `Matrix.mulHeight_mulVec_le`, which is Mathlib's
  `Height.mulHeight_linearMap_apply_le` read through the definition, and its Arakelov companion.

The Leibniz expansion carries the signs of the permutations, so the tuple sum bound is used here
through `Height.mulHeight_sum_sign_comp_le'`, a version whose summands may be multiplied by `±1`.
That version is deduced from the unsigned one by doubling the alphabet with a `Bool`, whose two
letters `1` and `-1` have height `1`.

## Main definitions

* `Matrix.mulHeight A` and `Matrix.logHeight A`: the height of the tuple of entries of `A`.
* `Matrix.mulHeightAff A` and `Matrix.logHeightAff A`: its affine counterpart, the height of the
  tuple of entries with a coordinate `1` appended.
* `Matrix.arakelovMulHeight A` and `Matrix.arakelovLogHeight A`: the same in the Arakelov
  normalization, over a number field.

## Main results

* `Matrix.mulHeight_transpose`, `Matrix.mulHeight_submatrix_le`,
  `Matrix.mulHeight_submatrix_equiv` and `Matrix.mulHeight_smul`: invariance under transpose, under
  re-indexing of rows and columns — in particular under row and column permutations — and under
  scaling, and the submatrix bound.
* `Matrix.mulHeight_mul_le` and `Matrix.logHeight_mul_le`: the product bound.
* `Matrix.arakelovMulHeight_mul_le` and `Matrix.arakelovLogHeight_mul_le`: the product bound in the
  Arakelov normalization, with constant `1`.
* `Matrix.mulHeight₁_det_le` and `Matrix.logHeight₁_det_le`: the determinant against the affine
  heights of the columns, and `Matrix.mulHeight₁_det_le_mulHeightAff_pow` against the affine height
  of the matrix.
* `Matrix.exists_not_mulHeight₁_det_le`: no constant bounds the height of a determinant by the
  projective height of the matrix.
* `Height.mulHeight_sum_sign_comp_le'`: the signed tuple sum bound.

## Implementation notes

`Matrix m n K` is definitionally `m → n → K`, and `Height.mulHeight` takes a tuple, so
`Matrix.mulHeight` is the height of `fun q : m × n ↦ A q.1 q.2`. Every statement about
re-indexing is then a statement about `Prod.map`, and transpose is `Equiv.prodComm`.

The finiteness hypotheses are `Finite` wherever the height alone is involved and `Fintype` only
where a matrix product or a determinant is formed.

`Height.mulHeight_sum_sign_comp_le'` belongs next to the unsigned tuple sum bound of Layer 2.4;
it is here because the determinant is the only consumer so far.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
2.9.8 (p. 75) for the entry-tuple height `H(A)`, and Definition 2.8.1 with 2.8.2–2.8.3
(pp. 66–67) for the local Euclidean factors and absolute Arakelov normalization.
Definition 2.8.11 instead concerns the Grassmannian row-space height, treated separately in
`ArithmeticHeights.RowSpace`.

This is Layer 2.5 of the `ArithmeticHeights` roadmap.
-/

public section

open Finset Function Height AdmissibleAbsValues Real

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {α ι κ : Type*}

/-- The two-letter alphabet `{1, -1}` has height `1`: it is the tuple `![-1, 1]` up to the
re-indexing `finTwoEquiv` and a swap, and `mulHeight₁ (-1) = mulHeight₁ 1 = 1`. -/
private lemma mulHeight_boolSign :
    mulHeight (fun b : Bool ↦ if b then (-1 : K) else 1) = 1 := by
  have he : (fun b : Bool ↦ if b then (-1 : K) else 1) ∘ finTwoEquiv = ![(1 : K), -1] := by
    ext i
    fin_cases i <;> rfl
  rw [← mulHeight_comp_equiv finTwoEquiv, he, mulHeight_swap, ← mulHeight₁_eq_mulHeight,
    show (-1 : K) = -(1 : K) from rfl, mulHeight₁_neg, mulHeight₁_one]

/-- **The signed tuple sum bound.** `Height.mulHeight_sum_comp_le'` with each summand allowed a
sign: if in each coordinate `i` at most `n` entries of one tuple `w`, each possibly negated, are
summed, the height of the tuple of sums is at most `n ^ totalWeight K` times `mulHeight w`.

Signs cost nothing, because `v (-x) = v x` at every absolute value. Formally this is the unsigned
bound for the doubled alphabet `κ × Bool`, whose height is `mulHeight w` by the Segre relation and
`Height.mulHeight_boolSign`. The Leibniz expansion of a determinant is the intended consumer. -/
theorem mulHeight_sum_sign_comp_le' [Finite ι] [Finite κ] {n : ℕ} (hn : 0 < n)
    {s : ι → Finset α} (hs : ∀ i, #(s i) ≤ n) {ε : α → ι → K}
    (hε : ∀ a i, ε a i = 1 ∨ ε a i = -1) (f : α → ι → κ) (w : κ → K) :
    mulHeight (fun i ↦ ∑ a ∈ s i, ε a i * w (f a i)) ≤ (n : ℝ) ^ totalWeight K * mulHeight w := by
  classical
  have hn1 : (1 : ℝ) ≤ (n : ℝ) ^ totalWeight K := one_le_pow₀ (by exact_mod_cast hn)
  rcases eq_or_ne w 0 with rfl | hw
  · have h0 : (fun i ↦ ∑ a ∈ s i, ε a i * (0 : κ → K) (f a i)) = (0 : ι → K) := by
      ext i
      simp
    rw [h0, mulHeight_zero, mulHeight_zero, mul_one]
    exact hn1
  have hy : (fun b : Bool ↦ if b then (-1 : K) else 1) ≠ 0 := fun h ↦ by
    simpa using congrFun h false
  have key := mulHeight_sum_comp_le' hn hs (fun a i ↦ (f a i, decide (ε a i = -1)))
    (fun q : κ × Bool ↦ w q.1 * (if q.2 then (-1 : K) else 1))
  rw [mulHeight_fun_mul_eq hw hy, mulHeight_boolSign, mul_one] at key
  refine le_trans (le_of_eq ?_) key
  congr 1
  funext i
  refine Finset.sum_congr rfl fun a _ ↦ ?_
  by_cases hd : ε a i = -1
  · rw [show decide (ε a i = -1) = true from decide_eq_true hd]
    simp [hd]
  · rw [show decide (ε a i = -1) = false from decide_eq_false hd]
    rcases hε a i with h | h
    · simp [h]
    · exact absurd h hd

end Height

namespace Matrix

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {m n p m' n' : Type*}

/-- **The height of a matrix** is the sup-norm height of the tuple of its **entries**,
corresponding to the entry-tuple construction in Bombieri–Gubler 2.9.8.
Bombieri–Vaaler's `H(A)` instead uses the absolute Arakelov height of the maximal minors. -/
@[expose] noncomputable def mulHeight (A : Matrix m n K) : ℝ :=
  Height.mulHeight fun q : m × n ↦ A q.1 q.2

/-- The logarithmic height of a matrix. As everywhere in this development, the logarithmic height
is *defined* as the logarithm of the multiplicative one and never independently. -/
@[expose] noncomputable def logHeight (A : Matrix m n K) : ℝ := log (mulHeight A)

theorem logHeight_eq_log_mulHeight (A : Matrix m n K) : logHeight A = log (mulHeight A) := rfl

theorem logHeight_eq (A : Matrix m n K) :
    logHeight A = Height.logHeight fun q : m × n ↦ A q.1 q.2 := rfl

/-- **The affine height of a matrix**: the height of the tuple of its entries with a coordinate
`1` appended, `Height.mulHeightAff` of the entries. Unlike `Matrix.mulHeight` it is not invariant
under scaling, which is exactly what a bound on the determinant needs. -/
@[expose] noncomputable def mulHeightAff (A : Matrix m n K) : ℝ :=
  Height.mulHeightAff fun q : m × n ↦ A q.1 q.2

/-- The logarithmic affine height of a matrix. -/
@[expose] noncomputable def logHeightAff (A : Matrix m n K) : ℝ := log (mulHeightAff A)

theorem logHeightAff_eq_log_mulHeightAff (A : Matrix m n K) :
    logHeightAff A = log (mulHeightAff A) :=
  rfl

@[simp]
theorem mulHeight_zero : mulHeight (0 : Matrix m n K) = 1 := Height.mulHeight_zero

@[simp]
theorem logHeight_zero : logHeight (0 : Matrix m n K) = 0 := by
  rw [logHeight_eq_log_mulHeight, mulHeight_zero, log_one]

theorem mulHeight_neg (A : Matrix m n K) : mulHeight (-A) = mulHeight A :=
  Height.mulHeight_neg _

theorem logHeight_neg (A : Matrix m n K) : logHeight (-A) = logHeight A := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, mulHeight_neg]

/-- The height of a matrix is invariant under transpose: transposing re-indexes the entries by
`Equiv.prodComm`. -/
theorem mulHeight_transpose (A : Matrix m n K) : mulHeight Aᵀ = mulHeight A :=
  Height.mulHeight_comp_equiv (Equiv.prodComm n m) fun q : m × n ↦ A q.1 q.2

theorem logHeight_transpose (A : Matrix m n K) : logHeight Aᵀ = logHeight A := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, mulHeight_transpose]

/-- Re-indexing rows and columns by equivalences leaves the height unchanged; taking
`e` and `e'` to be permutations, the height is invariant under row and column permutations. -/
theorem mulHeight_submatrix_equiv (A : Matrix m n K) (e : m' ≃ m) (e' : n' ≃ n) :
    mulHeight (A.submatrix e e') = mulHeight A :=
  Height.mulHeight_comp_equiv (e.prodCongr e') fun q : m × n ↦ A q.1 q.2

theorem logHeight_submatrix_equiv (A : Matrix m n K) (e : m' ≃ m) (e' : n' ≃ n) :
    logHeight (A.submatrix e e') = logHeight A := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, mulHeight_submatrix_equiv]

section Basic

variable [Finite m] [Finite n]

theorem one_le_mulHeight (A : Matrix m n K) : 1 ≤ mulHeight A := Height.one_le_mulHeight _

theorem mulHeight_pos (A : Matrix m n K) : 0 < mulHeight A := Height.mulHeight_pos _

theorem mulHeight_ne_zero (A : Matrix m n K) : mulHeight A ≠ 0 := Height.mulHeight_ne_zero _

theorem logHeight_nonneg (A : Matrix m n K) : 0 ≤ logHeight A := Height.logHeight_nonneg _

theorem one_le_mulHeightAff (A : Matrix m n K) : 1 ≤ mulHeightAff A :=
  Height.one_le_mulHeightAff _

theorem mulHeightAff_pos (A : Matrix m n K) : 0 < mulHeightAff A := Height.mulHeightAff_pos _

theorem mulHeightAff_ne_zero (A : Matrix m n K) : mulHeightAff A ≠ 0 :=
  Height.mulHeightAff_ne_zero _

theorem logHeightAff_nonneg (A : Matrix m n K) : 0 ≤ logHeightAff A :=
  Height.logHeightAff_nonneg _

theorem mulHeight_le_mulHeightAff (A : Matrix m n K) : mulHeight A ≤ mulHeightAff A :=
  Height.mulHeight_le_mulHeightAff _

theorem logHeight_le_logHeightAff (A : Matrix m n K) : logHeight A ≤ logHeightAff A :=
  Height.logHeight_le_logHeightAff _

/-- The affine height of a column of `A` is at most the affine height of `A`: a column is a
sub-tuple of the entries, and the appended coordinate `1` is common to both. -/
theorem mulHeightAff_col_le (A : Matrix m n K) (j : n) :
    Height.mulHeightAff (fun i ↦ A i j) ≤ mulHeightAff A :=
  Height.mulHeightAff_comp_le (fun i ↦ (i, j)) fun q : m × n ↦ A q.1 q.2

theorem mulHeight_submatrix_le [Finite m'] [Finite n'] (A : Matrix m n K) (f : m' → m)
    (g : n' → n) : mulHeight (A.submatrix f g) ≤ mulHeight A :=
  Height.mulHeight_comp_le (Prod.map f g) fun q : m × n ↦ A q.1 q.2

theorem logHeight_submatrix_le [Finite m'] [Finite n'] (A : Matrix m n K) (f : m' → m)
    (g : n' → n) : logHeight (A.submatrix f g) ≤ logHeight A :=
  Height.logHeight_comp_le (Prod.map f g) fun q : m × n ↦ A q.1 q.2

theorem mulHeight_smul (A : Matrix m n K) {c : K} (hc : c ≠ 0) : mulHeight (c • A) = mulHeight A :=
  Height.mulHeight_smul_eq_mulHeight _ hc

theorem logHeight_smul (A : Matrix m n K) {c : K} (hc : c ≠ 0) : logHeight (c • A) = logHeight A :=
  by rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight, mulHeight_smul _ hc]

end Basic

section Mul

variable [Finite m] [Fintype n] [Finite p]

/-- **The product bound.** An entry of `A * B` is a sum of
`Fintype.card n` entries of the multiplication table of the entries of `A` and of `B`, so the
tuple sum bound of Layer 2.4 applies with `#s = Fintype.card n`, and the Segre relation evaluates
the height of that table as `mulHeight A * mulHeight B`.

`n` must be nonempty: for `n` empty `A * B = 0` has the junk height `1` against a right-hand side
of `0`. The constant is sharp, and its exponent `totalWeight K` is needed as soon as `K` has
degree `> 1`; both are the examples at the end of this file. In the Arakelov normalization the
constant disappears entirely, `Matrix.arakelovMulHeight_mul_le`. -/
theorem mulHeight_mul_le [Nonempty n] (A : Matrix m n K) (B : Matrix n p K) :
    mulHeight (A * B) ≤ (Fintype.card n : ℝ) ^ totalWeight K * (mulHeight A * mulHeight B) := by
  have hcard : (1 : ℝ) ≤ (Fintype.card n : ℝ) ^ totalWeight K :=
    one_le_pow₀ (by exact_mod_cast Fintype.card_pos)
  have key := Height.mulHeight_sum_comp_le' (K := K) (ι := m × p) (α := n)
    (n := Fintype.card n) Fintype.card_pos (s := fun _ ↦ (univ : Finset n))
    (fun _ ↦ le_of_eq card_univ) (fun k q ↦ ((q.1, k), (k, q.2)))
    (fun r : (m × n) × (n × p) ↦ A r.1.1 r.1.2 * B r.2.1 r.2.2)
  have hL : (fun q : m × p ↦ ∑ k ∈ (univ : Finset n), A q.1 k * B k q.2)
      = fun q : m × p ↦ (A * B) q.1 q.2 := by
    ext q
    rw [Matrix.mul_apply]
  rw [hL] at key
  have hone : (1 : ℝ) ≤ (Fintype.card n : ℝ) ^ totalWeight K * (mulHeight A * mulHeight B) :=
    hcard.trans <| le_mul_of_one_le_right (by positivity)
      (one_le_mul_of_one_le_of_one_le (one_le_mulHeight _) (one_le_mulHeight _))
  rcases eq_or_ne (fun q : m × n ↦ A q.1 q.2) 0 with hA | hA
  · have hAB : A * B = 0 := by
      have : A = 0 := by ext i k; exact congrFun hA (i, k)
      simp [this]
    rwa [hAB, mulHeight_zero]
  rcases eq_or_ne (fun q : n × p ↦ B q.1 q.2) 0 with hB | hB
  · have hAB : A * B = 0 := by
      have : B = 0 := by ext k j; exact congrFun hB (k, j)
      simp [this]
    rwa [hAB, mulHeight_zero]
  rwa [Height.mulHeight_fun_mul_eq hA hB] at key

/-- The logarithmic form of `Matrix.mulHeight_mul_le`. -/
theorem logHeight_mul_le [Nonempty n] (A : Matrix m n K) (B : Matrix n p K) :
    logHeight (A * B) ≤ totalWeight K * log (Fintype.card n) + (logHeight A + logHeight B) := by
  have hcard : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos (α := n)
  simp only [logHeight_eq_log_mulHeight]
  refine (log_le_log (mulHeight_pos _) (mulHeight_mul_le A B)).trans_eq ?_
  rw [log_mul (pow_ne_zero _ hcard.ne') (mul_ne_zero (mulHeight_ne_zero A) (mulHeight_ne_zero B)),
    log_mul (mulHeight_ne_zero A) (mulHeight_ne_zero B), log_pow]

/-- **The action on tuples**, Mathlib's `Height.mulHeight_linearMap_apply_le` read through the
definition of `Matrix.mulHeight`. Nothing is reproved here. -/
theorem mulHeight_mulVec_le [Nonempty n] (A : Matrix m n K) (x : n → K) :
    Height.mulHeight (A.mulVec x)
      ≤ (Fintype.card n : ℝ) ^ totalWeight K * mulHeight A * Height.mulHeight x := by
  have := Height.mulHeight_linearMap_apply_le (fun q : m × n ↦ A q.1 q.2) x
  rwa [Nat.card_eq_fintype_card] at this

/-- The logarithmic form of `Matrix.mulHeight_mulVec_le`. -/
theorem logHeight_mulVec_le [Nonempty n] (A : Matrix m n K) (x : n → K) :
    Height.logHeight (A.mulVec x)
      ≤ totalWeight K * log (Fintype.card n) + (logHeight A + Height.logHeight x) := by
  have hcard : (0 : ℝ) < (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos (α := n)
  simp only [logHeight_eq_log_mulHeight, Height.logHeight_eq_log_mulHeight]
  refine (log_le_log (Height.mulHeight_pos _) (mulHeight_mulVec_le A x)).trans_eq ?_
  rw [mul_assoc, log_mul (pow_ne_zero _ hcard.ne')
      (mul_ne_zero (mulHeight_ne_zero A) (Height.mulHeight_ne_zero x)),
    log_mul (mulHeight_ne_zero A) (Height.mulHeight_ne_zero x), log_pow]

end Mul

section Det

variable [Fintype n] [DecidableEq n]

/-- **The height of a determinant**, from the Leibniz expansion. The determinant is a sum of
`(Fintype.card n)!` products, one entry from each column, so the signed tuple sum bound applies to
the multiplication table of the affine columns and the Segre relation of
`Height.mulHeight_fun_prod_eq` evaluates its height as the product of the affine column heights.

The right-hand side cannot be made scaling-invariant: see
`Matrix.exists_not_mulHeight₁_det_le`. -/
theorem mulHeight₁_det_le (A : Matrix n n K) :
    Height.mulHeight₁ A.det ≤ (Nat.factorial (Fintype.card n) : ℝ) ^ totalWeight K
      * ∏ j, Height.mulHeightAff fun i ↦ A i j := by
  classical
  set x : n → Option n → K := fun j o ↦ o.elim 1 fun i ↦ A i j with hxdef
  have hxne : ∀ j, x j ≠ 0 := fun j ↦ Height.optionElim_one_ne_zero _
  set w : (n → Option n) → K := fun I ↦ ∏ j, x j (I j) with hwdef
  have hwh : Height.mulHeight w = ∏ j, Height.mulHeightAff fun i ↦ A i j :=
    Height.mulHeight_fun_prod_eq hxne
  set ee : Equiv.Perm n → Fin 2 → K := fun σ ↦ ![((Equiv.Perm.sign σ : ℤ) : K), 1] with heedef
  have hee : ∀ σ i, ee σ i = 1 ∨ ee σ i = -1 := by
    intro σ i
    fin_cases i
    · rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [heedef, h]
    · simp [heedef]
  set s : Fin 2 → Finset (Equiv.Perm n) := ![Finset.univ, {1}] with hsdef
  have hcard : ∀ i, #(s i) ≤ Nat.factorial (Fintype.card n) := by
    intro i
    fin_cases i
    · simp [hsdef, Finset.card_univ, Fintype.card_perm]
    · simpa [hsdef] using (Nat.factorial_pos (Fintype.card n)).nat_succ_le
  set f : Equiv.Perm n → Fin 2 → (n → Option n) :=
    fun σ ↦ ![fun j ↦ some (σ j), fun _ ↦ none] with hfdef
  have key := Height.mulHeight_sum_sign_comp_le' (K := K) (Nat.factorial_pos (Fintype.card n))
    hcard hee f w
  have hval : (fun i ↦ ∑ a ∈ s i, ee a i * w (f a i)) = ![A.det, 1] := by
    ext i
    fin_cases i
    · simp [hsdef, hwdef, hxdef, heedef, hfdef, Matrix.det_apply']
    · simp [hsdef, hwdef, hxdef, heedef, hfdef]
  rw [hval, hwh] at key
  rwa [Height.mulHeight₁_eq_mulHeight]

/-- The logarithmic form of `Matrix.mulHeight₁_det_le`. -/
theorem logHeight₁_det_le (A : Matrix n n K) :
    Height.logHeight₁ A.det ≤ totalWeight K * log (Nat.factorial (Fintype.card n))
      + ∑ j, Height.logHeightAff fun i ↦ A i j := by
  have hf : (0 : ℝ) < Nat.factorial (Fintype.card n) := by
    exact_mod_cast Nat.factorial_pos (Fintype.card n)
  simp only [Height.logHeight₁_eq_log_mulHeight₁, Height.logHeightAff_eq_log_mulHeightAff]
  rw [← log_prod fun j _ ↦ Height.mulHeightAff_ne_zero (fun i ↦ A i j)]
  refine (log_le_log (Height.mulHeight₁_pos _) (mulHeight₁_det_le A)).trans_eq ?_
  rw [log_mul (pow_ne_zero _ hf.ne')
    (Finset.prod_ne_zero_iff.mpr fun j _ ↦ Height.mulHeightAff_ne_zero _), log_pow]

/-- `Matrix.mulHeight₁_det_le` with the affine height of the whole matrix in place of the affine
heights of its columns. This is the form the roadmap states, except that the height on the right
is the affine one. -/
theorem mulHeight₁_det_le_mulHeightAff_pow (A : Matrix n n K) :
    Height.mulHeight₁ A.det ≤ (Nat.factorial (Fintype.card n) : ℝ) ^ totalWeight K
      * mulHeightAff A ^ Fintype.card n := by
  refine (mulHeight₁_det_le A).trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  calc ∏ j, Height.mulHeightAff (fun i ↦ A i j) ≤ ∏ _j : n, mulHeightAff A :=
        Finset.prod_le_prod₀ (fun j _ ↦ (Height.mulHeightAff_pos _).le)
          fun j _ ↦ mulHeightAff_col_le A j
    _ = mulHeightAff A ^ Fintype.card n := by rw [Finset.prod_const, Finset.card_univ]

/-- The logarithmic form of `Matrix.mulHeight₁_det_le_mulHeightAff_pow`. -/
theorem logHeight₁_det_le_mulHeightAff_pow (A : Matrix n n K) :
    Height.logHeight₁ A.det ≤ totalWeight K * log (Nat.factorial (Fintype.card n))
      + Fintype.card n * logHeightAff A := by
  have hf : (0 : ℝ) < Nat.factorial (Fintype.card n) := by
    exact_mod_cast Nat.factorial_pos (Fintype.card n)
  simp only [Height.logHeight₁_eq_log_mulHeight₁, logHeightAff_eq_log_mulHeightAff]
  refine (log_le_log (Height.mulHeight₁_pos _) (mulHeight₁_det_le_mulHeightAff_pow A)).trans_eq ?_
  rw [log_mul (pow_ne_zero _ hf.ne') (pow_ne_zero _ (mulHeightAff_ne_zero A)), log_pow, log_pow]

end Det

/-- **The determinant is not bounded by the projective height of the matrix.** For a `1 × 1`
matrix the index type is a subsingleton, so `mulHeight A = 1` whatever the entry is, while the
determinant is that entry. This is the same scaling obstruction as in Layer 2.4: `A ↦ c • A`
fixes `mulHeight A` and multiplies `A.det` by `c ^ n`. The affine height of
`Matrix.mulHeight₁_det_le` is what the statement needs. -/
theorem exists_not_mulHeight₁_det_le (c : ℝ) :
    ∃ A : Matrix (Fin 1) (Fin 1) ℚ, ¬ Height.mulHeight₁ A.det ≤ c * mulHeight A := by
  obtain ⟨N, hN⟩ := exists_nat_gt (max c 1)
  have hN1 : (1 : ℝ) < N := (le_max_right c 1).trans_lt hN
  have hN0 : N ≠ 0 := by
    rintro rfl
    norm_num at hN1
  have : NeZero N := ⟨hN0⟩
  refine ⟨Matrix.of ![![(N : ℚ)]], ?_⟩
  rw [mulHeight, Height.mulHeight_eq_one_of_subsingleton, mul_one, Matrix.det_fin_one,
    show (Matrix.of ![![(N : ℚ)]] : Matrix (Fin 1) (Fin 1) ℚ) 0 0 = ((N : ℕ) : ℚ) from rfl,
    Rat.mulHeight₁_natCast]
  exact not_le.2 ((le_max_left c 1).trans_lt hN)

end Matrix

namespace Matrix

variable {K : Type*} [Field K] [NumberField K] {m n p : Type*} [Fintype m] [Fintype n] [Fintype p]

/-!
### Matrices in the Arakelov normalization

At an infinite place the local factor of the Arakelov height is the Frobenius norm of the matrix,
and Cauchy–Schwarz entry by entry makes it submultiplicative; at a finite place the sup norm is
submultiplicative by the ultrametric inequality. So the constant
`Fintype.card n ^ totalWeight K` of `Matrix.mulHeight_mul_le` disappears.
-/

/-- **The Arakelov height of a matrix**: the Arakelov height of the tuple of its entries, so the
Frobenius norm at each infinite place and the sup norm at each finite one. -/
@[expose] noncomputable def arakelovMulHeight (A : Matrix m n K) : ℝ :=
  NumberField.arakelovMulHeight fun q : m × n ↦ A q.1 q.2

/-- The logarithmic Arakelov height of a matrix. -/
@[expose] noncomputable def arakelovLogHeight (A : Matrix m n K) : ℝ := log (arakelovMulHeight A)

theorem arakelovLogHeight_eq_log_arakelovMulHeight (A : Matrix m n K) :
    arakelovLogHeight A = log (arakelovMulHeight A) :=
  rfl

@[simp]
theorem arakelovMulHeight_zero : arakelovMulHeight (0 : Matrix m n K) = 1 :=
  NumberField.arakelovMulHeight_zero

theorem one_le_arakelovMulHeight (A : Matrix m n K) : 1 ≤ arakelovMulHeight A :=
  NumberField.one_le_arakelovMulHeight _

theorem arakelovMulHeight_pos (A : Matrix m n K) : 0 < arakelovMulHeight A :=
  NumberField.arakelovMulHeight_pos _

theorem arakelovMulHeight_ne_zero (A : Matrix m n K) : arakelovMulHeight A ≠ 0 :=
  NumberField.arakelovMulHeight_ne_zero _

theorem arakelovLogHeight_nonneg (A : Matrix m n K) : 0 ≤ arakelovLogHeight A :=
  NumberField.arakelovLogHeight_nonneg _

theorem mulHeight_le_arakelovMulHeight (A : Matrix m n K) :
    mulHeight A ≤ arakelovMulHeight A :=
  NumberField.mulHeight_le_arakelovMulHeight _

omit [NumberField K] in
/-- Cauchy–Schwarz entry by entry at an infinite place: the squared Frobenius norm of `A * B` is
at most the product of those of `A` and of `B`. This is where the cardinality of the inner index
type is not paid. -/
private lemma sum_sq_mul_le (v : NumberField.InfinitePlace K) (A : Matrix m n K)
    (B : Matrix n p K) :
    ∑ q : m × p, v ((A * B) q.1 q.2) ^ 2
      ≤ (∑ r : m × n, v (A r.1 r.2) ^ 2) * ∑ t : n × p, v (B t.1 t.2) ^ 2 := by
  calc ∑ q : m × p, v ((A * B) q.1 q.2) ^ 2 = ∑ i, ∑ j, v ((A * B) i j) ^ 2 :=
        Fintype.sum_prod_type ..
    _ ≤ ∑ i, ∑ j, (∑ k, v (A i k) ^ 2) * ∑ k, v (B k j) ^ 2 := by
        refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
        calc v ((A * B) i j) ^ 2 = v (∑ k, A i k * B k j) ^ 2 := by rw [Matrix.mul_apply]
          _ ≤ (∑ k, v (A i k) * v (B k j)) ^ 2 := by
              gcongr ?_ ^ 2
              refine (v.1.sum_le _ _).trans_eq (Finset.sum_congr rfl fun k _ ↦ ?_)
              exact map_mul ..
          _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    _ = (∑ i, ∑ k, v (A i k) ^ 2) * ∑ j, ∑ k, v (B k j) ^ 2 := (Finset.sum_mul_sum ..).symm
    _ = (∑ r : m × n, v (A r.1 r.2) ^ 2) * ∑ t : n × p, v (B t.1 t.2) ^ 2 := by
        rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
        congr 1
        exact Finset.sum_comm

omit [NumberField K] [Fintype m] [Fintype p] in
/-- The ultrametric inequality at a finite place: the sup norm is submultiplicative on matrix
products. -/
private lemma iSup_mul_le [Finite m] [Finite p] {v : AbsoluteValue K ℝ}
    (hv : IsNonarchimedean v) (A : Matrix m n K) (B : Matrix n p K) :
    ⨆ q : m × p, v ((A * B) q.1 q.2)
      ≤ (⨆ r : m × n, v (A r.1 r.2)) * ⨆ t : n × p, v (B t.1 t.2) := by
  have hA : (0 : ℝ) ≤ ⨆ r : m × n, v (A r.1 r.2) := Real.iSup_nonneg fun _ ↦ v.nonneg _
  have hB : (0 : ℝ) ≤ ⨆ t : n × p, v (B t.1 t.2) := Real.iSup_nonneg fun _ ↦ v.nonneg _
  rcases isEmpty_or_nonempty (m × p) with h | h
  · simpa using mul_nonneg hA hB
  refine ciSup_le fun q ↦ ?_
  rw [Matrix.mul_apply]
  refine hv.apply_sum_univ_le.trans ?_
  rcases isEmpty_or_nonempty n with hn | hn
  · simp
  refine ciSup_le fun k ↦ ?_
  rw [map_mul]
  gcongr
  · exact Finite.le_ciSup_of_le (q.1, k) le_rfl
  · exact Finite.le_ciSup_of_le (k, q.2) le_rfl

/-- **The Arakelov product bound, with constant `1`.** Against
`Fintype.card n ^ totalWeight K` for the sup-norm height of `Matrix.mulHeight_mul_le`, and with no
hypothesis on the index types at all — for `n` empty, `A * B = 0` has the junk height `1`, which
is at most the right-hand side. This is the matrix form of
`NumberField.arakelovMulHeight_linearMap_apply_le`. -/
theorem arakelovMulHeight_mul_le (A : Matrix m n K) (B : Matrix n p K) :
    arakelovMulHeight (A * B) ≤ arakelovMulHeight A * arakelovMulHeight B := by
  rcases eq_or_ne (fun q : m × p ↦ (A * B) q.1 q.2) 0 with h0 | h0
  · rw [arakelovMulHeight, h0, NumberField.arakelovMulHeight_zero]
    exact one_le_mul_of_one_le_of_one_le (one_le_arakelovMulHeight A) (one_le_arakelovMulHeight B)
  have hA : (fun r : m × n ↦ A r.1 r.2) ≠ 0 := by
    intro h
    have hA0 : A = 0 := by ext i k; exact congrFun h (i, k)
    exact h0 (funext fun q ↦ by simp [hA0])
  have hB : (fun t : n × p ↦ B t.1 t.2) ≠ 0 := by
    intro h
    have hB0 : B = 0 := by ext k j; exact congrFun h (k, j)
    exact h0 (funext fun q ↦ by simp [hB0])
  have hfinA :
      (fun v : NumberField.FinitePlace K ↦ ⨆ r : m × n, v (A r.1 r.2)).HasFiniteMulSupport :=
    Height.hasFiniteMulSupport_iSup_nonarchAbsVal hA
  have hfinB :
      (fun v : NumberField.FinitePlace K ↦ ⨆ t : n × p, v (B t.1 t.2)).HasFiniteMulSupport :=
    Height.hasFiniteMulSupport_iSup_nonarchAbsVal hB
  have hfin0 :
      (fun v : NumberField.FinitePlace K ↦ ⨆ q : m × p, v ((A * B) q.1 q.2)).HasFiniteMulSupport :=
    Height.hasFiniteMulSupport_iSup_nonarchAbsVal h0
  rw [arakelovMulHeight, arakelovMulHeight, arakelovMulHeight,
    NumberField.arakelovMulHeight_eq h0, NumberField.arakelovMulHeight_eq hA,
    NumberField.arakelovMulHeight_eq hB, mul_mul_mul_comm]
  refine mul_le_mul ?_ ?_ ?_ ?_
  · rw [← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod₀ (fun v _ ↦ by positivity) fun v _ ↦ ?_
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    exact Real.rpow_le_rpow (by positivity) (sum_sq_mul_le v A B) (by positivity)
  · rw [← _root_.finprod_mul_distrib hfinA hfinB]
    exact finprod_le_finprod₀ hfin0 (fun v ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _)
      (hfinA.mul hfinB) fun v ↦ iSup_mul_le (NumberField.FinitePlace.add_le v) A B
  · exact _root_.finprod_nonneg fun v ↦ Real.iSup_nonneg fun _ ↦ apply_nonneg _ _
  · positivity

/-- The logarithmic form of `Matrix.arakelovMulHeight_mul_le`: in the Arakelov normalization a
matrix product costs nothing beyond the two heights. -/
theorem arakelovLogHeight_mul_le (A : Matrix m n K) (B : Matrix n p K) :
    arakelovLogHeight (A * B) ≤ arakelovLogHeight A + arakelovLogHeight B := by
  simp only [arakelovLogHeight_eq_log_arakelovMulHeight]
  refine (log_le_log (arakelovMulHeight_pos _) (arakelovMulHeight_mul_le A B)).trans_eq ?_
  rw [log_mul (arakelovMulHeight_ne_zero A) (arakelovMulHeight_ne_zero B)]

/-- The action on tuples in the Arakelov normalization, from
`NumberField.arakelovMulHeight_linearMap_apply_le`. -/
theorem arakelovMulHeight_mulVec_le (A : Matrix m n K) (x : n → K) :
    NumberField.arakelovMulHeight (A.mulVec x)
      ≤ arakelovMulHeight A * NumberField.arakelovMulHeight x :=
  NumberField.arakelovMulHeight_linearMap_apply_le (fun q : m × n ↦ A q.1 q.2) x

/-- The logarithmic form of `Matrix.arakelovMulHeight_mulVec_le`. -/
theorem arakelovLogHeight_mulVec_le (A : Matrix m n K) (x : n → K) :
    NumberField.arakelovLogHeight (A.mulVec x)
      ≤ arakelovLogHeight A + NumberField.arakelovLogHeight x :=
  NumberField.arakelovLogHeight_linearMap_apply_le (fun q : m × n ↦ A q.1 q.2) x

end Matrix

/-!
### Examples

The tests that fix the constants of the product bound: that `Fintype.card n ^ totalWeight K` is
attained, that its *exponent* is needed as soon as `K` has degree `> 1` — the rejection test the
roadmap states over `ℚ(i)`, here for every number field at once — that `[Nonempty n]` cannot be
dropped, and that the Arakelov constant `1` is attained.
-/

section Examples

open Height NumberField

private def exA : Matrix (Fin 1) (Fin 2) ℚ := Matrix.of ![![1, 1]]

private def exB : Matrix (Fin 2) (Fin 2) ℚ := Matrix.of ![![1, 0], ![1, 1]]

private lemma mulHeight_exA : Matrix.mulHeight exA = 1 := by
  have h : (fun q : Fin 1 × Fin 2 ↦ exA q.1 q.2) = 1 := by
    ext q
    obtain ⟨i, j⟩ := q
    fin_cases i
    fin_cases j <;> rfl
  rw [Matrix.mulHeight, h, mulHeight_one]

private lemma mulHeight_exB : Matrix.mulHeight exB = 1 := by
  have h : (fun q : Fin 2 × Fin 2 ↦ exB q.1 q.2)
      = ((↑) : ℤ → ℚ) ∘ fun q : Fin 2 × Fin 2 ↦ ![![1, 0], ![1, 1]] q.1 q.2 := by
    ext q
    obtain ⟨i, j⟩ := q
    fin_cases i <;> fin_cases j <;> rfl
  have hsup : (⨆ q : Fin 2 × Fin 2, |(![![1, 0], ![1, 1]] : Fin 2 → Fin 2 → ℤ) q.1 q.2|) = 1 :=
    le_antisymm
      (ciSup_le fun q ↦ by obtain ⟨i, j⟩ := q; fin_cases i <;> fin_cases j <;> decide)
      (Finite.le_ciSup_of_le (0, 0) (by decide))
  rw [Matrix.mulHeight, h, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide), hsup]
  norm_num

private lemma mulHeight_exA_mul_exB : Matrix.mulHeight (exA * exB) = 2 := by
  have h : (fun q : Fin 1 × Fin 2 ↦ (exA * exB) q.1 q.2)
      = ((↑) : ℤ → ℚ) ∘ fun q : Fin 1 × Fin 2 ↦ ![2, 1] q.2 := by
    ext q
    obtain ⟨i, j⟩ := q
    fin_cases i
    fin_cases j <;> norm_num [exA, exB, Matrix.mul_apply, Fin.sum_univ_two]
  have hsup : (⨆ q : Fin 1 × Fin 2, |(![2, 1] : Fin 2 → ℤ) q.2|) = 2 :=
    le_antisymm
      (ciSup_le fun q ↦ by
        obtain ⟨i, j⟩ := q
        fin_cases i
        fin_cases j <;> decide)
      (Finite.le_ciSup_of_le (0, 0) (by decide))
  rw [Matrix.mulHeight, h, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide), hsup]
  norm_num

/-- **Sharpness of the product bound over `ℚ`.** With `A = ![![1, 1]]` and
`B = ![![1, 0], ![1, 1]]` the product is `![![2, 1]]`, of height `2`, while both factors have
height `1` and `Fintype.card (Fin 2) ^ totalWeight ℚ = 2`. The constant of
`Matrix.mulHeight_mul_le` is attained. -/
example :
    Matrix.mulHeight (exA * exB) = 2 ∧ Matrix.mulHeight exA = 1 ∧ Matrix.mulHeight exB = 1
      ∧ (Fintype.card (Fin 2) : ℝ) ^ totalWeight ℚ = 2 := by
  have hw : totalWeight ℚ = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self]
  exact ⟨mulHeight_exA_mul_exB, mulHeight_exA, mulHeight_exB, by rw [hw]; norm_num⟩

private lemma mulHeight_map_eq {K : Type*} [Field K] [NumberField K] {m' n' : Type*} [Finite m']
    [Finite n'] (M : Matrix m' n' ℚ) :
    Matrix.mulHeight (M.map (algebraMap ℚ K)) = Matrix.mulHeight M ^ Module.finrank ℚ K := by
  have he : (fun q : m' × n' ↦ (M.map (algebraMap ℚ K)) q.1 q.2)
      = algebraMap ℚ K ∘ fun q : m' × n' ↦ M q.1 q.2 := rfl
  rw [Matrix.mulHeight, Matrix.mulHeight, he]
  exact (NumberField.mulHeight_pow_finrank _).symm

/-- **The exponent `totalWeight K` is needed.** Reading the same two matrices in a number field
`K` raises every height to the power `totalWeight K = [K : ℚ]`, so the product bound is attained
with the constant `2 ^ totalWeight K` and false with any smaller one. Over a quadratic field such
as `ℚ(i)` the absolute constant `Fintype.card (Fin 2) = 2` already fails, which is the roadmap's
`ℚ(i)` rejection test — here for every number field at once. -/
example (K : Type*) [Field K] [NumberField K] :
    Matrix.mulHeight (exA.map (algebraMap ℚ K) * exB.map (algebraMap ℚ K)) = 2 ^ totalWeight K
      ∧ Matrix.mulHeight (exA.map (algebraMap ℚ K)) = 1
      ∧ Matrix.mulHeight (exB.map (algebraMap ℚ K)) = 1 := by
  have hdeg : totalWeight K = Module.finrank ℚ K := NumberField.totalWeight_eq_finrank K
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, mulHeight_map_eq, mulHeight_exA_mul_exB, hdeg]
  · rw [mulHeight_map_eq, mulHeight_exA, one_pow]
  · rw [mulHeight_map_eq, mulHeight_exB, one_pow]

/-- **`[Nonempty n]` cannot be dropped from the product bound.** For `n` empty the product is the
zero matrix, of junk height `1`, while the right-hand side has the factor
`(Fintype.card n : ℝ) ^ totalWeight K = 0`. -/
example :
    ¬ Matrix.mulHeight ((0 : Matrix (Fin 1) (Fin 0) ℚ) * (0 : Matrix (Fin 0) (Fin 1) ℚ))
      ≤ (Fintype.card (Fin 0) : ℝ) ^ totalWeight ℚ
          * (Matrix.mulHeight (0 : Matrix (Fin 1) (Fin 0) ℚ)
              * Matrix.mulHeight (0 : Matrix (Fin 0) (Fin 1) ℚ)) := by
  have hw : totalWeight ℚ = 1 := by
    rw [NumberField.totalWeight_eq_finrank, Module.finrank_self]
  rw [Matrix.zero_mul, Matrix.mulHeight_zero, Matrix.mulHeight_zero, Matrix.mulHeight_zero, hw]
  norm_num

/-- **Sharpness of the Arakelov constant.** Multiplying by the `1 × 1` identity matrix changes
nothing, and the identity matrix has Arakelov height `1` because its index type is a
subsingleton; so `Matrix.arakelovMulHeight_mul_le` is an equality and the constant `1` cannot be
lowered. -/
example {K : Type*} [Field K] [NumberField K] {m : Type*} [Fintype m] (A : Matrix m (Fin 1) K) :
    Matrix.arakelovMulHeight (A * (1 : Matrix (Fin 1) (Fin 1) K))
      = Matrix.arakelovMulHeight A * Matrix.arakelovMulHeight (1 : Matrix (Fin 1) (Fin 1) K) := by
  have h1 : Matrix.arakelovMulHeight (1 : Matrix (Fin 1) (Fin 1) K) = 1 :=
    arakelovMulHeight_eq_one_of_subsingleton _
  rw [Matrix.mul_one, h1, mul_one]

end Examples

end
