/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.RowSpace
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.LinearAlgebra.Dual.Basis

/-!
# The Cauchy–Binet identity

The product of a matrix with the transpose of another is a determinant that the maximal minors
compute: `det (A Bᵀ) = ∑ₛ det Aₛ · det Bₛ`, the sum over the sets `s` of `m` columns. Taking
`B = A` turns the sum of squares of the maximal minors into the **Gram determinant** `det (A Aᵀ)`
of the rows, and taking `B = conj A` turns the sum of their squared absolute values into
`det (A Aᴴ)`. Those two are the archimedean local factors of the Arakelov height of the tuple of
minors — of the row space, by Layer 3.3 — and they are where the `√|det (A Aᵀ)|` of the
Bombieri–Vaaler bound comes from.

Everything here is proved once, over an arbitrary commutative ring, for the Plücker coordinates of
Layer 3.1; the matrix statements are that identity read through Layer 3.3's dictionary.

## Main results

* `exteriorPower.sum_plucker_mul_plucker`: the identity itself, for two families of vectors —
  `∑ₛ plucker k v s * plucker k w s` is the determinant of the matrix of dot products `v i ⬝ᵥ w j`.
* `Matrix.det_mul_eq_sum_plucker` and `Matrix.det_mul_transpose_eq_sum_plucker`, with
  `Matrix.det_mul_eq_sum_det_submatrix` and `Matrix.det_mul_transpose_eq_sum_det_submatrix`
  spelling the same statements with `Matrix.submatrix` and `Finset.orderEmbOfFin`.
* `Matrix.det_mul_transpose_self_eq_sum_sq`: the **real** specialization, `det (A Aᵀ)` is the sum of
  the squares of the maximal minors, over any commutative ring.
* `Matrix.det_mul_conjTranspose_self_eq_sum`: the **complex** specialization, over a commutative
  star ring, with `Matrix.det_mul_conjTranspose_self_eq_sum_sq_norm` its `RCLike` form
  `det (A Aᴴ) = ∑ₛ ‖det Aₛ‖²` and
  `NumberField.InfinitePlace.det_map_embedding_mul_conjTranspose_self` its form at an infinite
  place of a number field, which is the local factor named above.
* `Matrix.det_mul_transpose_self_eq_zero_iff` and
  `Matrix.linearIndependent_row_iff_det_mul_transpose_self_ne_zero`: over an ordered field the Gram
  determinant of the rows detects full row rank, the Gram criterion.
* `exteriorPower.plucker_map`: the Plücker coordinates commute with a ring homomorphism, which is
  what carries the identity to a completion or an embedding.

## Implementation notes

The proof is Mathlib's pairing `exteriorPower.pairingDual` between `⋀ⁿ (Dual R M)` and `⋀ⁿ M`,
evaluated on the image of a wedge under `exteriorPower.map n (Pi.basisFun R ι).toDual`. Read on the
induced basis of the exterior power that composite is the diagonal bilinear form
`∑ₛ xₛ yₛ`, because `Basis.toDual` sends the standard basis to the dual basis and
`exteriorPower.ιMultiDual` — the coordinate functional of Layer 3.1's basis — is *by definition*
the pairing against the wedge of dual basis vectors; read on wedges it is a determinant of
dot products, by `exteriorPower.pairingDual_ιMulti_ιMulti`. So the identity is the statement that
one bilinear form has two descriptions, and no expansion of a determinant over permutations is
carried out anywhere.

Mathlib's `LinearMap.BilinForm.exteriorPower` is that same composite and would be the natural name
for it. What is missing is its defining equation: `LinearMap.BilinForm.bilinForm_ιMulti_ιMulti`,
which evaluates the form on two wedges as a determinant, carries no `public` in a module that has
no `public section`, so it is invisible outside its own file and every user has to re-prove it.
That proof is exactly the content of the identity below, so the composite is written out here.

`Pi.basisFun_toDual_apply`, that `Basis.toDual` of the standard basis is the dot product, is
stated here because Mathlib has `Basis.toDual_apply_left` only for a basis vector in the second
argument.

## References

A. L. Cauchy (1812) and J. P. M. Binet (1812); the identity is Proposition 2.8.8 of
E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
and §2 Lemma 1 of W. M. Schmidt, "On heights of algebraic subspaces and diophantine
approximations", *Annals of Mathematics* **85** (1967), 430–472. It enters the Siegel-lemma
literature as equation (2.4)(iv) of E. Bombieri and J. Vaaler, "On Siegel's lemma",
*Inventiones Mathematicae* **73** (1983), 11–32, whose bound is stated in terms of
`√|det (A Aᵀ)|`.

This is Layer 3.4 of the `ArithmeticHeights` roadmap.
-/

public section

namespace exteriorPower

open Matrix Module

/-!
### The identity in Plücker coordinates
-/

section Dual

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The dual map of the standard basis is the dot product.** Mathlib's `Basis.toDual_apply_left`
evaluates `b.toDual x` on a basis vector; for the standard basis of `ι → R` the value on an
arbitrary vector is the dot product. -/
theorem _root_.Pi.basisFun_toDual_apply (x y : ι → R) :
    (Pi.basisFun R ι).toDual x y = x ⬝ᵥ y := by
  conv_lhs => rw [← (Pi.basisFun R ι).sum_repr y]
  rw [map_sum]
  simp only [map_smul, Basis.toDual_apply_left, Pi.basisFun_repr, smul_eq_mul, dotProduct]
  exact Finset.sum_congr rfl fun i _ ↦ mul_comm _ _

end Dual

section Basis

variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] [LinearOrder ι]

/-- The pairing against the image of a basis vector of `⋀^k (ι → R)` reads off a coordinate: this
is `exteriorPower.ιMultiDual` unfolded, since that functional is *defined* as the pairing against
the wedge of the dual basis vectors indexed by `s`. -/
private lemma pairingDual_map_toDual_basis (k : ℕ) (s : Set.powersetCard ι k)
    (y : ⋀[R]^k (ι → R)) :
    pairingDual R (ι → R) k
        (map k (Pi.basisFun R ι).toDual ((Pi.basisFun R ι).exteriorPower k s)) y
      = ((Pi.basisFun R ι).exteriorPower k).repr y s := by
  rw [basis_apply, map_apply_ιMulti_family,
    show (Pi.basisFun R ι).toDual ∘ (Pi.basisFun R ι) = (Pi.basisFun R ι).coord from
      funext fun i ↦ Basis.coe_toDual_self _ i, basis_repr_apply]
  rfl

end Basis

section CauchyBinet

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {k : ℕ}

/-- On the basis of `⋀^k (ι → R)` induced by the standard basis, the bilinear form obtained by
pairing along `Basis.toDual` is the diagonal one. -/
private lemma pairingDual_map_toDual (k : ℕ) (x y : ⋀[R]^k (ι → R)) :
    pairingDual R (ι → R) k (map k (Pi.basisFun R ι).toDual x) y
      = ∑ s : Set.powersetCard ι k, ((Pi.basisFun R ι).exteriorPower k).repr x s *
          ((Pi.basisFun R ι).exteriorPower k).repr y s := by
  conv_lhs => rw [← ((Pi.basisFun R ι).exteriorPower k).sum_repr x]
  rw [map_sum, map_sum, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_smul, map_smul, LinearMap.smul_apply, pairingDual_map_toDual_basis, smul_eq_mul]

/-- **The Cauchy–Binet identity.** The sum over the `k`-element sets of columns of the product of
the two Plücker coordinates is the determinant of the `k × k` matrix of dot products. Over any
commutative ring, and with no hypothesis on either family. -/
theorem sum_plucker_mul_plucker (k : ℕ) (v w : Fin k → (ι → R)) :
    ∑ s : Set.powersetCard ι k, plucker k v s * plucker k w s
      = (Matrix.of fun i j ↦ v i ⬝ᵥ w j).det := by
  have h := pairingDual_map_toDual k (ιMulti R k v) (ιMulti R k w)
  rw [map_apply_ιMulti, pairingDual_ιMulti_ιMulti] at h
  simp only [plucker, Basis.equivFun_apply]
  rw [← h]
  simp only [Function.comp_apply, Pi.basisFun_toDual_apply]
  rw [← Matrix.det_transpose (Matrix.of fun i j ↦ v i ⬝ᵥ w j)]
  rfl

/-- **The Plücker coordinates commute with a ring homomorphism**, each being a determinant. This is
what carries the identity along an embedding of a number field into `ℂ`. -/
theorem plucker_map {S : Type*} [CommRing S] (f : R →+* S) (k : ℕ) (v : Fin k → (ι → R))
    (s : Set.powersetCard ι k) : plucker k (fun i ↦ f ∘ v i) s = f (plucker k v s) := by
  rw [plucker_apply, plucker_apply, RingHom.map_det]
  rfl

end CauchyBinet

end exteriorPower

namespace Matrix

open Module exteriorPower

/-!
### The identity for matrices
-/

section CauchyBinet

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- The Plücker coordinates of the rows commute with a ring homomorphism applied entrywise. -/
theorem plucker_row_map {S : Type*} [CommRing S] (f : R →+* S) (A : Matrix (Fin m) ι R)
    (s : Set.powersetCard ι m) : plucker m (A.map f).row s = f (plucker m A.row s) :=
  plucker_map f m A.row s

/-- **The Cauchy–Binet identity**, for `A Bᵀ`: the determinant of the matrix of dot products of the
rows of `A` with the rows of `B` is the sum over the sets of `m` columns of the products of
corresponding maximal minors. -/
theorem det_mul_transpose_eq_sum_plucker (A B : Matrix (Fin m) ι R) :
    (A * Bᵀ).det = ∑ s : Set.powersetCard ι m, plucker m A.row s * plucker m B.row s :=
  (sum_plucker_mul_plucker m A.row B.row).symm

/-- **The Cauchy–Binet identity**, for a product `A B` of an `m × ι` by an `ι × m` matrix: the
determinant is the sum over the sets of `m` indices of the product of the maximal minor of `A` on
those columns with the maximal minor of `B` on those rows. -/
theorem det_mul_eq_sum_plucker (A : Matrix (Fin m) ι R) (B : Matrix ι (Fin m) R) :
    (A * B).det = ∑ s : Set.powersetCard ι m, plucker m A.row s * plucker m B.col s := by
  conv_lhs => rw [← Matrix.transpose_transpose B]
  exact (sum_plucker_mul_plucker m A.row Bᵀ.row).symm

/-- The Cauchy–Binet identity in the `submatrix` spelling of Layer 3.3: the minors are taken on the
columns of `s`, enumerated in increasing order. -/
theorem det_mul_transpose_eq_sum_det_submatrix (A B : Matrix (Fin m) ι R) :
    (A * Bᵀ).det = ∑ s : Set.powersetCard ι m,
      (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det *
        (B.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
  rw [det_mul_transpose_eq_sum_plucker]
  exact Finset.sum_congr rfl fun s _ ↦ by
    rw [plucker_row_eq_det_submatrix, plucker_row_eq_det_submatrix]

/-- The Cauchy–Binet identity for `A B` in the `submatrix` spelling: the maximal minors of `A` on
the columns of `s` against those of `B` on the rows of `s`. -/
theorem det_mul_eq_sum_det_submatrix (A : Matrix (Fin m) ι R) (B : Matrix ι (Fin m) R) :
    (A * B).det = ∑ s : Set.powersetCard ι m,
      (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det *
        (B.submatrix ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s)) id).det := by
  rw [det_mul_eq_sum_plucker]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [plucker_row_eq_det_submatrix, show B.col = Bᵀ.row from rfl, plucker_row_eq_det_submatrix,
    ← Matrix.det_transpose (B.submatrix _ id), Matrix.transpose_submatrix]

end CauchyBinet

/-!
### The Gram determinant of the rows
-/

section Gram

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- **The archimedean specialization at a real place.** The Gram determinant of the rows is the sum
of the squares of the maximal minors. This is the `√|det (A Aᵀ)|` of the Bombieri–Vaaler bound:
its square is the ℓ² local factor of the tuple of minors. -/
theorem det_mul_transpose_self_eq_sum_sq (A : Matrix (Fin m) ι R) :
    (A * Aᵀ).det = ∑ s : Set.powersetCard ι m, plucker m A.row s ^ 2 := by
  rw [det_mul_transpose_eq_sum_plucker]
  exact Finset.sum_congr rfl fun s _ ↦ (sq _).symm

variable {S : Type*} [CommRing S] [LinearOrder S] [IsStrictOrderedRing S]

/-- The Gram determinant of the rows is nonnegative. -/
theorem det_mul_transpose_self_nonneg (A : Matrix (Fin m) ι S) : 0 ≤ (A * Aᵀ).det := by
  rw [det_mul_transpose_self_eq_sum_sq]
  exact Finset.sum_nonneg fun s _ ↦ sq_nonneg _

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- **The Gram criterion.** Over an ordered field the Gram determinant of the rows vanishes exactly
when the rows are linearly dependent. -/
theorem det_mul_transpose_self_eq_zero_iff (A : Matrix (Fin m) ι K) :
    (A * Aᵀ).det = 0 ↔ ¬ LinearIndependent K A.row := by
  rw [det_mul_transpose_self_eq_sum_sq, ← plucker_eq_zero_iff m A.row,
    Finset.sum_eq_zero_iff_of_nonneg fun s _ ↦ sq_nonneg _]
  simp [funext_iff]

/-- **The Gram criterion**, in the form the Bombieri–Vaaler bound needs: full row rank is exactly
positivity of the Gram determinant, so `√|det (A Aᵀ)|` is nonzero there. -/
theorem det_mul_transpose_self_pos_iff (A : Matrix (Fin m) ι K) :
    0 < (A * Aᵀ).det ↔ LinearIndependent K A.row :=
  ⟨fun h ↦ by
    by_contra hA
    exact h.ne' ((det_mul_transpose_self_eq_zero_iff A).2 hA),
   fun hA ↦ lt_of_le_of_ne (det_mul_transpose_self_nonneg A)
    (Ne.symm fun h ↦ (det_mul_transpose_self_eq_zero_iff A).1 h hA)⟩

/-- Full row rank, detected by the Gram determinant. -/
theorem linearIndependent_row_iff_det_mul_transpose_self_ne_zero (A : Matrix (Fin m) ι K) :
    LinearIndependent K A.row ↔ (A * Aᵀ).det ≠ 0 :=
  ⟨fun hA h ↦ (det_mul_transpose_self_eq_zero_iff A).1 h hA,
   fun h ↦ not_not.1 fun hA ↦ h ((det_mul_transpose_self_eq_zero_iff A).2 hA)⟩

end Gram

/-!
### The Gram determinant at a complex place
-/

section Star

variable {R : Type*} [CommRing R] [StarRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- **The archimedean specialization at a complex place.** Pairing `A` against its conjugate
transpose replaces the squares of the maximal minors by their norms. -/
theorem det_mul_conjTranspose_self_eq_sum (A : Matrix (Fin m) ι R) :
    (A * Aᴴ).det =
      ∑ s : Set.powersetCard ι m, plucker m A.row s * star (plucker m A.row s) := by
  rw [show Aᴴ = (A.map (starRingEnd R))ᵀ from rfl, det_mul_transpose_eq_sum_plucker]
  exact Finset.sum_congr rfl fun s _ ↦ by rw [plucker_row_map]; rfl

variable {K : Type*} [RCLike K]

/-- The complex specialization, with the squared absolute values displayed: `det (A Aᴴ)` is the
square of the ℓ² norm of the tuple of maximal minors. -/
theorem det_mul_conjTranspose_self_eq_sum_sq_norm (A : Matrix (Fin m) ι K) :
    (A * Aᴴ).det = ((∑ s : Set.powersetCard ι m, ‖plucker m A.row s‖ ^ 2 : ℝ) : K) := by
  rw [det_mul_conjTranspose_self_eq_sum]
  push_cast
  exact Finset.sum_congr rfl fun s _ ↦ RCLike.mul_conj _

end Star

end Matrix

namespace NumberField.InfinitePlace

open Matrix exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- **The archimedean local factor of the tuple of maximal minors is a Gram determinant.** At an
infinite place `v` of a number field, `∑ₛ v(det Aₛ)²` — the quantity the ℓ² normalization of Layer
0.1 raises to the power `mult v / 2` — is the determinant of the Gram matrix of the rows of `A`
read through the embedding attached to `v`. At a real place the conjugate transpose is the
transpose, so this covers both kinds of place. -/
theorem det_map_embedding_mul_conjTranspose_self (v : InfinitePlace K) (A : Matrix (Fin m) ι K) :
    ((A.map v.embedding) * (A.map v.embedding)ᴴ).det
      = ((∑ s : Set.powersetCard ι m, v (plucker m A.row s) ^ 2 : ℝ) : ℂ) := by
  rw [Matrix.det_mul_conjTranspose_self_eq_sum_sq_norm]
  exact congrArg _ (Finset.sum_congr rfl fun s _ ↦ by
    rw [Matrix.plucker_row_map, norm_embedding_eq])

end NumberField.InfinitePlace

section Examples

open Matrix exteriorPower

/-- **Acceptance test: the sum of squares of the maximal minors, computed as a Gram determinant.**
The three maximal minors of this `2 × 3` matrix are `1`, `3` and `−2` — the acceptance test of
Layer 3.3 — so the sum of their squares is `1 + 9 + 4 = 14`, and Cauchy–Binet produces it from the
`2 × 2` determinant of `A Aᵀ` without enumerating a single minor. -/
example : (∑ s : Set.powersetCard (Fin 3) 2,
    plucker 2 (Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ).row s ^ 2) = 14 := by
  rw [← Matrix.det_mul_transpose_self_eq_sum_sq, Matrix.det_fin_two]
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- **Rejection test: `A Aᵀ` and not `Aᵀ A`.** The Gram matrix of the *rows* is `m × m`; the `n × n`
matrix `Aᵀ A` is singular whenever `m < n`, so its determinant is `0` and carries none of the
information. A statement of Cauchy–Binet with the factors in the other order is refuted here. -/
example : ((Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ)ᵀ *
    (Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ)).det = 0 := by
  rw [Matrix.det_fin_three]
  norm_num [Matrix.mul_apply, Fin.sum_univ_succ]

/-- **Conformance.** The milestone's three statements: the identity over a commutative ring, its
real specialization, and its complex specialization. -/
example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}
    (A B : Matrix (Fin m) ι R) (C : Matrix (Fin m) ι ℂ) :
    (A * Bᵀ).det = ∑ s : Set.powersetCard ι m, plucker m A.row s * plucker m B.row s ∧
      (A * Aᵀ).det = ∑ s : Set.powersetCard ι m, plucker m A.row s ^ 2 ∧
      (C * Cᴴ).det = ((∑ s : Set.powersetCard ι m, ‖plucker m C.row s‖ ^ 2 : ℝ) : ℂ) :=
  ⟨Matrix.det_mul_transpose_eq_sum_plucker A B, Matrix.det_mul_transpose_self_eq_sum_sq A,
    Matrix.det_mul_conjTranspose_self_eq_sum_sq_norm C⟩

end Examples

end
