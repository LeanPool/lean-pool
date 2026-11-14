/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.Subspace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Rank

-- Only the worked examples below mention `Matrix.mulHeight`, the height of the entries of
-- Layer 2.5, and they mention it in order to distinguish it from the height of the row space.
import LeanPool.CCDN.ArithmeticHeights.Matrix

/-!
# The row space of a matrix and the height of its maximal minors

The dictionary between a matrix of full row rank and the subspace it spans: the Plücker
coordinates of the row space are the maximal minors, so the height of the row space is the height
of the tuple of minors, and left multiplication by an invertible matrix — a row operation — leaves
it unchanged. That invariance is what distinguishes the height of the row space from
`Matrix.mulHeight`, the height of the entries of Layer 2.5, and it is the reason Bombieri–Vaaler
can improve on the naïve Siegel bound.

## Main definitions

None, deliberately. The row space of `A` is `Submodule.span R (Set.range A.row)`, which is
Mathlib's `LinearMap.range A.vecMulLinear` by `range_vecMulLinear`, and the tuple of maximal minors
is `exteriorPower.plucker m A.row` of Layer 3.1. A third name for either would force every later
statement to choose between three spellings of one object.

## Main results

* `Matrix.plucker_row_eq_det_submatrix`: the Plücker coordinate of `A` at a set `s` of columns is
  the determinant of the submatrix on those columns, taken in increasing order. This is the index
  identification, and `Matrix.plucker_row_eq_det_submatrix_orderIso` restates it with
  `Finset.orderIsoOfFin` in place of `Finset.orderEmbOfFin`.
* `Matrix.plucker_row_mul`: `plucker m (U * A).row = U.det • plucker m A.row`, for *every* square
  `U` and over any commutative ring — the determinant identity underlying the height invariance
  in Bombieri–Vaaler (2.5).
* `Matrix.span_range_row_mul`: for `U` of unit determinant the row space itself is unchanged, whence
  `Matrix.mulHeight_span_range_row_mul` and its Arakelov and absolute companions.
* `Matrix.mulHeight_span_range_row` and `Matrix.arakelovMulHeight_span_range_row`: the height of the
  row space is the height of the tuple of maximal minors in each chosen normalization.
  The relative Arakelov version corresponds to Bombieri–Vaaler's absolute `H(A)` after raising
  to the number-field degree. These row-space heights differ from `Matrix.mulHeight A`.
* `Matrix.linearIndependent_row_iff_rank_eq` and
  `Matrix.linearIndependent_row_iff_plucker_row_ne_zero`: full row rank, in the two forms that the
  statements above take as a hypothesis.

## Implementation notes

The invariance under row operations is not a theorem about heights. `Matrix.span_range_row_mul` is
an equality of submodules, and every height statement below is one `congrArg` away from it,
because Layer 3.2 defines the height of a subspace as a function of the subspace alone. The
mathematical content sits in that span equality and, quantitatively, in `Matrix.plucker_row_mul`.

`Matrix.plucker_row_mul` needs no hypothesis on `U`, no field, and no expansion of an alternating
map along a matrix — which is fortunate, since Mathlib has no such expansion. The proof is Layer
3.1 used twice: `exteriorPower.plucker_fin_eq_det` says that the single Plücker coordinate of a
square family is its determinant, so the wedge of the rows of `U` is `U.det` times the wedge of the
standard basis; and `exteriorPower.plucker_eq_smul_iff` transports a proportionality of coordinate
tuples to one of wedges. `exteriorPower.map` then pushes the relation along `A.vecMulLinear`,
whose composition with the rows of `U` is the rows of `U * A` — by `rfl`.

## References

E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge University Press (2006),
Remark 2.8.7 for the dictionary, Definition 2.8.11 for the Arakelov normalization of the row-space
height, and 2.9.8 for the height of the entries, which is a different number and is Layer 2.5 here.
The book's `h_Ar` is absolute logarithmic; the relative multiplicative Arakelov height here is
`exp([K : ℚ] · h_Ar(A))` in that convention.
E. Bombieri and J. Vaaler, "On Siegel's lemma", *Inventiones Mathematicae* **73** (1983), 11–32,
equation (2.5), where the invariance is the statement that the height is intrinsic on the
Grassmannian. W. M. Schmidt, "On heights of algebraic subspaces and diophantine approximations",
*Annals of Mathematics* **85** (1967), 430–472, §1.

This is Layer 3.3 of the `ArithmeticHeights` roadmap.
-/

public section

namespace Matrix

open Module Submodule exteriorPower

/-!
### The Plücker coordinates of a matrix are its maximal minors
-/

section Minors

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- **The Plücker coordinates of a matrix are its maximal minors.** The coordinate at a set `s` of
`m` columns is the determinant of the submatrix on those columns, enumerated in increasing order.
The enumeration is Mathlib's `Finset.orderEmbOfFin`, the one `Set.powersetCard.ofFinEmbEquiv`
already fixes, so no later statement has to choose it again. -/
theorem plucker_row_eq_det_submatrix (A : Matrix (Fin m) ι R) (s : Set.powersetCard ι m) :
    plucker m A.row s =
      (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
  rw [plucker_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply]
  rfl

/-- `Matrix.plucker_row_eq_det_submatrix` with `Finset.orderIsoOfFin` in place of
`Finset.orderEmbOfFin`; the two enumerations agree by `Finset.coe_orderIsoOfFin_apply`. -/
theorem plucker_row_eq_det_submatrix_orderIso (A : Matrix (Fin m) ι R)
    (s : Set.powersetCard ι m) :
    plucker m A.row s =
      (A.submatrix id fun j ↦
        (((s : Finset ι).orderIsoOfFin (Set.powersetCard.card_eq s) j : ι))).det := by
  rw [plucker_row_eq_det_submatrix]
  simp only [Finset.coe_orderIsoOfFin_apply]

end Minors

/-!
### Row operations multiply the Plücker coordinates by a determinant
-/

section RowOps

variable {R : Type*} [CommRing R] {ι : Type*} {m : ℕ}

/-- The rows of `U * A` are the rows of `U` read through `A`. -/
theorem row_mul_eq_comp (U : Matrix (Fin m) (Fin m) R) (A : Matrix (Fin m) ι R) :
    (U * A).row = ⇑A.vecMulLinear ∘ U.row :=
  rfl

/-- The rows of the identity matrix are the standard basis. -/
theorem row_one_eq_basisFun :
    (1 : Matrix (Fin m) (Fin m) R).row = ⇑(Pi.basisFun R (Fin m)) := by
  funext i j
  simp [Matrix.one_apply, Pi.single_apply, eq_comm]

/-- **The wedge of the rows of a square matrix is its determinant times the wedge of the standard
basis.** This is `exteriorPower.plucker_fin_eq_det` read through the injectivity of the coordinate
map on the top exterior power, which is a line. -/
theorem ιMulti_row_eq_det_smul (U : Matrix (Fin m) (Fin m) R) :
    ιMulti R m U.row = U.det • ιMulti R m (1 : Matrix (Fin m) (Fin m) R).row := by
  refine (plucker_eq_smul_iff ..).1 ?_
  funext s
  rw [plucker_fin_eq_det, Pi.smul_apply, plucker_fin_eq_det, smul_eq_mul,
    show of U.row = U from rfl, show of (1 : Matrix (Fin m) (Fin m) R).row = 1 from rfl,
    det_one, mul_one]

/-- **A row operation multiplies the wedge of the rows by the determinant.** -/
theorem ιMulti_row_mul (U : Matrix (Fin m) (Fin m) R) (A : Matrix (Fin m) ι R) :
    ιMulti R m (U * A).row = U.det • ιMulti R m A.row := by
  rw [row_mul_eq_comp U, ← map_apply_ιMulti, ιMulti_row_eq_det_smul U, map_smul,
    map_apply_ιMulti, ← row_mul_eq_comp 1, Matrix.one_mul]

end RowOps

section Plucker

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}

/-- **A row operation multiplies the tuple of maximal minors by the determinant.** This identity
underlies the height invariance in Bombieri–Vaaler (2.5). No hypothesis on `U` is needed:
for `U` singular both sides vanish. -/
theorem plucker_row_mul (U : Matrix (Fin m) (Fin m) R) (A : Matrix (Fin m) ι R) :
    plucker m (U * A).row = U.det • plucker m A.row :=
  (plucker_eq_smul_iff ..).2 (ιMulti_row_mul U A)

end Plucker

/-!
### The row space
-/

section Span

variable {R : Type*} [CommRing R] {ι : Type*} {m : ℕ}
variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- Every row of `U * A` lies in the row space of `A`. -/
theorem span_range_row_mul_le (U : Matrix n n R) (A : Matrix n ι R) :
    span R (Set.range (U * A).row) ≤ span R (Set.range A.row) := by
  rw [← range_vecMulLinear A, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨U.row i, rfl⟩

/-- **A row operation does not change the row space.** Everything below about the height of a row
space is this equality followed by a `congrArg`, the height of Layer 3.2 being a function of the
subspace alone. The row index is an arbitrary finite type: Layer 5.6 multiplies by a
block-diagonal matrix whose rows are indexed by a product. -/
theorem span_range_row_mul {U : Matrix n n R} (hU : IsUnit U.det)
    (A : Matrix n ι R) :
    span R (Set.range (U * A).row) = span R (Set.range A.row) := by
  refine le_antisymm (span_range_row_mul_le U A) ?_
  calc span R (Set.range A.row)
      = span R (Set.range (U⁻¹ * (U * A)).row) := by
        rw [← Matrix.mul_assoc, nonsing_inv_mul U hU, Matrix.one_mul]
    _ ≤ span R (Set.range (U * A).row) := span_range_row_mul_le _ _

@[simp]
theorem span_range_row_one : span R (Set.range (1 : Matrix (Fin m) (Fin m) R).row) = ⊤ := by
  rw [row_one_eq_basisFun]
  exact (Pi.basisFun R (Fin m)).span_eq

/-- A square matrix of unit determinant has the whole space as its row space. -/
theorem span_range_row_eq_top_of_isUnit {U : Matrix (Fin m) (Fin m) R} (hU : IsUnit U.det) :
    span R (Set.range U.row) = ⊤ := by
  have h := span_range_row_mul hU (1 : Matrix (Fin m) (Fin m) R)
  rwa [Matrix.mul_one, span_range_row_one] at h

end Span

/-!
### Full row rank
-/

section Rank

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {m : ℕ}

/-- **Full row rank**, in the form Mathlib's `Matrix.rank` takes. -/
theorem linearIndependent_row_iff_rank_eq (A : Matrix (Fin m) ι K) :
    LinearIndependent K A.row ↔ A.rank = m := by
  rw [rank_eq_finrank_span_row, linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin,
    Set.finrank]
  exact eq_comm

/-- **A matrix has a maximal independent family of rows, of size its rank**, spanning the same row
space: `f` picks out `R = rank A` of the rows, the submatrix on them has independent rows, and its
row space is that of `A`. This is what lets a bound in terms of the rows be paid `rank A` times
rather than once per row. -/
theorem exists_submatrix_row_linearIndependent (A : Matrix (Fin m) ι K) :
    ∃ (R : ℕ) (f : Fin R → Fin m), A.rank = R ∧
      LinearIndependent K (A.submatrix f id).row ∧
      span K (Set.range (A.submatrix f id).row) = span K (Set.range A.row) := by
  classical
  obtain ⟨b, -, -, hsp, hind⟩ :=
    exists_linearIndepOn_extension (K := K) (v := A.row) (linearIndepOn_empty K A.row)
      (Set.empty_subset (Set.univ : Set (Fin m)))
  set s : Finset (Fin m) := b.toFinset with hs
  set R : ℕ := s.card with hR
  set E : Fin R ≃ ↥b :=
    (s.orderIsoOfFin hR.symm).toEquiv.trans (Equiv.subtypeEquivRight fun x ↦ Set.mem_toFinset)
    with hE
  have hindB : LinearIndependent K (A.submatrix (fun i ↦ (E i : Fin m)) id).row :=
    hind.comp E E.injective
  have hrange : Set.range (fun i : Fin R ↦ ((E i : Fin m))) = b := by
    rw [show (fun i : Fin R ↦ ((E i : Fin m))) = Subtype.val ∘ E from rfl,
      Set.range_comp, E.range_eq_univ, Set.image_univ, Subtype.range_coe]
  have himg : Set.range (A.submatrix (fun i ↦ (E i : Fin m)) id).row = A.row '' b := by
    rw [show (A.submatrix (fun i ↦ (E i : Fin m)) id).row
        = A.row ∘ (fun i : Fin R ↦ ((E i : Fin m))) from rfl, Set.range_comp, hrange]
  have hspanB : span K (Set.range (A.submatrix (fun i ↦ (E i : Fin m)) id).row)
      = span K (Set.range A.row) := by
    rw [himg]
    refine le_antisymm (span_mono ?_) (span_le.2 ?_)
    · rintro _ ⟨x, -, rfl⟩
      exact ⟨x, rfl⟩
    · rw [← Set.image_univ]
      exact hsp
  refine ⟨R, fun i ↦ (E i : Fin m), ?_, hindB, hspanB⟩
  rw [rank_eq_finrank_span_row, ← hspanB, finrank_span_eq_card hindB, Fintype.card_fin]

/-- **Full row rank, in minors**: a matrix has independent rows exactly when some maximal minor is
nonzero. This is `exteriorPower.plucker_eq_zero_iff` of Layer 3.1, and it is what makes the height
of the row space a statement about a nonzero tuple. -/
theorem linearIndependent_row_iff_plucker_row_ne_zero [LinearOrder ι] (A : Matrix (Fin m) ι K) :
    LinearIndependent K A.row ↔ plucker m A.row ≠ 0 := by
  rw [ne_eq, plucker_eq_zero_iff, not_not]

end Rank

/-!
### The height of the row space
-/

section Height

variable {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Fintype ι]
  [LinearOrder ι] {m : ℕ} {A : Matrix (Fin m) ι K} {U : Matrix (Fin m) (Fin m) K}

/-- **The height of the row space is the height of the tuple of maximal minors** (Bombieri–Gubler,
Remark 2.8.7). This uses sup norms, while Bombieri–Vaaler's `H(A)` uses the absolute Arakelov
height of the minors. `Matrix.mulHeight A` instead measures the entries. -/
theorem mulHeight_span_range_row (hA : LinearIndependent K A.row) :
    (span K (Set.range A.row)).mulHeight =
      Height.mulHeight fun s : Set.powersetCard ι m ↦
        (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
  rw [Submodule.mulHeight_span_range hA]
  exact congrArg _ (funext (plucker_row_eq_det_submatrix A))

/-- The logarithmic form of `Matrix.mulHeight_span_range_row`. -/
theorem logHeight_span_range_row (hA : LinearIndependent K A.row) :
    (span K (Set.range A.row)).logHeight =
      Height.logHeight fun s : Set.powersetCard ι m ↦
        (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
  rw [Submodule.logHeight_span_range hA]
  exact congrArg _ (funext (plucker_row_eq_det_submatrix A))

/-- **The sup-norm height of the row space is invariant under row operations.** This is the
sup-norm counterpart of the Arakelov height invariance in Bombieri–Vaaler (2.5). -/
theorem mulHeight_span_range_row_mul (hU : IsUnit U.det) (A : Matrix (Fin m) ι K) :
    (span K (Set.range (U * A).row)).mulHeight = (span K (Set.range A.row)).mulHeight :=
  congrArg _ (span_range_row_mul hU A)

/-- The logarithmic form of `Matrix.mulHeight_span_range_row_mul`. -/
theorem logHeight_span_range_row_mul (hU : IsUnit U.det) (A : Matrix (Fin m) ι K) :
    (span K (Set.range (U * A).row)).logHeight = (span K (Set.range A.row)).logHeight :=
  congrArg _ (span_range_row_mul hU A)

/-- The same invariance read on the tuple of minors rather than on the subspace: a row operation
scales it by `U.det`, and the projective height does not see a scalar. -/
theorem mulHeight_plucker_row_mul (hU : IsUnit U.det) (A : Matrix (Fin m) ι K) :
    Height.mulHeight (plucker m (U * A).row) = Height.mulHeight (plucker m A.row) := by
  rw [plucker_row_mul, Height.mulHeight_smul_eq_mulHeight _ hU.ne_zero]

/-- The logarithmic form of `Matrix.mulHeight_plucker_row_mul`. -/
theorem logHeight_plucker_row_mul (hU : IsUnit U.det) (A : Matrix (Fin m) ι K) :
    Height.logHeight (plucker m (U * A).row) = Height.logHeight (plucker m A.row) :=
  congrArg Real.log (mulHeight_plucker_row_mul hU A)

end Height

section ArakelovHeight

variable {K : Type*} [Field K] [NumberField K] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : ℕ}
  {A : Matrix (Fin m) ι K} {U : Matrix (Fin m) (Fin m) K}

/-- **The relative Arakelov height of the row space is that of its tuple of maximal minors.**
This is `exp([K : ℚ] · h_Ar(A))` for the absolute logarithmic matrix height of
Bombieri–Gubler Definition 2.8.11. The Siegel-lemma constants of Layer 5 use the relative
multiplicative normalization here. -/
theorem arakelovMulHeight_span_range_row (hA : LinearIndependent K A.row) :
    (span K (Set.range A.row)).arakelovMulHeight =
      NumberField.arakelovMulHeight fun s : Set.powersetCard ι m ↦
        (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
  rw [Submodule.arakelovMulHeight_span_range hA]
  exact congrArg _ (funext (plucker_row_eq_det_submatrix A))

/-- The logarithmic form of `Matrix.arakelovMulHeight_span_range_row`. -/
theorem arakelovLogHeight_span_range_row (hA : LinearIndependent K A.row) :
    (span K (Set.range A.row)).arakelovLogHeight =
      NumberField.arakelovLogHeight fun s : Set.powersetCard ι m ↦
        (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
  rw [Submodule.arakelovLogHeight_span_range hA]
  exact congrArg _ (funext (plucker_row_eq_det_submatrix A))

theorem arakelovMulHeight_span_range_row_mul (hU : IsUnit U.det) (A : Matrix (Fin m) ι K) :
    (span K (Set.range (U * A).row)).arakelovMulHeight =
      (span K (Set.range A.row)).arakelovMulHeight :=
  congrArg _ (span_range_row_mul hU A)

theorem arakelovLogHeight_span_range_row_mul (hU : IsUnit U.det) (A : Matrix (Fin m) ι K) :
    (span K (Set.range (U * A).row)).arakelovLogHeight =
      (span K (Set.range A.row)).arakelovLogHeight :=
  congrArg _ (span_range_row_mul hU A)

end ArakelovHeight

section AbsoluteHeight

variable {K : Type*} [Field K] [CharZero K] [Algebra.IsAlgebraic ℚ K] {ι : Type*} [Fintype ι]
  [LinearOrder ι] {m : ℕ} {A : Matrix (Fin m) ι K} {U : Matrix (Fin m) (Fin m) K}

/-- **The absolute sup-norm height of the row space is that of its tuple of maximal minors.**
Bombieri–Vaaler's `H(A)` uses the Arakelov normalization instead. -/
theorem absMulHeight_span_range_row (hA : LinearIndependent K A.row) :
    (span K (Set.range A.row)).absMulHeight =
      NumberField.absMulHeight fun s : Set.powersetCard ι m ↦
        (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
  rw [Submodule.absMulHeight_span_range hA]
  exact congrArg _ (funext (plucker_row_eq_det_submatrix A))

/-- The logarithmic form of `Matrix.absMulHeight_span_range_row`. -/
theorem absLogHeight_span_range_row (hA : LinearIndependent K A.row) :
    (span K (Set.range A.row)).absLogHeight =
      NumberField.absLogHeight fun s : Set.powersetCard ι m ↦
        (A.submatrix id ((s : Finset ι).orderEmbOfFin (Set.powersetCard.card_eq s))).det := by
  rw [Submodule.absLogHeight_span_range hA]
  exact congrArg _ (funext (plucker_row_eq_det_submatrix A))

theorem absMulHeight_span_range_row_mul (hU : IsUnit U.det) (A : Matrix (Fin m) ι K) :
    (span K (Set.range (U * A).row)).absMulHeight = (span K (Set.range A.row)).absMulHeight :=
  congrArg _ (span_range_row_mul hU A)

theorem absLogHeight_span_range_row_mul (hU : IsUnit U.det) (A : Matrix (Fin m) ι K) :
    (span K (Set.range (U * A).row)).absLogHeight = (span K (Set.range A.row)).absLogHeight :=
  congrArg _ (span_range_row_mul hU A)

end AbsoluteHeight

end Matrix

/-!
### Worked examples
-/

section Examples

open Matrix Submodule exteriorPower

/-- **Acceptance test: the index identification.** The three maximal minors of a `2 × 3` matrix,
at the three two-element column sets. The columns of each set are taken in increasing order, so
the minor at `{1, 2}` is `0 · 3 − 2 · 1 = −2` and not its negative; a construction that enumerated
a column set in any other order is refuted here. -/
example :
    plucker 2 (Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ).row
        ⟨{0, 1}, Set.powersetCard.mem_iff.2 (by decide)⟩ = 1 ∧
      plucker 2 (Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ).row
        ⟨{0, 2}, Set.powersetCard.mem_iff.2 (by decide)⟩ = 3 ∧
      plucker 2 (Matrix.of ![![1, 0, 2], ![0, 1, 3]] : Matrix (Fin 2) (Fin 3) ℚ).row
        ⟨{1, 2}, Set.powersetCard.mem_iff.2 (by decide)⟩ = -2 := by
  have h01 : ⇑(({0, 1} : Finset (Fin 3)).orderEmbOfFin (by decide)) = ![0, 1] :=
    (Finset.orderEmbOfFin_unique _ (by decide) (by decide)).symm
  have h02 : ⇑(({0, 2} : Finset (Fin 3)).orderEmbOfFin (by decide)) = ![0, 2] :=
    (Finset.orderEmbOfFin_unique _ (by decide) (by decide)).symm
  have h12 : ⇑(({1, 2} : Finset (Fin 3)).orderEmbOfFin (by decide)) = ![1, 2] :=
    (Finset.orderEmbOfFin_unique _ (by decide) (by decide)).symm
  refine ⟨?_, ?_, ?_⟩
  · rw [Matrix.plucker_row_eq_det_submatrix, h01, Matrix.det_fin_two]
    norm_num
  · rw [Matrix.plucker_row_eq_det_submatrix, h02, Matrix.det_fin_two]
    norm_num
  · rw [Matrix.plucker_row_eq_det_submatrix, h12, Matrix.det_fin_two]
    norm_num

/-- **Rejection test: the height of the entries is not a height on the Grassmannian.** A row
operation leaves the row space, and hence its height, alone, while it changes the height of the
entries: adding three times the first row of the identity to the second turns a matrix of height
`1` into one of height `3`. This is why the naïve Siegel bound, which is stated in terms of the
entries, is not invariant, and why Bombieri–Vaaler state theirs in terms of the row space. -/
example : ∃ U A : Matrix (Fin 2) (Fin 2) ℚ, IsUnit U.det ∧
    (span ℚ (Set.range (U * A).row)).mulHeight = (span ℚ (Set.range A.row)).mulHeight ∧
    Matrix.mulHeight (U * A) ≠ Matrix.mulHeight A := by
  obtain ⟨U, hUdef⟩ : ∃ U : Matrix (Fin 2) (Fin 2) ℚ, ∀ i j, U i j = ![![1, 0], ![3, 1]] i j :=
    ⟨Matrix.of ![![1, 0], ![3, 1]], fun _ _ ↦ rfl⟩
  have hU : IsUnit U.det := by
    rw [Matrix.det_fin_two]
    simp only [hUdef]
    norm_num
  have h1 : Matrix.mulHeight (1 : Matrix (Fin 2) (Fin 2) ℚ) = 1 := by
    have hx : Matrix.mulHeight (1 : Matrix (Fin 2) (Fin 2) ℚ)
        = Height.mulHeight (((↑) : ℤ → ℚ) ∘
          fun q : Fin 2 × Fin 2 ↦ (1 : Matrix (Fin 2) (Fin 2) ℤ) q.1 q.2) := by
      refine congrArg Height.mulHeight (funext fun q ↦ ?_)
      obtain ⟨i, j⟩ := q
      fin_cases i <;> fin_cases j <;> simp
    have hs : (⨆ q : Fin 2 × Fin 2, |(1 : Matrix (Fin 2) (Fin 2) ℤ) q.1 q.2|) = 1 := by
      refine le_antisymm (ciSup_le fun q ↦ ?_)
        (le_ciSup_of_le (Finite.bddAbove_range _) (0, 0) (by simp))
      obtain ⟨i, j⟩ := q
      fin_cases i <;> fin_cases j <;> simp
    rw [hx, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide), hs]
    norm_num
  have h3 : Matrix.mulHeight U = 3 := by
    have hx : Matrix.mulHeight U = Height.mulHeight (((↑) : ℤ → ℚ) ∘
        fun q : Fin 2 × Fin 2 ↦ (![![1, 0], ![3, 1]] : Matrix (Fin 2) (Fin 2) ℤ) q.1 q.2) := by
      refine congrArg Height.mulHeight (funext fun q ↦ ?_)
      obtain ⟨i, j⟩ := q
      rw [hUdef]
      fin_cases i <;> fin_cases j <;> simp
    have hs : (⨆ q : Fin 2 × Fin 2, |(![![1, 0], ![3, 1]] : Matrix (Fin 2) (Fin 2) ℤ) q.1 q.2|)
        = 3 := by
      refine le_antisymm (ciSup_le fun q ↦ ?_)
        (le_ciSup_of_le (Finite.bddAbove_range _) (1, 0) (by norm_num))
      obtain ⟨i, j⟩ := q
      fin_cases i <;> fin_cases j <;> norm_num
    rw [hx, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide), hs]
    norm_num
  refine ⟨U, 1, hU, Matrix.mulHeight_span_range_row_mul hU 1, ?_⟩
  rw [Matrix.mul_one, h1, h3]
  norm_num

/-- **Conformance.** The milestone's three statements: the height of the row space is the height of
the tuple of maximal minors, it is invariant under row operations, and the two Mathlib spellings of
the row space agree. -/
example {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Fintype ι]
    [LinearOrder ι] {m : ℕ} (A : Matrix (Fin m) ι K) (hA : LinearIndependent K A.row)
    {U : Matrix (Fin m) (Fin m) K} (hU : IsUnit U.det) :
    (span K (Set.range A.row)).mulHeight = Height.mulHeight (plucker m A.row) ∧
      (span K (Set.range (U * A).row)).mulHeight = (span K (Set.range A.row)).mulHeight ∧
      LinearMap.range A.vecMulLinear = span K (Set.range A.row) :=
  ⟨Submodule.mulHeight_span_range hA, Matrix.mulHeight_span_range_row_mul hU A,
    range_vecMulLinear A⟩

end Examples

end
