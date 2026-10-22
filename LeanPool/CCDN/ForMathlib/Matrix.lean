/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Minors and determinants of matrices

Nonzero minors of matrices with arbitrarily many rows: the row index type may be infinite, as
for coefficient matrices indexed by all monomials; only the column index type is finite.

## Main results

* `Matrix.exists_fin_linearIndependent_row_span_eq`: finitely many linearly independent rows
  span the row space.
* `Matrix.exists_rank_linearIndependent_rows`: there are `A.rank` linearly independent rows.
* `Matrix.exists_det_submatrix_ne_zero_of_le_rank`: every `r ≤ A.rank` is witnessed by a
  nonzero `r × r` minor with distinct rows and columns.
* `Matrix.le_rank_of_det_submatrix_ne_zero`: conversely, a nonzero `k × k` minor shows
  `k ≤ A.rank`.
* `Matrix.HasNonzeroMinor`: the predicate that some `r × r` minor is nonzero; its rows and
  columns are automatically distinct (`Matrix.injective_rows_of_det_submatrix_ne_zero`,
  `Matrix.injective_cols_of_det_submatrix_ne_zero`).
* `Matrix.det_blockDiagonal'`: the determinant of `blockDiagonal' M` is the product of the
  determinants of the blocks. Mathlib computes `Matrix.det_blockDiagonal` for blocks of a common
  size; here the blocks may have different sizes.
* `Matrix.dvd_det_sub_det_of_dvd_sub`: entrywise congruence of integer matrices implies
  congruence of their determinants.
-/

@[expose] public section

namespace Matrix

/-- A finite independent family spans the rows even when their original index
set is infinite. -/
theorem exists_fin_linearIndependent_row_span_eq
    {F ι ν : Type*} [Field F] [Finite ν] (A : Matrix ι ν F) :
    ∃ (s : ℕ) (a : Fin s → ι), Function.Injective a ∧
      LinearIndependent F (A.submatrix a id).row ∧
      Submodule.span F (Set.range (A.submatrix a id).row) =
        Submodule.span F (Set.range A.row) := by
  classical
  let := Fintype.ofFinite ν
  obtain ⟨κ, a, ha, hs, hi⟩ := exists_linearIndependent' F A.row
  let : Finite κ := hi.finite
  let : Fintype κ := Fintype.ofFinite κ
  let e := (Fintype.equivFin κ).symm
  have hli : LinearIndependent F (A.submatrix (a ∘ e) id).row := hi.comp e e.injective
  refine ⟨Fintype.card κ, a ∘ e, ha.comp e.injective, hli, ?_⟩
  have hr : Set.range (A.submatrix (a ∘ e) id).row = Set.range (A.row ∘ a) := by
    change Set.range ((A.row ∘ a) ∘ e) = _
    exact e.surjective.range_comp _
  rw [hr, hs]

/-- Restriction to spanning rows preserves the exact kernel. -/
theorem ker_mulVecLin_submatrix_eq_of_span_row_eq
    {F ι κ ν : Type*} [Field F] [Fintype ν] (A : Matrix ι ν F) (a : κ → ι)
    (hs : Submodule.span F (Set.range (A.submatrix a id).row) =
      Submodule.span F (Set.range A.row)) :
    (A.submatrix a id).mulVecLin.ker = A.mulVecLin.ker := by
  ext v
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  constructor
  · intro hv
    ext i
    have hm : A.row i ∈ Submodule.span F (Set.range (A.submatrix a id).row) := by
      rw [hs]
      exact Submodule.subset_span ⟨i, rfl⟩
    change A.row i ⬝ᵥ v = 0
    suffices hh : ∀ r ∈ Submodule.span F (Set.range (A.submatrix a id).row), r ⬝ᵥ v = 0 from hh _ hm
    intro r hr
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨j, rfl⟩ := hr
      exact congrFun hv j
    | zero => simp
    | add x y hx hy ihx ihy => simp [add_dotProduct, ihx, ihy]
    | smul b x hx ih => simp [smul_dotProduct, ih]
  · intro hv
    ext i
    exact congrFun hv (a i)

/-- There are exactly rank-many independent rows. -/
theorem exists_rank_linearIndependent_rows
    {F ι ν : Type*} [Field F] [Fintype ν] (A : Matrix ι ν F) :
    ∃ a : Fin A.rank → ι, Function.Injective a ∧
      LinearIndependent F (A.submatrix a id).row := by
  obtain ⟨s, a, ha, hi, hs⟩ := exists_fin_linearIndependent_row_span_eq A
  have hk := ker_mulVecLin_submatrix_eq_of_span_row_eq A a hs
  have h₁ := (A.submatrix a id).mulVecLin.finrank_range_add_finrank_ker
  have h₂ := A.mulVecLin.finrank_range_add_finrank_ker
  change (A.submatrix a id).rank + _ = _ at h₁
  change A.rank + _ = _ at h₂
  rw [hi.rank_matrix, Fintype.card_fin, hk] at h₁
  have he : s = A.rank := by omega
  subst s
  exact ⟨a, ha, hi⟩

/-- Full row rank supplies a nonzero square minor: some set of columns of the transpose is
linearly independent. -/
theorem exists_det_submatrix_ne_zero_of_linearIndependent_row
    {F ν : Type*} [Field F] [Finite ν] {s : ℕ}
    (A : Matrix (Fin s) ν F) (hi : LinearIndependent F A.row) :
    ∃ c : Fin s → ν, Function.Injective c ∧ (A.submatrix id c).det ≠ 0 := by
  classical
  let := Fintype.ofFinite ν
  have hr : Aᵀ.rank = s := by rw [rank_transpose, hi.rank_matrix, Fintype.card_fin]
  obtain ⟨c, hc, hli⟩ := exists_rank_linearIndependent_rows Aᵀ
  let e := finCongr hr
  refine ⟨c ∘ e.symm, hc.comp e.symm.injective, ?_⟩
  have hcol : LinearIndependent F (A.submatrix id (c ∘ e.symm)).col :=
    hli.comp e.symm e.symm.injective
  rw [← isUnit_iff_ne_zero, ← isUnit_iff_isUnit_det]
  exact linearIndependent_cols_iff_isUnit.mp hcol

/-- Every rank lower bound is witnessed by a nonzero minor with distinct rows
and distinct columns, without any finiteness requirement on the rows. -/
theorem exists_det_submatrix_ne_zero_of_le_rank
    {F ι ν : Type*} [Field F] [Fintype ν] (A : Matrix ι ν F)
    (r : ℕ) (hr : r ≤ A.rank) :
    ∃ (a : Fin r → ι) (c : Fin r → ν), Function.Injective a ∧
      Function.Injective c ∧ (A.submatrix a c).det ≠ 0 := by
  obtain ⟨a, ha, hi⟩ := exists_rank_linearIndependent_rows A
  let b : Fin r → Fin A.rank := Fin.castLE hr
  have hb : Function.Injective b := Fin.castLE_injective hr
  have hli : LinearIndependent F (A.submatrix (a ∘ b) id).row := hi.comp b hb
  obtain ⟨c, hc, hd⟩ := exists_det_submatrix_ne_zero_of_linearIndependent_row _ hli
  exact ⟨a ∘ b, c, ha.comp hb, hc, hd⟩

/-- A nonzero `k × k` minor shows that a matrix over a domain has rank at least `k`. -/
theorem le_rank_of_det_submatrix_ne_zero {R ι ν : Type*} [CommRing R] [IsDomain R] [Fintype ν]
    {k : ℕ} (A : Matrix ι ν R) (r : Fin k → ι) (c : Fin k → ν)
    (h : (A.submatrix r c).det ≠ 0) : k ≤ A.rank := by
  simpa only [rank_of_det_ne_zero h, Fintype.card_fin] using A.rank_submatrix_le r c

/-- The rows selected by a nonzero minor are distinct: a repeated row forces the determinant
to vanish. -/
theorem injective_rows_of_det_submatrix_ne_zero {R ι ν : Type*} [CommRing R] {k : ℕ}
    {A : Matrix ι ν R} {r : Fin k → ι} {c : Fin k → ν} (h : (A.submatrix r c).det ≠ 0) :
    Function.Injective r := by
  intro i j hij
  by_contra hne
  exact h (det_zero_of_row_eq hne (by ext l; simp [hij]))

/-- The columns selected by a nonzero minor are distinct: a repeated column forces the
determinant to vanish. -/
theorem injective_cols_of_det_submatrix_ne_zero {R ι ν : Type*} [CommRing R] {k : ℕ}
    {A : Matrix ι ν R} {r : Fin k → ι} {c : Fin k → ν} (h : (A.submatrix r c).det ≠ 0) :
    Function.Injective c := by
  intro i j hij
  by_contra hne
  exact h (det_zero_of_column_eq hne (by intro l; simp [hij]))

/-- `A` has a nonzero `r × r` minor: some choice of `r` rows and `r` columns of `A` whose
square submatrix has nonzero determinant. The chosen rows and columns are automatically
distinct (`Matrix.injective_rows_of_det_submatrix_ne_zero`,
`Matrix.injective_cols_of_det_submatrix_ne_zero`). -/
def HasNonzeroMinor {R ι ν : Type*} [CommRing R] (A : Matrix ι ν R) (r : ℕ) : Prop :=
  ∃ (a : Fin r → ι) (c : Fin r → ν), (A.submatrix a c).det ≠ 0

/-- Every rank lower bound over a field is witnessed by a nonzero minor. -/
theorem hasNonzeroMinor_of_le_rank {F ι ν : Type*} [Field F] [Fintype ν] (A : Matrix ι ν F)
    {r : ℕ} (hr : r ≤ A.rank) : A.HasNonzeroMinor r :=
  let ⟨a, c, _, _, h⟩ := exists_det_submatrix_ne_zero_of_le_rank A r hr
  ⟨a, c, h⟩

/-- A nonzero `r × r` minor of a matrix over a domain shows `r ≤ A.rank`. -/
theorem HasNonzeroMinor.le_rank {R ι ν : Type*} [CommRing R] [IsDomain R] [Fintype ν]
    {A : Matrix ι ν R} {r : ℕ} (h : A.HasNonzeroMinor r) : r ≤ A.rank :=
  let ⟨a, c, hdet⟩ := h
  le_rank_of_det_submatrix_ne_zero A a c hdet

variable {o R : Type*} {m' : o → Type*} [Fintype o] [DecidableEq o]
  [∀ i, Fintype (m' i)] [∀ i, DecidableEq (m' i)] [CommRing R]

/-- The determinant of a block-diagonal matrix with blocks of varying sizes is the product of
the determinants of its blocks. -/
theorem det_blockDiagonal' (M : ∀ i, Matrix (m' i) (m' i) R) :
    (blockDiagonal' M).det = ∏ i, (M i).det := by
  classical
  let _ : LinearOrder o := LinearOrder.lift' (Fintype.equivFin o) (Fintype.equivFin o).injective
  rw [(blockTriangular_blockDiagonal' M).det_fintype]
  refine Finset.prod_congr rfl fun i _ => ?_
  let e := (Equiv.sigmaSubtype (β := m') i).symm
  have he : ((blockDiagonal' M).toSquareBlock Sigma.fst i).submatrix e e = M i := by
    ext j k
    exact blockDiagonal'_apply_eq M i j k
  rw [← he, det_submatrix_equiv_self]

/-- Entrywise congruence implies determinant congruence, for every modulus. -/
theorem dvd_det_sub_det_of_dvd_sub {s : ℕ} (A B : Matrix (Fin s) (Fin s) ℤ)
    (m : ℤ) (h : ∀ i j, m ∣ A i j - B i j) : m ∣ A.det - B.det := by
  let I : Ideal ℤ := Ideal.span {m}
  let φ := Ideal.Quotient.mk I
  have he : A.map φ = B.map φ := by
    ext i j
    apply sub_eq_zero.mp
    change φ (A i j) - φ (B i j) = 0
    rw [← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (h i j))
  apply Ideal.mem_span_singleton.mp
  change A.det - B.det ∈ I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change φ (A.det - B.det) = 0
  rw [map_sub, φ.map_det, φ.map_det]
  change (A.map φ).det - (B.map φ).det = 0
  rw [he, sub_self]

end Matrix
