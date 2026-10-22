/-
Copyright (c) 2026 Ralf Stephan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ralf Stephan
-/
module

/- Modified for Lean Pool: module paths, toolchain compatibility, and quality repairs.
Upstream: jasondavies/ccdn-dimension-growth @ bb025e7207f3a35a21b898629f5678b72aa7e44f. -/

public import LeanPool.CCDN.ArithmeticHeights.RowSpace
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.StdBasis

-- Used only inside proofs: the complement of a subspace and the basis it produces, the dual
-- basis, the dimension of an annihilator, and the two-sided inverse of a square matrix.
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Projection

/-!
# The duality theorem for the height of a subspace

A subspace and its annihilator have the same height. This is W. M. Schmidt's theorem: the Plücker
coordinates of the annihilator are those of the subspace read at the complementary index, up to a
sign at each index and one common nonzero factor, and every height in this development is
insensitive to exactly that much — a signed reindexing and a scalar.

## Main results

* `Submodule.mulHeight_comap_piEquiv_dualAnnihilator`, with its Arakelov and absolute companions
  `Submodule.arakelovMulHeight_comap_piEquiv_dualAnnihilator` and
  `Submodule.absMulHeight_comap_piEquiv_dualAnnihilator` and every logarithmic form: **the duality
  theorem**, the height of `V` against the height of its annihilator, transported back to `ι → K`
  along the standard basis.
* `Matrix.mulHeight_ker_mulVecLin` and its five companions: **the height of a subspace is the
  height of any matrix cutting it out** (Bombieri–Gubler, Corollary 2.8.12) — the solution space of
  `A x = 0` and the row space of `A` have the same height. This is the form Layer 5 consumes.
* `Submodule.exists_plucker_eq_plucker_compl`: the coordinate statement behind both. A subspace and
  its annihilator have bases whose Plücker coordinates agree at complementary indices up to a sign
  and one common nonzero factor — Schmidt's involution `τ`.
* `Submodule.mem_comap_piEquiv_dualAnnihilator`: the transported annihilator is the orthogonal
  complement for the standard bilinear form, and
  `Submodule.eq_comap_piEquiv_dualAnnihilator_of_forall_dotProduct_eq_zero` is that reading as a
  way into the theorems above. `Submodule.comap_piEquiv_dualAnnihilator_eq_map` is the same
  subspace in the other spelling, the `map` along the inverse identification.
* `Height.mulHeight_eq_of_forall_eq_or_eq_neg` and its Arakelov and absolute companions: no height
  in this development sees a change of sign in a coordinate. These are statements about Mathlib's
  heights and belong upstream.

## Implementation notes

The annihilator lives in the dual space, so it is transported back to `ι → K` along
`Module.piEquiv ι K K`, whose value at `x` is the functional `v ↦ v ⬝ᵥ x`; the transported
annihilator is therefore the orthogonal complement of `V` for the standard bilinear form.
`Submodule.comap_piEquiv_dualAnnihilator_eq_map` turns the `comap` used here into the `map` along
the inverse equivalence, which is the other spelling in use.

⚠ The annihilator and not the orthogonal complement is what the *proof* must use, even though the
two are identified here. Over a field that is not formally real the two summands `V` and `V^⊥` can
meet — over `ℚ(i)`, the line spanned by `(1, i)` is its own orthogonal complement — so the matrix
whose rows are a basis of `V` stacked on a basis of `V^⊥` is singular, and every argument through
its determinant fails. The proof below is stated for a *complement* `W` of `V`, which always
exists, and reaches the annihilator through the dual basis.

The proof is elementary, and in particular uses neither a Laplace expansion along a block of rows
nor Jacobi's identity for the complementary minors of an inverse, neither of which Mathlib has.
Instead: let the rows of `C` be a basis of `ι → K` whose first block is a basis of `V`, and let the
rows of `D` be the dual basis read back in `ι → K`, so that `C * Dᵀ = 1`. For a set `s` of `k`
columns, multiply `C` by the matrix whose first `k` columns are the standard basis vectors at `s`
and whose remaining columns are the second block of `Dᵀ`. The product is block triangular with the
`s`-minor of the first block of `C` in one corner and an identity in the other, while the second
factor, read through the enumeration of `ι` that lists `s` and then its complement, is block
triangular with the complementary minor of the second block of `D` in one corner. Two applications
of `Matrix.det_fromBlocks_zero₁₂` and `Matrix.det_fromBlocks_zero₂₁` give the identity, and the
factor that appears is the determinant of `C` read through that enumeration, which depends on `s`
only through a permutation sign (`Matrix.det_permute'`).

## References

W. M. Schmidt, *On heights of algebraic subspaces and diophantine approximations*, Annals of
Mathematics 85 (1967), §1, equations (2) and (4), where the involution on Grassmann coordinates
that reverses the index order and attaches a sign is what makes the theorem hold in every
normalization at once. E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Cambridge
University Press (2006), Proposition 2.8.10 and Corollary 2.8.12. The underlying linear algebra is
Hindry–Silverman, *Diophantine Geometry: An Introduction*, Exercise A.1.11(c).

This is Layer 3.5 of the `ArithmeticHeights` roadmap.
-/

public section

open Finset Module Set.powersetCard exteriorPower

namespace Height

variable {K : Type*} [Field K] [AdmissibleAbsValues K] {ι : Type*}

/-- **A change of sign in a coordinate does not change the height.** Every absolute value takes
the same value at `x` and at `-x`, and the tuple is zero exactly when the original is, so both
the displayed product and the junk value are unchanged. This is the invariance that the duality
theorem of Layer 3.5 needs, the Plücker coordinates of an annihilator carrying a sign that depends
on the index. -/
theorem mulHeight_eq_of_forall_eq_or_eq_neg {x y : ι → K} (h : ∀ i, y i = x i ∨ y i = -x i) :
    mulHeight y = mulHeight x := by
  have hv (v : AbsoluteValue K ℝ) (i : ι) : v (y i) = v (x i) := by
    rcases h i with hi | hi
    · rw [hi]
    · rw [hi, v.map_neg]
  have hzero : y = 0 ↔ x = 0 := by
    simp only [funext_iff, Pi.zero_apply]
    refine ⟨fun h0 i ↦ ?_, fun h0 i ↦ ?_⟩ <;> rcases h i with hi | hi
    · rw [← hi]; exact h0 i
    · have := h0 i; rw [hi, neg_eq_zero] at this; exact this
    · rw [hi, h0 i]
    · rw [hi, h0 i, neg_zero]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [hzero.2 rfl]
  · have hy : y ≠ 0 := fun h0 ↦ hx (hzero.1 h0)
    rw [mulHeight_eq hx, mulHeight_eq hy]
    congr 1
    · exact congrArg Multiset.prod (Multiset.map_congr rfl fun v _ ↦ iSup_congr (hv v))
    · exact finprod_congr fun v ↦ iSup_congr (hv v.val)

/-- The logarithmic form of `Height.mulHeight_eq_of_forall_eq_or_eq_neg`. -/
theorem logHeight_eq_of_forall_eq_or_eq_neg {x y : ι → K} (h : ∀ i, y i = x i ∨ y i = -x i) :
    logHeight y = logHeight x := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    mulHeight_eq_of_forall_eq_or_eq_neg h]

end Height

namespace NumberField

variable {K : Type*} [Field K] {ι : Type*}

section Arakelov

variable [NumberField K] [Fintype ι]

/-- **A change of sign in a coordinate does not change the Arakelov height** either: the
archimedean factor is a sum of squares of absolute values and the finite factor a supremum of
absolute values, and neither sees a sign. -/
theorem arakelovMulHeight_eq_of_forall_eq_or_eq_neg {x y : ι → K}
    (h : ∀ i, y i = x i ∨ y i = -x i) : arakelovMulHeight y = arakelovMulHeight x := by
  have hinf (v : InfinitePlace K) (i : ι) : v (y i) = v (x i) := by
    rcases h i with hi | hi
    · rw [hi]
    · rw [hi]; exact v.1.map_neg _
  have hfin (v : FinitePlace K) (i : ι) : v (y i) = v (x i) := by
    rcases h i with hi | hi
    · rw [hi]
    · rw [hi]; simp
  have hzero : y = 0 ↔ x = 0 := by
    simp only [funext_iff, Pi.zero_apply]
    refine ⟨fun h0 i ↦ ?_, fun h0 i ↦ ?_⟩ <;> rcases h i with hi | hi
    · rw [← hi]; exact h0 i
    · have := h0 i; rw [hi, neg_eq_zero] at this; exact this
    · rw [hi, h0 i]
    · rw [hi, h0 i, neg_zero]
  rcases eq_or_ne x 0 with rfl | hx
  · rw [hzero.2 rfl]
  · have hy : y ≠ 0 := fun h0 ↦ hx (hzero.1 h0)
    rw [arakelovMulHeight_eq hx, arakelovMulHeight_eq hy]
    congr 1
    · exact Finset.prod_congr rfl fun v _ ↦ by
        rw [Finset.sum_congr rfl fun i _ ↦ by rw [hinf v i]]
    · exact finprod_congr fun v ↦ iSup_congr (hfin v)

/-- The logarithmic form of `NumberField.arakelovMulHeight_eq_of_forall_eq_or_eq_neg`. -/
theorem arakelovLogHeight_eq_of_forall_eq_or_eq_neg {x y : ι → K}
    (h : ∀ i, y i = x i ∨ y i = -x i) : arakelovLogHeight y = arakelovLogHeight x := by
  rw [arakelovLogHeight, arakelovLogHeight, arakelovMulHeight_eq_of_forall_eq_or_eq_neg h]

end Arakelov

section Absolute

variable [CharZero K] [Finite ι]

/-- **A change of sign in a coordinate does not change the absolute height.** The coordinates of
`y` lie in the field generated by those of `x` and conversely, so the two are computed in one and
the same number field, where the relative statement applies. -/
theorem absMulHeight_eq_of_forall_eq_or_eq_neg {x y : ι → K} (h : ∀ i, y i = x i ∨ y i = -x i) :
    absMulHeight y = absMulHeight x := by
  by_cases hx : ∀ i, IsIntegral ℚ (x i)
  · have hmem (i : ι) : y i ∈ IntermediateField.adjoin ℚ (Set.range x) := by
      rcases h i with hi | hi
      · exact hi ▸ IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩
      · exact hi ▸ neg_mem (IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩)
    have hmemx (i : ι) : x i ∈ IntermediateField.adjoin ℚ (Set.range x) :=
      IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩
    have : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range x)) :=
      IntermediateField.finiteDimensional_adjoin fun z hz ↦ by
        obtain ⟨i, rfl⟩ := hz; exact hx i
    have : NumberField (IntermediateField.adjoin ℚ (Set.range x)) := {}
    rw [absMulHeight_eq_of_mem hmem, absMulHeight_eq_of_mem hmemx]
    refine congrArg (· ^ _) (Height.mulHeight_eq_of_forall_eq_or_eq_neg fun i ↦ ?_)
    rcases h i with hi | hi
    · exact Or.inl (Subtype.ext hi)
    · exact Or.inr (Subtype.ext hi)
  · have hy : ¬ ∀ i, IsIntegral ℚ (y i) := fun hy ↦ hx fun i ↦ by
      rcases h i with hi | hi
      · exact hi ▸ hy i
      · have := (hy i).neg
        rwa [hi, neg_neg] at this
    rw [absMulHeight_eq_one_of_not_isIntegral hx, absMulHeight_eq_one_of_not_isIntegral hy]

/-- The logarithmic form of `NumberField.absMulHeight_eq_of_forall_eq_or_eq_neg`. -/
theorem absLogHeight_eq_of_forall_eq_or_eq_neg {x y : ι → K} (h : ∀ i, y i = x i ∨ y i = -x i) :
    absLogHeight y = absLogHeight x := by
  rw [absLogHeight_eq_log_absMulHeight, absLogHeight_eq_log_absMulHeight,
    absMulHeight_eq_of_forall_eq_or_eq_neg h]

end Absolute

end NumberField

namespace Matrix

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {k l : ℕ}

/-- Mathlib's `Matrix.submatrix_mul_equiv`, read as a re-indexing of the inner index of a
product: with both factors square it turns a product of rectangular matrices into a product of
square ones, where `Matrix.det_mul` applies. -/
private lemma mul_eq_submatrix_mul_submatrix {m p r : Type*} [Fintype r]
    (X : Matrix m ι R) (Y : Matrix ι p R) (e : r ≃ ι) :
    X * Y = X.submatrix id e * Y.submatrix e id := by
  rw [Matrix.submatrix_mul_equiv X Y id e id, Matrix.submatrix_id_id]

variable [LinearOrder ι]

/-- The enumeration of `ι` that lists the elements of `s` in increasing order and then those of
its complement. This is the index identification the complementary-minor identity runs on; the
determinant of a matrix read through it depends on `s` only up to a sign. -/
private noncomputable def enumEquiv {s : Finset ι} (hs : s.card = k) (hsc : sᶜ.card = l) :
    Fin k ⊕ Fin l ≃ ι :=
  (Equiv.sumCongr (s.orderIsoOfFin hs).toEquiv
    ((sᶜ.orderIsoOfFin hsc).toEquiv.trans
      (Equiv.subtypeEquivRight fun _ ↦ Finset.mem_compl))).trans (Equiv.sumCompl (· ∈ s))

private lemma enumEquiv_inl {s : Finset ι} (hs : s.card = k) (hsc : sᶜ.card = l) (a : Fin k) :
    enumEquiv hs hsc (Sum.inl a) = s.orderEmbOfFin hs a :=
  Finset.coe_orderIsoOfFin_apply s hs a

private lemma enumEquiv_inr {s : Finset ι} (hs : s.card = k) (hsc : sᶜ.card = l) (b : Fin l) :
    enumEquiv hs hsc (Sum.inr b) = sᶜ.orderEmbOfFin hsc b :=
  Finset.coe_orderIsoOfFin_apply sᶜ hsc b

/-- **The complementary-minor identity.** If the rows of `C` and the rows of `D` are dual to one
another for the standard bilinear form, then the maximal minor of the first block of `C` on the
columns `s` is the complementary minor of the second block of `D` times the determinant of `C`
read through the enumeration attached to `s`. This is the whole content of duality: the
`s`-dependence of the factor is a sign, by `Matrix.det_permute'`. -/
private theorem det_submatrix_inl_eq_mul (C D : Matrix (Fin k ⊕ Fin l) ι R) (hCD : C * Dᵀ = 1)
    {s : Finset ι} (hs : s.card = k) (hsc : sᶜ.card = l) :
    ((C.submatrix Sum.inl id).submatrix id (s.orderEmbOfFin hs)).det
      = (C.submatrix id (enumEquiv hs hsc)).det *
          ((D.submatrix Sum.inr id).submatrix id (sᶜ.orderEmbOfFin hsc)).det := by
  classical
  have hdual (r c : Fin k ⊕ Fin l) :
      ∑ i, C r i * D c i = (1 : Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) R) r c := by
    rw [← hCD, Matrix.mul_apply]
    rfl
  set E : Matrix ι (Fin k ⊕ Fin l) R :=
    Matrix.of fun i r ↦ Sum.elim (fun a ↦ if i = s.orderEmbOfFin hs a then 1 else 0)
      (fun b ↦ D (Sum.inr b) i) r with hE
  have hCE : C * E = Matrix.fromBlocks
      ((C.submatrix Sum.inl id).submatrix id (s.orderEmbOfFin hs)) 0
      ((C.submatrix Sum.inr id).submatrix id (s.orderEmbOfFin hs)) 1 := by
    ext r c
    rcases c with a | b
    · rcases r with a' | b' <;>
        simp [Matrix.mul_apply, hE, mul_ite, Finset.sum_ite_eq' Finset.univ]
    · rcases r with a' | b' <;>
        simp [Matrix.mul_apply, hE, hdual _ (Sum.inr b), Matrix.one_apply]
  have hEσ : E.submatrix (enumEquiv hs hsc) id = Matrix.fromBlocks 1
      (Matrix.of fun a' b ↦ D (Sum.inr b) (s.orderEmbOfFin hs a')) 0
      ((D.submatrix Sum.inr id).submatrix id (sᶜ.orderEmbOfFin hsc))ᵀ := by
    ext r c
    rcases r with a' | b' <;> rcases c with a | b
    · simp only [Matrix.submatrix_apply, id_eq, enumEquiv_inl, hE, Matrix.of_apply, Sum.elim_inl,
        Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
      exact if_congr ⟨fun h ↦ (s.orderEmbOfFin hs).injective h, fun h ↦ by rw [h]⟩ rfl rfl
    · simp [hE, enumEquiv_inl]
    · have hne : sᶜ.orderEmbOfFin hsc b' ≠ s.orderEmbOfFin hs a := by
        intro hcon
        have h1 : sᶜ.orderEmbOfFin hsc b' ∈ sᶜ := sᶜ.orderEmbOfFin_mem hsc b'
        rw [hcon, Finset.mem_compl] at h1
        exact h1 (s.orderEmbOfFin_mem hs a)
      simp [hE, enumEquiv_inr, hne]
    · simp [hE, enumEquiv_inr, Matrix.transpose_apply]
  have hdet : (C * E).det = ((C.submatrix Sum.inl id).submatrix id (s.orderEmbOfFin hs)).det := by
    rw [hCE, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, mul_one]
  rw [← hdet, mul_eq_submatrix_mul_submatrix C E (enumEquiv hs hsc), Matrix.det_mul, hEσ,
    Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul, Matrix.det_transpose]

end Matrix

namespace Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {r : Type*} [Fintype r] [DecidableEq r]

omit [Fintype ι] in
/-- Two enumerations of the column index differ by a permutation, so the determinants they
produce differ by a sign. -/
theorem det_submatrix_equiv_eq_or_eq_neg (X : Matrix r ι K) (e₁ e₂ : r ≃ ι) :
    (X.submatrix id e₁).det = (X.submatrix id e₂).det ∨
      (X.submatrix id e₁).det = -(X.submatrix id e₂).det := by
  have h : X.submatrix id e₁ = (X.submatrix id e₂).submatrix id (e₁.trans e₂.symm) := by
    ext i j
    simp
  rw [h, Matrix.det_permute']
  rcases Int.units_eq_one_or (Equiv.Perm.sign (e₁.trans e₂.symm)) with hs | hs <;> rw [hs] <;> simp

/-- Dual rows make the enumerated determinant a unit. -/
theorem isUnit_det_submatrix_of_mul_transpose_eq_one {C D : Matrix r ι K}
    (hCD : C * Dᵀ = 1) (e : r ≃ ι) : IsUnit (C.submatrix id e).det :=
  IsUnit.of_mul_eq_one ((Dᵀ).submatrix e id).det <| by
    rw [← Matrix.det_mul, ← mul_eq_submatrix_mul_submatrix, hCD, Matrix.det_one]

omit [Fintype r] in
/-- Rows dual to a family of rows are linearly independent. -/
theorem linearIndependent_row_of_mul_transpose_eq_one {C D : Matrix r ι K}
    (hCD : C * Dᵀ = 1) : LinearIndependent K C.row := by
  refine linearIndependent_iff'.2 fun t g hg i hi ↦ ?_
  have h := congrArg (· ⬝ᵥ D.row i) hg
  simp only [sum_dotProduct, smul_dotProduct, zero_dotProduct, smul_eq_mul] at h
  rw [Finset.sum_congr rfl fun j _ ↦ by
    rw [show C.row j ⬝ᵥ D.row i = (C * Dᵀ) j i from rfl, hCD]] at h
  simpa [Matrix.one_apply, Finset.sum_ite_eq' t, hi] using h

/-- The two-sided form of duality of rows: the dual rows expand every vector, with the pairings
against the original rows as coefficients. -/
private lemma eq_sum_dotProduct_smul_row {C D : Matrix r ι K} (hCD : C * Dᵀ = 1)
    (hcard : Fintype.card r = Fintype.card ι) (x : ι → K) :
    x = ∑ j, (C.row j ⬝ᵥ x) • D.row j := by
  classical
  obtain ⟨e⟩ := Fintype.truncEquivOfCardEq hcard
  have hsq : (Dᵀ.submatrix e id) * (C.submatrix id e) = 1 := by
    refine mul_eq_one_comm.1 ?_
    rw [← mul_eq_submatrix_mul_submatrix, hCD]
  have hDC : Dᵀ * C = 1 := by
    have hsub : (Dᵀ * C).submatrix e e = (Dᵀ.submatrix e id) * (C.submatrix id e) := by
      ext a b
      simp [Matrix.mul_apply]
    have h : (Dᵀ * C).submatrix e e = (1 : Matrix ι ι K).submatrix e e := by
      rw [hsub, hsq, Matrix.submatrix_one_equiv]
    have h2 := congrArg (fun M ↦ M.submatrix e.symm e.symm) h
    simpa [Matrix.submatrix_submatrix] using h2
  funext i
  have hx : x i = ∑ a, (Dᵀ * C) i a * x a := by
    rw [hDC]
    simp [Matrix.one_apply, Finset.sum_ite_eq]
  rw [hx, Finset.sum_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, dotProduct,
    Matrix.row, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ ↦ Finset.sum_congr rfl fun a _ ↦ by ring

/-- **The complementary-minor identity, for any enumeration.** If the rows of `C` and of `D` are
dual for the standard bilinear form, the Plücker coordinate at `s` of the first block of `C` is,
up to a sign, the determinant of `C` read through `e` times the Plücker coordinate at the
complement of `s` of the second block of `D`. The factor does not depend on `s`; this is the
local form of duality the twisted duality theorem runs on. -/
theorem plucker_inl_eq_or_eq_neg [LinearOrder ι] {k l : ℕ} (C D : Matrix (Fin k ⊕ Fin l) ι K)
    (hCD : C * Dᵀ = 1) (hlk : l + k = Fintype.card ι) (e : Fin k ⊕ Fin l ≃ ι)
    (s : Set.powersetCard ι k) :
    exteriorPower.plucker k (C.submatrix Sum.inl id).row s =
        (C.submatrix id e).det *
          exteriorPower.plucker l (D.submatrix Sum.inr id).row (Set.powersetCard.compl hlk s) ∨
      exteriorPower.plucker k (C.submatrix Sum.inl id).row s =
        -((C.submatrix id e).det *
          exteriorPower.plucker l (D.submatrix Sum.inr id).row (Set.powersetCard.compl hlk s)) := by
  have hs : (s : Finset ι).card = k := Set.powersetCard.card_eq s
  have hsc : ((s : Finset ι))ᶜ.card = l := by
    rw [Finset.card_compl, hs]
    omega
  rw [Matrix.plucker_row_eq_det_submatrix, Matrix.plucker_row_eq_det_submatrix,
    Matrix.det_submatrix_inl_eq_mul C D hCD hs hsc]
  rcases det_submatrix_equiv_eq_or_eq_neg C (Matrix.enumEquiv hs hsc) e with hsign | hsign
  · refine Or.inl ?_
    rw [hsign]
    rfl
  · refine Or.inr ?_
    rw [hsign, neg_mul]
    rfl

end Matrix

namespace Submodule

open Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] {k l : ℕ}

/-- **The transported annihilator is the orthogonal complement.** `Module.piEquiv ι K K` sends
`x` to the functional `v ↦ v ⬝ᵥ x`, so a vector lies in the annihilator of `V` read back in
`ι → K` exactly when it is orthogonal to `V` for the standard bilinear form. -/
theorem mem_comap_piEquiv_dualAnnihilator {V : Submodule K (ι → K)} {x : ι → K} :
    x ∈ V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap ↔ ∀ v ∈ V, v ⬝ᵥ x = 0 := by
  simp only [Submodule.mem_comap, Submodule.mem_dualAnnihilator]
  refine forall₂_congr fun v _ ↦ ?_
  rw [show ((Module.piEquiv ι K K).toLinearMap x) v = Module.piEquiv ι K K x v from rfl,
    Module.piEquiv_apply_apply]
  simp [dotProduct]

omit [Fintype ι] in
/-- The two spellings of the transported annihilator: the `comap` along the identification of
`ι → K` with its dual, and the `map` along the inverse. This is Mathlib's
`Submodule.comap_equiv_eq_map_symm` in the form the roadmap pins. -/
theorem comap_piEquiv_dualAnnihilator_eq_map [Finite ι] (V : Submodule K (ι → K)) :
    V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap
      = V.dualAnnihilator.map (Module.piEquiv ι K K).symm.toLinearMap := by
  ext x
  rw [Submodule.mem_comap, Submodule.mem_map]
  refine ⟨fun h ↦ ⟨Module.piEquiv ι K K x, h, (Module.piEquiv ι K K).symm_apply_apply x⟩, ?_⟩
  rintro ⟨y, hy, rfl⟩
  rwa [show (Module.piEquiv ι K K).toLinearMap ((Module.piEquiv ι K K).symm.toLinearMap y) = y from
    (Module.piEquiv ι K K).apply_symm_apply y]

/-- The span of a family is orthogonal to `x` as soon as every member is. -/
private lemma span_le_ker_piEquiv {s : Set (ι → K)} {x : ι → K} (h : ∀ v ∈ s, v ⬝ᵥ x = 0) :
    span K s ≤ LinearMap.ker (Module.piEquiv ι K K x) := by
  rw [Submodule.span_le]
  intro v hv
  simpa only [SetLike.mem_coe, LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul,
    dotProduct] using h v hv

/-- **Every subspace sits in a dual pair of matrices.** The rows of `C` are a basis of `ι → K`
whose first block is a basis of `V`; the rows of `D` are the dual basis, read back in `ι → K`
through the standard bilinear form. -/
theorem exists_dual_matrices (V : Submodule K (ι → K)) (hk : finrank K V = k)
    (hlk : l + k = Fintype.card ι) :
    ∃ C D : Matrix (Fin k ⊕ Fin l) ι K, C * Dᵀ = 1 ∧
      span K (Set.range (C.submatrix Sum.inl id).row) = V := by
  classical
  obtain ⟨W, hW⟩ := V.exists_isCompl
  have hWrank : finrank K W = l := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq V W
    rw [hW.sup_eq_top, hW.inf_eq_bot, finrank_top, finrank_bot, hk, Module.finrank_pi] at h
    omega
  let bV := Module.finBasisOfFinrankEq K V hk
  let bW := Module.finBasisOfFinrankEq K W hWrank
  let c : Module.Basis (Fin k ⊕ Fin l) K (ι → K) :=
    (bV.prod bW).map (V.prodEquivOfIsCompl W hW)
  have hcl (a : Fin k) : c (Sum.inl a) = (bV a : ι → K) := by
    simp only [c, Module.Basis.map_apply]
    rw [show (bV.prod bW) (Sum.inl a) = ((bV a : V), (0 : W)) from
      Prod.ext (bV.prod_apply_inl_fst bW a) (bV.prod_apply_inl_snd bW a)]
    simp [V.coe_prodEquivOfIsCompl' W hW ((bV a : V), (0 : W))]
  refine ⟨Matrix.of fun r ↦ (c r), Matrix.of fun s i ↦ c.coord s (Pi.basisFun K ι i), ?_, ?_⟩
  · ext r s
    rw [Matrix.mul_apply, Matrix.one_apply]
    have : ∑ i, c r i * c.coord s (Pi.basisFun K ι i) = c.coord s (c r) := by
      conv_rhs => rw [← (Pi.basisFun K ι).sum_repr (c r)]
      rw [map_sum]
      exact Finset.sum_congr rfl fun i _ ↦ by
        rw [map_smul, smul_eq_mul, Pi.basisFun_repr]
    simp only [Matrix.transpose_apply, Matrix.of_apply]
    rw [this, Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  · have hrange : Set.range ((Matrix.of fun r ↦ (c r) : Matrix (Fin k ⊕ Fin l) ι K).submatrix
        Sum.inl id).row = V.subtype '' (Set.range bV) := by
      rw [← Set.range_comp]
      exact congrArg Set.range (funext fun a ↦ hcl a)
    rw [hrange, Submodule.span_image, bV.span_eq, Submodule.map_top,
      Submodule.range_subtype]

variable [LinearOrder ι]

omit [LinearOrder ι] in
/-- **The second block of the dual basis spans the orthogonal complement.** -/
theorem span_range_inr_row_eq {V : Submodule K (ι → K)} {C D : Matrix (Fin k ⊕ Fin l) ι K}
    (hCD : C * Dᵀ = 1) (hlk : l + k = Fintype.card ι)
    (hV : span K (Set.range (C.submatrix Sum.inl id).row) = V) :
    span K (Set.range (D.submatrix Sum.inr id).row)
      = V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap := by
  have hdual (r t : Fin k ⊕ Fin l) :
      C.row r ⬝ᵥ D.row t = (1 : Matrix (Fin k ⊕ Fin l) (Fin k ⊕ Fin l) K) r t := by
    rw [← hCD]
    rfl
  have hcard : Fintype.card (Fin k ⊕ Fin l) = Fintype.card ι := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  refine le_antisymm (Submodule.span_le.2 ?_) fun x hx ↦ ?_
  · rintro _ ⟨b, rfl⟩
    rw [SetLike.mem_coe, mem_comap_piEquiv_dualAnnihilator]
    intro v hv
    rw [← hV] at hv
    have hker := span_le_ker_piEquiv (s := Set.range (C.submatrix Sum.inl id).row)
      (x := (D.submatrix Sum.inr id).row b) (fun y hy ↦ ?_) hv
    · simpa only [LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul, dotProduct]
        using hker
    · obtain ⟨a, rfl⟩ := hy
      rw [show (C.submatrix Sum.inl id).row a ⬝ᵥ (D.submatrix Sum.inr id).row b
        = C.row (Sum.inl a) ⬝ᵥ D.row (Sum.inr b) from rfl, hdual]
      simp
  · rw [mem_comap_piEquiv_dualAnnihilator] at hx
    have hzero (a : Fin k) : C.row (Sum.inl a) ⬝ᵥ x = 0 :=
      hx _ (hV ▸ Submodule.subset_span ⟨a, rfl⟩)
    have hmem : (∑ j, (C.row j ⬝ᵥ x) • D.row j)
        ∈ span K (Set.range (D.submatrix Sum.inr id).row) := by
      rw [Fintype.sum_sum_type]
      simp only [hzero, zero_smul, Finset.sum_const_zero, zero_add]
      exact Submodule.sum_mem _ fun b _ ↦
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)
    rwa [← Matrix.eq_sum_dotProduct_smul_row hCD hcard x] at hmem

/-- **Plücker duality in coordinates** (W. M. Schmidt 1967, §1, equations (2) and (4)). A
subspace and its annihilator have bases whose Plücker coordinates agree at complementary indices,
up to a sign at each index and one common nonzero factor — the involution Schmidt calls `τ`.
Every height in this development is invariant under exactly that much. -/
theorem exists_plucker_eq_plucker_compl (V : Submodule K (ι → K)) (hk : finrank K V = k)
    (hlk : l + k = Fintype.card ι) :
    ∃ (v : Fin k → (ι → K)) (w : Fin l → (ι → K)) (c : K), c ≠ 0 ∧
      LinearIndependent K v ∧ LinearIndependent K w ∧
      span K (Set.range v) = V ∧
      span K (Set.range w) = V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap ∧
      ∀ s : Set.powersetCard ι k,
        exteriorPower.plucker k v s
            = c * exteriorPower.plucker l w (Set.powersetCard.compl hlk s) ∨
          exteriorPower.plucker k v s
            = -(c * exteriorPower.plucker l w (Set.powersetCard.compl hlk s)) := by
  classical
  obtain ⟨C, D, hCD, hV⟩ := exists_dual_matrices V hk hlk
  have hcard : Fintype.card (Fin k ⊕ Fin l) = Fintype.card ι := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  obtain ⟨e₀⟩ := Fintype.truncEquivOfCardEq hcard
  have hDC : D * Cᵀ = 1 := by
    have h := congrArg Matrix.transpose hCD
    rwa [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
  refine ⟨(C.submatrix Sum.inl id).row, (D.submatrix Sum.inr id).row, (C.submatrix id e₀).det,
    (Matrix.isUnit_det_submatrix_of_mul_transpose_eq_one hCD e₀).ne_zero,
    (Matrix.linearIndependent_row_of_mul_transpose_eq_one hCD).comp _ Sum.inl_injective,
    (Matrix.linearIndependent_row_of_mul_transpose_eq_one hDC).comp _ Sum.inr_injective,
    hV, span_range_inr_row_eq hCD hlk hV, fun s ↦ ?_⟩
  have hs : (s : Finset ι).card = k := Set.powersetCard.card_eq s
  have hsc : ((s : Finset ι))ᶜ.card = l := by
    rw [Finset.card_compl, hs]
    omega
  rw [Matrix.plucker_row_eq_det_submatrix, Matrix.plucker_row_eq_det_submatrix,
    Matrix.det_submatrix_inl_eq_mul C D hCD hs hsc]
  rcases Matrix.det_submatrix_equiv_eq_or_eq_neg C (Matrix.enumEquiv hs hsc) e₀ with hsign | hsign
  · refine Or.inl ?_
    rw [hsign]
    rfl
  · refine Or.inr ?_
    rw [hsign, neg_mul]
    rfl

end Submodule

namespace Submodule

open Matrix exteriorPower

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- The two tuples of Plücker coordinates attached to `V` and to its annihilator, with the
relation between them. This is `Submodule.exists_plucker_eq_plucker_compl` with the two ranks
existentially bound, the form the height statements consume. -/
private lemma exists_plucker_pair (V : Submodule K (ι → K)) :
    ∃ (k l : ℕ) (hlk : l + k = Fintype.card ι) (v : Fin k → (ι → K)) (w : Fin l → (ι → K))
      (c : K), c ≠ 0 ∧ LinearIndependent K v ∧ LinearIndependent K w ∧
      span K (Set.range v) = V ∧
      span K (Set.range w) = V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap ∧
      ∀ s : Set.powersetCard ι k,
        plucker k v s = c * plucker l w (Set.powersetCard.compl hlk s) ∨
          plucker k v s = -(c * plucker l w (Set.powersetCard.compl hlk s)) := by
  have hle : Module.finrank K V ≤ Fintype.card ι := by
    have h := V.finrank_le (R := K)
    rwa [Module.finrank_pi] at h
  obtain ⟨v, w, c, hc, hv, hw, hVv, hWw, hpl⟩ :=
    exists_plucker_eq_plucker_compl V (l := Fintype.card ι - Module.finrank K V) rfl (by omega)
  exact ⟨_, _, _, v, w, c, hc, hv, hw, hVv, hWw, hpl⟩

section Relative

variable [Height.AdmissibleAbsValues K]

/-- **The duality theorem** (W. M. Schmidt 1967; Bombieri–Gubler, Proposition 2.8.10): a subspace
and its annihilator have the same height, the annihilator being read back in `ι → K` along the
standard basis. By `Submodule.mem_comap_piEquiv_dualAnnihilator` the subspace on the left is the
orthogonal complement of `V` for the standard bilinear form. -/
theorem mulHeight_comap_piEquiv_dualAnnihilator (V : Submodule K (ι → K)) :
    (V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap).mulHeight = V.mulHeight := by
  obtain ⟨k, l, hlk, v, w, c, hc, hv, hw, hVv, hWw, hpl⟩ := exists_plucker_pair V
  rw [← hWw, ← hVv, mulHeight_span_range hv, mulHeight_span_range hw,
    Height.mulHeight_eq_of_forall_eq_or_eq_neg hpl,
    show (fun s ↦ c * plucker l w (Set.powersetCard.compl hlk s))
      = c • (plucker l w ∘ (Set.powersetCard.compl hlk)) from rfl,
    Height.mulHeight_smul_eq_mulHeight _ hc, Height.mulHeight_comp_equiv]

/-- The logarithmic form of `Submodule.mulHeight_comap_piEquiv_dualAnnihilator`. -/
theorem logHeight_comap_piEquiv_dualAnnihilator (V : Submodule K (ι → K)) :
    (V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap).logHeight = V.logHeight := by
  rw [logHeight_eq_log_mulHeight, logHeight_eq_log_mulHeight,
    mulHeight_comap_piEquiv_dualAnnihilator]

end Relative

section Arakelov

variable [NumberField K]

/-- **The duality theorem in the Arakelov normalization** (Bombieri–Gubler, Proposition 2.8.10).
Schmidt's mechanism gives both normalizations at once: the two coordinate tuples differ by a
signed reindexing and a scalar, and no height in Layer 0 sees either. -/
theorem arakelovMulHeight_comap_piEquiv_dualAnnihilator (V : Submodule K (ι → K)) :
    (V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap).arakelovMulHeight =
      V.arakelovMulHeight := by
  obtain ⟨k, l, hlk, v, w, c, hc, hv, hw, hVv, hWw, hpl⟩ := exists_plucker_pair V
  rw [← hWw, ← hVv, arakelovMulHeight_span_range hv, arakelovMulHeight_span_range hw,
    NumberField.arakelovMulHeight_eq_of_forall_eq_or_eq_neg hpl,
    show (fun s ↦ c * plucker l w (Set.powersetCard.compl hlk s))
      = c • (plucker l w ∘ (Set.powersetCard.compl hlk)) from rfl,
    NumberField.arakelovMulHeight_smul_eq _ hc, NumberField.arakelovMulHeight_comp_equiv]

/-- The logarithmic form of `Submodule.arakelovMulHeight_comap_piEquiv_dualAnnihilator`. -/
theorem arakelovLogHeight_comap_piEquiv_dualAnnihilator (V : Submodule K (ι → K)) :
    (V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap).arakelovLogHeight =
      V.arakelovLogHeight := by
  rw [arakelovLogHeight_eq_log_arakelovMulHeight, arakelovLogHeight_eq_log_arakelovMulHeight,
    arakelovMulHeight_comap_piEquiv_dualAnnihilator]

end Arakelov

section Absolute

variable [CharZero K] [Algebra.IsAlgebraic ℚ K]

/-- **The duality theorem for the absolute height.** -/
theorem absMulHeight_comap_piEquiv_dualAnnihilator (V : Submodule K (ι → K)) :
    (V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap).absMulHeight =
      V.absMulHeight := by
  obtain ⟨k, l, hlk, v, w, c, hc, hv, hw, hVv, hWw, hpl⟩ := exists_plucker_pair V
  rw [← hWw, ← hVv, absMulHeight_span_range hv, absMulHeight_span_range hw,
    NumberField.absMulHeight_eq_of_forall_eq_or_eq_neg hpl,
    show (fun s ↦ c * plucker l w (Set.powersetCard.compl hlk s))
      = c • (plucker l w ∘ (Set.powersetCard.compl hlk)) from rfl,
    NumberField.absMulHeight_smul_eq _ hc (Algebra.IsAlgebraic.isAlgebraic c),
    NumberField.absMulHeight_comp_equiv]

/-- The logarithmic form of `Submodule.absMulHeight_comap_piEquiv_dualAnnihilator`. -/
theorem absLogHeight_comap_piEquiv_dualAnnihilator (V : Submodule K (ι → K)) :
    (V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap).absLogHeight =
      V.absLogHeight := by
  rw [absLogHeight_eq_log_absMulHeight, absLogHeight_eq_log_absMulHeight,
    absMulHeight_comap_piEquiv_dualAnnihilator]

end Absolute

end Submodule

namespace Submodule

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι]

/-- **The orthogonal-complement form of the hypothesis.** A subspace cut out by orthogonality to
`V` for the standard bilinear form *is* the transported annihilator, so each duality theorem above
applies to it. `Submodule.comap_piEquiv_dualAnnihilator_eq_map` turns the `comap` into a `map`
along the inverse, which is the other spelling in use. -/
theorem eq_comap_piEquiv_dualAnnihilator_of_forall_dotProduct_eq_zero
    {V W : Submodule K (ι → K)} (h : ∀ x, x ∈ W ↔ ∀ v ∈ V, v ⬝ᵥ x = 0) :
    W = V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap :=
  SetLike.ext fun x ↦ (h x).trans mem_comap_piEquiv_dualAnnihilator.symm

end Submodule

namespace Matrix

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [LinearOrder ι] {m : Type*}

omit [LinearOrder ι] in
/-- **The solution space of `A x = 0` is the orthogonal complement of the row space of `A`.** -/
theorem ker_mulVecLin_eq_comap_piEquiv_dualAnnihilator (A : Matrix m ι K) :
    LinearMap.ker A.mulVecLin =
      (Submodule.span K (Set.range A.row)).dualAnnihilator.comap
        (Module.piEquiv ι K K).toLinearMap := by
  refine Submodule.eq_comap_piEquiv_dualAnnihilator_of_forall_dotProduct_eq_zero fun x ↦ ?_
  simp only [LinearMap.mem_ker, Matrix.mulVecLin_apply]
  refine ⟨fun h v hv ↦ ?_, fun h ↦ funext fun i ↦ h _ (Submodule.subset_span ⟨i, rfl⟩)⟩
  have hker := Submodule.span_le_ker_piEquiv (s := Set.range A.row) (x := x)
    (fun y hy ↦ by obtain ⟨i, rfl⟩ := hy; exact congrFun h i) hv
  simpa only [LinearMap.mem_ker, Module.piEquiv_apply_apply, smul_eq_mul, dotProduct] using hker

section Relative

variable [Height.AdmissibleAbsValues K]

/-- **The height of a subspace is the height of any matrix cutting it out** (Bombieri–Gubler,
Corollary 2.8.12): the solution space of `A x = 0` and the row space of `A` have the same height.
This is the form Layer 5 consumes, the right-hand side being `H(A)` of Bombieri–Vaaler. -/
theorem mulHeight_ker_mulVecLin (A : Matrix m ι K) :
    (LinearMap.ker A.mulVecLin).mulHeight = (Submodule.span K (Set.range A.row)).mulHeight := by
  rw [ker_mulVecLin_eq_comap_piEquiv_dualAnnihilator,
    Submodule.mulHeight_comap_piEquiv_dualAnnihilator]

/-- The logarithmic form of `Matrix.mulHeight_ker_mulVecLin`. -/
theorem logHeight_ker_mulVecLin (A : Matrix m ι K) :
    (LinearMap.ker A.mulVecLin).logHeight = (Submodule.span K (Set.range A.row)).logHeight := by
  rw [ker_mulVecLin_eq_comap_piEquiv_dualAnnihilator,
    Submodule.logHeight_comap_piEquiv_dualAnnihilator]

end Relative

section Arakelov

variable [NumberField K]

/-- **The Arakelov height of a subspace is the Arakelov height of any matrix cutting it out**
(Bombieri–Gubler, Corollary 2.8.12), `H_Ar^row(A)` of Bombieri–Vaaler. -/
theorem arakelovMulHeight_ker_mulVecLin (A : Matrix m ι K) :
    (LinearMap.ker A.mulVecLin).arakelovMulHeight =
      (Submodule.span K (Set.range A.row)).arakelovMulHeight := by
  rw [ker_mulVecLin_eq_comap_piEquiv_dualAnnihilator,
    Submodule.arakelovMulHeight_comap_piEquiv_dualAnnihilator]

/-- The logarithmic form of `Matrix.arakelovMulHeight_ker_mulVecLin`. -/
theorem arakelovLogHeight_ker_mulVecLin (A : Matrix m ι K) :
    (LinearMap.ker A.mulVecLin).arakelovLogHeight =
      (Submodule.span K (Set.range A.row)).arakelovLogHeight := by
  rw [ker_mulVecLin_eq_comap_piEquiv_dualAnnihilator,
    Submodule.arakelovLogHeight_comap_piEquiv_dualAnnihilator]

end Arakelov

section Absolute

variable [CharZero K] [Algebra.IsAlgebraic ℚ K]

/-- **The absolute height of a subspace is the absolute height of any matrix cutting it out.** -/
theorem absMulHeight_ker_mulVecLin (A : Matrix m ι K) :
    (LinearMap.ker A.mulVecLin).absMulHeight =
      (Submodule.span K (Set.range A.row)).absMulHeight := by
  rw [ker_mulVecLin_eq_comap_piEquiv_dualAnnihilator,
    Submodule.absMulHeight_comap_piEquiv_dualAnnihilator]

/-- The logarithmic form of `Matrix.absMulHeight_ker_mulVecLin`. -/
theorem absLogHeight_ker_mulVecLin (A : Matrix m ι K) :
    (LinearMap.ker A.mulVecLin).absLogHeight =
      (Submodule.span K (Set.range A.row)).absLogHeight := by
  rw [ker_mulVecLin_eq_comap_piEquiv_dualAnnihilator,
    Submodule.absLogHeight_comap_piEquiv_dualAnnihilator]

end Absolute

end Matrix

/-!
### Worked examples
-/

section Examples

open Matrix Submodule

/-- The height of the point `(1 : 3)` of the rational projective line. -/
private lemma mulHeight_one_three : Height.mulHeight ![(1 : ℚ), 3] = 3 := by
  have hx : (![(1 : ℚ), 3]) = ((↑) : ℤ → ℚ) ∘ ![(1 : ℤ), 3] := by
    funext i
    fin_cases i <;> simp
  have hs : (⨆ i, |(![(1 : ℤ), 3]) i|) = 3 := by
    refine le_antisymm (ciSup_le fun i ↦ ?_)
      (le_ciSup_of_le (Finite.bddAbove_range _) 1 (by norm_num))
    fin_cases i <;> norm_num
  rw [hx, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide), hs]
  norm_num

/-- The height of the point `(0 : 1)`. -/
private lemma mulHeight_zero_one : Height.mulHeight ![(0 : ℚ), 1] = 1 := by
  have hx : (![(0 : ℚ), 1]) = ((↑) : ℤ → ℚ) ∘ ![(0 : ℤ), 1] := by
    funext i
    fin_cases i <;> simp
  have hs : (⨆ i, |(![(0 : ℤ), 1]) i|) = 1 := by
    refine le_antisymm (ciSup_le fun i ↦ ?_)
      (le_ciSup_of_le (Finite.bddAbove_range _) 1 (by norm_num))
    fin_cases i <;> norm_num
  rw [hx, Rat.mulHeight_eq_max_abs_of_gcd_eq_one (by decide), hs]
  norm_num

/-- **Acceptance test: the height of a solution space, computed from the matrix.** The line
`x₀ + 3 x₁ = 0` in `ℚ²` has height `3`, the height of the single row `(1, 3)` that cuts it out —
this is Corollary 2.8.12 on the smallest case where the answer is not `1`, and it is the step
Layer 5 takes when it bounds the solutions of `A x = 0` by the height of the row space of `A`.
A duality theorem that returned the height of the entries of the *solution*, or that returned `1`,
is refuted here. -/
example :
    (LinearMap.ker (Matrix.of ![![(1 : ℚ), 3]] : Matrix (Fin 1) (Fin 2) ℚ).mulVecLin).mulHeight
      = 3 := by
  rw [Matrix.mulHeight_ker_mulVecLin]
  have hrange : Set.range (Matrix.of ![![(1 : ℚ), 3]] : Matrix (Fin 1) (Fin 2) ℚ).row
      = {![(1 : ℚ), 3]} := Set.range_unique
  have hne : ![(1 : ℚ), 3] ≠ 0 := fun h ↦ by simpa using congrFun h 0
  rw [hrange, Submodule.mulHeight_span_singleton hne, mulHeight_one_three]

/-- **Rejection test: the annihilator, not an arbitrary complement.** The line spanned by
`(0, 1)` is a complement of the line spanned by `(1, 3)` in `ℚ²`, and the two have different
heights — `1` against `3`. So the duality theorem is a statement about the annihilator and not
about complements, and the proof above may not replace the annihilator by the complement it picks
up along the way when it extends a basis. -/
example : (span ℚ {![(1 : ℚ), 3]}) ⊔ (span ℚ {![(0 : ℚ), 1]}) = ⊤ ∧
    (span ℚ {![(0 : ℚ), 1]}).mulHeight ≠ (span ℚ {![(1 : ℚ), 3]}).mulHeight := by
  constructor
  · refine Submodule.eq_top_iff'.2 fun x ↦ ?_
    have hx : x = x 0 • ![(1 : ℚ), 3] + (x 1 - 3 * x 0) • ![(0 : ℚ), 1] := by
      funext i
      fin_cases i
      · simp
      · simp
        ring
    rw [hx]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  · have h0 : ![(0 : ℚ), 1] ≠ 0 := fun h ↦ by simpa using congrFun h 1
    have h1 : ![(1 : ℚ), 3] ≠ 0 := fun h ↦ by simpa using congrFun h 0
    rw [Submodule.mulHeight_span_singleton h0, Submodule.mulHeight_span_singleton h1,
      mulHeight_zero_one, mulHeight_one_three]
    norm_num

/-- **Acceptance test in the Arakelov normalization, the roadmap's worked case.** The plane
`x₀ + x₁ + x₂ = 0` in `ℚ³` has Arakelov height `√3`, the Arakelov height of the row `(1, 1, 1)`
that cuts it out — and Cauchy–Binet reads the same number off the Gram determinant
`det (A Aᵀ) = 3`. A duality theorem that returned `1` here has confused the Arakelov height with
the sup-norm height, which is `1` on this tuple by the product formula. -/
example :
    (LinearMap.ker
        (Matrix.of ![![(1 : ℚ), 1, 1]] : Matrix (Fin 1) (Fin 3) ℚ).mulVecLin).arakelovMulHeight
      = Real.sqrt 3 := by
  have hrange : Set.range (Matrix.of ![![(1 : ℚ), 1, 1]] : Matrix (Fin 1) (Fin 3) ℚ).row
      = {![(1 : ℚ), 1, 1]} := Set.range_unique
  have hne : ![(1 : ℚ), 1, 1] ≠ 0 := fun h ↦ by simpa using congrFun h 0
  rw [Matrix.arakelovMulHeight_ker_mulVecLin, hrange,
    Submodule.arakelovMulHeight_span_singleton hne,
    show ![(1 : ℚ), 1, 1] = 1 from by funext i; fin_cases i <;> rfl,
    NumberField.arakelovMulHeight_one, Fintype.card_fin, NumberField.totalWeight_eq_finrank,
    Module.finrank_self, Nat.cast_one, Real.sqrt_eq_rpow]
  norm_num

/-- **Rejection test: a subspace can meet its own orthogonal complement.** Over `ℂ` the line
spanned by `(1, i)` is isotropic — `1 · 1 + i · i = 0` — so it lies inside the orthogonal
complement it is supposed to be dual to, and the square matrix obtained by stacking a basis of the
line on a basis of the complement is singular. Every proof of duality that expands the determinant
of that stack therefore fails over a field that is not formally real; the proof above runs through
an arbitrary complement and the dual basis instead, and never forms the stack. -/
example : ![(1 : ℂ), Complex.I] ∈
    (Submodule.span ℂ {![(1 : ℂ), Complex.I]}).dualAnnihilator.comap
      (Module.piEquiv (Fin 2) ℂ ℂ).toLinearMap := by
  rw [Submodule.mem_comap_piEquiv_dualAnnihilator]
  intro v hv
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
  simp only [dotProduct, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_fin_one, smul_eq_mul, mul_one]
  rw [mul_assoc, Complex.I_mul_I]
  ring

/-- **Conformance.** The milestone's two statements: a subspace and its annihilator have the same
height, and the height of a subspace is the height of any matrix cutting it out. -/
example {K : Type*} [Field K] [Height.AdmissibleAbsValues K] {ι : Type*} [Fintype ι]
    [LinearOrder ι] (V : Submodule K (ι → K)) {m : Type*} (A : Matrix m ι K) :
    (V.dualAnnihilator.comap (Module.piEquiv ι K K).toLinearMap).mulHeight = V.mulHeight ∧
      (LinearMap.ker A.mulVecLin).mulHeight = (span K (Set.range A.row)).mulHeight :=
  ⟨Submodule.mulHeight_comap_piEquiv_dualAnnihilator V, Matrix.mulHeight_ker_mulVecLin A⟩

end Examples
