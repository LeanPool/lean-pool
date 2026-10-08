/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormFoundations
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Kronecker
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# High-contrast homogenization: Entry.Analysis.SingularValueTheory

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Singular Value Theory

The singular values of a real square matrix: their definition and trace bound, the best rank-`k`
approximation in the operator norm, the moment identity relating them to the Schatten norm, and
their amplification under tensor powers. The trace and Schatten-moment bounds serve
`l.fixed.geometry.matrix.averaging`; the rank approximation serves the Schatten ideal property
consumed by `p.fixed.geometry.parent.child.recurrence`.
-/

section
/-!
## Singular values and the trace bound

Singular values of a real square matrix are square roots of its Gram
eigenvalues. `singularValues` uses the original index type, without an order
claim; `singularValues₀` uses Mathlib's decreasing eigenvalue enumeration.
The trace bound uses a Gram eigenbasis and scalar Cauchy–Schwarz, so it
also applies to singular matrices and empty index types.
-/

namespace HCPolySupport.HighContrast.Analysis

open scoped BigOperators

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Singular values indexed by the original matrix index type, without an ordering claim. -/
@[expose]
def singularValues (X : Matrix n n ℝ) (i : n) : ℝ :=
  Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i)

/-- Singular values in decreasing order, indexed from zero. -/
@[expose]
def singularValues₀ (X : Matrix n n ℝ) (i : Fin (Fintype.card n)) : ℝ :=
  Real.sqrt ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues₀ i)

theorem singularValues_nonneg (X : Matrix n n ℝ) (i : n) :
    0 ≤ singularValues X i := Real.sqrt_nonneg _

theorem singularValues₀_nonneg (X : Matrix n n ℝ) (i : Fin (Fintype.card n)) :
    0 ≤ singularValues₀ X i := Real.sqrt_nonneg _

theorem singularValues₀_antitone (X : Matrix n n ℝ) : Antitone (singularValues₀ X) := by
  intro i j hij
  exact Real.sqrt_le_sqrt
    ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues₀_antitone hij)

theorem sum_singularValues₀ (X : Matrix n n ℝ) (f : ℝ → ℝ) :
    ∑ i, f (singularValues₀ X i) = ∑ i, f (singularValues X i) := by
  let e : n ≃ Fin (Fintype.card n) :=
    (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  exact (e.sum_comp (fun i => f (singularValues₀ X i))).symm

private theorem sum_sq_col_unitary (U : Matrix.unitaryGroup n ℝ) (i : n) :
    ∑ j, (U : Matrix n n ℝ) j i ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix n n ℝ => M i i) (Unitary.coe_star_mul_self U)
  simpa only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    star_trivial, Matrix.one_apply_eq, pow_two] using h

private theorem sum_sq_col_mul_gram_unitary (X : Matrix n n ℝ) (i : n) :
    ∑ j, (X * (Matrix.isHermitian_conjTranspose_mul_self X).eigenvectorUnitary) j i ^ 2 =
      (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues i := by
  let hG := Matrix.isHermitian_conjTranspose_mul_self X
  let U := hG.eigenvectorUnitary
  have hdiag : star (X * (U : Matrix n n ℝ)) * (X * (U : Matrix n n ℝ)) =
      Matrix.diagonal hG.eigenvalues := by
    have h := hG.conjStarAlgAut_star_eigenvectorUnitary
    simpa only [Unitary.conjStarAlgAut_star_apply, star_mul, Matrix.mul_assoc,
      RCLike.ofReal_real_eq_id, Function.id_comp] using! h
  have h := congrArg (fun M : Matrix n n ℝ => M i i) hdiag
  simpa only [Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    star_trivial, Matrix.diagonal_apply_eq, pow_two] using h

theorem abs_trace_le_sum_singularValues (X : Matrix n n ℝ) :
    |Matrix.trace X| ≤ ∑ i, singularValues X i := by
  let hG := Matrix.isHermitian_conjTranspose_mul_self X
  let U := hG.eigenvectorUnitary
  have htrace : Matrix.trace (star (U : Matrix n n ℝ) * X * (U : Matrix n n ℝ)) =
      Matrix.trace X := by
    rw [Matrix.trace_mul_cycle, Unitary.mul_star_self_of_mem U.prop, one_mul]
  rw [← htrace, Matrix.trace]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => (U : Matrix n n ℝ) j i) (fun j => (X * (U : Matrix n n ℝ)) j i)
  rw [sum_sq_col_unitary U i, one_mul, sum_sq_col_mul_gram_unitary X i] at hcs
  have hentry : (star (U : Matrix n n ℝ) * X * (U : Matrix n n ℝ)) i i =
      ∑ j, (U : Matrix n n ℝ) j i * (X * (U : Matrix n n ℝ)) j i := by
    rw [Matrix.mul_assoc, Matrix.mul_apply]
    simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply, star_trivial]
  change |(star (U : Matrix n n ℝ) * X * (U : Matrix n n ℝ)) i i| ≤ singularValues X i
  rw [hentry]
  calc
    |∑ j, (U : Matrix n n ℝ) j i * (X * (U : Matrix n n ℝ)) j i| =
        Real.sqrt ((∑ j, (U : Matrix n n ℝ) j i * (X * (U : Matrix n n ℝ)) j i) ^ 2) :=
      (Real.sqrt_sq_eq_abs _).symm
    _ ≤ singularValues X i := Real.sqrt_le_sqrt hcs

theorem abs_trace_le_sum_singularValues₀ (X : Matrix n n ℝ) :
    |Matrix.trace X| ≤ ∑ i, singularValues₀ X i := by
  rw [sum_singularValues₀ X (fun x => x)]
  exact abs_trace_le_sum_singularValues X

end

end HCPolySupport.HighContrast.Analysis
end

section
/-!
## Approximation by matrices of bounded rank

The decreasing singular values, padded by zero, characterize approximation
in the L2 operator norm. All statements allow an empty index type.
-/

namespace HCPolySupport.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The decreasing singular values, indexed from zero and padded by zero. -/
@[expose]
def singularValueAt (X : Matrix n n ℝ) (r : ℕ) : ℝ :=
  if h : r < Fintype.card n then singularValues₀ X ⟨r, h⟩ else 0

theorem singularValueAt_nonneg (X : Matrix n n ℝ) (r : ℕ) :
    0 ≤ singularValueAt X r := by
  unfold singularValueAt
  split
  · exact singularValues₀_nonneg X _
  · exact le_rfl

theorem singularValueAt_antitone (X : Matrix n n ℝ) : Antitone (singularValueAt X) := by
  intro i j hij
  by_cases hj : j < Fintype.card n
  · have hi := lt_of_le_of_lt hij hj
    simp only [singularValueAt, dite_eq_left hi, dite_eq_left hj]
    exact singularValues₀_antitone X hij
  · simp only [singularValueAt, dite_eq_right hj]
    split
    · exact singularValues₀_nonneg X _
    · exact le_rfl

theorem singularValueAt_eq_zero (X : Matrix n n ℝ) {r : ℕ}
    (hr : Fintype.card n ≤ r) : singularValueAt X r = 0 := by
  exact dite_eq_right (not_lt_of_ge hr)

omit [DecidableEq n] in
theorem rank_add_le (X Y : Matrix n n ℝ) : (X + Y).rank ≤ X.rank + Y.rank := by
  unfold Matrix.rank
  rw [Matrix.mulVecLin_add]
  exact (Submodule.finrank_mono (LinearMap.range_add_le X.mulVecLin Y.mulVecLin)).trans
    (Submodule.finrank_add_le_finrank_add_finrank _ _)

private theorem gram_diagonal (X : Matrix n n ℝ) :
    star (X * (isHermitian_conjTranspose_mul_self X).eigenvectorUnitary) *
        (X * (isHermitian_conjTranspose_mul_self X).eigenvectorUnitary) =
      diagonal (isHermitian_conjTranspose_mul_self X).eigenvalues := by
  simpa only [Unitary.conjStarAlgAut_star_apply, StarMul.star_mul, Matrix.mul_assoc,
    RCLike.ofReal_real_eq_id, Function.id_comp] using!
    (isHermitian_conjTranspose_mul_self X).conjStarAlgAut_star_eigenvectorUnitary

omit [DecidableEq n] in
private theorem dot_mulVec_self (A : Matrix n n ℝ) (v : n → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ ((star A * A) *ᵥ v) := by
  symm
  rw [← mulVec_mulVec, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, dotProduct_mulVec, vecMul_transpose]

private theorem dot_gram_coordinates (X : Matrix n n ℝ) (v : n → ℝ) :
    ((X * ((isHermitian_conjTranspose_mul_self X).eigenvectorUnitary : Matrix n n ℝ)) *ᵥ v) ⬝ᵥ
        ((X * ((isHermitian_conjTranspose_mul_self X).eigenvectorUnitary : Matrix n n ℝ)) *ᵥ v) =
      ∑ i, (isHermitian_conjTranspose_mul_self X).eigenvalues i * v i ^ 2 := by
  rw [dot_mulVec_self, gram_diagonal]
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem dot_mulVec_le (A : Matrix n n ℝ) (v : n → ℝ) :
    (A *ᵥ v) ⬝ᵥ (A *ᵥ v) ≤ ‖A‖ ^ 2 * (v ⬝ᵥ v) := by
  have h := (Matrix.toEuclideanCLM (n := n) (𝕜 := ℝ) A).le_opNorm (WithLp.toLp 2 v)
  have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.2 h
  rw [Matrix.toEuclideanCLM_toLp, Matrix.l2_opNorm_toEuclideanCLM, mul_pow,
    EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq] at hs
  simp only [Real.norm_eq_abs] at hs
  simp only [sq_abs] at hs
  simpa only [dotProduct, pow_two] using hs

omit [DecidableEq n] in
private theorem exists_supported_kernel (B : Matrix n n ℝ)
    (e : n ≃ Fin (Fintype.card n)) (r : ℕ) (hr : r < Fintype.card n)
    (hB : B.rank ≤ r) :
    ∃ v : n → ℝ, v ≠ 0 ∧ B *ᵥ v = 0 ∧ ∀ i, r < (e i).val → v i = 0 := by
  classical
  let f : Fin (r + 1) → n := fun j => e.symm ⟨j.val, lt_of_lt_of_le j.isLt hr⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    simpa only [f, Equiv.apply_symm_apply] using congrArg (fun k => (e k).val) hij
  let J : Matrix n (Fin (r + 1)) ℝ := fun i j => if i = f j then 1 else 0
  have hJ (w : Fin (r + 1) → ℝ) (j : Fin (r + 1)) : (J *ᵥ w) (f j) = w j := by
    simp only [J, mulVec, dotProduct, hf.eq_iff, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hdim := (B * J).mulVecLin.finrank_range_add_finrank_ker
  have hCJ : (B * J).rank ≤ r := (Matrix.rank_mul_le_left B J).trans hB
  have hker : LinearMap.ker (B * J).mulVecLin ≠ ⊥ := by
    apply Submodule.one_le_finrank_iff.mp
    change (B * J).rank + Module.finrank ℝ (LinearMap.ker (B * J).mulVecLin) =
      Module.finrank ℝ (Fin (r + 1) → ℝ) at hdim
    rw [Module.finrank_pi, Fintype.card_fin] at hdim
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨J *ᵥ w, ?_, ?_, ?_⟩
  · intro hzero
    apply hw0
    funext j
    have h := congrFun hzero (f j)
    simpa only [hJ, Pi.zero_apply] using h
  · rw [mulVec_mulVec]
    exact hw
  · intro i hi
    change ∑ j, J i j * w j = 0
    apply Finset.sum_eq_zero
    intro j _
    have hij : i ≠ f j := by
      intro h
      have hv : (e i).val = j.val := by
        simpa only [f, Equiv.apply_symm_apply] using congrArg (fun k => (e k).val) h
      omega
    simp only [J, ite_eq_right hij, zero_mul]

private theorem norm_gram_diagonal (X : Matrix n n ℝ) (a : n → ℝ) :
    ‖X * (isHermitian_conjTranspose_mul_self X).eigenvectorUnitary * diagonal a‖ ^ 2 =
      ‖fun i => (isHermitian_conjTranspose_mul_self X).eigenvalues i * a i ^ 2‖ := by
  let Y := X * ((isHermitian_conjTranspose_mul_self X).eigenvectorUnitary : Matrix n n ℝ)
  have hgram : star (Y * diagonal a) * (Y * diagonal a) =
      diagonal (fun i => (isHermitian_conjTranspose_mul_self X).eigenvalues i * a i ^ 2) := by
    rw [StarMul.star_mul, ← Matrix.mul_assoc, Matrix.mul_assoc (star (diagonal a)),
      gram_diagonal]
    simp only [Matrix.star_eq_conjTranspose, diagonal_conjTranspose, star_trivial,
      diagonal_mul_diagonal]
    congr 1
    funext i
    ring
  rw [pow_two, ← CStarRing.norm_star_mul_self, hgram, Matrix.l2_opNorm_diagonal]

private theorem singularValueAt_sq (X : Matrix n n ℝ) {r : ℕ}
    (hr : r < Fintype.card n) :
    singularValueAt X r ^ 2 = (isHermitian_conjTranspose_mul_self X).eigenvalues₀ ⟨r, hr⟩ := by
  let e : n ≃ Fin (Fintype.card n) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
  have h := Matrix.eigenvalues_conjTranspose_mul_self_nonneg X (e.symm ⟨r, hr⟩)
  change 0 ≤ (isHermitian_conjTranspose_mul_self X).eigenvalues₀ (e (e.symm ⟨r, hr⟩)) at h
  rw [Equiv.apply_symm_apply] at h
  simpa only [singularValueAt, dite_eq_left hr, singularValues₀] using Real.sq_sqrt h

theorem singularValueAt_le_norm_sub (X R : Matrix n n ℝ) {r : ℕ}
    (hR : R.rank ≤ r) : singularValueAt X r ≤ ‖X - R‖ := by
  by_cases hr : r < Fintype.card n
  · let hG := isHermitian_conjTranspose_mul_self X
    let U := hG.eigenvectorUnitary
    let e : n ≃ Fin (Fintype.card n) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    obtain ⟨v, hv0, hvR, hv⟩ := exists_supported_kernel
      (R * (U : Matrix n n ℝ)) e r hr
      ((Matrix.rank_mul_le_left R (U : Matrix n n ℝ)).trans hR)
    have hvpos : 0 < v ⬝ᵥ v := by
      exact lt_of_le_of_ne (Finset.sum_nonneg fun i _ => mul_self_nonneg (v i))
        (fun h => hv0 (dotProduct_self_eq_zero.mp h.symm))
    have hlow : singularValueAt X r ^ 2 * (v ⬝ᵥ v) ≤
        ((X * (U : Matrix n n ℝ)) *ᵥ v) ⬝ᵥ ((X * (U : Matrix n n ℝ)) *ᵥ v) := by
      rw [dot_gram_coordinates, singularValueAt_sq X hr]
      simp only [dotProduct, Finset.mul_sum, ← pow_two]
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : r < (e i).val
      · simp only [hv i hi, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
      · exact mul_le_mul_of_nonneg_right
          (hG.eigenvalues₀_antitone (show e i ≤ ⟨r, hr⟩ from Nat.le_of_not_gt hi)) (sq_nonneg _)
    have hnorm := dot_mulVec_le ((X - R) * (U : Matrix n n ℝ)) v
    rw [CStarRing.norm_mul_coe_unitary, Matrix.sub_mul, Matrix.sub_mulVec, hvR, sub_zero] at hnorm
    exact (sq_le_sq₀ (singularValueAt_nonneg X r) (norm_nonneg _)).1
      ((mul_le_mul_iff_left₀ hvpos).1 (hlow.trans hnorm))
  · rw [singularValueAt_eq_zero X (Nat.le_of_not_gt hr)]
    exact norm_nonneg _

theorem exists_rank_approximation (X : Matrix n n ℝ) (r : ℕ) :
    ∃ R : Matrix n n ℝ, R.rank ≤ r ∧ ‖X - R‖ ≤ singularValueAt X r := by
  classical
  by_cases hr : r < Fintype.card n
  · let hG := isHermitian_conjTranspose_mul_self X
    let U := hG.eigenvectorUnitary
    let e : n ≃ Fin (Fintype.card n) := (Fintype.equivOfCardEq (Fintype.card_fin _)).symm
    let a : n → ℝ := fun i => if (e i).val < r then 1 else 0
    let b : n → ℝ := fun i => if (e i).val < r then 0 else 1
    have ha_rank : (diagonal a).rank ≤ r := by
      rw [Matrix.rank_diagonal]
      have ha (i : {i // a i ≠ 0}) : (e i.val).val < r := by
        by_contra hi
        exact i.prop (ite_eq_right hi)
      let f : {i // a i ≠ 0} → Fin r := fun i => ⟨(e i.val).val, ha i⟩
      have hf : Function.Injective f := by
        intro i j hij
        apply Subtype.ext
        apply e.injective
        apply Fin.ext
        exact congrArg (fun k : Fin r => k.val) hij
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hf
    refine ⟨X * (U : Matrix n n ℝ) * diagonal a * star (U : Matrix n n ℝ), ?_, ?_⟩
    · exact (Matrix.rank_mul_le_left _ _).trans
        ((Matrix.rank_mul_le_right _ _).trans ha_rank)
    · have hdiag : diagonal b = 1 - diagonal a := by
        rw [← diagonal_one, diagonal_sub]
        congr 1
        funext i
        dsimp [a, b]
        split <;> norm_num
      have hres : X - X * (U : Matrix n n ℝ) * diagonal a * star (U : Matrix n n ℝ) =
          X * (U : Matrix n n ℝ) * diagonal b * star (U : Matrix n n ℝ) := by
        have hU : X * (U : Matrix n n ℝ) * star (U : Matrix n n ℝ) = X := by
          rw [Matrix.mul_assoc, Unitary.mul_star_self_of_mem U.prop, mul_one]
        rw [hdiag, mul_sub, mul_one, sub_mul, hU]
      rw [hres, CStarRing.norm_mul_mem_unitary _ (Unitary.star_mem U.prop)]
      apply (sq_le_sq₀ (norm_nonneg _) (singularValueAt_nonneg X r)).1
      rw [norm_gram_diagonal, singularValueAt_sq X hr]
      apply (pi_norm_le_iff_of_nonneg ?_).2
      · intro i
        by_cases hi : (e i).val < r
        · simp only [b, ite_eq_left hi, zero_pow (by decide : 2 ≠ 0), mul_zero, norm_zero]
          rw [← singularValueAt_sq X hr]
          exact sq_nonneg _
        · simp only [b, ite_eq_right hi, one_pow, mul_one]
          rw [Real.norm_of_nonneg (Matrix.eigenvalues_conjTranspose_mul_self_nonneg X i)]
          exact hG.eigenvalues₀_antitone (show (⟨r, hr⟩ : Fin (Fintype.card n)) ≤ e i from
            Nat.le_of_not_gt hi)
      · rw [← singularValueAt_sq X hr]
        exact sq_nonneg _
  · refine ⟨X, (Matrix.rank_le_card_width X).trans (Nat.le_of_not_gt hr), ?_⟩
    rw [sub_self, norm_zero]
    exact singularValueAt_nonneg X r

end

end HCPolySupport.HighContrast.Analysis
end

section
/-!
## Singular moments and the Schatten norm

For a Hermitian matrix, the singular-value multiset is the absolute-value
eigenvalue multiset. The proof compares characteristic polynomials; it does
not assert that the two enumerations have the same order. The resulting
moment identity identifies the generic singular norm with the
Schatten norm on its intended Hermitian domain.
-/

namespace HCPolySupport.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The singular p-norm of an arbitrary real square matrix. Norm identities
below require a positive exponent; no norm interpretation is asserted at p=0. -/
@[expose]
def singularNorm (p : ℝ) (X : Matrix n n ℝ) : ℝ :=
  (∑ i, singularValues X i ^ p) ^ p⁻¹

theorem sum_eigenvalues_cfc {X : Matrix n n ℝ} (hX : X.IsHermitian)
    (f g : ℝ → ℝ) (hf : (cfc f X).IsHermitian) :
    ∑ i, g (hf.eigenvalues i) = ∑ i, g (f (hX.eigenvalues i)) := by
  have hroots : (cfc f X).charpoly.roots =
      Finset.univ.val.map (fun i => f (hX.eigenvalues i)) := by
    rw [hX.charpoly_cfc_eq]
    simpa only [Finset.prod, Multiset.map_map, Function.comp_def] using!
      (Polynomial.roots_multiset_prod_X_sub_C
        (Finset.univ.val.map (fun i => f (hX.eigenvalues i))))
  have h := congrArg (fun s : Multiset ℝ => (s.map g).sum)
    (hf.roots_charpoly_eq_eigenvalues.symm.trans hroots)
  simpa only [Multiset.map_map, Function.comp_def, Finset.sum] using! h

theorem sum_singularValues_eq_abs_eigenvalues {X : Matrix n n ℝ}
    (hX : X.IsHermitian) (f : ℝ → ℝ) :
    ∑ i, f (singularValues X i) = ∑ i, f |hX.eigenvalues i| := by
  have hGram : X.conjTranspose * X = cfc (fun x : ℝ => x ^ (2 : ℕ)) X := by
    calc
      X.conjTranspose * X = X ^ (2 : ℕ) := by rw [hX.eq, pow_two]
      _ = _ := (cfc_pow_id (R := ℝ) (a := X) (n := 2) (ha := hX)).symm
  have hG := Matrix.isHermitian_conjTranspose_mul_self X
  have hf : (cfc (fun x : ℝ => x ^ (2 : ℕ)) X).IsHermitian := hGram ▸ hG
  have h := sum_eigenvalues_cfc hX (fun x => x ^ (2 : ℕ)) (fun x => f (Real.sqrt x)) hf
  simp only [Real.sqrt_sq_eq_abs] at h
  rw [← h]
  unfold singularValues
  congr 1
  funext i
  congr 2
  exact congrFun ((hG.eigenvalues_eq_eigenvalues_iff hf).2
    (congrArg Matrix.charpoly hGram)) i

theorem singularNorm_nonneg (p : ℝ) (X : Matrix n n ℝ) : 0 ≤ singularNorm p X :=
  Real.rpow_nonneg (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (singularValues_nonneg X i) p) _

theorem singularNorm_rpow (X : Matrix n n ℝ) {p : ℝ} (hp : 0 < p) :
    singularNorm p X ^ p = ∑ i, singularValues X i ^ p := by
  exact Real.rpow_inv_rpow (Finset.sum_nonneg fun i _ =>
    Real.rpow_nonneg (singularValues_nonneg X i) p) hp.ne'

theorem singularNorm_eq_absSchattenNorm {d : ℕ} {A : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) {p : ℝ} (hp : 1 ≤ p) :
    singularNorm p (toFullBlockMat A) = absSchattenNorm p A := by
  have _hp := hp
  rw [singularNorm, sum_singularValues_eq_abs_eigenvalues hA (fun x => x ^ p),
    absSchattenNorm_eq_eigenvalues hA, schattenNormEigen]

end

end HCPolySupport.HighContrast.Analysis
end

section
/-!
## Tensor amplification of singular norms

Finite tensor products preserve matrix multiplication and multiply traces and
singular moments. All index types may be empty. In particular, the zeroth
tensor power is the identity on the singleton type `Fin 0 → n`.
-/

namespace HCPolySupport.HighContrast.Analysis

open scoped BigOperators Kronecker

noncomputable section

variable {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The tensor power on a function index type, including the scalar zeroth power. -/
@[expose]
def tensorPower (X : Matrix n n ℝ) (q : ℕ) :
    Matrix (Fin q → n) (Fin q → n) ℝ := fun i j => ∏ k, X (i k) (j k)

omit [DecidableEq n] in
theorem tensorPower_mul (X Y : Matrix n n ℝ) (q : ℕ) :
    tensorPower (X * Y) q = tensorPower X q * tensorPower Y q := by
  ext i j
  simp only [tensorPower, Matrix.mul_apply, ← Finset.prod_mul_distrib]
  exact Fintype.prod_sum (fun k a => X (i k) a * Y a (j k))

omit [Fintype n] in
private theorem tensorPower_diagonal (d : n → ℝ) (q : ℕ) :
    tensorPower (Matrix.diagonal d) q = Matrix.diagonal (fun i => ∏ k, d (i k)) := by
  ext i j
  by_cases h : i = j
  · subst j
    simp only [tensorPower, Matrix.diagonal_apply_eq]
  · obtain ⟨k, hk⟩ := Function.ne_iff.mp h
    rw [Matrix.diagonal_apply_ne _ h]
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    exact Matrix.diagonal_apply_ne _ hk

omit [Fintype n] in
theorem tensorPower_one (q : ℕ) :
    tensorPower (1 : Matrix n n ℝ) q = 1 := by
  rw [← Matrix.diagonal_one, tensorPower_diagonal]
  simp only [Finset.prod_const_one, Matrix.diagonal_one]

omit [DecidableEq n] in
theorem trace_tensorPower (X : Matrix n n ℝ) (q : ℕ) :
    Matrix.trace (tensorPower X q) = Matrix.trace X ^ q := by
  exact (Fintype.sum_pow (fun i => X i i) q).symm

omit [Fintype n] [DecidableEq n] in
private theorem tensorPower_star (X : Matrix n n ℝ) (q : ℕ) :
    tensorPower (star X) q = star (tensorPower X q) := by
  ext i j
  simp only [tensorPower, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply,
    star_trivial]

private theorem sum_singularValues_of_diagonalization (X U : Matrix n n ℝ)
    (d : n → ℝ) (hU : star U * U = 1)
    (hX : star X * X = U * Matrix.diagonal d * star U) (f : ℝ → ℝ) :
    ∑ i, f (singularValues X i) = ∑ i, f (Real.sqrt (d i)) := by
  have hchar : (star X * X).charpoly = (Matrix.diagonal d).charpoly := by
    rw [hX, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU, one_mul]
  have hroots : (star X * X).charpoly.roots = Finset.univ.val.map d := by
    rw [hchar, Matrix.charpoly_diagonal]
    simpa only [Finset.prod, Multiset.map_map, Function.comp_def] using
      (Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map d))
  have h := congrArg (fun s : Multiset ℝ => (s.map (fun x => f (Real.sqrt x))).sum)
    ((Matrix.isHermitian_conjTranspose_mul_self X).roots_charpoly_eq_eigenvalues.symm.trans
      hroots)
  simpa only [singularValues, Multiset.map_map, Function.comp_def, Finset.sum,
    RCLike.ofReal_real_eq_id, id_eq] using h

private theorem gram_diagonalization (X : Matrix n n ℝ) :
    star X * X =
      (Matrix.isHermitian_conjTranspose_mul_self X).eigenvectorUnitary *
        Matrix.diagonal (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues *
          star ((Matrix.isHermitian_conjTranspose_mul_self X).eigenvectorUnitary :
            Matrix n n ℝ) := by
  simpa only [Unitary.conjStarAlgAut_apply, RCLike.ofReal_real_eq_id,
    Function.id_comp] using! (Matrix.isHermitian_conjTranspose_mul_self X).spectral_theorem

theorem singularNorm_tensorPower (X : Matrix n n ℝ) {p : ℝ} (hp : 0 < p)
    (q : ℕ) : singularNorm p (tensorPower X q) = singularNorm p X ^ q := by
  let U : Matrix n n ℝ := (Matrix.isHermitian_conjTranspose_mul_self X).eigenvectorUnitary
  let d := (Matrix.isHermitian_conjTranspose_mul_self X).eigenvalues
  have hU : star U * U = 1 := Unitary.coe_star_mul_self _
  have hT : star (tensorPower U q) * tensorPower U q = 1 := by
    rw [← tensorPower_star, ← tensorPower_mul, hU, tensorPower_one]
  have hG : star (tensorPower X q) * tensorPower X q =
      tensorPower U q * Matrix.diagonal (fun i => ∏ k, d (i k)) *
        star (tensorPower U q) := by
    rw [← tensorPower_star, ← tensorPower_mul, gram_diagonalization X,
      tensorPower_mul, tensorPower_mul, tensorPower_diagonal, tensorPower_star]
  apply (Real.rpow_left_inj (singularNorm_nonneg _ _)
    (pow_nonneg (singularNorm_nonneg _ _) q) hp.ne').mp
  rw [singularNorm_rpow _ hp, ← Real.rpow_pow_comm (singularNorm_nonneg _ _),
    singularNorm_rpow _ hp]
  rw [sum_singularValues_of_diagonalization (tensorPower X q) (tensorPower U q) _ hT hG
    (fun x => x ^ p)]
  have hsqrt (i : Fin q → n) : Real.sqrt (∏ k, d (i k)) =
      ∏ k, singularValues X (i k) := by
    simp only [singularValues, Real.sqrt_eq_rpow]
    exact (Real.finsetProd_rpow _ _
      (fun k _ => Matrix.eigenvalues_conjTranspose_mul_self_nonneg X (i k)) _).symm
  simp_rw [hsqrt, ← Real.finsetProd_rpow _ _
    (fun k _ => singularValues_nonneg X _) p]
  exact (Fintype.sum_pow (fun i => singularValues X i ^ p) q).symm

theorem tensorPower_prod {N : ℕ} (A : Fin N → Matrix n n ℝ) (q : ℕ) :
    tensorPower ((List.ofFn A).prod) q = (List.ofFn fun k => tensorPower (A k) q).prod := by
  let F : Matrix n n ℝ →* Matrix (Fin q → n) (Fin q → n) ℝ :=
    { toFun := fun X => tensorPower X q
      map_one' := tensorPower_one q
      map_mul' := fun X Y => tensorPower_mul X Y q }
  simpa only [List.map_ofFn, Function.comp_def] using! ((List.ofFn A).prod_hom F).symm

end

end HCPolySupport.HighContrast.Analysis
end
