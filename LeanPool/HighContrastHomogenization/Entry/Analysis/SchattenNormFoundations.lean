/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Setup.SchattenNorm
public import LeanPool.HighContrastHomogenization.Support.Ambient.BlockMatrix
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# High-contrast homogenization: Entry.Analysis.SchattenNormFoundations

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schatten Norm Foundations

The deterministic Schatten norm: its spectral formula, the diagonal Hölder bound in an
orthogonal basis, and the triangle inequality.  These deterministic estimates serve the
finite-range matrix averaging lemma `l.fixed.geometry.matrix.averaging`, through the
even trace-power identity and the spectral formula, and the positive-gap lemma
`l.fixed.geometry.positive.gap`, through the trace and operator-norm comparisons and the
triangle inequality.
-/

section
/-!
## Spectral facts for the Schatten norm

This file discharges the deterministic spectral bridge for the real-valued
Schatten norm of `HCPoly/Entry/Setup/SchattenNorm.lean`.
-/

open HCPolySupport.HighContrast (blockTrace)
namespace HCPolySupport.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

theorem toFullBlockMat_isHermitian_iff (H : BlockMat d) :
    (toFullBlockMat H).IsHermitian ↔ IsSymmetricBlockMat H := by
  constructor
  · intro hH α β
    have h := congrFun (congrFun hH.eq β) α
    cases α <;> cases β <;>
      simpa [toFullBlockMat, blockMatEntry, Matrix.conjTranspose, starRingEnd_apply] using h
  · intro hH
    change Matrix.conjTranspose (toFullBlockMat H) = toFullBlockMat H
    ext α β
    cases α with
    | inl i =>
        cases β with
        | inl j =>
            simpa [toFullBlockMat, blockMatEntry, Matrix.conjTranspose, starRingEnd_apply]
              using (hH (Sum.inl i) (Sum.inl j)).symm
        | inr j =>
            simpa [toFullBlockMat, blockMatEntry, Matrix.conjTranspose, starRingEnd_apply]
              using (hH (Sum.inl i) (Sum.inr j)).symm
    | inr i =>
        cases β with
        | inl j =>
            simpa [toFullBlockMat, blockMatEntry, Matrix.conjTranspose, starRingEnd_apply]
              using (hH (Sum.inr i) (Sum.inl j)).symm
        | inr j =>
            simpa [toFullBlockMat, blockMatEntry, Matrix.conjTranspose, starRingEnd_apply]
              using (hH (Sum.inr i) (Sum.inr j)).symm

private theorem trace_cfc_eq_sum {H : BlockMat d} (hH : (toFullBlockMat H).IsHermitian)
    (f : ℝ → ℝ) :
    Matrix.trace (cfc f (toFullBlockMat H)) = ∑ i, f (hH.eigenvalues i) := by
  rw [hH.cfc_eq f, Matrix.IsHermitian.cfc, Unitary.conjStarAlgAut_apply,
    Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  rfl

theorem trace_cfc_abs_rpow_eq_sum {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (_hN : 1 ≤ N) :
    Matrix.trace (cfc (fun x : ℝ => |x| ^ N) (toFullBlockMat H)) =
      ∑ i, |hH.eigenvalues i| ^ N := by
  exact trace_cfc_eq_sum hH (fun x : ℝ => |x| ^ N)

theorem absSchattenNorm_eq_eigenvalues {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} :
    absSchattenNorm N H = schattenNormEigen hH N := by
  unfold absSchattenNorm schattenNormEigen
  rw [trace_cfc_eq_sum hH (fun x : ℝ => |x| ^ N)]

private theorem eigenvalue_abs_rpow_sum_nonneg {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) (N : ℝ) :
    0 ≤ ∑ i, |hH.eigenvalues i| ^ N :=
  Finset.sum_nonneg fun _ _ => Real.rpow_nonneg (abs_nonneg _) N

theorem absSchattenNorm_nonneg {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (_hN : 1 ≤ N) :
    0 ≤ absSchattenNorm N H := by
  rw [absSchattenNorm_eq_eigenvalues hH, schattenNormEigen]
  exact Real.rpow_nonneg (eigenvalue_abs_rpow_sum_nonneg hH N) N⁻¹

theorem absSchattenNorm_rpow_eq_sum {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N H ^ N = ∑ i, |hH.eigenvalues i| ^ N := by
  rw [absSchattenNorm_eq_eigenvalues hH, schattenNormEigen]
  exact Real.rpow_inv_rpow (eigenvalue_abs_rpow_sum_nonneg hH N)
    (ne_of_gt (lt_of_lt_of_le zero_lt_one hN))

private theorem abs_pow_even_two_mul (x : ℝ) (k : ℕ) :
    |x| ^ (2 * k : ℕ) = x ^ (2 * k : ℕ) := by
  by_cases hx : 0 ≤ x
  · simp [abs_of_nonneg hx]
  · have hxlt : x < 0 := lt_of_not_ge hx
    have heven : Even (2 * k) := ⟨k, by omega⟩
    rw [abs_of_neg hxlt, heven.neg_pow]

theorem absSchattenNorm_even_pow_eq_trace {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) (k : ℕ) (hk : 1 ≤ k) :
    absSchattenNorm (2 * (k : ℝ)) H ^ (2 * k) =
      Matrix.trace ((toFullBlockMat H) ^ (2 * k)) := by
  have hcast : ((2 * k : ℕ) : ℝ) = 2 * (k : ℝ) := by norm_num
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hparam : (1 : ℝ) ≤ 2 * (k : ℝ) := by linarith only [hkR]
  calc
    absSchattenNorm (2 * (k : ℝ)) H ^ (2 * k)
        = absSchattenNorm (2 * (k : ℝ)) H ^ (2 * (k : ℝ)) := by
            rw [← Real.rpow_natCast, hcast]
    _ = ∑ i, |hH.eigenvalues i| ^ (2 * (k : ℝ)) :=
        absSchattenNorm_rpow_eq_sum hH hparam
    _ = ∑ i, hH.eigenvalues i ^ (2 * k : ℕ) := by
        apply Finset.sum_congr rfl
        intro i _hi
        rw [← hcast, Real.rpow_natCast, abs_pow_even_two_mul]
    _ = Matrix.trace ((toFullBlockMat H) ^ (2 * k)) := by
        rw [← trace_cfc_eq_sum hH (fun x : ℝ => x ^ (2 * k : ℕ))]
        exact congrArg Matrix.trace
          (cfc_pow_id (R := ℝ) (a := toFullBlockMat H) (n := 2 * k) (ha := hH))

theorem blockTrace_nonneg {H : BlockMat d} (hH : (toFullBlockMat H).PosSemidef) :
    0 ≤ blockTrace H := by
  unfold blockTrace
  exact hH.trace_nonneg

private theorem finite_rpow_sum_le_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) {N : ℝ} (hN : 1 ≤ N) (hf : ∀ i ∈ s, 0 ≤ f i) :
    (∑ i ∈ s, f i ^ N) ^ (1 / N) ≤ ∑ i ∈ s, f i := by
  classical
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNne : N ≠ 0 := hNpos.ne'
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, Real.zero_rpow (one_div_ne_zero hNne)]
  | insert a s has ih =>
      have hfa : 0 ≤ f a := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, 0 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hsumPow : 0 ≤ ∑ i ∈ s, f i ^ N :=
        Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hfs i hi) N
      have hroot : 0 ≤ (∑ i ∈ s, f i ^ N) ^ (1 / N) :=
        Real.rpow_nonneg hsumPow (1 / N)
      have hroot_pow :
          ((∑ i ∈ s, f i ^ N) ^ (1 / N)) ^ N = ∑ i ∈ s, f i ^ N := by
        rw [one_div]
        exact Real.rpow_inv_rpow hsumPow hNne
      rw [Finset.sum_insert has, Finset.sum_insert has]
      calc
        (f a ^ N + ∑ i ∈ s, f i ^ N) ^ (1 / N)
            = (f a ^ N + ((∑ i ∈ s, f i ^ N) ^ (1 / N)) ^ N) ^ (1 / N) := by
                rw [hroot_pow]
        _ ≤ f a + (∑ i ∈ s, f i ^ N) ^ (1 / N) :=
            Real.rpow_add_rpow_le_add hfa hroot hN
        _ ≤ f a + ∑ i ∈ s, f i := by
            simpa [add_comm, add_left_comm, add_assoc] using add_le_add_left (ih hfs) (f a)

private theorem finite_abs_rpow_sum_le_abs_sum {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) {N : ℝ} (hN : 1 ≤ N) :
    (∑ i ∈ s, |f i| ^ N) ^ N⁻¹ ≤ ∑ i ∈ s, |f i| := by
  rw [← one_div]
  exact finite_rpow_sum_le_sum s (fun i => |f i|) hN fun i _ => abs_nonneg (f i)

private theorem l2_opNorm_conjStarAlgAut {n : Type*} [Fintype n] [DecidableEq n]
    (U : unitary (Matrix n n ℝ)) (A : Matrix n n ℝ) :
    ‖(Unitary.conjStarAlgAut ℝ _ U) A‖ = ‖A‖ := by
  rw [Unitary.conjStarAlgAut_apply]
  rw [CStarRing.norm_mul_mem_unitary
    (A := (U : Matrix n n ℝ) * A) (hU := Unitary.star_mem U.prop)]
  exact CStarRing.norm_mem_unitary_mul A U.prop

private theorem hermitian_l2_opNorm_eq_eigenvalue_norm {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) :
    ‖toFullBlockMat H‖ = ‖hH.eigenvalues‖ := by
  conv_lhs => rw [hH.spectral_theorem]
  rw [l2_opNorm_conjStarAlgAut]
  simp

private theorem abs_eigenvalue_le_l2_opNorm {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) (i : BlockCoord d) :
    |hH.eigenvalues i| ≤ ‖toFullBlockMat H‖ := by
  rw [hermitian_l2_opNorm_eq_eigenvalue_norm hH]
  simpa [Real.norm_eq_abs] using norm_le_pi_norm hH.eigenvalues i

private theorem abs_eigenvalue_le_absSchattenNorm {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (hN : 1 ≤ N) (i : BlockCoord d) :
    |hH.eigenvalues i| ≤ absSchattenNorm N H := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hNne : N ≠ 0 := (ne_of_lt hNpos).symm
  have hterm_nonneg : 0 ≤ |hH.eigenvalues i| ^ N :=
    Real.rpow_nonneg (abs_nonneg _) N
  have hterm_le_sum :
      |hH.eigenvalues i| ^ N ≤ ∑ j : BlockCoord d, |hH.eigenvalues j| ^ N :=
    Finset.single_le_sum (fun _ _ => Real.rpow_nonneg (abs_nonneg _) N) (Finset.mem_univ i)
  have hinv_nonneg : 0 ≤ 1 / N := by positivity
  calc
    |hH.eigenvalues i| = (|hH.eigenvalues i| ^ N) ^ (1 / N) := by
      rw [one_div, ← Real.rpow_mul (abs_nonneg (hH.eigenvalues i)) N N⁻¹,
        mul_inv_cancel₀ hNne, Real.rpow_one]
    _ ≤ (∑ j : BlockCoord d, |hH.eigenvalues j| ^ N) ^ (1 / N) :=
      Real.rpow_le_rpow hterm_nonneg hterm_le_sum hinv_nonneg
    _ = schattenNormEigen hH N := by
      unfold schattenNormEigen
      rw [one_div]
    _ = absSchattenNorm N H := (absSchattenNorm_eq_eigenvalues hH).symm

theorem absSchattenNorm_one_eq_blockTrace {H : BlockMat d}
    (hH : (toFullBlockMat H).PosSemidef) : absSchattenNorm 1 H = blockTrace H := by
  let hHerm := hH.isHermitian
  calc
    absSchattenNorm 1 H = schattenNormEigen hHerm 1 :=
      absSchattenNorm_eq_eigenvalues hHerm
    _ = blockTrace H := by
      unfold schattenNormEigen blockTrace
      rw [inv_one, Real.rpow_one, hHerm.trace_eq_sum_eigenvalues]
      have hEigNonneg : 0 ≤ hHerm.eigenvalues :=
        hHerm.posSemidef_iff_eigenvalues_nonneg.mp hH
      apply Finset.sum_congr rfl
      intro i _hi
      simpa using (abs_of_nonneg (hEigNonneg i))

theorem absSchattenNorm_le_blockTrace {H : BlockMat d}
    (hH : (toFullBlockMat H).PosSemidef) {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N H ≤ blockTrace H := by
  let hHerm := hH.isHermitian
  calc
    absSchattenNorm N H = schattenNormEigen hHerm N :=
      absSchattenNorm_eq_eigenvalues hHerm
    _ ≤ ∑ i : BlockCoord d, |hHerm.eigenvalues i| := by
      unfold schattenNormEigen
      exact finite_abs_rpow_sum_le_abs_sum Finset.univ hHerm.eigenvalues hN
    _ = blockTrace H := by
      unfold blockTrace
      rw [hHerm.trace_eq_sum_eigenvalues]
      have hEigNonneg : 0 ≤ hHerm.eigenvalues :=
        hHerm.posSemidef_iff_eigenvalues_nonneg.mp hH
      apply Finset.sum_congr rfl
      intro i _hi
      exact abs_of_nonneg (hEigNonneg i)

theorem blockOpNorm_le_absSchattenNorm {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (hN : 1 ≤ N) :
    blockOpNorm H ≤ absSchattenNorm N H := by
  unfold blockOpNorm
  rw [hermitian_l2_opNorm_eq_eigenvalue_norm hH]
  refine (pi_norm_le_iff_of_nonneg (absSchattenNorm_nonneg hH hN)).mpr ?_
  intro i
  simpa [Real.norm_eq_abs] using abs_eigenvalue_le_absSchattenNorm hH hN i

theorem blockTrace_le_dim_mul_blockOpNorm {H : BlockMat d}
    (hH : (toFullBlockMat H).PosSemidef) :
    blockTrace H ≤ (2 * (d : ℝ)) * blockOpNorm H := by
  let hHerm := hH.isHermitian
  have hEigNonneg : 0 ≤ hHerm.eigenvalues :=
    hHerm.posSemidef_iff_eigenvalues_nonneg.mp hH
  calc
    blockTrace H = ∑ i : BlockCoord d, hHerm.eigenvalues i := by
      unfold blockTrace
      rw [hHerm.trace_eq_sum_eigenvalues]
      rfl
    _ ≤ ∑ _i : BlockCoord d, blockOpNorm H := by
      apply Finset.sum_le_sum
      intro i _hi
      exact (le_abs_self (hHerm.eigenvalues i)).trans
        (by simpa [blockOpNorm] using abs_eigenvalue_le_l2_opNorm hHerm i)
    _ = (Fintype.card (BlockCoord d) : ℝ) * blockOpNorm H := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = (2 * (d : ℝ)) * blockOpNorm H := by
      have hcard : (Fintype.card (BlockCoord d) : ℝ) = 2 * (d : ℝ) := by
        simp only [BlockCoord, Fintype.card_sum, Fintype.card_fin]
        rw [Nat.cast_add]
        ring
      rw [hcard]

end

end HCPolySupport.HighContrast.Analysis
end

section
/-!
## Diagonal estimates in orthogonal bases

Squared entries of a real unitary matrix have row and column sums one. Weighted
scalar Hölder therefore bounds the diagonal in any orthogonal basis by the
spectral Schatten value. No commutation of the matrices is used.
-/

namespace HCPolySupport.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem unitary_sum_sq_row (U : unitary (Matrix n n ℝ)) (i : n) :
    ∑ j, (U : Matrix n n ℝ) i j ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix n n ℝ => M i i) (Unitary.coe_mul_star_self U)
  simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply_eq,
    pow_two] using! h

theorem unitary_sum_sq_col (U : unitary (Matrix n n ℝ)) (j : n) :
    ∑ i, (U : Matrix n n ℝ) i j ^ 2 = 1 := by
  have h := congrArg (fun M : Matrix n n ℝ => M j j) (Unitary.coe_star_mul_self U)
  simpa only [Matrix.mul_apply, Matrix.star_apply, star_trivial, Matrix.one_apply_eq,
    pow_two] using h

theorem unitary_conj_diagonal_apply (U : unitary (Matrix n n ℝ)) (f : n → ℝ) (i : n) :
    (Unitary.conjStarAlgAut ℝ _ U (Matrix.diagonal f)) i i =
      ∑ j, (U : Matrix n n ℝ) i j ^ 2 * f j := by
  rw [Unitary.conjStarAlgAut_apply, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.star_apply, star_trivial]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem hermitian_conj_diagonal_eq {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℝ)) (i : n) :
    (Unitary.conjStarAlgAut ℝ _ U A) i i =
      ∑ j, ((U * hA.eigenvectorUnitary : unitary (Matrix n n ℝ)) : Matrix n n ℝ) i j ^ 2 *
        hA.eigenvalues j := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [← Unitary.conjStarAlgAut_mul_apply]
  exact unitary_conj_diagonal_apply _ _ i

theorem hermitian_norm_eq_eigenvalue_norm {A : Matrix n n ℝ} (hA : A.IsHermitian) :
    ‖A‖ = ‖hA.eigenvalues‖ := by
  conv_lhs => rw [hA.spectral_theorem]
  rw [Unitary.conjStarAlgAut_apply,
    CStarRing.norm_mul_mem_unitary (hU := Unitary.star_mem hA.eigenvectorUnitary.prop),
    CStarRing.norm_mem_unitary_mul _ hA.eigenvectorUnitary.prop]
  change ‖Matrix.diagonal hA.eigenvalues‖ = ‖hA.eigenvalues‖
  exact Matrix.l2_opNorm_diagonal _

theorem hermitian_conj_diagonal_le_norm {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℝ)) (i : n) :
    (Unitary.conjStarAlgAut ℝ _ U A) i i ≤ ‖A‖ := by
  rw [hermitian_conj_diagonal_eq hA U i, hermitian_norm_eq_eigenvalue_norm hA]
  calc
    _ ≤ ∑ j, ((U * hA.eigenvectorUnitary : unitary (Matrix n n ℝ)) : Matrix n n ℝ) i j ^ 2 *
        ‖hA.eigenvalues‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
          (norm_le_pi_norm hA.eigenvalues j))) (sq_nonneg _)
    _ = ‖hA.eigenvalues‖ := by
      rw [← Finset.sum_mul, unitary_sum_sq_row, one_mul]

theorem unitary_diagonal_rpow_le (U : unitary (Matrix n n ℝ)) (f : n → ℝ)
    {N : ℝ} (hN : 1 ≤ N) (i : n) :
    |∑ j, (U : Matrix n n ℝ) i j ^ 2 * f j| ^ N ≤
      ∑ j, (U : Matrix n n ℝ) i j ^ 2 * |f j| ^ N := by
  have hNpos : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have habs : |∑ j, (U : Matrix n n ℝ) i j ^ 2 * f j| ≤
      ∑ j, (U : Matrix n n ℝ) i j ^ 2 * |f j| := by
    calc
      _ ≤ ∑ j, |(U : Matrix n n ℝ) i j ^ 2 * f j| := Finset.abs_sum_le_sum_abs _ _
      _ = _ := by simp only [abs_mul, abs_pow, sq_abs]
  have hh := Real.inner_le_weight_mul_Lp_of_nonneg Finset.univ hN
    (fun j => (U : Matrix n n ℝ) i j ^ 2) (fun j => |f j|)
    (fun _ => sq_nonneg _) (fun _ => abs_nonneg _)
  rw [unitary_sum_sq_row, Real.one_rpow, one_mul] at hh
  have hr := Real.rpow_le_rpow (abs_nonneg _) (habs.trans hh) hNpos.le
  rwa [Real.rpow_inv_rpow (Finset.sum_nonneg (fun j _ =>
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (abs_nonneg _) _))) hNpos.ne'] at hr

theorem hermitian_sum_diagonal_rpow_le {A : Matrix n n ℝ} (hA : A.IsHermitian)
    (U : unitary (Matrix n n ℝ)) {N : ℝ} (hN : 1 ≤ N) :
    ∑ i, |(Unitary.conjStarAlgAut ℝ _ U A) i i| ^ N ≤
      ∑ j, |hA.eigenvalues j| ^ N := by
  calc
    _ ≤ ∑ i, ∑ j,
        ((U * hA.eigenvectorUnitary : unitary (Matrix n n ℝ)) : Matrix n n ℝ) i j ^ 2 *
          |hA.eigenvalues j| ^ N := by
      apply Finset.sum_le_sum
      intro i _
      rw [hermitian_conj_diagonal_eq]
      exact unitary_diagonal_rpow_le _ _ hN i
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, unitary_sum_sq_col, one_mul]

end

end HCPolySupport.HighContrast.Analysis
end

section
/-!
## The Schatten triangle inequality for symmetric real blocks

Diagonalize the sum, apply scalar Minkowski to its diagonal entries, and bound
the diagonal of each summand by weighted Hölder. This proves coefficient one
for noncommuting signed symmetric matrices and every real exponent `N ≥ 1`.
-/

open HCPolySupport.HighContrast (blockSub)
namespace HCPolySupport.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {d : ℕ}

private theorem absSchattenNorm_diagonal_root_le {A : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (U : unitary (FullBlockMat d))
    {N : ℝ} (hN : 1 ≤ N) :
    (∑ i, |(Unitary.conjStarAlgAut ℝ _ U (toFullBlockMat A)) i i| ^ N) ^ N⁻¹ ≤
      absSchattenNorm N A := by
  rw [absSchattenNorm_eq_eigenvalues hA, schattenNormEigen]
  exact Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ =>
    Real.rpow_nonneg (abs_nonneg _) _)) (hermitian_sum_diagonal_rpow_le hA U hN)
    (inv_nonneg.mpr (le_trans zero_le_one hN))

/-- Full triangle inequality, including the trace-norm endpoint and empty blocks. -/
theorem absSchattenNorm_add_le {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N (ofFullBlockMat (toFullBlockMat A + toFullBlockMat B)) ≤
      absSchattenNorm N A + absSchattenNorm N B := by
  let U := star (hA.add hB).eigenvectorUnitary
  let T := Unitary.conjStarAlgAut ℝ (FullBlockMat d) U
  have heq (i : BlockCoord d) :
      (hA.add hB).eigenvalues i =
        T (toFullBlockMat A) i i + T (toFullBlockMat B) i i := by
    have hh := congrArg (fun M : FullBlockMat d => M i i)
      (hA.add hB).conjStarAlgAut_star_eigenvectorUnitary
    change T (toFullBlockMat A + toFullBlockMat B) i i = _ at hh
    rw [map_add] at hh
    simpa only [Matrix.diagonal_apply_eq, Matrix.add_apply, Function.comp_apply,
      RCLike.ofReal_real_eq_id, id_eq] using hh.symm
  have hsum : absSchattenNorm N (ofFullBlockMat (toFullBlockMat A + toFullBlockMat B)) =
      (∑ i, |T (toFullBlockMat A) i i + T (toFullBlockMat B) i i| ^ N) ^ N⁻¹ := by
    have hAB : (toFullBlockMat (ofFullBlockMat (toFullBlockMat A + toFullBlockMat
      B))).IsHermitian := by
      simpa only [toFullBlockMat_ofFullBlockMat] using hA.add hB
    rw [absSchattenNorm_eq_eigenvalues hAB, schattenNormEigen]
    simp only [toFullBlockMat_ofFullBlockMat]
    change (∑ i, |(hA.add hB).eigenvalues i| ^ N) ^ N⁻¹ = _
    simp only [heq]
  rw [hsum]
  calc
    _ ≤ (∑ i, |T (toFullBlockMat A) i i| ^ N) ^ N⁻¹ +
        (∑ i, |T (toFullBlockMat B) i i| ^ N) ^ N⁻¹ := by
      simpa only [one_div] using Real.Lp_add_le Finset.univ
        (fun i => T (toFullBlockMat A) i i) (fun i => T (toFullBlockMat B) i i) hN
    _ ≤ _ := add_le_add (absSchattenNorm_diagonal_root_le hA U hN)
      (absSchattenNorm_diagonal_root_le hB U hN)

/-- Invariance under negation, obtained by applying the diagonal estimate twice. -/
theorem absSchattenNorm_neg {A : BlockMat d} (hA : (toFullBlockMat A).IsHermitian)
    {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N (ofFullBlockMat (-toFullBlockMat A)) = absSchattenNorm N A := by
  have hneg : (toFullBlockMat (ofFullBlockMat (-toFullBlockMat A))).IsHermitian := by
    simpa only [toFullBlockMat_ofFullBlockMat] using hA.neg
  have aux {B : BlockMat d} (hB : (toFullBlockMat B).IsHermitian) :
      absSchattenNorm N (ofFullBlockMat (-toFullBlockMat B)) ≤ absSchattenNorm N B := by
    let hn : (-toFullBlockMat B).IsHermitian := hB.neg
    let U := star hn.eigenvectorUnitary
    have hh := absSchattenNorm_diagonal_root_le hB U hN
    have heq (i : BlockCoord d) :
        |(Unitary.conjStarAlgAut ℝ _ U (toFullBlockMat B)) i i| = |hn.eigenvalues i| := by
      have he := congrArg (fun M : FullBlockMat d => M i i)
        hn.conjStarAlgAut_star_eigenvectorUnitary
      rw [map_neg] at he
      simp only [Matrix.neg_apply, Matrix.diagonal_apply_eq, Function.comp_apply,
        RCLike.ofReal_real_eq_id, id_eq] at he
      rw [← he, abs_neg]
    simp only [heq] at hh
    have hn' : (toFullBlockMat (ofFullBlockMat (-toFullBlockMat B))).IsHermitian := by
      simpa only [toFullBlockMat_ofFullBlockMat] using hn
    rw [absSchattenNorm_eq_eigenvalues hn', schattenNormEigen]
    simpa only [toFullBlockMat_ofFullBlockMat] using hh
  apply le_antisymm (aux hA)
  simpa only [toFullBlockMat_ofFullBlockMat, neg_neg, ofFullBlockMat_toFullBlockMat] using aux hneg

/-- Subtraction form consumed by the centering step. -/
theorem absSchattenNorm_sub_le {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N (blockSub A B) ≤ absSchattenNorm N A + absSchattenNorm N B := by
  have hn : (toFullBlockMat (ofFullBlockMat (-toFullBlockMat B))).IsHermitian := by
    simpa only [toFullBlockMat_ofFullBlockMat] using hB.neg
  have hh := absSchattenNorm_add_le hA hn hN
  rw [absSchattenNorm_neg hB hN, toFullBlockMat_ofFullBlockMat, ← sub_eq_add_neg] at hh
  have heq : blockSub A B = ofFullBlockMat (toFullBlockMat A - toFullBlockMat B) := by
    cases A
    cases B
    rfl
  rwa [heq]

end

end HCPolySupport.HighContrast.Analysis
end
