/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Geometry.PositiveSqrtCongruence
public import LeanPool.HighContrastHomogenization.Entry.Setup.Profile
public import LeanPool.HighContrastHomogenization.Provider.Recurrence.DetTransport
public import Mathlib.Tactic

/-!
# High-contrast homogenization: Entry.Multiscale.DriftAdvance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Drift Advance

The identities of the diagonal profile and the finite-sum algebra of the determinant drift
they advance.  At equal generations the profile is the printed prefactor times the history,
and it equals the history once the terminal mean is positive definite; the drift algebra
splits the printed determinant drift at an intermediate generation, telescopes the
log-determinant loss, and bounds one synchronized step of the drift by the terminal loss
increment.  These deterministic finite-sum facts are the drift-advance input to
`p.fixed.geometry.one.grid.propagation`.
-/

section
/-!
## Diagonal profile identities

This file contains only the deterministic finite-sum and normalization algebra needed at
the diagonal `m = n`.  The positivity assumption is kept exactly where the total
normalization needs it.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean blockSub blockTrace matSqrt matSqrt_spec
  normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-- The inverse square root is positive definite on every finite real matrix carrier. -/
theorem matSqrt_inv_posDef_full {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : Matrix ι ι ℝ} (hm : m.PosDef) : (matSqrt m⁻¹).PosDef := by
  rw [matSqrt_eq_cfc_sqrt hm.inv.posSemidef]
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (IsStrictlyPositive.sqrt m⁻¹ hm.inv.isStrictlyPositive)

private theorem ofFullBlockMat_one_eq_blockIdentity {d : ℕ} :
    ofFullBlockMat (1 : FullBlockMat d) = Book.Ch02.blockIdentity d := by
  rw [← ofFullBlockMat_toFullBlockMat (Book.Ch02.blockIdentity d)]
  congr
  funext α β
  cases α <;> cases β <;>
    simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]

private theorem blockTrace_blockSub_identity_self {d : ℕ} :
    blockTrace (blockSub (Book.Ch02.blockIdentity d) (Book.Ch02.blockIdentity d)) = 0 := by
  unfold blockTrace
  have hzero :
      toFullBlockMat (blockSub (Book.Ch02.blockIdentity d) (Book.Ch02.blockIdentity d)) =
        (0 : FullBlockMat d) := by
    funext α β
    cases α <;> cases β <;> simp [blockSub, toFullBlockMat]
  rw [hzero, Matrix.trace_zero]

/-- Normalizing a positive definite block by itself gives the doubled identity. -/
theorem normalizedBlock_self_of_posDef
    {d : ℕ} (F : BlockMat d) (hF : (toFullBlockMat F).PosDef) :
    normalizedBlock F F = Book.Ch02.blockIdentity d := by
  unfold normalizedBlock
  rw [matSqrt_inv_conj hF]
  exact ofFullBlockMat_one_eq_blockIdentity

/-- The mean penalty of the identity is zero, for every natural moment including `0`. -/
theorem meanPenalty_identity
    {d : ℕ} (Q : ℕ) :
    meanPenalty Q (Book.Ch02.blockIdentity d) = 0 := by
  simp [meanPenalty, blockTrace_blockSub_identity_self]

/-- At the diagonal, the profile is exactly the printed prefactor times the history. -/
theorem profile_self_eq_factor_mul_history
    {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ) (n : ℤ) :
    profile P γ q jStar n n =
    (1 + meanPenalty (bigQ d γ) (relMean P q n n)) * history P γ q jStar n := by
  unfold profile meanHistory
  simp

/-- With a positive terminal mean, the diagonal normalized mean is the identity. -/
theorem profile_self_of_posDef
    {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ) (n : ℤ)
    (hF : (toFullBlockMat (adaptedMean P q n)).PosDef) :
    profile P γ q jStar n n = history P γ q jStar n := by
  rw [profile_self_eq_factor_mul_history]
  simp [relMean, normalizedBlock_self_of_posDef (adaptedMean P q n) hF,
    meanPenalty_identity]

end

end HCPolySupport.HighContrast.Multiscale
end

section
/-!
## Determinant drift algebra

Spectral trace/determinant bounds, positive matrix normalization, and the finite-sum
algebra for the printed determinant drift.  The matrix-family hypotheses are deterministic
support inputs; their annealed proofs are the mean order of
`p.fixed.geometry.parent.child.recurrence`.
-/

open HCPolySupport.HighContrast (CoeffSpace adaptedMean blockLogDet blockSub blockTrace matSqrt
  matSqrt_spec normalizedBlock)
namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder

noncomputable section

/-- Split the printed drift sum at an intermediate generation `m`. -/
theorem determinantDrift_split
    {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (q : Mat d) (jStar : ℕ) (m L : ℤ)
    (hm : (jStar : ℤ) ≤ m) (hL : 0 ≤ L) :
    determinantDrift P γ q jStar (m + L) =
    (∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
      (3 : ℝ) ^ (-((1 - γ) / 8) * (((m + L : ℤ) : ℝ) - (j : ℝ))) *
        blockTrace (blockSub (relMean P q (j - 1) (m + L)) (relMean P q j (m + L)))) +
    ∑ j ∈ Finset.Icc (m + 1) (m + L),
      (3 : ℝ) ^ (-((1 - γ) / 8) * (((m + L : ℤ) : ℝ) - (j : ℝ))) *
        blockTrace (blockSub (relMean P q (j - 1) (m + L)) (relMean P q j (m + L))) := by
  classical
  let a : ℤ := (jStar : ℤ) + 1
  let f : ℤ → ℝ := fun j =>
    (3 : ℝ) ^ (-((1 - γ) / 8) * (((m + L : ℤ) : ℝ) - (j : ℝ))) *
      blockTrace (blockSub (relMean P q (j - 1) (m + L))
        (relMean P q j (m + L)))
  have hset : Finset.Icc a (m + L) = Finset.Icc a m ∪ Finset.Icc (m + 1) (m + L) := by
    ext j
    simp [a, Finset.mem_Icc]
    omega
  have hdisj : Disjoint (Finset.Icc a m) (Finset.Icc (m + 1) (m + L)) := by
    rw [Finset.disjoint_left]
    intro j hjOld hjNew
    have hjOld' := Finset.mem_Icc.mp hjOld
    have hjNew' := Finset.mem_Icc.mp hjNew
    omega
  unfold determinantDrift
  change (∑ j ∈ Finset.Icc a (m + L), f j) =
      (∑ j ∈ Finset.Icc a m, f j) + ∑ j ∈ Finset.Icc (m + 1) (m + L), f j
  rw [hset, Finset.sum_union hdisj]

private theorem one_add_sum_sub_one_le_prod {ι : Type*} (s : Finset ι)
    (f : ι → ℝ) (hf : ∀ i ∈ s, 1 ≤ f i) :
    1 + (∑ i ∈ s, (f i - 1)) ≤ ∏ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty, add_zero, le_refl]
  | insert a s ha ih =>
    have hfa := hf a (Finset.mem_insert_self a s)
    have hfs : ∀ i ∈ s, 1 ≤ f i := fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hs : 0 ≤ ∑ i ∈ s, (f i - 1) :=
      Finset.sum_nonneg fun i hi => sub_nonneg.mpr (hfs i hi)
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    calc
      1 + (f a - 1 + ∑ i ∈ s, (f i - 1)) ≤
          f a * (1 + ∑ i ∈ s, (f i - 1)) := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hfa) hs]
      _ ≤ f a * ∏ i ∈ s, f i := mul_le_mul_of_nonneg_left (ih hfs) (zero_le_one.trans hfa)

/-- The determinant of the positive square root has the expected square. -/
theorem det_matSqrt_sq {ι : Type*} [Fintype ι] [DecidableEq ι]
    {m : Matrix ι ι ℝ} (hm : m.PosSemidef) : (matSqrt m).det ^ 2 = m.det := by
  rw [sq, ← Matrix.det_mul, (matSqrt_spec hm).2]

/-- The normalized determinant is the quotient of full determinants. -/
theorem det_normalized_eq_div {ι : Type*} [Fintype ι] [DecidableEq ι]
    (F G : Matrix ι ι ℝ) (hG : G.PosDef) :
    (matSqrt G⁻¹ * F * matSqrt G⁻¹).det = F.det / G.det := by
  rw [Matrix.det_mul, Matrix.det_mul]
  calc
    (matSqrt G⁻¹).det * F.det * (matSqrt G⁻¹).det =
        F.det * (matSqrt G⁻¹).det ^ 2 := by ring
    _ = F.det / G.det := by rw [det_matSqrt_sq hG.inv.posSemidef, Matrix.det_nonsing_inv,
      Ring.inverse_eq_inv, div_eq_mul_inv]

/-- Full log determinants give the normalization factor with coefficient one. -/
theorem det_normalizedBlock_eq_exp {d : ℕ} (F G : BlockMat d)
    (hF : (toFullBlockMat F).PosDef) (hG : (toFullBlockMat G).PosDef) :
    (toFullBlockMat (normalizedBlock F G)).det =
      Real.exp (blockLogDet F - blockLogDet G) := by
  rw [normalizedBlock, toFullBlockMat_ofFullBlockMat, det_normalized_eq_div _ _ hG,
    blockLogDet, blockLogDet, Real.exp_sub, Real.exp_log hF.det_pos, Real.exp_log hG.det_pos]

private theorem matrixOrder_of_blockMatLoewnerLE {d : ℕ} {A B : BlockMat d}
    (hA : (toFullBlockMat A).IsHermitian) (hB : (toFullBlockMat B).IsHermitian)
    (hAB : BlockMatLoewnerLE A B) : toFullBlockMat A ≤ toFullBlockMat B := by
  apply Matrix.le_iff.mpr
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (hB.sub hA) ?_
  intro x
  have h := hAB (ofFullBlockVec x)
  simp only [← dotProduct_toFullBlockVec, toFullBlockVec_blockMatVecMul,
    toFullBlockVec_ofFullBlockVec] at h
  simp only [star_trivial, Matrix.sub_mulVec, dotProduct_sub]
  linarith only [h]

private theorem matrix_congr_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℝ} (hAB : A ≤ B) (S : Matrix ι ι ℝ) (hS : S.IsHermitian) :
    S * A * S ≤ S * B * S := by
  apply Matrix.le_iff.mpr
  have h := (Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same S
  simpa only [hS.eq, mul_sub, sub_mul] using h

/-- The conjugated trace/determinant bound on a positive definite pair. -/
theorem normalized_trace_sub_one_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F G : Matrix ι ι ℝ} (hF : F.PosDef) (hG : G.PosDef) (hGF : G ≤ F) :
    Matrix.trace (matSqrt G⁻¹ * F * matSqrt G⁻¹ - 1) ≤ F.det / G.det - 1 := by
  have hnorm := hF.posSemidef.conjTranspose_mul_mul_same (matSqrt G⁻¹)
  rw [(matSqrt_inv_posDef_full hG).isHermitian.eq] at hnorm
  rw [← det_normalized_eq_div F G hG]
  exact Recurrence.trace_sub_one_le_det_sub_one hnorm.isHermitian (Recurrence.one_le_normalize
    hG hGF)

private theorem toFullBlockMat_sub {d : ℕ} (A B : BlockMat d) :
    toFullBlockMat (blockSub A B) = toFullBlockMat A - toFullBlockMat B := by
  ext α β
  cases α <;> cases β <;> rfl

private theorem toFullBlockMat_identity {d : ℕ} :
    toFullBlockMat (Book.Ch02.blockIdentity d) = 1 := by
  ext α β
  cases α <;> cases β <;>
    simp [Book.Ch02.blockIdentity, Book.Ch02.blockDiag, toFullBlockMat, Matrix.one_apply]

/-- The printed trace increment bound for normalized full blocks. -/
theorem normalizedMean_trace_sub_identity_le
    {d : ℕ} (F G : BlockMat d) (hF : (toFullBlockMat F).PosDef)
    (hG : (toFullBlockMat G).PosDef) (hGF : BlockMatLoewnerLE G F) :
    blockTrace (blockSub (normalizedBlock F G) (Book.Ch02.blockIdentity d)) ≤
    Real.exp (blockLogDet F - blockLogDet G) - 1 := by
  rw [blockTrace, toFullBlockMat_sub, toFullBlockMat_identity,
    ← det_normalizedBlock_eq_exp F G hF hG]
  simp only [normalizedBlock, toFullBlockMat_ofFullBlockMat]
  rw [det_normalized_eq_div _ _ hG]
  exact normalized_trace_sub_one_le hF hG
    (matrixOrder_of_blockMatLoewnerLE hG.isHermitian hF.isHermitian hGF)

/-- Every eigenvalue is bounded by the determinant when all eigenvalues are at least one. -/
theorem matrix_le_det_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {P : Matrix ι ι ℝ} (hP : P.IsHermitian) (hIP : 1 ≤ P) : P ≤ P.det • 1 := by
  have heig : ∀ i, 1 ≤ hP.eigenvalues i := by
    intro i
    apply (algebraMap_le_iff_le_spectrum (a := P) (r := (1 : ℝ)) (ha := hP)).mp
      (by simpa only [map_one] using hIP)
    rw [hP.spectrum_real_eq_range_eigenvalues]
    exact Set.mem_range_self i
  have hprod := one_add_sum_sub_one_le_prod Finset.univ hP.eigenvalues (fun i _ => heig i)
  rw [← Algebra.algebraMap_eq_smul_one]
  apply le_algebraMap_of_spectrum_le (ha := hP)
  intro x hx
  obtain ⟨i, rfl⟩ := hP.spectrum_real_eq_range_eigenvalues ▸ hx
  have hi := Finset.single_le_sum (f := fun i => hP.eigenvalues i - 1)
    (fun i _ => sub_nonneg.mpr (heig i)) (Finset.mem_univ i)
  rw [hP.det_eq_prod_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  linarith only [hprod, hi]

private theorem inv_le_inv_of_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F G : Matrix ι ι ℝ} (hF : F.PosDef) (hG : G.PosDef) (hGF : G ≤ F) : F⁻¹ ≤ G⁻¹ := by
  have hD : (G⁻¹ - F⁻¹).IsHermitian := hG.inv.isHermitian.sub hF.inv.isHermitian
  have h₁ := hG.posSemidef.conjTranspose_mul_mul_same (G⁻¹ - F⁻¹)
  have h₂ := (Matrix.le_iff.mp hGF).conjTranspose_mul_mul_same F⁻¹
  rw [hD.eq] at h₁
  rw [hF.inv.isHermitian.eq] at h₂
  apply Matrix.le_iff.mpr
  (convert h₁.add h₂ using 1; try rfl)
  have hGiG := Matrix.nonsing_inv_mul G ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit)
  have hGGi := Matrix.mul_nonsing_inv G ((Matrix.isUnit_iff_isUnit_det G).mp hG.isUnit)
  have hFiF := Matrix.nonsing_inv_mul F ((Matrix.isUnit_iff_isUnit_det F).mp hF.isUnit)
  simp only [mul_sub, sub_mul, hGiG, hFiF, one_mul]
  rw [mul_assoc F⁻¹ G G⁻¹, hGGi, mul_one]
  abel

private theorem trace_mul_mono {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A B H : Matrix ι ι ℝ} (hAB : A ≤ B) (hH : H.PosSemidef) :
    (A * H).trace ≤ (B * H).trace := by
  have hR := matSqrt_spec hH
  have h := ((Matrix.le_iff.mp hAB).conjTranspose_mul_mul_same (matSqrt H)).trace_nonneg
  rw [hR.1.isHermitian.eq, Matrix.trace_mul_cycle, hR.2,
    mul_sub, Matrix.trace_sub, Matrix.trace_mul_comm H B, Matrix.trace_mul_comm H A] at h
  exact sub_nonneg.mp h

private theorem inverse_le_det_ratio_smul {ι : Type*} [Fintype ι] [DecidableEq ι]
    {F G : Matrix ι ι ℝ} (hF : F.PosDef) (hG : G.PosDef) (hGF : G ≤ F) :
    G⁻¹ ≤ (F.det / G.det) • F⁻¹ := by
  let : Invertible F := hF.isUnit.invertible
  let R := matSqrt F
  have hR : R.PosDef := by
    simpa only [Matrix.inv_inv_of_invertible] using matSqrt_inv_posDef_full hF.inv
  have hRR : R * R = F := (matSqrt_spec hF.posSemidef).2
  have hRnorm : R * F⁻¹ * R = 1 := by
    simpa only [Matrix.inv_inv_of_invertible] using matSqrt_inv_conj hF.inv
  have hN := hG.inv.posSemidef.conjTranspose_mul_mul_same R
  rw [hR.isHermitian.eq] at hN
  have hIN : 1 ≤ R * G⁻¹ * R := by
    simpa only [hRnorm] using matrix_congr_le (inv_le_inv_of_le hF hG hGF) R hR.isHermitian
  have hdet : (R * G⁻¹ * R).det = F.det / G.det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    calc
      R.det * G⁻¹.det * R.det = (R.det * R.det) * G⁻¹.det := by ring
      _ = F.det / G.det := by
        rw [← Matrix.det_mul, hRR, Matrix.det_nonsing_inv, Ring.inverse_eq_inv, div_eq_mul_inv]
  have hbound := matrix_le_det_smul_one hN.isHermitian hIN
  rw [hdet] at hbound
  have h := matrix_congr_le hbound R⁻¹ hR.inv.isHermitian
  have hRiR := Matrix.nonsing_inv_mul R ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit)
  have hRRi := Matrix.mul_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit)
  have hRiRi : R⁻¹ * R⁻¹ = F⁻¹ := by rw [← Matrix.mul_inv_rev, hRR]
  have hleft : R⁻¹ * (R * G⁻¹ * R) * R⁻¹ = G⁻¹ := by
    calc
      _ = (R⁻¹ * R) * G⁻¹ * (R * R⁻¹) := by simp only [mul_assoc]
      _ = G⁻¹ := by rw [hRiR, hRRi, one_mul, mul_one]
  simpa only [hleft, Matrix.mul_smul, Matrix.smul_mul, mul_one, hRiRi] using h

private theorem trace_normalized_eq_trace_inv_mul {ι : Type*} [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℝ) {F : Matrix ι ι ℝ} (hF : F.PosDef) :
    (matSqrt F⁻¹ * H * matSqrt F⁻¹).trace = (F⁻¹ * H).trace := by
  rw [Matrix.trace_mul_cycle, (matSqrt_spec hF.inv.posSemidef).2]

/-- Changing normalization of a positive increment costs at most the full determinant ratio.
The argument uses spectral order, inverse order and cyclic trace, without commutativity. -/
theorem normalized_increment_trace_le
    {d : ℕ} (F G H : BlockMat d) (hF : (toFullBlockMat F).PosDef)
    (hG : (toFullBlockMat G).PosDef) (hH : (toFullBlockMat H).PosSemidef)
    (hGF : BlockMatLoewnerLE G F) :
    blockTrace (normalizedBlock H G) ≤
    Real.exp (blockLogDet F - blockLogDet G) * blockTrace (normalizedBlock H F) := by
  have h := trace_mul_mono
    (inverse_le_det_ratio_smul hF hG
      (matrixOrder_of_blockMatLoewnerLE hG.isHermitian hF.isHermitian hGF)) hH
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at h
  simp only [blockTrace, normalizedBlock, toFullBlockMat_ofFullBlockMat,
    trace_normalized_eq_trace_inv_mul _ hG, trace_normalized_eq_trace_inv_mul _ hF]
  rwa [blockLogDet, blockLogDet, Real.exp_sub, Real.exp_log hF.det_pos,
    Real.exp_log hG.det_pos]

/-- The logarithm of the normalized mean is exactly the loss increment. -/
theorem blockLogDet_normalizedMean_eq_loss {d : ℕ} (P : MeasureTheory.Measure (CoeffSpace d))
    (q : Mat d) (j k : ℤ) (hj : (toFullBlockMat (adaptedMean P q j)).PosDef)
    (hk : (toFullBlockMat (adaptedMean P q k)).PosDef) :
    blockLogDet (relMean P q j k) = detIncrement P q j k := by
  unfold blockLogDet relMean
  rw [det_normalizedBlock_eq_exp _ _ hj hk, Real.log_exp]
  rfl

/-- The full log-determinant loss telescopes without analytic premises. -/
theorem logDetLoss_add {d : ℕ} (P : MeasureTheory.Measure (CoeffSpace d))
    (q : Mat d) (i j k : ℤ) :
    detIncrement P q i j + detIncrement P q j k = detIncrement P q i k := by
  unfold detIncrement
  exact sub_add_sub_cancel _ _ _

private theorem blockTrace_sub {d : ℕ} (A B : BlockMat d) :
    blockTrace (blockSub A B) = blockTrace A - blockTrace B := by
  rw [blockTrace, toFullBlockMat_sub, Matrix.trace_sub]
  rfl

private theorem normalized_sub_trace {d : ℕ} (A B F : BlockMat d) :
    blockTrace (blockSub (normalizedBlock A F) (normalizedBlock B F)) =
      blockTrace (normalizedBlock (blockSub A B) F) := by
  simp only [blockTrace, toFullBlockMat_sub, normalizedBlock,
    toFullBlockMat_ofFullBlockMat, mul_sub, sub_mul]

private theorem normalized_trace_nonneg {d : ℕ} (H F : BlockMat d)
    (hH : (toFullBlockMat H).PosSemidef) (hF : (toFullBlockMat F).PosDef) :
    0 ≤ blockTrace (normalizedBlock H F) := by
  have h := hH.conjTranspose_mul_mul_same (matSqrt (toFullBlockMat F)⁻¹)
  rw [(matSqrt_inv_posDef_full hF).isHermitian.eq] at h
  simpa only [blockTrace, normalizedBlock, toFullBlockMat_ofFullBlockMat] using h.trace_nonneg

private theorem block_order_of_adjacent {d : ℕ} (f : ℤ → BlockMat d) {a b : ℤ}
    (h : ∀ j ∈ Set.Icc (a + 1) b, BlockMatLoewnerLE (f j) (f (j - 1)))
    {i k : ℤ} (hi : a ≤ i) (hk : k ≤ b) (hik : i ≤ k) : BlockMatLoewnerLE (f k) (f i) := by
  revert hk
  induction k, hik using Int.leInduction with
  | base => exact fun _ => BlockMatLoewnerLE.refl _
  | succ k hik ih =>
    intro hk
    have hstep := h (k + 1) ⟨by omega, hk⟩
    simp only [add_sub_cancel_right] at hstep
    exact hstep.trans (ih (by omega))

private theorem sum_Icc_trace_telescope (f : ℤ → ℝ) {m n : ℤ} (hmn : m ≤ n) :
    (∑ j ∈ Finset.Icc (m + 1) n, (f (j - 1) - f j)) = f m - f n := by
  classical
  induction n, hmn using Int.leInduction with
  | base => simp only [Finset.Icc_eq_empty_of_lt (by omega : m < m + 1), Finset.sum_empty, sub_self]
  | succ n hmn ih =>
    have hset : Finset.Icc (m + 1) (n + 1) = insert (n + 1) (Finset.Icc (m + 1) n) := by
      ext j
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    have hnot : n + 1 ∉ Finset.Icc (m + 1) n := by simp only [Finset.mem_Icc]; omega
    rw [hset, Finset.sum_insert hnot, ih, add_sub_cancel_right]
    abel

private theorem drift_weight_split (γ : ℝ) (m L j : ℤ) :
    (3 : ℝ) ^ (-((1 - γ) / 8) * (((m + L : ℤ) : ℝ) - (j : ℝ))) =
      (3 : ℝ) ^ (-((1 - γ) / 8) * (L : ℝ)) *
      (3 : ℝ) ^ (-((1 - γ) / 8) * ((m : ℝ) - (j : ℝ))) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
  congr 1
  push_cast
  ring

private theorem drift_weight_le_one (γ : ℝ) (hγ : γ ≤ 1) {n j : ℤ} (hj : j ≤ n) :
    (3 : ℝ) ^ (-((1 - γ) / 8) * ((n : ℝ) - (j : ℝ))) ≤ 1 := by
  apply Real.rpow_le_one_of_one_le_of_nonpos (by norm_num)
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (div_nonneg (sub_nonneg.mpr hγ) (by norm_num)))
    (sub_nonneg.mpr (Int.cast_le.mpr hj))

/-- The printed drift advance for a positive adjacent-decreasing mean family.
These finite-dimensional hypotheses are the future outputs of annealed mean order;
no integrability of the total real drift formula is required. -/
theorem determinantDrift_advance_of_posDef_antitone
    {d : ℕ} (P : Measure (CoeffSpace d)) (γ : ℝ) (hγ : γ ≤ 1)
    (q : Mat d) (jStar : ℕ) (m L : ℤ) (hm : (jStar : ℤ) ≤ m) (hL : 1 ≤ L)
    (hpos : ∀ j ∈ Set.Icc (jStar : ℤ) (m + L), (toFullBlockMat (adaptedMean P q j)).PosDef)
    (horder : ∀ j ∈ Set.Icc ((jStar : ℤ) + 1) (m + L),
      BlockMatLoewnerLE (adaptedMean P q j) (adaptedMean P q (j - 1))) :
    determinantDrift P γ q jStar (m + L) ≤
    (3 : ℝ) ^ (-((1 - γ) / 8) * (L : ℝ)) * Real.exp (detIncrement P q m (m + L)) *
      determinantDrift P γ q jStar m + Real.exp (detIncrement P q m (m + L)) - 1 := by
  have hFm := hpos m ⟨hm, by omega⟩
  have hFt := hpos (m + L) ⟨by omega, le_rfl⟩
  have htm := block_order_of_adjacent (adaptedMean P q) horder hm le_rfl (by omega : m ≤ m + L)
  have hincrement : ∀ j ∈ Finset.Icc ((jStar : ℤ) + 1) (m + L),
      (toFullBlockMat (blockSub (adaptedMean P q (j - 1)) (adaptedMean P q j))).PosSemidef := by
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    rw [toFullBlockMat_sub]
    exact Matrix.le_iff.mp (matrixOrder_of_blockMatLoewnerLE
      (hpos j ⟨by omega, hj'.2⟩).isHermitian
      (hpos (j - 1) ⟨by omega, by omega⟩).isHermitian (horder j hj'))
  have hold :
      (∑ j ∈ Finset.Icc ((jStar : ℤ) + 1) m,
        (3 : ℝ) ^ (-((1 - γ) / 8) * (((m + L : ℤ) : ℝ) - (j : ℝ))) *
          blockTrace (blockSub (relMean P q (j - 1) (m + L))
            (relMean P q j (m + L)))) ≤
      (3 : ℝ) ^ (-((1 - γ) / 8) * (L : ℝ)) * Real.exp (detIncrement P q m (m + L)) *
        determinantDrift P γ q jStar m := by
    unfold determinantDrift
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j hj
    have hj' := Finset.mem_Icc.mp hj
    have hcmp := normalized_increment_trace_le (adaptedMean P q m) (adaptedMean P q (m + L))
      (blockSub (adaptedMean P q (j - 1)) (adaptedMean P q j)) hFm hFt
      (hincrement j (Finset.mem_Icc.mpr ⟨hj'.1, by omega⟩)) htm
    simp only [relMean, normalized_sub_trace, drift_weight_split]
    have hweight : 0 ≤ (3 : ℝ) ^ (-((1 - γ) / 8) * (L : ℝ)) *
        (3 : ℝ) ^ (-((1 - γ) / 8) * ((m : ℝ) - (j : ℝ))) :=
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (by norm_num) _)
    calc
      _ ≤ ((3 : ℝ) ^ (-((1 - γ) / 8) * (L : ℝ)) *
          (3 : ℝ) ^ (-((1 - γ) / 8) * ((m : ℝ) - (j : ℝ)))) *
          (Real.exp (detIncrement P q m (m + L)) *
            blockTrace (normalizedBlock (blockSub (adaptedMean P q (j - 1)) (adaptedMean P q j))
              (adaptedMean P q m))) := mul_le_mul_of_nonneg_left hcmp hweight
      _ = _ := by ring
  have hnew :
      (∑ j ∈ Finset.Icc (m + 1) (m + L),
        (3 : ℝ) ^ (-((1 - γ) / 8) * (((m + L : ℤ) : ℝ) - (j : ℝ))) *
          blockTrace (blockSub (relMean P q (j - 1) (m + L))
            (relMean P q j (m + L)))) ≤ Real.exp (detIncrement P q m (m + L)) - 1 := by
    calc
      _ ≤ ∑ j ∈ Finset.Icc (m + 1) (m + L),
          blockTrace (blockSub (relMean P q (j - 1) (m + L))
            (relMean P q j (m + L))) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_Icc.mp hj
        have hnonneg : 0 ≤ blockTrace (blockSub (relMean P q (j - 1) (m + L))
            (relMean P q j (m + L))) := by
          rw [relMean, relMean, normalized_sub_trace]
          exact normalized_trace_nonneg _ _
            (hincrement j (Finset.mem_Icc.mpr ⟨by omega, hj'.2⟩)) hFt
        exact mul_le_of_le_one_left hnonneg (drift_weight_le_one γ hγ hj'.2)
      _ = blockTrace (blockSub (relMean P q m (m + L)) (Book.Ch02.blockIdentity d)) := by
        simp only [blockTrace_sub]
        rw [sum_Icc_trace_telescope (fun j => blockTrace (relMean P q j (m + L))) (by omega)]
        simp only [relMean, normalizedBlock_self_of_posDef _ hFt]
      _ ≤ Real.exp (detIncrement P q m (m + L)) - 1 :=
        normalizedMean_trace_sub_identity_le _ _ hFm hFt htm
  rw [determinantDrift_split P γ q jStar m L hm (by omega)]
  exact (add_le_add hold hnew).trans_eq (by ring)

end

end HCPolySupport.HighContrast.Multiscale
end
