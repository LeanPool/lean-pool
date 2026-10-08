/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormCellEnergy

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormScaleEnergy

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Single-scale energy bound for the diagonal weak estimate

The equal-weight partition identity turns the centered child averages into a
finite variance.  The response maximum controls every child metric, while the
partitioned energy of the canonical state closes the resulting square sum.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02 MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem avsum_matVecMul_apply {iota : Type*} (Z : Finset iota)
    (A : Mat d) (u : iota → Vec d) (i : Fin d) :
    avsum Z (fun z => matVecMul A (u z) i) =
      matVecMul A (fun j => avsum Z (fun z => u z j)) i := by
  rw [avsum_eq]
  simp_rw [matVecMul, avsum_eq]
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => by ring_nf

private theorem blockMatVecMul_sub (A : BlockMat d) (X Y : BlockVec d) :
    blockMatVecMul A (X - Y) = blockMatVecMul A X - blockMatVecMul A Y := by
  have hneg : blockMatVecMul A (-Y) = -blockMatVecMul A Y := by
    simpa using blockMatVecMul_smul A (-1) Y
  rw [sub_eq_add_neg, blockMatVecMul_add, hneg]
  rfl

private theorem blockMatVecMul_blockDiag_fst (A B : Mat d) (X : BlockVec d) :
    (blockMatVecMul (blockDiag A B) X).1 = matVecMul A X.1 := by
  rcases X with ⟨x, y⟩
  change matVecMul A x + matVecMul 0 y = matVecMul A x
  rw [zero_matVecMul, add_zero]

private theorem blockMatVecMul_blockDiag_snd (A B : Mat d) (X : BlockVec d) :
    (blockMatVecMul (blockDiag A B) X).2 = matVecMul B X.2 := by
  rcases X with ⟨x, y⟩
  change matVecMul 0 x + matVecMul B y = matVecMul B y
  rw [zero_matVecMul, zero_add]

/-- Applying a fixed block metric preserves the finite-variance contraction
from child averages to their parent mean. -/
theorem blockAvsumL2_metricRoot_centered_le
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {S : Mat d} {F : Vec d → BlockVec d}
    (hF₁ : ∀ i, IntegrableOn (fun x => (F x).1 i) (adaptedCell q t) volume)
    (hF₂ : ∀ i, IntegrableOn (fun x => (F x).2 i) (adaptedCell q t) volume) :
    blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w) F -
            blockCellAverage (adaptedCell q t) F)) ≤
      blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w) F)) := by
  let Z := alignedIndex q k t
  let u : (Fin d → ℤ) → BlockVec d := fun w =>
    blockMatVecMul (blockDiag S S⁻¹)
      (blockCellAverage (adaptedCellAt q k w) F)
  let m : BlockVec d := blockMatVecMul (blockDiag S S⁻¹)
    (blockCellAverage (adaptedCell q t) F)
  have hparent := blockCellAverage_adaptedCell_eq_avsum hq hkt hF₁ hF₂
  have hmean : ∀ alpha : BlockCoord d,
      avsum Z (fun w => toFullBlockVec (u w) alpha) = toFullBlockVec m alpha := by
    intro alpha
    cases alpha with
    | inl i =>
        simp only [u, m, toFullBlockVec, blockMatVecMul_blockDiag_fst]
        rw [avsum_matVecMul_apply]
        exact congrArg (fun v : Vec d => matVecMul S v i)
          (congrArg Prod.fst hparent).symm
    | inr i =>
        simp only [u, m, toFullBlockVec, blockMatVecMul_blockDiag_snd]
        rw [avsum_matVecMul_apply]
        exact congrArg (fun v : Vec d => matVecMul S⁻¹ v i)
          (congrArg Prod.snd hparent).symm
  have hvar := blockAvsumL2_sub_mean_le (alignedIndex_nonempty hq hkt) u m hmean
  change blockAvsumL2 Z (fun w =>
      blockMatVecMul (blockDiag S S⁻¹)
        (blockCellAverage (adaptedCellAt q k w) F -
          blockCellAverage (adaptedCell q t) F)) ≤ _
  rw [show (fun w => blockMatVecMul (blockDiag S S⁻¹)
      (blockCellAverage (adaptedCellAt q k w) F -
        blockCellAverage (adaptedCell q t) F)) =
      (fun w => u w - m) by
        funext w
        exact blockMatVecMul_sub _ _ _]
  exact hvar

private theorem memVectorL2_integrableOn_component_adaptedCell
    {q : Mat d} (hq : q.PosDef) (t : ℤ) {F : Vec d → Vec d}
    (hF : MemVectorL2 (adaptedCell q t) F) (i : Fin d) :
    IntegrableOn (fun x => F x i) (adaptedCell q t) volume :=
  integrableOn_component (U := adaptedDomain hq t) hF i

/-- The canonical diagonal state satisfies the centered finite-variance
contraction on every aligned child scale. -/
theorem blockAvsumL2_metricRoot_centered_diagonalWeakState_le
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {S : Mat d} {a : CoeffSpace d} (p r : Vec d) :
    blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w)
              (diagonalWeakState hq t a p r) -
            blockCellAverage (adaptedCell q t)
              (diagonalWeakState hq t a p r))) ≤
      blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakState hq t a p r))) := by
  exact blockAvsumL2_metricRoot_centered_le hq hkt
    (S := S) (F := diagonalWeakState hq t a p r)
    (fun i => memVectorL2_integrableOn_component_adaptedCell hq t
      (diagonalWeakState_memVectorL2 hq t a p r).1 i)
    (fun i => memVectorL2_integrableOn_component_adaptedCell hq t
      (diagonalWeakState_memVectorL2 hq t a p r).2 i)

/-- The uncentered metric square sum on one child scale is controlled by the
response maximum and the energy of the canonical parent optimizer. -/
theorem blockAvsumL2_metricRoot_diagonalWeakState_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {S m : Mat d} (hsymm : matTranspose S = S) (hsq : S * S = m)
    (hm : m.PosDef) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho : ℝ} {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤) :
    blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w)
            (diagonalWeakState hq t a p r))) ≤
      Real.sqrt 2 * diagonalWeakMetricFactor m E *
        (1 + Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
          (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2)) *
            diagonalWeakEnergy hq t a p r := by
  let Z := alignedIndex q k t
  let F := diagonalWeakState hq t a p r
  let K := diagonalWeakMetricFactor m E
  let B := 1 + Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
    (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2)
  let e := diagonalWeakEnergy hq t a p r
  let G : (Fin d → ℤ) → ℝ := fun w =>
    Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
      blockVecDot (F x)
        (blockMatVecMul (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x)) (F x)))
  have hK0 : 0 ≤ K := diagonalWeakMetricFactor_nonneg m E
  have hB0 : 0 ≤ B := by
    exact add_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg (by norm_num) _))
  have he0 : 0 ≤ e := diagonalWeakEnergy_nonneg hq t a p r
  have hG0 : ∀ w, 0 ≤ G w := by
    intro w
    exact diagonalWeakState_cellEnergy_nonneg hq k t w a p r
  have hsize : ∀ w ∈ Z,
      blockSize (adaptedResponse q k w a) E ≤ B ^ 2 := by
    intro w hw
    have hA0 : 0 ≤ blockSize (adaptedResponse q k w a) E :=
      PortableHistory.blockSize_nonneg (Recurrence.isSymmetricBlockMat_adaptedResponse q k w a)
        hE hEpd
    calc
      blockSize (adaptedResponse q k w a) E =
          (Real.sqrt (blockSize (adaptedResponse q k w a) E)) ^ 2 :=
        (Real.sq_sqrt hA0).symm
      _ ≤ B ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _)
        (sqrt_blockSize_adaptedResponse_le_of_maximum_finite
          hq hE hEpd hkt hw hfinite) 2
  have hcell : ∀ w ∈ Z,
      blockVecDot
          (blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w) F))
          (blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w) F)) ≤
        (K * B) ^ 2 * G w := by
    intro w hw
    have hmap := metricBlockNormSq_blockCellAverage_diagonalWeakState_le
      hq hkt hw a p r hm hE hEpd
    have hscale : K ^ 2 * blockSize (adaptedResponse q k w a) E * G w ≤
        K ^ 2 * B ^ 2 * G w := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hsize w hw) (sq_nonneg K)) (hG0 w)
    calc
      blockVecDot
          (blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w) F))
          (blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w) F)) =
          metricBlockNormSq m (blockCellAverage (adaptedCellAt q k w) F) :=
        blockVecDot_self_blockDiag_root hsymm hsq _
      _ ≤ K ^ 2 * blockSize (adaptedResponse q k w a) E * G w := hmap
      _ ≤ K ^ 2 * B ^ 2 * G w := hscale
      _ = (K * B) ^ 2 * G w := by ring
  have hsum : avsum Z (fun w =>
      blockVecDot
        (blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w) F))
        (blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w) F))) ≤
      (K * B) ^ 2 * (2 * e ^ 2) := by
    calc
      avsum Z (fun w =>
          blockVecDot
            (blockMatVecMul (blockDiag S S⁻¹)
              (blockCellAverage (adaptedCellAt q k w) F))
            (blockMatVecMul (blockDiag S S⁻¹)
              (blockCellAverage (adaptedCellAt q k w) F))) ≤
          avsum Z (fun w => (K * B) ^ 2 * G w) := avsum_le_avsum hcell
      _ = (K * B) ^ 2 * avsum Z G := avsum_const_mul Z _ G
      _ = (K * B) ^ 2 * (2 * e ^ 2) := by
        rw [show avsum Z G = 2 * e ^ 2 from
          avsum_diagonalWeakState_energy_eq hq hkt a p r]
  have hC0 : 0 ≤ Real.sqrt 2 * K * B * e := by positivity
  have hradicand : (K * B) ^ 2 * (2 * e ^ 2) =
      (Real.sqrt 2 * K * B * e) ^ 2 := by
    calc
      (K * B) ^ 2 * (2 * e ^ 2) = 2 * (K * B * e) ^ 2 := by ring
      _ = (Real.sqrt 2) ^ 2 * (K * B * e) ^ 2 := by
        rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      _ = (Real.sqrt 2 * K * B * e) ^ 2 := by ring
  change blockAvsumL2 Z (fun w =>
      blockMatVecMul (blockDiag S S⁻¹)
        (blockCellAverage (adaptedCellAt q k w) F)) ≤
    Real.sqrt 2 * K * B * e
  rw [blockAvsumL2_eq]
  calc
    Real.sqrt (avsum Z (fun w =>
        blockVecDot
          (blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w) F))
          (blockMatVecMul (blockDiag S S⁻¹)
            (blockCellAverage (adaptedCellAt q k w) F)))) ≤
        Real.sqrt ((K * B) ^ 2 * (2 * e ^ 2)) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt ((Real.sqrt 2 * K * B * e) ^ 2) := by rw [hradicand]
    _ = Real.sqrt 2 * K * B * e := Real.sqrt_sq hC0

end

end Response

end HighContrast

end HCPolySupport

end
