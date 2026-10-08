/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.DiagonalWeakNormRecentEnergyMap

/-!
# High-contrast homogenization: Provider.Response.DiagonalWeakNormRecentBound

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The averaged term on recent scales

The energy map and the factor-two response identity control the cell averages
of the optimizer differences.  On the good branch, the all-scale maximum
reduces the remaining response factor to the printed geometric weight.
-/

namespace HCPolySupport
namespace HighContrast
namespace Response

open Book.Ch02

noncomputable section

variable {d : ℕ}

/-- Each recent optimizer-difference energy is nonnegative. -/
theorem diagonalWeak_recent_difference_energy_nonneg
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {w : Fin d → ℤ} (hw : w ∈ alignedIndex q k t)
    (a : CoeffSpace d) (p r : Vec d) :
    0 ≤ Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
      blockVecDot
        (diagonalWeakChildState hq k w a p r x -
          diagonalWeakState hq t a p r x)
        (blockMatVecMul
          (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
          (diagonalWeakChildState hq k w a p r x -
            diagonalWeakState hq t a p r x))) := by
  obtain ⟨u, _hu, henergy⟩ := diagonalWeak_child_difference_energy_eq
    hq hkt hw a p r
  have hmax := diagonalWeakChildOptimizer_isMaximizer hq k w a p r u
  have hJ := responseJ_eq_responseValue_of_isResponseMaximizer
    (diagonalWeakChildOptimizer_isMaximizer hq k w a p r)
  rw [henergy]
  rw [← hJ] at hmax
  linarith only [hmax]

/-- Before imposing the good-event threshold, the recent averaged term is
controlled by the square-root response maximum and averaged defect. -/
theorem diagonalWeak_recent_average_bound [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {S m : Mat d} (hsymm : matTranspose S = S) (hsq : S * S = m)
    (hm : m.PosDef) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho : ℝ} {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤) :
    blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w) (fun x =>
            diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x))) ≤
      Real.sqrt 2 * diagonalWeakMetricFactor m E *
        (1 + Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
          (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2)) *
        diagonalWeakLoadMinus E p r *
        Real.sqrt (blockSize (diagonalWeakAverageDefect q k t E a)
          (blockIdentity d)) := by
  let Z := alignedIndex q k t
  let K := diagonalWeakMetricFactor m E
  let L := diagonalWeakLoadMinus E p r
  let B := 1 + Real.sqrt (diagonalWeakMaximum rho q t E a).toReal *
    (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2)
  let D := blockSize (diagonalWeakAverageDefect q k t E a) (blockIdentity d)
  let G : (Fin d → ℤ) → ℝ := fun w =>
    Book.Ch02.average (adaptedDomainAt hq k w) (fun x =>
      blockVecDot
        (diagonalWeakChildState hq k w a p r x -
          diagonalWeakState hq t a p r x)
        (blockMatVecMul
          (blockMatrixOfCoeff ((⇑a.1 : CoeffField d) x))
          (diagonalWeakChildState hq k w a p r x -
            diagonalWeakState hq t a p r x)))
  let V : (Fin d → ℤ) → BlockVec d := fun w =>
    blockCellAverage (adaptedCellAt q k w) (fun x =>
      diagonalWeakChildState hq k w a p r x -
        diagonalWeakState hq t a p r x)
  have hK0 : 0 ≤ K := diagonalWeakMetricFactor_nonneg m E
  have hL0 : 0 ≤ L := diagonalWeakLoadMinus_nonneg E p r
  have hB0 : 0 ≤ B := by
    exact add_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg (by norm_num) _))
  have hD0 : 0 ≤ D := blockSize_diagonalWeakAverageDefect_nonneg
    hq hkt hE hEpd a
  have hG0 : ∀ w ∈ Z, 0 ≤ G w := by
    intro w hw
    exact diagonalWeak_recent_difference_energy_nonneg hq hkt hw a p r
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
      blockVecDot (blockMatVecMul (blockDiag S S⁻¹) (V w))
          (blockMatVecMul (blockDiag S S⁻¹) (V w)) ≤
        (K * B) ^ 2 * G w := by
    intro w hw
    have hmap := metricBlockNormSq_recent_difference_le
      hq hkt hw a p r hm hE hEpd
    have hscale : K ^ 2 * blockSize (adaptedResponse q k w a) E * G w ≤
        K ^ 2 * B ^ 2 * G w := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hsize w hw) (sq_nonneg K)) (hG0 w hw)
    calc
      blockVecDot (blockMatVecMul (blockDiag S S⁻¹) (V w))
          (blockMatVecMul (blockDiag S S⁻¹) (V w)) =
        metricBlockNormSq m (V w) := blockVecDot_self_blockDiag_root hsymm hsq _
      _ ≤ K ^ 2 * blockSize (adaptedResponse q k w a) E * G w := hmap
      _ ≤ K ^ 2 * B ^ 2 * G w := hscale
      _ = (K * B) ^ 2 * G w := by ring
  have henergy : avsum Z G ≤ 2 * L ^ 2 * D :=
    diagonalWeak_recent_difference_energy_le hq hkt hE hEpd a p r
  have hsum : avsum Z (fun w =>
      blockVecDot (blockMatVecMul (blockDiag S S⁻¹) (V w))
        (blockMatVecMul (blockDiag S S⁻¹) (V w))) ≤
      (K * B) ^ 2 * (2 * L ^ 2 * D) := by
    calc
      avsum Z (fun w =>
          blockVecDot (blockMatVecMul (blockDiag S S⁻¹) (V w))
            (blockMatVecMul (blockDiag S S⁻¹) (V w))) ≤
        avsum Z (fun w => (K * B) ^ 2 * G w) := avsum_le_avsum hcell
      _ = (K * B) ^ 2 * avsum Z G := avsum_const_mul Z _ G
      _ ≤ (K * B) ^ 2 * (2 * L ^ 2 * D) :=
        mul_le_mul_of_nonneg_left henergy (sq_nonneg (K * B))
  have hC0 : 0 ≤ Real.sqrt 2 * K * B * L * Real.sqrt D := by positivity
  have hradicand : (K * B) ^ 2 * (2 * L ^ 2 * D) =
      (Real.sqrt 2 * K * B * L * Real.sqrt D) ^ 2 := by
    have hroot2 : Real.sqrt 2 ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    have hrootD : Real.sqrt D ^ 2 = D := Real.sq_sqrt hD0
    calc
      (K * B) ^ 2 * (2 * L ^ 2 * D) =
          Real.sqrt 2 ^ 2 * (K * B * L) ^ 2 * Real.sqrt D ^ 2 := by
        rw [hroot2, hrootD]
        ring
      _ = (Real.sqrt 2 * K * B * L * Real.sqrt D) ^ 2 := by ring
  change blockAvsumL2 Z (fun w =>
      blockMatVecMul (blockDiag S S⁻¹) (V w)) ≤
    Real.sqrt 2 * K * B * L * Real.sqrt D
  rw [blockAvsumL2_eq]
  calc
    Real.sqrt (avsum Z (fun w =>
        blockVecDot (blockMatVecMul (blockDiag S S⁻¹) (V w))
          (blockMatVecMul (blockDiag S S⁻¹) (V w)))) ≤
      Real.sqrt ((K * B) ^ 2 * (2 * L ^ 2 * D)) := Real.sqrt_le_sqrt hsum
    _ = Real.sqrt ((Real.sqrt 2 * K * B * L * Real.sqrt D) ^ 2) := by
      rw [hradicand]
    _ = Real.sqrt 2 * K * B * L * Real.sqrt D := Real.sqrt_sq hC0

/-- On the good branch, the recent averaged term has the geometric factor
`3^{rho(t-k)/2}` and no remaining maximum. -/
theorem diagonalWeak_recent_average_good_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {S m : Mat d} (hsymm : matTranspose S = S) (hsq : S * S = m)
    (hm : m.PosDef) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho delta : ℝ} (hrho : 0 < rho)
    (hdelta1 : delta ≤ 1) {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hgood : (diagonalWeakMaximum rho q t E a).toReal ≤ delta) :
    blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w) (fun x =>
            diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x))) ≤
      4 * diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
        (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2) *
        Real.sqrt (blockSize (diagonalWeakAverageDefect q k t E a)
          (blockIdentity d)) := by
  let M := (diagonalWeakMaximum rho q t E a).toReal
  let K := diagonalWeakMetricFactor m E
  let L := diagonalWeakLoadMinus E p r
  let R := (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2)
  let D := blockSize (diagonalWeakAverageDefect q k t E a) (blockIdentity d)
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hM1 : M ≤ 1 := hgood.trans hdelta1
  have hrootM : Real.sqrt M ≤ 1 := Real.sqrt_le_one.mpr hM1
  have hktR : (k : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkt
  have hgap : (0 : ℝ) ≤ (t : ℝ) - (k : ℝ) := by
    linarith only [hktR]
  have hR0 : 0 ≤ R := Real.rpow_nonneg (by norm_num) _
  have hR1 : 1 ≤ R := Real.one_le_rpow (by norm_num)
    (div_nonneg (mul_nonneg hrho.le hgap) (by norm_num))
  have hB0 : 0 ≤ 1 + Real.sqrt M * R := by positivity
  have hB : 1 + Real.sqrt M * R ≤ 2 * R := by
    have hmR : Real.sqrt M * R ≤ R := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hrootM hR0
    linarith only [hmR, hR1]
  have hroot2 : Real.sqrt 2 ≤ 2 := by
    rw [Real.sqrt_le_iff]
    constructor <;> norm_num
  have hcoeff : Real.sqrt 2 * (1 + Real.sqrt M * R) ≤ 4 * R := by
    calc
      Real.sqrt 2 * (1 + Real.sqrt M * R) ≤
          2 * (1 + Real.sqrt M * R) :=
        mul_le_mul_of_nonneg_right hroot2 hB0
      _ ≤ 2 * (2 * R) := mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = 4 * R := by ring
  have hraw := diagonalWeak_recent_average_bound hq hkt hsymm hsq hm
    hE hEpd p r hfinite
  have hrest0 : 0 ≤ K * L * Real.sqrt D :=
    mul_nonneg
      (mul_nonneg (diagonalWeakMetricFactor_nonneg m E)
        (diagonalWeakLoadMinus_nonneg E p r))
      (Real.sqrt_nonneg D)
  calc
    blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w) (fun x =>
            diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x))) ≤
      Real.sqrt 2 * K * (1 + Real.sqrt M * R) * L * Real.sqrt D := hraw
    _ = (Real.sqrt 2 * (1 + Real.sqrt M * R)) *
        (K * L * Real.sqrt D) := by ring
    _ ≤ (4 * R) * (K * L * Real.sqrt D) :=
      mul_le_mul_of_nonneg_right hcoeff hrest0
    _ = 4 * K * L * R * Real.sqrt D := by ring

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

/-- The recent averaged term at a released split level: the printed Step 4
constant `√2(1+√δ)`, which is `2√2` at the fixed level. -/
theorem diagonalWeak_recent_average_good_at_level_le [NeZero d]
    {q : Mat d} (hq : q.PosDef) {k t : ℤ} (hkt : k ≤ t)
    {S m : Mat d} (hsymm : matTranspose S = S) (hsq : S * S = m)
    (hm : m.PosDef) {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho delta : ℝ} (hrho : 0 < rho)
    {a : CoeffSpace d} (p r : Vec d)
    (hfinite : diagonalWeakMaximum rho q t E a ≠ ⊤)
    (hgood : (diagonalWeakMaximum rho q t E a).toReal ≤ delta) :
    blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w) (fun x =>
            diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x))) ≤
      Real.sqrt 2 * (1 + Real.sqrt delta) *
        diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r *
        (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2) *
        Real.sqrt (blockSize (diagonalWeakAverageDefect q k t E a)
          (blockIdentity d)) := by
  set M : ℝ := (diagonalWeakMaximum rho q t E a).toReal with hMdef
  set K : ℝ := diagonalWeakMetricFactor m E with hKdef
  set L : ℝ := diagonalWeakLoadMinus E p r with hLdef
  set R : ℝ := (3 : ℝ) ^ ((rho * ((t : ℝ) - (k : ℝ))) / 2) with hRdef
  set D : ℝ := blockSize (diagonalWeakAverageDefect q k t E a)
    (blockIdentity d) with hDdef
  have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
  have hrootMD : Real.sqrt M ≤ Real.sqrt delta := Real.sqrt_le_sqrt hgood
  have hktR : (k : ℝ) ≤ (t : ℝ) := by exact_mod_cast hkt
  have hgap : (0 : ℝ) ≤ (t : ℝ) - (k : ℝ) := by linarith only [hktR]
  have hR0 : 0 ≤ R := Real.rpow_nonneg (by norm_num) _
  have hR1 : 1 ≤ R := Real.one_le_rpow (by norm_num)
    (div_nonneg (mul_nonneg hrho.le hgap) (by norm_num))
  have hB0 : 0 ≤ 1 + Real.sqrt M * R := by positivity
  have hB : 1 + Real.sqrt M * R ≤ (1 + Real.sqrt delta) * R := by
    have hmR : Real.sqrt M * R ≤ Real.sqrt delta * R :=
      mul_le_mul_of_nonneg_right hrootMD hR0
    calc
      1 + Real.sqrt M * R ≤ R + Real.sqrt M * R := by linarith only [hR1]
      _ ≤ R + Real.sqrt delta * R := by linarith only [hmR]
      _ = (1 + Real.sqrt delta) * R := by ring
  have hroot20 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  have hcoeff : Real.sqrt 2 * (1 + Real.sqrt M * R) ≤
      Real.sqrt 2 * (1 + Real.sqrt delta) * R := by
    calc
      Real.sqrt 2 * (1 + Real.sqrt M * R) ≤
          Real.sqrt 2 * ((1 + Real.sqrt delta) * R) :=
        mul_le_mul_of_nonneg_left hB hroot20
      _ = Real.sqrt 2 * (1 + Real.sqrt delta) * R := by ring
  have hraw := diagonalWeak_recent_average_bound hq hkt hsymm hsq hm
    hE hEpd p r hfinite
  have hrest0 : 0 ≤ K * L * Real.sqrt D :=
    mul_nonneg
      (mul_nonneg (diagonalWeakMetricFactor_nonneg m E)
        (diagonalWeakLoadMinus_nonneg E p r))
      (Real.sqrt_nonneg D)
  calc
    blockAvsumL2 (alignedIndex q k t) (fun w =>
        blockMatVecMul (blockDiag S S⁻¹)
          (blockCellAverage (adaptedCellAt q k w) (fun x =>
            diagonalWeakChildState hq k w a p r x -
              diagonalWeakState hq t a p r x))) ≤
      Real.sqrt 2 * K * (1 + Real.sqrt M * R) * L * Real.sqrt D := hraw
    _ = (Real.sqrt 2 * (1 + Real.sqrt M * R)) * (K * L * Real.sqrt D) := by
      ring
    _ ≤ (Real.sqrt 2 * (1 + Real.sqrt delta) * R) *
        (K * L * Real.sqrt D) :=
      mul_le_mul_of_nonneg_right hcoeff hrest0
    _ = Real.sqrt 2 * (1 + Real.sqrt delta) * K * L * R * Real.sqrt D := by
      ring

end

end Response
end HighContrast
end HCPolySupport
