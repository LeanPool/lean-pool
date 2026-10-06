/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowSkewCarriers
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileWeakCarriers

/-!
# High-contrast homogenization: Provider.Response.ProfileRowMeanEstimates

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The cutoff-defect mean rows of the pre-Young estimate

The pre-Young assembly controls the two annealed means
`E[((φ-1)∇v_t)_{U_t}]` and `E[((φ-1)a∇v_t)_{U_t}]`, paired against the two
annealed optimizer centers.  Each pairing is bounded by a defect root times the
scale-`s` Schur load, plus a scale gain times the energy root times the root of
the all-earlier Schur row.

This file records the two annealed means, the two halves of the Schur load, the
place of the scale-`s` load inside the all-earlier row, and the combination of
the two mean estimates into the single boundary-mean term of the assembly.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## A normalized-average Cauchy-Schwarz inequality -/

/-- The normalized average of a square root is at most the square root of the
normalized average. -/
theorem avsum_sqrt_le_sqrt_avsum {ι : Type*} {Z : Finset ι} {f : ι → ℝ}
    (hZ : Z.Nonempty) (hf : ∀ z ∈ Z, 0 ≤ f z) :
    avsum Z (fun z ↦ Real.sqrt (f z)) ≤ Real.sqrt (avsum Z f) := by
  classical
  have hcard : (0 : ℝ) < (Z.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hZ
  have hsq : ∀ z ∈ Z, Real.sqrt (f z) ^ 2 = f z := fun z hz ↦
    Real.sq_sqrt (hf z hz)
  have hcheb :
      (∑ z ∈ Z, Real.sqrt (f z)) ^ 2 ≤
        (Z.card : ℝ) * ∑ z ∈ Z, Real.sqrt (f z) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsum : (∑ z ∈ Z, Real.sqrt (f z) ^ 2) = ∑ z ∈ Z, f z :=
    Finset.sum_congr rfl hsq
  rw [hsum] at hcheb
  have hnonneg : 0 ≤ avsum Z (fun z ↦ Real.sqrt (f z)) :=
    avsum_nonneg fun z _ ↦ Real.sqrt_nonneg _
  have hinv : ((Z.card : ℝ)⁻¹) ^ 2 * ((Z.card : ℝ) * ∑ z ∈ Z, f z) =
      (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, f z := by
    field_simp
  have hsq_le : avsum Z (fun z ↦ Real.sqrt (f z)) ^ 2 ≤ avsum Z f := by
    rw [avsum_eq, avsum_eq, mul_pow]
    calc ((Z.card : ℝ)⁻¹) ^ 2 * (∑ z ∈ Z, Real.sqrt (f z)) ^ 2
        ≤ ((Z.card : ℝ)⁻¹) ^ 2 * ((Z.card : ℝ) * ∑ z ∈ Z, f z) :=
          mul_le_mul_of_nonneg_left hcheb (by positivity)
      _ = (Z.card : ℝ)⁻¹ * ∑ z ∈ Z, f z := hinv
  have hroot := Real.sqrt_le_sqrt hsq_le
  rwa [Real.sqrt_sq hnonneg] at hroot

/-- **The defect half of a cutoff-defect mean row.**  A family of cell pairings,
each bounded by the root of a cell energy defect times a fixed load, has
normalized average at most the root of the total defect times that load, once
the cutoff weights are bounded by one.  The total defect is twice the response
defect. -/
theorem avsum_weighted_le_sqrt_two_mul_defect {ι : Type*} {Z : Finset ι}
    {defect pairing weight : ι → ℝ} {tau load : ℝ}
    (hZ : Z.Nonempty) (hload : 0 ≤ load)
    (hdefect : ∀ z ∈ Z, 0 ≤ defect z)
    (hweight : ∀ z ∈ Z, |weight z| ≤ 1)
    (hpairing : ∀ z ∈ Z, |pairing z| ≤ Real.sqrt (defect z) * load)
    (htau : avsum Z defect = 2 * tau) :
    avsum Z (fun z ↦ |weight z * pairing z|) ≤ Real.sqrt (2 * tau) * load := by
  have hterm : ∀ z ∈ Z, |weight z * pairing z| ≤ load * Real.sqrt (defect z) := by
    intro z hz
    rw [abs_mul]
    calc |weight z| * |pairing z| ≤ 1 * |pairing z| :=
          mul_le_mul_of_nonneg_right (hweight z hz) (abs_nonneg _)
      _ = |pairing z| := one_mul _
      _ ≤ Real.sqrt (defect z) * load := hpairing z hz
      _ = load * Real.sqrt (defect z) := mul_comm _ _
  have hstep :
      avsum Z (fun z ↦ |weight z * pairing z|) ≤
        load * avsum Z (fun z ↦ Real.sqrt (defect z)) := by
    calc avsum Z (fun z ↦ |weight z * pairing z|)
        ≤ avsum Z (fun z ↦ load * Real.sqrt (defect z)) := avsum_le_avsum hterm
      _ = load * avsum Z (fun z ↦ Real.sqrt (defect z)) :=
          avsum_const_mul Z load _
  refine hstep.trans ?_
  have hroot := avsum_sqrt_le_sqrt_avsum hZ hdefect
  calc load * avsum Z (fun z ↦ Real.sqrt (defect z))
      ≤ load * Real.sqrt (avsum Z defect) :=
        mul_le_mul_of_nonneg_left hroot hload
    _ = Real.sqrt (2 * tau) * load := by rw [htau, mul_comm]

/-! ## The two halves of the Schur load -/

/-- The flux half `|σ_bar_*^{-1/2}Q|` of the Schur load. -/
@[expose]
def profileSchurLoadFlux (H : BlockMat d) (Qcen : Vec d) : ℝ :=
  Book.Ch02.vecNorm (matVecMul (matSqrt ((schurSigmaStar H)⁻¹)) Qcen)

/-- The gradient half `|b_bar^{1/2}P|` of the Schur load. -/
@[expose]
def profileSchurLoadGradient (H : BlockMat d) (Pcen : Vec d) : ℝ :=
  Book.Ch02.vecNorm (matVecMul (matSqrt H.upperLeft) Pcen)

theorem profileSchurLoadFlux_nonneg (H : BlockMat d) (Qcen : Vec d) :
    0 ≤ profileSchurLoadFlux H Qcen :=
  Book.Ch02.vecNorm_nonneg _

theorem profileSchurLoadGradient_nonneg (H : BlockMat d) (Pcen : Vec d) :
    0 ≤ profileSchurLoadGradient H Pcen :=
  Book.Ch02.vecNorm_nonneg _

/-- The Schur load is the square of the sum of its two halves. -/
theorem profileSchurLoad_eq_add_sq (H : BlockMat d) (Pcen Qcen : Vec d) :
    profileSchurLoad H Pcen Qcen =
      (profileSchurLoadFlux H Qcen + profileSchurLoadGradient H Pcen) ^ 2 := rfl

/-- **The root of the Schur load splits**: the two halves add to the root. -/
theorem sqrt_profileSchurLoad (H : BlockMat d) (Pcen Qcen : Vec d) :
    Real.sqrt (profileSchurLoad H Pcen Qcen) =
      profileSchurLoadFlux H Qcen + profileSchurLoadGradient H Pcen := by
  rw [profileSchurLoad_eq_add_sq, Real.sqrt_sq]
  exact add_nonneg (profileSchurLoadFlux_nonneg H Qcen)
    (profileSchurLoadGradient_nonneg H Pcen)

/-! ## The scale-`s` cell inside the all-earlier row -/

/-- The origin lies in every adapted cell. -/
theorem zero_mem_adaptedCell (q : Mat d) (j : ℤ) : (0 : Vec d) ∈ adaptedCell q j := by
  refine ⟨0, ?_, matVecMul_zero q⟩
  have h := standardCellCenter_zero_mem_centeredCube (d := d) j j
  have hzero : standardCellCenter (d := d) j (0 : Fin d → ℤ) = (0 : Vec d) := by
    funext i
    simp [standardCellCenter]
  rwa [hzero] at h

/-- The aligned adapted cell at the zero label is the adapted cell. -/
theorem adaptedCellAt_zero (q : Mat d) (j : ℤ) :
    adaptedCellAt q j 0 = adaptedCell q j := by
  have hlabel : (fun i ↦ (((0 : Fin d → ℤ) i : ℤ) : ℝ)) = (0 : Vec d) := by
    funext i
    simp
  have hmap : (fun x : Vec d ↦
      (3 : ℝ) ^ j • matVecMul q (fun i ↦ (((0 : Fin d → ℤ) i : ℤ) : ℝ)) + x) = id := by
    funext x
    rw [hlabel, matVecMul_zero, smul_zero, zero_add]
    rfl
  rw [adaptedCellAt, hmap, Set.image_id]

/-- The aligned index of a scale against itself is the single zero label. -/
theorem alignedIndex_self {q : Mat d} (hq : q.PosDef) (j : ℤ) :
    alignedIndex q j j = {0} := by
  classical
  have hmem : (0 : Fin d → ℤ) ∈ alignedIndex q j j := by
    refine (mem_alignedIndex_iff hq (le_refl j)).mpr ?_
    have hcenter : adaptedCellCenter q j (0 : Fin d → ℤ) = (0 : Vec d) := by
      have : (fun i ↦ (((0 : Fin d → ℤ) i : ℤ) : ℝ)) = (0 : Vec d) := by
        funext i
        simp
      rw [adaptedCellCenter, this, matVecMul_zero, smul_zero]
    rw [hcenter]
    exact zero_mem_adaptedCell q j
  have hcard : (alignedIndex q j j).card = 1 := by
    rw [card_alignedIndex hq (le_refl j)]
    simp
  obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hcard
  rw [hw] at hmem ⊢
  rw [Finset.mem_singleton] at hmem
  rw [hmem]

/-- A normalized average over the aligned index of a scale against itself is the
value at the zero label. -/
theorem avsum_alignedIndex_self {q : Mat d} (hq : q.PosDef) (j : ℤ)
    (f : (Fin d → ℤ) → ℝ) :
    avsum (alignedIndex q j j) f = f 0 := by
  rw [alignedIndex_self hq j, avsum_eq]
  simp

/-- The lower-cutoff hatted row taken at the terminal cutoff is exactly the
scale-`s` Schur load. -/
theorem profilePrimalHattedRowPartial_self (P : Measure (CoeffSpace d))
    {q : Mat d} (hq : q.PosDef) (h : Mat d) (s : ℤ) (Pcen Qcen : Vec d) :
    profilePrimalHattedRowPartial P q h s s Pcen Qcen =
      profileSchurLoad (profileHattedBlock h (adaptedMean P q s)) Pcen Qcen := by
  rw [profilePrimalHattedRowPartial, Finset.Icc_self, Finset.sum_singleton,
    avsum_alignedIndex_self hq s, adaptedCellAt_zero]
  have hweight : profileRowWeight s s = 1 := by
    rw [profileRowWeight]
    norm_num
  rw [hweight, one_mul]
  rfl

/-- The same statement for the coefficient-transpose row. -/
theorem profileAdjointHattedRowPartial_self (P : Measure (CoeffSpace d))
    {q : Mat d} (hq : q.PosDef) (h : Mat d) (s : ℤ) (Pcen Qcen : Vec d) :
    profileAdjointHattedRowPartial P q h s s Pcen Qcen =
      profileSchurLoad (profileHattedAdjointBlock h (adaptedMean P q s))
        Pcen Qcen := by
  rw [profileAdjointHattedRowPartial, Finset.Icc_self, Finset.sum_singleton,
    avsum_alignedIndex_self hq s, adaptedCellAt_zero]
  have hweight : profileRowWeight s s = 1 := by
    rw [profileRowWeight]
    norm_num
  rw [hweight, one_mul]
  rfl

/-- **The scale-row order**: the scale-`s` Schur load is dominated by the primal
all-earlier hatted row, because the scale-`s` row is the single cell `U_s`. -/
theorem profileSchurLoad_le_profilePrimalHattedEarlierRow
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.PosDef) (h : Mat d)
    (s : ℤ) (Pcen Qcen : Vec d) :
    ENNReal.ofReal
        (profileSchurLoad (profileHattedBlock h (adaptedMean P q s)) Pcen Qcen) ≤
      profilePrimalHattedEarlierRow P q h s Pcen Qcen := by
  refine le_iSup_of_le s (le_of_eq ?_)
  rw [profilePrimalHattedRowPartial_self P hq h s Pcen Qcen]

/-- The coefficient-transpose scale-row order. -/
theorem profileSchurLoad_le_profileAdjointHattedEarlierRow
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.PosDef) (h : Mat d)
    (s : ℤ) (Pcen Qcen : Vec d) :
    ENNReal.ofReal
        (profileSchurLoad (profileHattedAdjointBlock h (adaptedMean P q s))
          Pcen Qcen) ≤
      profileAdjointHattedEarlierRow P q h s Pcen Qcen := by
  refine le_iSup_of_le s (le_of_eq ?_)
  rw [profileAdjointHattedRowPartial_self P hq h s Pcen Qcen]

/-- The root of the scale-`s` Schur load is dominated by the root of the primal
all-earlier hatted row. -/
theorem sqrt_profileSchurLoad_le_profilePrimalHattedEarlierRow_rpow
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.PosDef) (h : Mat d)
    (s : ℤ) (Pcen Qcen : Vec d) :
    ENNReal.ofReal
        (Real.sqrt
          (profileSchurLoad (profileHattedBlock h (adaptedMean P q s))
            Pcen Qcen)) ≤
      profilePrimalHattedEarlierRow P q h s Pcen Qcen ^ (1 / 2 : ℝ) := by
  have hbase := profileSchurLoad_le_profilePrimalHattedEarlierRow P hq h s Pcen Qcen
  have hrpow :
      ENNReal.ofReal
          (profileSchurLoad (profileHattedBlock h (adaptedMean P q s))
            Pcen Qcen) ^ (1 / 2 : ℝ) ≤
        profilePrimalHattedEarlierRow P q h s Pcen Qcen ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow hbase (by norm_num)
  rwa [Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg
      (profileSchurLoad_nonneg (profileHattedBlock h (adaptedMean P q s))
        Pcen Qcen) (by norm_num)]

/-- The coefficient-transpose form of the scale-row root order. -/
theorem sqrt_profileSchurLoad_le_profileAdjointHattedEarlierRow_rpow
    (P : Measure (CoeffSpace d)) {q : Mat d} (hq : q.PosDef) (h : Mat d)
    (s : ℤ) (Pcen Qcen : Vec d) :
    ENNReal.ofReal
        (Real.sqrt
          (profileSchurLoad (profileHattedAdjointBlock h (adaptedMean P q s))
            Pcen Qcen)) ≤
      profileAdjointHattedEarlierRow P q h s Pcen Qcen ^ (1 / 2 : ℝ) := by
  have hbase := profileSchurLoad_le_profileAdjointHattedEarlierRow P hq h s Pcen Qcen
  have hrpow :
      ENNReal.ofReal
          (profileSchurLoad (profileHattedAdjointBlock h (adaptedMean P q s))
            Pcen Qcen) ^ (1 / 2 : ℝ) ≤
        profileAdjointHattedEarlierRow P q h s Pcen Qcen ^ (1 / 2 : ℝ) :=
    ENNReal.rpow_le_rpow hbase (by norm_num)
  rwa [Real.sqrt_eq_rpow,
    ← ENNReal.ofReal_rpow_of_nonneg
      (profileSchurLoad_nonneg (profileHattedAdjointBlock h (adaptedMean P q s))
        Pcen Qcen) (by norm_num)]

/-! ## The annealed cutoff-defect means -/

/-- The annealed cutoff-defect mean `E[((φ-1)X_t)_{U_t}]` of the primal doubled
optimizer state, taken slotwise. -/
@[expose]
def profilePrimalCutoffMean (P : Measure (CoeffSpace d)) {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (sample : CoeffSpace d → CoeffSpace d)
    (cut : Vec d → ℝ) (p r : Vec d) : BlockVec d :=
  ((fun i ↦ ∫ a, volumeAverageVec (adaptedCell q t)
      (fun x ↦ (cut x - 1) • (diagonalWeakState hq t (sample a) p r x).1) i ∂P),
    fun i ↦ ∫ a, volumeAverageVec (adaptedCell q t)
      (fun x ↦ (cut x - 1) • (diagonalWeakState hq t (sample a) p r x).2) i ∂P)

/-- The annealed cutoff-defect mean of the coefficient-transpose doubled
optimizer state. -/
@[expose]
def profileAdjointCutoffMean (P : Measure (CoeffSpace d)) {q : Mat d}
    (hq : q.PosDef) (t : ℤ) (sample : CoeffSpace d → CoeffSpace d)
    (cut : Vec d → ℝ) (p r : Vec d) : BlockVec d :=
  ((fun i ↦ ∫ a, volumeAverageVec (adaptedCell q t)
      (fun x ↦ (cut x - 1) •
        (diagonalWeakAdjointState hq t (sample a) p r x).1) i ∂P),
    fun i ↦ ∫ a, volumeAverageVec (adaptedCell q t)
      (fun x ↦ (cut x - 1) •
        (diagonalWeakAdjointState hq t (sample a) p r x).2) i ∂P)

/-! ## The boundary-mean term -/

end

end HCPolySupport.HighContrast.Response
