/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRecentMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRowOscillationSum
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRecentPointwise
public import LeanPool.HighContrastHomogenization.Provider.Quenched.AlignedSubdivisionVariance
public import LeanPool.HighContrastHomogenization.Provider.PortableHistory.MajorizationSize

/-!
# High-contrast homogenization: Provider.Quenched.SmallContrastWeakCellVariance

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The recent cell sums by per-scale variances

The weighted recent cell sum of the weak-norm split is bounded in `L²(P)` by
the per-scale single-cell fluctuation carriers — the same
`lqSchattenSize`-carriers as the aligned-subdivision concentration — plus the
deterministic mean drops, with the geometric weights of the sum.  This is the
first (variance) group of the printed display HC (3.68),
with no window multiplier and no history.
-/

namespace HCPolySupport.HighContrast.Quenched

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The per-scale single-cell fluctuation carrier in normalization `F`. -/
@[expose]
def scaleVariance (P : Measure (CoeffSpace d)) (q : Mat d) (F : BlockMat d)
    (k : ℤ) : ℝ≥0∞ :=
  eLpNorm
    (fun a => schattenSize 2
      (blockSub (coarseBlock (adaptedCell q k) a) (adaptedMean P q k)) F)
    2 P

/-- Squares compare iff the values compare. -/
theorem le_of_sq_le_sq {a b : ℝ≥0∞}
    (h : a ^ (2 : ℕ) ≤ b ^ (2 : ℕ)) : a ≤ b :=
  (ENNReal.pow_le_pow_left_iff two_ne_zero).mp h

/-- The square of the two-norm of a nonnegative statistic. -/
theorem eLpNorm_two_real_sq {P : Measure (CoeffSpace d)}
    {f : CoeffSpace d → ℝ} (hf : ∀ a, 0 ≤ f a) (hfm : AEStronglyMeasurable f P) :
    eLpNorm f 2 P ^ (2 : ℕ) =
      ∫⁻ a, ENNReal.ofReal (f a ^ 2) ∂P := by
  have h1 : ∀ a, ‖f a‖ₑ ^ (2 : ℝ) = ENNReal.ofReal (f a ^ 2) := by
    intro a
    rw [Real.enorm_eq_ofReal (hf a),
      ENNReal.ofReal_rpow_of_nonneg (hf a) (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    rw [← Real.rpow_natCast (f a) 2]
    norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hfm]
  simp only [ENNReal.toReal_ofNat]
  rw [lintegral_congr h1, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

/-- Minkowski on the normalized finite average. -/
theorem sqrt_avsum_sq_add {ι : Type*} (Z : Finset ι)
    (f g : ι → ℝ) :
    Real.sqrt (Response.avsum Z fun z => (f z + g z) ^ 2) ≤
      Real.sqrt (Response.avsum Z fun z => f z ^ 2) +
        Real.sqrt (Response.avsum Z fun z => g z ^ 2) := by
  have hf2 : 0 ≤ Response.avsum Z fun z => f z ^ 2 :=
    Response.avsum_nonneg (fun z _ => sq_nonneg _)
  have hg2 : 0 ≤ Response.avsum Z fun z => g z ^ 2 :=
    Response.avsum_nonneg (fun z _ => sq_nonneg _)
  have hcs := Response.avsum_mul_le_sqrt_mul_sqrt Z f g
  have hsplit : (Response.avsum Z fun z => (f z + g z) ^ 2) =
      (Response.avsum Z fun z => f z ^ 2) +
        2 * Response.avsum Z (fun z => f z * g z) +
        Response.avsum Z fun z => g z ^ 2 := by
    simp only [Response.avsum]
    have hexp : ∑ z ∈ Z, (f z + g z) ^ 2 =
        (∑ z ∈ Z, f z ^ 2) + 2 * (∑ z ∈ Z, f z * g z) +
          ∑ z ∈ Z, g z ^ 2 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [hexp]
    ring
  have hsq : (Response.avsum Z fun z => (f z + g z) ^ 2) ≤
      (Real.sqrt (Response.avsum Z fun z => f z ^ 2) +
        Real.sqrt (Response.avsum Z fun z => g z ^ 2)) ^ 2 := by
    rw [hsplit, add_sq, Real.sq_sqrt hf2, Real.sq_sqrt hg2]
    have habs : Response.avsum Z (fun z => f z * g z) ≤
        Real.sqrt (Response.avsum Z fun z => f z ^ 2) *
          Real.sqrt (Response.avsum Z fun z => g z ^ 2) := hcs
    linarith only [habs]
  calc
    Real.sqrt (Response.avsum Z fun z => (f z + g z) ^ 2) ≤
        Real.sqrt ((Real.sqrt (Response.avsum Z fun z => f z ^ 2) +
          Real.sqrt (Response.avsum Z fun z => g z ^ 2)) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    _ = _ := by
      rw [Real.sqrt_sq (by positivity)]

/-- Stationarity transport of the centred aligned-cell carrier (clone of the
aligned-subdivision transport). -/
theorem eLpNorm_schattenTwo_adaptedCellAt_eq
    {P : Measure (CoeffSpace d)} (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hq : IsRoundedGrid l q) {j : ℤ} (hlj : l ≤ j)
    (E F : BlockMat d) (hE : IsSymmetricBlockMat E) (w : Fin d → ℤ) :
    eLpNorm
        (fun a ↦ schattenSize 2
          (blockSub (coarseBlock (adaptedCellAt q j w) a) E) F) 2 P =
      eLpNorm
        (fun a ↦ schattenSize 2
          (blockSub (coarseBlock (adaptedCell q j) a) E) F) 2 P := by
  obtain ⟨z, hz⟩ := Recurrence.exists_intVec_adaptedCellCenter hq hlj w
  have hblock : ∀ a : CoeffSpace d,
      coarseBlock (adaptedCellAt q j w) a =
        coarseBlock (adaptedCell q j) (translateCoeff z a) :=
    fun a ↦ Recurrence.adaptedResponse_eq_coarseBlock_translateCoeff hz a
  let X : CoeffSpace d → BlockMat d :=
    fun a ↦ blockSub (coarseBlock (adaptedCell q j) a) E
  have hfun :
      (fun a : CoeffSpace d ↦
          schattenSize 2
            (blockSub (coarseBlock (adaptedCellAt q j w) a) E) F) =
        (fun a : CoeffSpace d ↦ schattenSize 2 (X a) F) ∘
          translateCoeff z := by
    funext a
    simp only [Function.comp_apply, X, hblock a]
  have hXsymm : ∀ a, IsSymmetricBlockMat (X a) := fun a ↦
    isSymmetricBlockMat_blockSub
      (isSymmetricBlockMat_coarseBlock (adaptedCell q j) a) hE
  have hXmeas : ∀ α β : BlockCoord d,
      AEStronglyMeasurable (fun a ↦ toFullBlockMat (X a) α β) P := by
    intro α β
    have hmA : AEStronglyMeasurable
        (fun a : CoeffSpace d ↦
          toFullBlockMat (coarseBlock (adaptedCell q j) a) α β) P := by
      exact Recurrence.hasMeasurableCoarseBlock_adaptedCell P
        (Recurrence.posDef_of_isRoundedGrid hq) j α β
    have hmE : AEStronglyMeasurable
        (fun _ : CoeffSpace d ↦ toFullBlockMat E α β) P :=
      aestronglyMeasurable_const
    have hm := hmA.sub hmE
    simpa only [X, Recurrence.toFullBlockMat_blockSub_apply] using! hm
  have hmeas : AEStronglyMeasurable
      (fun a : CoeffSpace d ↦ schattenSize 2 (X a) F) P :=
    Transport.aestronglyMeasurable_schattenSize (P := P) (A := X) (F := F)
      (by exact even_two) hXsymm hXmeas
  rw [hfun]
  exact eLpNorm_comp_measurePreserving hmeas
    (Recurrence.measurePreserving_translateCoeff hstat z)

private theorem diagonal_cell_defect_pointwise_split
    {P : Measure (CoeffSpace d)} {q : Mat d} {k t : ℤ}
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F)
    {B : ℝ} (hB : B =
      blockSize (blockSub (adaptedMean P q k) (adaptedMean P q t)) F)
    (hB0 : 0 ≤ B)
    {A : (Fin d → ℤ) → CoeffSpace d → ℝ}
    (hA : A = fun w a => schattenSize 2
      (blockSub (coarseBlock (adaptedCellAt q k w) a) (adaptedMean P q k)) F)
    {C : CoeffSpace d → ℝ}
    (hC : C = fun a => schattenSize 2
      (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t)) F)
    (hC0 : ∀ a, 0 ≤ C a) :
    ∀ a, Response.diagonalWeakCellDefect q k t F a ≤
      Real.sqrt (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2) +
        (B + C a) := by
  classical
  have hpoint : ∀ a, Response.diagonalWeakCellDefect q k t F a ≤
      Real.sqrt (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2) +
        (B + C a) := by
    intro a
    rw [Response.diagonalWeakCellDefect_eq]
    have hterm : ∀ w ∈ Response.alignedIndex q k t,
        blockSize
            (blockSub (coarseBlock (adaptedCellAt q k w) a)
              (coarseBlock (adaptedCell q t) a)) F ^ 2 ≤
          (A w a + (B + C a)) ^ 2 := by
      intro w _hw
      have hsymW : IsSymmetricBlockMat
          (coarseBlock (adaptedCellAt q k w) a) :=
        isSymmetricBlockMat_coarseBlock _ _
      have hsymT : IsSymmetricBlockMat (coarseBlock (adaptedCell q t) a) :=
        isSymmetricBlockMat_coarseBlock _ _
      have hsymMk : IsSymmetricBlockMat (adaptedMean P q k) :=
        Recurrence.isSymmetricBlockMat_adaptedMean P q k
      have hsymMt : IsSymmetricBlockMat (adaptedMean P q t) :=
        Recurrence.isSymmetricBlockMat_adaptedMean P q t
      have htri1 := Response.blockSize_blockSub_triangle
        hsymW hsymMk hsymT hFsym hFpd
      have htri2 := Response.blockSize_blockSub_triangle
        hsymMk hsymMt hsymT hFsym hFpd
      have hcomm := Response.blockSize_blockSub_comm hsymMt hsymT hFsym hFpd
      have h1 : blockSize
          (blockSub (coarseBlock (adaptedCellAt q k w) a)
            (adaptedMean P q k)) F ≤ A w a := by
        rw [hA]
        exact PortableHistory.blockSize_le_schattenSize
          (isSymmetricBlockMat_blockSub hsymW hsymMk) hFsym hFpd
          (by norm_num)
      have h3 : blockSize
          (blockSub (adaptedMean P q t)
            (coarseBlock (adaptedCell q t) a)) F ≤ C a := by
        rw [hC, hcomm]
        exact PortableHistory.blockSize_le_schattenSize
          (isSymmetricBlockMat_blockSub hsymT hsymMt) hFsym hFpd
          (by norm_num)
      have hle : blockSize
          (blockSub (coarseBlock (adaptedCellAt q k w) a)
            (coarseBlock (adaptedCell q t) a)) F ≤
          A w a + (B + C a) := by
        calc
          blockSize
              (blockSub (coarseBlock (adaptedCellAt q k w) a)
                (coarseBlock (adaptedCell q t) a)) F ≤
              blockSize
                  (blockSub (coarseBlock (adaptedCellAt q k w) a)
                    (adaptedMean P q k)) F +
                blockSize
                  (blockSub (adaptedMean P q k)
                    (coarseBlock (adaptedCell q t) a)) F := htri1
          _ ≤ blockSize
                  (blockSub (coarseBlock (adaptedCellAt q k w) a)
                    (adaptedMean P q k)) F +
                (blockSize
                    (blockSub (adaptedMean P q k) (adaptedMean P q t))
                    F +
                  blockSize
                    (blockSub (adaptedMean P q t)
                      (coarseBlock (adaptedCell q t) a)) F) :=
            add_le_add le_rfl htri2
          _ ≤ A w a + (B + C a) := by
            rw [hB]
            exact add_le_add h1 (add_le_add le_rfl h3)
      have hnn : 0 ≤ blockSize
          (blockSub (coarseBlock (adaptedCellAt q k w) a)
            (coarseBlock (adaptedCell q t) a)) F :=
        PortableHistory.blockSize_nonneg
          (isSymmetricBlockMat_blockSub hsymW hsymT) hFsym hFpd
      exact pow_le_pow_left₀ hnn hle 2
    calc
      Real.sqrt
          (Response.avsum (Response.alignedIndex q k t) fun w =>
            blockSize
                (blockSub (coarseBlock (adaptedCellAt q k w) a)
                  (coarseBlock (adaptedCell q t) a)) F ^ 2) ≤
          Real.sqrt
            (Response.avsum (Response.alignedIndex q k t) fun w =>
              (A w a + (B + C a)) ^ 2) := by
        refine Real.sqrt_le_sqrt (Response.avsum_le_avsum hterm)
      _ ≤ Real.sqrt
            (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2) +
          Real.sqrt
            (Response.avsum (Response.alignedIndex q k t) fun w => (B + C a) ^ 2) :=
        sqrt_avsum_sq_add _ _ _
      _ ≤ Real.sqrt
            (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2) +
          (B + C a) := by
        refine add_le_add le_rfl ?_
        have hconst : Response.avsum (Response.alignedIndex q k t)
            (fun _ => (B + C a) ^ 2) ≤ (B + C a) ^ 2 := by
          rcases Finset.eq_empty_or_nonempty (Response.alignedIndex q k t) with
            hE | hNE
          · rw [hE, Response.avsum]
            simp only [Finset.card_empty, Finset.sum_empty, mul_zero]
            positivity
          · exact le_of_eq (Response.avsum_const hNE _)
        calc
          Real.sqrt (Response.avsum (Response.alignedIndex q k t)
              fun _ => (B + C a) ^ 2) ≤
              Real.sqrt ((B + C a) ^ 2) := Real.sqrt_le_sqrt hconst
          _ = B + C a := Real.sqrt_sq (add_nonneg hB0 (hC0 a))
  exact hpoint

/-- **The per-scale cell defect in `L²`.**  The recent-cell defect at scale
`k` is bounded by the two single-cell fluctuation carriers plus the
deterministic mean drop. -/
theorem eLpNorm_diagonalWeakCellDefect_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q) {k t : ℤ}
    (hlk : l ≤ k)
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) :
    eLpNorm (fun a => Response.diagonalWeakCellDefect q k t F a) 2 P ≤
      scaleVariance P q F k + scaleVariance P q F t +
        ENNReal.ofReal
          (blockSize (blockSub (adaptedMean P q k) (adaptedMean P q t))
            F) := by
  classical
  have hq : q.PosDef := Recurrence.posDef_of_isRoundedGrid hgrid
  set B : ℝ :=
    blockSize (blockSub (adaptedMean P q k) (adaptedMean P q t)) F with hB
  have hB0 : 0 ≤ B :=
    PortableHistory.blockSize_nonneg
      (isSymmetricBlockMat_blockSub
        (Recurrence.isSymmetricBlockMat_adaptedMean P q k)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q t)) hFsym hFpd
  -- the pathwise scale decomposition
  set A : (Fin d → ℤ) → CoeffSpace d → ℝ := fun w a =>
    schattenSize 2
      (blockSub (coarseBlock (adaptedCellAt q k w) a) (adaptedMean P q k))
      F with hA
  set C : CoeffSpace d → ℝ := fun a =>
    schattenSize 2
      (blockSub (coarseBlock (adaptedCell q t) a) (adaptedMean P q t))
      F with hC
  have hA0 : ∀ w a, 0 ≤ A w a := fun w a =>
    Recurrence.zero_le_schattenNorm
      (isSymmetricBlockMat_normalizedBlock (F := F)
        (isSymmetricBlockMat_blockSub
          (isSymmetricBlockMat_coarseBlock _ _)
          (Recurrence.isSymmetricBlockMat_adaptedMean P q k))) _
  have hC0 : ∀ a, 0 ≤ C a := fun a =>
    Recurrence.zero_le_schattenNorm
      (isSymmetricBlockMat_normalizedBlock (F := F)
        (isSymmetricBlockMat_blockSub
          (isSymmetricBlockMat_coarseBlock _ _)
          (Recurrence.isSymmetricBlockMat_adaptedMean P q t))) _
  have hpoint := diagonal_cell_defect_pointwise_split hFsym hFpd hB hB0 hA hC hC0
  -- measurability of the three parts
  have hmeasA : ∀ w : Fin d → ℤ, AEStronglyMeasurable (A w) P := by
    intro w
    rw [hA]
    refine Transport.aestronglyMeasurable_schattenSize (by exact even_two)
      (fun a => isSymmetricBlockMat_blockSub
        (isSymmetricBlockMat_coarseBlock _ _)
        (Recurrence.isSymmetricBlockMat_adaptedMean P q k)) ?_
    intro α β
    have hmA : AEStronglyMeasurable
        (fun a : CoeffSpace d ↦
          toFullBlockMat (coarseBlock (adaptedCellAt q k w) a) α β) P :=
      Recurrence.hasMeasurableCoarseBlock_adaptedCellAt P hq k w α β
    have hm := hmA.sub
      (aestronglyMeasurable_const
        (b := toFullBlockMat (adaptedMean P q k) α β))
    simpa only [Recurrence.toFullBlockMat_blockSub_apply] using! hm
  have hmeasG1 : AEStronglyMeasurable
      (fun a => Real.sqrt
        (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2)) P := by
    refine Continuous.comp_aestronglyMeasurable Real.continuous_sqrt ?_
    have hsum : AEStronglyMeasurable
        (fun a => ∑ w ∈ Response.alignedIndex q k t, A w a ^ 2) P := by
      refine (Finset.aestronglyMeasurable_sum (Response.alignedIndex q k t)
        (f := fun w => fun a => A w a ^ 2) (fun w _ =>
          ((hmeasA w).mul (hmeasA w)).congr
            (_root_.Filter.Eventually.of_forall fun a => by
              show A w a * A w a = A w a ^ 2
              rw [pow_two]))).congr
        (_root_.Filter.Eventually.of_forall fun a => by rw [Finset.sum_apply])
    exact (aestronglyMeasurable_const.mul hsum).congr
      (_root_.Filter.Eventually.of_forall fun a => rfl)
  -- the L² triangle
  have hmono : eLpNorm (fun a => Response.diagonalWeakCellDefect q k t F a) 2 P ≤
      eLpNorm
        ((fun a => Real.sqrt
            (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2)) +
          ((fun _ => B) + C)) 2 P := by
    refine eLpNorm_mono
      (Response.aemeasurable_diagonalWeakCellDefect hq k t hFsym hFpd).aestronglyMeasurable
      fun a => ?_
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Response.diagonalWeakCellDefect_nonneg q k t F a)]
    calc
      Response.diagonalWeakCellDefect q k t F a ≤
          Real.sqrt
              (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2) +
            (B + C a) := hpoint a
      _ ≤ ‖(Real.sqrt
              (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2) +
            (B + C a))‖ := le_abs_self _
  have htri : eLpNorm
      ((fun a => Real.sqrt
          (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2)) +
        ((fun _ => B) + C)) 2 P ≤
      eLpNorm (fun a => Real.sqrt
          (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2)) 2 P +
        (eLpNorm (fun _ : CoeffSpace d => B) 2 P + eLpNorm C 2 P) := by
    refine le_trans (eLpNorm_add_le (by norm_num)) ?_
    exact add_le_add le_rfl (eLpNorm_add_le (by norm_num))
  -- the three parts
  have hpart1 : eLpNorm (fun a => Real.sqrt
      (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2)) 2 P ≤
      scaleVariance P q F k := by
    refine le_of_sq_le_sq ?_
    rw [eLpNorm_two_real_sq (fun a => Real.sqrt_nonneg _) hmeasG1]
    have hsq : ∀ a, Real.sqrt
        (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2) ^ 2 =
        Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2 := fun a =>
      Real.sq_sqrt (Response.avsum_nonneg (fun w _ => sq_nonneg _))
    rw [lintegral_congr fun a => congrArg ENNReal.ofReal (hsq a)]
    have hbound : ∫⁻ a, ENNReal.ofReal
        (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2) ∂P ≤
        scaleVariance P q F k ^ (2 : ℕ) := by
      have hcard0 : (0 : ℝ) ≤ ((Response.alignedIndex q k t).card : ℝ)⁻¹ := by
        positivity
      have hexp : ∀ a, ENNReal.ofReal
          (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2) =
          ENNReal.ofReal (((Response.alignedIndex q k t).card : ℝ)⁻¹) *
            ∑ w ∈ Response.alignedIndex q k t,
              ENNReal.ofReal (A w a ^ 2) := by
        intro a
        rw [Response.avsum, ENNReal.ofReal_mul hcard0,
          ENNReal.ofReal_sum_of_nonneg fun w _ => sq_nonneg _]
      rw [lintegral_congr hexp,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_finsetSum']
      · have hper : ∀ w ∈ Response.alignedIndex q k t,
            ∫⁻ a, ENNReal.ofReal (A w a ^ 2) ∂P =
              scaleVariance P q F k ^ (2 : ℕ) := by
          intro w _
          have h1 : eLpNorm (A w) 2 P = scaleVariance P q F k := by
            simp only [hA]
            exact eLpNorm_schattenTwo_adaptedCellAt_eq hstat hgrid hlk
              (adaptedMean P q k) F
              (Recurrence.isSymmetricBlockMat_adaptedMean P q k) w
          rw [← eLpNorm_two_real_sq (hA0 w) (hmeasA w), h1]
        rw [Finset.sum_congr rfl hper]
        rw [Finset.sum_const, nsmul_eq_mul]
        rcases Finset.eq_empty_or_nonempty (Response.alignedIndex q k t) with
          hE | hNE
        · rw [hE]
          simp
        · have hcard : (0 : ℝ) < ((Response.alignedIndex q k t).card : ℝ) := by
            exact_mod_cast Finset.card_pos.mpr hNE
          rw [show ENNReal.ofReal
              (((Response.alignedIndex q k t).card : ℝ)⁻¹) *
              (((Response.alignedIndex q k t).card : ℕ) *
                scaleVariance P q F k ^ (2 : ℕ)) =
              (ENNReal.ofReal (((Response.alignedIndex q k t).card : ℝ)⁻¹) *
                ((Response.alignedIndex q k t).card : ℕ)) *
                scaleVariance P q F k ^ (2 : ℕ) from by ring]
          have hone : ENNReal.ofReal
              (((Response.alignedIndex q k t).card : ℝ)⁻¹) *
              (((Response.alignedIndex q k t).card : ℕ) : ℝ≥0∞) = 1 := by
            rw [← ENNReal.ofReal_natCast ((Response.alignedIndex q k t).card),
              ← ENNReal.ofReal_mul hcard0,
              inv_mul_cancel₀ (ne_of_gt hcard), ENNReal.ofReal_one]
          rw [hone, one_mul]
      · intro w _
        exact (ENNReal.measurable_ofReal.comp_aemeasurable
          (((hmeasA w).aemeasurable.mul
            (hmeasA w).aemeasurable).congr
            (_root_.Filter.Eventually.of_forall fun a => by
              show A w a * A w a = A w a ^ 2
              rw [pow_two])))
    exact hbound
  have hpart2 : eLpNorm (fun _ : CoeffSpace d => B) 2 P ≤
      ENNReal.ofReal B := by
    have hP0 : (P : Measure (CoeffSpace d)) ≠ 0 := by
      intro h0
      have huniv := measure_univ (μ := P)
      rw [h0] at huniv
      simp at huniv
    rw [eLpNorm_const _ (by norm_num) hP0]
    simp only [measure_univ, ENNReal.one_rpow, mul_one]
    rw [Real.enorm_eq_ofReal hB0]
  have hpart3 : eLpNorm C 2 P = scaleVariance P q F t := by
    simp only [hC]
    rfl
  calc
    eLpNorm (fun a => Response.diagonalWeakCellDefect q k t F a) 2 P ≤
        eLpNorm (fun a => Real.sqrt
            (Response.avsum (Response.alignedIndex q k t) fun w => A w a ^ 2)) 2 P +
          (eLpNorm (fun _ : CoeffSpace d => B) 2 P + eLpNorm C 2 P) :=
      hmono.trans htri
    _ ≤ scaleVariance P q F k +
          (ENNReal.ofReal B + scaleVariance P q F t) :=
      add_le_add hpart1 (add_le_add hpart2 (le_of_eq hpart3))
    _ = scaleVariance P q F k + scaleVariance P q F t +
          ENNReal.ofReal B := by ring

/-- **The recent cell sum in `L²`.**  The weighted recent cell sum is
bounded by the weighted per-scale variance carriers and mean drops. -/
theorem eLpNorm_diagonalWeakCellSum_le_variance [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P)
    {l : ℤ} {q : Mat d} (hgrid : IsRoundedGrid l q) {t : ℤ} (H : ℕ)
    (hstart : l ≤ t - (H : ℤ))
    {F : BlockMat d} (hFsym : IsSymmetricBlockMat F)
    (hFpd : Book.Ch02.BlockPosDef F) :
    eLpNorm (fun a => Response.diagonalWeakCellSum q t H (1 / 2) F a) 2 P ≤
      ∑ j ∈ Finset.range (H + 1),
        ENNReal.ofReal ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ))) *
          (scaleVariance P q F (t - (j : ℤ)) + scaleVariance P q F t +
            ENNReal.ofReal
              (blockSize
                (blockSub (adaptedMean P q (t - (j : ℤ)))
                  (adaptedMean P q t)) F)) := by
  classical
  have hfun : (fun a => Response.diagonalWeakCellSum q t H (1 / 2) F a) =
      ∑ j ∈ Finset.range (H + 1),
        (fun a => (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) *
          Response.diagonalWeakCellDefect q (t - (j : ℤ)) t F a) := by
    funext a
    rw [Response.diagonalWeakCellSum]
    rw [Finset.sum_apply]
  rw [hfun]
  refine le_trans
    (eLpNorm_sum_le (by norm_num)) ?_
  refine Finset.sum_le_sum fun j hj => ?_
  have hjH : (j : ℤ) ≤ (H : ℤ) := by
    exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hsmul : (fun a => (3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ)) *
      Response.diagonalWeakCellDefect q (t - (j : ℤ)) t F a) =
      ((3 : ℝ) ^ (-(1 / 2 : ℝ) * (j : ℝ))) •
        fun a => Response.diagonalWeakCellDefect q (t - (j : ℤ)) t F a := by
    funext a
    simp [smul_eq_mul]
  rw [hsmul, eLpNorm_const_smul]
  rw [Real.enorm_eq_ofReal hw0]
  refine mul_le_mul' le_rfl ?_
  exact eLpNorm_diagonalWeakCellDefect_le hstat hgrid
    (by omega) hFsym hFpd

end

end HCPolySupport.HighContrast.Quenched
