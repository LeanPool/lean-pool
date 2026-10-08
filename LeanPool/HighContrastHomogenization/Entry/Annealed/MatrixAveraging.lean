/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Annealed.AveragingTransport
public import LeanPool.HighContrastHomogenization.Entry.Analysis.PositiveGapSupport
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenHolderInequalities
public import LeanPool.HighContrastHomogenization.Entry.Analysis.MatrixMomentSum

/-!
# High-contrast homogenization: Entry.Annealed.MatrixAveraging

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite-range matrix averaging

`l.fixed.geometry.matrix.averaging`. Positive homogeneity and
finite-sum Minkowski turn the exact independent matrix sum estimate into the
class-average bound. The original average is a convex combination of these
class averages; Cauchy–Schwarz over the residue palette gives `3^(d/2)`.
Empty classes have weight zero and are handled before any inverse cancellation.
The full endpoint derives all moments, centering, and stationarity transport
from the standing law, and certifies the positive definite inverse square root
of the deterministic normalizer before using its congruence form.
-/

open HCPolySupport.HighContrast (CoeffSpace UnitSeparated adaptedCellCenter adaptedMean blockSub
  coarseBlock matSqrt normalizedBlock)
namespace HCPolySupport.HighContrast.Annealed

open MeasureTheory

open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## Deterministic positive homogeneity -/

private theorem blockSub_ofFullBlockMat (A B : FullBlockMat d) :
    blockSub (ofFullBlockMat A) (ofFullBlockMat B) = ofFullBlockMat (A - B) := rfl

/-- **Deterministic positive homogeneity.**  `|c • H|_{S_N} = |c| |H|_{S_N}` for a symmetric
`H` and real `N ≥ 1`. -/
theorem absSchattenNorm_smul {H : BlockMat d} (hH : (toFullBlockMat H).IsHermitian)
    {N : ℝ} (hN : 1 ≤ N) (c : ℝ) :
    absSchattenNorm N (ofFullBlockMat (c • toFullBlockMat H)) = |c| * absSchattenNorm N H := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hcnn : (0 : ℝ) ≤ |c| := abs_nonneg c
  have hTnn : (0 : ℝ) ≤ Matrix.trace (cfc (fun x : ℝ => |x| ^ N) (toFullBlockMat H)) := by
    rw [Analysis.trace_cfc_abs_rpow_eq_sum hH hN]
    exact Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _
  have hcont : ContinuousOn (fun x : ℝ => |x| ^ N) Set.univ := by
    refine Continuous.continuousOn ?_
    exact (Real.continuous_rpow_const (le_of_lt hNpos)).comp continuous_abs
  -- move the scalar inside the functional calculus
  have hsa : IsSelfAdjoint (toFullBlockMat H) := hH
  have hfun : (fun x : ℝ => |c * x| ^ N) = fun x : ℝ => |c| ^ N * |x| ^ N := by
    funext x
    rw [abs_mul, Real.mul_rpow (abs_nonneg c) (abs_nonneg x)]
  have hmove : cfc (fun x : ℝ => |c * x| ^ N) (toFullBlockMat H)
      = cfc (fun x : ℝ => |x| ^ N) (c • toFullBlockMat H) :=
    cfc_comp_const_mul (R := ℝ) c (fun x : ℝ => |x| ^ N) (toFullBlockMat H)
      (hcont.mono (Set.subset_univ _)) hsa
  have hpull : cfc (fun x : ℝ => |c| ^ N * |x| ^ N) (toFullBlockMat H)
      = |c| ^ N • cfc (fun x : ℝ => |x| ^ N) (toFullBlockMat H) :=
    cfc_const_mul (R := ℝ) (|c| ^ N) (fun x : ℝ => |x| ^ N) (toFullBlockMat H)
      (hcont.mono (Set.subset_univ _))
  have hstep : cfc (fun x : ℝ => |x| ^ N) (c • toFullBlockMat H)
      = |c| ^ N • cfc (fun x : ℝ => |x| ^ N) (toFullBlockMat H) := by
    rw [← hmove, hfun, hpull]
  unfold absSchattenNorm
  rw [toFullBlockMat_ofFullBlockMat, hstep, Matrix.trace_smul, smul_eq_mul,
    Real.mul_rpow (Real.rpow_nonneg hcnn N) hTnn,
    ← Real.rpow_mul hcnn, mul_inv_cancel₀ (ne_of_gt hNpos), Real.rpow_one]

/-- `|0|_{S_N} = 0`; the `c = 0` instance of `absSchattenNorm_smul`. -/
theorem absSchattenNorm_ofFullBlockMat_zero {N : ℝ} (hN : 1 ≤ N) :
    absSchattenNorm N (ofFullBlockMat (0 : FullBlockMat d)) = 0 := by
  have hH : (toFullBlockMat (ofFullBlockMat (0 : FullBlockMat d))).IsHermitian := by
    rw [toFullBlockMat_ofFullBlockMat]
    exact Matrix.isHermitian_zero
  have h := absSchattenNorm_smul hH hN 0
  rw [toFullBlockMat_ofFullBlockMat, smul_zero] at h
  simpa using h

/-! ## Law-level positive homogeneity -/

/-- **Positive homogeneity** for the mixed norm (group 5 item 1). -/
theorem lqSchattenNorm_smul {P : Measure (CoeffSpace d)} {N : ℝ} (hN : 1 ≤ N)
    {H : CoeffSpace d → BlockMat d} (hH : SchattenMemLp P N H) (c : ℝ) :
    lqSchattenNorm P N (fun a => ofFullBlockMat (c • toFullBlockMat (H a)))
      = |c| * lqSchattenNorm P N H := by
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
  have hcnn : (0 : ℝ) ≤ |c| := abs_nonneg c
  have hInn : (0 : ℝ) ≤ ∫ a, absSchattenNorm N (H a) ^ N ∂P := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hH.symmetric] with a ha
    change (0 : ℝ) ≤ absSchattenNorm N (H a) ^ N
    exact Real.rpow_nonneg
      (Analysis.absSchattenNorm_nonneg ((Analysis.toFullBlockMat_isHermitian_iff _).2 ha) hN) N
  have hpoint : (fun a => absSchattenNorm N (ofFullBlockMat (c • toFullBlockMat (H a))) ^ N)
      =ᵐ[P] fun a => |c| ^ N * absSchattenNorm N (H a) ^ N := by
    filter_upwards [hH.symmetric] with a ha
    have hHa := (Analysis.toFullBlockMat_isHermitian_iff (H a)).2 ha
    rw [absSchattenNorm_smul hHa hN c,
      Real.mul_rpow hcnn (Analysis.absSchattenNorm_nonneg hHa hN)]
  unfold lqSchattenNorm
  rw [integral_congr_ae hpoint, integral_const_mul,
    Real.mul_rpow (Real.rpow_nonneg hcnn N) hInn,
    ← Real.rpow_mul hcnn, mul_inv_cancel₀ (ne_of_gt hNpos), Real.rpow_one]

/-! ## Finite-sum Minkowski -/

/-- **Finite-sum Minkowski** for the mixed norm (group 5 item 2).  Induction on the finset,
exactly as `Analysis.lqSchattenNorm_sub_le` does for two terms.  The empty sum gives `0 ≤ 0`;
no nonemptiness premise is added. -/
theorem lqSchattenNorm_finset_sum_le {ι : Type*}
    {P : Measure (CoeffSpace d)} {N : ℝ} (hN : 1 ≤ N)
    (t : Finset ι) (H : ι → CoeffSpace d → BlockMat d)
    (hH : ∀ i ∈ t, SchattenMemLp P N (H i)) :
    lqSchattenNorm P N (fun a => ofFullBlockMat (∑ i ∈ t, toFullBlockMat (H i a)))
      ≤ ∑ i ∈ t, lqSchattenNorm P N (H i) := by
  classical
  induction t using Finset.cons_induction with
  | empty =>
      have hNpos : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN
      simp only [Finset.sum_empty]
      unfold lqSchattenNorm
      simp [absSchattenNorm_ofFullBlockMat_zero hN, Real.zero_rpow (ne_of_gt hNpos),
        Real.zero_rpow (inv_ne_zero (ne_of_gt hNpos))]
  | cons i₀ t hi₀ ih =>
      have hHt : ∀ i ∈ t, SchattenMemLp P N (H i) := fun i hi =>
        hH i (Finset.mem_cons_of_mem hi)
      have hHi₀ : SchattenMemLp P N (H i₀) := hH i₀ (Finset.mem_cons_self i₀ t)
      -- membership of the tail sum, and of its negative
      have hsum : SchattenMemLp P N
          (fun a => ofFullBlockMat (∑ i ∈ t, toFullBlockMat (H i a))) := by
        have := Source.memLqSchatten_finset_sum hN t (fun _ => (1 : ℝ)) H hHt
        simpa using this
      have hneg : SchattenMemLp P N
          (fun a => ofFullBlockMat (-(∑ i ∈ t, toFullBlockMat (H i a)))) := by
        have := Source.memLqSchatten_finset_sum hN t (fun _ => (-1 : ℝ)) H hHt
        simpa [Finset.sum_neg_distrib] using this
      -- rewrite the head-plus-tail sum as a `blockSub`
      have hshape : (fun a => ofFullBlockMat
            (∑ i ∈ Finset.cons i₀ t hi₀, toFullBlockMat (H i a)))
          = fun a => blockSub (H i₀ a)
              (ofFullBlockMat (-(∑ i ∈ t, toFullBlockMat (H i a)))) := by
        funext a
        rw [Finset.sum_cons]
        rw [← ofFullBlockMat_toFullBlockMat (H i₀ a), blockSub_ofFullBlockMat,
          toFullBlockMat_ofFullBlockMat, sub_neg_eq_add]
      have hnegnorm : lqSchattenNorm P N
          (fun a => ofFullBlockMat (-(∑ i ∈ t, toFullBlockMat (H i a))))
          = lqSchattenNorm P N (fun a => ofFullBlockMat (∑ i ∈ t, toFullBlockMat (H i a))) := by
        have h := lqSchattenNorm_smul hN hsum (-1)
        simp only [toFullBlockMat_ofFullBlockMat, neg_smul, one_smul, abs_neg, abs_one,
          one_mul] at h
        exact h
      rw [hshape, Finset.sum_cons]
      calc lqSchattenNorm P N (fun a => blockSub (H i₀ a)
              (ofFullBlockMat (-(∑ i ∈ t, toFullBlockMat (H i a)))))
          ≤ lqSchattenNorm P N (H i₀) +
              lqSchattenNorm P N
                (fun a => ofFullBlockMat (-(∑ i ∈ t, toFullBlockMat (H i a)))) :=
            Analysis.lqSchattenNorm_sub_le hN hHi₀ hneg
        _ = lqSchattenNorm P N (H i₀) +
              lqSchattenNorm P N
                (fun a => ofFullBlockMat (∑ i ∈ t, toFullBlockMat (H i a))) := by
            rw [hnegnorm]
        _ ≤ lqSchattenNorm P N (H i₀) + ∑ i ∈ t, lqSchattenNorm P N (H i) := by
            have := ih hHt
            linarith only [this]


private theorem inv_mul_rpow_half {n : ℝ} (hn : 0 < n) :
    n⁻¹ * n ^ ((1 : ℝ) / 2) = (n ^ ((1 : ℝ) / 2))⁻¹ := by
  rw [← Real.rpow_neg_one, ← Real.rpow_add hn]
  norm_num
  rw [Real.rpow_neg hn.le]

/-- A nonempty independent class with a common single-cell norm has the printed average bound. -/
theorem lqSchattenNorm_class_average_le {d : ℕ} {ι : Type*}
    (P : Measure (CoeffSpace d)) (hP : IsProbabilityMeasure P)
    {N : ℕ} (hN : 2 ≤ N) (hNeven : Even N)
    (C : Finset ι) (hC : C.Nonempty) (Y : ι → CoeffSpace d → BlockMat d)
    (hmem : ∀ i ∈ C, SchattenMemLp P (N : ℝ) (Y i))
    (hcent : ∀ i ∈ C,
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (Y i a) α β ∂P)
        = ofFullBlockMat (0 : FullBlockMat d))
    (hindep : ProbabilityTheory.iIndepFun
      (fun (i : C) a => toFullBlockMat (Y (i : ι) a)) P)
    (u : ℝ) (hu : 0 ≤ u) (hnorm : ∀ i ∈ C, lqSchattenNorm P (N : ℝ) (Y i) = u) :
    lqSchattenNorm P (N : ℝ)
      (fun a => ofFullBlockMat ((C.card : ℝ)⁻¹ • ∑ i ∈ C, toFullBlockMat (Y i a))) ≤
      (N : ℝ) / (C.card : ℝ) ^ ((1 : ℝ) / 2) * u := by
  classical
  let := hP
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hc : (0 : ℝ) < C.card := by exact_mod_cast hC.card_pos
  have hsum : SchattenMemLp P (N : ℝ)
      (fun a => ofFullBlockMat (∑ i ∈ C, toFullBlockMat (Y i a))) := by
    simpa using Source.memLqSchatten_finset_sum hNR C (fun _ => (1 : ℝ)) Y hmem
  have hsquares : (∑ i ∈ C, lqSchattenNorm P (N : ℝ) (Y i) ^ 2) = (C.card : ℝ) * u ^ 2 := by
    simp only [Finset.sum_congr rfl (fun i hi => congrArg (fun x : ℝ => x ^ 2) (hnorm i hi)),
      Finset.sum_const, nsmul_eq_mul]
  have hroot : ((C.card : ℝ) * u ^ 2) ^ ((1 : ℝ) / 2) =
      (C.card : ℝ) ^ ((1 : ℝ) / 2) * u := by
    rw [← Real.sqrt_eq_rpow, Real.sqrt_mul hc.le, Real.sqrt_sq hu, Real.sqrt_eq_rpow]
  have hb := Analysis.lqSchattenNorm_finset_sum_le_of_iIndepFun P hP hN hNeven C Y hmem hcent hindep
  rw [hsquares, hroot] at hb
  calc
    _ = (C.card : ℝ)⁻¹ * lqSchattenNorm P (N : ℝ)
        (fun a => ofFullBlockMat (∑ i ∈ C, toFullBlockMat (Y i a))) := by
      simpa only [toFullBlockMat_ofFullBlockMat, abs_of_nonneg (inv_nonneg.mpr hc.le)] using
        lqSchattenNorm_smul hNR hsum (C.card : ℝ)⁻¹
    _ ≤ (C.card : ℝ)⁻¹ * ((N : ℝ) * ((C.card : ℝ) ^ ((1 : ℝ) / 2) * u)) :=
      mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hc.le)
    _ = (N : ℝ) / (C.card : ℝ) ^ ((1 : ℝ) / 2) * u := by
      calc
        _ = (N : ℝ) * ((C.card : ℝ)⁻¹ * (C.card : ℝ) ^ ((1 : ℝ) / 2)) * u := by ring
        _ = _ := by rw [inv_mul_rpow_half hc]; rfl

/-- A finite average is the sum of its class averages weighted by relative class size.
Empty classes contribute zero; no inverse cancellation is used on them. -/
theorem average_eq_sum_class_averages {ι κ M : Type*} [Fintype κ]
    [DecidableEq κ] [AddCommGroup M] [Module ℝ M]
    (Z : Finset ι) (col : ι → κ) (Y : ι → M) :
    (Z.card : ℝ)⁻¹ • ∑ z ∈ Z, Y z =
      ∑ c : κ, (((Z.filter (fun z => col z = c)).card : ℝ) / (Z.card : ℝ)) •
        (((Z.filter (fun z => col z = c)).card : ℝ)⁻¹ •
          ∑ z ∈ Z.filter (fun z => col z = c), Y z) := by
  classical
  rw [← Finset.sum_fiberwise Z col Y, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : Z.filter (fun z => col z = c) = ∅
  · simp only [hc, Finset.card_empty, Nat.cast_zero, Finset.sum_empty, smul_zero]
  · have hn : (((Z.filter (fun z => col z = c)).card : ℝ)) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hc)
    rw [smul_smul]
    congr 1
    field_simp

/-- The class weights are nonnegative and sum to one when the original set is nonempty. -/
theorem class_average_weights {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (Z : Finset ι) (hZ : Z.Nonempty) (col : ι → κ) :
    (∀ c, 0 ≤ ((Z.filter (fun z => col z = c)).card : ℝ) / (Z.card : ℝ)) ∧
      (∑ c : κ, ((Z.filter (fun z => col z = c)).card : ℝ) / (Z.card : ℝ)) = 1 := by
  have hn : (Z.card : ℝ) ≠ 0 := by exact_mod_cast hZ.card_pos.ne'
  refine ⟨fun c => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _), ?_⟩
  rw [← Finset.sum_div, ← Nat.cast_sum,
    ← Finset.card_eq_sum_card_fiberwise (fun z _ => Finset.mem_univ (col z)), div_self hn]


/-- Scalar multiplication preserves finite mixed moments. -/
theorem memLqSchatten_smul {d : ℕ} {P : Measure (CoeffSpace d)} {N : ℝ}
    (hN : 1 ≤ N) {H : CoeffSpace d → BlockMat d} (hH : SchattenMemLp P N H) (c : ℝ) :
    SchattenMemLp P N (fun a => ofFullBlockMat (c • toFullBlockMat (H a))) := by
  simpa only [Finset.sum_singleton] using Source.memLqSchatten_finset_sum hN
    ({()} : Finset Unit) (fun _ => c) (fun _ => H) (fun _ _ => hH)

/-- Convex recombination of independent class averages gives the square root of the palette size. -/
theorem lqSchattenNorm_coloured_average_le {d : ℕ} {ι κ : Type*}
    [Fintype κ] [DecidableEq κ]
    (P : Measure (CoeffSpace d)) (hP : IsProbabilityMeasure P)
    {N : ℕ} (hN : 2 ≤ N) (hNeven : Even N)
    (Z : Finset ι) (hZ : Z.Nonempty) (col : ι → κ) (Y : ι → CoeffSpace d → BlockMat d)
    (hmem : ∀ i ∈ Z, SchattenMemLp P (N : ℝ) (Y i))
    (hcent : ∀ i ∈ Z,
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (Y i a) α β ∂P)
        = ofFullBlockMat (0 : FullBlockMat d))
    (hindep : ∀ c : κ, ProbabilityTheory.iIndepFun
      (fun (i : Z.filter (fun z => col z = c)) a => toFullBlockMat (Y (i : ι) a)) P)
    (u : ℝ) (hu : 0 ≤ u) (hnorm : ∀ i ∈ Z, lqSchattenNorm P (N : ℝ) (Y i) = u) :
    lqSchattenNorm P (N : ℝ)
      (fun a => ofFullBlockMat ((Z.card : ℝ)⁻¹ • ∑ i ∈ Z, toFullBlockMat (Y i a))) ≤
      (N : ℝ) * (Fintype.card κ : ℝ) ^ ((1 : ℝ) / 2) /
        (Z.card : ℝ) ^ ((1 : ℝ) / 2) * u := by
  classical
  let := hP
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn : (0 : ℝ) < Z.card := by exact_mod_cast hZ.card_pos
  let C : κ → Finset ι := fun c => Z.filter (fun z => col z = c)
  let H : κ → CoeffSpace d → BlockMat d := fun c a =>
    ofFullBlockMat (((C c).card : ℝ)⁻¹ • ∑ i ∈ C c, toFullBlockMat (Y i a))
  let w : κ → ℝ := fun c => ((C c).card : ℝ) / (Z.card : ℝ)
  have hw : ∀ c, 0 ≤ w c := (class_average_weights Z hZ col).1
  have hH (c : κ) : SchattenMemLp P (N : ℝ) (H c) := by
    simpa only [H, Finset.smul_sum] using Source.memLqSchatten_finset_sum hNR (C c)
      (fun _ => ((C c).card : ℝ)⁻¹) Y (fun i hi => hmem i (Finset.mem_filter.mp hi).1)
  have hshape : (fun a => ofFullBlockMat ((Z.card : ℝ)⁻¹ • ∑ i ∈ Z, toFullBlockMat (Y i a))) =
      (fun a => ofFullBlockMat (∑ c : κ, toFullBlockMat
        (ofFullBlockMat (w c • toFullBlockMat (H c a))))) := by
    funext a
    simp only [toFullBlockMat_ofFullBlockMat, H]
    exact congrArg ofFullBlockMat (average_eq_sum_class_averages Z col (fun i => toFullBlockMat
      (Y i a)))
  have hclass (c : κ) : w c * lqSchattenNorm P (N : ℝ) (H c) ≤
      (N : ℝ) / (Z.card : ℝ) * ((C c).card : ℝ) ^ ((1 : ℝ) / 2) * u := by
    by_cases hc : (C c).Nonempty
    · have hcpos : (0 : ℝ) < (C c).card := by exact_mod_cast hc.card_pos
      have hb := lqSchattenNorm_class_average_le P hP hN hNeven (C c) hc Y
        (fun i hi => hmem i (Finset.mem_filter.mp hi).1)
        (fun i hi => hcent i (Finset.mem_filter.mp hi).1) (hindep c) u hu
        (fun i hi => hnorm i (Finset.mem_filter.mp hi).1)
      refine (mul_le_mul_of_nonneg_left hb (hw c)).trans_eq ?_
      have hs : (((C c).card : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = ((C c).card : ℝ) := by
        rw [← Real.sqrt_eq_rpow, Real.sq_sqrt hcpos.le]
      have hsp : 0 < ((C c).card : ℝ) ^ ((1 : ℝ) / 2) := Real.rpow_pos_of_pos hcpos _
      dsimp [w]
      field_simp
      rw [hs]
    · have hc0 : C c = ∅ := Finset.not_nonempty_iff_eq_empty.mp hc
      simp only [w, hc0, Finset.card_empty, Nat.cast_zero, zero_div, zero_mul,
        Real.zero_rpow (by norm_num : (1 : ℝ) / 2 ≠ 0), mul_zero, le_refl]
  rw [hshape]
  calc
    _ ≤ ∑ c : κ, lqSchattenNorm P (N : ℝ)
        (fun a => ofFullBlockMat (w c • toFullBlockMat (H c a))) :=
      lqSchattenNorm_finset_sum_le hNR Finset.univ _ (fun c _ => memLqSchatten_smul hNR (hH c)
        (w c))
    _ = ∑ c : κ, w c * lqSchattenNorm P (N : ℝ) (H c) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [lqSchattenNorm_smul hNR (hH c), abs_of_nonneg (hw c)]
    _ ≤ ∑ c : κ, (N : ℝ) / (Z.card : ℝ) * ((C c).card : ℝ) ^ ((1 : ℝ) / 2) * u :=
      Finset.sum_le_sum (fun c _ => hclass c)
    _ = (N : ℝ) / (Z.card : ℝ) * (∑ c : κ, ((C c).card : ℝ) ^ ((1 : ℝ) / 2)) * u := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ (N : ℝ) / (Z.card : ℝ) *
        ((Fintype.card κ : ℝ) ^ ((1 : ℝ) / 2) * (Z.card : ℝ) ^ ((1 : ℝ) / 2)) * u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (sum_rpow_card_fiber_le Z col)
        (div_nonneg (Nat.cast_nonneg _) hn.le)) hu
    _ = _ := by
      calc
        _ = (N : ℝ) * (Fintype.card κ : ℝ) ^ ((1 : ℝ) / 2) *
            ((Z.card : ℝ)⁻¹ * (Z.card : ℝ) ^ ((1 : ℝ) / 2)) * u := by ring
        _ = _ := by rw [inv_mul_rpow_half hn]; rfl

/-- The ordinary-support endpoint of finite-range matrix averaging, with the printed constant.
The inverse square root is certified positive definite before the normalized variables
are identified with a Hermitian congruence. All moment receipts come from the standing law. -/
theorem matrix_averaging_roundedGrid (d : ℕ) (hd : 2 ≤ d)
    (P : Measure (CoeffSpace d)) (hP : IsProbabilityMeasure P)
    (γ : ℝ) (E : BlockMat d) (Ψ : ℝ → ℝ) (K : ℝ) (S : CoeffSpace d → ℝ)
    (hstat : IsStationaryLaw P) (hunit : IsUnitRangeLaw P)
    (hdag : CoarseEllipticityDagger P γ E Ψ K S)
    (N : ℕ) (hN : 2 ≤ N) (hNeven : Even N)
    (jStar : ℕ) (hj : 2 * d ≤ 3 ^ jStar)
    (m : Mat d) (hm : m.PosDef)
    (j : ℤ) (hjgen : (jStar : ℤ) ≤ j)
    (Z : Finset (Vec d)) (hZne : Z.Nonempty)
    (hZ : (Z : Set (Vec d)) ⊆ adaptedLatticeAtScale (Geometry.explicitRoundedGrid jStar m) j)
    (R : BlockMat d) (hRsymm : IsSymmetricBlockMat R)
    (hRpos : Book.Ch02.BlockPosDef R) :
    lqSchattenNorm P (N : ℝ) (fun a => ofFullBlockMat ((Z.card : ℝ)⁻¹ • ∑ z ∈ Z,
        toFullBlockMat (normalizedBlock (blockSub
          (coarseBlock (HighContrast.adaptedCellTranslate (Geometry.explicitRoundedGrid jStar m)
            j z) a)
          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j)) R))) ≤
      (N : ℝ) * (3 : ℝ) ^ ((d : ℝ) / 2) / (Z.card : ℝ) ^ ((1 : ℝ) / 2) *
        lqSchattenNorm P (N : ℝ) (fun a => normalizedBlock (blockSub
          (coarseBlock (HighContrast.adaptedCell (Geometry.explicitRoundedGrid jStar m) j) a)
          (adaptedMean P (Geometry.explicitRoundedGrid jStar m) j)) R) := by
  classical
  let := hP
  have : NeZero d := ⟨by omega⟩
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let q := Geometry.explicitRoundedGrid jStar m
  have hq : IsUnit q := Geometry.isUnit_roundedGrid hj hm
  have hRfull := posDef_toFullBlockMat hRsymm hRpos
  let T := matSqrt (toFullBlockMat R)⁻¹
  have hT : T.PosDef := Multiscale.matSqrt_inv_posDef_full hRfull
  let Y : Vec d → CoeffSpace d → BlockMat d := fun z a =>
    ofFullBlockMat (T.conjTranspose * toFullBlockMat (blockSub
      (coarseBlock (HighContrast.adaptedCellTranslate q j z) a) (adaptedMean P q j)) * T)
  have hY (z : Vec d) : Y z = (fun a => normalizedBlock (blockSub
      (coarseBlock (HighContrast.adaptedCellTranslate q j z) a) (adaptedMean P q j)) R) := by
    funext a
    dsimp only [Y]
    rw [hT.isHermitian.eq]
    rfl
  let Y₀ : CoeffSpace d → BlockMat d := fun a => normalizedBlock (blockSub
    (coarseBlock (HighContrast.adaptedCell q j) a) (adaptedMean P q j)) R
  have hm0 : SchattenMemLp P (N : ℝ) Y₀ := by
    simpa only [Y₀, adaptedCellTranslate_zero] using
      memLqSchatten_normalizedCentered d hd P γ E Ψ K S hstat hdag jStar hj m hm j 0 R (N : ℝ) hNR
  have hmem (z : Vec d) : SchattenMemLp P (N : ℝ) (Y z) := by
    simpa only [hY] using
      memLqSchatten_normalizedCentered d hd P γ E Ψ K S hstat hdag jStar hj m hm j z R (N : ℝ) hNR
  let w : Vec d → Fin d → ℤ := fun z => if hz : z ∈ Z then
    Classical.choose (exists_unique_index_of_mem_adaptedLatticeAtScale hq j (hZ hz)) else 0
  have hw (z : Vec d) (hz : z ∈ Z) : adaptedCellCenter q j (w z) = z := by
    dsimp only [w]
    rw [dite_eq_left hz]
    exact (Classical.choose_spec (exists_unique_index_of_mem_adaptedLatticeAtScale hq j (hZ hz))).1
  let col : Vec d → Fin d → ZMod 3 := fun z i => (w z i : ZMod 3)
  have hc (z : Vec d) (hz : z ∈ Z) :
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (Y z a) α β ∂P) =
        ofFullBlockMat (0 : FullBlockMat d) := by
    rw [hY, ← hw z hz]
    exact integral_normalizedCentered_lattice_eq_zero hd P γ E Ψ K S hstat hdag
      jStar hj m hm hjgen (w z) R
  have hind (c : Fin d → ZMod 3) : ProbabilityTheory.iIndepFun
      (fun (z : Z.filter (fun z => col z = c)) a => toFullBlockMat (Y z a)) P := by
    have hsep : Pairwise fun (z z' : Z.filter (fun z => col z = c)) =>
        UnitSeparated (HighContrast.adaptedCellTranslate q j z)
          (HighContrast.adaptedCellTranslate q j z') := by
      intro z z' hne
      have hz := (Finset.mem_filter.mp z.property).1
      have hz' := (Finset.mem_filter.mp z'.property).1
      have hwne : w z ≠ w z' := by
        intro he
        apply hne
        apply Subtype.ext
        rw [← hw z hz, ← hw z' hz', he]
      have hres : ∀ i, ((w z i : ZMod 3)) = ((w z' i : ZMod 3)) := by
        intro i
        exact congrFun ((Finset.mem_filter.mp z.property).2.trans
          (Finset.mem_filter.mp z'.property).2.symm) i
      have h := unitSeparated_adaptedCellAtCenter_of_residue_eq hd hj hm hjgen hwne hres
      change UnitSeparated (HighContrast.adaptedCellTranslate q j (adaptedCellCenter q j (w z)))
        (HighContrast.adaptedCellTranslate q j (adaptedCellCenter q j (w z'))) at h
      rw [hw z hz, hw z' hz'] at h
      exact h
    simpa only [hY] using iIndepFun_coarseBlockNormalized_of_unitSeparated P hunit
      q hq j (fun z : Z.filter (fun z => col z = c) => (z : Vec d)) hsep (adaptedMean P q j) R
  have hnorm (z : Vec d) (hz : z ∈ Z) :
      lqSchattenNorm P (N : ℝ) (Y z) = lqSchattenNorm P (N : ℝ) Y₀ := by
    rw [hY, ← hw z hz]
    exact lqSchattenNorm_normalizedCentered_transport P hstat
      jStar m hjgen (w z) (adaptedMean P q j) R hNR hm0
  have hb := lqSchattenNorm_coloured_average_le P hP hN hNeven Z hZne col Y
    (fun z _ => hmem z) hc hind (lqSchattenNorm P (N : ℝ) Y₀)
    (hm0.lqSchattenNorm_eq_eLpNorm_toReal hNR).2.1 hnorm
  have hpalette : (Fintype.card (Fin d → ZMod 3) : ℝ) ^ ((1 : ℝ) / 2) =
      (3 : ℝ) ^ ((d : ℝ) / 2) := by
    rw [card_residue_colours, Nat.cast_pow, Nat.cast_ofNat,
      ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    congr 1
    ring
  simpa only [hY, hpalette] using hb


end

end HCPolySupport.HighContrast.Annealed
