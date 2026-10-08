/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Regularity.CorrectorIntrinsicSlopeGoodTail

/-!
# High-contrast homogenization: Provider.Regularity.FiniteAffineAverageSlopeGoodTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Finite affine average-slope control from a scalar good tail

The summable corrected weak-error row controls, uniformly in the outer scale,
the average gradient of every finite zero-trace corrector on a fixed inner
cube. Consequently the average full gradient of a finite affine solution is
close to its boundary slope. This is the finite quantitative form of the
normalized-slope uniqueness input in the Liouville endgame.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory

noncomputable section

private theorem euclideanNorm_le_add_sub_avg
    {d : ℕ} (x y : Vec d) :
    euclideanNorm y ≤ euclideanNorm x + euclideanNorm (x - y) := by
  rw [euclideanNorm_eq_norm_ofVec, euclideanNorm_eq_norm_ofVec,
    euclideanNorm_eq_norm_ofVec]
  change ‖WithLp.toLp 2 y‖ ≤
    ‖WithLp.toLp 2 x‖ + ‖WithLp.toLp 2 (x - y)‖
  have h := norm_add_le (WithLp.toLp 2 x) (WithLp.toLp 2 (y - x))
  rw [← WithLp.toLp_add] at h
  have hsum : x + (y - x) = y := by abel
  rw [hsum] at h
  simpa only [show y - x = -(x - y) by abel,
    WithLp.toLp_neg, norm_neg] using h

private theorem normalizedLocalH1_finiteAffineCorrection_grad_avg
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k : ℕ) :
    (normalizedLocalH1
      (finiteAffineCorrectionLocalSequence a e) q k).grad =
        (finiteAffineCorrectionLocalSequence a e (q + k)).grad := by
  funext x
  change
    (normalizeOnUnitCube
      (finiteAffineCorrectionLocalSequence a e (q + k))).grad x =
        (finiteAffineCorrectionLocalSequence a e (q + k)).grad x
  rw [normalizeOnUnitCube_grad]

private theorem gradToHilbertVectorL2_sub_avg {d : ℕ}
    {U : Set (Vec d)} (u v : H1Function U) :
    (u - v).gradToHilbertVectorL2 =
      u.gradToHilbertVectorL2 - v.gradToHilbertVectorL2 := by
  rw [sub_eq_add_neg, H1Function.gradToHilbertVectorL2_add]
  have hneg := H1Function.gradToHilbertVectorL2_smul (-1 : ℝ) v
  rw [show (-v : H1Function U) = (-1 : ℝ) • v by rfl, hneg]
  simp only [neg_smul, one_smul, sub_eq_add_neg]

private theorem gradToHilbertVectorL2_eq_of_grad_eq_avg {d : ℕ}
    {U : Set (Vec d)} (u v : H1Function U) (hgrad : u.grad = v.grad) :
    u.gradToHilbertVectorL2 = v.gradToHilbertVectorL2 := by
  apply Lp.ext
  filter_upwards [u.coeFn_gradToHilbertVectorL2,
      v.coeFn_gradToHilbertVectorL2] with x hu hv
  rw [hu, hv, hgrad]

private theorem normalizedFiniteCorrection_successor_gradient_eq_avg
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k r : ℕ) (hqr : q ≤ r)
    (hrm : (r : ℤ) ≤ ((q + k : ℕ) : ℤ)) :
    (normalizedLocalH1
          (finiteAffineCorrectionLocalSequence a e) q
          (k + 1)).gradToHilbertVectorL2 -
        (normalizedLocalH1
          (finiteAffineCorrectionLocalSequence a e) q k).gradToHilbertVectorL2 =
      localGradientRestrict hqr
        (finiteCubeSolutionRestriction a hrm
          (finiteAffineSuccessorDifference a
            ((q + k : ℕ) : ℤ) e)).toH1.gradToHilbertVectorL2 := by
  let w : H1Function (localGradientCube d r) := by
    simp only [localGradientCube]
    exact (finiteCubeSolutionRestriction a hrm
      (finiteAffineSuccessorDifference a ((q + k : ℕ) : ℤ) e)).toH1
  have hcast :
      (finiteCubeSolutionRestriction a hrm
          (finiteAffineSuccessorDifference a
            ((q + k : ℕ) : ℤ) e)).toH1.gradToHilbertVectorL2 =
        w.gradToHilbertVectorL2 := rfl
  rw [hcast, ← gradToHilbertVectorL2_sub_avg,
    localGradientRestrict_gradToHilbertVectorL2_restrictLocalH1]
  apply gradToHilbertVectorL2_eq_of_grad_eq_avg
  funext x
  rw [H1Function.sub_grad,
    normalizedLocalH1_finiteAffineCorrection_grad_avg,
    normalizedLocalH1_finiteAffineCorrection_grad_avg]
  change _ =
    (finiteCubeSolutionRestriction a hrm
      (finiteAffineSuccessorDifference a ((q + k : ℕ) : ℤ) e)).toH1.grad x
  rw [finiteCubeSolutionRestriction_grad,
    finiteAffineSuccessorDifference_grad]
  have hindex : ((q + (k + 1) : ℕ) : ℤ) =
      ((q + k : ℕ) : ℤ) + 1 := by omega
  change
    (finiteAffineCorrection a
          ((q + (k + 1) : ℕ) : ℤ) e).toH1Function.grad x -
        (finiteAffineCorrection a
          ((q + k : ℕ) : ℤ) e).toH1Function.grad x =
      (finiteAffineCubeSolution a
          (((q + k : ℕ) : ℤ) + 1) e).toH1.grad x -
        (finiteAffineCubeSolution a
          ((q + k : ℕ) : ℤ) e).toH1.grad x
  rw [hindex]
  simp only [finiteAffineCubeSolution, finiteAffineSolution_toH1,
    H1Function.add_grad, finiteAffineBoundaryH1_grad]
  abel

private theorem localGradientClassAverage_restrictedH1Gradient_avg
    {d m n : ℕ} (hmn : m ≤ n)
    (u : H1Function (localGradientCube d n)) :
    localGradientClassAverage
        (localGradientRestrict hmn u.gradToHilbertVectorL2) =
      cubeAverageVec (originCube d (m : ℤ)) u.grad := by
  apply localGradientClassAverage_eq_cubeAverageVec_of_ae
  let hmu : volumeMeasureOn (localGradientCube d m) ≤
      volumeMeasureOn (localGradientCube d n) :=
    Measure.restrict_mono_set volume (localGradientCube_mono hmn)
  exact
    (localGradientRestrict_coeFn_ae hmn u.gradToHilbertVectorL2).trans
      (u.coeFn_gradToHilbertVectorL2.filter_mono (ae_mono hmu))

private theorem finiteAffineCorrectionLocalGradientAverage_eq_cubeAverageVec_avg
    {d : ℕ} [NeZero d] (a : Book.Ch02.TriadicCoeffFamily d)
    (e : Vec d) (q k : ℕ) :
    localGradientClassAverage
        (normalizedLocalPair
          (finiteAffineCorrectionLocalSequence a e) q k).2 =
      cubeAverageVec (originCube d (q : ℤ))
        (finiteAffineCorrectionLocalSequence a e (q + k)).grad := by
  rw [normalizedLocalPair_gradient_eq]
  exact localGradientClassAverage_restrictedH1Gradient_avg
    (Nat.le_add_right q k) (finiteAffineCorrectionLocalSequence a e (q + k))

/-- A scalar good tail uniformly controls the average gradient of a finite
correction two or more scales outside a fixed centered cube. -/
theorem exists_scalarIdentityGoodTailFiniteCorrectionGradientAverageConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 0 < C ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
          ∀ (q t : ℕ), n ≤ (q : ℤ) → ∀ e : Vec d,
          ‖cubeAverageVec (originCube d (q : ℤ))
              (finiteAffineCorrection a ((q + t + 2 : ℕ) : ℤ) e).toH1Function.grad‖ ≤
            C * (1 + delta) * delta * euclideanNorm e := by
  obtain ⟨Cstep, c, hCstep, hc, hstep⟩ :=
    exists_finiteAffineSuccessorGradientAverageEstimateConstant
      d s hs hs_lt
  obtain ⟨Cinit, hCinit, hinit⟩ :=
    exists_finiteAffineCorrectionDepthTwoGradientAverageEstimateConstant
      d (s + 1 / 2) s hs (by linarith only [hs_lt])
        (by linarith only [hs_lt])
  let C : ℝ := Cinit + 2 * Cstep
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro a delta n hdelta hgood q t hnq e
  have hgoodQ : ScalarIdentityGoodTail a s delta (q : ℤ) :=
    hgood.mono_start hnq
  let E : ℕ → ℝ := fun j =>
    scalarIdentityCorrectedWeakError a s ((q + j : ℕ) : ℤ)
  let epsilon : ℕ → ℝ := fun j => E (j + 2) + E (j + 3)
  let x : ℕ → Vec d := fun j =>
    localGradientClassAverage
      (normalizedLocalPair
        (finiteAffineCorrectionLocalSequence a e) q (j + 2)).2
  have hx0 : ‖x 0‖ ≤ Cinit * E 2 * euclideanNorm e := by
    rw [show x 0 = cubeAverageVec (originCube d (q : ℤ))
        (finiteAffineCorrection a ((q + 2 : ℕ) : ℤ) e).toH1Function.grad by
      dsimp only [x]
      rw [finiteAffineCorrectionLocalGradientAverage_eq_cubeAverageVec_avg]
      congr 3]
    simpa only [E] using hinit a q e
  have hsuccessive : ∀ j,
      ‖x (j + 1) - x j‖ ≤ Cstep * epsilon j * euclideanNorm e := by
    intro j
    let m : ℤ := ((q + j + 2 : ℕ) : ℤ)
    let w : Book.Ch03.CubeSolution (originCube d (q : ℤ)) a :=
      finiteCubeSolutionRestriction a (by omega : (q : ℤ) ≤ m)
        (finiteAffineSuccessorDifference a m e)
    have hinterval : ScalarIdentityGoodTailOnInterval a s delta
        (q : ℤ) (m + 1) :=
      (hgood.interval (by omega)).mono_start hnq
    have hbound := hstep a delta (q : ℤ) m e hdelta
      (by dsimp [m]; omega) hinterval
    have hclass :
        (normalizedLocalPair
              (finiteAffineCorrectionLocalSequence a e) q (j + 3)).2 -
            (normalizedLocalPair
              (finiteAffineCorrectionLocalSequence a e) q (j + 2)).2 =
          w.toH1.gradToHilbertVectorL2 := by
      simpa only [normalizedLocalPair, w, m,
        localGradientRestrict_refl, ContinuousLinearMap.id_apply] using!
        normalizedFiniteCorrection_successor_gradient_eq_avg
          a e q (j + 2) q le_rfl (by omega)
    have havg : localGradientClassAverage w.toH1.gradToHilbertVectorL2 =
        cubeAverageVec (originCube d (q : ℤ))
          (finiteAffineSuccessorDifference a m e).toH1.grad := by
      calc
        localGradientClassAverage w.toH1.gradToHilbertVectorL2 =
            cubeAverageVec (originCube d (q : ℤ)) w.toH1.grad := by
          simpa only [localGradientRestrict_refl, ContinuousLinearMap.id_apply]
            using! localGradientClassAverage_restrictedH1Gradient_avg le_rfl w.toH1
        _ = cubeAverageVec (originCube d (q : ℤ))
            (finiteAffineSuccessorDifference a m e).toH1.grad := by
          simp only [w, finiteCubeSolutionRestriction_grad]
    rw [← localGradientClassAverage_sub, hclass, havg]
    dsimp only [epsilon, E]
    have hm0 : ((q + (j + 2) : ℕ) : ℤ) = m := by dsimp only [m]; omega
    have hmSucc : ((q + (j + 3) : ℕ) : ℤ) = m + 1 := by dsimp only [m]; omega
    rw [hm0, hmSucc]
    convert hbound using 1
  have htelescope := norm_sub_le_sum_Ico_of_successive_norm_le
    x epsilon Cstep (euclideanNorm e) hsuccessive (Nat.zero_le t)
  have hEnonneg : ∀ j, 0 ≤ E j := fun j =>
    scalarIdentityCorrectedWeakError_nonneg a s _
  have hEsum : Summable E := by
    simpa only [E, Int.natCast_add] using
      hgoodQ.summable_corrected_nat_shift
  have hEtotal : ∑' j, E j ≤ (1 + delta) * delta :=
    Real.tsum_le_of_sum_range_le hEnonneg fun N => by
      simpa only [E, Nat.Ico_zero_eq_range, Int.natCast_add] using
        hgoodQ.sum_Ico_corrected_nat_shift_le 0 N
  have hsumShift (r : ℕ) : (∑ j ∈ Finset.Ico 0 t, E (j + r)) ≤
      ∑' j, E j := by
    let S := (Finset.Ico 0 t).image (fun j : ℕ => j + r)
    calc
      (∑ j ∈ Finset.Ico 0 t, E (j + r)) = ∑ j ∈ S, E j := by
        dsimp only [S]
        rw [Finset.sum_image]
        intro x _ y _ hxy
        exact Nat.add_right_cancel hxy
      _ ≤ ∑' j, E j := hEsum.sum_le_tsum S fun j _ => hEnonneg j
  have hsumTwo : (∑ j ∈ Finset.Ico 0 t, E (j + 2)) ≤
      (1 + delta) * delta := (hsumShift 2).trans hEtotal
  have hsumThree : (∑ j ∈ Finset.Ico 0 t, E (j + 3)) ≤
      (1 + delta) * delta := (hsumShift 3).trans hEtotal
  have hsum : (∑ j ∈ Finset.Ico 0 t, epsilon j) ≤
      2 * ((1 + delta) * delta) := by
    rw [show (∑ j ∈ Finset.Ico 0 t, epsilon j) =
        (∑ j ∈ Finset.Ico 0 t, E (j + 2)) +
          ∑ j ∈ Finset.Ico 0 t, E (j + 3) by
      simp only [epsilon, Finset.sum_add_distrib]]
    linarith only [hsumTwo, hsumThree]
  have hE2 : E 2 ≤ (1 + delta) * delta := by
    have hsingle : E 2 ≤ ∑' j, E j := by
      simpa only [Finset.sum_singleton] using
        hEsum.sum_le_tsum ({2} : Finset ℕ) fun j _ => hEnonneg j
    exact hsingle.trans hEtotal
  have hbudget : 0 ≤ (1 + delta) * delta := by
    exact mul_nonneg (by linarith only [hdelta.1]) hdelta.1.le
  have hxBound : ‖x t‖ ≤
      C * (1 + delta) * delta * euclideanNorm e := by
    have htri : ‖x t‖ ≤ ‖x 0‖ + ‖x t - x 0‖ := by
      calc
        ‖x t‖ = ‖x 0 + (x t - x 0)‖ := by congr 1; abel
        _ ≤ ‖x 0‖ + ‖x t - x 0‖ := norm_add_le _ _
    calc
      ‖x t‖ ≤ ‖x 0‖ + ‖x t - x 0‖ := htri
      _ ≤ Cinit * E 2 * euclideanNorm e +
          Cstep * (∑ j ∈ Finset.Ico 0 t, epsilon j) * euclideanNorm e :=
        add_le_add hx0 htelescope
      _ ≤ Cinit * ((1 + delta) * delta) * euclideanNorm e +
          Cstep * (2 * ((1 + delta) * delta)) * euclideanNorm e :=
        add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hE2 hCinit.le)
            (euclideanNorm_nonneg e))
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum hCstep.le)
            (euclideanNorm_nonneg e))
      _ = C * (1 + delta) * delta * euclideanNorm e := by
        dsimp [C]
        ring
  rw [show x t = cubeAverageVec (originCube d (q : ℤ))
      (finiteAffineCorrection a ((q + t + 2 : ℕ) : ℤ) e).toH1Function.grad by
    dsimp only [x]
    rw [finiteAffineCorrectionLocalGradientAverage_eq_cubeAverageVec_avg]
    congr 3] at hxBound
  exact hxBound

/-- The average full gradient of a finite affine solution is uniformly close
to its boundary slope on every fixed inner cube at good-tail order. -/
theorem exists_scalarIdentityGoodTailFiniteAffineAverageSlopeConstant
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ C c : ℝ, 0 < C ∧ c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ (q t : ℕ), n ≤ (q : ℤ) → ∀ e : Vec d,
          euclideanNorm
              (cubeAverageVec (originCube d (q : ℤ))
                (finiteAffineSolution a ((q + t + 2 : ℕ) : ℤ) e).toH1.grad - e) ≤
            C * (1 + delta) * delta * euclideanNorm e := by
  obtain ⟨C₀, c, hC₀, hc, hcorr⟩ :=
    exists_scalarIdentityGoodTailFiniteCorrectionGradientAverageConstant
      d s hs hs_lt
  let C : ℝ := (d : ℝ) * C₀
  have hd : 0 < (d : ℝ) := by exact_mod_cast NeZero.pos d
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, c, hC, hc, ?_⟩
  intro a delta n hdelta hgood q t hnq e
  let m : ℤ := ((q + t + 2 : ℕ) : ℤ)
  have hqm : (q : ℤ) ≤ m := by dsimp [m]; omega
  have hdesc : originCube d (q : ℤ) ∈
      descendantsAtDepth (originCube d m) (Int.toNat (m - (q : ℤ))) :=
    originCube_mem_descendantsAtDepth_of_le hqm
  have haffineMem : MemVectorL2 (cubeSet (originCube d (q : ℤ)))
      (finiteAffineBoundaryH1 m e).grad :=
    Book.Ch03.publicH1ToCubeSet_grad_memVectorL2_descendant_cubeSet
      (finiteAffineBoundaryH1 m e) hdesc
  have hcorrMem : MemVectorL2 (cubeSet (originCube d (q : ℤ)))
      (finiteAffineCorrection a m e).toH1Function.grad :=
    Book.Ch03.publicH10ToCubeSet_toH1Function_grad_memVectorL2_descendant_cubeSet
      (finiteAffineCorrection a m e) hdesc
  have havgAdd := cubeAverageVec_add (originCube d (q : ℤ))
    (finiteAffineBoundaryH1 m e).grad
    (finiteAffineCorrection a m e).toH1Function.grad haffineMem hcorrMem
  have hfull : cubeAverageVec (originCube d (q : ℤ))
      (finiteAffineSolution a m e).toH1.grad =
      e + cubeAverageVec (originCube d (q : ℤ))
        (finiteAffineCorrection a m e).toH1Function.grad := by
    rw [finiteAffineSolution_toH1, H1Function.add_grad, havgAdd,
      finiteAffineBoundaryH1_grad, cubeAverageVec_const]
  rw [hfull, add_sub_cancel_left]
  let z : Vec d := cubeAverageVec (originCube d (q : ℤ))
    (finiteAffineCorrection a m e).toH1Function.grad
  have hz : ‖z‖ ≤ C₀ * (1 + delta) * delta * euclideanNorm e := by
    simpa only [z, m] using hcorr a delta n hdelta hgood q t hnq e
  calc
    euclideanNorm z = ‖HilbertVec.ofVec z‖ := euclideanNorm_eq_norm_ofVec z
    _ ≤ (d : ℝ) * ‖z‖ := HilbertVec.norm_ofVec_le_mul_norm z
    _ ≤ (d : ℝ) * (C₀ * (1 + delta) * delta * euclideanNorm e) :=
      mul_le_mul_of_nonneg_left hz hd.le
    _ = C * (1 + delta) * delta * euclideanNorm e := by
      dsimp [C]
      ring

/-- At a sufficiently small good tail, a finite affine boundary slope is
controlled by the average gradient on any fixed admissible inner cube. -/
theorem exists_scalarIdentityGoodTailFiniteAffineSlopeAverageCoercivityThreshold
    (d : ℕ) [NeZero d] (s : ℝ) (hs : 0 < s) (hs_lt : s < 1 / 2) :
    ∃ c : ℝ, c ∈ Set.Ioo (0 : ℝ) 1 ∧
      ∀ (a : Book.Ch02.TriadicCoeffFamily d) (delta : ℝ) (n : ℤ),
        delta ∈ Set.Ioc (0 : ℝ) c →
        ScalarIdentityGoodTail a s delta n →
        ∀ (q t : ℕ), n ≤ (q : ℤ) → ∀ e : Vec d,
          euclideanNorm e ≤ 2 * euclideanNorm
            (cubeAverageVec (originCube d (q : ℤ))
              (finiteAffineSolution a ((q + t + 2 : ℕ) : ℤ) e).toH1.grad) := by
  obtain ⟨C, c₀, hC, hc₀, hclose⟩ :=
    exists_scalarIdentityGoodTailFiniteAffineAverageSlopeConstant
      d s hs hs_lt
  let c : ℝ := min c₀ ((4 * C)⁻¹)
  have hcpos : 0 < c := by
    dsimp [c]
    exact lt_min hc₀.1 (inv_pos.mpr (mul_pos (by norm_num) hC))
  have hcone : c < 1 := lt_of_le_of_lt (min_le_left _ _) hc₀.2
  refine ⟨c, ⟨hcpos, hcone⟩, ?_⟩
  intro a delta n hdelta hgood q t hnq e
  have hdelta₀ : delta ∈ Set.Ioc (0 : ℝ) c₀ :=
    ⟨hdelta.1, hdelta.2.trans (min_le_left _ _)⟩
  have hdeltaInv : delta ≤ (4 * C)⁻¹ :=
    hdelta.2.trans (min_le_right _ _)
  have hdeltaOne : delta ≤ 1 :=
    hdelta.2.trans (le_of_lt hcone)
  have hCdelta : C * delta ≤ 1 / 4 := by
    calc
      C * delta ≤ C * (4 * C)⁻¹ :=
        mul_le_mul_of_nonneg_left hdeltaInv hC.le
      _ = 1 / 4 := by field_simp
  have hfactor : C * (1 + delta) * delta ≤ 1 / 2 := by
    calc
      C * (1 + delta) * delta = (1 + delta) * (C * delta) := by ring
      _ ≤ 2 * (1 / 4 : ℝ) := by
        exact mul_le_mul (by linarith only [hdeltaOne]) hCdelta
          (mul_nonneg hC.le hdelta.1.le) (by norm_num)
      _ = 1 / 2 := by norm_num
  let z : Vec d := cubeAverageVec (originCube d (q : ℤ))
    (finiteAffineSolution a ((q + t + 2 : ℕ) : ℤ) e).toH1.grad
  have hze : euclideanNorm (z - e) ≤
      C * (1 + delta) * delta * euclideanNorm e := by
    simpa only [z] using hclose a delta n hdelta₀ hgood q t hnq e
  have hsmall : euclideanNorm (z - e) ≤
      (1 / 2 : ℝ) * euclideanNorm e :=
    hze.trans (mul_le_mul_of_nonneg_right hfactor (euclideanNorm_nonneg e))
  have htri : euclideanNorm e ≤ euclideanNorm z + euclideanNorm (z - e) :=
    euclideanNorm_le_add_sub_avg z e
  linarith only [htri, hsmall]

end

end HighContrast
end HCPolySupport
