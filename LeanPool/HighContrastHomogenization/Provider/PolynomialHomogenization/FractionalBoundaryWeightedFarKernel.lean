/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.ConvexBoundaryWeightLocalAllScales
public import LeanPool.HighContrastHomogenization.Provider.PolynomialHomogenization.EuclideanBallDistance

/-!
# High-contrast homogenization:
Provider.PolynomialHomogenization.FractionalBoundaryWeightedFarKernel

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Far-field fractional boundary-weight kernel

Expanding Euclidean annuli combine the local `r^(d-p)` boundary moment with
the kernel power `r^(s-d)`. The resulting ratio is `2^(s-p)`.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory Set
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Outside half the center boundary distance, the Riesz kernel against a
negative boundary-distance moment has homogeneous order `s-p`. -/
theorem exists_bound_lintegral_far_fractionalBoundaryKernel
    (hd : 1 ≤ d) {rho Rad s p : ℝ}
    (hrho : 0 < rho) (hRad : 0 < Rad) (hs : 0 < s)
    (hsp : s < p) (hp1 : p < 1) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
      ∀ (U : Set (Vec d)), IsOpenBoundedConvexDomain U →
        HasBallSandwich U rho Rad → ∀ x ∈ U,
          (∫⁻ y in U \ euclideanBallAt x
              (euclideanBoundaryDistance U x / 2),
            ENNReal.ofReal
                (euclideanDist x y ^ (s - (d : ℝ))) *
              euclideanBoundaryWeight U p y ∂volume) ≤
            C * ENNReal.ofReal
              (euclideanBoundaryDistance U x ^ (s - p)) := by
  classical
  obtain ⟨M, hMtop, hM⟩ :=
    exists_bound_lintegral_local_euclideanBoundaryWeight_all_scales
      hd hrho hRad (hs.trans hsp) hp1
  let ratio : ℝ := (2 : ℝ) ^ (s - p)
  let A : ℝ := (2 : ℝ) ^ ((d : ℝ) - s)
  let C : ℝ≥0∞ :=
    M * ENNReal.ofReal A * (1 - ENNReal.ofReal ratio)⁻¹
  have hratio0 : 0 < ratio := by
    dsimp only [ratio]
    positivity
  have hratio1 : ratio < 1 := by
    dsimp only [ratio]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num)
      (by linarith only [hsp])
  have hA0 : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨C, ENNReal.mul_ne_top
    (ENNReal.mul_ne_top hMtop ENNReal.ofReal_ne_top) (by
      rw [ENNReal.inv_ne_top]
      exact ne_of_gt ((tsub_pos_iff_lt).2
        (ENNReal.ofReal_lt_one.mpr hratio1))), ?_⟩
  intro U hU hsand x hx
  let delta : ℝ := euclideanBoundaryDistance U x
  let r0 : ℝ := delta / 2
  have hdelta : 0 < delta := euclideanBoundaryDistance_pos hd hU hx
  have hr0 : 0 < r0 := by dsimp only [r0]; positivity
  have he0 : s - (d : ℝ) < 0 := by
    have hdreal : 1 ≤ (d : ℝ) := by exact_mod_cast hd
    linarith only [hdreal, hp1, hsp]
  let shell : ℕ → Set (Vec d) := fun k =>
    U ∩ (euclideanBallAt x ((2 : ℝ) ^ (k + 1) * r0) \
      euclideanBallAt x ((2 : ℝ) ^ k * r0))
  let T : ℕ → ℝ := fun k =>
    (((2 : ℝ) ^ k * r0) ^ (s - (d : ℝ))) *
      (((2 : ℝ) ^ (k + 1) * r0) ^ ((d : ℝ) - p))
  have hTrec : ∀ k : ℕ, T (k + 1) = ratio * T k := by
    intro k
    have hrk : 0 ≤ (2 : ℝ) ^ k * r0 := by positivity
    have hrk1 : 0 ≤ (2 : ℝ) ^ (k + 1) * r0 := by positivity
    have h1 : ((2 : ℝ) ^ (k + 1) * r0) ^ (s - (d : ℝ)) =
        2 ^ (s - (d : ℝ)) *
          (((2 : ℝ) ^ k * r0) ^ (s - (d : ℝ))) := by
      rw [pow_succ]
      rw [show (2 : ℝ) ^ k * 2 * r0 =
        2 * ((2 : ℝ) ^ k * r0) by ring,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hrk]
    have h2 : ((2 : ℝ) ^ (k + 1 + 1) * r0) ^ ((d : ℝ) - p) =
        2 ^ ((d : ℝ) - p) *
          (((2 : ℝ) ^ (k + 1) * r0) ^ ((d : ℝ) - p)) := by
      rw [pow_succ]
      rw [show (2 : ℝ) ^ (k + 1) * 2 * r0 =
        2 * ((2 : ℝ) ^ (k + 1) * r0) by ring,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hrk1]
    have hcoef : 2 ^ (s - (d : ℝ)) * 2 ^ ((d : ℝ) - p) = ratio := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    dsimp only [T]
    rw [h1, h2]
    calc
      2 ^ (s - (d : ℝ)) * (((2 : ℝ) ^ k * r0) ^ (s - (d : ℝ))) *
          (2 ^ ((d : ℝ) - p) *
            (((2 : ℝ) ^ (k + 1) * r0) ^ ((d : ℝ) - p))) =
          (2 ^ (s - (d : ℝ)) * 2 ^ ((d : ℝ) - p)) *
            ((((2 : ℝ) ^ k * r0) ^ (s - (d : ℝ))) *
              (((2 : ℝ) ^ (k + 1) * r0) ^ ((d : ℝ) - p))) := by ring
      _ = ratio * ((((2 : ℝ) ^ k * r0) ^ (s - (d : ℝ))) *
              (((2 : ℝ) ^ (k + 1) * r0) ^ ((d : ℝ) - p))) := by rw [hcoef]
  have hTbase : T 0 = A * delta ^ (s - p) := by
    dsimp only [T, A, r0]
    norm_num
    have hhalf : delta / 2 = (2 : ℝ)⁻¹ * delta := by ring
    rw [hhalf, show (2 : ℝ) * ((2 : ℝ)⁻¹ * delta) = delta by ring,
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ (2 : ℝ)⁻¹) hdelta.le]
    have hinv : ((2 : ℝ)⁻¹) ^ (s - (d : ℝ)) =
        2 ^ ((d : ℝ) - s) := by
      rw [Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
        ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    calc
      ((2 : ℝ)⁻¹) ^ (s - (d : ℝ)) * delta ^ (s - (d : ℝ)) *
          delta ^ ((d : ℝ) - p) =
          ((2 : ℝ)⁻¹) ^ (s - (d : ℝ)) *
            (delta ^ (s - (d : ℝ)) * delta ^ ((d : ℝ) - p)) := by ring
      _ = ((2 : ℝ)⁻¹) ^ (s - (d : ℝ)) *
          delta ^ ((s - (d : ℝ)) + ((d : ℝ) - p)) := by
        rw [Real.rpow_add hdelta]
      _ = 2 ^ ((d : ℝ) - s) * delta ^ (s - p) := by
        rw [hinv]
        congr 2
        ring
  have hTpow : ∀ k : ℕ, T k = (A * delta ^ (s - p)) * ratio ^ k := by
    intro k
    induction k with
    | zero => simpa only [pow_zero, mul_one] using hTbase
    | succ k ih => rw [hTrec k, ih, pow_succ]; ring
  have hT0 : ∀ k : ℕ, 0 ≤ T k := by
    intro k
    dsimp only [T]
    positivity
  have hshell : ∀ k : ℕ,
      (∫⁻ y in shell k,
          ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) *
            euclideanBoundaryWeight U p y ∂volume) ≤
        M * ENNReal.ofReal (T k) := by
    intro k
    have hinner : 0 < (2 : ℝ) ^ k * r0 := by positivity
    have houter : 0 < (2 : ℝ) ^ (k + 1) * r0 := by positivity
    have hset : shell k ⊆
        U ∩ euclideanBallAt x ((2 : ℝ) ^ (k + 1) * r0) := by
      rintro y ⟨hyU, hyouter, _hyinner⟩
      exact ⟨hyU, hyouter⟩
    have hshellMeas : MeasurableSet (shell k) := by
      dsimp only [shell]
      exact hU.isOpen.measurableSet.inter
        ((isOpen_euclideanBallAt x _).measurableSet.diff
          (isOpen_euclideanBallAt x _).measurableSet)
    calc
      (∫⁻ y in shell k,
          ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) *
            euclideanBoundaryWeight U p y ∂volume) ≤
          ∫⁻ y in shell k,
            ENNReal.ofReal
              (((2 : ℝ) ^ k * r0) ^ (s - (d : ℝ))) *
              euclideanBoundaryWeight U p y ∂volume := by
        refine lintegral_mono_ae ?_
        filter_upwards [self_mem_ae_restrict hshellMeas] with y hy
        have hfar : (2 : ℝ) ^ k * r0 ≤ euclideanDist x y := by
          have hnot := hy.2.2
          rw [mem_euclideanBallAt_iff_euclideanDist_lt hinner] at hnot
          simpa only [euclideanDist_comm, not_lt] using hnot
        exact mul_le_mul_left
          (ENNReal.ofReal_le_ofReal
            (Real.rpow_le_rpow_of_nonpos hinner hfar he0.le)) _
      _ = ENNReal.ofReal (((2 : ℝ) ^ k * r0) ^ (s - (d : ℝ))) *
          (∫⁻ y in shell k, euclideanBoundaryWeight U p y ∂volume) := by
        rw [lintegral_const_mul _ (measurable_euclideanBoundaryWeight U p)]
      _ ≤ ENNReal.ofReal (((2 : ℝ) ^ k * r0) ^ (s - (d : ℝ))) *
          (M * ENNReal.ofReal
            (((2 : ℝ) ^ (k + 1) * r0) ^ ((d : ℝ) - p))) := by
        simpa only [mul_comm] using mul_le_mul_left
          ((lintegral_mono_set hset).trans
            (hM U hU hsand x houter))
          (ENNReal.ofReal (((2 : ℝ) ^ k * r0) ^ (s - (d : ℝ))))
      _ = M * ENNReal.ofReal (T k) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg hinner.le _)]
        ac_rfl
  have hcover : U \ euclideanBallAt x r0 ⊆ ⋃ k, shell k := by
    rintro y ⟨hyU, hyfar⟩
    have hfar : r0 ≤ euclideanDist x y := by
      rw [mem_euclideanBallAt_iff_euclideanDist_lt hr0] at hyfar
      simpa only [euclideanDist_comm, not_lt] using hyfar
    have hex : ∃ n : ℕ,
        euclideanDist x y < (2 : ℝ) ^ (n + 1) * r0 := by
      have hevent : ∀ᶠ n : ℕ in Filter.atTop,
          euclideanDist x y / r0 < (2 : ℝ) ^ n :=
        (tendsto_pow_atTop_atTop_of_one_lt
          (by norm_num : (1 : ℝ) < 2)).eventually_gt_atTop _
      obtain ⟨n, hn⟩ := hevent.exists
      refine ⟨n, ?_⟩
      have hn' : euclideanDist x y < (2 : ℝ) ^ n * r0 :=
        (div_lt_iff₀ hr0).mp hn
      exact hn'.trans_le (by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right
          (le_mul_of_one_le_right (by positivity) (by norm_num)) hr0.le)
    let n := Nat.find hex
    have hnouter : euclideanDist x y < (2 : ℝ) ^ (n + 1) * r0 :=
      Nat.find_spec hex
    have hninner : (2 : ℝ) ^ n * r0 ≤ euclideanDist x y := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · simpa only [hn, pow_zero, one_mul] using hfar
      · have hmin := Nat.find_min hex (Nat.pred_lt hn.ne')
        push Not at hmin
        have hnid : n.pred + 1 = n := Nat.succ_pred_eq_of_pos hn
        rwa [hnid] at hmin
    refine Set.mem_iUnion.mpr ⟨n, hyU, ?_, ?_⟩
    · exact (mem_euclideanBallAt_iff_euclideanDist_lt (by positivity)).mpr
        (by simpa only [euclideanDist_comm] using hnouter)
    · rw [mem_euclideanBallAt_iff_euclideanDist_lt (by positivity)]
      simpa only [euclideanDist_comm, not_lt] using hninner
  calc
    (∫⁻ y in U \ euclideanBallAt x
        (euclideanBoundaryDistance U x / 2),
      ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) *
        euclideanBoundaryWeight U p y ∂volume) ≤
        ∫⁻ y in ⋃ k, shell k,
          ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) *
            euclideanBoundaryWeight U p y ∂volume := by
      simpa only [r0, delta] using lintegral_mono_set hcover
    _ ≤ ∑' k, ∫⁻ y in shell k,
          ENNReal.ofReal (euclideanDist x y ^ (s - (d : ℝ))) *
            euclideanBoundaryWeight U p y ∂volume := lintegral_iUnion_le _ _
    _ ≤ ∑' k, M * ENNReal.ofReal (T k) := ENNReal.tsum_le_tsum hshell
    _ = ∑' k, (M * ENNReal.ofReal A *
          ENNReal.ofReal (delta ^ (s - p))) *
        (ENNReal.ofReal ratio) ^ k := by
      refine tsum_congr fun k => ?_
      rw [hTpow k, ENNReal.ofReal_mul
        (mul_nonneg hA0 (Real.rpow_nonneg hdelta.le _)),
        ENNReal.ofReal_mul hA0, ENNReal.ofReal_pow hratio0.le]
      ac_rfl
    _ = (M * ENNReal.ofReal A * ENNReal.ofReal (delta ^ (s - p))) *
        ∑' k, (ENNReal.ofReal ratio) ^ k := ENNReal.tsum_mul_left
    _ = C * ENNReal.ofReal
        (euclideanBoundaryDistance U x ^ (s - p)) := by
      rw [ENNReal.tsum_geometric]
      dsimp only [C, delta]
      ac_rfl

end

end HighContrast
end HCPolySupport
