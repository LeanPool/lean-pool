/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Window.SuccessorDiscrete

/-!
# High-contrast homogenization: Provider.Window.SuccessorTail

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section


namespace HCPolySupport
namespace HighContrast
namespace Window
open MeasureTheory _root_.Filter
open scoped ENNReal BigOperators
noncomputable section

variable {d : ℕ}

private theorem growthBar_pow_pos (K : ℝ) (d : ℕ) :
    0 < growthBar K ^ (4 * (d + 1)) := by
  apply pow_pos
  rw [growthBar]
  exact lt_of_lt_of_le (by norm_num) (le_max_left _ _)

/-- The strict successor has the continuous source-gauge tail with the printed
maximum at the terminal generation. -/
theorem measureReal_successorScale_tail [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M : ℤ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M)
    {t : ℝ} (ht : 1 ≤ t) :
    P.real {a : CoeffSpace d |
        ENNReal.ofReal
          (max ((3 : ℝ) ^ M)
            (t * growthBar K ^ (4 * (d + 1)) *
              (3 : ℝ) ^ (M - jStar + 1))) <
          successorScale g E (M - jStar) a} ≤ (Ψ t)⁻¹ := by
  let h : ℤ := M - jStar
  let C : ℝ := growthBar K ^ (4 * (d + 1))
  let T : ℝ := (3 : ℝ) ^ (jStar - 1) * C⁻¹
  let X : ℝ := t * C * (3 : ℝ) ^ (h + 1)
  have hC : 0 < C := by exact growthBar_pow_pos K d
  have htpos : 0 < t := zero_lt_one.trans_le ht
  have hX : 0 < X := by dsimp only [X]; positivity
  have hthreshold : T * C * (3 : ℝ) ^ (h + 1) = (3 : ℝ) ^ M := by
    calc
      T * C * (3 : ℝ) ^ (h + 1) =
          (3 : ℝ) ^ (jStar - 1) * (3 : ℝ) ^ (h + 1) := by
            dsimp only [T]
            field_simp [hC.ne']
      _ = (3 : ℝ) ^ ((jStar - 1) + (h + 1)) :=
        (zpow_add₀ (by norm_num : (3 : ℝ) ≠ 0) _ _).symm
      _ = (3 : ℝ) ^ M := by dsimp only [h]; congr 1; omega
  by_cases hlarge : T ≤ t
  · obtain ⟨n, hnlow, hnup⟩ := exists_mem_Ico_zpow hX (by norm_num : (1 : ℝ) < 3)
    have hMX : (3 : ℝ) ^ M ≤ X := by
      have hm := mul_le_mul_of_nonneg_right hlarge
        (mul_nonneg hC.le (by positivity : 0 ≤ (3 : ℝ) ^ (h + 1)))
      calc
        (3 : ℝ) ^ M = T * C * (3 : ℝ) ^ (h + 1) := hthreshold.symm
        _ = T * (C * (3 : ℝ) ^ (h + 1)) := by ring
        _ ≤ t * (C * (3 : ℝ) ^ (h + 1)) := hm
        _ = X := by dsimp only [X]; ring
    have hnM : M ≤ n := by
      have hlt : (3 : ℝ) ^ M < (3 : ℝ) ^ (n + 1) := hMX.trans_lt hnup
      have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1 : ℝ) < 3)).mp hlt
      omega
    have hden : 0 < C * (3 : ℝ) ^ (h + 1) := by positivity
    have htarg : t < C⁻¹ * (3 : ℝ) ^ (n - h) := by
      have hraw : t < (3 : ℝ) ^ (n + 1) /
          (C * (3 : ℝ) ^ (h + 1)) := by
        apply (lt_div_iff₀ hden).2
        simpa only [X, mul_assoc] using hnup
      have hpow : (3 : ℝ) ^ (n + 1) / (3 : ℝ) ^ (h + 1) =
          (3 : ℝ) ^ (n - h) := by
        rw [← zpow_sub₀ (by norm_num : (3 : ℝ) ≠ 0)]
        congr 1
        omega
      calc
        t < (3 : ℝ) ^ (n + 1) / (C * (3 : ℝ) ^ (h + 1)) := hraw
        _ = C⁻¹ * ((3 : ℝ) ^ (n + 1) / (3 : ℝ) ^ (h + 1)) := by
          field_simp [hC.ne', zpow_ne_zero]
        _ = C⁻¹ * (3 : ℝ) ^ (n - h) := by rw [hpow]
    have hψle : Ψ t ≤ Ψ (C⁻¹ * (3 : ℝ) ^ (n - h)) :=
      hdag.gauge_admissible.1 (zero_le_one.trans ht)
        (le_of_lt (mul_pos (inv_pos.mpr hC) (by positivity))) htarg.le
    have hψt : 0 < Ψ t := lt_of_lt_of_le zero_lt_one
      (hdag.gauge_admissible.2 (zero_le_one.trans ht))
    have hψn : 0 < Ψ (C⁻¹ * (3 : ℝ) ^ (n - h)) :=
      lt_of_lt_of_le zero_lt_one (hdag.gauge_admissible.2 (by positivity))
    have hsub : {a : CoeffSpace d |
        ENNReal.ofReal (max ((3 : ℝ) ^ M) X) < successorScale g E h a} ⊆
        {a : CoeffSpace d |
          ENNReal.ofReal ((3 : ℝ) ^ n) < successorScale g E h a} := by
      intro a ha
      exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal
        (hnlow.trans (le_max_right _ _))) ha
    calc
      P.real {a : CoeffSpace d |
          ENNReal.ofReal
            (max ((3 : ℝ) ^ M)
              (t * growthBar K ^ (4 * (d + 1)) *
                (3 : ℝ) ^ (M - jStar + 1))) <
            successorScale g E (M - jStar) a}
          ≤ P.real {a : CoeffSpace d |
            ENNReal.ofReal ((3 : ℝ) ^ n) < successorScale g E h a} := by
              simpa only [C, h, X] using measureReal_mono hsub
      _ ≤ (Ψ (C⁻¹ * (3 : ℝ) ^ (n - h)))⁻¹ := by
        simpa only [C, h] using
          measureReal_successorScale_gt_zpow_le hstat hdag hQ hw hnM
      _ ≤ (Ψ t)⁻¹ := (inv_le_inv₀ hψn hψt).2 hψle
  · have hsmall : t < T := lt_of_not_ge hlarge
    have hXM : X < (3 : ℝ) ^ M := by
      have hm := mul_lt_mul_of_pos_right hsmall
        (mul_pos hC (by positivity : 0 < (3 : ℝ) ^ (h + 1)))
      calc
        X = t * (C * (3 : ℝ) ^ (h + 1)) := by dsimp only [X]; ring
        _ < T * (C * (3 : ℝ) ^ (h + 1)) := hm
        _ = T * C * (3 : ℝ) ^ (h + 1) := by ring
        _ = (3 : ℝ) ^ M := hthreshold
    have hψle : Ψ t ≤ Ψ (C⁻¹ * (3 : ℝ) ^ (M - h)) := by
      have hTle : T ≤ C⁻¹ * (3 : ℝ) ^ (M - h) := by
        have hz : (3 : ℝ) ^ (jStar - 1) ≤ (3 : ℝ) ^ jStar :=
          zpow_le_zpow_right₀ (by norm_num) (by omega)
        have hm := mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hC.le)
        dsimp only [T, h]
        rw [show M - (M - jStar) = jStar by omega]
        simpa only [mul_comm] using hm
      exact hdag.gauge_admissible.1 (zero_le_one.trans ht)
        (le_of_lt (mul_pos (inv_pos.mpr hC) (by positivity)))
        (hsmall.le.trans hTle)
    have hψt : 0 < Ψ t := lt_of_lt_of_le zero_lt_one
      (hdag.gauge_admissible.2 (zero_le_one.trans ht))
    have hψM : 0 < Ψ (C⁻¹ * (3 : ℝ) ^ (M - h)) :=
      lt_of_lt_of_le zero_lt_one (hdag.gauge_admissible.2 (by positivity))
    calc
      P.real {a : CoeffSpace d |
          ENNReal.ofReal
            (max ((3 : ℝ) ^ M)
              (t * growthBar K ^ (4 * (d + 1)) *
                (3 : ℝ) ^ (M - jStar + 1))) <
            successorScale g E (M - jStar) a}
          = P.real {a : CoeffSpace d |
              ENNReal.ofReal ((3 : ℝ) ^ M) < successorScale g E h a} := by
                simp only [C, h, X, max_eq_left hXM.le]
      _ ≤ (Ψ (C⁻¹ * (3 : ℝ) ^ (M - h)))⁻¹ := by
        simpa only [C, h] using
          measureReal_successorScale_gt_zpow_le hstat hdag hQ hw le_rfl
      _ ≤ (Ψ t)⁻¹ := (inv_le_inv₀ hψM hψt).2 hψle

/-- The strict successor is finite almost surely. -/
theorem ae_successorScale_ne_top [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    (hstat : HCPoly.Frozen.IsStationaryLaw P) {g : ℝ} {E : BlockMat d}
    {Ψ : ℝ → ℝ} {K Q : ℝ} {S : CoeffSpace d → ℝ}
    (hdag : HCPoly.Frozen.CoarseEllipticityDagger P g E Ψ K S)
    {jStar M : ℤ} (hQ : 1 ≤ Q) (hw : IsCoupledWindow d Q K jStar M) :
    ∀ᵐ a ∂P, successorScale g E (M - jStar) a ≠ ⊤ := by
  let A : ℕ → Set (CoeffSpace d) := fun q =>
    {a | badScaleEvent g E (M - jStar) (M + (q : ℤ)) a}
  have hs : Summable fun q => P.real (A q) := by
    exact badScaleEvent_tail_summable hstat hdag hQ hw le_rfl
  have hmeasure : ∀ q, P (A q) = ENNReal.ofReal (P.real (A q)) := by
    intro q
    rw [Measure.real, ENNReal.ofReal_toReal (measure_ne_top P _)]
  have htop : (∑' q, P (A q)) ≠ ⊤ := by
    rw [show (∑' q, P (A q)) = ∑' q, ENNReal.ofReal (P.real (A q)) from
      tsum_congr hmeasure]
    exact hs.tsum_ofReal_ne_top
  filter_upwards [ae_eventually_notMem htop] with a ha
  obtain ⟨N, hN⟩ := eventually_atTop.1 ha
  have hall : ∀ m : ℤ, badScaleEvent g E (M - jStar) m a →
      m ≤ M + (N : ℤ) := by
    intro m hm
    by_contra hmn
    have hMm : M ≤ m := by omega
    let q : ℕ := (m - M).toNat
    have hmq : m = M + (q : ℤ) := by dsimp only [q]; omega
    have hNq : N ≤ q := by dsimp only [q]; omega
    exact hN q hNq (by simpa only [A, ← hmq] using! hm)
  have hsup : (⨆ (m : ℤ) (_ : badScaleEvent g E (M - jStar) m a),
      ENNReal.ofReal ((3 : ℝ) ^ m)) ≤
      ENNReal.ofReal ((3 : ℝ) ^ (M + (N : ℤ))) :=
    iSup_le fun m => iSup_le fun hm => ENNReal.ofReal_le_ofReal
      (zpow_le_zpow_right₀ (by norm_num) (hall m hm))
  have hfinite : successorScale g E (M - jStar) a < ⊤ := by
    calc
      successorScale g E (M - jStar) a ≤
          3 * ENNReal.ofReal ((3 : ℝ) ^ (M + (N : ℤ))) := by
            simpa only [successorScale] using
              mul_le_mul_of_nonneg_left hsup (by positivity : (0 : ℝ≥0∞) ≤ 3)
      _ < ⊤ := ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top
  exact hfinite.ne

end
end Window
end HighContrast
end HCPolySupport
