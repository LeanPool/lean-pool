/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileEnergyMeasurability
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileMaximumBadLp
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileRecentCellLp

/-!
# High-contrast homogenization: Provider.Response.ProfileEnergyLp

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Optimizer-energy bounds in probability

The bad branch uses the complete maximum only through its `Q`-norm, its
pathwise comparison with the total profile, and the total-profile moment.
The good branch uses only the deterministic pointwise energy bound.  The same
two arguments apply to the primal and coefficient-transpose optimizers.
-/

namespace HCPolySupport.HighContrast.Response

open MeasureTheory Book.Ch02

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- The all-scale response maximum is an a.e. measurable statistic. -/
theorem aemeasurable_diagonalWeakMaximum [NeZero d]
    {P : Measure (CoeffSpace d)} {rho : ℝ} {q : Mat d} (hq : q.PosDef)
    {t : ℤ} {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) :
    AEMeasurable (diagonalWeakMaximum rho q t E) P := by
  rw [show diagonalWeakMaximum rho q t E = fun a =>
      ⨆ (k : ℤ) (_ : k ≤ t) (w : Fin d → ℤ)
          (_ : w ∈ alignedIndex q k t),
        ENNReal.ofReal
          ((3 : ℝ) ^ (-rho * ((t : ℝ) - (k : ℝ))) *
            blockExcess (adaptedResponse q k w a) E) by
    funext a
    exact diagonalWeakMaximum_eq rho q t E a]
  exact AEMeasurable.iSup fun k => AEMeasurable.iSup fun _ =>
    AEMeasurable.iSup fun w => AEMeasurable.iSup fun _ =>
      aemeasurable_source_excess_term hq t k w hE hEpd

/-- A finite positive `L^Q` bound forces an extended-real statistic to be
finite almost everywhere. -/
theorem ae_ne_top_of_eLpNorm_le_ofReal
    {P : Measure (CoeffSpace d)} {Q c : ℝ} (hQ : 0 < Q)
    {M : CoeffSpace d → ℝ≥0∞} (hM : AEMeasurable M P)
    (hnorm : eLpNorm M (ENNReal.ofReal Q) P ≤ ENNReal.ofReal c) :
    ∀ᵐ a ∂P, M a ≠ ⊤ := by
  have hp0 : ENNReal.ofReal Q ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact hQ
  have hnormTop : eLpNorm M (ENNReal.ofReal Q) P < ⊤ :=
    hnorm.trans_lt ENNReal.ofReal_lt_top
  have hlinRaw := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    hp0 ENNReal.ofReal_ne_top hnormTop
  have hlin : (∫⁻ a, M a ^ Q ∂P) < ⊤ := by
    simpa only [ENNReal.toReal_ofReal hQ.le, enorm_eq_self] using hlinRaw
  filter_upwards [ae_lt_top' (hM.pow_const Q) hlin.ne] with a ha
  exact ((ENNReal.rpow_lt_top_iff_of_pos hQ).mp ha).ne

/-- Multiplying an energy by the square root of a finite extended-real
maximum turns a real square-root estimate into a linear maximum estimate. -/
theorem rpow_half_mul_ofReal_le_of_le_sqrt_toReal
    {x : ℝ≥0∞} (hx : x ≠ ⊤) {energy C : ℝ} (hC : 0 ≤ C)
    (henergy : energy ≤ C * Real.sqrt x.toReal) :
    x ^ (1 / 2 : ℝ) * ENNReal.ofReal energy ≤ ENNReal.ofReal C * x := by
  have hx0 : 0 ≤ x.toReal := ENNReal.toReal_nonneg
  have hroot0 : 0 ≤ Real.sqrt x.toReal := Real.sqrt_nonneg _
  have hroot : x ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt x.toReal) := by
    calc
      x ^ (1 / 2 : ℝ) =
          (ENNReal.ofReal x.toReal) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.ofReal_toReal hx]
      _ = ENNReal.ofReal (x.toReal ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hx0 (by norm_num)]
      _ = ENNReal.ofReal (Real.sqrt x.toReal) := by
        rw [Real.sqrt_eq_rpow]
  have hreal : Real.sqrt x.toReal * (C * Real.sqrt x.toReal) =
      C * x.toReal := by
    rw [show Real.sqrt x.toReal * (C * Real.sqrt x.toReal) =
        C * (Real.sqrt x.toReal) ^ 2 by ring,
      Real.sq_sqrt hx0]
  calc
    x ^ (1 / 2 : ℝ) * ENNReal.ofReal energy =
        ENNReal.ofReal (Real.sqrt x.toReal) * ENNReal.ofReal energy := by
      rw [hroot]
    _ ≤ ENNReal.ofReal (Real.sqrt x.toReal) *
        ENNReal.ofReal (C * Real.sqrt x.toReal) :=
      mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal henergy) zero_le
    _ = ENNReal.ofReal (Real.sqrt x.toReal *
        (C * Real.sqrt x.toReal)) := by
      rw [← ENNReal.ofReal_mul hroot0]
    _ = ENNReal.ofReal C * ENNReal.ofReal x.toReal := by
      rw [hreal, ENNReal.ofReal_mul hC]
    _ = ENNReal.ofReal C * x := by
      rw [ENNReal.ofReal_toReal hx]

/-- Generic bad-branch energy estimate driven by the complete maximum. -/
theorem profileBadEnergy_le_of_complete_maximum
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {Q h beta : ℝ} (hQ : 2 < Q) (hh : 0 ≤ h) (hbeta : 0 ≤ beta)
    {M W : CoeffSpace d → ℝ≥0∞} (hM : AEMeasurable M P)
    (hW : AEMeasurable W P)
    (hpoint : ∀ a, M a ≤ W a + ENNReal.ofReal beta)
    (hnorm : eLpNorm M (ENNReal.ofReal Q) P ≤
      ENNReal.ofReal (h ^ Q⁻¹ + beta))
    (hmoment : ∫⁻ a, W a ^ Q ∂P ≤ ENNReal.ofReal h)
    {energy : CoeffSpace d → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (henergy : ∀ a, M a ≠ ⊤ → (1 : ℝ≥0∞) < M a →
      energy a ≤ C * Real.sqrt (M a).toReal)
    (hmeas : AEStronglyMeasurable ({a | (1 : ℝ≥0∞) < M a}.indicator fun a =>
      M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (energy a)) P) :
    profileBadEnergy P M energy ≤
      ENNReal.ofReal (C * profileBadMajorant Q h beta) := by
  let bad : Set (CoeffSpace d) := {a | (1 : ℝ≥0∞) < M a}
  have hfinite := ae_ne_top_of_eLpNorm_le_ofReal
    (lt_trans (by norm_num) hQ) hM hnorm
  have hbadNull : NullMeasurableSet bad P :=
    nullMeasurableSet_lt aemeasurable_const hM
  have hbadM : AEStronglyMeasurable (bad.indicator M) P :=
    (hM.indicator₀ hbadNull).aestronglyMeasurable
  have hmono : eLpNorm (bad.indicator fun a =>
      M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (energy a)) 2 P ≤
      eLpNorm (fun a => ENNReal.ofReal C * bad.indicator M a) 2 P := by
    have hmeasBad : AEStronglyMeasurable (bad.indicator fun a =>
        M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (energy a)) P := hmeas
    apply eLpNorm_mono_enorm_ae hmeasBad
    filter_upwards [hfinite] with a ha
    by_cases habad : a ∈ bad
    · simp only [Set.indicator_of_mem habad, enorm_eq_self]
      exact rpow_half_mul_ofReal_le_of_le_sqrt_toReal ha hC
        (henergy a ha habad)
    · simp only [Set.indicator_of_notMem habad, mul_zero, enorm_zero]
      exact le_rfl
  have hmaximum := eLpNorm_indicator_gt_one_le_profileBadMajorant
    P hQ hh hbeta hM hW hpoint hnorm hmoment
  calc
    profileBadEnergy P M energy ≤
        eLpNorm (fun a => ENNReal.ofReal C * bad.indicator M a) 2 P := hmono
    _ ≤ ENNReal.ofReal C * eLpNorm (bad.indicator M) 2 P :=
      eLpNorm_ofReal_mul_le hbadM C 2
    _ ≤ ENNReal.ofReal C *
        ENNReal.ofReal (profileBadMajorant Q h beta) :=
      mul_le_mul_of_nonneg_left (by simpa only [bad] using hmaximum) zero_le
    _ = ENNReal.ofReal (C * profileBadMajorant Q h beta) := by
      rw [← ENNReal.ofReal_mul hC]

/-- Generic good-branch energy estimate. -/
theorem profileGoodEnergy_le_of_pointwise
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {alpha : ℝ} {H : ℕ} {M : CoeffSpace d → ℝ≥0∞}
    {energy : CoeffSpace d → ℝ} {C : ℝ}
    (henergy : ∀ a, M a ≤ (1 : ℝ≥0∞) → energy a ≤ C)
    (hmeas : AEStronglyMeasurable ({a | M a ≤ (1 : ℝ≥0∞)}.indicator fun a =>
      ENNReal.ofReal (energy a)) P) :
    profileGoodEnergy P alpha H M energy ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ)) * C) := by
  let good : Set (CoeffSpace d) := {a | M a ≤ (1 : ℝ≥0∞)}
  have hconst : eLpNorm (good.indicator fun a => ENNReal.ofReal (energy a)) 2 P ≤
      ENNReal.ofReal C := by
    calc
      eLpNorm (good.indicator fun a => ENNReal.ofReal (energy a)) 2 P ≤
          eLpNorm (fun _ : CoeffSpace d => ENNReal.ofReal C) 2 P := by
        have hmeasGood : AEStronglyMeasurable (good.indicator fun a =>
            ENNReal.ofReal (energy a)) P := hmeas
        apply eLpNorm_mono_enorm hmeasGood
        intro a
        by_cases hgood : a ∈ good
        · simp only [Set.indicator_of_mem hgood, enorm_eq_self]
          exact ENNReal.ofReal_le_ofReal (henergy a hgood)
        · simp only [Set.indicator_of_notMem hgood, enorm_zero]
          exact zero_le
      _ = ENNReal.ofReal C := by
        rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero P),
          measure_univ, ENNReal.one_rpow, mul_one, enorm_eq_self]
  have hfac0 : 0 ≤ (3 : ℝ) ^ (-alpha * (H : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    profileGoodEnergy P alpha H M energy ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
          ENNReal.ofReal C :=
      mul_le_mul_of_nonneg_left hconst zero_le
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ)) * C) := by
      rw [← ENNReal.ofReal_mul hfac0]

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

/-- The released good-event optimizer energy from a pointwise bound on the
released good event. -/
theorem profileGoodEnergyAt_le_of_pointwise
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {alpha : ℝ} {H : ℕ} {lev : ℝ≥0∞} {M : CoeffSpace d → ℝ≥0∞}
    {energy : CoeffSpace d → ℝ} {C : ℝ}
    (henergy : ∀ a, M a ≤ lev → energy a ≤ C)
    (hmeas : AEStronglyMeasurable ({a | M a ≤ lev}.indicator fun a =>
      ENNReal.ofReal (energy a)) P) :
    profileGoodEnergyAt P lev alpha H M energy ≤
      ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ)) * C) := by
  let good : Set (CoeffSpace d) := {a | M a ≤ lev}
  have hconst : eLpNorm (good.indicator fun a => ENNReal.ofReal (energy a)) 2 P ≤
      ENNReal.ofReal C := by
    calc
      eLpNorm (good.indicator fun a => ENNReal.ofReal (energy a)) 2 P ≤
          eLpNorm (fun _ : CoeffSpace d => ENNReal.ofReal C) 2 P := by
        have hmeasGood : AEStronglyMeasurable (good.indicator fun a =>
            ENNReal.ofReal (energy a)) P := hmeas
        apply eLpNorm_mono_enorm hmeasGood
        intro a
        by_cases hgood : a ∈ good
        · simp only [Set.indicator_of_mem hgood, enorm_eq_self]
          exact ENNReal.ofReal_le_ofReal (henergy a hgood)
        · simp only [Set.indicator_of_notMem hgood, enorm_zero]
          exact zero_le
      _ = ENNReal.ofReal C := by
        rw [eLpNorm_const _ (by norm_num) (IsProbabilityMeasure.ne_zero P),
          measure_univ, ENNReal.one_rpow, mul_one, enorm_eq_self]
  have hfac0 : 0 ≤ (3 : ℝ) ^ (-alpha * (H : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  calc
    profileGoodEnergyAt P lev alpha H M energy ≤
        ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
          ENNReal.ofReal C :=
      mul_le_mul_of_nonneg_left hconst zero_le
    _ = ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ)) * C) := by
      rw [← ENNReal.ofReal_mul hfac0]

/-- The primal good optimizer energy at a released split level. -/
theorem profileGoodEnergyAt_diagonalWeakEnergy_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {alpha rho lev : ℝ} {H : ℕ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hlev : 1 ≤ lev) (p r : Vec d) :
    profileGoodEnergyAt P (ENNReal.ofReal lev) alpha H
      (diagonalWeakMaximum rho q t E)
      (fun a => diagonalWeakEnergy hq t a p r) ≤
      ENNReal.ofReal (energyGoodConstantAtLevel lev *
        (3 : ℝ) ^ (-alpha * (H : ℝ)) *
        profileEnergyLoad (diagonalWeakLoadMinus E p r) p r) := by
  have hmain := profileGoodEnergyAt_le_of_pointwise
    (P := P) (alpha := alpha) (H := H) (lev := ENNReal.ofReal lev)
    (M := diagonalWeakMaximum rho q t E)
    (energy := fun a => diagonalWeakEnergy hq t a p r)
    (C := energyGoodConstantAtLevel lev *
      profileEnergyLoad (diagonalWeakLoadMinus E p r) p r)
    (fun a hgood => diagonalWeakEnergy_le_sqrt_two_mul_good_at_level
      hq hE hEpd p r hlev hgood)
    ((ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_diagonalWeakEnergy hq t p r)).indicator₀
      (nullMeasurableSet_le (aemeasurable_diagonalWeakMaximum hq hE hEpd)
        aemeasurable_const)).aestronglyMeasurable
  exact hmain.trans_eq (congrArg ENNReal.ofReal (by ring))

/-- The adjoint good optimizer energy at a released split level. -/
theorem profileGoodEnergyAt_diagonalWeakAdjointEnergy_le [NeZero d]
    {P : Measure (CoeffSpace d)} [IsProbabilityMeasure P]
    {alpha rho lev : ℝ} {H : ℕ} {q : Mat d} (hq : q.PosDef) {t : ℤ}
    {E : BlockMat d} (hE : IsSymmetricBlockMat E) (hEpd : BlockPosDef E)
    (hlev : 1 ≤ lev) (p r : Vec d) :
    profileGoodEnergyAt P (ENNReal.ofReal lev) alpha H
      (diagonalWeakMaximum rho q t E)
      (fun a => diagonalWeakAdjointEnergy hq t a p r) ≤
      ENNReal.ofReal (energyGoodConstantAtLevel lev *
        (3 : ℝ) ^ (-alpha * (H : ℝ)) *
        profileEnergyLoad (diagonalWeakLoadPlus E p r) p r) := by
  have hmain := profileGoodEnergyAt_le_of_pointwise
    (P := P) (alpha := alpha) (H := H) (lev := ENNReal.ofReal lev)
    (M := diagonalWeakMaximum rho q t E)
    (energy := fun a => diagonalWeakAdjointEnergy hq t a p r)
    (C := energyGoodConstantAtLevel lev *
      profileEnergyLoad (diagonalWeakLoadPlus E p r) p r)
    (fun a hgood => diagonalWeakAdjointEnergy_le_sqrt_two_mul_good_at_level
      hq hE hEpd p r hlev hgood)
    ((ENNReal.measurable_ofReal.comp_aemeasurable
      (aemeasurable_diagonalWeakAdjointEnergy hq t p r)).indicator₀
      (nullMeasurableSet_le (aemeasurable_diagonalWeakMaximum hq hE hEpd)
        aemeasurable_const)).aestronglyMeasurable
  exact hmain.trans_eq (congrArg ENNReal.ofReal (by ring))

end

end HCPolySupport.HighContrast.Response
