/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileCenterMeasurability

/-!
# High-contrast homogenization: Provider.Response.ProfileWeakFullLp

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Full annealed-centered weak estimates

The random optimizer average is replaced by its annealed center before the
pointwise diagonal estimate is integrated.  A sample map is retained so the
result applies directly to constant-skew recentering.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

private theorem aestronglyMeasurable_weakProfileMajorant
    {P : Measure (CoeffSpace d)} {U V En : CoeffSpace d → ℝ}
    {M : CoeffSpace d → ℝ≥0∞}
    (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    (hM : AEMeasurable M P) (hEn : AEMeasurable En P)
    (A B alpha : ℝ) (H : ℕ) :
    AEStronglyMeasurable (fun a ↦
      ENNReal.ofReal A * (ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) +
        ENNReal.ofReal B *
          (if (1 : ℝ≥0∞) < M a then
              M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
            else ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
              ENNReal.ofReal (En a))) P := by
  let bad : Set (CoeffSpace d) := {a | (1 : ℝ≥0∞) < M a}
  let good : Set (CoeffSpace d) := {a | M a ≤ (1 : ℝ≥0∞)}
  let badValue : CoeffSpace d → ℝ≥0∞ := fun a ↦
    M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
  let goodValue : CoeffSpace d → ℝ≥0∞ := fun a ↦
    ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) * ENNReal.ofReal (En a)
  have hEnOf : AEMeasurable (fun a ↦ ENNReal.ofReal (En a)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable hEn
  have hbadSet : NullMeasurableSet bad P :=
    nullMeasurableSet_lt aemeasurable_const hM
  have hgoodSet : NullMeasurableSet good P :=
    nullMeasurableSet_le hM aemeasurable_const
  have hbadValue : AEMeasurable badValue P :=
    (hM.pow_const (1 / 2 : ℝ)).mul hEnOf
  have hgoodValue : AEMeasurable goodValue P :=
    aemeasurable_const.mul hEnOf
  have hbranch : AEMeasurable (fun a ↦
      bad.indicator badValue a + good.indicator goodValue a) P :=
    (hbadValue.indicator₀ hbadSet).add (hgoodValue.indicator₀ hgoodSet)
  have hbranchEq : (fun a ↦
      if (1 : ℝ≥0∞) < M a then badValue a else goodValue a) =
      fun a ↦ bad.indicator badValue a + good.indicator goodValue a := by
    funext a
    by_cases hbad : (1 : ℝ≥0∞) < M a
    · have hbadMem : a ∈ bad := by
        simpa only [bad, Set.mem_ofPred_eq] using hbad
      have hnotGood : a ∉ good := by
        simpa only [good, Set.mem_ofPred_eq, not_le] using hbad
      rw [ite_eq_left hbad, Set.indicator_of_mem hbadMem,
        Set.indicator_of_notMem hnotGood, add_zero]
    · have hnotBad : a ∉ bad := by
        simpa only [bad, Set.mem_ofPred_eq] using hbad
      have hgood : a ∈ good := by
        simpa only [good, Set.mem_ofPred_eq] using le_of_not_gt hbad
      rw [ite_eq_right hbad, Set.indicator_of_notMem hnotBad,
        Set.indicator_of_mem hgood, zero_add]
  have hbranchIf : AEMeasurable (fun a ↦
      if (1 : ℝ≥0∞) < M a then badValue a else goodValue a) P := by
    rw [hbranchEq]
    exact hbranch
  have hrecent : AEMeasurable (fun a ↦
      ENNReal.ofReal A *
        (ENNReal.ofReal (U a) + ENNReal.ofReal (V a))) P :=
    aemeasurable_const.mul
      ((ENNReal.measurable_ofReal.comp_aemeasurable hU).add
        (ENNReal.measurable_ofReal.comp_aemeasurable hV))
  exact (hrecent.add (aemeasurable_const.mul hbranchIf)).aestronglyMeasurable

private theorem eLpNorm_fullWeakRoot_le_profileMajorant
    {P : Measure (CoeffSpace d)}
    {fullRoot center : CoeffSpace d → ℝ≥0∞}
    {U V En : CoeffSpace d → ℝ} {M : CoeffSpace d → ℝ≥0∞}
    (hU0 : ∀ a, 0 ≤ U a) (hV0 : ∀ a, 0 ≤ V a)
    (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    (hM : AEMeasurable M P) (hEn : AEMeasurable En P)
    (hcenter : AEMeasurable center P) {A B alpha c : ℝ} {H : ℕ}
    (hfinite : ∀ᵐ a ∂P, M a ≠ ⊤)
    (hpoint : ∀ᵐ a ∂P, fullRoot a ≤
      (ENNReal.ofReal A * (ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) +
        ENNReal.ofReal B *
          (if (1 : ℝ≥0∞) < M a then
              M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
            else ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
              ENNReal.ofReal (En a))) + ENNReal.ofReal c * center a)
    (hroot : AEStronglyMeasurable fullRoot P) :
    eLpNorm fullRoot 2 P ≤
      (ENNReal.ofReal A * (eLpNorm U 2 P + eLpNorm V 2 P) +
        ENNReal.ofReal B *
          (profileBadEnergy P M En + profileGoodEnergy P alpha H M En)) +
        ENNReal.ofReal c * eLpNorm center 2 P := by
  let majorant : CoeffSpace d → ℝ≥0∞ := fun a ↦
    ENNReal.ofReal A * (ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) +
      ENNReal.ofReal B *
        (if (1 : ℝ≥0∞) < M a then
            M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
          else ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
            ENNReal.ofReal (En a))
  have hmajorant : AEStronglyMeasurable majorant P :=
    aestronglyMeasurable_weakProfileMajorant hU hV hM hEn A B alpha H
  have hmono : eLpNorm fullRoot 2 P ≤
      eLpNorm (fun a ↦ majorant a + ENNReal.ofReal c * center a) 2 P := by
    apply eLpNorm_mono_enorm_ae hroot
    filter_upwards [hpoint] with a ha
    simpa only [majorant, enorm_eq_self] using ha
  have hmajorantNorm : eLpNorm majorant 2 P ≤
      ENNReal.ofReal A * (eLpNorm U 2 P + eLpNorm V 2 P) +
        ENNReal.ofReal B *
          (profileBadEnergy P M En + profileGoodEnergy P alpha H M En) := by
    refine eLpNorm_weakRoot_le_profileMajorant hU0 hV0 hU hV hM hEn hfinite ?_
      hmajorant
    filter_upwards [] with a
    exact le_rfl
  have htriangle := eLpNorm_add_le (f := majorant)
    (g := fun a ↦ ENNReal.ofReal c * center a) (μ := P) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcenterNorm : eLpNorm (fun a ↦ ENNReal.ofReal c * center a) 2 P ≤
      ENNReal.ofReal c * eLpNorm center 2 P :=
    eLpNorm_ofReal_mul_le hcenter.aestronglyMeasurable c 2
  exact hmono.trans (htriangle.trans (add_le_add hmajorantNorm hcenterNorm))

/-- The full primal weak root for an arbitrary coefficient sample map has
the recent, optimizer-event, and exact centering-variance bound. -/
theorem eLpNorm_profilePrimalWeakRoot_sample_le [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (H : ℕ) {m : Mat d} (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho alpha : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1)
    (halpha : alpha = (1 - rho) / 2)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    (hU : AEMeasurable
      (fun a ↦ diagonalWeakCellSum q t H (1 / 2) E (sample a)) P)
    (hV : AEMeasurable
      (fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rho E (sample a)) P)
    (hM : AEMeasurable
      (fun a ↦ diagonalWeakMaximum rho q t E (sample a)) P)
    (hEn : AEMeasurable
      (fun a ↦ diagonalWeakEnergy hq t (sample a) p r) P)
    (havg : AEMeasurable (fun a ↦ blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t (sample a) p r)) P)
    (hfinite : ∀ᵐ a ∂P, diagonalWeakMaximum rho q t E (sample a) ≠ ⊤)
    (hroot : AEStronglyMeasurable (profilePrimalWeakRoot m hq t sample p r
        (profilePrimalCenter P hq t sample p r)) P) :
    eLpNorm (profilePrimalWeakRoot m hq t sample p r
        (profilePrimalCenter P hq t sample p r)) 2 P ≤
      (ENNReal.ofReal (16 * diagonalWeakMetricFactor m E *
          diagonalWeakLoadMinus E p r) *
        (eLpNorm (fun a ↦ diagonalWeakCellSum q t H (1 / 2) E (sample a)) 2 P +
          eLpNorm (fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rho E
            (sample a)) 2 P) +
      ENNReal.ofReal (16 * diagonalWeakMetricFactor m E / (2 * alpha)) *
        (profileBadEnergy P (fun a ↦ diagonalWeakMaximum rho q t E (sample a))
            (fun a ↦ diagonalWeakEnergy hq t (sample a) p r) +
          profileGoodEnergy P alpha H
            (fun a ↦ diagonalWeakMaximum rho q t E (sample a))
            (fun a ↦ diagonalWeakEnergy hq t (sample a) p r))) +
      ENNReal.ofReal constantSeminormCoefficient *
        profilePrimalCenterVariance P m hq t sample p r := by
  let center := profilePrimalCenter P hq t sample p r
  let fluct : CoeffSpace d → ℝ≥0∞ := fun a ↦ ENNReal.ofReal
    (Real.sqrt (metricBlockNormSq m
      (blockCellAverage (adaptedCell q t)
        (diagonalWeakState hq t (sample a) p r) - center)))
  have hfluct : AEMeasurable fluct P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (AEMeasurable.sqrt_metricBlockNormSq_sub_const havg m center)
  apply eLpNorm_fullWeakRoot_le_profileMajorant
    (fun a ↦ diagonalWeakCellSum_nonneg q t H (1 / 2) E (sample a))
    (fun a ↦ diagonalWeakAverageSum_nonneg q t H (1 / 2) rho E (sample a))
    hU hV hM hEn hfluct hfinite ?_ hroot
  filter_upwards [hfinite] with a ha
  have hsplit := profilePrimalWeakRoot_le_randomCentered_add_constant
    hq t hm (sample a) p r center
  have hexp : -((1 / 2 : ℝ) * (t : ℝ)) =
      (-(1 / 2 : ℝ)) * (t : ℝ) := by ring
  rw [hexp] at hsplit
  have hraw := profilePrimalWeakRoot_randomCentered_le
    hq t H hm hE hEpd hrho hrho1 halpha (sample a) p r ha
  exact hsplit.trans (add_le_add hraw le_rfl)

/-- The full adjoint weak root retains its independent plus load under the
same arbitrary sample map. -/
theorem eLpNorm_profileAdjointWeakRoot_sample_le [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (H : ℕ) {m : Mat d} (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho alpha : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1)
    (halpha : alpha = (1 - rho) / 2)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    (hU : AEMeasurable
      (fun a ↦ diagonalWeakCellSum q t H (1 / 2) E (sample a)) P)
    (hV : AEMeasurable
      (fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rho E (sample a)) P)
    (hM : AEMeasurable
      (fun a ↦ diagonalWeakMaximum rho q t E (sample a)) P)
    (hEn : AEMeasurable
      (fun a ↦ diagonalWeakAdjointEnergy hq t (sample a) p r) P)
    (havg : AEMeasurable (fun a ↦ blockCellAverage (adaptedCell q t)
      (diagonalWeakAdjointState hq t (sample a) p r)) P)
    (hfinite : ∀ᵐ a ∂P, diagonalWeakMaximum rho q t E (sample a) ≠ ⊤)
    (hroot : AEStronglyMeasurable (profileAdjointWeakRoot m hq t sample p r
        (profileAdjointCenter P hq t sample p r)) P) :
    eLpNorm (profileAdjointWeakRoot m hq t sample p r
        (profileAdjointCenter P hq t sample p r)) 2 P ≤
      (ENNReal.ofReal (16 * diagonalWeakMetricFactor m E *
          diagonalWeakLoadPlus E p r) *
        (eLpNorm (fun a ↦ diagonalWeakCellSum q t H (1 / 2) E (sample a)) 2 P +
          eLpNorm (fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rho E
            (sample a)) 2 P) +
      ENNReal.ofReal (16 * diagonalWeakMetricFactor m E / (2 * alpha)) *
        (profileBadEnergy P (fun a ↦ diagonalWeakMaximum rho q t E (sample a))
            (fun a ↦ diagonalWeakAdjointEnergy hq t (sample a) p r) +
          profileGoodEnergy P alpha H
            (fun a ↦ diagonalWeakMaximum rho q t E (sample a))
            (fun a ↦ diagonalWeakAdjointEnergy hq t (sample a) p r))) +
      ENNReal.ofReal constantSeminormCoefficient *
        profileAdjointCenterVariance P m hq t sample p r := by
  let center := profileAdjointCenter P hq t sample p r
  let fluct : CoeffSpace d → ℝ≥0∞ := fun a ↦ ENNReal.ofReal
    (Real.sqrt (metricBlockNormSq m
      (blockCellAverage (adaptedCell q t)
        (diagonalWeakAdjointState hq t (sample a) p r) - center)))
  have hfluct : AEMeasurable fluct P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (AEMeasurable.sqrt_metricBlockNormSq_sub_const havg m center)
  apply eLpNorm_fullWeakRoot_le_profileMajorant
    (fun a ↦ diagonalWeakCellSum_nonneg q t H (1 / 2) E (sample a))
    (fun a ↦ diagonalWeakAverageSum_nonneg q t H (1 / 2) rho E (sample a))
    hU hV hM hEn hfluct hfinite ?_ hroot
  filter_upwards [hfinite] with a ha
  have hsplit := profileAdjointWeakRoot_le_randomCentered_add_constant
    hq t hm (sample a) p r center
  have hexp : -((1 / 2 : ℝ) * (t : ℝ)) =
      (-(1 / 2 : ℝ)) * (t : ℝ) := by ring
  rw [hexp] at hsplit
  have hraw := profileAdjointWeakRoot_randomCentered_le
    hq t H hm hE hEpd hrho hrho1 halpha (sample a) p r ha
  exact hsplit.trans (add_le_add hraw le_rfl)

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

private theorem aestronglyMeasurable_weakProfileMajorantAt
    {P : Measure (CoeffSpace d)} {U V En : CoeffSpace d → ℝ}
    {M : CoeffSpace d → ℝ≥0∞}
    (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    (hM : AEMeasurable M P) (hEn : AEMeasurable En P)
    (A B alpha : ℝ) (H : ℕ) (lev : ℝ≥0∞) :
    AEStronglyMeasurable (fun a ↦
      ENNReal.ofReal A * (ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) +
        ENNReal.ofReal B *
          (if lev < M a then
              M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
            else ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
              ENNReal.ofReal (En a))) P := by
  let bad : Set (CoeffSpace d) := {a | lev < M a}
  let good : Set (CoeffSpace d) := {a | M a ≤ lev}
  let badValue : CoeffSpace d → ℝ≥0∞ := fun a ↦
    M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
  let goodValue : CoeffSpace d → ℝ≥0∞ := fun a ↦
    ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) * ENNReal.ofReal (En a)
  have hEnOf : AEMeasurable (fun a ↦ ENNReal.ofReal (En a)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable hEn
  have hbadSet : NullMeasurableSet bad P :=
    nullMeasurableSet_lt aemeasurable_const hM
  have hgoodSet : NullMeasurableSet good P :=
    nullMeasurableSet_le hM aemeasurable_const
  have hbadValue : AEMeasurable badValue P :=
    (hM.pow_const (1 / 2 : ℝ)).mul hEnOf
  have hgoodValue : AEMeasurable goodValue P :=
    aemeasurable_const.mul hEnOf
  have hbranch : AEMeasurable (fun a ↦
      bad.indicator badValue a + good.indicator goodValue a) P :=
    (hbadValue.indicator₀ hbadSet).add (hgoodValue.indicator₀ hgoodSet)
  have hbranchEq : (fun a ↦
      if lev < M a then badValue a else goodValue a) =
      fun a ↦ bad.indicator badValue a + good.indicator goodValue a := by
    funext a
    by_cases hbad : lev < M a
    · have hbadMem : a ∈ bad := by
        simpa only [bad, Set.mem_ofPred_eq] using hbad
      have hnotGood : a ∉ good := by
        simpa only [good, Set.mem_ofPred_eq, not_le] using hbad
      rw [ite_eq_left hbad, Set.indicator_of_mem hbadMem,
        Set.indicator_of_notMem hnotGood, add_zero]
    · have hnotBad : a ∉ bad := by
        simpa only [bad, Set.mem_ofPred_eq] using hbad
      have hgood : a ∈ good := by
        simpa only [good, Set.mem_ofPred_eq] using le_of_not_gt hbad
      rw [ite_eq_right hbad, Set.indicator_of_notMem hnotBad,
        Set.indicator_of_mem hgood, zero_add]
  have hbranchIf : AEMeasurable (fun a ↦
      if lev < M a then badValue a else goodValue a) P := by
    rw [hbranchEq]
    exact hbranch
  have hrecent : AEMeasurable (fun a ↦
      ENNReal.ofReal A *
        (ENNReal.ofReal (U a) + ENNReal.ofReal (V a))) P :=
    aemeasurable_const.mul
      ((ENNReal.measurable_ofReal.comp_aemeasurable hU).add
        (ENNReal.measurable_ofReal.comp_aemeasurable hV))
  exact (hrecent.add (aemeasurable_const.mul hbranchIf)).aestronglyMeasurable

private theorem eLpNorm_fullWeakRoot_le_profileMajorantAt
    {P : Measure (CoeffSpace d)}
    {fullRoot center : CoeffSpace d → ℝ≥0∞}
    {U V En : CoeffSpace d → ℝ} {M : CoeffSpace d → ℝ≥0∞}
    (hU0 : ∀ a, 0 ≤ U a) (hV0 : ∀ a, 0 ≤ V a)
    (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    (hM : AEMeasurable M P) (hEn : AEMeasurable En P)
    (hcenter : AEMeasurable center P) {A B alpha c : ℝ} {H : ℕ}
    {lev : ℝ≥0∞}
    (hfinite : ∀ᵐ a ∂P, M a ≠ ⊤)
    (hpoint : ∀ᵐ a ∂P, fullRoot a ≤
      (ENNReal.ofReal A * (ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) +
        ENNReal.ofReal B *
          (if lev < M a then
              M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
            else ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
              ENNReal.ofReal (En a))) + ENNReal.ofReal c * center a)
    (hroot : AEStronglyMeasurable fullRoot P) :
    eLpNorm fullRoot 2 P ≤
      (ENNReal.ofReal A * (eLpNorm U 2 P + eLpNorm V 2 P) +
        ENNReal.ofReal B *
          (profileBadEnergyAt P lev M En +
            profileGoodEnergyAt P lev alpha H M En)) +
        ENNReal.ofReal c * eLpNorm center 2 P := by
  let majorant : CoeffSpace d → ℝ≥0∞ := fun a ↦
    ENNReal.ofReal A * (ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) +
      ENNReal.ofReal B *
        (if lev < M a then
            M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
          else ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
            ENNReal.ofReal (En a))
  have hmajorant : AEStronglyMeasurable majorant P :=
    aestronglyMeasurable_weakProfileMajorantAt hU hV hM hEn A B alpha H lev
  have hmono : eLpNorm fullRoot 2 P ≤
      eLpNorm (fun a ↦ majorant a + ENNReal.ofReal c * center a) 2 P := by
    apply eLpNorm_mono_enorm_ae hroot
    filter_upwards [hpoint] with a ha
    simpa only [majorant, enorm_eq_self] using ha
  have hmajorantNorm : eLpNorm majorant 2 P ≤
      ENNReal.ofReal A * (eLpNorm U 2 P + eLpNorm V 2 P) +
        ENNReal.ofReal B *
          (profileBadEnergyAt P lev M En +
            profileGoodEnergyAt P lev alpha H M En) := by
    refine eLpNorm_weakRoot_le_profileMajorantAt hU0 hV0 hU hV hM hEn hfinite ?_
      hmajorant
    filter_upwards [] with a
    exact le_rfl
  have htriangle := eLpNorm_add_le (f := majorant)
    (g := fun a ↦ ENNReal.ofReal c * center a) (μ := P) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hcenterNorm : eLpNorm (fun a ↦ ENNReal.ofReal c * center a) 2 P ≤
      ENNReal.ofReal c * eLpNorm center 2 P :=
    eLpNorm_ofReal_mul_le hcenter.aestronglyMeasurable c 2
  exact hmono.trans (htriangle.trans (add_le_add hmajorantNorm hcenterNorm))

/-- The full primal weak root at a released split level. -/
theorem eLpNorm_profilePrimalWeakRoot_sample_at_level_le [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (H : ℕ) {m : Mat d} (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho alpha lev : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hlev : 0 < lev)
    (halpha : alpha = (1 - rho) / 2)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    (hU : AEMeasurable
      (fun a ↦ diagonalWeakCellSum q t H (1 / 2) E (sample a)) P)
    (hV : AEMeasurable
      (fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rho E (sample a)) P)
    (hM : AEMeasurable
      (fun a ↦ diagonalWeakMaximum rho q t E (sample a)) P)
    (hEn : AEMeasurable
      (fun a ↦ diagonalWeakEnergy hq t (sample a) p r) P)
    (havg : AEMeasurable (fun a ↦ blockCellAverage (adaptedCell q t)
      (diagonalWeakState hq t (sample a) p r)) P)
    (hfinite : ∀ᵐ a ∂P, diagonalWeakMaximum rho q t E (sample a) ≠ ⊤)
    (hroot : AEStronglyMeasurable (profilePrimalWeakRoot m hq t sample p r
        (profilePrimalCenter P hq t sample p r)) P) :
    eLpNorm (profilePrimalWeakRoot m hq t sample p r
        (profilePrimalCenter P hq t sample p r)) 2 P ≤
      (ENNReal.ofReal (recentConstantAtLevel lev *
          diagonalWeakMetricFactor m E * diagonalWeakLoadMinus E p r) *
        (eLpNorm (fun a ↦ diagonalWeakCellSum q t H (1 / 2) E (sample a)) 2 P +
          eLpNorm (fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rho E
            (sample a)) 2 P) +
      ENNReal.ofReal (maxGroupConstantAtLevel lev *
          diagonalWeakMetricFactor m E / (2 * alpha)) *
        (profileBadEnergyAt P (ENNReal.ofReal lev)
            (fun a ↦ diagonalWeakMaximum rho q t E (sample a))
            (fun a ↦ diagonalWeakEnergy hq t (sample a) p r) +
          profileGoodEnergyAt P (ENNReal.ofReal lev) alpha H
            (fun a ↦ diagonalWeakMaximum rho q t E (sample a))
            (fun a ↦ diagonalWeakEnergy hq t (sample a) p r))) +
      ENNReal.ofReal constantSeminormCoefficient *
        profilePrimalCenterVariance P m hq t sample p r := by
  let center := profilePrimalCenter P hq t sample p r
  let fluct : CoeffSpace d → ℝ≥0∞ := fun a ↦ ENNReal.ofReal
    (Real.sqrt (metricBlockNormSq m
      (blockCellAverage (adaptedCell q t)
        (diagonalWeakState hq t (sample a) p r) - center)))
  have hfluct : AEMeasurable fluct P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (AEMeasurable.sqrt_metricBlockNormSq_sub_const havg m center)
  apply eLpNorm_fullWeakRoot_le_profileMajorantAt
    (fun a ↦ diagonalWeakCellSum_nonneg q t H (1 / 2) E (sample a))
    (fun a ↦ diagonalWeakAverageSum_nonneg q t H (1 / 2) rho E (sample a))
    hU hV hM hEn hfluct hfinite ?_ hroot
  filter_upwards [hfinite] with a ha
  have hsplit := profilePrimalWeakRoot_le_randomCentered_add_constant
    hq t hm (sample a) p r center
  have hexp : -((1 / 2 : ℝ) * (t : ℝ)) =
      (-(1 / 2 : ℝ)) * (t : ℝ) := by ring
  rw [hexp] at hsplit
  have hraw := profilePrimalWeakRoot_randomCentered_at_level_le
    hq t H hm hE hEpd hrho hrho1 hlev halpha (sample a) p r ha
  exact hsplit.trans (add_le_add hraw le_rfl)

/-- The full adjoint weak root at a released split level. -/
theorem eLpNorm_profileAdjointWeakRoot_sample_at_level_le [NeZero d]
    {P : Measure (CoeffSpace d)} {q : Mat d} (hq : q.PosDef)
    (t : ℤ) (H : ℕ) {m : Mat d} (hm : m.PosDef)
    {E : BlockMat d} (hE : IsSymmetricBlockMat E)
    (hEpd : BlockPosDef E) {rho alpha lev : ℝ}
    (hrho : 0 < rho) (hrho1 : rho < 1) (hlev : 0 < lev)
    (halpha : alpha = (1 - rho) / 2)
    (sample : CoeffSpace d → CoeffSpace d) (p r : Vec d)
    (hU : AEMeasurable
      (fun a ↦ diagonalWeakCellSum q t H (1 / 2) E (sample a)) P)
    (hV : AEMeasurable
      (fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rho E (sample a)) P)
    (hM : AEMeasurable
      (fun a ↦ diagonalWeakMaximum rho q t E (sample a)) P)
    (hEn : AEMeasurable
      (fun a ↦ diagonalWeakAdjointEnergy hq t (sample a) p r) P)
    (havg : AEMeasurable (fun a ↦ blockCellAverage (adaptedCell q t)
      (diagonalWeakAdjointState hq t (sample a) p r)) P)
    (hfinite : ∀ᵐ a ∂P, diagonalWeakMaximum rho q t E (sample a) ≠ ⊤)
    (hroot : AEStronglyMeasurable (profileAdjointWeakRoot m hq t sample p r
        (profileAdjointCenter P hq t sample p r)) P) :
    eLpNorm (profileAdjointWeakRoot m hq t sample p r
        (profileAdjointCenter P hq t sample p r)) 2 P ≤
      (ENNReal.ofReal (recentConstantAtLevel lev *
          diagonalWeakMetricFactor m E * diagonalWeakLoadPlus E p r) *
        (eLpNorm (fun a ↦ diagonalWeakCellSum q t H (1 / 2) E (sample a)) 2 P +
          eLpNorm (fun a ↦ diagonalWeakAverageSum q t H (1 / 2) rho E
            (sample a)) 2 P) +
      ENNReal.ofReal (maxGroupConstantAtLevel lev *
          diagonalWeakMetricFactor m E / (2 * alpha)) *
        (profileBadEnergyAt P (ENNReal.ofReal lev)
            (fun a ↦ diagonalWeakMaximum rho q t E (sample a))
            (fun a ↦ diagonalWeakAdjointEnergy hq t (sample a) p r) +
          profileGoodEnergyAt P (ENNReal.ofReal lev) alpha H
            (fun a ↦ diagonalWeakMaximum rho q t E (sample a))
            (fun a ↦ diagonalWeakAdjointEnergy hq t (sample a) p r))) +
      ENNReal.ofReal constantSeminormCoefficient *
        profileAdjointCenterVariance P m hq t sample p r := by
  let center := profileAdjointCenter P hq t sample p r
  let fluct : CoeffSpace d → ℝ≥0∞ := fun a ↦ ENNReal.ofReal
    (Real.sqrt (metricBlockNormSq m
      (blockCellAverage (adaptedCell q t)
        (diagonalWeakAdjointState hq t (sample a) p r) - center)))
  have hfluct : AEMeasurable fluct P :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (AEMeasurable.sqrt_metricBlockNormSq_sub_const havg m center)
  apply eLpNorm_fullWeakRoot_le_profileMajorantAt
    (fun a ↦ diagonalWeakCellSum_nonneg q t H (1 / 2) E (sample a))
    (fun a ↦ diagonalWeakAverageSum_nonneg q t H (1 / 2) rho E (sample a))
    hU hV hM hEn hfluct hfinite ?_ hroot
  filter_upwards [hfinite] with a ha
  have hsplit := profileAdjointWeakRoot_le_randomCentered_add_constant
    hq t hm (sample a) p r center
  have hexp : -((1 / 2 : ℝ) * (t : ℝ)) =
      (-(1 / 2 : ℝ)) * (t : ℝ) := by ring
  rw [hexp] at hsplit
  have hraw := profileAdjointWeakRoot_randomCentered_at_level_le
    hq t H hm hE hEpd hrho hrho1 hlev halpha (sample a) p r ha
  exact hsplit.trans (add_le_add hraw le_rfl)

end

end HCPolySupport.HighContrast.Response
