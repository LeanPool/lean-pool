/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileWeakPointwise
public import LeanPool.HighContrastHomogenization.Provider.Response.ProfileEnergyLp
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# High-contrast homogenization: Provider.Response.ProfileWeakLp

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Probabilistic random-centered weak estimates

The pointwise diagonal estimate is integrated after its maximum is known to
be finite almost everywhere.  The two maximum events remain correlated with
the optimizer energy throughout this step.
-/

namespace HCPolySupport.HighContrast.Response

open Book.Ch02 MeasureTheory

open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- A pointwise weak-root majorant with the exact recent and optimizer-event
terms passes to the corresponding `L²` bound. -/
theorem eLpNorm_weakRoot_le_profileMajorant
    {P : Measure (CoeffSpace d)} {root : CoeffSpace d → ℝ≥0∞}
    {U V En : CoeffSpace d → ℝ} {M : CoeffSpace d → ℝ≥0∞}
    (hU0 : ∀ a, 0 ≤ U a) (hV0 : ∀ a, 0 ≤ V a)
    (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    (hM : AEMeasurable M P) (hEn : AEMeasurable En P)
    {A B alpha : ℝ} {H : ℕ}
    (hfinite : ∀ᵐ a ∂P, M a ≠ ⊤)
    (hpoint : ∀ᵐ a ∂P, root a ≤
      ENNReal.ofReal A * (ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) +
        ENNReal.ofReal B *
          (if (1 : ℝ≥0∞) < M a then
              M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
            else ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
              ENNReal.ofReal (En a)))
    (hroot : AEStronglyMeasurable root P) :
    eLpNorm root 2 P ≤
      ENNReal.ofReal A * (eLpNorm U 2 P + eLpNorm V 2 P) +
        ENNReal.ofReal B *
          (profileBadEnergy P M En + profileGoodEnergy P alpha H M En) := by
  let bad : Set (CoeffSpace d) := {a | (1 : ℝ≥0∞) < M a}
  let good : Set (CoeffSpace d) := {a | M a ≤ (1 : ℝ≥0∞)}
  let badEnergy : CoeffSpace d → ℝ≥0∞ := bad.indicator fun a ↦
    M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
  let goodEnergy : CoeffSpace d → ℝ≥0∞ := good.indicator fun a ↦
    ENNReal.ofReal (En a)
  let R : ℝ := (3 : ℝ) ^ (-alpha * (H : ℝ))
  have hbadSet : NullMeasurableSet bad P :=
    nullMeasurableSet_lt aemeasurable_const hM
  have hgoodSet : NullMeasurableSet good P :=
    nullMeasurableSet_le hM aemeasurable_const
  have hEnOf : AEMeasurable (fun a ↦ ENNReal.ofReal (En a)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable hEn
  have hbadMeas : AEStronglyMeasurable badEnergy P := by
    exact ((hM.pow_const (1 / 2 : ℝ)).mul hEnOf).indicator₀
      hbadSet |>.aestronglyMeasurable
  have hgoodMeas : AEStronglyMeasurable goodEnergy P := by
    exact hEnOf.indicator₀ hgoodSet |>.aestronglyMeasurable
  have hUOf : AEStronglyMeasurable (fun a ↦ ENNReal.ofReal (U a)) P :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hU).aestronglyMeasurable
  have hVOf : AEStronglyMeasurable (fun a ↦ ENNReal.ofReal (V a)) P :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hV).aestronglyMeasurable
  have hUV : AEStronglyMeasurable
      (fun a ↦ ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) P :=
    hUOf.add hVOf
  have hRgood : AEStronglyMeasurable
      (fun a ↦ ENNReal.ofReal R * goodEnergy a) P :=
    (aemeasurable_const.mul hgoodMeas.aemeasurable).aestronglyMeasurable
  have henergies : AEStronglyMeasurable
      (fun a ↦ badEnergy a + ENNReal.ofReal R * goodEnergy a) P :=
    hbadMeas.add hRgood
  have hbranch : ∀ a,
      (if (1 : ℝ≥0∞) < M a then
          M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
        else ENNReal.ofReal R * ENNReal.ofReal (En a)) =
        badEnergy a + ENNReal.ofReal R * goodEnergy a := by
    intro a
    by_cases hbad : (1 : ℝ≥0∞) < M a
    · have hnotGood : a ∉ good := by
        simpa only [good, Set.mem_ofPred_eq, not_le] using hbad
      have hbadMem : a ∈ bad := by
        simpa only [bad, Set.mem_ofPred_eq] using hbad
      rw [ite_eq_left hbad, show badEnergy a =
          M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a) by
            exact Set.indicator_of_mem hbadMem _,
        show goodEnergy a = (0 : ℝ≥0∞) by
          exact Set.indicator_of_notMem hnotGood _]
      simp only [mul_zero, add_zero]
    · have hgood : a ∈ good := by
        simpa only [good, Set.mem_ofPred_eq] using le_of_not_gt hbad
      have hnotBad : a ∉ bad := by
        simpa only [bad, Set.mem_ofPred_eq] using hbad
      rw [ite_eq_right hbad,
        show badEnergy a = (0 : ℝ≥0∞) by
          exact Set.indicator_of_notMem hnotBad _,
        show goodEnergy a = ENNReal.ofReal (En a) by
          exact Set.indicator_of_mem hgood _]
      simp only [zero_add]
  have hmono : eLpNorm root 2 P ≤ eLpNorm
      (fun a ↦
        ENNReal.ofReal A *
            (ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) +
          ENNReal.ofReal B *
            (badEnergy a + ENNReal.ofReal R * goodEnergy a)) 2 P := by
    apply eLpNorm_mono_enorm_ae hroot
    filter_upwards [hpoint, hfinite] with a ha _
    simpa only [enorm_eq_self, R, hbranch a] using ha
  have htriangle := eLpNorm_add_le
    (f := fun a ↦ ENNReal.ofReal A * (ENNReal.ofReal (U a) + ENNReal.ofReal (V a)))
    (g := fun a ↦ ENNReal.ofReal B * (badEnergy a + ENNReal.ofReal R * goodEnergy a))
    (μ := P) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hrecentNorm : eLpNorm (fun a ↦
      ENNReal.ofReal A *
        (ENNReal.ofReal (U a) + ENNReal.ofReal (V a))) 2 P ≤
      ENNReal.ofReal A * (eLpNorm U 2 P + eLpNorm V 2 P) := by
    calc
      eLpNorm (fun a ↦ ENNReal.ofReal A *
          (ENNReal.ofReal (U a) + ENNReal.ofReal (V a))) 2 P ≤
          ENNReal.ofReal A * eLpNorm
            (fun a ↦ ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) 2 P :=
        eLpNorm_ofReal_mul_le hUV A 2
      _ ≤ ENNReal.ofReal A *
          (eLpNorm (ENNReal.ofReal ∘ U) 2 P +
            eLpNorm (ENNReal.ofReal ∘ V) 2 P) :=
        mul_le_mul_right (eLpNorm_add_le (f := ENNReal.ofReal ∘ U)
          (g := ENNReal.ofReal ∘ V) (by norm_num)) _
      _ = ENNReal.ofReal A * (eLpNorm U 2 P + eLpNorm V 2 P) := by
        rw [eLpNorm_ofReal U (_root_.Filter.Eventually.of_forall hU0),
          eLpNorm_ofReal V (_root_.Filter.Eventually.of_forall hV0)]
  have hgoodNorm : eLpNorm
      (fun a ↦ ENNReal.ofReal R * goodEnergy a) 2 P ≤
      profileGoodEnergy P alpha H M En := by
    simpa only [profileGoodEnergy, R, goodEnergy, good] using
      eLpNorm_ofReal_mul_le hgoodMeas R 2
  have henergyNorm : eLpNorm (fun a ↦
      ENNReal.ofReal B *
        (badEnergy a + ENNReal.ofReal R * goodEnergy a)) 2 P ≤
      ENNReal.ofReal B *
        (profileBadEnergy P M En + profileGoodEnergy P alpha H M En) := by
    calc
      eLpNorm (fun a ↦ ENNReal.ofReal B *
          (badEnergy a + ENNReal.ofReal R * goodEnergy a)) 2 P ≤
          ENNReal.ofReal B * eLpNorm
            (fun a ↦ badEnergy a + ENNReal.ofReal R * goodEnergy a) 2 P :=
        eLpNorm_ofReal_mul_le henergies B 2
      _ ≤ ENNReal.ofReal B *
          (eLpNorm badEnergy 2 P +
            eLpNorm (fun a ↦ ENNReal.ofReal R * goodEnergy a) 2 P) :=
        mul_le_mul_right (eLpNorm_add_le (f := badEnergy)
          (g := fun a ↦ ENNReal.ofReal R * goodEnergy a) (by norm_num)) _
      _ ≤ ENNReal.ofReal B *
          (profileBadEnergy P M En + profileGoodEnergy P alpha H M En) :=
        mul_le_mul_right (add_le_add (by rfl) hgoodNorm) _
  exact hmono.trans (htriangle.trans (add_le_add hrecentNorm henergyNorm))

/-! ## The released split level -/

open Book.Ch02 MeasureTheory

open scoped ENNReal

/-- The `L²` weak-root majorant at a released split level. -/
theorem eLpNorm_weakRoot_le_profileMajorantAt
    {P : Measure (CoeffSpace d)} {root : CoeffSpace d → ℝ≥0∞}
    {U V En : CoeffSpace d → ℝ} {M : CoeffSpace d → ℝ≥0∞}
    (hU0 : ∀ a, 0 ≤ U a) (hV0 : ∀ a, 0 ≤ V a)
    (hU : AEMeasurable U P) (hV : AEMeasurable V P)
    (hM : AEMeasurable M P) (hEn : AEMeasurable En P)
    {A B alpha : ℝ} {H : ℕ} {lev : ℝ≥0∞}
    (hfinite : ∀ᵐ a ∂P, M a ≠ ⊤)
    (hpoint : ∀ᵐ a ∂P, root a ≤
      ENNReal.ofReal A * (ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) +
        ENNReal.ofReal B *
          (if lev < M a then
              M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
            else ENNReal.ofReal ((3 : ℝ) ^ (-alpha * (H : ℝ))) *
              ENNReal.ofReal (En a)))
    (hroot : AEStronglyMeasurable root P) :
    eLpNorm root 2 P ≤
      ENNReal.ofReal A * (eLpNorm U 2 P + eLpNorm V 2 P) +
        ENNReal.ofReal B *
          (profileBadEnergyAt P lev M En +
            profileGoodEnergyAt P lev alpha H M En) := by
  let bad : Set (CoeffSpace d) := {a | lev < M a}
  let good : Set (CoeffSpace d) := {a | M a ≤ lev}
  let badEnergy : CoeffSpace d → ℝ≥0∞ := bad.indicator fun a ↦
    M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
  let goodEnergy : CoeffSpace d → ℝ≥0∞ := good.indicator fun a ↦
    ENNReal.ofReal (En a)
  let R : ℝ := (3 : ℝ) ^ (-alpha * (H : ℝ))
  have hbadSet : NullMeasurableSet bad P :=
    nullMeasurableSet_lt aemeasurable_const hM
  have hgoodSet : NullMeasurableSet good P :=
    nullMeasurableSet_le hM aemeasurable_const
  have hEnOf : AEMeasurable (fun a ↦ ENNReal.ofReal (En a)) P :=
    ENNReal.measurable_ofReal.comp_aemeasurable hEn
  have hbadMeas : AEStronglyMeasurable badEnergy P := by
    exact ((hM.pow_const (1 / 2 : ℝ)).mul hEnOf).indicator₀
      hbadSet |>.aestronglyMeasurable
  have hgoodMeas : AEStronglyMeasurable goodEnergy P := by
    exact hEnOf.indicator₀ hgoodSet |>.aestronglyMeasurable
  have hUOf : AEStronglyMeasurable (fun a ↦ ENNReal.ofReal (U a)) P :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hU).aestronglyMeasurable
  have hVOf : AEStronglyMeasurable (fun a ↦ ENNReal.ofReal (V a)) P :=
    (ENNReal.measurable_ofReal.comp_aemeasurable hV).aestronglyMeasurable
  have hUV : AEStronglyMeasurable
      (fun a ↦ ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) P :=
    hUOf.add hVOf
  have hRgood : AEStronglyMeasurable
      (fun a ↦ ENNReal.ofReal R * goodEnergy a) P :=
    (aemeasurable_const.mul hgoodMeas.aemeasurable).aestronglyMeasurable
  have henergies : AEStronglyMeasurable
      (fun a ↦ badEnergy a + ENNReal.ofReal R * goodEnergy a) P :=
    hbadMeas.add hRgood
  have hbranch : ∀ a,
      (if lev < M a then
          M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a)
        else ENNReal.ofReal R * ENNReal.ofReal (En a)) =
        badEnergy a + ENNReal.ofReal R * goodEnergy a := by
    intro a
    by_cases hbad : lev < M a
    · have hnotGood : a ∉ good := by
        simpa only [good, Set.mem_ofPred_eq, not_le] using hbad
      have hbadMem : a ∈ bad := by
        simpa only [bad, Set.mem_ofPred_eq] using hbad
      rw [ite_eq_left hbad, show badEnergy a =
          M a ^ (1 / 2 : ℝ) * ENNReal.ofReal (En a) by
            exact Set.indicator_of_mem hbadMem _,
        show goodEnergy a = (0 : ℝ≥0∞) by
          exact Set.indicator_of_notMem hnotGood _]
      simp only [mul_zero, add_zero]
    · have hgood : a ∈ good := by
        simpa only [good, Set.mem_ofPred_eq] using le_of_not_gt hbad
      have hnotBad : a ∉ bad := by
        simpa only [bad, Set.mem_ofPred_eq] using hbad
      rw [ite_eq_right hbad,
        show badEnergy a = (0 : ℝ≥0∞) by
          exact Set.indicator_of_notMem hnotBad _,
        show goodEnergy a = ENNReal.ofReal (En a) by
          exact Set.indicator_of_mem hgood _]
      simp only [zero_add]
  have hmono : eLpNorm root 2 P ≤ eLpNorm
      (fun a ↦
        ENNReal.ofReal A *
            (ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) +
          ENNReal.ofReal B *
            (badEnergy a + ENNReal.ofReal R * goodEnergy a)) 2 P := by
    apply eLpNorm_mono_enorm_ae hroot
    filter_upwards [hpoint, hfinite] with a ha _
    simpa only [enorm_eq_self, R, hbranch a] using ha
  have htriangle := eLpNorm_add_le
    (f := fun a ↦ ENNReal.ofReal A * (ENNReal.ofReal (U a) + ENNReal.ofReal (V a)))
    (g := fun a ↦ ENNReal.ofReal B * (badEnergy a + ENNReal.ofReal R * goodEnergy a))
    (μ := P) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hrecentNorm : eLpNorm (fun a ↦
      ENNReal.ofReal A *
        (ENNReal.ofReal (U a) + ENNReal.ofReal (V a))) 2 P ≤
      ENNReal.ofReal A * (eLpNorm U 2 P + eLpNorm V 2 P) := by
    calc
      eLpNorm (fun a ↦ ENNReal.ofReal A *
          (ENNReal.ofReal (U a) + ENNReal.ofReal (V a))) 2 P ≤
          ENNReal.ofReal A * eLpNorm
            (fun a ↦ ENNReal.ofReal (U a) + ENNReal.ofReal (V a)) 2 P :=
        eLpNorm_ofReal_mul_le hUV A 2
      _ ≤ ENNReal.ofReal A *
          (eLpNorm (ENNReal.ofReal ∘ U) 2 P +
            eLpNorm (ENNReal.ofReal ∘ V) 2 P) :=
        mul_le_mul_right (eLpNorm_add_le (f := ENNReal.ofReal ∘ U)
          (g := ENNReal.ofReal ∘ V) (by norm_num)) _
      _ = ENNReal.ofReal A * (eLpNorm U 2 P + eLpNorm V 2 P) := by
        rw [eLpNorm_ofReal U (_root_.Filter.Eventually.of_forall hU0),
          eLpNorm_ofReal V (_root_.Filter.Eventually.of_forall hV0)]
  have hgoodNorm : eLpNorm
      (fun a ↦ ENNReal.ofReal R * goodEnergy a) 2 P ≤
      profileGoodEnergyAt P lev alpha H M En := by
    simpa only [profileGoodEnergyAt, R, goodEnergy, good] using
      eLpNorm_ofReal_mul_le hgoodMeas R 2
  have henergyNorm : eLpNorm (fun a ↦
      ENNReal.ofReal B *
        (badEnergy a + ENNReal.ofReal R * goodEnergy a)) 2 P ≤
      ENNReal.ofReal B *
        (profileBadEnergyAt P lev M En +
          profileGoodEnergyAt P lev alpha H M En) := by
    calc
      eLpNorm (fun a ↦ ENNReal.ofReal B *
          (badEnergy a + ENNReal.ofReal R * goodEnergy a)) 2 P ≤
          ENNReal.ofReal B * eLpNorm
            (fun a ↦ badEnergy a + ENNReal.ofReal R * goodEnergy a) 2 P :=
        eLpNorm_ofReal_mul_le henergies B 2
      _ ≤ ENNReal.ofReal B *
          (eLpNorm badEnergy 2 P +
            eLpNorm (fun a ↦ ENNReal.ofReal R * goodEnergy a) 2 P) :=
        mul_le_mul_right (eLpNorm_add_le (f := badEnergy)
          (g := fun a ↦ ENNReal.ofReal R * goodEnergy a) (by norm_num)) _
      _ ≤ ENNReal.ofReal B *
          (profileBadEnergyAt P lev M En +
            profileGoodEnergyAt P lev alpha H M En) :=
        mul_le_mul_right (add_le_add (by rfl) hgoodNorm) _
  exact hmono.trans (htriangle.trans (add_le_add hrecentNorm henergyNorm))

end

end HCPolySupport.HighContrast.Response
