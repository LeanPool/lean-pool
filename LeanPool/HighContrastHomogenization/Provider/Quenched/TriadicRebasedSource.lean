/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger
public import LeanPool.HighContrastHomogenization.Provider.Quenched.TriadicRebasedLaw

/-!
# High-contrast homogenization: Provider.Quenched.TriadicRebasedSource

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Source and gauge under triadic rebasing

The rebased source is measured in units of the enlarged microscopic scale.
Its tail is therefore governed by the original gauge evaluated at the
correspondingly dilated argument.
-/

namespace HCPolySupport
namespace HighContrast

open MeasureTheory
open IndependentSums

noncomputable section

variable {d : ℕ}

/-- The source scale of a rebased coefficient sample, expressed in the new
microscopic units. -/
@[expose]
noncomputable def triadicRebasedSource (n : ℕ)
    (S : CoeffSpace d → ℝ) : CoeffSpace d → ℝ :=
  fun a ↦ S (CoeffSpace.triadicContraction n a) / (3 : ℝ) ^ n

/-- The gauge naturally paired with `triadicRebasedSource`. -/
@[expose]
def triadicRebasedGauge (n : ℕ) (Ψ : ℝ → ℝ) : ℝ → ℝ :=
  fun t ↦ Ψ ((3 : ℝ) ^ n * t)

/-- Evaluating the rebased source on a dilated sample recovers the original
source divided by the scale factor. -/
@[simp] theorem triadicRebasedSource_triadicDilation (n : ℕ)
    (S : CoeffSpace d → ℝ) (a : CoeffSpace d) :
    triadicRebasedSource n S (CoeffSpace.triadicDilation n a) =
      S a / (3 : ℝ) ^ n := by
  simp [triadicRebasedSource]

/-- Measurability of the source is preserved by rebasing. -/
theorem measurable_triadicRebasedSource (n : ℕ) {S : CoeffSpace d → ℝ}
    (hS : Measurable S) : Measurable (triadicRebasedSource n S) := by
  exact (hS.comp (CoeffSpace.measurable_triadicContraction n)).div_const _

/-- Nonnegativity of the source is preserved by rebasing. -/
theorem triadicRebasedSource_nonneg (n : ℕ) {S : CoeffSpace d → ℝ}
    (hS : ∀ a, 0 ≤ S a) : ∀ a, 0 ≤ triadicRebasedSource n S a := by
  intro a
  exact div_nonneg (hS _) (by positivity)

/-- Admissibility of the gauge is preserved by positive dilation of its
argument. -/
theorem admissiblePsi_triadicRebasedGauge (n : ℕ) {Ψ : ℝ → ℝ}
    (hΨ : AdmissiblePsi Ψ) : AdmissiblePsi (triadicRebasedGauge n Ψ) := by
  have hr0 : 0 ≤ (3 : ℝ) ^ n := by positivity
  constructor
  · intro s hs t ht hst
    exact hΨ.1 (mul_nonneg hr0 hs) (mul_nonneg hr0 ht)
      (mul_le_mul_of_nonneg_left hst hr0)
  · intro t ht
    exact hΨ.2 (mul_nonneg hr0 ht)

/-- The same growth witness works for the rebased gauge. -/
theorem hasPsiGrowth_triadicRebasedGauge (n : ℕ) {Ψ : ℝ → ℝ} {K : ℝ}
    (hΨ : AdmissiblePsi Ψ) (hgrowth : HasPsiGrowth Ψ K) :
    HasPsiGrowth (triadicRebasedGauge n Ψ) K := by
  intro t ht
  let r : ℝ := (3 : ℝ) ^ n
  have hr : 1 ≤ r := one_le_pow₀ (by norm_num)
  have ht0 : 0 ≤ t := le_trans zero_le_one ht
  have hrt : 1 ≤ r * t := by
    calc
      1 = (1 : ℝ) * 1 := by ring
      _ ≤ r * t := mul_le_mul hr ht zero_le_one (le_trans zero_le_one hr)
  have hΨnonneg : 0 ≤ Ψ (r * t) :=
    le_trans zero_le_one (hΨ.2 (mul_nonneg (by positivity) ht0))
  calc
    t * triadicRebasedGauge n Ψ t ≤
        (r * t) * Ψ (r * t) := by
      exact mul_le_mul_of_nonneg_right
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hr ht0)
        hΨnonneg
    _ ≤ Ψ (K * (r * t)) := hgrowth hrt
    _ = triadicRebasedGauge n Ψ (K * t) := by
      simp only [triadicRebasedGauge, r]
      congr 1
      ring

/-- The source tail transports exactly through the mapped coefficient law. -/
theorem sourceTail_triadicRebasedLaw (n : ℕ) {P : Measure (CoeffSpace d)}
    {Ψ : ℝ → ℝ} {S : CoeffSpace d → ℝ}
    (hSmeas : Measurable S)
    (htail : ∀ t : ℝ, 0 < t → P.real (upperTailEvent S t) ≤ (Ψ t)⁻¹) :
    ∀ t : ℝ, 0 < t →
      (triadicRebasedLaw n P).real
          (upperTailEvent (triadicRebasedSource n S) t) ≤
        (triadicRebasedGauge n Ψ t)⁻¹ := by
  intro t ht
  let r : ℝ := (3 : ℝ) ^ n
  have hr : 0 < r := by positivity
  have hrebasedMeas : Measurable (triadicRebasedSource n S) :=
    measurable_triadicRebasedSource n hSmeas
  have heventMeas :
      MeasurableSet (upperTailEvent (triadicRebasedSource n S) t) := by
    exact hrebasedMeas measurableSet_Ioi
  have hevent :
      CoeffSpace.triadicDilation n ⁻¹'
          upperTailEvent (triadicRebasedSource n S) t =
        upperTailEvent S (r * t) := by
    ext a
    simp only [Set.mem_preimage, mem_upperTailEvent,
      triadicRebasedSource_triadicDilation]
    exact (lt_div_iff₀ hr).trans (by rw [mul_comm])
  rw [triadicRebasedLaw,
    map_measureReal_apply (CoeffSpace.measurable_triadicDilation n) heventMeas,
    hevent]
  exact htail (r * t) (mul_pos hr ht)

end

end HighContrast
end HCPolySupport
