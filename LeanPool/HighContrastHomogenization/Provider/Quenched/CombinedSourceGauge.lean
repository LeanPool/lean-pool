/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Frozen.CoarseEllipticityDagger

/-!
# High-contrast homogenization: Provider.Quenched.CombinedSourceGauge

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Combining two source scales and their gauges

The maximum of two source scales has a union-bound tail.  The factor two is
absorbed into a gauge by flooring half of the pointwise minimum at one.  Two
applications of the original growth inequalities give a growth witness for
the combined gauge.
-/

namespace HCPolySupport
namespace HighContrast
namespace Quenched

open MeasureTheory IndependentSums

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The gauge used for the maximum of two source scales. -/
@[expose]
def combinedSourceGauge (Psi₁ Psi₂ : Real -> Real) : Real -> Real :=
  fun t => max 1 (min (Psi₁ t) (Psi₂ t) / 2)

/-- The source scale obtained by retaining both source constraints. -/
@[expose]
def combinedSource (S₁ S₂ : Omega -> Real) : Omega -> Real :=
  fun omega => max (S₁ omega) (S₂ omega)

/-- The gauge paired with flooring a source scale at one. -/
@[expose]
def flooredSourceGauge (Psi : Real -> Real) : Real -> Real :=
  fun t => if t < 1 then 1 else Psi t

/-- A source scale floored at one. -/
@[expose]
def flooredSource (S : Omega -> Real) : Omega -> Real := fun omega => max 1 (S omega)

theorem admissiblePsi_flooredSourceGauge {Psi : Real -> Real}
    (hPsi : AdmissiblePsi Psi) : AdmissiblePsi (flooredSourceGauge Psi) := by
  constructor
  · intro s hs t ht hst
    simp only [Set.mem_Ici] at hs ht
    by_cases hs1 : s < 1
    · by_cases ht1 : t < 1
      · simp only [flooredSourceGauge, ite_eq_left hs1, ite_eq_left ht1]
        exact le_rfl
      · simp only [flooredSourceGauge, ite_eq_left hs1, ite_eq_right ht1]
        exact hPsi.2 ht
    · have ht1 : ¬ t < 1 := fun h => hs1 (lt_of_le_of_lt hst h)
      simp only [flooredSourceGauge, ite_eq_right hs1, ite_eq_right ht1]
      exact hPsi.1 hs ht hst
  · intro t ht
    by_cases ht1 : t < 1
    · simp only [flooredSourceGauge, ite_eq_left ht1]
      exact le_rfl
    · simp only [flooredSourceGauge, ite_eq_right ht1]
      exact hPsi.2 ht

theorem hasPsiGrowth_flooredSourceGauge {Psi : Real -> Real} {K : Real}
    (hK : 1 < K) (hPsi : HasPsiGrowth Psi K) :
    HasPsiGrowth (flooredSourceGauge Psi) K := by
  intro t ht
  have ht1 : ¬ t < 1 := not_lt_of_ge ht
  have hKt : ¬ K * t < 1 := by
    have hKt' : 1 < K * t := by
      calc
        (1 : Real) < K := hK
        _ = K * 1 := by ring
        _ <= K * t := mul_le_mul_of_nonneg_left ht (le_of_lt (zero_lt_one.trans hK))
    exact not_lt_of_ge hKt'.le
  simpa only [flooredSourceGauge, ite_eq_right ht1, ite_eq_right hKt] using hPsi ht

theorem measurable_flooredSource {S : Omega -> Real} (hS : Measurable S) :
    Measurable (flooredSource S) := measurable_const.max hS

omit [MeasurableSpace Omega] in theorem one_le_flooredSource (S : Omega -> Real) :
    forall omega, 1 <= flooredSource S omega := fun _ => le_max_left _ _

theorem sourceTail_flooredSource {P : Measure Omega} [IsProbabilityMeasure P]
    {Psi : Real -> Real} {S : Omega -> Real}
    (htail : forall t : Real, 1 <= t ->
      P.real (upperTailEvent S t) <= (Psi t)⁻¹) :
    forall t : Real, 0 < t ->
      P.real (upperTailEvent (flooredSource S) t) <=
        (flooredSourceGauge Psi t)⁻¹ := by
  intro t ht
  by_cases ht1 : t < 1
  · rw [flooredSourceGauge, ite_eq_left ht1, inv_one]
    exact measureReal_le_one
  · have h1t : 1 <= t := le_of_not_gt ht1
    have hevent : upperTailEvent (flooredSource S) t = upperTailEvent S t := by
      ext omega
      simp only [upperTailEvent, Set.mem_ofPred_eq, flooredSource]
      exact lt_max_iff.trans <| or_iff_right (not_lt_of_ge h1t)
    rw [flooredSourceGauge, ite_eq_right ht1, hevent]
    exact htail t h1t

theorem admissiblePsi_combinedSourceGauge {Psi₁ Psi₂ : Real -> Real}
    (hPsi₁ : AdmissiblePsi Psi₁) (hPsi₂ : AdmissiblePsi Psi₂) :
    AdmissiblePsi (combinedSourceGauge Psi₁ Psi₂) := by
  constructor
  · intro s hs t ht hst
    exact max_le_max le_rfl <| div_le_div_of_nonneg_right
      (min_le_min (hPsi₁.1 hs ht hst) (hPsi₂.1 hs ht hst)) (by norm_num)
  · intro t ht
    exact le_max_left _ _

theorem one_le_combinedGrowthWitness (K₁ K₂ : Real) :
    1 <= (max 2 (max K₁ K₂)) ^ (2 : Nat) := by
  have hK : (1 : Real) <= max 2 (max K₁ K₂) :=
    le_trans (by norm_num) (le_max_left _ _)
  exact one_le_pow₀ hK

private theorem hasPsiGrowth_mono_witness {Psi : Real -> Real} {K K' : Real}
    (hPsi : AdmissiblePsi Psi) (hgrowth : HasPsiGrowth Psi K)
    (hK : 0 <= K) (hKK' : K <= K') : HasPsiGrowth Psi K' := by
  intro t ht
  have ht0 : 0 <= t := zero_le_one.trans ht
  exact (hgrowth ht).trans <| hPsi.1
    (mul_nonneg hK ht0)
    (mul_nonneg (hK.trans hKK') ht0)
    (mul_le_mul_of_nonneg_right hKK' ht0)

private theorem two_step_growth {Psi : Real -> Real} {K t : Real}
    (hK : 2 <= K) (hgrowth : HasPsiGrowth Psi K)
    (ht : 1 <= t) :
    K * t ^ 2 * Psi t <= Psi (K ^ (2 : Nat) * t) := by
  have hKt : 1 <= K * t := by
    nlinarith only [hK, ht]
  have h1 := hgrowth ht
  have h2 := hgrowth hKt
  have ht0 : 0 <= t := zero_le_one.trans ht
  have hK0 : 0 <= K := (by norm_num : (0 : Real) <= 2).trans hK
  have hmul := mul_le_mul_of_nonneg_left h1 (mul_nonneg hK0 ht0)
  calc
    K * t ^ 2 * Psi t = (K * t) * (t * Psi t) := by ring
    _ <= (K * t) * Psi (K * t) := hmul
    _ <= Psi (K * (K * t)) := h2
    _ = Psi (K ^ (2 : Nat) * t) := by ring_nf

theorem hasPsiGrowth_combinedSourceGauge {Psi₁ Psi₂ : Real -> Real}
    {K₁ K₂ : Real} (hPsi₁ : AdmissiblePsi Psi₁) (hPsi₂ : AdmissiblePsi Psi₂)
    (hK₁ : 1 < K₁) (hK₂ : 1 < K₂)
    (hgrowth₁ : HasPsiGrowth Psi₁ K₁) (hgrowth₂ : HasPsiGrowth Psi₂ K₂) :
    HasPsiGrowth (combinedSourceGauge Psi₁ Psi₂)
      ((max 2 (max K₁ K₂)) ^ (2 : Nat)) := by
  intro t ht
  let K : Real := max 2 (max K₁ K₂)
  have hK2 : 2 <= K := le_max_left _ _
  have hK₁K : K₁ <= K := (le_max_left K₁ K₂).trans (le_max_right 2 _)
  have hK₂K : K₂ <= K := (le_max_right K₁ K₂).trans (le_max_right 2 _)
  have hg₁ : HasPsiGrowth Psi₁ K :=
    hasPsiGrowth_mono_witness hPsi₁ hgrowth₁ (le_of_lt (zero_lt_one.trans hK₁)) hK₁K
  have hg₂ : HasPsiGrowth Psi₂ K :=
    hasPsiGrowth_mono_witness hPsi₂ hgrowth₂ (le_of_lt (zero_lt_one.trans hK₂)) hK₂K
  have htwo₁ := two_step_growth hK2 hg₁ ht
  have htwo₂ := two_step_growth hK2 hg₂ ht
  have hmin : K * t ^ 2 * min (Psi₁ t) (Psi₂ t) <=
      min (Psi₁ (K ^ (2 : Nat) * t)) (Psi₂ (K ^ (2 : Nat) * t)) := by
    rcases le_total (Psi₁ t) (Psi₂ t) with h12 | h21
    · rw [min_eq_left h12]
      refine le_min htwo₁ ?_
      exact (mul_le_mul_of_nonneg_left h12
        (mul_nonneg ((by norm_num : (0 : Real) <= 2).trans hK2) (sq_nonneg t))).trans htwo₂
    · rw [min_eq_right h21]
      refine le_min ?_ htwo₂
      exact (mul_le_mul_of_nonneg_left h21
        (mul_nonneg ((by norm_num : (0 : Real) <= 2).trans hK2) (sq_nonneg t))).trans htwo₁
  have hminone : (1 : Real) <= min (Psi₁ t) (Psi₂ t) :=
    le_min (hPsi₁.2 (zero_le_one.trans ht)) (hPsi₂.2 (zero_le_one.trans ht))
  change t * max 1 (min (Psi₁ t) (Psi₂ t) / 2) <=
    max 1 (min (Psi₁ (K ^ (2 : Nat) * t))
      (Psi₂ (K ^ (2 : Nat) * t)) / 2)
  rcases le_total (min (Psi₁ t) (Psi₂ t)) 2 with hsmall | hlarge
  · rw [max_eq_left (by linarith only [hsmall])]
    apply le_max_of_le_right
    have hKt : 2 * t <= K * t ^ 2 * min (Psi₁ t) (Psi₂ t) := by
      have ht0 : 0 <= t := zero_le_one.trans ht
      have hKt' : 2 <= K * t * min (Psi₁ t) (Psi₂ t) := by
        calc
          (2 : Real) <= K := hK2
          _ <= K * t := by
            simpa only [mul_one] using mul_le_mul_of_nonneg_left ht
              ((by norm_num : (0 : Real) <= 2).trans hK2)
          _ <= K * t * min (Psi₁ t) (Psi₂ t) :=
            le_mul_of_one_le_right (mul_nonneg
              ((by norm_num : (0 : Real) <= 2).trans hK2)
              (zero_le_one.trans ht)) hminone
      have := mul_le_mul_of_nonneg_right hKt' ht0
      nlinarith only [this]
    linarith only [hmin, hKt]
  · rw [max_eq_right (by linarith only [hlarge])]
    apply le_max_of_le_right
    have hcoef : t <= K * t ^ 2 := by
      have ht0 : 0 <= t := zero_le_one.trans ht
      have hKt : 1 <= K * t := by nlinarith only [hK2, ht]
      have := mul_le_mul_of_nonneg_right hKt ht0
      nlinarith only [this]
    have hmin0 : 0 <= min (Psi₁ t) (Psi₂ t) := zero_le_one.trans hminone
    have hscaled := mul_le_mul_of_nonneg_right hcoef hmin0
    linarith only [hscaled, hmin]

theorem measurable_combinedSource {S₁ S₂ : Omega -> Real}
    (hS₁ : Measurable S₁) (hS₂ : Measurable S₂) :
    Measurable (combinedSource S₁ S₂) := hS₁.max hS₂

omit [MeasurableSpace Omega] in theorem combinedSource_nonneg {S₁ S₂ : Omega -> Real}
    (hS₁ : forall omega, 0 <= S₁ omega) :
    forall omega, 0 <= combinedSource S₁ S₂ omega := by
  intro omega
  exact (hS₁ omega).trans (le_max_left _ _)

theorem sourceTail_combinedSource {P : Measure Omega} [IsProbabilityMeasure P]
    {Psi₁ Psi₂ : Real -> Real} {S₁ S₂ : Omega -> Real}
    (hPsi₁ : AdmissiblePsi Psi₁) (hPsi₂ : AdmissiblePsi Psi₂)
    (htail₁ : forall t : Real, 0 < t ->
      P.real (upperTailEvent S₁ t) <= (Psi₁ t)⁻¹)
    (htail₂ : forall t : Real, 0 < t ->
      P.real (upperTailEvent S₂ t) <= (Psi₂ t)⁻¹) :
    forall t : Real, 0 < t ->
      P.real (upperTailEvent (combinedSource S₁ S₂) t) <=
        (combinedSourceGauge Psi₁ Psi₂ t)⁻¹ := by
  intro t ht
  have hsub : upperTailEvent (combinedSource S₁ S₂) t <=
      upperTailEvent S₁ t ∪ upperTailEvent S₂ t := by
    intro omega homega
    simp only [upperTailEvent, Set.mem_ofPred_eq, combinedSource] at homega ⊢
    exact (lt_max_iff.mp homega)
  have hunion : P.real (upperTailEvent (combinedSource S₁ S₂) t) <=
      P.real (upperTailEvent S₁ t) + P.real (upperTailEvent S₂ t) :=
    (measureReal_mono hsub).trans (measureReal_union_le _ _)
  have htails := add_le_add (htail₁ t ht) (htail₂ t ht)
  let y : Real := min (Psi₁ t) (Psi₂ t)
  have ht0 : 0 <= t := ht.le
  have hPsi₁pos : 0 < Psi₁ t := lt_of_lt_of_le zero_lt_one (hPsi₁.2 ht0)
  have hPsi₂pos : 0 < Psi₂ t := lt_of_lt_of_le zero_lt_one (hPsi₂.2 ht0)
  have hypos : 0 < y := lt_of_lt_of_le zero_lt_one
    (le_min (hPsi₁.2 ht0) (hPsi₂.2 ht0))
  have hinvsum : (Psi₁ t)⁻¹ + (Psi₂ t)⁻¹ <= 2 * y⁻¹ := by
    have h1 : (Psi₁ t)⁻¹ <= y⁻¹ := (inv_le_inv₀ hPsi₁pos hypos).2 (min_le_left _ _)
    have h2 : (Psi₂ t)⁻¹ <= y⁻¹ := (inv_le_inv₀ hPsi₂pos hypos).2 (min_le_right _ _)
    linarith only [h1, h2]
  rcases le_total y 2 with hsmall | hlarge
  · have hprob := measureReal_le_one (μ := P)
      (s := upperTailEvent (combinedSource S₁ S₂) t)
    have hsmall' : min (Psi₁ t) (Psi₂ t) / 2 <= 1 := by
      change y / 2 <= 1
      linarith only [hsmall]
    rw [combinedSourceGauge, max_eq_left hsmall', inv_one]
    exact hprob
  · have hmax : max 1 (y / 2) = y / 2 := max_eq_right (by linarith only [hlarge])
    rw [combinedSourceGauge, show min (Psi₁ t) (Psi₂ t) = y by rfl, hmax]
    have heq : (y / 2)⁻¹ = 2 * y⁻¹ := by field_simp [hypos.ne']
    rw [heq]
    exact hunion.trans (htails.trans hinvsum)

end

end Quenched
end HighContrast
end HCPolySupport
