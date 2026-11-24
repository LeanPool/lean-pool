/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.DeficitIntegrability
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Compact localization of an extended-real deficit

The real deficit is nonnegative even at a negative-infinite pole, provided the
chosen upper bound is nonnegative. Its equality with the extended nonnegative
deficit is asserted only almost everywhere, after finiteness of the potential
has been established. Compact localization of a locally integrable real
representative gives a genuine globally integrable density.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis

variable {X : Type*} {u : X → EReal} {K : Set X} {C : ℝ}

/-- A nonnegative upper bound gives a nonnegative real deficit, including at
poles where the totalized real representative is zero. A separate exclusion
of positive infinity is unnecessary, since the finite upper bound excludes it. -/
theorem indicator_realDeficit_nonneg (hC : 0 ≤ C)
    (huC : ∀ x ∈ K, u x ≤ (C : EReal)) (x : X) :
    0 ≤ K.indicator (fun y => C - (u y).toReal) x := by
  classical
  by_cases hx : x ∈ K
  · rw [Set.indicator_of_mem hx]
    by_cases hbot : u x = ⊥
    · simpa only [hbot, EReal.toReal_bot, sub_zero] using hC
    · exact sub_nonneg.mpr (by
        simpa only [EReal.toReal_coe] using
          EReal.toReal_le_toReal (huC x hx) hbot (EReal.coe_ne_top C))
  · simp only [Set.indicator_of_notMem hx, le_refl]

variable [MeasurableSpace X] {μ : Measure X}

/-- On a measurable set of finite measure, an integrable real representative
has a genuinely integrable zero-extended deficit. -/
theorem integrable_indicator_realDeficit (hK : MeasurableSet K) (hμK : μ K ≠ ⊤)
    (hu : IntegrableOn (fun x => (u x).toReal) K μ) (C : ℝ) :
    Integrable (K.indicator (fun x => C - (u x).toReal)) μ :=
  ((integrableOn_const (C := C) hμK).sub hu).integrable_indicator hK

/-- Almost-everywhere finiteness is retained explicitly when identifying the
extended deficit with the nonnegative real deficit. The statement remains
valid without an upper bound because `ofReal` truncates negative values. -/
theorem indicator_deficit_ae_eq_ofReal (hK : MeasurableSet K)
    (hfin : ∀ᵐ x ∂μ.restrict K, u x ≠ ⊤ ∧ u x ≠ ⊥) (C : ℝ) :
    K.indicator (fun x => ((C : EReal) - u x).toENNReal) =ᵐ[μ]
      fun x => ENNReal.ofReal (K.indicator (fun y => C - (u y).toReal) x) := by
  classical
  filter_upwards [(ae_restrict_iff' hK).mp hfin] with x hx
  by_cases hxK : x ∈ K
  · simp only [Set.indicator_of_mem hxK]
    rw [← EReal.coe_toReal (hx hxK).1 (hx hxK).2, ← EReal.coe_sub,
      EReal.real_coe_toENNReal, EReal.toReal_coe]
  · simp only [Set.indicator_of_notMem hxK, ENNReal.ofReal_zero]

section Compact

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
variable {μ : Measure E} [IsFiniteMeasureOnCompacts μ]
variable {u : E → EReal} {K U : Set E}

/-- The compact-set specialization derives integrability from local
integrability on the ambient domain, rather than assuming it on the compact
set. The ambient domain need not be open. -/
theorem integrable_indicator_realDeficit_of_isCompact (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : LocallyIntegrableOn (fun x => (u x).toReal) U μ) (C : ℝ) :
    Integrable (K.indicator (fun x => C - (u x).toReal)) μ :=
  integrable_indicator_realDeficit hK.measurableSet hK.measure_ne_top
    ((hu.mono_set hKU).integrableOn_isCompact hK) C

/-- The compactly localized deficit is a valid locally integrable density
for scalar convolution pairings on the entire ambient space. -/
theorem locallyIntegrable_indicator_realDeficit_of_isCompact
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hu : LocallyIntegrableOn (fun x => (u x).toReal) U μ) (C : ℝ) :
    LocallyIntegrable (K.indicator (fun x => C - (u x).toReal)) μ :=
  (integrable_indicator_realDeficit_of_isCompact hK hKU hu C).locallyIntegrable

omit [IsFiniteMeasureOnCompacts μ] in
/-- Almost-everywhere finiteness on the ambient domain suffices for equality
of the two localized deficits on the whole space. -/
theorem indicator_deficit_ae_eq_ofReal_of_isCompact
    (hK : IsCompact K) (hKU : K ⊆ U)
    (hfin : ∀ᵐ x ∂μ.restrict U, u x ≠ ⊤ ∧ u x ≠ ⊥) (C : ℝ) :
    K.indicator (fun x => ((C : EReal) - u x).toENNReal) =ᵐ[μ]
      fun x => ENNReal.ofReal (K.indicator (fun y => C - (u y).toReal) x) :=
  indicator_deficit_ae_eq_ofReal hK.measurableSet
    (ae_restrict_of_ae_restrict_of_subset hKU hfin) C

end Compact

end SGPT.Foundations.Analysis
