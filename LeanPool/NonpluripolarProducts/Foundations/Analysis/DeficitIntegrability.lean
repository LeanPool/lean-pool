/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.Data.EReal.Operations

/-!
# Integrability from a finite nonnegative deficit

For an extended-real function below a finite constant, integrability of the
nonnegative deficit proves both almost-everywhere finiteness and integrability
of the real representative. The exclusion of negative infinity is proved
before using `toReal`; no information is lost by silently replacing a pole by
zero. Measurability is required only for the deficit.
-/

@[expose] public section

open Set Filter MeasureTheory
open scoped ENNReal

namespace SGPT.Foundations.Analysis

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable {u : X → EReal} {C : ℝ}

/-- A finite deficit integral excludes negative infinity almost everywhere,
even without an upper-bound assumption. -/
theorem ae_ne_bot_of_lintegral_deficit_lt_top
    (hd : AEMeasurable (fun x => ((C : EReal) - u x).toENNReal) μ)
    (hI : ∫⁻ x, ((C : EReal) - u x).toENNReal ∂μ < ⊤) :
    ∀ᵐ x ∂μ, u x ≠ ⊥ := by
  filter_upwards [ae_lt_top' hd hI.ne] with x hx
  intro hbot
  simp only [hbot, EReal.coe_sub_bot, EReal.toENNReal_top, lt_self_iff_false] at hx

/-- Under a finite upper bound, the actual extended-real function agrees
almost everywhere with its real representative. -/
theorem ae_coe_toReal_eq_of_lintegral_deficit_lt_top
    (hC : ∀ᵐ x ∂μ, u x ≤ (C : EReal))
    (hd : AEMeasurable (fun x => ((C : EReal) - u x).toENNReal) μ)
    (hI : ∫⁻ x, ((C : EReal) - u x).toENNReal ∂μ < ⊤) :
    (fun x => ((u x).toReal : EReal)) =ᶠ[ae μ] u := by
  filter_upwards [hC, ae_ne_bot_of_lintegral_deficit_lt_top hd hI] with x hx hbot
  exact EReal.coe_toReal (hx.trans_lt (EReal.coe_lt_top C)).ne hbot

/-- The real representative is a constant minus the real nonnegative deficit
almost everywhere. This equality is established only after finiteness. -/
theorem ae_toReal_eq_const_sub_deficit_of_lintegral_lt_top
    (hC : ∀ᵐ x ∂μ, u x ≤ (C : EReal))
    (hd : AEMeasurable (fun x => ((C : EReal) - u x).toENNReal) μ)
    (hI : ∫⁻ x, ((C : EReal) - u x).toENNReal ∂μ < ⊤) :
    (fun x => (u x).toReal) =ᶠ[ae μ]
      (fun x => C - ((C : EReal) - u x).toENNReal.toReal) := by
  filter_upwards [hC, ae_ne_bot_of_lintegral_deficit_lt_top hd hI] with x hx hbot
  have htop : u x ≠ ⊤ := (hx.trans_lt (EReal.coe_lt_top C)).ne
  have hnonneg : 0 ≤ (C : EReal) - u x :=
    (EReal.sub_nonneg (Or.inl (EReal.coe_ne_top C))
      (Or.inl (EReal.coe_ne_bot C))).mpr hx
  rw [EReal.toReal_toENNReal hnonneg,
    EReal.toReal_sub (EReal.coe_ne_top C) (EReal.coe_ne_bot C) htop hbot,
    EReal.toReal_coe]
  exact (sub_sub_cancel C (u x).toReal).symm

/-- A finite nonnegative deficit gives an integrable real representative on
a finite measure space. -/
theorem integrable_toReal_of_lintegral_deficit_lt_top [IsFiniteMeasure μ]
    (hC : ∀ᵐ x ∂μ, u x ≤ (C : EReal))
    (hd : AEMeasurable (fun x => ((C : EReal) - u x).toENNReal) μ)
    (hI : ∫⁻ x, ((C : EReal) - u x).toENNReal ∂μ < ⊤) :
    Integrable (fun x => (u x).toReal) μ := by
  have hdef := integrable_toReal_of_lintegral_ne_top hd hI.ne
  exact ((integrable_const C).sub hdef).congr
    (ae_toReal_eq_const_sub_deficit_of_lintegral_lt_top hC hd hI).symm

/-- The complete finite-measure bridge retains both almost-everywhere
finiteness and equality with the real representative. -/
theorem ae_finite_and_integrable_of_lintegral_deficit_lt_top [IsFiniteMeasure μ]
    (hC : ∀ᵐ x ∂μ, u x ≤ (C : EReal))
    (hd : AEMeasurable (fun x => ((C : EReal) - u x).toENNReal) μ)
    (hI : ∫⁻ x, ((C : EReal) - u x).toENNReal ∂μ < ⊤) :
    (∀ᵐ x ∂μ, u x ≠ ⊤ ∧ u x ≠ ⊥) ∧
      Integrable (fun x => (u x).toReal) μ ∧
      ((fun x => ((u x).toReal : EReal)) =ᶠ[ae μ] u) := by
  refine ⟨?_, integrable_toReal_of_lintegral_deficit_lt_top hC hd hI,
    ae_coe_toReal_eq_of_lintegral_deficit_lt_top hC hd hI⟩
  filter_upwards [hC, ae_ne_bot_of_lintegral_deficit_lt_top hd hI] with x hx hbot
  exact ⟨(hx.trans_lt (EReal.coe_lt_top C)).ne, hbot⟩

/-- Restricted-set version; the set need not be measurable, and no separate
measurability hypothesis on the extended-real function is needed. -/
theorem ae_finite_and_integrableOn_of_lintegral_deficit_lt_top {s : Set X}
    (hμs : μ s < ⊤)
    (hC : ∀ᵐ x ∂μ.restrict s, u x ≤ (C : EReal))
    (hd : AEMeasurable (fun x => ((C : EReal) - u x).toENNReal) (μ.restrict s))
    (hI : ∫⁻ x in s, ((C : EReal) - u x).toENNReal ∂μ < ⊤) :
    (∀ᵐ x ∂μ.restrict s, u x ≠ ⊤ ∧ u x ≠ ⊥) ∧
      IntegrableOn (fun x => (u x).toReal) s μ ∧
      ((fun x => ((u x).toReal : EReal)) =ᶠ[ae (μ.restrict s)] u) := by
  let : IsFiniteMeasure (μ.restrict s) := ⟨by simpa using hμs⟩
  exact ae_finite_and_integrable_of_lintegral_deficit_lt_top hC hd hI

end SGPT.Foundations.Analysis
