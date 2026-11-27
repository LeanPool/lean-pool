/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The inclusion `L_r ↪ L_p` for a finite measure

For a finite measure `μ` and `p ≤ r`, every element of `L_r(μ)` is also an element of
`L_p(μ)`, with

`‖f‖_p ≤ μ(Ω)^(1/p - 1/r) ‖f‖_r`

(Hölder's inequality, `MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ`).  Mathlib has
this as an inclusion of additive subgroups of the space of a.e. classes (`Lp.antitone`), but
not as a map between the normed spaces `Lp E r μ` and `Lp E p μ`, which are different types.
This file provides that map, `MeasureTheory.Lp.inclusionOfExponentLe`, as a bounded linear
map; it is injective, and for a probability measure it has norm at most `1`.

Every embedding theorem between different `L_p` spaces is stated through this map: "`f ∈ L_p`
lies in `L_r`" becomes "`f = inclusionOfExponentLe μ hpr g` for some `g ∈ L_r`".
-/

@[expose] public section

open scoped ENNReal

namespace MeasureTheory.Lp

variable {α E 𝕜 : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] {p r : ℝ≥0∞}

section Linear

variable [IsFiniteMeasure μ]

/-- The inclusion `L_r → L_p` for `p ≤ r` and a finite measure, as a linear map. -/
noncomputable def inclusionOfExponentLeLinear (μ : Measure α) [IsFiniteMeasure μ] (hpr : p ≤ r) :
    Lp E r μ →ₗ[𝕜] Lp E p μ where
  toFun f := ((Lp.memLp f).mono_exponent hpr).toLp f
  map_add' f g := by
    ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_add, Lp.coeFn_add, MemLp.coeFn_toLp, MemLp.coeFn_toLp]
  map_smul' c f := by
    ext
    grw [MemLp.coeFn_toLp, Lp.coeFn_smul, Lp.coeFn_smul, MemLp.coeFn_toLp]
    rfl

/-- The inclusion does not change the function, up to null sets. -/
theorem coeFn_inclusionOfExponentLeLinear (hpr : p ≤ r) (f : Lp E r μ) :
    inclusionOfExponentLeLinear (𝕜 := 𝕜) μ hpr f =ᵐ[μ] f :=
  MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hpr)

end Linear

/-- The constant `μ(Ω)^(1/p - 1/r)` of Hölder's inequality between `L_r` and `L_p`. -/
noncomputable def inclusionConst (μ : Measure α) (p r : ℝ≥0∞) : ℝ :=
  (μ Set.univ ^ (1 / p.toReal - 1 / r.toReal)).toReal

/-- The constant `μ(Ω)^(1/p - 1/r)` is nonnegative. -/
theorem inclusionConst_nonneg (μ : Measure α) (p r : ℝ≥0∞) : 0 ≤ inclusionConst μ p r :=
  ENNReal.toReal_nonneg

/-- For a probability measure the constant is `1`. -/
@[simp]
theorem inclusionConst_of_isProbabilityMeasure [IsProbabilityMeasure μ] (p r : ℝ≥0∞) :
    inclusionConst μ p r = 1 := by
  simp [inclusionConst]

variable [Fact (1 ≤ p)] [Fact (1 ≤ r)] [IsFiniteMeasure μ]

/-- Hölder's inequality: `‖f‖_p ≤ μ(Ω)^(1/p - 1/r) ‖f‖_r`. -/
theorem norm_inclusionOfExponentLeLinear_apply_le (hpr : p ≤ r) (f : Lp E r μ) :
    ‖inclusionOfExponentLeLinear (𝕜 := 𝕜) μ hpr f‖ ≤ inclusionConst μ p r * ‖f‖ := by
  have hp : 1 ≤ p := Fact.out
  have hexp : 0 ≤ 1 / p.toReal - 1 / r.toReal := by
    rcases eq_or_ne r ∞ with rfl | hr
    · simp
    have hp' : p ≠ ∞ := ne_top_of_le_ne_top hr hpr
    have hp0 : 0 < p.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le hp).ne' hp'
    rw [sub_nonneg]
    exact one_div_le_one_div_of_le hp0 (ENNReal.toReal_mono hr hpr)
  have hM : μ Set.univ ^ (1 / p.toReal - 1 / r.toReal) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg hexp (measure_ne_top μ _)
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (coeFn_inclusionOfExponentLeLinear hpr f),
    inclusionConst, ← ENNReal.toReal_mul, mul_comm]
  exact ENNReal.toReal_mono (ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hM)
    (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpr (Lp.aestronglyMeasurable f))

/-- The **inclusion `L_r ↪ L_p`** for `p ≤ r` and a finite measure `μ`, as a bounded linear
map with `‖f‖_p ≤ μ(Ω)^(1/p - 1/r) ‖f‖_r`. -/
noncomputable def inclusionOfExponentLe (μ : Measure α) [IsFiniteMeasure μ] (hpr : p ≤ r) :
    Lp E r μ →L[𝕜] Lp E p μ :=
  LinearMap.mkContinuous (inclusionOfExponentLeLinear μ hpr) (inclusionConst μ p r)
    (norm_inclusionOfExponentLeLinear_apply_le hpr)

/-- The inclusion does not change the function: `inclusionOfExponentLe μ hpr f = f` a.e. -/
theorem coeFn_inclusionOfExponentLe (hpr : p ≤ r) (f : Lp E r μ) :
    inclusionOfExponentLe (𝕜 := 𝕜) μ hpr f =ᵐ[μ] f :=
  coeFn_inclusionOfExponentLeLinear hpr f

/-- Hölder's inequality: `‖f‖_p ≤ μ(Ω)^(1/p - 1/r) ‖f‖_r`. -/
theorem norm_inclusionOfExponentLe_apply_le (hpr : p ≤ r) (f : Lp E r μ) :
    ‖inclusionOfExponentLe (𝕜 := 𝕜) μ hpr f‖ ≤ inclusionConst μ p r * ‖f‖ :=
  norm_inclusionOfExponentLeLinear_apply_le hpr f

/-- The inclusion has norm at most `μ(Ω)^(1/p - 1/r)`. -/
theorem norm_inclusionOfExponentLe_le (hpr : p ≤ r) :
    ‖(inclusionOfExponentLe (E := E) (𝕜 := 𝕜) μ hpr)‖ ≤ inclusionConst μ p r :=
  LinearMap.mkContinuous_norm_le _ (inclusionConst_nonneg μ p r) _

/-- For a probability measure the inclusion is a contraction. -/
theorem norm_inclusionOfExponentLe_apply_le_of_prob [IsProbabilityMeasure μ] (hpr : p ≤ r)
    (f : Lp E r μ) : ‖inclusionOfExponentLe (𝕜 := 𝕜) μ hpr f‖ ≤ ‖f‖ := by
  simpa using norm_inclusionOfExponentLe_apply_le (𝕜 := 𝕜) hpr f

/-- The inclusion is injective: an `L_r` class is determined by its `L_p` class. -/
theorem inclusionOfExponentLe_injective (hpr : p ≤ r) :
    Function.Injective (inclusionOfExponentLe (E := E) (𝕜 := 𝕜) μ hpr) := fun f g h => by
  ext
  have := congrArg (fun F : Lp E p μ => (F : α → E)) h
  filter_upwards [coeFn_inclusionOfExponentLe (𝕜 := 𝕜) hpr f,
    coeFn_inclusionOfExponentLe (𝕜 := 𝕜) hpr g] with x hf hg
  rw [← hf, ← hg]
  exact congrFun this x

/-- The identity case `p = r`. -/
@[simp]
theorem inclusionOfExponentLe_self (f : Lp E p μ) :
    inclusionOfExponentLe (𝕜 := 𝕜) μ le_rfl f = f := by
  ext1; exact coeFn_inclusionOfExponentLe le_rfl f

/-- Two inclusions compose to an inclusion. -/
theorem inclusionOfExponentLe_comp {s : ℝ≥0∞} [Fact (1 ≤ s)] (hps : p ≤ s) (hsr : s ≤ r)
    (f : Lp E r μ) :
    inclusionOfExponentLe (𝕜 := 𝕜) μ hps (inclusionOfExponentLe (𝕜 := 𝕜) μ hsr f) =
      inclusionOfExponentLe (𝕜 := 𝕜) μ (hps.trans hsr) f := by
  ext1
  filter_upwards [coeFn_inclusionOfExponentLe (𝕜 := 𝕜) hps (inclusionOfExponentLe (𝕜 := 𝕜) μ hsr f),
    coeFn_inclusionOfExponentLe (𝕜 := 𝕜) hsr f,
    coeFn_inclusionOfExponentLe (𝕜 := 𝕜) (hps.trans hsr) f] with x h1 h2 h3
  rw [h1, h2, h3]

end MeasureTheory.Lp
