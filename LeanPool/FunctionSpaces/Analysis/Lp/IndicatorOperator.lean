/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Indicators, extension by zero and restriction in `L_p`

For a measurable set `s` of a measure space, multiplication by the indicator `1_s` is a bounded
linear operator on `L_p(μ)` of norm at most `1` (`Rd.indicatorLp`); it is multiplication by
`1_s` almost everywhere (`Rd.indicatorLp_apply_ae`) and `‖1_s g‖_p ≤ ‖g‖_p`
(`Rd.enorm_indicatorLp_le`). Two classes have the same image iff they agree almost everywhere
on `s` (`Rd.indicatorLp_eq_iff_ae_eq_restrict`), and `∫_s a b = ⟨1_s a, b⟩` for `a, b ∈ L_2`
with Mathlib's pairing of `L_2` with `L_2` (`Rd.setIntegral_mul_eq_lpPairing`). For a measurable
`T ⊆ O`, the extension by zero `g ↦ 1_T g` from `L_p(μ|_O)` to `L_p(μ)` is a bounded linear
operator of norm at most `1` (`Rd.indicatorExtendLp`). The cut-off norm `‖1_s f‖_{L_p(μ)}` is the
norm of the restriction `f|_s ∈ L_p(μ|_s)` (`Rd.enorm_indicatorLp_eq`), and the extension by zero
of `f|_s` agrees with `f` on `s` (`Rd.indicatorLp_indicatorExtendLp_restrict`); it is `f` when `f`
vanishes almost everywhere outside `s` (`Rd.indicatorExtendLp_restrict_of_ae_eq_zero`). For a
measurable `D ⊆ O`, the restriction `g ↦ g|_D` from `L_p(μ|_O)` to `L_p(μ|_D)` is a bounded
linear operator (`Rd.restrictSubsetLp`) that agrees with `g` almost everywhere on `D`
(`Rd.restrictSubsetLp_ae`).
-/

@[expose] public section

open MeasureTheory Filter
open scoped ENNReal

namespace Rd

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- `1_s g ∈ L_p` for `g ∈ L_p`. -/
theorem memLp_indicator_coe {s : Set α} (hs : MeasurableSet s) (g : Lp ℂ p μ) :
    MemLp (s.indicator (g : α → ℂ)) p μ :=
  (Lp.memLp g).indicator hs.nullMeasurableSet

omit [Fact (1 ≤ p)] in
/-- `‖1_s g‖_p ≤ ‖g‖_p` for the class of `1_s g`. -/
theorem norm_toLp_indicator_le {s : Set α} (hs : MeasurableSet s) (g : Lp ℂ p μ) :
    ‖(memLp_indicator_coe hs g).toLp _‖ ≤ ‖g‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) (eLpNorm_indicator_le _ hs.nullMeasurableSet)

/-- **Multiplication by the indicator of a measurable set** as an operator on `L_p` of norm at
most `1`. -/
noncomputable def indicatorLp {s : Set α} (hs : MeasurableSet s) : Lp ℂ p μ →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun := fun g => (memLp_indicator_coe hs g).toLp _
      map_add' := fun f g => by
        refine Lp.ext ?_
        have e1 := MemLp.coeFn_toLp (memLp_indicator_coe hs (f + g))
        have e2 := MemLp.coeFn_toLp (memLp_indicator_coe hs f)
        have e3 := MemLp.coeFn_toLp (memLp_indicator_coe hs g)
        have e4 := Lp.coeFn_add f g
        have e5 := Lp.coeFn_add ((memLp_indicator_coe hs f).toLp _)
          ((memLp_indicator_coe hs g).toLp _)
        filter_upwards [e1, e2, e3, e4, e5] with x h1 h2 h3 h4 h5
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ s
        · simp only [Set.indicator_of_mem hx, h4, Pi.add_apply]
        · simp only [Set.indicator_of_notMem hx, add_zero]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        have e1 := MemLp.coeFn_toLp (memLp_indicator_coe hs (c • f))
        have e2 := MemLp.coeFn_toLp (memLp_indicator_coe hs f)
        have e3 := Lp.coeFn_smul c f
        have e4 := Lp.coeFn_smul c ((memLp_indicator_coe hs f).toLp _)
        filter_upwards [e1, e2, e3, e4] with x h1 h2 h3 h4
        rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2]
        by_cases hx : x ∈ s
        · simp only [Set.indicator_of_mem hx, h3, Pi.smul_apply]
        · simp only [Set.indicator_of_notMem hx, smul_zero] }
    1 (fun g => by
      rw [one_mul]
      exact norm_toLp_indicator_le hs g)

/-- Multiplication by an indicator is multiplication by the indicator, almost everywhere. -/
theorem indicatorLp_apply_ae {s : Set α} (hs : MeasurableSet s) (g : Lp ℂ p μ) :
    indicatorLp hs g =ᵐ[μ] s.indicator g :=
  MemLp.coeFn_toLp (memLp_indicator_coe hs g)

/-- **Integrals over a set as a pairing**: `∫_s a b = ⟨1_s a, b⟩` for `a, b ∈ L_2(μ)` and a
measurable set `s`, with Mathlib's bounded bilinear pairing of `L_2` with `L_2`
(`ContinuousLinearMap.lpPairing`). -/
theorem setIntegral_mul_eq_lpPairing {s : Set α} (hs : MeasurableSet s) (a b : Lp ℂ 2 μ) :
    ∫ x in s, a x * b x ∂μ =
      (ContinuousLinearMap.mul ℂ ℂ).lpPairing μ 2 2 (indicatorLp hs a) b := by
  rw [ContinuousLinearMap.lpPairing_eq_integral, ← integral_indicator hs]
  refine integral_congr_ae ?_
  filter_upwards [indicatorLp_apply_ae hs a] with x hx
  rw [ContinuousLinearMap.mul_apply', hx]
  by_cases h : x ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, zero_mul]

/-- `‖1_s g‖_p ≤ ‖g‖_p`. -/
theorem enorm_indicatorLp_le {s : Set α} (hs : MeasurableSet s) (g : Lp ℂ p μ) :
    ‖indicatorLp hs g‖ₑ ≤ ‖g‖ₑ := by
  rw [Lp.eNorm_def, Lp.eNorm_def, eLpNorm_congr_ae (indicatorLp_apply_ae hs g)]
  exact eLpNorm_indicator_le _ hs.nullMeasurableSet

/-- **The `L_p(μ|_s)` norm as a cut-off norm**: `‖1_s f‖_{L_p(μ)} = ‖f|_s‖_{L_p(μ|_s)}` for a
measurable `s` (Mathlib's `MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict` and
`MeasureTheory.LpToLpRestrictCLM_coeFn`). -/
theorem enorm_indicatorLp_eq {s : Set α} (hs : MeasurableSet s) (f : Lp ℂ p μ) :
    ‖indicatorLp hs f‖ₑ = ‖LpToLpRestrictCLM α ℂ ℂ μ p s f‖ₑ := by
  rw [Lp.eNorm_def, Lp.eNorm_def, eLpNorm_congr_ae (indicatorLp_apply_ae hs f),
    eLpNorm_indicator_eq_eLpNorm_restrict hs.nullMeasurableSet,
    eLpNorm_congr_ae (LpToLpRestrictCLM_coeFn ℂ s f)]

/-- Two elements of `L_p` have the same restriction `1_s F = 1_s f` to a measurable set `s` iff
they agree almost everywhere on `s`: Mathlib's `MeasureTheory.ae_eq_restrict_iff_indicator_ae_eq`
for the classes in `L_p`. -/
theorem indicatorLp_eq_iff_ae_eq_restrict {s : Set α} (hs : MeasurableSet s) {F f : Lp ℂ p μ} :
    indicatorLp hs F = indicatorLp hs f ↔ (F : α → ℂ) =ᵐ[μ.restrict s] f := by
  rw [ae_eq_restrict_iff_indicator_ae_eq hs, Lp.ext_iff]
  exact ⟨fun h => (indicatorLp_apply_ae hs F).symm.trans (h.trans (indicatorLp_apply_ae hs f)),
    fun h => (indicatorLp_apply_ae hs F).trans (h.trans (indicatorLp_apply_ae hs f).symm)⟩

/-! ### Extension by zero -/

omit [Fact (1 ≤ p)] in
/-- For `g ∈ L_p(μ|_O)` and a measurable `T ⊆ O`, the extension by zero `1_T g` lies in `L_p(μ)`
(Mathlib's `MeasureTheory.memLp_indicator_iff_restrict`). -/
theorem memLp_indicator_restrict {T O : Set α} (hT : MeasurableSet T) (hTO : T ⊆ O)
    (g : Lp ℂ p (μ.restrict O)) : MemLp (T.indicator (g : α → ℂ)) p μ :=
  (memLp_indicator_iff_restrict hT.nullMeasurableSet).2
    ((Lp.memLp g).mono_measure (Measure.restrict_mono hTO le_rfl))

omit [Fact (1 ≤ p)] in
/-- `‖1_T g‖_{L_p(μ)} ≤ ‖g‖_{L_p(μ|_O)}` for `T ⊆ O` (Mathlib's
`MeasureTheory.eLpNorm_indicator_eq_eLpNorm_restrict`). -/
theorem eLpNorm_indicator_restrict_le {T O : Set α} (hT : MeasurableSet T) (hTO : T ⊆ O)
    (g : Lp ℂ p (μ.restrict O)) :
    eLpNorm (T.indicator (g : α → ℂ)) p μ ≤ eLpNorm g p (μ.restrict O) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hT.nullMeasurableSet]
  exact eLpNorm_mono_measure _ (Measure.restrict_mono hTO le_rfl)

/-- **Extension by zero** from `L_p(μ|_O)` to `L_p(μ)` on a measurable `T ⊆ O`: the operator
`g ↦ 1_T g` of norm at most `1`. -/
noncomputable def indicatorExtendLp {T O : Set α} (hT : MeasurableSet T) (hTO : T ⊆ O) :
    Lp ℂ p (μ.restrict O) →L[ℂ] Lp ℂ p μ :=
  LinearMap.mkContinuous
    { toFun := fun g => (memLp_indicator_restrict hT hTO g).toLp _
      map_add' := fun f g => by
        refine Lp.ext ?_
        have e1 := MemLp.coeFn_toLp (memLp_indicator_restrict hT hTO (f + g))
        have e2 := MemLp.coeFn_toLp (memLp_indicator_restrict hT hTO f)
        have e3 := MemLp.coeFn_toLp (memLp_indicator_restrict hT hTO g)
        have e4 := ae_restrict_of_ae_restrict_of_subset hTO (Lp.coeFn_add f g)
        have e5 := Lp.coeFn_add ((memLp_indicator_restrict hT hTO f).toLp _)
          ((memLp_indicator_restrict hT hTO g).toLp _)
        filter_upwards [e1, e2, e3, e5, (ae_restrict_iff' hT).1 e4] with x h1 h2 h3 h5 h4
        rw [h1, h5, Pi.add_apply, h2, h3]
        by_cases hx : x ∈ T
        · simp only [Set.indicator_of_mem hx, h4 hx, Pi.add_apply]
        · simp only [Set.indicator_of_notMem hx, add_zero]
      map_smul' := fun c f => by
        refine Lp.ext ?_
        have e1 := MemLp.coeFn_toLp (memLp_indicator_restrict hT hTO (c • f))
        have e2 := MemLp.coeFn_toLp (memLp_indicator_restrict hT hTO f)
        have e3 := ae_restrict_of_ae_restrict_of_subset hTO (Lp.coeFn_smul c f)
        have e4 := Lp.coeFn_smul c ((memLp_indicator_restrict hT hTO f).toLp _)
        filter_upwards [e1, e2, e4, (ae_restrict_iff' hT).1 e3] with x h1 h2 h4 h3
        rw [h1, RingHom.id_apply, h4, Pi.smul_apply, h2]
        by_cases hx : x ∈ T
        · simp only [Set.indicator_of_mem hx, h3 hx, Pi.smul_apply]
        · simp only [Set.indicator_of_notMem hx, smul_zero] }
    1 (fun g => by
      change ‖(memLp_indicator_restrict hT hTO g).toLp _‖ ≤ 1 * ‖g‖
      rw [one_mul, Lp.norm_toLp, Lp.norm_def]
      exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top g) (eLpNorm_indicator_restrict_le hT hTO g))

/-- The extension by zero is `1_T g` almost everywhere. -/
theorem indicatorExtendLp_apply_ae {T O : Set α} (hT : MeasurableSet T) (hTO : T ⊆ O)
    (g : Lp ℂ p (μ.restrict O)) : indicatorExtendLp hT hTO g =ᵐ[μ] T.indicator g :=
  MemLp.coeFn_toLp (memLp_indicator_restrict hT hTO g)

/-- `‖1_T g‖_{L_p(μ)} ≤ ‖g‖_{L_p(μ|_O)}` for the extension by zero. -/
theorem enorm_indicatorExtendLp_le {T O : Set α} (hT : MeasurableSet T) (hTO : T ⊆ O)
    (g : Lp ℂ p (μ.restrict O)) : ‖indicatorExtendLp hT hTO g‖ₑ ≤ ‖g‖ₑ := by
  rw [Lp.eNorm_def, Lp.eNorm_def g, eLpNorm_congr_ae (indicatorExtendLp_apply_ae hT hTO g)]
  exact eLpNorm_indicator_restrict_le hT hTO g

/-- **The zero extension of a restriction agrees with the function on the set**: for a
measurable `s` and `f ∈ L_p(μ)`, `1_s E(f|_s) = 1_s f` in `L_p(μ)`, where `E` is the extension by
zero from `L_p(μ|_s)` (`Rd.indicatorLp_eq_iff_ae_eq_restrict`). -/
theorem indicatorLp_indicatorExtendLp_restrict {s : Set α} (hs : MeasurableSet s)
    (f : Lp ℂ p μ) :
    indicatorLp hs (indicatorExtendLp hs subset_rfl (LpToLpRestrictCLM α ℂ ℂ μ p s f)) =
      indicatorLp hs f := by
  refine (indicatorLp_eq_iff_ae_eq_restrict hs).2 ?_
  filter_upwards [ae_restrict_of_ae (indicatorExtendLp_apply_ae hs subset_rfl
    (LpToLpRestrictCLM α ℂ ℂ μ p s f)), LpToLpRestrictCLM_coeFn ℂ s f,
    ae_restrict_mem hs] with x hx1 hx2 hx3
  rw [hx1, Set.indicator_of_mem hx3, hx2]

/-- **The zero extension of a restriction**: if `f ∈ L_p(μ)` vanishes almost everywhere outside a
measurable set `s`, then the zero extension of `f|_s` is `f`. -/
theorem indicatorExtendLp_restrict_of_ae_eq_zero {s : Set α} (hs : MeasurableSet s)
    {f : Lp ℂ p μ} (hf : ∀ᵐ x ∂μ, x ∉ s → f x = 0) :
    indicatorExtendLp hs subset_rfl (LpToLpRestrictCLM α ℂ ℂ μ p s f) = f := by
  refine Lp.ext ?_
  filter_upwards [indicatorExtendLp_apply_ae hs subset_rfl (LpToLpRestrictCLM α ℂ ℂ μ p s f),
    (ae_restrict_iff' hs).1 (LpToLpRestrictCLM_coeFn ℂ s f), hf] with x h1 h2 h3
  rw [h1]
  by_cases hx : x ∈ s
  · rw [Set.indicator_of_mem hx, h2 hx]
  · rw [Set.indicator_of_notMem hx, h3 hx]

/-! ### Restriction to a smaller set -/

/-- **Restriction to a smaller set**: for measurable `D ⊆ O`, the operator
`L_p(μ|_O) → L_p(μ|_D)`, `g ↦ g|_D`, as the zero extension to the whole space
(`Rd.indicatorExtendLp`) followed by the restriction to `D` (Mathlib's
`MeasureTheory.LpToLpRestrictCLM`). Mathlib's `MeasureTheory.Lp.LpToLpOfMeasureLeSMul` gives the
same map as an `ℝ`-linear operator. -/
noncomputable def restrictSubsetLp {D O : Set α} (hD : MeasurableSet D) (hDO : D ⊆ O) :
    Lp ℂ p (μ.restrict O) →L[ℂ] Lp ℂ p (μ.restrict D) :=
  LpToLpRestrictCLM α ℂ ℂ μ p D ∘L indicatorExtendLp hD hDO

/-- The restriction to `D` agrees with `g` almost everywhere on `D`. -/
theorem restrictSubsetLp_ae {D O : Set α} (hD : MeasurableSet D) (hDO : D ⊆ O)
    (g : Lp ℂ p (μ.restrict O)) : restrictSubsetLp hD hDO g =ᵐ[μ.restrict D] g := by
  filter_upwards [LpToLpRestrictCLM_coeFn ℂ D (indicatorExtendLp hD hDO g),
    ae_restrict_of_ae (indicatorExtendLp_apply_ae hD hDO g), ae_restrict_mem hD] with x h1 h2 h3
  change LpToLpRestrictCLM α ℂ ℂ μ p D (indicatorExtendLp hD hDO g) x = g x
  rw [h1, h2, Set.indicator_of_mem h3]

end Rd
