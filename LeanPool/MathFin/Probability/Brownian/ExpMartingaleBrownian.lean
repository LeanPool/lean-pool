/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Brownian.ExpMartingaleQBrownian
public import LeanPool.KLS.BrownianMotion.Gaussian.BrownianMotion

/-!
# Brownian motion from an exponential martingale

`Probability/Brownian/ExpMartingaleQBrownian.lean` turns the exponential-martingale data
`IsExpQMartingale Q 𝓕 Y T` (`Y` adapted, `Y_0 = 0` a.e., every `t ↦ exp(a·Y_t − ½a²t)` a
`Q`-martingale on `[0,T]`) into `N(0,t−s)` increments and Mathlib's `HasIndepIncrements` on
`[0,T]`. Its docstring names what it leaves out: independence of the increments from the past,
and the conclusion on the whole time axis. This module supplies both.

* **Independence from the past.** The conditional moment-generating function
  `𝔼_Q[exp(a·(Y_t − Y_s)) | 𝓕_s] = exp(½a²(t−s))` is deterministic. Integrated over
  `A ∈ 𝓕_s`, it says that the law of `Y_t − Y_s` under `Q` restricted to `A` has the
  moment-generating function of `Q(A)·N(0,t−s)`, and a finite measure with every exponential
  moment is fixed by its moment-generating function (`measure_eq_of_mgf_id_eq`). Evaluated on a
  Borel set `B`, this is `Q({Y_t − Y_s ∈ B} ∩ A) = Q(Y_t − Y_s ∈ B)·Q(A)`.
* **The whole time axis.** If the data hold for every horizon `T`, the marginal laws are
  `N(0,t)` and the increments are independent, so `Y` is a pre-Brownian motion (Mathlib's
  `HasIndepIncrements.isPreBrownianReal_of_hasLaw`); with independence from the past it is a
  filtered pre-Brownian motion in the sense of BrownianMotion's `IsFilteredPreBrownian`; with
  continuous paths it is Mathlib's `IsBrownianReal`.

This is the exponential-martingale form of Lévy's characterization: the hypothesis is that every
`exp(a·Y − ½a²·)` is a martingale. Lévy's characterization in its usual form (a continuous local
martingale `M` with `M₀ = 0` and `M² − t` a local martingale is a Brownian motion) is proved from
this theorem in `LevyCharacterization.lean`: the exponential martingales come from a cell-by-cell
second-order expansion, not from Itô's formula.

## Main results

* `MathFin.indep_increment_of_expMartingale`: `Y_t − Y_s` is `Q`-independent of `𝓕_s` for
  `s ≤ t ≤ T`.
* `MathFin.hasIndepIncrements_of_forall_expMartingale`: `HasIndepIncrements Y Q` on all of `ℝ≥0`
  when the data hold for every horizon.
* `MathFin.isPreBrownianReal_of_expMartingale`: then `IsPreBrownianReal Y Q`.
* `MathFin.isFilteredPreBrownian_of_expMartingale`: then `IsFilteredPreBrownian Y 𝓕 Q`.
* `MathFin.isBrownianReal_of_expMartingale`: with a.s. continuous paths, `IsBrownianReal Y Q`.

## Tags

Lévy characterization, exponential martingale, Brownian motion, independent increments,
filtered Brownian motion, MSC 60J65, MSC 60G44
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {Q : Measure Ω} [IsProbabilityMeasure Q]
  {𝓕 : Filtration ℝ≥0 mΩ} {Y : ℝ≥0 → Ω → ℝ} {T : ℝ≥0}

/-- **Increments are independent of the past.** For `s ≤ t ≤ T`, `Y_t − Y_s` is `Q`-independent
of `𝓕_s`. Integrating the deterministic conditional moment-generating function
(`IsExpQMartingale.condExp_exp_increment`) over `A ∈ 𝓕_s` shows that the law of `Y_t − Y_s` under
`Q` restricted to `A` has the moment-generating function of `Q(A)·N(0,t−s)`, hence is that measure
(`measure_eq_of_mgf_id_eq`); on a Borel set `B` this reads
`Q({Y_t − Y_s ∈ B} ∩ A) = Q(A)·N(0,t−s)(B) = Q(A)·Q(Y_t − Y_s ∈ B)`. -/
theorem indep_increment_of_expMartingale (h : IsExpQMartingale Q 𝓕 Y T) {s t : ℝ≥0}
    (hst : s ≤ t) (htT : t ≤ T) :
    Indep (MeasurableSpace.comap (fun ω ↦ Y t ω - Y s ω) inferInstance) (𝓕 s) Q := by
  have hD : Measurable fun ω ↦ Y t ω - Y s ω := (h.measurable t).sub (h.measurable s)
  have hlaw := increment_map_eq_gaussianReal_of_expMartingale h hst htT
  have hlaw' : HasLaw (fun ω ↦ Y t ω - Y s ω) (gaussianReal 0 (t - s)) Q :=
    ⟨hD.aemeasurable, hlaw⟩
  have hexp (u : ℝ) : Integrable (fun ω ↦ Real.exp (u * (Y t ω - Y s ω))) Q :=
    hlaw'.integrable_fun_comp (integrable_exp_mul_gaussianReal u)
  refine (Indep_iff _ _ Q).2 fun _ A ⟨B, hB, hBA⟩ hA ↦ ?_
  subst hBA
  have : IsFiniteMeasure (Q A • gaussianReal 0 (t - s)) :=
    Measure.smul_finite _ (measure_ne_top Q A)
  have hrestrict : (Q.restrict A).map (fun ω ↦ Y t ω - Y s ω) = Q A • gaussianReal 0 (t - s) := by
    refine measure_eq_of_mgf_id_eq (fun u ↦ (integrable_map_measure (by fun_prop)
      hD.aemeasurable).2 (hexp u).restrict) ?_
    funext u
    rw [mgf_id_map hD.aemeasurable, mgf_smul_measure, mgf_id_gaussianReal, mgf,
      ← setIntegral_condExp (𝓕.le s) (hexp u) hA,
      setIntegral_congr_ae (𝓕.le s A hA) ((h.condExp_exp_increment u hst
        htT).mono fun _ hω _ ↦ hω), setIntegral_const, NNReal.coe_sub hst, measureReal_def,
      smul_eq_mul]
    ring_nf
  have hB' := congrArg (· B) hrestrict
  simp only [Measure.map_apply hD hB, Measure.restrict_apply (hD hB), smul_apply,
    smul_eq_mul, ← hlaw] at hB'
  rw [hB', mul_comm]

/-! ### The whole time axis -/

/-- **Independent increments on the whole axis.** If the exponential-martingale data hold for every
horizon `T`, then `Y` has independent increments on `ℝ≥0`: times `t₀ ≤ ⋯ ≤ tₙ` lie in `[0,tₙ]`,
where `hasIndepIncrements_of_expMartingale` applies. -/
theorem hasIndepIncrements_of_forall_expMartingale (h : ∀ T, IsExpQMartingale Q 𝓕 Y T) :
    HasIndepIncrements Y Q := fun n t ht ↦
  hasIndepIncrements_of_expMartingale (h (t (Fin.last n))) n
    (fun i ↦ ⟨t i, ht (Fin.le_last i)⟩) fun _ _ hij ↦ ht hij

/-- **Pre-Brownian motion from exponential martingales.** If the exponential-martingale data hold
for every horizon, `Y` is a pre-Brownian motion under `Q`: its marginals are `N(0,t)`
(`map_eq_gaussianReal_of_expMartingale`) and its increments are independent, which fixes every
finite-dimensional law (`HasIndepIncrements.isPreBrownianReal_of_hasLaw`). -/
theorem isPreBrownianReal_of_expMartingale (h : ∀ T, IsExpQMartingale Q 𝓕 Y T) :
    IsPreBrownianReal Y Q :=
  (hasIndepIncrements_of_forall_expMartingale h).isPreBrownianReal_of_hasLaw fun t ↦
    ⟨((h t).measurable t).aemeasurable, map_eq_gaussianReal_of_expMartingale (h t) le_rfl⟩

/-- **Filtered pre-Brownian motion from exponential martingales.** If the exponential-martingale
data hold for every horizon, `Y` is an `𝓕`-pre-Brownian motion under `Q` in the sense of
BrownianMotion's `IsFilteredPreBrownian`: pre-Brownian, adapted, and with each increment
`Y_t − Y_s` independent of `𝓕_s` (`indep_increment_of_expMartingale`). -/
theorem isFilteredPreBrownian_of_expMartingale (h : ∀ T, IsExpQMartingale Q 𝓕 Y T) :
    IsFilteredPreBrownian Y 𝓕 Q where
  toIsPreBrownianReal := isPreBrownianReal_of_expMartingale h
  stronglyAdapted := (h 0).adapted
  indep _ t hst := indep_increment_of_expMartingale (h t) hst le_rfl

/-- **Brownian motion from exponential martingales.** If the exponential-martingale data hold for
every horizon and the paths of `Y` are a.s. continuous, `Y` is a Brownian motion under `Q`
(`IsBrownianReal`). -/
theorem isBrownianReal_of_expMartingale (h : ∀ T, IsExpQMartingale Q 𝓕 Y T)
    (hcont : ∀ᵐ ω ∂Q, Continuous (Y · ω)) : IsBrownianReal Y Q where
  toIsPreBrownianReal := isPreBrownianReal_of_expMartingale h
  cont := hcont

end MathFin
