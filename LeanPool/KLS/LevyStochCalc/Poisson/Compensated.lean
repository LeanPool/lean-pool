/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.RandomMeasure
public import LeanPool.KLS.LevyStochCalc.Poisson.NaturalFiltration
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedProcessQuadVar
public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDiff
public import LeanPool.KLS.LevyStochCalc.Martingale.CadlagModification
public import Mathlib.Probability.Martingale.Basic

/-!
# Compensated Poisson L²-Itô–Lévy integral

The L²-Itô–Lévy integral against the compensated Poisson random measure `Ñ`,
with its martingale, quadratic-variation, isometry, and càdlàg properties
(Applebaum 2009 §4.2, Theorems 4.2.3 and 4.2.4).

`stochasticIntegral` is the càdlàg adapted modification (`exists_cadlag_modification`)
of the `L²` integral process `process` (`Poisson/CompensatedProcess.lean`), the
`L²`-limit at every time of the integrals of the mark-step approximants of the
integrand (`Poisson/CompensatedApprox.lean`). `itoIsometry_compensated_unified_existence`
packages the martingale property, the quadratic variation, the L²-isometry, and the
càdlàg paths of `stochasticIntegral` in one 4-conjunct existential;
`itoLevyIsometry`, `quadVar_stochasticIntegral`, `martingale_stochasticIntegral`,
`cadlag_modification_exists`, and `L2Isometry.itoLevyIsometry` are its conjuncts.

`itoIsometry_diff_compensated` is the per-difference L²-isometry for this integral
(Applebaum Thm 4.2.3 step II): the integrals are modifications of the `L²` integral
processes, whose difference isometry `process_sub_lintegral_sq`
(`Poisson/CompensatedDiff.lean`) comes from the mark-step approximants of the two
integrands on a common dyadic refinement. It is consumed by
`Ito.Picard.picardStep_jump_diff_lipschitz_sq_componentwise` and mirrors
`Brownian.Ito.itoIsometry_diff_brownian`.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, 2009, §4.2 (Thm 4.2.3/4.2.4).
* Ikeda–Watanabe, *SDEs and Diffusion Processes*, 1989, §II.3.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
-- `open Classical` is scoped per-declaration (`open Classical in`) rather than
-- at file scope.

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

section Integral

variable {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]
  (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν) (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ
    : IsPoissonFiltration N ℱ)
  (φ : Ω → ℝ → E → ℝ)
  (h_meas : Measurable (fun (p : Ω × ℝ × E) => φ p.1 p.2.1 p.2.2))
  (h_progMeas : Probability.MarkedProgressivelyMeasurable ℱ φ)
  (h_sq_int_global : ∀ T : ℝ, 0 < T →
    ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
      (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)

include hℱ in
/-- The `L²` integral process `t ↦ ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` has a modification adapted to
the right-continuous natural filtration whose paths are almost surely càdlàg. -/
theorem exists_cadlag_modification :
    ∃ Y : ℝ → Ω → ℝ, Adapted ℱ.rightCont Y ∧
      (∀ t, Y t =ᵐ[P] process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ,
        Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y t ω)) ∧
          ∃ L : ℝ, Filter.Tendsto (fun s => Y s ω) (nhdsWithin t (Set.Iio t)) (nhds L) :=
  LevyStochCalc.Martingale.exists_adapted_ae_cadlag_of_eLpNorm
    (martingale_rightCont_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
    (process_eLpNorm_two_right_tendsto N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
    (fun _ ht => process_ae_zero_of_nonpos N ℱ hℱ φ h_meas h_progMeas h_sq_int_global ht.le)

/-- The L² Itô–Lévy integral `M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` against the compensated
measure of a Poisson random measure: the càdlàg adapted modification of the `L²` integral
process `process`, the `L²`-limit of the integrals of the mark-step approximants of `φ`. -/
noncomputable def stochasticIntegral (T : ℝ) : Ω → ℝ :=
  Classical.choose (exists_cadlag_modification N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) T

include hℱ in
lemma stochasticIntegral_adapted :
    Adapted ℱ.rightCont
      (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global) :=
  (Classical.choose_spec (exists_cadlag_modification N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)).1

include hℱ in
/-- The stochastic integral agrees almost surely with the `L²` integral process at every
time. -/
lemma stochasticIntegral_ae_eq_process (t : ℝ) :
    stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t
      =ᵐ[P] process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t :=
  (Classical.choose_spec
    (exists_cadlag_modification N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)).2.1 t

include hℱ in
/-- The paths of the stochastic integral are almost surely càdlàg. -/
lemma stochasticIntegral_cadlag :
    ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω)
          (nhdsWithin t (Set.Ioi t))
          (nhds (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω))
        ∧ ∃ L : ℝ,
            Filter.Tendsto
              (fun s => stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global s ω)
              (nhdsWithin t (Set.Iio t)) (nhds L) :=
  (Classical.choose_spec
    (exists_cadlag_modification N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)).2.2

include hℱ in
/-- The stochastic integral is a martingale on the right-continuous natural filtration. -/
theorem martingale_stochasticIntegral_rightCont :
    Martingale (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
      ℱ.rightCont P :=
  LevyStochCalc.Martingale.martingale_of_ae_eq
    (martingale_rightCont_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
    (fun t => (stochasticIntegral_adapted N ℱ hℱ φ h_meas h_progMeas h_sq_int_global
      t).stronglyMeasurable)
    (stochasticIntegral_ae_eq_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)

include hℱ in
/-- The compensated square `M_t² − ∫_0^t ∫_E φ(s, e)² ν(de) ds` of the stochastic integral is a
martingale on the right-continuous natural filtration. -/
theorem martingale_quadVar_stochasticIntegral_rightCont :
    Martingale
      (fun t ω => (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2
        - ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ ω s e) ^ 2 ∂ν)
      ℱ.rightCont P :=
  LevyStochCalc.Martingale.martingale_of_ae_eq
    (martingale_rightCont_quadVar_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global)
    (fun t => ((stochasticIntegral_adapted N ℱ hℱ φ h_meas h_progMeas h_sq_int_global
      t).stronglyMeasurable.pow 2).sub
      ((compensator_stronglyAdapted ℱ φ h_progMeas t).mono (ℱ.le_rightCont t)))
    (fun t => by
      filter_upwards [stochasticIntegral_ae_eq_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t]
        with ω hω
      show (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2 - _
        = (process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2 - _
      rw [hω]
      rfl)

include hℱ in
/-- The Itô–Lévy isometry of the stochastic integral at every time `T > 0`. -/
theorem isometry_stochasticIntegral (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global T ω‖₊ : ℝ≥0∞) ^ 2 ∂P
      = ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
          (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← process_lintegral_sq' N ℱ hℱ φ h_meas h_progMeas h_sq_int_global hT.le]
  refine lintegral_congr_ae ?_
  filter_upwards [stochasticIntegral_ae_eq_process N ℱ hℱ φ h_meas h_progMeas h_sq_int_global T]
    with ω hω
  rw [hω]

include h_meas h_progMeas h_sq_int_global hℱ in
/-- **Unified L²-Itô-Lévy integral with martingale + quadVar + isometry + càdlàg.**

For predictable square-integrable `φ : Ω → ℝ → E → ℝ`, there exists a process
`F : ℝ → Ω → ℝ` and a filtration `Filt` such that:

* `F` is a martingale wrt `Filt`,
* `(F t)² − ∫_0^t ∫_E |φ(s, e)|² ν(de) ds` is a martingale wrt `Filt`
  (quadratic variation identity),
* `∫⁻ ω, ‖F T‖₊² ∂P`
  `= ∫⁻ ω, ∫⁻ s in [0,T], ∫⁻ e, ‖φ ω s e‖₊² ∂ν ∂volume ∂P`
  for every `T > 0` with `h_meas + h_sq_int` (L²-isometry),
* `F` has càdlàg paths.

The statement asserts existence of *some* process `F` with these four
properties for `Filt = ℱ.rightCont`; it does not name `F` or mention `N`. The
witness supplied by the proof is `stochasticIntegral`; the pinned forms that
name it directly are `isometry_stochasticIntegral`,
`martingale_stochasticIntegral_rightCont` and
`martingale_quadVar_stochasticIntegral_rightCont`. Consolidates Applebaum
2009 Thm 4.2.3 + Thm 4.2.4.

The integrand hypotheses (`h_meas` joint measurability on `Ω×ℝ×E`,
`h_progMeas` progressive measurability w.r.t. `ℱ t`,
`h_sq_int_global` a global L² bound) are taken as *outer* hypotheses, mirroring
the Brownian-side statement; the existential body is then unconditional on them.
This matches Applebaum Thm 4.2.3's predictable-`φ` hypothesis class and prevents
a `Measurable`-only `F ≡ 0` from satisfying the conjuncts vacuously. `Filt` is
pinned to `ℱ.rightCont`, ruling out trivial-filtration
witnesses such as `Filt = const ⊤`.

**Reference**: Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed.,
CUP 2009, **Theorem 4.2.3** (martingale + quadratic variation + L²-isometry of
the L² Itô-Lévy integral) + **Theorem 4.2.4** (càdlàg modification); Ikeda &
Watanabe, *SDEs and Diffusion Processes*, 2nd ed., North-Holland 1989, **Section
II.3**.

**Construction**: `F := stochasticIntegral`, the càdlàg adapted modification
(`exists_cadlag_modification`, from the quasimartingale regularisation of
`RemyDegenne/brownian-motion`) of the `L²` integral process `process`
(`Poisson/CompensatedProcess.lean`), itself the `L²`-limit at every time of the
integrals of the mark-step approximants of `φ` (`Poisson/CompensatedApprox.lean`).
Conjunct 1 is `martingale_stochasticIntegral_rightCont`, conjunct 2 is
`martingale_quadVar_stochasticIntegral_rightCont` (the stage compensated squares
are martingales by the set-level increment isometries, and converge in `L¹`),
conjunct 3 is `isometry_stochasticIntegral`, conjunct 4 is
`stochasticIntegral_cadlag`. -/
theorem itoIsometry_compensated_unified_existence :
    ∃ (F : ℝ → Ω → ℝ) (Filt : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›),
      Filt = ℱ.rightCont ∧
      MeasureTheory.Martingale F Filt P ∧
      MeasureTheory.Martingale
        (fun t ω => (F t ω) ^ 2
          - ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ ω s e) ^ 2 ∂ν) Filt P ∧
      (∀ T : ℝ, 0 < T →
        ∫⁻ ω, (‖F T ω‖₊ : ℝ≥0∞) ^ 2 ∂P =
          ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
            (‖φ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ,
        Filter.Tendsto (fun s => F s ω) (nhdsWithin t (Set.Ioi t)) (nhds (F t ω))
          ∧ ∃ L : ℝ,
              Filter.Tendsto (fun s => F s ω) (nhdsWithin t (Set.Iio t)) (nhds L)) :=
  ⟨stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global, ℱ.rightCont, rfl,
    martingale_stochasticIntegral_rightCont N ℱ hℱ φ h_meas h_progMeas h_sq_int_global,
    martingale_quadVar_stochasticIntegral_rightCont N ℱ hℱ φ h_meas h_progMeas h_sq_int_global,
    isometry_stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global,
    stochasticIntegral_cadlag N ℱ hℱ φ h_meas h_progMeas h_sq_int_global⟩

include hℱ in
/-- Itô-Lévy L² isometry on the bounded interval `[0, T]`.

  `𝔼[ (∫_0^T ∫_E φ(s, e) Ñ(ds, de))² ] = 𝔼[ ∫_0^T ∫_E |φ(s, e)|² ν(de) ds ]`

ENNReal form. -/
theorem itoLevyIsometry (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global T ω‖₊
        : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        ((‖φ ω s e‖₊ : ℝ≥0∞)) ^ 2 ∂ν ∂volume ∂P :=
  isometry_stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global T hT

include hℱ in
/-- **Quadratic variation of the L² Itô-Lévy integral.**

For predictable square-integrable `φ`, the process
`t ↦ (M_t)² − ∫_0^t ∫_E |φ(s, e)|² ν(de) ds`, where
`M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)` is the L² Itô-Lévy integral, is a
martingale with respect to some filtration (the statement does not name it;
the pinned form for `ℱ.rightCont` is
`martingale_quadVar_stochasticIntegral_rightCont`). -/
theorem quadVar_stochasticIntegral :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => fun ω : Ω =>
          (stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ^ 2
            - ∫ s in Set.Icc (0 : ℝ) t, ∫ e, (φ ω s e) ^ 2 ∂ν)
        F P :=
  ⟨ℱ.rightCont,
    martingale_quadVar_stochasticIntegral_rightCont N ℱ hℱ φ h_meas h_progMeas h_sq_int_global⟩

include hℱ in
/-- **The L² Itô-Lévy integral is a martingale.**

The compensated-Poisson stochastic integral `M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)`
is a martingale with respect to some filtration (the statement does not name
it; the pinned form for `ℱ.rightCont` is
`martingale_stochasticIntegral_rightCont`). -/
theorem martingale_stochasticIntegral :
    ∃ F : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›,
      MeasureTheory.Martingale
        (fun t : ℝ => stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t) F P :=
  ⟨ℱ.rightCont,
    martingale_stochasticIntegral_rightCont N ℱ hℱ φ h_meas h_progMeas h_sq_int_global⟩

include hℱ in
/-- **Càdlàg modification of L² Itô-Lévy integral.**

The compensated-Poisson stochastic integral `M_t = ∫_0^t ∫_E φ(s, e) Ñ(ds, de)`
admits a càdlàg modification: there exists `M' : ℝ → Ω → ℝ` equal to
`stochasticIntegral N ℱ hℱ φ` a.s. at each `t`, with càdlàg paths a.s. The integral is
itself càdlàg, so `M' := stochasticIntegral N ℱ hℱ φ`. -/
theorem cadlag_modification_exists :
    ∃ M' : ℝ → Ω → ℝ,
      (∀ t : ℝ, ∀ᵐ ω ∂P,
        M' t ω = stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global t ω) ∧
      (∀ᵐ ω ∂P,
        ∀ t : ℝ,
          (Filter.Tendsto (fun s => M' s ω) (nhdsWithin t (Set.Ioi t))
              (nhds (M' t ω)))
            ∧ ∃ L : ℝ,
                Filter.Tendsto (fun s => M' s ω) (nhdsWithin t (Set.Iio t))
                  (nhds L)) :=
  ⟨stochasticIntegral N ℱ hℱ φ h_meas h_progMeas h_sq_int_global,
    fun _ => Filter.Eventually.of_forall (fun _ => rfl),
    stochasticIntegral_cadlag N ℱ hℱ φ h_meas h_progMeas h_sq_int_global⟩

end Integral

/-- **L²-isometry for the *difference* of two compensated-Poisson Itô-Lévy integrals.**

For two jointly-measurable, progressively-measurable, L²-bounded
integrands `φ₁, φ₂ : Ω → ℝ → E → ℝ`, the difference
`M¹_T - M²_T := ∫_0^T ∫_E φ₁ Ñ - ∫_0^T ∫_E φ₂ Ñ` satisfies the
L²-isometry against the *integrand difference*:

  `𝔼 |M¹_T - M²_T|² = 𝔼 ∫_0^T ∫_E |φ₁(s, e) - φ₂(s, e)|² ν(de) ds`.

This is the per-`(φ₁, φ₂)` instance of the L²-linearity + isometry of the
Itô-Lévy integral as a linear isometry from `L²(Ω × [0, T] × E, dP ⊗ ds ⊗ dν)`
to `L²(Ω, dP)` (Applebaum, *Lévy Processes and Stochastic Calculus*, 2nd ed.,
CUP 2009, **Theorem 4.2.3** step (II); Ikeda-Watanabe **Section II.3**). Both
integrals are modifications of the `L²` integral processes of their integrands,
whose difference isometry `process_sub_lintegral_sq` comes from the mark-step
approximants of the two integrands on a common dyadic refinement. -/
theorem itoIsometry_diff_compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    (φ₁ φ₂ : Ω → ℝ → E → ℝ)
    (h_meas₁ : Measurable (fun (p : Ω × ℝ × E) => φ₁ p.1 p.2.1 p.2.2))
    (h_meas₂ : Measurable (fun (p : Ω × ℝ × E) => φ₂ p.1 p.2.1 p.2.2))
    (h_progMeas₁ : Probability.MarkedProgressivelyMeasurable ℱ φ₁)
    (h_progMeas₂ : Probability.MarkedProgressivelyMeasurable ℱ φ₂)
    (h_sq_int_global₁ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ₁ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (h_sq_int_global₂ : ∀ T : ℝ, 0 < T →
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P < ⊤)
    (T : ℝ) (hT : 0 < T) :
    ∫⁻ ω, (‖stochasticIntegral N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq_int_global₁ T ω
              - stochasticIntegral N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq_int_global₂ T ω‖₊
            : ℝ≥0∞) ^ 2 ∂P =
      ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T, ∫⁻ e,
        (‖φ₁ ω s e - φ₂ ω s e‖₊ : ℝ≥0∞) ^ 2 ∂ν ∂volume ∂P := by
  rw [← process_sub_lintegral_sq N ℱ hℱ φ₁ φ₂ h_meas₁ h_meas₂ h_progMeas₁ h_progMeas₂
    h_sq_int_global₁ h_sq_int_global₂ hT]
  refine lintegral_congr_ae ?_
  filter_upwards [stochasticIntegral_ae_eq_process N ℱ hℱ φ₁ h_meas₁ h_progMeas₁ h_sq_int_global₁ T,
    stochasticIntegral_ae_eq_process N ℱ hℱ φ₂ h_meas₂ h_progMeas₂ h_sq_int_global₂ T] with ω h₁ h₂
  rw [h₁, h₂]

end LevyStochCalc.Poisson.Compensated
