/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0, with
-- source adaptations (deprecated names, proof-context visibility) listed in vendor/port.patch.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.ItoFinsetSum
public import LeanPool.KLS.LevyStochCalc.Brownian.ItoPullOut
public import LeanPool.KLS.LevyStochCalc.Probability.StoppedProgressive

/-!
# Optional stopping for the Itô integral, for a stopping time of finite range

Cutting the integrand off at a stopping time that takes finitely many values below the horizon
subtracts, for each of those values `c`, the increment of the integral across `(c, T]` weighted
by the event `{τ = c}`. That weight is known at `c` and the cut integrand is carried by `(c, T]`,
so it passes inside the integral; the resulting sum telescopes into the integral evaluated at
`τ ∧ T`.

## Main statements

* `LevyStochCalc.Brownian.Ito.hitInd`, `cutTerm` — the weight and the cut integrand.
* `LevyStochCalc.Brownian.Ito.stopped_eq_sub_sum` — the pathwise decomposition of the cut
  integrand.
* `LevyStochCalc.Brownian.Ito.stochasticIntegralBrownian_stopped` — the identity.
-/

@[expose] public section

namespace LevyStochCalc.Brownian.Ito

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

omit [IsProbabilityMeasure P] in
/-- Square-integrability transfers along a pointwise domination of the integrands. -/
theorem energy_lt_top_of_abs_le {K G : Ω → ℝ → ℝ} (h : ∀ ω s, |K ω s| ≤ |G ω s|)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖G ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ := by
  intro T hT
  refine lt_of_le_of_lt (lintegral_mono fun ω => lintegral_mono fun s => ?_) (hq T hT)
  have hle : (‖K ω s‖₊ : ℝ≥0∞) ≤ (‖G ω s‖₊ : ℝ≥0∞) := by
    refine ENNReal.coe_le_coe.mpr ?_
    rw [← NNReal.coe_le_coe]
    simpa [Real.norm_eq_abs] using h ω s
  gcongr

section Stopped

variable (τ : Ω → WithTop ℝ)

/-- The indicator of the event that the stopping time takes the value `c`. -/
noncomputable def hitInd (c : ℝ) : Ω → ℝ :=
  Set.indicator {ω | τ ω = ((c : ℝ) : WithTop ℝ)} fun _ => (1 : ℝ)

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem abs_hitInd_le_one (c : ℝ) (ω : Ω) : |hitInd τ c ω| ≤ 1 := by
  by_cases h : ω ∈ {ω | τ ω = ((c : ℝ) : WithTop ℝ)} <;> simp [hitInd, h]

theorem measurable_hitInd {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (c : ℝ) : Measurable (hitInd τ c) :=
  measurable_const.indicator (ℱ.le c _ (hτ.measurableSet_eq c))

theorem stronglyMeasurable_hitInd {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) (c : ℝ) :
    @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ c) (hitInd τ c) := by
  let : MeasurableSpace Ω := ℱ c
  exact (measurable_const.indicator (hτ.measurableSet_eq c)).stronglyMeasurable

/-- The part of the integrand that the cut at `τ = c` removes from the window `(c, t]`. -/
noncomputable def cutTerm (H : Ω → ℝ → ℝ) (c t : ℝ) : Ω → ℝ → ℝ :=
  fun ω s => hitInd τ c ω * indIoc Ω c t ω s * H ω s

theorem measurable_cutTerm {ℱ : Filtration ℝ ‹MeasurableSpace Ω›}
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hm : Measurable (Function.uncurry H)) (c t : ℝ) :
    Measurable (Function.uncurry (cutTerm τ H c t)) := by
  have hind : Measurable fun p : Ω × ℝ => indIoc Ω c t p.1 p.2 := by
    simp only [indIoc]
    exact (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
  exact (((measurable_hitInd τ hτ c).comp measurable_fst).mul hind).mul hm

theorem progressivelyMeasurable_cutTerm (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (hτ : MeasureTheory.IsStoppingTime ℱ τ) {H : Ω → ℝ → ℝ}
    (hp : Probability.ProgressivelyMeasurable ℱ H) {c t : ℝ} (hc : 0 ≤ c) (hct : c < t) :
    Probability.ProgressivelyMeasurable ℱ (cutTerm τ H c t) :=
  (progressivelyMeasurable_mul_indIoc ℱ hc hct ⟨1, abs_hitInd_le_one τ c⟩
    (measurable_hitInd τ hτ c) (stronglyMeasurable_hitInd τ hτ c)).mul hp

omit [IsProbabilityMeasure P] [MeasurableSpace Ω] in
theorem abs_cutTerm_le {H : Ω → ℝ → ℝ} (c t : ℝ) (ω : Ω) (s : ℝ) :
    |cutTerm τ H c t ω s| ≤ |H ω s| := by
  have h1 : |hitInd τ c ω| ≤ 1 := abs_hitInd_le_one τ c ω
  have h2 : |indIoc Ω c t ω s| ≤ 1 := indIoc_le_one c t ω s
  calc |cutTerm τ H c t ω s| = |hitInd τ c ω| * |indIoc Ω c t ω s| * |H ω s| := by
        rw [cutTerm, abs_mul, abs_mul]
    _ ≤ 1 * 1 * |H ω s| := by
        gcongr
    _ = |H ω s| := by ring

omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
theorem abs_stopped_le' {H : Ω → ℝ → ℝ} (ω : Ω) (s : ℝ) :
    |Probability.stopped τ H ω s| ≤ |H ω s| := Probability.abs_stopped_le τ H ω s

/-- The integrand restricted to a window, as a `cutTerm` with unit weight. -/
noncomputable def indTerm (H : Ω → ℝ → ℝ) (c t : ℝ) : Ω → ℝ → ℝ :=
  fun ω s => indIoc Ω c t ω s * H ω s

omit [IsProbabilityMeasure P] in
theorem measurable_indTerm {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H)) (c t : ℝ) :
    Measurable (Function.uncurry (indTerm H c t)) := by
  have hind : Measurable fun p : Ω × ℝ => indIoc Ω c t p.1 p.2 := by
    simp only [indIoc]
    exact (measurable_const.indicator measurableSet_Ioc).comp measurable_snd
  exact hind.mul hm

theorem progressivelyMeasurable_indTerm (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {H : Ω → ℝ → ℝ} (hp : Probability.ProgressivelyMeasurable ℱ H) {c t : ℝ} (hc : 0 ≤ c)
    (hct : c < t) : Probability.ProgressivelyMeasurable ℱ (indTerm H c t) := by
  have hfun : (fun (ω : Ω) (s : ℝ) => (1 : ℝ) * indIoc Ω c t ω s)
      = fun ω s => indIoc Ω c t ω s := by
    funext ω s
    ring
  have h1 := progressivelyMeasurable_mul_indIoc (Ω := Ω) ℱ hc hct
    (V := fun _ => (1 : ℝ)) ⟨1, fun ω => by simp⟩ measurable_const stronglyMeasurable_const
  exact (hfun ▸ h1).mul hp

omit [IsProbabilityMeasure P] [MeasurableSpace Ω] in
theorem abs_indTerm_le {H : Ω → ℝ → ℝ} (c t : ℝ) (ω : Ω) (s : ℝ) :
    |indTerm H c t ω s| ≤ |H ω s| := by
  have h2 : |indIoc Ω c t ω s| ≤ 1 := indIoc_le_one c t ω s
  calc |indTerm H c t ω s| = |indIoc Ω c t ω s| * |H ω s| := by rw [indTerm, abs_mul]
    _ ≤ 1 * |H ω s| := by gcongr
    _ = |H ω s| := by ring

omit [IsProbabilityMeasure P] in
omit [MeasurableSpace Ω] in
/-- **The pathwise decomposition of the cut integrand.** On the window `(0, t]` the integrand cut
off at `τ` is the integrand minus, for each value `c` the stopping time can take below `t`, the
piece it carries on `(c, t]`. -/
theorem stopped_eq_sub_sum (H : Ω → ℝ → ℝ) {t : ℝ} (J : Finset ℝ)
    (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    indTerm (Probability.stopped τ H) 0 t
      = fun ω s => indTerm H 0 t ω s - ∑ c ∈ J, cutTerm τ H c t ω s := by
  classical
  funext ω s
  simp only [indTerm]
  by_cases hs : s ∈ Set.Ioc (0 : ℝ) t
  · have hind0 : indIoc Ω 0 t ω s = 1 := by simp [indIoc, hs]
    have hzero : ∀ c ∈ J, τ ω ≠ ((c : ℝ) : WithTop ℝ) → cutTerm τ H c t ω s = 0 := by
      intro c _ hne
      simp [cutTerm, hitInd, Set.indicator_of_notMem (show ω ∉ {ω | τ ω = ((c : ℝ) :
        WithTop ℝ)} from hne)]
    rcases hτJ ω with ⟨c₀, hc₀J, hc₀⟩ | hge
    · have hsum : ∑ c ∈ J, cutTerm τ H c t ω s = cutTerm τ H c₀ t ω s := by
        refine Finset.sum_eq_single_of_mem c₀ hc₀J fun c hc hne => ?_
        refine hzero c hc ?_
        rw [hc₀]
        exact fun hcc => hne (by exact_mod_cast hcc.symm)
      have hhit : hitInd τ c₀ ω = 1 := by
        simp [hitInd, Set.indicator_of_mem (show ω ∈ {ω | τ ω = ((c₀ : ℝ) : WithTop ℝ)} from hc₀)]
      rw [hsum, hind0, cutTerm, hhit]
      by_cases hsc : s ≤ c₀
      · have h1 : Probability.stopped τ H ω s = H ω s := by
          rw [Probability.stopped, ite_eq_left]
          rw [hc₀]
          exact_mod_cast hsc
        have h2 : indIoc Ω c₀ t ω s = 0 := by
          simp only [indIoc]
          rw [Set.indicator_of_notMem]
          exact fun hmem => absurd hmem.1 (not_lt.mpr hsc)
        rw [h1, h2]
        ring
      · push Not at hsc
        have h1 : Probability.stopped τ H ω s = 0 := by
          rw [Probability.stopped, ite_eq_right]
          rw [hc₀]
          exact fun hcon => absurd (by exact_mod_cast hcon : s ≤ c₀) (not_le.mpr hsc)
        have h2 : indIoc Ω c₀ t ω s = 1 := by
          simp [indIoc, Set.indicator_of_mem (show s ∈ Set.Ioc c₀ t from ⟨hsc, hs.2⟩)]
        rw [h1, h2]
        ring
    · have hsum : ∑ c ∈ J, cutTerm τ H c t ω s = 0 := by
        refine Finset.sum_eq_zero fun c hc => hzero c hc ?_
        intro hcon
        rw [hcon] at hge
        exact absurd (by exact_mod_cast hge : t ≤ c) (not_le.mpr (hJt c hc))
      have h1 : Probability.stopped τ H ω s = H ω s := by
        rw [Probability.stopped, ite_eq_left]
        exact le_trans (by exact_mod_cast hs.2) hge
      rw [hsum, hind0, h1]
      ring
  · have hind0 : indIoc Ω 0 t ω s = 0 := by
      simp only [indIoc]
      exact Set.indicator_of_notMem hs _
    have hsum : ∑ c ∈ J, cutTerm τ H c t ω s = 0 := by
      refine Finset.sum_eq_zero fun c hc => ?_
      have hnot : s ∉ Set.Ioc c t := by
        intro hmem
        exact hs ⟨lt_of_le_of_lt (hJ0 c hc) hmem.1, hmem.2⟩
      have hz : indIoc Ω c t ω s = 0 := by
        simp only [indIoc]
        exact Set.indicator_of_notMem hnot _
      simp [cutTerm, hz]
    rw [hsum, hind0]
    ring

section Identity

variable (W : LevyStochCalc.Brownian.BrownianMotion P)
  (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsBrownianFiltration W ℱ)

include hℱ in
/-- The window cut is invisible at the horizon. -/
theorem stochasticIntegralBrownian_indTerm_zero {t : ℝ} (ht : 0 < t) {K : Ω → ℝ → ℝ}
    (hmK : Measurable (Function.uncurry K)) (hpK : Probability.ProgressivelyMeasurable ℱ K)
    (hqK : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖K ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    (hmW : Measurable (Function.uncurry (indTerm K 0 t)))
    (hpW : Probability.ProgressivelyMeasurable ℱ (indTerm K 0 t))
    (hqW : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖indTerm K 0 t ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤) :
    stochasticIntegralBrownian W ℱ hℱ (indTerm K 0 t) hmW hpW hqW t
      =ᵐ[P] stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK t := by
  filter_upwards [stochasticIntegralBrownian_indicator_Ioc W ℱ hℱ K hmK hpK hqK
      (le_refl (0 : ℝ)) ht hmW hpW hqW ht,
    stochasticIntegralBrownian_ae_zero_of_nonpos W ℱ hℱ K hmK hpK hqK (le_refl (0 : ℝ))]
    with ω hloc hz
  have hloc' : stochasticIntegralBrownian W ℱ hℱ (indTerm K 0 t) hmW hpW hqW t ω
      = stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK (min t t) ω
        - stochasticIntegralBrownian W ℱ hℱ K hmK hpK hqK (min 0 t) ω := hloc
  rw [hloc', min_self, min_eq_left ht.le, hz]
  simp

include hℱ in
/-- **Optional stopping for the Itô integral, for a stopping time of finite range.** -/
theorem stochasticIntegralBrownian_stopped
    (hτ : MeasureTheory.IsStoppingTime ℱ τ)
    {H : Ω → ℝ → ℝ} (hm : Measurable (Function.uncurry H))
    (hp : Probability.ProgressivelyMeasurable ℱ H)
    (hq : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖H ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤)
    {t : ℝ} (ht : 0 < t) (J : Finset ℝ)
    (hJ0 : ∀ c ∈ J, 0 ≤ c) (hJt : ∀ c ∈ J, c < t)
    (hτJ : ∀ ω, (∃ c ∈ J, τ ω = ((c : ℝ) : WithTop ℝ)) ∨ ((t : ℝ) : WithTop ℝ) ≤ τ ω) :
    stochasticIntegralBrownian W ℱ hℱ (Probability.stopped τ H)
        (Probability.measurable_uncurry_stopped hτ hm)
        (Probability.ProgressivelyMeasurable.stopped hτ hp)
        (energy_lt_top_of_abs_le (fun ω s => Probability.abs_stopped_le τ H ω s) hq) t
      =ᵐ[P] fun ω => stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
        - ∑ c ∈ J, hitInd τ c ω * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω) := by
  classical
  have hmS := Probability.measurable_uncurry_stopped hτ hm
  have hpS := Probability.ProgressivelyMeasurable.stopped hτ hp
  have hqS := energy_lt_top_of_abs_le (P := P) (fun ω s => Probability.abs_stopped_le τ H ω s) hq
  have hmI0 := measurable_indTerm hm 0 t
  have hpI0 := progressivelyMeasurable_indTerm ℱ hp (le_refl (0 : ℝ)) ht
  have hqI0 := energy_lt_top_of_abs_le (P := P) (fun ω s => abs_indTerm_le (H := H) 0 t ω s) hq
  have hmW := measurable_indTerm hmS 0 t
  have hpW := progressivelyMeasurable_indTerm ℱ hpS (le_refl (0 : ℝ)) ht
  have hqW := energy_lt_top_of_abs_le (P := P)
    (fun ω s => abs_indTerm_le (H := Probability.stopped τ H) 0 t ω s) hqS
  set ι := {c : ℝ // c ∈ J} with hι
  have hmF : ∀ i : ι, Measurable (Function.uncurry (cutTerm τ H i.1 t)) :=
    fun i => measurable_cutTerm τ hτ hm i.1 t
  have hpF : ∀ i : ι, Probability.ProgressivelyMeasurable ℱ (cutTerm τ H i.1 t) :=
    fun i => progressivelyMeasurable_cutTerm τ ℱ hτ hp (hJ0 i.1 i.2) (hJt i.1 i.2)
  have hqF : ∀ (i : ι) (T : ℝ), 0 < T → ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) T,
      (‖cutTerm τ H i.1 t ω s‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    fun i => energy_lt_top_of_abs_le (P := P)
      (fun ω s => abs_cutTerm_le τ (H := H) i.1 t ω s) hq
  obtain ⟨hmSum, hpSum, hqSum, hSum⟩ := exists_stochasticIntegralBrownian_finsetSum W ℱ hℱ
    (fun i : ι => cutTerm τ H i.1 t) hmF hpF hqF (Finset.univ : Finset ι) ht
  have hmD : Measurable (Function.uncurry fun ω u =>
      indTerm H 0 t ω u - ∑ i : ι, cutTerm τ H i.1 t ω u) := hmI0.sub hmSum
  have hpD : Probability.ProgressivelyMeasurable ℱ
      (fun ω u => indTerm H 0 t ω u - ∑ i : ι, cutTerm τ H i.1 t ω u) := hpI0.sub hpSum
  have hqD : ∀ T, 0 < T → ∫⁻ ω, ∫⁻ u in Set.Icc (0 : ℝ) T,
      (‖indTerm H 0 t ω u - ∑ i : ι, cutTerm τ H i.1 t ω u‖₊ : ℝ≥0∞) ^ 2 ∂volume ∂P < ⊤ :=
    lintegral_energy_lt_top_of_bound (fun ω u => sq_nnnorm_sub_le_two_mul _ _) hmI0 hmSum
      hqI0 hqSum
  have hpath : indTerm (Probability.stopped τ H) 0 t
      = fun ω u => indTerm H 0 t ω u - ∑ i : ι, cutTerm τ H i.1 t ω u := by
    rw [stopped_eq_sub_sum τ H J hJ0 hJt hτJ]
    funext ω u
    congr 1
    exact (Finset.sum_coe_sort J fun c => cutTerm τ H c t ω u).symm
  have hterm : ∀ i : ι,
      stochasticIntegralBrownian W ℱ hℱ (cutTerm τ H i.1 t) (hmF i) (hpF i) (hqF i) t
        =ᵐ[P] fun ω => hitInd τ i.1 ω
          * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
            - stochasticIntegralBrownian W ℱ hℱ H hm hp hq i.1 ω) := by
    intro i
    have hc0 : 0 ≤ i.1 := hJ0 i.1 i.2
    have hct : i.1 < t := hJt i.1 i.2
    have hmIc := measurable_indTerm hm i.1 t
    have hpIc := progressivelyMeasurable_indTerm ℱ hp hc0 hct
    have hqIc := energy_lt_top_of_abs_le (P := P)
      (fun ω s => abs_indTerm_le (H := H) i.1 t ω s) hq
    have hpull := mul_stochasticIntegralBrownian_indIoc W ℱ hℱ hc0 hct
      (V := hitInd τ i.1) ⟨1, abs_hitInd_le_one τ i.1⟩ (measurable_hitInd τ hτ i.1)
      (stronglyMeasurable_hitInd τ hτ i.1) H hm hp hq hmIc hpIc hqIc
      (hmF i) (hpF i) (hqF i) ht
    have hloc := stochasticIntegralBrownian_indicator_Ioc W ℱ hℱ H hm hp hq hc0 hct
      hmIc hpIc hqIc ht
    filter_upwards [hpull, hloc] with ω hpullω hlocω
    have hpull' : hitInd τ i.1 ω
        * stochasticIntegralBrownian W ℱ hℱ (indTerm H i.1 t) hmIc hpIc hqIc t ω
        = stochasticIntegralBrownian W ℱ hℱ (cutTerm τ H i.1 t) (hmF i) (hpF i) (hqF i) t ω :=
      hpullω
    have hloc' : stochasticIntegralBrownian W ℱ hℱ (indTerm H i.1 t) hmIc hpIc hqIc t ω
        = stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min t t) ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq (min i.1 t) ω := hlocω
    rw [← hpull', hloc', min_self, min_eq_left hct.le]
  have hstep := stochasticIntegralBrownian_indTerm_zero W ℱ hℱ ht hmS hpS hqS hmW hpW hqW
  have hcongr := stochasticIntegralBrownian_congr_fun W ℱ hℱ hpath hmW hpW hqW hmD hpD hqD t
  have hsub := stochasticIntegralBrownian_sub W ℱ hℱ hmI0 hmSum hpI0 hpSum hqI0 hqSum
    hmD hpD hqD ht
  have hI0 := stochasticIntegralBrownian_indTerm_zero W ℱ hℱ ht hm hp hq hmI0 hpI0 hqI0
  have hall : ∀ᵐ ω ∂P, ∀ i : ι,
      stochasticIntegralBrownian W ℱ hℱ (cutTerm τ H i.1 t) (hmF i) (hpF i) (hqF i) t ω
        = hitInd τ i.1 ω * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
          - stochasticIntegralBrownian W ℱ hℱ H hm hp hq i.1 ω) :=
    MeasureTheory.ae_all_iff.mpr hterm
  filter_upwards [hstep, hsub, hI0, hSum, hall] with ω h1 h3 h4 h5 h6
  have h2 := congrFun hcongr ω
  rw [← h1, h2, h3, h4, h5, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => h6 i,
    Finset.sum_coe_sort J fun c => hitInd τ c ω
      * (stochasticIntegralBrownian W ℱ hℱ H hm hp hq t ω
        - stochasticIntegralBrownian W ℱ hℱ H hm hp hq c ω)]

end Identity

end Stopped

end LevyStochCalc.Brownian.Ito
