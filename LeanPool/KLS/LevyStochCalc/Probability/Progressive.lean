/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Progressively measurable real processes

`ProgressivelyMeasurable ℱ H` says that the process `H : Ω → ℝ → E`, viewed as a function of
`(ω, s)`, is `ℱ t ⊗ Borel`-measurable on the time window `s ≤ t`, for every `t`. This is
the progressive measurability of Mathlib's `IsStronglyProgressive`, phrased on `Ω × ℝ` by
truncating the time variable at `t`, which is the form in which the stochastic integrals of
this library consume it; `isStronglyProgressive` and `of_isStronglyProgressive` relate the
two.
-/

@[expose] public section

open MeasureTheory

namespace LevyStochCalc.Probability

variable {Ω E F : Type*} {mΩ : MeasurableSpace Ω}

section General

variable [TopologicalSpace E] [Zero E] [TopologicalSpace F] [Zero F]

/-- The process `H` is progressively measurable for `ℱ`: for every time `t`, the map
`(ω, s) ↦ H ω s` restricted to times `s ≤ t` (and `0` after `t`) is
`ℱ t ⊗ Borel`-measurable. -/
def ProgressivelyMeasurable (ℱ : Filtration ℝ mΩ) (H : Ω → ℝ → E) : Prop :=
  ∀ t : ℝ,
    @StronglyMeasurable (Ω × ℝ) E _ (@Prod.instMeasurableSpace Ω ℝ (ℱ t) inferInstance)
      fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2

namespace ProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

/-- A progressively measurable process is adapted. -/
theorem stronglyMeasurable_eval (h : ProgressivelyMeasurable ℱ H) (t : ℝ) :
    StronglyMeasurable[ℱ t] fun ω => H ω t := by
  let : MeasurableSpace Ω := ℱ t
  have := (h t).comp_measurable (measurable_prodMk_right (y := t))
  simpa [Function.comp_def] using this

/-- Composition with a continuous map fixing `0` preserves progressive measurability. -/
theorem _root_.Continuous.comp_progressivelyMeasurable {φ : E → F} (hφ : Continuous φ)
    (hφ0 : φ 0 = 0) (h : ProgressivelyMeasurable ℱ H) :
    ProgressivelyMeasurable ℱ fun ω s => φ (H ω s) := by
  intro t
  have : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => φ (H p.1 s)) p.2)
      = fun p : Ω × ℝ => φ ((Set.Iic t).indicator (H p.1) p.2) := by
    funext p
    exact congrFun (Set.indicator_comp_of_zero (f := H p.1) (s := Set.Iic t) hφ0) p.2
  rw [this]
  exact hφ.comp_stronglyMeasurable (h t)

/-- Progressive measurability is monotone in the filtration. -/
theorem mono {𝒢 : Filtration ℝ mΩ} (h : ProgressivelyMeasurable ℱ H)
    (hle : ∀ t, ℱ t ≤ 𝒢 t) : ProgressivelyMeasurable 𝒢 H := fun t =>
  (h t).mono (sup_le_sup (MeasurableSpace.comap_mono (hle t)) le_rfl)

/-- Freezing a progressively measurable process at a deterministic time keeps it progressively
measurable. -/
theorem minTime (h : ProgressivelyMeasurable ℱ H) (T : ℝ) :
    ProgressivelyMeasurable ℱ fun ω s => H ω (min s T) := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  have hmono : ℱ (min t T) ≤ ℱ t := ℱ.mono (min_le_left t T)
  have hG : StronglyMeasurable fun q : Ω × ℝ => (Set.Iic (min t T)).indicator (H q.1) q.2 :=
    (h (min t T)).mono (sup_le_sup (MeasurableSpace.comap_mono hmono) le_rfl)
  have he : Measurable fun q : Ω × ℝ => ((q.1 : Ω), min q.2 T) :=
    measurable_fst.prodMk (measurable_snd.min measurable_const)
  have hcomp := hG.comp_measurable he
  have hind := hcomp.indicator (s := Set.univ ×ˢ Set.Iic t)
    (MeasurableSet.univ.prod measurableSet_Iic)
  have heq : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => H p.1 (min s T)) p.2)
      = (Set.univ ×ˢ Set.Iic t).indicator
        ((fun q : Ω × ℝ => (Set.Iic (min t T)).indicator (H q.1) q.2)
          ∘ fun q : Ω × ℝ => ((q.1 : Ω), min q.2 T)) := by
    funext p
    by_cases hp : p.2 ≤ t
    · have hmin : min p.2 T ≤ min t T := min_le_min hp le_rfl
      simp [hp, hmin, Function.comp_def]
    · simp [hp, Function.comp_def]
  rw [heq]
  exact hind

/-- A progressively measurable process is strongly progressive in the sense of Mathlib. -/
theorem isStronglyProgressive (h : ProgressivelyMeasurable ℱ H) :
    IsStronglyProgressive ℱ fun s ω => H ω s := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  have he : Measurable fun q : Set.Iic t × Ω => (q.2, (q.1 : ℝ)) :=
    measurable_snd.prodMk (measurable_subtype_coe.comp measurable_fst)
  have := (h t).comp_measurable he
  have heq : (fun q : Set.Iic t × Ω => H q.2 q.1)
      = (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2) ∘ fun q : Set.Iic t × Ω =>
        (q.2, (q.1 : ℝ)) := by
    funext q
    exact (Set.indicator_of_mem q.1.2 _).symm
  rw [heq]
  exact this

/-- A strongly progressive process in the sense of Mathlib is progressively measurable. -/
theorem of_isStronglyProgressive (h : IsStronglyProgressive ℱ fun s ω => H ω s) :
    ProgressivelyMeasurable ℱ H := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  let e : Ω × ℝ → Set.Iic t × Ω := fun p => (⟨min p.2 t, Set.mem_Iic.mpr (min_le_right _ _)⟩, p.1)
  have he : Measurable e :=
    ((measurable_snd.min measurable_const).subtype_mk).prodMk measurable_fst
  have : (fun p : Ω × ℝ => (Set.Iic t).indicator (H p.1) p.2)
      = (Set.univ ×ˢ Set.Iic t).indicator
        ((fun q : Set.Iic t × Ω => H q.2 q.1) ∘ e) := by
    funext p
    by_cases hp : p.2 ≤ t
    · simp [e, hp]
    · simp [e, hp]
  rw [this]
  exact ((h t).comp_measurable he).indicator (MeasurableSet.univ.prod measurableSet_Iic)

end ProgressivelyMeasurable

end General

section Mul

variable [TopologicalSpace E] [MulZeroClass E] [ContinuousMul E] {ℱ : Filtration ℝ mΩ}

/-- The pointwise product of two progressively measurable processes is progressively
measurable. -/
theorem ProgressivelyMeasurable.comp_continuous {A : Ω → ℝ → ℝ} {φ : ℝ → ℝ}
    (hφ : Continuous φ) (hφ0 : φ 0 = 0) (hA : ProgressivelyMeasurable ℱ A) :
    ProgressivelyMeasurable ℱ fun ω s => φ (A ω s) := by
  intro t
  have heq : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => φ (A p.1 s)) p.2)
      = fun p : Ω × ℝ => φ ((Set.Iic t).indicator (A p.1) p.2) := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp, hφ0]
  rw [heq]
  exact hφ.comp_stronglyMeasurable (hA t)

theorem ProgressivelyMeasurable.mul {A B : Ω → ℝ → E} (hA : ProgressivelyMeasurable ℱ A)
    (hB : ProgressivelyMeasurable ℱ B) :
    ProgressivelyMeasurable ℱ fun ω s => A ω s * B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s * B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 * (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, zero_mul]
  rw [key]
  exact (hA t).mul (hB t)

end Mul

section Add

variable [NormedAddCommGroup E] {ℱ : Filtration ℝ mΩ}

/-- The pointwise sum of two progressively measurable processes is progressively measurable. -/
theorem ProgressivelyMeasurable.add {A B : Ω → ℝ → E} (hA : ProgressivelyMeasurable ℱ A)
    (hB : ProgressivelyMeasurable ℱ B) :
    ProgressivelyMeasurable ℱ fun ω s => A ω s + B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s + B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 + (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, add_zero]
  rw [key]
  exact (hA t).add (hB t)

/-- The pointwise difference of two progressively measurable processes is progressively
measurable. -/
theorem ProgressivelyMeasurable.sub {A B : Ω → ℝ → E} (hA : ProgressivelyMeasurable ℱ A)
    (hB : ProgressivelyMeasurable ℱ B) :
    ProgressivelyMeasurable ℱ fun ω s => A ω s - B ω s := by
  intro t
  have key : (fun p : Ω × ℝ => (Set.Iic t).indicator (fun s => A p.1 s - B p.1 s) p.2)
      = fun p : Ω × ℝ =>
        (Set.Iic t).indicator (A p.1) p.2 - (Set.Iic t).indicator (B p.1) p.2 := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · rw [Set.indicator_of_mem hp, Set.indicator_of_mem hp, Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, sub_zero]
  rw [key]
  exact (hA t).sub (hB t)

end Add

section Integral

variable [NormedAddCommGroup E] [NormedSpace ℝ E] {ℱ : Filtration ℝ mΩ} {H : Ω → ℝ → E}

/-- The integral of a progressively measurable process over a measurable set of times `≤ t`
is `ℱ t`-measurable. -/
theorem ProgressivelyMeasurable.stronglyMeasurable_setIntegral (h : ProgressivelyMeasurable ℱ H)
    {t : ℝ} {S : Set ℝ} (hS : MeasurableSet S) (hSt : S ⊆ Set.Iic t) (μ : Measure ℝ)
    [SFinite μ] : StronglyMeasurable[ℱ t] fun ω => ∫ s in S, H ω s ∂μ := by
  let : MeasurableSpace Ω := ℱ t
  have h1 : StronglyMeasurable fun ω => ∫ s in S, (Set.Iic t).indicator (H ω) s ∂μ :=
    (h t).integral_prod_right' (ν := μ.restrict S)
  have : (fun ω => ∫ s in S, H ω s ∂μ)
      = fun ω => ∫ s in S, (Set.Iic t).indicator (H ω) s ∂μ := by
    funext ω
    exact setIntegral_congr_fun hS fun s hs => (Set.indicator_of_mem (hSt hs) _).symm
  rw [this]
  exact h1

end Integral

section Marked

variable {E : Type*} [MeasurableSpace E] [TopologicalSpace F] [Zero F]

/-- A marked process `φ : Ω → ℝ → E → F` is progressively measurable for `ℱ` when, for every
time `t`, `(ω, s, e) ↦ φ ω s e` restricted to times `s ≤ t` (and `0` after `t`) is
`ℱ t ⊗ Borel ⊗ 𝓔`-measurable. -/
def MarkedProgressivelyMeasurable (ℱ : Filtration ℝ mΩ) (φ : Ω → ℝ → E → F) : Prop :=
  ∀ t : ℝ,
    @StronglyMeasurable (Ω × ℝ × E) F _
      (@Prod.instMeasurableSpace Ω (ℝ × E) (ℱ t) inferInstance)
      fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1

namespace MarkedProgressivelyMeasurable

variable {ℱ : Filtration ℝ mΩ} {φ : Ω → ℝ → E → F}

/-- Composition with a continuous map fixing `0` preserves progressive measurability. -/
theorem _root_.Continuous.comp_markedProgressivelyMeasurable {G : Type*} [TopologicalSpace G]
    [Zero G] {g : F → G} (hg : Continuous g) (hg0 : g 0 = 0)
    (h : MarkedProgressivelyMeasurable ℱ φ) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => g (φ ω s e) := by
  intro t
  have : (fun p : Ω × ℝ × E => (Set.Iic t).indicator (fun s => g (φ p.1 s p.2.2)) p.2.1)
      = fun p : Ω × ℝ × E => g ((Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1) := by
    funext p
    exact congrFun (Set.indicator_comp_of_zero (f := fun s => φ p.1 s p.2.2)
      (s := Set.Iic t) hg0) p.2.1
  rw [this]
  exact hg.comp_stronglyMeasurable (h t)

/-- Restricting the marks to a measurable set preserves progressive measurability. -/
theorem indicator_mark (h : MarkedProgressivelyMeasurable ℱ φ) {S : Set E}
    (hS : MeasurableSet S) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => S.indicator (fun _ => φ ω s e) e := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  have : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => S.indicator (fun _ => φ p.1 s p.2.2) p.2.2) p.2.1)
      = {p : Ω × ℝ × E | p.2.2 ∈ S}.indicator
        (fun p => (Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1) := by
    funext p
    by_cases hp : p.2.2 ∈ S
    · simp [hp]
    · simp [hp]
  rw [this]
  exact (h t).indicator (measurable_snd.snd hS)

/-- Restricting the times to a measurable set preserves progressive measurability. -/
theorem indicator_time (h : MarkedProgressivelyMeasurable ℱ φ) {S : Set ℝ}
    (hS : MeasurableSet S) :
    MarkedProgressivelyMeasurable ℱ fun ω s e => S.indicator (fun _ => φ ω s e) s := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  have hrw : (fun p : Ω × ℝ × E =>
        (Set.Iic t).indicator (fun s => S.indicator (fun _ => φ p.1 s p.2.2) s) p.2.1)
      = {p : Ω × ℝ × E | p.2.1 ∈ S}.indicator
        (fun p => (Set.Iic t).indicator (fun s => φ p.1 s p.2.2) p.2.1) := by
    funext p
    by_cases ht : p.2.1 ∈ Set.Iic t <;> by_cases hp : p.2.1 ∈ S <;> simp [ht, hp]
  rw [hrw]
  exact (h t).indicator (measurable_snd.fst hS)

end MarkedProgressivelyMeasurable

end Marked

section MarkedIntegral

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {ℱ : Filtration ℝ mΩ} {φ : Ω → ℝ → E → F}

/-- The integral over a measurable set of times `≤ t` of a progressively measurable marked
process is `ℱ t ⊗ 𝓔`-measurable in `(ω, e)`. -/
theorem MarkedProgressivelyMeasurable.stronglyMeasurable_setIntegral_prod
    (h : MarkedProgressivelyMeasurable ℱ φ) {t : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hSt : S ⊆ Set.Iic t) (μ : Measure ℝ) [SFinite μ] :
    @StronglyMeasurable (Ω × E) F _ (@Prod.instMeasurableSpace Ω E (ℱ t) inferInstance)
      fun q : Ω × E => ∫ s in S, φ q.1 s q.2 ∂μ := by
  let : MeasurableSpace Ω := ℱ t
  have hr : Measurable fun r : (Ω × E) × ℝ => (r.1.1, r.2, r.1.2) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.prodMk (measurable_snd.comp measurable_fst))
  have h1 : StronglyMeasurable fun q : Ω × E =>
      ∫ s in S, (Set.Iic t).indicator (fun s => φ q.1 s q.2) s ∂μ :=
    ((h t).comp_measurable hr).integral_prod_right' (ν := μ.restrict S)
  have : (fun q : Ω × E => ∫ s in S, φ q.1 s q.2 ∂μ)
      = fun q : Ω × E => ∫ s in S, (Set.Iic t).indicator (fun s => φ q.1 s q.2) s ∂μ := by
    funext q
    exact setIntegral_congr_fun hS fun s hs =>
      (Set.indicator_of_mem (hSt hs) (fun s => φ q.1 s q.2)).symm
  rw [this]
  exact h1

/-- The integral over a measurable set of times `≤ t` and over the marks of a progressively
measurable marked process is `ℱ t`-measurable. -/
theorem MarkedProgressivelyMeasurable.stronglyMeasurable_setIntegral_integral
    (h : MarkedProgressivelyMeasurable ℱ φ) {t : ℝ} {S : Set ℝ} (hS : MeasurableSet S)
    (hSt : S ⊆ Set.Iic t) (μ : Measure ℝ) [SFinite μ] (ν : Measure E) [SFinite ν] :
    StronglyMeasurable[ℱ t] fun ω => ∫ s in S, ∫ e, φ ω s e ∂ν ∂μ := by
  let : MeasurableSpace Ω := ℱ t
  have h1 : StronglyMeasurable fun r : (Ω × ℝ) × E =>
      (Set.Iic t).indicator (fun s => φ r.1.1 s r.2) r.1.2 :=
    (h t).comp_measurable MeasurableEquiv.prodAssoc.measurable
  have h2 : StronglyMeasurable fun ω =>
      ∫ s in S, ∫ e, (Set.Iic t).indicator (fun s => φ ω s e) s ∂ν ∂μ :=
    (h1.integral_prod_right' (ν := ν)).integral_prod_right' (ν := μ.restrict S)
  have : (fun ω => ∫ s in S, ∫ e, φ ω s e ∂ν ∂μ)
      = fun ω => ∫ s in S, ∫ e, (Set.Iic t).indicator (fun s => φ ω s e) s ∂ν ∂μ := by
    funext ω
    refine setIntegral_congr_fun hS fun s hs => ?_
    simp only [Set.indicator_of_mem (hSt hs)]
  rw [this]
  exact h2

end MarkedIntegral

/-! ### Countable suprema of real progressively measurable processes -/

section RealLimsup

variable {ℱ : Filtration ℝ mΩ}

/-- A pointwise `limsup` along `atTop` of countably many progressively measurable real processes
is progressively measurable. -/
theorem ProgressivelyMeasurable.limsup {H : ℕ → Ω → ℝ → ℝ}
    (h : ∀ k, ProgressivelyMeasurable ℱ (H k)) :
    ProgressivelyMeasurable ℱ fun ω s => Filter.limsup (fun k => H k ω s) Filter.atTop := by
  intro t
  let : MeasurableSpace Ω := ℱ t
  have hind : (fun p : Ω × ℝ =>
        (Set.Iic t).indicator (fun s => Filter.limsup (fun k => H k p.1 s) Filter.atTop) p.2)
      = fun p : Ω × ℝ =>
        Filter.limsup (fun k => (Set.Iic t).indicator (H k p.1) p.2) Filter.atTop := by
    funext p
    by_cases hp : p.2 ∈ Set.Iic t
    · simp only [Set.indicator_of_mem hp]
    · simp only [Set.indicator_of_notMem hp, Filter.limsup_const]
  rw [hind]
  refine stronglyMeasurable_iff_measurable.mpr (Measurable.limsup fun k => ?_)
  exact (h k t).measurable

end RealLimsup

end LevyStochCalc.Probability
