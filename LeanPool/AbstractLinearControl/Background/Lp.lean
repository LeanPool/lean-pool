/-
Copyright (c) 2026 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Complete
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
public import Mathlib.MeasureTheory.Function.UniformIntegrable
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.RegularityCompacts


/-!
# Inputs: the space `L^p(ℝ₊; U)`, concatenation, shifts and truncations

This file contains the measure-theoretic plumbing on inputs used throughout the
development. Nothing here is specific to control systems.

## Conventions

* `L^p(ℝ₊; U)` is Mathlib's `Lp U p muPlus`, where `muPlus` is Lebesgue measure
  restricted to `ℝ₊ = [0, ∞)`. Its elements are almost-everywhere classes;
  `⇑u : ℝ → U` is an (arbitrary) representative, whose values at negative times
  are irrelevant.
* The `τ`-concatenation `u ⋄_τ v` of the paper is `concat τ u v`, defined on raw
  functions `ℝ → U`. Statements about inputs are phrased as "`w` is an element of
  `L^p(ℝ₊; U)` whose representative is a.e. equal to `concat τ ⇑u ⇑v`".

## Main declarations

* `muPlus`, `concat`, `ALCS.concat_congr` : definitions, and independence of
  the concatenation from the chosen representatives.
* `ALCS.shiftLeft a u` : the input `s ↦ u (a + s)`; `ALCS.exists_shift` gives
  `u = u ⋄_a (shiftLeft a u)`, and `ALCS.tendsto_norm_shiftLeft_sub` is the
  continuity of translations in `L^p` for `p < ∞`.
* `ALCS.exists_delay` : the delayed input `0 ⋄_a u`, with the same norm bound.
* `ALCS.truncate τ u` : the input `u ⋄_τ 0`; `ALCS.tendsto_norm_truncate` says
  that `‖u‖_{L^p(0, τ)} → 0` as `τ → 0` for `p < ∞`.
* `ALCS.exists_concat` : for `p = ∞`, the concatenation of two inputs of norm
  at most `C` is an input of norm at most `C`.
-/

namespace AbstractLinearControl

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

variable {U : Type*}

/-- Lebesgue measure on `ℝ₊ = [0, ∞)`. -/
noncomputable abbrev muPlus : Measure ℝ := volume.restrict (Set.Ici 0)

/-- The `τ`-concatenation `u ⋄_τ v` of the paper: equal to `u s` for `s < τ` and to
`v (s - τ)` for `s ≥ τ` ("play `u` on `[0, τ)`, then play `v`"). -/
noncomputable def concat (τ : ℝ) (u v : ℝ → U) : ℝ → U :=
  fun s => if s < τ then u s else v (s - τ)

namespace ALCS

/-! ## Translations of the half-line -/

/-- `s ↦ a + s` sends `ℝ₊` to `[a, ∞)`, preserving Lebesgue measure. -/
theorem measurePreserving_shift (a : ℝ) :
    MeasurePreserving (fun s => a + s) muPlus (volume.restrict (Set.Ici a)) := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) a).restrict_preimage
    (measurableSet_Ici : MeasurableSet (Set.Ici a))
  rwa [Set.preimage_const_add_Ici, sub_self] at h

/-- `s ↦ -a + s` sends `[a, ∞)` to `ℝ₊`, preserving Lebesgue measure. -/
theorem measurePreserving_unshift (a : ℝ) :
    MeasurePreserving (fun s => -a + s) (volume.restrict (Set.Ici a)) muPlus := by
  have h := (measurePreserving_add_left (volume : Measure ℝ) (-a)).restrict_preimage
    (measurableSet_Ici : MeasurableSet (Set.Ici (0 : ℝ)))
  rwa [Set.preimage_const_add_Ici, zero_sub, neg_neg] at h

/-! ## Concatenation -/

/-- The concatenation does not depend on the chosen representatives. For the second
argument, the null set has to be transported by a translation. -/
lemma concat_congr {f f' g g' : ℝ → U} (a : ℝ)
    (hf : f =ᵐ[muPlus] f') (hg : g =ᵐ[muPlus] g') :
    concat a f g =ᵐ[muPlus] concat a f' g' := by
  have hg₁ := (measurePreserving_unshift a).quasiMeasurePreserving.ae hg
  have hg₂ := (ae_restrict_iff'
    (measurableSet_Ici : MeasurableSet (Set.Ici a))).1 hg₁
  filter_upwards [hf, ae_restrict_of_ae hg₂] with t hft hgt
  by_cases ht : t < a
  · simp [concat, ht, hft]
  · simpa only [concat, ite_eq_right ht, sub_eq_neg_add] using
      hgt (Set.mem_Ici.2 (not_lt.1 ht))

variable [NormedAddCommGroup U]

lemma concat_stronglyMeasurable {f g : ℝ → U}
    (hf : StronglyMeasurable f) (hg : StronglyMeasurable g) (a : ℝ) :
    StronglyMeasurable (concat a f g) :=
  StronglyMeasurable.ite measurableSet_Iio hf
    (hg.comp_measurable (measurable_id.sub_const a))

/-! ## Extension by zero to the whole line -/

/-- Extension by zero to `ℝ` of a function on `ℝ₊`. -/
noncomputable def zeroExt (f : ℝ → U) : ℝ → U := (Set.Ici (0 : ℝ)).indicator f

lemma zeroExt_of_nonneg (f : ℝ → U) {s : ℝ} (hs : 0 ≤ s) : zeroExt f s = f s :=
  Set.indicator_of_mem (Set.mem_Ici.2 hs) f

lemma zeroExt_of_neg (f : ℝ → U) {s : ℝ} (hs : s < 0) : zeroExt f s = 0 :=
  Set.indicator_of_notMem (fun h => (not_le.2 hs) (Set.mem_Ici.1 h)) f

section General

variable {p : ℝ≥0∞}

lemma memLp_zeroExt (u : Lp U p muPlus) : MemLp (zeroExt ⇑u) p volume :=
  (memLp_indicator_iff_restrict measurableSet_Ici).2 (Lp.memLp u)

lemma eLpNorm_zeroExt (u : Lp U p muPlus) :
    eLpNorm (zeroExt ⇑u) p volume = eLpNorm (⇑u) p muPlus :=
  eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_Ici

/-- If `φ` preserves Lebesgue measure on `ℝ`, then `‖(zeroExt u) ∘ φ‖_{L^p(ℝ₊)} ≤ ‖u‖`. -/
lemma eLpNorm_zeroExt_comp_le (u : Lp U p muPlus) {φ : ℝ → ℝ}
    (hφ : MeasurePreserving φ volume volume) :
    eLpNorm (zeroExt ⇑u ∘ φ) p muPlus ≤ eLpNorm (⇑u) p muPlus :=
  calc eLpNorm (zeroExt ⇑u ∘ φ) p muPlus
      ≤ eLpNorm (zeroExt ⇑u ∘ φ) p volume := eLpNorm_mono_measure _ Measure.restrict_le_self
    _ = eLpNorm (zeroExt ⇑u) p volume :=
        eLpNorm_comp_measurePreserving (memLp_zeroExt u).aestronglyMeasurable hφ
    _ = eLpNorm (⇑u) p muPlus := eLpNorm_zeroExt u

lemma memLp_zeroExt_comp (u : Lp U p muPlus) {φ : ℝ → ℝ}
    (hφ : MeasurePreserving φ volume volume) : MemLp (zeroExt ⇑u ∘ φ) p muPlus :=
  ((memLp_zeroExt u).comp_measurePreserving hφ).mono_measure Measure.restrict_le_self

/-- An element of `L^p` defined from a raw function has norm at most `‖u‖` as soon as
the `eLpNorm` of the raw function is at most that of `u`. -/
lemma norm_toLp_le_of_eLpNorm_le {f : ℝ → U} (hf : MemLp f p muPlus) (u : Lp U p muPlus)
    (h : eLpNorm f p muPlus ≤ eLpNorm (⇑u) p muPlus) : ‖hf.toLp f‖ ≤ ‖u‖ := by
  rw [Lp.norm_toLp, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top u) h

/-! ## Left shifts `u ↦ u (a + ·)` -/

/-- The left shift `s ↦ u (a + s)` of an input. (For `a < 0`, the input is first
extended by zero to negative times.) -/
noncomputable def shiftLeft (a : ℝ) (u : Lp U p muPlus) : Lp U p muPlus :=
  (memLp_zeroExt_comp u (measurePreserving_add_left volume a)).toLp
    (zeroExt ⇑u ∘ fun s => a + s)

lemma shiftLeft_ae (a : ℝ) (u : Lp U p muPlus) :
    ⇑(shiftLeft a u) =ᵐ[muPlus] (zeroExt ⇑u ∘ fun s => a + s) :=
  (memLp_zeroExt_comp u (measurePreserving_add_left volume a)).coeFn_toLp

lemma norm_shiftLeft_le (a : ℝ) (u : Lp U p muPlus) : ‖shiftLeft a u‖ ≤ ‖u‖ :=
  norm_toLp_le_of_eLpNorm_le _ u
    (eLpNorm_zeroExt_comp_le u (measurePreserving_add_left volume a))

/-- For `a ≥ 0`, `u = u ⋄_a (shiftLeft a u)`. -/
lemma concat_shiftLeft (a : ℝ) (ha : 0 ≤ a) (u : Lp U p muPlus) :
    ⇑u =ᵐ[muPlus] concat a ⇑u ⇑(shiftLeft a u) := by
  -- pointwise, `u = u ⋄_a (zeroExt u ∘ (a + ·))`
  have hraw : (⇑u : ℝ → U) = concat a ⇑u (zeroExt ⇑u ∘ fun s => a + s) := by
    funext s
    by_cases hs : s < a
    · simp only [concat, ite_eq_left hs]
    · have hs' : 0 ≤ s := le_trans ha (not_lt.1 hs)
      have e : a + (s - a) = s := by ring
      simp only [concat, ite_eq_right hs, Function.comp_apply, e, zeroExt_of_nonneg (⇑u) hs']
  exact (Filter.EventuallyEq.of_eq hraw).trans
    (concat_congr a (Filter.EventuallyEq.refl _ _) (shiftLeft_ae a u)).symm

/-- Shifted input (used with `τ := a` in the composition property):
for `a ≥ 0`, `u₁ := u (a + ·)` satisfies `‖u₁‖ ≤ ‖u‖` and `u = u ⋄_a u₁`. -/
theorem exists_shift (a : ℝ) (ha : 0 ≤ a) (u : Lp U p muPlus) :
    ∃ u₁ : Lp U p muPlus, ‖u₁‖ ≤ ‖u‖ ∧ ⇑u =ᵐ[muPlus] concat a ⇑u ⇑u₁ :=
  ⟨shiftLeft a u, norm_shiftLeft_le a u, concat_shiftLeft a ha u⟩

/-! ## Delays `u ↦ 0 ⋄_a u` -/

/-- Delayed input: the input `0 ⋄_a u` (zero on `[0, a)`, then `u`)
belongs to `L^p(ℝ₊; U)`, with norm at most `‖u‖`. -/
theorem exists_delay (a : ℝ) (u : Lp U p muPlus) :
    ∃ w : Lp U p muPlus, ‖w‖ ≤ ‖u‖ ∧
      ⇑w =ᵐ[muPlus] concat a ⇑(0 : Lp U p muPlus) ⇑u := by
  have hφ : MeasurePreserving (fun s : ℝ => -a + s) volume volume :=
    measurePreserving_add_left volume (-a)
  refine ⟨(memLp_zeroExt_comp u hφ).toLp _,
    norm_toLp_le_of_eLpNorm_le _ u (eLpNorm_zeroExt_comp_le u hφ), ?_⟩
  -- pointwise, `zeroExt u (s - a) = (0 ⋄_a u) s`
  have hraw : (zeroExt ⇑u ∘ fun s => -a + s) = concat a (fun _ => (0 : U)) ⇑u := by
    funext s
    by_cases hsa : s < a
    · simp only [Function.comp_apply, zeroExt_of_neg (⇑u) (show -a + s < 0 by linarith),
        concat, ite_eq_left hsa]
    · simp only [Function.comp_apply, concat, ite_eq_right hsa, neg_add_eq_sub,
        zeroExt_of_nonneg (⇑u) (show 0 ≤ s - a by linarith [not_lt.1 hsa])]
  exact (memLp_zeroExt_comp u hφ).coeFn_toLp.trans
    ((Filter.EventuallyEq.of_eq hraw).trans (concat_congr a (Lp.coeFn_zero U p muPlus).symm
      (Filter.EventuallyEq.refl _ _)))

/-! ## Truncations `u ↦ u ⋄_τ 0` -/

/-- The truncated input `u ⋄_τ 0`: equal to `u` on `[0, τ)` and to zero afterwards. -/
noncomputable def truncate (τ : ℝ) (u : Lp U p muPlus) : Lp U p muPlus :=
  ((Lp.memLp u).indicator measurableSet_Iio).toLp ((Set.Iio τ).indicator ⇑u)

lemma concat_truncate (τ : ℝ) (u : Lp U p muPlus) :
    ⇑(truncate τ u) =ᵐ[muPlus] concat τ ⇑u ⇑(0 : Lp U p muPlus) := by
  have hraw : (Set.Iio τ).indicator ⇑u = concat τ ⇑u (fun _ => (0 : U)) := by
    funext s
    by_cases hs : s < τ
    · simp only [Set.indicator_of_mem (Set.mem_Iio.2 hs), concat, ite_eq_left hs]
    · simp only [Set.indicator_of_notMem (fun h => hs (Set.mem_Iio.1 h)), concat, ite_eq_right hs]
  exact ((Lp.memLp u).indicator measurableSet_Iio).coeFn_toLp.trans
    ((Filter.EventuallyEq.of_eq hraw).trans
      (concat_congr τ (Filter.EventuallyEq.refl _ _) (Lp.coeFn_zero U p muPlus).symm))

lemma muPlus_Iio (τ : ℝ) : muPlus (Set.Iio τ) = ENNReal.ofReal τ := by
  rw [Measure.restrict_apply measurableSet_Iio, Set.inter_comm, Set.Ici_inter_Iio,
    Real.volume_Ico, sub_zero]

/-- For `p < ∞`, `‖u‖_{L^p(0, τ)} → 0` as `τ → 0`. -/
theorem tendsto_norm_truncate [Fact (1 ≤ p)] (hp : p ≠ ∞) (u : Lp U p muPlus) :
    Tendsto (fun τ => ‖truncate τ u‖) (𝓝 0) (𝓝 0) := by
  -- first in `ℝ≥0∞`, using the absolute continuity of the `L^p` norm
  have hmeas : Tendsto (fun τ : ℝ => ENNReal.ofReal τ) (𝓝 0) (𝓝 0) :=
    ENNReal.continuous_ofReal.tendsto' 0 0 ENNReal.ofReal_zero
  have hlim : Tendsto (fun τ => eLpNorm ((Set.Iio τ).indicator ⇑u) p muPlus) (𝓝 0) (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ := (Lp.memLp u).eLpNorm_indicator_le Fact.out hp hε
    filter_upwards [hmeas.eventually (eventually_lt_nhds hδ)] with τ hτ
    exact hsmall _ measurableSet_Iio (by rw [muPlus_Iio]; exact hτ.le)
  -- then take real parts
  have hreal := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim
  simpa only [truncate, Lp.norm_toLp, Function.comp_def, ENNReal.toReal_zero] using hreal

/-! ## Continuity of left shifts for `p < ∞` -/

/-- The translations `s ↦ a + s`, as continuous maps depending continuously on `a`. -/
noncomputable def translation : C(ℝ, C(ℝ, ℝ)) :=
  ContinuousMap.curry ⟨fun q : ℝ × ℝ => q.1 + q.2, continuous_fst.add continuous_snd⟩

lemma translation_apply (a s : ℝ) : translation a s = a + s := by
  simp [translation]

lemma measurePreserving_translation (a : ℝ) :
    MeasurePreserving (translation a) volume volume := by
  have h : ⇑(translation a) = fun s => a + s := funext (translation_apply a)
  rw [h]
  exact measurePreserving_add_left volume a

/-- The zero extension of `u`, as an element of `L^p(ℝ)`. -/
noncomputable def zeroExtLp (u : Lp U p muPlus) : Lp U p (volume : Measure ℝ) :=
  (memLp_zeroExt u).toLp (zeroExt ⇑u)

/-- The zero extension of `u`, translated by `a`, as an element of `L^p(ℝ)`. -/
noncomputable def translateLp (u : Lp U p muPlus) (a : ℝ) : Lp U p (volume : Measure ℝ) :=
  Lp.compMeasurePreserving (translation a) (measurePreserving_translation a) (zeroExtLp u)

lemma translateLp_ae (u : Lp U p muPlus) (a : ℝ) :
    ⇑(translateLp u a) =ᵐ[volume] zeroExt ⇑u ∘ translation a :=
  (Lp.coeFn_compMeasurePreserving (zeroExtLp u) (measurePreserving_translation a)).trans
    ((measurePreserving_translation a).quasiMeasurePreserving.ae_eq_comp
      (memLp_zeroExt u).coeFn_toLp)

/-- `‖u (a + ·) - u‖_{L^p(ℝ₊)} ≤ ‖Z (a + ·) - Z‖_{L^p(ℝ)}`, where `Z` is the zero
extension of `u`. -/
lemma norm_shiftLeft_sub_le (a : ℝ) (u : Lp U p muPlus) :
    ‖shiftLeft a u - u‖ ≤ ‖translateLp u a - translateLp u 0‖ := by
  have hae : ⇑(shiftLeft a u - u) =ᵐ[muPlus] ⇑(translateLp u a - translateLp u 0) := by
    have a1 := Lp.coeFn_sub (shiftLeft a u) u
    have a2 := shiftLeft_ae a u
    have a3 := ae_restrict_of_ae (s := Set.Ici (0 : ℝ))
      (Lp.coeFn_sub (translateLp u a) (translateLp u 0))
    have a4 := ae_restrict_of_ae (s := Set.Ici (0 : ℝ)) (translateLp_ae u a)
    have a5 := ae_restrict_of_ae (s := Set.Ici (0 : ℝ)) (translateLp_ae u 0)
    have a6 : ∀ᵐ s ∂muPlus, s ∈ Set.Ici (0 : ℝ) := ae_restrict_mem measurableSet_Ici
    filter_upwards [a1, a2, a3, a4, a5, a6] with s e1 e2 e3 e4 e5 hs
    rw [e1, Pi.sub_apply, e2, e3, Pi.sub_apply, e4, e5]
    simp only [Function.comp_apply, translation_apply, zero_add,
      zeroExt_of_nonneg (⇑u) (Set.mem_Ici.1 hs)]
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae hae]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _)
    (eLpNorm_mono_measure _ Measure.restrict_le_self)

/-- Continuity of translations in `L^p(ℝ₊; U)` for `p < ∞`: `u (a + ·) → u` as `a → 0`. -/
theorem tendsto_norm_shiftLeft_sub [Fact (1 ≤ p)] (hp : p ≠ ∞) (u : Lp U p muPlus) :
    Tendsto (fun a => ‖shiftLeft a u - u‖) (𝓝 0) (𝓝 0) := by
  -- continuity of translations in `L^p(ℝ)` (Mathlib)
  have hlim : Tendsto (fun a => translateLp u a) (𝓝 0) (𝓝 (translateLp u 0)) := by
    unfold translateLp
    exact Filter.Tendsto.compMeasurePreservingLp tendsto_const_nhds
      (translation.continuous.tendsto 0) measurePreserving_translation
      (measurePreserving_translation 0) hp
  exact squeeze_zero (fun a => norm_nonneg _) (fun a => norm_shiftLeft_sub_le a u)
    (tendsto_iff_norm_sub_tendsto_zero.1 hlim)

end General

/-! ## Inputs in `L^∞(ℝ₊; U)` -/

section Infinity

/-- A pointwise bound gives membership in `L^∞`, without a finite-measure assumption. -/
lemma memLp_of_bound {f : ℝ → U} (hf : StronglyMeasurable f)
    {C : ℝ} (hb : ∀ t, ‖f t‖ ≤ C) : MemLp f ∞ muPlus :=
  memLp_top_of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hb)

/-- The `L^∞` norm is bounded by any nonnegative a.e. bound. -/
lemma lp_norm_le {u : Lp U ∞ muPlus} {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ᵐ t ∂muPlus, ‖u t‖ ≤ C) : ‖u‖ ≤ C := by
  have htop : eLpNorm (⇑u) ∞ muPlus = eLpNormEssSup (⇑u) muPlus :=
    eLpNorm_exponent_top (Lp.aestronglyMeasurable u)
  rw [Lp.norm_def, htop]
  calc
    (eLpNormEssSup (⇑u) muPlus).toReal ≤ (ENNReal.ofReal C).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top (eLpNormEssSup_le_of_ae_bound hb)
    _ = C := ENNReal.toReal_ofReal hC

/-- The representative of an `L^∞` class obeys its norm bound a.e. -/
lemma ae_norm_le (u : Lp U ∞ muPlus) : ∀ᵐ t ∂muPlus, ‖u t‖ ≤ ‖u‖ := by
  have htop : eLpNorm (⇑u) ∞ muPlus = eLpNormEssSup (⇑u) muPlus :=
    eLpNorm_exponent_top (Lp.aestronglyMeasurable u)
  have hfinite : eLpNormEssSup (⇑u) muPlus ≠ ∞ := by
    rw [← htop]
    exact Lp.eLpNorm_ne_top u
  filter_upwards [enorm_ae_le_eLpNormEssSup (⇑u) muPlus] with t ht
  have ht' := ENNReal.toReal_mono hfinite ht
  simpa only [Lp.norm_def, htop, toReal_enorm] using ht'

/-- An everywhere bounded, strongly measurable representative. The representative is
only modified where it exceeds `C`. -/
lemma exists_bounded_rep (u : Lp U ∞ muPlus) {C : ℝ}
    (hC : 0 ≤ C) (hu : ‖u‖ ≤ C) :
    ∃ f : ℝ → U, StronglyMeasurable f ∧ (∀ t, ‖f t‖ ≤ C) ∧ ⇑u =ᵐ[muPlus] f := by
  let f : ℝ → U := fun t => if ‖u t‖ ≤ C then u t else 0
  have hf : StronglyMeasurable f :=
    StronglyMeasurable.ite
      ((Lp.stronglyMeasurable u).norm.measurableSet_le stronglyMeasurable_const)
      (Lp.stronglyMeasurable u) stronglyMeasurable_const
  refine ⟨f, hf, ?_, ?_⟩
  · intro t
    by_cases ht : ‖u t‖ ≤ C
    · simp [f, ht]
    · simpa [f, ht] using hC
  · filter_upwards [ae_norm_le u] with t ht
    simp [f, ht.trans hu]

/-- For `p = ∞`, concatenation preserves a common norm bound: if `‖u‖, ‖v‖ ≤ C`, then
`u ⋄_a v` is an input of norm at most `C`. -/
lemma exists_concat (a : ℝ) (u v : Lp U ∞ muPlus) {C : ℝ}
    (hC : 0 ≤ C) (hu : ‖u‖ ≤ C) (hv : ‖v‖ ≤ C) :
    ∃ w : Lp U ∞ muPlus, ‖w‖ ≤ C ∧ ⇑w =ᵐ[muPlus] concat a ⇑u ⇑v := by
  obtain ⟨f, hf, hfb, huf⟩ := exists_bounded_rep u hC hu
  obtain ⟨g, hg, hgb, hvg⟩ := exists_bounded_rep v hC hv
  have hb : ∀ t, ‖concat a f g t‖ ≤ C := by
    intro t
    by_cases ht : t < a
    · simpa [concat, ht] using hfb t
    · simpa [concat, ht] using hgb (t - a)
  have hm := memLp_of_bound (concat_stronglyMeasurable hf hg a) hb
  refine ⟨hm.toLp _, ?_, ?_⟩
  · apply lp_norm_le hC
    filter_upwards [hm.coeFn_toLp] with t ht
    rw [ht]
    exact hb t
  · exact hm.coeFn_toLp.trans (concat_congr a huf hvg).symm

/-- The `L^∞` class of a bounded raw function has the same bound. -/
lemma norm_toLp_le {f : ℝ → U} (hf : MemLp f ∞ muPlus)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ t, ‖f t‖ ≤ C) : ‖hf.toLp f‖ ≤ C := by
  apply lp_norm_le hC
  filter_upwards [hf.coeFn_toLp] with t ht
  rw [ht]
  exact hb t

end Infinity

/-- `‖(a + b) - (c + d)‖ ≤ ‖a - c‖ + ‖b‖ + ‖d‖` -/
lemma norm_three_terms_le {X : Type*} [NormedAddCommGroup X] (a b c d : X) :
    ‖a + b - (c + d)‖ ≤ ‖a - c‖ + ‖b‖ + ‖d‖ := by
  have key : a + b - (c + d) = (a - c + b) - d := by abel
  rw [key]
  have k1 := norm_sub_le (a - c + b) d
  have k2 := norm_add_le (a - c) b
  linarith

end ALCS

end

end AbstractLinearControl
