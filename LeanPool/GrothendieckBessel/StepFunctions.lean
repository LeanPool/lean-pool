/-
Copyright (c) 2026 Lukas Liehr, Mitchell A. Taylor, Peiyang Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Liehr, Mitchell A. Taylor, Peiyang Yu
-/
module

public import LeanPool.GrothendieckBessel.Definitions

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Bounded step-function realizations of finite Gram matrices
Adapted for Lean Pool from the Apache-2.0 upstream formalization, with module-system,
Mathlib API, and compilation changes.
-/

@[expose] public section

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace OlevskiiGram

private def partialWeight {m : ℕ} (p : Fin m → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, if h : i < m then p ⟨i, h⟩ else 0

private lemma partialWeight_succ {m : ℕ} (p : Fin m → ℝ) {k : ℕ} (hk : k < m) :
    partialWeight p (k + 1) = partialWeight p k + p ⟨k, hk⟩ := by
  simp [partialWeight, Finset.sum_range_succ, hk]

private lemma partialWeight_nonneg {m : ℕ} (p : Fin m → ℝ) (hp : ∀ r, 0 ≤ p r) :
    ∀ k, 0 ≤ partialWeight p k := by
  intro k
  dsimp [partialWeight]
  exact Finset.sum_nonneg fun i _hi => by
    by_cases h : i < m
    · simpa [h] using hp ⟨i, h⟩
    · simp [h]

private lemma partialWeight_mono_succ {m : ℕ} (p : Fin m → ℝ) (hp : ∀ r, 0 ≤ p r) :
    ∀ k, partialWeight p k ≤ partialWeight p (k + 1) := by
  intro k
  by_cases hk : k < m
  · rw [partialWeight_succ p hk]
    exact le_add_of_nonneg_right (hp ⟨k, hk⟩)
  · have hk' : ¬ k < m := hk
    rw [partialWeight]
    rw [partialWeight]
    simp [Finset.sum_range_succ, hk']

private lemma partialWeight_mono {m : ℕ} (p : Fin m → ℝ) (hp : ∀ r, 0 ≤ p r) :
    Monotone (partialWeight p) := by
  intro a b hab
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b _ ih => exact ih.trans (partialWeight_mono_succ p hp b)

private lemma partialWeight_total {m : ℕ} (p : Fin m → ℝ) :
    partialWeight p m = ∑ r, p r := by
  rw [partialWeight]
  rw [Finset.sum_fin_eq_sum_range]

private def stepInterval {m : ℕ} (p : Fin m → ℝ) (r : Fin m) : Set ℝ :=
  Set.Ioc (partialWeight p r.1) (partialWeight p (r.1 + 1))

private lemma measurableSet_stepInterval {m : ℕ} (p : Fin m → ℝ) (r : Fin m) :
    MeasurableSet (stepInterval p r) := by
  exact measurableSet_Ioc

private lemma stepInterval_measureReal {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ r, 0 ≤ p r) (r : Fin m) :
    volume.real (stepInterval p r) = p r := by
  have hle : partialWeight p r.1 ≤ partialWeight p (r.1 + 1) :=
    partialWeight_mono_succ p hp r.1
  rw [stepInterval, Real.volume_real_Ioc_of_le hle]
  rw [partialWeight_succ p r.2]
  ring

private lemma stepInterval_subset_Ioc {m : ℕ} (p : Fin m → ℝ)
    (hp : ∀ r, 0 ≤ p r) (hpsum : ∑ r, p r = 1) (r : Fin m) :
    stepInterval p r ⊆ Set.Ioc (0 : ℝ) 1 := by
  intro x hx
  rcases hx with ⟨hlx, hxu⟩
  constructor
  · exact lt_of_le_of_lt (partialWeight_nonneg p hp r.1) hlx
  · have hle_total : partialWeight p (r.1 + 1) ≤ partialWeight p m :=
      partialWeight_mono p hp (Nat.succ_le_of_lt r.2)
    rw [partialWeight_total p, hpsum] at hle_total
    exact hxu.trans hle_total

private lemma disjoint_stepInterval {m : ℕ} (p : Fin m → ℝ) (hp : ∀ r, 0 ≤ p r)
    {r s : Fin m} (hrs : r ≠ s) :
    Disjoint (stepInterval p r) (stepInterval p s) := by
  rw [Set.disjoint_left]
  intro x hxr hxs
  have hval_ne : r.1 ≠ s.1 := by
    intro hval
    exact hrs (Fin.ext hval)
  rcases lt_or_gt_of_ne hval_ne with hlt | hgt
  · have hle_rs : r.1 + 1 ≤ s.1 := by omega
    have hmono : partialWeight p (r.1 + 1) ≤ partialWeight p s.1 :=
      partialWeight_mono p hp hle_rs
    rcases hxr with ⟨_, hxru⟩
    rcases hxs with ⟨hsl, _⟩
    linarith
  · have hle_sr : s.1 + 1 ≤ r.1 := by omega
    have hmono : partialWeight p (s.1 + 1) ≤ partialWeight p r.1 :=
      partialWeight_mono p hp hle_sr
    rcases hxs with ⟨_, hxsu⟩
    rcases hxr with ⟨hrl, _⟩
    linarith

private def finiteStep {m : ℕ} {n : Type*} (p : Fin m → ℝ) (ζ : Fin m → n → ℂ)
    (j : n) : ℝ → ℂ :=
  ∑ r, (stepInterval p r).indicator (fun _ : ℝ => ζ r j)

private lemma finiteStep_eq_of_mem {m : ℕ} {n : Type*}
    (p : Fin m → ℝ) (ζ : Fin m → n → ℂ) (hp : ∀ r, 0 ≤ p r)
    {r : Fin m} {t : ℝ} (hr : t ∈ stepInterval p r) (j : n) :
    finiteStep p ζ j t = ζ r j := by
  classical
  rw [finiteStep]
  simp only [Finset.sum_apply]
  rw [Finset.sum_eq_single (a := r)
    (f := fun s => (stepInterval p s).indicator (fun _ : ℝ => ζ s j) t)]
  · simp [Set.indicator_of_mem hr]
  · intro s _hs hsr
    have hnot : t ∉ stepInterval p s := by
      intro hts
      exact (Set.disjoint_left.mp (disjoint_stepInterval p hp hsr) hts hr)
    simp [Set.indicator_of_notMem hnot]
  · intro hrmem
    simp at hrmem

private lemma finiteStep_eq_zero_of_notMem {m : ℕ} {n : Type*}
    (p : Fin m → ℝ) (ζ : Fin m → n → ℂ) {t : ℝ}
    (hnot : ∀ r, t ∉ stepInterval p r) (j : n) :
    finiteStep p ζ j t = 0 := by
  rw [finiteStep]
  simp only [Finset.sum_apply]
  refine Finset.sum_eq_zero fun r _hr => ?_
  simp [Set.indicator_of_notMem (hnot r)]

private lemma finiteStep_norm_le {m : ℕ} {n : Type*}
    (p : Fin m → ℝ) (ζ : Fin m → n → ℂ)
    (hp : ∀ r, 0 ≤ p r) (hζ : ∀ r j, ‖ζ r j‖ ≤ 1) (j : n) (t : ℝ) :
    ‖finiteStep p ζ j t‖ ≤ 1 := by
  classical
  by_cases hhit : ∃ r, t ∈ stepInterval p r
  · rcases hhit with ⟨r, hr⟩
    rw [finiteStep_eq_of_mem p ζ hp hr j]
    exact hζ r j
  · have hnot : ∀ r, t ∉ stepInterval p r := by
      intro r htr
      exact hhit ⟨r, htr⟩
    rw [finiteStep_eq_zero_of_notMem p ζ hnot j]
    norm_num

private lemma finiteStep_LInfNormLe {m : ℕ} {n : Type*}
    (p : Fin m → ℝ) (ζ : Fin m → n → ℂ)
    (hp : ∀ r, 0 ≤ p r) (hζ : ∀ r j, ‖ζ r j‖ ≤ 1) (j : n) :
    LInfNormLe 1 (finiteStep p ζ j) := by
  unfold LInfNormLe
  exact eLpNormEssSup_le_of_ae_bound
    (ae_of_all _ fun t => finiteStep_norm_le p ζ hp hζ j t)

private lemma finiteStep_mul_star_eq {m : ℕ} {n : Type*}
    (p : Fin m → ℝ) (ζ : Fin m → n → ℂ) (hp : ∀ r, 0 ≤ p r) (j k : n) (t : ℝ) :
    finiteStep p ζ j t * star (finiteStep p ζ k t) =
      ∑ r, (stepInterval p r).indicator (fun _ : ℝ => ζ r j * star (ζ r k)) t := by
  classical
  by_cases hhit : ∃ r, t ∈ stepInterval p r
  · rcases hhit with ⟨r, hr⟩
    rw [finiteStep_eq_of_mem p ζ hp hr j, finiteStep_eq_of_mem p ζ hp hr k]
    rw [Finset.sum_eq_single (a := r)
      (f := fun s => (stepInterval p s).indicator
        (fun _ : ℝ => ζ s j * star (ζ s k)) t)]
    · simp [Set.indicator_of_mem hr]
    · intro s _hs hsr
      have hnot : t ∉ stepInterval p s := by
        intro hts
        exact (Set.disjoint_left.mp (disjoint_stepInterval p hp hsr) hts hr)
      simp [Set.indicator_of_notMem hnot]
    · intro hrmem
      simp at hrmem
  · have hnot : ∀ r, t ∉ stepInterval p r := by
      intro r htr
      exact hhit ⟨r, htr⟩
    rw [finiteStep_eq_zero_of_notMem p ζ hnot j, finiteStep_eq_zero_of_notMem p ζ hnot k]
    simp [hnot]

private lemma finiteStep_integral {m : ℕ} {n : Type*}
    (p : Fin m → ℝ) (ζ : Fin m → n → ℂ)
    (hp : ∀ r, 0 ≤ p r) (hpsum : ∑ r, p r = 1) (j k : n) :
    (∫ t in Set.Ioo (0 : ℝ) (1 : ℝ), finiteStep p ζ j t * star (finiteStep p ζ k t)) =
      ∑ r, (p r : ℂ) * ζ r j * star (ζ r k) := by
  classical
  rw [← MeasureTheory.integral_Ioc_eq_integral_Ioo' (μ := volume)
    (f := fun t => finiteStep p ζ j t * star (finiteStep p ζ k t))
    (x := (0 : ℝ)) (y := (1 : ℝ)) (by simp)]
  have hfun :
      (fun t => finiteStep p ζ j t * star (finiteStep p ζ k t)) =
        fun t => ∑ r, (stepInterval p r).indicator
          (fun _ : ℝ => ζ r j * star (ζ r k)) t := by
    funext t
    exact finiteStep_mul_star_eq p ζ hp j k t
  rw [hfun]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro r _hr
    rw [MeasureTheory.integral_indicator_const (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (e := ζ r j * star (ζ r k)) (s_meas := measurableSet_stepInterval p r)]
    rw [measureReal_restrict_apply (μ := volume) (s := Set.Ioc (0 : ℝ) 1)
      (t := stepInterval p r) (measurableSet_stepInterval p r)]
    rw [Set.inter_eq_left.mpr (stepInterval_subset_Ioc p hp hpsum r)]
    rw [stepInterval_measureReal p hp r]
    simp [mul_assoc]
  · intro r _hr
    exact (integrable_const (μ := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (ζ r j * star (ζ r k))).indicator (measurableSet_stepInterval p r)

/--
Realize a finite weighted complex Gram decomposition by piecewise constant
functions on `(0,1)`.
-/
theorem stepFunctionRealization
    {n : Type*}
    {m : ℕ}
    (p : Fin m → ℝ) (ζ : Fin m → n → ℂ) :
    (∀ r, 0 ≤ p r) →
    (∑ r, p r = 1) →
    (∀ r j, ‖ζ r j‖ ≤ 1) →
      ∃ f : n → ℝ → ℂ,
        (∀ j, LInfNormLe 1 (f j)) ∧
        ∀ j k,
          (∫ t in Set.Ioo (0 : ℝ) (1 : ℝ), f j t * star (f k t)) =
            ∑ r, (p r : ℂ) * ζ r j * star (ζ r k)
    := by
  intro hp hpsum hζ
  refine ⟨finiteStep p ζ, ?_, ?_⟩
  · intro j
    exact finiteStep_LInfNormLe p ζ hp hζ j
  · intro j k
    exact finiteStep_integral p ζ hp hpsum j k

/--
The same finite realization with the concrete measurability and everywhere
pointwise bound needed by the countable compactness construction.  The moment
identity is written on `[0,1]`; changing the endpoints does not change a
Lebesgue integral.
-/
theorem stepFunctionRealizationOnUnitInterval
    {n : Type*}
    {m : ℕ}
    (p : Fin m → ℝ) (ζ : Fin m → n → ℂ) :
    (∀ r, 0 ≤ p r) →
    (∑ r, p r = 1) →
    (∀ r j, ‖ζ r j‖ ≤ 1) →
      ∃ f : n → ℝ → ℂ,
        (∀ j, AEStronglyMeasurable (f j)
          (volume.restrict (Set.Icc (0 : ℝ) 1))) ∧
        (∀ j t, ‖f j t‖ ≤ 1) ∧
        ∀ j k,
          (∫ t in Set.Icc (0 : ℝ) (1 : ℝ), f j t * star (f k t)) =
            ∑ r, (p r : ℂ) * ζ r j * star (ζ r k) := by
  intro hp hpsum hζ
  refine ⟨finiteStep p ζ, ?_, ?_, ?_⟩
  · intro j
    have hstrong : StronglyMeasurable (finiteStep p ζ j) := by
      unfold finiteStep
      exact Finset.stronglyMeasurable_sum Finset.univ fun r _ =>
        (stronglyMeasurable_const :
          StronglyMeasurable (fun _ : ℝ => ζ r j)).indicator
            (measurableSet_stepInterval p r)
    exact hstrong.aestronglyMeasurable
  · intro j t
    exact finiteStep_norm_le p ζ hp hζ j t
  · intro j k
    rw [MeasureTheory.integral_Icc_eq_integral_Ioo]
    exact finiteStep_integral p ζ hp hpsum j k

end OlevskiiGram
