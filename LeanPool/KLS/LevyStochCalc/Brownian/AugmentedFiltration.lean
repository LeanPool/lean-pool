/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.Filtered
public import LeanPool.KLS.LevyStochCalc.Probability.Augmentation

/-!
# The augmented Brownian filtration

Augmenting each `ℱ t` by the null sets — and freezing the filtration before time `0` — keeps
`W` a Brownian motion for it: adaptedness only grows, and independence survives because an
augmented set differs from a set of the original σ-algebra by a null set. The result is a
filtration satisfying the usual conditions, which is what a continuous adapted version of an
Itô process needs.

## Main statements

* `LevyStochCalc.Probability.indep_aug` — independence survives augmentation.
* `LevyStochCalc.Brownian.augFiltration` — the `0`-clamped augmented filtration.
* `LevyStochCalc.Brownian.isBrownianFiltration_augFiltration` — it is a Brownian filtration.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LevyStochCalc.Probability

/-- **Independence survives augmentation by the null sets.** -/
theorem indep_aug {Ω : Type*} {mΩ m 𝒩 : MeasurableSpace Ω} (μ : @Measure Ω mΩ)
    (h : @Indep Ω m 𝒩 mΩ μ) : @Indep Ω (aug m mΩ μ) 𝒩 mΩ μ := by
  rw [Indep_iff] at h ⊢
  rintro A C ⟨-, B, hB, hAB⟩ hC
  have hae : A =ᵐ[μ] B := MeasureTheory.measure_symmDiff_eq_zero_iff.mp hAB
  have h1 : μ A = μ B := MeasureTheory.measure_congr hae
  have h2 : μ (A ∩ C) = μ (B ∩ C) :=
    MeasureTheory.measure_congr (hae.inter (Filter.EventuallyEq.refl _ _))
  rw [h1, h2]
  exact h B C hB hC

end LevyStochCalc.Probability

namespace LevyStochCalc.Brownian

open LevyStochCalc.Probability

universe u

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- The filtration obtained by freezing `ℱ` before time `0` and augmenting each σ-algebra by
the `μ`-null sets. -/
def augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
    Filtration ℝ ‹MeasurableSpace Ω› where
  seq t := aug (ℱ (max t 0)) ‹MeasurableSpace Ω› μ
  mono' _ _ hst := aug_mono (ℱ.mono (max_le_max hst le_rfl))
  le' _ := aug_le

theorem le_augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) (t : ℝ) :
    ℱ t ≤ augFiltration ℱ μ t :=
  le_trans (ℱ.mono (le_max_left t 0)) (le_aug (ℱ.le _))

theorem augFiltration_of_nonpos (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω)
    {t : ℝ} (ht : t ≤ 0) : augFiltration ℱ μ t = augFiltration ℱ μ 0 := by
  change aug (ℱ (max t 0)) ‹MeasurableSpace Ω› μ = aug (ℱ (max 0 0)) ‹MeasurableSpace Ω› μ
  rw [max_eq_right ht, max_self]

theorem measurableSet_augFiltration_of_null (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    (μ : Measure Ω) {s : Set Ω} (hs : MeasurableSet s) (h0 : μ s = 0) :
    MeasurableSet[augFiltration ℱ μ 0] s :=
  measurableSet_aug_of_null hs h0

/-- **The `0`-clamped augmented filtration is a Brownian filtration.** -/
theorem isBrownianFiltration_augFiltration {W : BrownianMotion P}
    {ℱ : Filtration ℝ ‹MeasurableSpace Ω›} (h : IsBrownianFiltration W ℱ) :
    IsBrownianFiltration W (augFiltration ℱ P) where
  measurable t := fun A hA => le_augFiltration ℱ P t _ (h.measurable t hA)
  indep_future s hs := by
    have hfeq : (augFiltration ℱ P) s = aug (ℱ s) ‹MeasurableSpace Ω› P := by
      change aug (ℱ (max s 0)) ‹MeasurableSpace Ω› P = aug (ℱ s) ‹MeasurableSpace Ω› P
      rw [max_eq_left hs]
    rw [hfeq]
    exact indep_aug P (h.indep_future hs)


/-- Augmenting a right-continuous filtration keeps it right-continuous. -/
theorem rightCont_augFiltration_le (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
    (augFiltration ℱ.rightCont μ).rightCont ≤ augFiltration ℱ.rightCont μ := by
  intro t
  rcases lt_or_ge t 0 with ht | ht
  · have hs : t < t / 2 := by linarith
    have h1 : (augFiltration ℱ.rightCont μ).rightCont t
        ≤ augFiltration ℱ.rightCont μ (t / 2) := by
      rw [Filtration.rightCont_eq]
      exact iInf₂_le _ hs
    rw [augFiltration_of_nonpos _ _ (by linarith : t / 2 ≤ 0)] at h1
    rw [augFiltration_of_nonpos _ _ ht.le]
    exact h1
  · have hseq : ∀ n : ℕ, t < t + ((n : ℝ) + 1)⁻¹ := by
      intro n
      have : (0 : ℝ) < ((n : ℝ) + 1)⁻¹ := by positivity
      linarith
    have hanti : Antitone fun n : ℕ => ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹) := by
      intro a b hab
      refine ℱ.rightCont.mono ?_
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
      have hinv : ((b : ℝ) + 1)⁻¹ ≤ ((a : ℝ) + 1)⁻¹ := by gcongr
      linarith
    have h1 : (augFiltration ℱ.rightCont μ).rightCont t
        ≤ ⨅ n : ℕ, aug (ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› μ := by
      refine le_iInf fun n => ?_
      have h2 : (augFiltration ℱ.rightCont μ).rightCont t
          ≤ augFiltration ℱ.rightCont μ (t + ((n : ℝ) + 1)⁻¹) := by
        rw [Filtration.rightCont_eq]
        exact iInf₂_le _ (hseq n)
      have h3 : augFiltration ℱ.rightCont μ (t + ((n : ℝ) + 1)⁻¹)
          = aug (ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹)) ‹MeasurableSpace Ω› μ := by
        change aug (ℱ.rightCont (max (t + ((n : ℝ) + 1)⁻¹) 0)) ‹MeasurableSpace Ω› μ = _
        rw [max_eq_left (by linarith [hseq n])]
      rwa [h3] at h2
    rw [aug_iInf_of_antitone hanti] at h1
    have h4 : (⨅ n : ℕ, ℱ.rightCont (t + ((n : ℝ) + 1)⁻¹)) ≤ ℱ.rightCont t := by
      rw [Filtration.rightCont_eq]
      refine le_iInf₂ fun u hu => ?_
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < u - t by linarith)
      refine le_trans (iInf_le _ n) ?_
      rw [Filtration.rightCont_eq]
      refine iInf₂_le u ?_
      rw [one_div] at hn
      linarith
    have h5 : augFiltration ℱ.rightCont μ t = aug (ℱ.rightCont t) ‹MeasurableSpace Ω› μ := by
      change aug (ℱ.rightCont (max t 0)) ‹MeasurableSpace Ω› μ = _
      rw [max_eq_left ht]
    rw [h5]
    exact le_trans h1 (aug_mono h4)

instance isRightContinuous_augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) :
    Filtration.IsRightContinuous (augFiltration ℱ.rightCont μ) :=
  ⟨rightCont_augFiltration_le ℱ μ⟩

/-- The `hℱ0` hypothesis, discharged for the augmentation of a right-continuous filtration. -/
theorem hF0_augFiltration (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (μ : Measure Ω) (t : ℝ)
    (ht : t ≤ 0) :
    (augFiltration ℱ.rightCont μ).rightCont 0 ≤ (augFiltration ℱ.rightCont μ).rightCont t := by
  rw [Filtration.IsRightContinuous.eq (𝓕 := augFiltration ℱ.rightCont μ)]
  rw [augFiltration_of_nonpos _ _ ht, augFiltration_of_nonpos _ _ (le_refl (0 : ℝ))]

end LevyStochCalc.Brownian
