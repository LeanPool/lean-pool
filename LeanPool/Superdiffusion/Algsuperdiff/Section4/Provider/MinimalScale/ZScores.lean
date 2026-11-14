/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Probability.RandomScaleWitness
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.GoodEvents.ObservableTranslate
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.CgEllipLowerConstant

/-!
# ZScores

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two window scores of `p.minimal.scale.separation.sec4`, and their bad windows

ABK26, §4.2, the definitions of `Z₁` and `Z₂`.  The proposition's two conclusions are
`δ`-thresholded inequalities for two `ℝ≥0∞`-valued *scores* attached to the
window `[n, m]` of triadic scales:

* the **Cesàro-`𝓔` score** — the centre-uniform Cesàro average of the
  flux-corrected error observable, gated by the good event; and
* the **bad-density score** — the centre-uniform Cesàro average of the
  *complement* indicator of the good event.

Both are copied here *verbatim* from the frozen statement's own display, so that
a consumer discharging the frozen clause never has to move a single subterm.  In
particular the tolerance is spelled `s * Real.sqrt delta`, the normalisation is
`(((m - n).toNat : ℝ≥0∞) + 1)⁻¹`, the centre set is
`Support.latticeCubeSet d (n - 1) m` and the centre is
`Support.triadicLatticePoint (n - 1) z`.

The scores are used **directly** as `ℝ≥0∞`-valued predicates: a window of
length `j` is *bad* when.ofReal delta` is strictly below the score of the
window `[m - j, m]`.  No real cast, no finiteness and no convergence side
condition enters (survey item does not bite: `Algsuperdiff.Probability`'s
`minimalScale is generic over the bad-window family).

## Contents

* `centerCesaroScore`, `centerDensityScore` — the two per-centre window
  averages, and `cesaroScore` / `densityScore`, their suprema over the centre
  set, at the frozen display's exact shape (`cesaroScore_eq_iSup`,
  `densityScore_eq_iSup` are `rfl`).
* `badCesaro`, `badDensity` — the two bad-window families, indexed by the
  window *length* `j : ℕ` at base scale `m`, i.e. at the window `[m - j, m]`.
* `measurable_cesaroScore`, `measurable_densityScore`,
  `measurableSet_badCesaro`, `measurableSet_badDensity` — the measurability
  layer feeding `Algsuperdiff.Probability.measurable_minimalScaleEN`.
* `cesaroScore_le_of_minimalScaleEN_le`, `densityScore_le_of_minimalScaleEN_le` — the two
  deterministic extractions, at the frozen conclusion's own `n : ℤ` indexing,
  holding for **every** `omega` (strictly stronger than the frozen statement's
  `∀ᵐ`).

## References

* ABK26, `p.minimal.scale.separation.sec4`.
-/

namespace Algsuperdiff.Section4.Provider.MinimalScale

open Algsuperdiff.Section3
open HCPolySupport MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## 1. The per-centre window averages -/

/-- **The Cesàro-`𝓔` window average at the centre `y`** — the inner term of
`minimal_scale_separation`'s first conclusion, before the maximum over
centres. -/
noncomputable def centerCesaroScore (M : ABKModel d) (s delta : ℝ) (hs : 0 < s)
    (y : Vec d) (n m : ℤ) (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  (((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
    ∑ k ∈ Finset.Icc n m,
      Set.indicator
        (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d) k y
          ⟨s, hs⟩ (s * Real.sqrt delta))
        (fun omega' =>
          Support.fluxCorrectedErrorObservableSup M k ⟨s, hs⟩
            (Cutoff.translateCutoffSample y omega'))
        omega

/-- **The bad-density window average at the centre `y`** — the inner term of
`minimal_scale_separation`'s second conclusion. -/
noncomputable def centerDensityScore (M : ABKModel d) (s delta : ℝ) (hs : 0 < s)
    (y : Vec d) (n m : ℤ) (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  (((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
    ∑ k ∈ Finset.Icc n m,
      Set.indicator
        ((Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d) k y
          ⟨s, hs⟩ (s * Real.sqrt delta))ᶜ)
        (fun _ => (1 : ℝ≥0∞)) omega

/-! ## 2. The centre-uniform scores, at the frozen display's shape -/

/-- **The Cesàro-`𝓔` score of the window `[n, m]`** — the left-hand side of
`e.scale.sep.for.mathcal.E` as frozen. -/
noncomputable def cesaroScore (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ⨆ z : ↥(Support.latticeCubeSet d (n - 1) m),
    (((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
      ∑ k ∈ Finset.Icc n m,
        Set.indicator
          (Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d) k
            (Support.triadicLatticePoint (n - 1) z) ⟨s, hs⟩ (s * Real.sqrt delta))
          (fun omega' =>
            Support.fluxCorrectedErrorObservableSup M k ⟨s, hs⟩
              (Cutoff.translateCutoffSample (Support.triadicLatticePoint (n - 1) z) omega'))
          omega

/-- **The bad-density score of the window `[n, m]`** — the left-hand side of
`e.scale.sep.for.good.events` as frozen. -/
noncomputable def densityScore (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) : ℝ≥0∞ :=
  ⨆ z : ↥(Support.latticeCubeSet d (n - 1) m),
    (((m - n).toNat : ℝ≥0∞) + 1)⁻¹ *
      ∑ k ∈ Finset.Icc n m,
        Set.indicator
          ((Algsuperdiff.Frozen.Section4.goodEventAt M (Support.cgEllipLowerConstant d) k
            (Support.triadicLatticePoint (n - 1) z) ⟨s, hs⟩ (s * Real.sqrt delta))ᶜ)
          (fun _ => (1 : ℝ≥0∞)) omega

/-- The centre-uniform Cesàro score is the supremum of the per-centre averages
over the frozen centre set. -/
theorem cesaroScore_eq_iSup (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    cesaroScore M s delta hs n m omega =
      ⨆ z : ↥(Support.latticeCubeSet d (n - 1) m),
        centerCesaroScore M s delta hs (Support.triadicLatticePoint (n - 1) z) n m omega :=
  rfl

/-- The centre-uniform density score is the supremum of the per-centre
averages over the frozen centre set. -/
theorem densityScore_eq_iSup (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (n m : ℤ)
    (omega : Cutoff.CutoffSample d) :
    densityScore M s delta hs n m omega =
      ⨆ z : ↥(Support.latticeCubeSet d (n - 1) m),
        centerDensityScore M s delta hs (Support.triadicLatticePoint (n - 1) z) n m omega :=
  rfl

/-! ## 3. The bad-window families -/

/-- **The bad windows of the Cesàro-`𝓔` score**, indexed by the window length
`j : ℕ` at base scale `m`: the window `[m - j, m]` is bad when its score
exceeds `δ`. -/
def badCesaro (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (m : ℤ) (j : ℕ)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ENNReal.ofReal delta < cesaroScore M s delta hs (m - (j : ℤ)) m omega

/-- **The bad windows of the bad-density score.** -/
def badDensity (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (m : ℤ) (j : ℕ)
    (omega : Cutoff.CutoffSample d) : Prop :=
  ENNReal.ofReal delta < densityScore M s delta hs (m - (j : ℤ)) m omega

/-! ## 4. The window-index bridge -/

/-- For `n ≤ m` the window length `(m - n).toNat` recovers the lower endpoint:
`m - ((m - n).toNat : ℤ) = n`. -/
theorem sub_toNat_sub_cancel {n m : ℤ} (hnm : n ≤ m) : m - (((m - n).toNat : ℕ) : ℤ) = n := by
  have h : (((m - n).toNat : ℕ) : ℤ) = m - n := Int.toNat_of_nonneg (by omega)
  rw [h]
  ring

/-- The window length of `[m - j, m]` is `j`. -/
theorem toNat_sub_sub (m : ℤ) (j : ℕ) : (m - (m - (j : ℤ))).toNat = j := by
  have h : m - (m - (j : ℤ)) = (j : ℤ) := by ring
  rw [h, Int.toNat_natCast]

/-! ## 5. Measurability -/

/-- Each summand of the Cesàro-`𝓔` window average is measurable. -/
theorem measurable_centerCesaroScore (M : ABKModel d) (s delta : ℝ) (hs : 0 < s)
    (y : Vec d) (n m : ℤ) :
    Measurable (centerCesaroScore M s delta hs y n m) := by
  refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => ?_) _
  exact ((Support.measurable_fluxCorrectedErrorObservableSup M k ⟨s, hs⟩).comp
      (Cutoff.measurable_translateCutoffSample y)).indicator
    (GoodEvents.measurableSet_goodEventAt M (Support.cgEllipLowerConstant d) k y ⟨s, hs⟩
      (s * Real.sqrt delta))

/-- The bad-density window average is measurable. -/
theorem measurable_centerDensityScore (M : ABKModel d) (s delta : ℝ) (hs : 0 < s)
    (y : Vec d) (n m : ℤ) :
    Measurable (centerDensityScore M s delta hs y n m) := by
  refine Measurable.const_mul (Finset.measurable_sum _ fun k _ => ?_) _
  exact measurable_const.indicator
    (GoodEvents.measurableSet_goodEventAt M (Support.cgEllipLowerConstant d) k y ⟨s, hs⟩
      (s * Real.sqrt delta)).compl

/-- **The Cesàro-`𝓔` score is measurable.**  The centre set is a subtype of the
countable type `Fin d → ℤ`, so the supremum is a countable one. -/
theorem measurable_cesaroScore (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (n m : ℤ) :
    Measurable (cesaroScore M s delta hs n m) := by
  change Measurable fun omega => ⨆ z : ↥(Support.latticeCubeSet d (n - 1) m),
    centerCesaroScore M s delta hs (Support.triadicLatticePoint (n - 1) z) n m omega
  exact Measurable.iSup fun z =>
    measurable_centerCesaroScore M s delta hs (Support.triadicLatticePoint (n - 1) z) n m

/-- **The bad-density score is measurable.** -/
theorem measurable_densityScore (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (n m : ℤ) :
    Measurable (densityScore M s delta hs n m) := by
  change Measurable fun omega => ⨆ z : ↥(Support.latticeCubeSet d (n - 1) m),
    centerDensityScore M s delta hs (Support.triadicLatticePoint (n - 1) z) n m omega
  exact Measurable.iSup fun z =>
    measurable_centerDensityScore M s delta hs (Support.triadicLatticePoint (n - 1) z) n m

/-- **Every Cesàro bad-window event is measurable** — the input of
`Algsuperdiff.Probability.measurable_minimalScaleEN`. -/
theorem measurableSet_badCesaro (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (m : ℤ) (j : ℕ) :
    MeasurableSet {omega | badCesaro M s delta hs m j omega} :=
  measurable_cesaroScore M s delta hs (m - (j : ℤ)) m measurableSet_Ioi

/-- **Every density bad-window event is measurable.** -/
theorem measurableSet_badDensity (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (m : ℤ) (j : ℕ) :
    MeasurableSet {omega | badDensity M s delta hs m j omega} :=
  measurable_densityScore M s delta hs (m - (j : ℤ)) m measurableSet_Ioi

/-! ## 6. The deterministic extractions -/

/-- **The Cesàro-`𝓔` clause, pointwise.**  If the Cesàro random scale is at most the
window length `(m - n).toNat`, then the window `[n, m]` clears `δ`.  This holds for
**every** `omega`, with no almost-sure qualifier and no finiteness hypothesis: it is
`Probability.minimalScaleEN_not_bad_of_le`, vacuous exactly on the `⊤`-event. -/
theorem cesaroScore_le_of_minimalScaleEN_le (M : ABKModel d) (s delta : ℝ) (hs : 0 < s)
    {n m : ℤ} (hnm : n ≤ m) {omega : Cutoff.CutoffSample d}
    (h : Probability.minimalScaleEN (badCesaro M s delta hs m) omega
      ≤ (((m - n).toNat : ℕ) : ℕ∞)) :
    cesaroScore M s delta hs n m omega ≤ ENNReal.ofReal delta := by
  have hnot := Probability.minimalScaleEN_not_bad_of_le h
  rw [badCesaro, sub_toNat_sub_cancel hnm] at hnot
  exact not_lt.mp hnot

/-- **The bad-density clause, pointwise** — the deterministic half of `Z₂`. -/
theorem densityScore_le_of_minimalScaleEN_le (M : ABKModel d) (s delta : ℝ) (hs : 0 < s)
    {n m : ℤ} (hnm : n ≤ m) {omega : Cutoff.CutoffSample d}
    (h : Probability.minimalScaleEN (badDensity M s delta hs m) omega
      ≤ (((m - n).toNat : ℕ) : ℕ∞)) :
    densityScore M s delta hs n m omega ≤ ENNReal.ofReal delta := by
  have hnot := Probability.minimalScaleEN_not_bad_of_le h
  rw [badDensity, sub_toNat_sub_cancel hnm] at hnot
  exact not_lt.mp hnot

/-! ## 7. The centre-wise cover of a bad window -/

/-- **`hcover`, as a theorem.**  A bad Cesàro window is witnessed by *some*
centre of the frozen centre set — the converse direction of the maximum, which
is `lt_iSup_iff` in the complete linear order `ℝ≥0∞` and needs no finiteness,
no positivity of `δ` and no measurability. -/
theorem exists_center_of_badCesaro (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (m : ℤ)
    (j : ℕ) {omega : Cutoff.CutoffSample d} (h : badCesaro M s delta hs m j omega) :
    ∃ z ∈ Support.latticeCubeSet d (m - (j : ℤ) - 1) m,
      ENNReal.ofReal delta <
        centerCesaroScore M s delta hs (Support.triadicLatticePoint (m - (j : ℤ) - 1) z)
          (m - (j : ℤ)) m omega := by
  rw [badCesaro, cesaroScore_eq_iSup, lt_iSup_iff] at h
  obtain ⟨z, hz⟩ := h
  exact ⟨z.1, z.2, hz⟩

/-- **`hcover`, as a theorem** — the density leg. -/
theorem exists_center_of_badDensity (M : ABKModel d) (s delta : ℝ) (hs : 0 < s) (m : ℤ)
    (j : ℕ) {omega : Cutoff.CutoffSample d} (h : badDensity M s delta hs m j omega) :
    ∃ z ∈ Support.latticeCubeSet d (m - (j : ℤ) - 1) m,
      ENNReal.ofReal delta <
        centerDensityScore M s delta hs (Support.triadicLatticePoint (m - (j : ℤ) - 1) z)
          (m - (j : ℤ)) m omega := by
  rw [badDensity, densityScore_eq_iSup, lt_iSup_iff] at h
  obtain ⟨z, hz⟩ := h
  exact ⟨z.1, z.2, hz⟩

end

end Algsuperdiff.Section4.Provider.MinimalScale
