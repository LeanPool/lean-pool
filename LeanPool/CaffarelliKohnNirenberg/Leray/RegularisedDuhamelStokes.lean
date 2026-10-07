/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedDuhamelSemigroup
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildStokesContinuity
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierStokesLinearity
public import Mathlib.MeasureTheory.Function.Holder

/-!
# Heat evolution of the projected tensor divergence

The Fourier formulas show that heat evolution composes with the regularized
Leray--Stokes operator by adding elapsed times.
-/

public section

open MeasureTheory
open Filter
open scoped ENNReal FourierTransform Topology

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

private instance : ENNReal.HolderTriple (∞ : ℝ≥0∞) 2 2 := by
  constructor
  simp

/-- The complex Stokes operator is strongly continuous at every positive
elapsed time for a fixed tensor input. -/
theorem stokesL2Operator_continuousAt {t₀ : ℝ} (ht₀ : 0 < t₀)
    (F : ComplexTensorL2) :
    ContinuousAt (fun t : {x : ℝ // 0 < x} => stokesL2Operator t.2 F)
      ⟨t₀, ht₀⟩ := by
  let ℱT := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexTensor3
  let ℱV := MeasureTheory.Lp.fourierTransformₗᵢ L2Vec3 ComplexVec3
  have hfrequency := stokesFourierMultiplier_continuousAt ht₀ (ℱT F)
  have hphysical : ContinuousAt
      (fun t : {x : ℝ // 0 < x} =>
        ℱV.symm (stokesFourierMultiplier t.2 (ℱT F))) ⟨t₀, ht₀⟩ :=
    ℱV.symm.continuous.continuousAt.comp hfrequency
  change ContinuousAt (fun t : {x : ℝ // 0 < x} =>
    ℱV.symm (stokesFourierMultiplier t.2 (ℱT F))) ⟨t₀, ht₀⟩
  exact hphysical

/-- Applying the complex Stokes family to a continuous tensor path is
continuous at every positive elapsed time. -/
theorem stokesL2Operator_continuousAt_apply {t₀ : ℝ} (ht₀ : 0 < t₀)
    {α : Type*} {l : Filter α} (t : α → {x : ℝ // 0 < x})
    (ht : Tendsto t l (𝓝 (⟨t₀, ht₀⟩ : {x : ℝ // 0 < x})))
    (F : {x : ℝ // 0 < x} → ComplexTensorL2)
    (hF : ContinuousAt F ⟨t₀, ht₀⟩) :
    Tendsto (fun x => stokesL2Operator (t x).2 (F (t x))) l
      (𝓝 (stokesL2Operator ht₀ (F ⟨t₀, ht₀⟩))) := by
  let t₀' : {x : ℝ // 0 < x} := ⟨t₀, ht₀⟩
  let Fpath : α → ComplexTensorL2 := F ∘ t
  have hFpath : Tendsto Fpath l (𝓝 (F t₀')) := hF.tendsto.comp ht
  have htval : Tendsto (fun x => (t x : ℝ)) l (𝓝 (t₀' : ℝ)) :=
    continuous_subtype_val.continuousAt.tendsto.comp ht
  have hFdiff : Tendsto (fun x => Fpath x - F t₀') l (𝓝 0) := by
    have hconst : Tendsto (fun _ : α => F t₀') l (𝓝 (F t₀')) := tendsto_const_nhds
    simpa using hFpath.sub hconst
  have hFnorm : Tendsto (fun x => ‖Fpath x - F t₀'‖) l (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).1 hFdiff
  have hnear : ∀ᶠ x in l, (t₀' : ℝ) / 2 < (t x : ℝ) := by
    have hopen : Set.Ioi ((t₀' : ℝ) / 2) ∈ 𝓝 (t₀' : ℝ) :=
      Ioi_mem_nhds (by linarith only [t₀'.2])
    exact htval.eventually_mem hopen
  let B : ℝ := 1 / Real.sqrt (Real.exp 1 * (t₀' : ℝ))
  have hupper : Tendsto (fun x => B * ‖Fpath x - F t₀'‖) l (𝓝 0) := by
    have hBconst : Tendsto (fun _ : α => B) l (𝓝 B) := tendsto_const_nhds
    simpa only [mul_zero] using hBconst.mul hFnorm
  have hfirstNorm : Tendsto
      (fun x => ‖stokesL2Operator (t x).2 (Fpath x - F t₀')‖) l (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper ?_ ?_
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _
    · filter_upwards [hnear] with x hx
      have hcoef :
          1 / Real.sqrt (2 * Real.exp 1 * (t x : ℝ)) ≤ B := by
        dsimp [B]
        apply one_div_le_one_div_of_le
        · positivity
        · apply Real.sqrt_le_sqrt
          calc
            Real.exp 1 * (t₀' : ℝ) ≤ Real.exp 1 * (2 * (t x : ℝ)) :=
              mul_le_mul_of_nonneg_left (by linarith only [hx])
                (le_of_lt (Real.exp_pos (1 : ℝ)))
            _ = 2 * Real.exp 1 * (t x : ℝ) := by ring
      calc
        ‖stokesL2Operator (t x).2 (Fpath x - F t₀')‖ ≤
          (1 / Real.sqrt (2 * Real.exp 1 * (t x : ℝ))) *
            ‖Fpath x - F t₀'‖ := stokesL2Operator_norm_le (t x).2 _
        _ ≤ B * ‖Fpath x - F t₀'‖ :=
          mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  have hfirst : Tendsto
      (fun x => stokesL2Operator (t x).2 (Fpath x - F t₀')) l (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hfirstNorm
  have hfixed : Tendsto
      (fun x => stokesL2Operator (t x).2 (F t₀')) l
      (𝓝 (stokesL2Operator t₀'.2 (F t₀'))) := by
    exact (stokesL2Operator_continuousAt ht₀ (F t₀')).tendsto.comp ht
  have hsecond : Tendsto
      (fun x => stokesL2Operator (t x).2 (F t₀') -
        stokesL2Operator t₀'.2 (F t₀')) l (𝓝 0) := by
    have hconst : Tendsto (fun _ : α => stokesL2Operator t₀'.2 (F t₀'))
        l (𝓝 (stokesL2Operator t₀'.2 (F t₀'))) := tendsto_const_nhds
    simpa using hfixed.sub hconst
  have hsum := hfirst.add hsecond
  have hadd : (fun x => stokesL2Operator (t x).2 (F (t x))) =
      fun x => stokesL2Operator (t x).2 (Fpath x - F t₀') +
        (stokesL2Operator (t x).2 (F t₀') -
          stokesL2Operator t₀'.2 (F t₀')) + stokesL2Operator t₀'.2 (F t₀') := by
    funext x
    change stokesL2Operator (t x).2 (Fpath x) = _
    calc
      stokesL2Operator (t x).2 (Fpath x) =
          stokesL2Operator (t x).2 ((Fpath x - F t₀') + F t₀') := by
        congr 1
        abel
      _ = stokesL2Operator (t x).2 (Fpath x - F t₀') +
          stokesL2Operator (t x).2 (F t₀') :=
            stokesL2Operator_add (t x).2 (Fpath x - F t₀') (F t₀')
      _ = stokesL2Operator (t x).2 (Fpath x - F t₀') +
          (stokesL2Operator (t x).2 (F t₀') -
            stokesL2Operator t₀'.2 (F t₀')) +
          stokesL2Operator t₀'.2 (F t₀') := by abel
  rw [hadd]
  simpa using hsum.add tendsto_const_nhds

end CKN.Leray

end
