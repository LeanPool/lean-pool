/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildJClosure
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildLipschitz
public import LeanPool.CaffarelliKohnNirenberg.Leray.FourierMildStokesContinuity

/-!
# Continuity of the regularized mild nonlinear and Stokes maps

These continuity statements are the time-regularity inputs to the Volterra
construction in `lem:reg-local-mild`.
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

namespace CKN.Leray

/-- The regularized quadratic tensor depends continuously on its velocity in
spatial `L²`, as required in `lem:reg-local-mild`. -/
theorem regularizedMildTensor_continuousAt (ρ : RegMollifierProfile)
    (ε : ℝ) (hε : 0 < ε) {α : Type*} {l : Filter α}
    (u : α → RealVectorL2) (u₀ : RealVectorL2)
    (hu : Tendsto u l (𝓝 u₀)) :
    Tendsto (fun x => regularizedMildTensor ρ ε hε (u x)) l
      (𝓝 (regularizedMildTensor ρ ε hε u₀)) := by
  have hdiff : Tendsto (fun x => u x - u₀) l (𝓝 0) := by
    have hconst : Tendsto (fun _ : α => u₀) l (𝓝 u₀) := tendsto_const_nhds
    simpa using hu.sub hconst
  have hdiffNorm : Tendsto (fun x => ‖u x - u₀‖) l (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).1 hdiff
  have hnorm : Tendsto (fun x => ‖u x‖) l (𝓝 ‖u₀‖) :=
    (continuous_norm.continuousAt.tendsto.comp hu)
  have hnear : ∀ᶠ x in l, ‖u x‖ ≤ ‖u₀‖ + 1 := by
    have hopen : Set.Iio (‖u₀‖ + 1) ∈ 𝓝 ‖u₀‖ :=
      Iio_mem_nhds (by linarith only [norm_nonneg u₀])
    filter_upwards [hnorm.eventually_mem hopen] with x hx
    exact le_of_lt hx
  have hc : 0 ≤ regularizedMildMollifierConstant ρ ε := by
    exact ENNReal.toReal_nonneg
  let B : ℝ := regularizedMildMollifierConstant ρ ε * (2 * ‖u₀‖ + 1)
  have hupper : Tendsto (fun x => B * ‖u x - u₀‖) l (𝓝 0) := by
    have hBconst : Tendsto (fun _ : α => B) l (𝓝 B) := tendsto_const_nhds
    simpa only [mul_zero] using hBconst.mul hdiffNorm
  have hnormDiff : Tendsto
      (fun x => ‖regularizedMildTensor ρ ε hε (u x) -
        regularizedMildTensor ρ ε hε u₀‖) l (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds hupper ?_ ?_
    · exact Filter.Eventually.of_forall fun x => norm_nonneg _
    · filter_upwards [hnear] with x hx
      have hLip := regularizedMildTensor_sub_norm_le ρ ε hε (u x) u₀
      calc
        ‖regularizedMildTensor ρ ε hε (u x) -
            regularizedMildTensor ρ ε hε u₀‖ ≤
          regularizedMildMollifierConstant ρ ε * (‖u x‖ + ‖u₀‖) * ‖u x - u₀‖ := hLip
        _ ≤ B * ‖u x - u₀‖ := by
          calc
            regularizedMildMollifierConstant ρ ε * (‖u x‖ + ‖u₀‖) *
                ‖u x - u₀‖ ≤
              regularizedMildMollifierConstant ρ ε *
                ((‖u₀‖ + 1) + ‖u₀‖) * ‖u x - u₀‖ := by
                  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
                  exact mul_le_mul_of_nonneg_left
                    (by
                      simpa [add_comm, add_left_comm, add_assoc] using
                        add_le_add_right hx ‖u₀‖) hc
            _ = B * ‖u x - u₀‖ := by
              dsimp [B]
              congr 1
              ring
  have hdiffTensor : Tendsto
      (fun x => regularizedMildTensor ρ ε hε (u x) -
        regularizedMildTensor ρ ε hε u₀) l (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hnormDiff
  have hconst : Tendsto
      (fun _ : α => regularizedMildTensor ρ ε hε u₀) l
      (𝓝 (regularizedMildTensor ρ ε hε u₀)) := tendsto_const_nhds
  simpa only [sub_add_cancel, zero_add] using hdiffTensor.add hconst

/-- Applying the Stokes family to a continuous tensor path is continuous at
every positive elapsed time; this is used for the integrand in
`lem:reg-local-mild`. -/
theorem realStokesOperator_continuousAt_apply {t₀ : ℝ} (ht₀ : 0 < t₀)
    {α : Type*} {l : Filter α} (t : α → {x : ℝ // 0 < x})
    (ht : Tendsto t l (𝓝 (⟨t₀, ht₀⟩ : {x : ℝ // 0 < x})))
    (G : {x : ℝ // 0 < x} → RealTensorL2)
    (hG : ContinuousAt G ⟨t₀, ht₀⟩) :
    Tendsto (fun x => realStokesOperator (t x).2 (G (t x))) l
      (𝓝 (realStokesOperator ht₀ (G ⟨t₀, ht₀⟩))) := by
  let t₀' : {x : ℝ // 0 < x} := ⟨t₀, ht₀⟩
  let F : α → RealTensorL2 := G ∘ t
  have hF : Tendsto F l (𝓝 (G t₀')) := hG.tendsto.comp ht
  have htval : Tendsto (fun x => (t x : ℝ)) l (𝓝 (t₀' : ℝ)) :=
    (continuous_subtype_val.continuousAt.tendsto.comp ht)
  have hFdiff : Tendsto (fun x => F x - G t₀') l (𝓝 0) := by
    have hconst : Tendsto (fun _ : α => G t₀') l (𝓝 (G t₀')) := tendsto_const_nhds
    simpa using hF.sub hconst
  have hFnorm : Tendsto (fun x => ‖F x - G t₀'‖) l (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).1 hFdiff
  have hnear : ∀ᶠ x in l, (t₀' : ℝ) / 2 < (t x : ℝ) := by
    have hopen : Set.Ioi ((t₀' : ℝ) / 2) ∈ 𝓝 (t₀' : ℝ) :=
      Ioi_mem_nhds (by linarith only [t₀'.2])
    exact htval.eventually_mem hopen
  let B : ℝ := 1 / Real.sqrt (Real.exp 1 * (t₀' : ℝ))
  have hupper : Tendsto (fun x => B * ‖F x - G t₀'‖) l (𝓝 0) := by
    have hBconst : Tendsto (fun _ : α => B) l (𝓝 B) := tendsto_const_nhds
    simpa only [mul_zero] using hBconst.mul hFnorm
  have hfirstNorm : Tendsto
      (fun x => ‖realStokesOperator (t x).2 (F x - G t₀')‖) l (𝓝 0) := by
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
          nlinarith only [hx, Real.exp_pos (1 : ℝ)]
      calc
        ‖realStokesOperator (t x).2 (F x - G t₀')‖ ≤
          (1 / Real.sqrt (2 * Real.exp 1 * (t x : ℝ))) *
            ‖F x - G t₀'‖ := realStokesOperator_norm_le (t x).2 _
        _ ≤ B * ‖F x - G t₀'‖ :=
          mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
  have hfirst : Tendsto
      (fun x => realStokesOperator (t x).2 (F x - G t₀')) l (𝓝 0) :=
    (tendsto_zero_iff_norm_tendsto_zero).2 hfirstNorm
  have hfixed : Tendsto
      (fun x => realStokesOperator (t x).2 (G t₀')) l
      (𝓝 (realStokesOperator t₀'.2 (G t₀'))) := by
    have htime := realStokesOperator_continuousAt ht₀ (G t₀')
    exact htime.tendsto.comp ht
  have hsecond : Tendsto
      (fun x => realStokesOperator (t x).2 (G t₀') -
        realStokesOperator t₀'.2 (G t₀')) l (𝓝 0) := by
    have hconst : Tendsto (fun _ : α => realStokesOperator t₀'.2 (G t₀'))
        l (𝓝 (realStokesOperator t₀'.2 (G t₀'))) := tendsto_const_nhds
    simpa using hfixed.sub hconst
  have hsum := hfirst.add hsecond
  have hadd : (fun x => realStokesOperator (t x).2 (G (t x))) =
      fun x => realStokesOperator (t x).2 (F x - G t₀') +
        (realStokesOperator (t x).2 (G t₀') -
          realStokesOperator t₀'.2 (G t₀')) +
          realStokesOperator t₀'.2 (G t₀') := by
    funext x
    rw [← realStokesContinuousLinearMap_apply (t x).2,
      ← realStokesContinuousLinearMap_apply (t x).2,
      ← realStokesContinuousLinearMap_apply (t x).2,
      map_sub]
    dsimp [F]
    abel
  rw [hadd]
  simpa using hsum.add tendsto_const_nhds

end CKN.Leray

end
