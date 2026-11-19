/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreHamiltonianOUReferenceSublevelStopped.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianOUReferenceProcess
public import LeanPool.GinibrePoincare.Analysis.BrownianStoppingExitCountableEvaluation
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianContinuousClosedStopping
public import LeanPool.GinibrePoincare.Analysis.GinibreHamiltonianSublevels

/-! The actual global OU reference admits genuine compact collision-free
stopping on every prescribed positive finite horizon. -/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal
namespace GinibrePoincare
noncomputable section

/-- The configurations at which the Ginibre weight exceeds `exp (-R)`. -/
def ginibreHamiltonianOUSublevelDomain (n : ℕ) (R : ℝ) : Set (Configuration n) :=
  {x | Real.exp (-R) < ginibreWeight n x}

/-- The first time in `[0, T]` at which the Ornstein–Uhlenbeck reference process leaves the
sublevel domain `ginibreHamiltonianOUSublevelDomain n R` (and `T` if it never does). -/
def ginibreHamiltonianOUSublevelStop {Ω : Type*} (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  hittingBtwn (ginibreHamiltonianOUReferenceProcess n α z B)
    (ginibreHamiltonianOUSublevelDomain n R)ᶜ 0 T ω

theorem ginibreHamiltonianOUSublevelStop_eq_horizon_of_stays {Ω : Type*}
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0) (ω : Ω)
    (hStay : ∀ t ≤ T, ginibreHamiltonianOUReferenceProcess n α z B t ω ∈
      ginibreHamiltonianOUSublevelDomain n R) :
    ginibreHamiltonianOUSublevelStop n α z B R T ω = T := by
  have hh : ¬∃ t ∈ Icc (0 : ℝ≥0) T,
      ginibreHamiltonianOUReferenceProcess n α z B t ω ∈ (ginibreHamiltonianOUSublevelDomain n R)ᶜ
          := by
    rintro ⟨t, ht, hmem⟩
    exact hmem (hStay t ht.2)
  unfold ginibreHamiltonianOUSublevelStop hittingBtwn
  rw [ite_eq_right hh]

/-- On the literal survival event the stopped reference is the full actual OU path. -/
theorem ginibreHamiltonianOUSublevelStopped_eq_reference_of_stays {Ω : Type*}
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0)
    (Y : ℝ≥0 → Ω → Configuration n) (θ : Ω → ℝ≥0)
    (hStopped : ∀ t ω, Y t ω = ginibreHamiltonianOUReferenceProcess n α z B (min t (θ ω)) ω)
    (hActual : ∀ ω, θ ω = ginibreHamiltonianOUSublevelStop n α z B R T ω)
    (ω : Ω) (hStay : ∀ t ≤ T, ginibreHamiltonianOUReferenceProcess n α z B t ω ∈
      ginibreHamiltonianOUSublevelDomain n R) :
    θ ω = T ∧ ∀ t ≤ T, Y t ω = ginibreHamiltonianOUReferenceProcess n α z B t ω := by
  have he : θ ω = T := (hActual ω).trans
    (ginibreHamiltonianOUSublevelStop_eq_horizon_of_stays n α z B R T ω hStay)
  refine ⟨he, fun t ht => ?_⟩
  rw [hStopped, he, min_eq_left ht]

/-- If the actual OU path leaves the open level on the horizon, its literal
first exit lies in the closed complement, including an exit at the endpoint. -/
theorem ginibreHamiltonianOUSublevelStop_mem_complement_of_not_stays {Ω : Type*}
    (n : ℕ) (α : ℝ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (R : ℝ) (T : ℝ≥0) (ω : Ω)
    (hNot : ¬ ∀ t ≤ T, ginibreHamiltonianOUReferenceProcess n α z B t ω ∈
      ginibreHamiltonianOUSublevelDomain n R) :
    ginibreHamiltonianOUReferenceProcess n α z B
      (ginibreHamiltonianOUSublevelStop n α z B R T ω) ω ∈
      (ginibreHamiltonianOUSublevelDomain n R)ᶜ := by
  classical
  have hW : Continuous (ginibreWeight n) :=
    (Real.continuous_exp.comp ((contDiff_configurationNormSq (n := n)).continuous.const_mul (-(n :
        ℝ)))).mul
      (contDiff_vandermondeWeight n).continuous
  have hG : IsOpen (ginibreHamiltonianOUSublevelDomain n R) := isOpen_lt continuous_const hW
  have he : ∃ t ∈ Icc (0 : ℝ≥0) T,
      ginibreHamiltonianOUReferenceProcess n α z B t ω ∈ (ginibreHamiltonianOUSublevelDomain n R)ᶜ
          := by
    push Not at hNot
    obtain ⟨t, ht, hm⟩ := hNot
    exact ⟨t, ⟨zero_le, ht⟩, hm⟩
  have hClosed : IsClosed (Icc (0 : ℝ≥0) T ∩
      {t | ginibreHamiltonianOUReferenceProcess n α z B t ω ∈ (ginibreHamiltonianOUSublevelDomain n
          R)ᶜ}) :=
    isClosed_Icc.inter (hG.isClosed_compl.preimage
      (ginibreHamiltonianOUReferenceProcess_continuous n α z B ω))
  have hNon : (Icc (0 : ℝ≥0) T ∩
      {t | ginibreHamiltonianOUReferenceProcess n α z B t ω ∈ (ginibreHamiltonianOUSublevelDomain n
          R)ᶜ}).Nonempty := by
    obtain ⟨t, ht, hm⟩ := he
    exact ⟨t, ht, hm⟩
  have hm := hClosed.csInf_mem hNon (OrderBot.bddBelow _)
  unfold ginibreHamiltonianOUSublevelStop hittingBtwn
  rw [ite_eq_left he]
  exact hm.2

theorem ginibreHamiltonianOU_reference_sublevel_stopped_exists {Ω : Type*} [mAmbient :
    MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω) [P.IsComplete]
    (hB : ∀ i, IsBrownianReal (B i) P) (α : ℝ)
    (z : Configuration n) (hz : CollisionFree z) (R : ℝ) (hR : ginibreHamiltonian n z < R)
    (T : ℝ≥0) (hT : 0 < T) :
    ∃ Y : ℝ≥0 → Ω → Configuration n,
      (∀ ω, Continuous (fun t => Y t ω)) ∧ (∀ t ω, Y t ω ∈ ginibreHamiltonianSublevel n R) ∧
      (∀ ω, Y 0 ω = z) ∧
      StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
          Y ∧
      ∃ θ : Ω → ℝ≥0,
      IsStoppingTime (ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal))
        (fun ω => (θ ω : WithTop ℝ≥0)) ∧ (∀ ω, 0 < θ ω ∧ θ ω ≤ T) ∧
      (∀ t ω, Y t ω = ginibreHamiltonianOUReferenceProcess n α z B (min t (θ ω)) ω) ∧
      (∀ ω, θ ω = ginibreHamiltonianOUSublevelStop n α z B R T ω) ∧
      ∀ᵐ ω ∂P, ∀ t ≤ θ ω, Y t ω = z+ginibreConfigurationBrownianNoise n B α ω t+
        ∫ s in (0 : ℝ)..t, (-2*α/(n : ℝ)) • Y s.toNNReal ω := by
  let K := ginibreHamiltonianSublevel n R
  let G := ginibreHamiltonianOUSublevelDomain n R
  have hW : Continuous (ginibreWeight n) :=
    (Real.continuous_exp.comp ((contDiff_configurationNormSq (n := n)).continuous.const_mul (-(n :
        ℝ)))).mul
      (contDiff_vandermondeWeight n).continuous
  have hG : IsOpen G := isOpen_lt continuous_const hW
  have hGz : z ∈ G := by
    change Real.exp (-R) < ginibreWeight n z
    rw [← ginibreHamiltonian_exp_neg z hz]
    exact Real.exp_lt_exp.mpr (neg_lt_neg hR)
  have hK : IsCompact K := ginibreHamiltonianSublevel_isCompact hn R
  have hClosure : closure G ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro x hx
    change x ∈ ginibreHamiltonianSublevel n R
    rw [ginibreHamiltonianSublevel_eq_weight_superlevel]
    exact le_of_lt (show Real.exp (-R) < ginibreWeight n x from hx)
  let U := ginibreHamiltonianOUReferenceProcess n α z B
  have hUC := ginibreHamiltonianOUReferenceProcess_continuous n α z B
  have hUA := ginibreHamiltonianOUReferenceProcess_stronglyAdapted n α z B P hB
  let θ := hittingBtwn U Gᶜ 0 T
  have hStop := ginibreContinuous_closed_exit_isStoppingTime _ U hUA hUC Gᶜ hG.isClosed_compl T
  have hθT (ω : Ω) : θ ω ≤ T := hittingBtwn_le ω
  have hθpos (ω : Ω) : 0 < θ ω :=
    drivenContinuous_closed_hitting_pos U Gᶜ hG.isClosed_compl T hT ω (hUC ω)
      (by simpa [U, ginibreHamiltonianOUReferenceProcess_zero] using hGz)
  let Y : ℝ≥0 → Ω → Configuration n := fun t ω => U (min t (θ ω)) ω
  have hYC (ω : Ω) : Continuous (fun t => Y t ω) := (hUC ω).comp (continuous_id.min
      continuous_const)
  have hYR (t : ℝ≥0) (ω : Ω) : Y t ω ∈ K :=
    hClosure (ginibreContinuous_mem_closure_until_exit U G T ω (hUC ω)
      (by simpa [U, ginibreHamiltonianOUReferenceProcess_zero] using hGz) _ (min_le_right t (θ ω)))
  have hYA : StronglyAdapted (ginibreBrownianAugmentedFiltration B P (fun i => (hB
      i).toIsPreBrownianReal)) Y := by
    let F := ginibreBrownianAugmentedFiltration B P (fun i => (hB i).toIsPreBrownianReal)
    intro s
    have hm (k : ℕ) : @StronglyMeasurable Ω (Configuration n) _ (F s)
        (fun ω => U (min s (stoppingUpperGrid k (θ ω))) ω) :=
      (adapted_capped_upper_grid_evaluation_measurable F U hUA.adapted θ hStop k
          s).stronglyMeasurable
    apply stronglyMeasurable_of_tendsto atTop hm
    rw [tendsto_pi_nhds]
    intro ω
    exact (hUC ω).continuousAt.tendsto.comp (tendsto_const_nhds.min (stoppingUpperGrid_tendsto (θ
        ω)))
  refine ⟨Y, hYC, hYR,?_, hYA, θ, hStop,
    fun ω => ⟨hθpos ω, hθT ω⟩, fun t ω => rfl, fun ω => rfl,?_⟩
  · intro ω
    simp [Y, U, ginibreHamiltonianOUReferenceProcess_zero]
  · filter_upwards [ginibreHamiltonianOUReferenceProcess_original_equation n α z B P hB] with ω hω
    intro t ht
    change U (min t (θ ω)) ω = _
    have huEq : U t ω = z+ginibreConfigurationBrownianNoise n B α ω t+
        ∫ s in (0 : ℝ)..t, (-2*α/(n : ℝ)) • U s.toNNReal ω := hω t
    rw [min_eq_left ht, huEq]
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    have hsI : s ∈ Icc (0 : ℝ) (t : ℝ) := by
      simpa only [uIcc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] using hs
    have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hsI.2
    change (-2*α/(n : ℝ)) • U s.toNNReal ω = (-2*α/(n : ℝ)) • U (min s.toNNReal (θ ω)) ω
    rw [min_eq_left (hst.trans ht)]

end
end GinibrePoincare
