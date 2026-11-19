/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryGibbsReversalKilledLaw.lean.
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
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalCoupling
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryGibbsReversalActionLocality
public import LeanPool.GinibrePoincare.Analysis.GinibreBrownianIntegralTiltKilledMapping
/-!
# Alternative Bakry Emery Gibbs reversal killed law

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryGibbs_fixed_initial_killed_law`.
-/

@[expose] public section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Topology NNReal ENNReal
namespace GinibrePoincare
noncomputable section
/-- The Borel σ-algebra on continuous configuration paths `C(Icc 0 T, Configuration n)`. -/
local instance bakryGibbsKilledPathMeasurable (n : ℕ) (T : ℝ≥0) :
    MeasurableSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := borel _
local instance bakryGibbsKilled_pathBorel (n : ℕ) (T : ℝ≥0) :
    BorelSpace C(Icc (0 : ℝ) (T : ℝ), Configuration n) := ⟨rfl⟩

private theorem killedLaw_referenceHorizon_apply {Ω : Type*} (n : ℕ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (sample : Ω) (t : Icc (0 : ℝ) (T : ℝ)) :
    ginibreHamiltonianOUReferenceHorizon n ((n : ℝ) ^ 2) z B T sample t =
      ginibreHamiltonianOUReferenceProcess n ((n : ℝ) ^ 2) z B t.val.toNNReal sample :=
  rfl

private theorem killedLaw_reference_survival_iff {Ω : Type*} (n : ℕ) (z : Configuration n)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (R : ℝ) (sample : Ω) :
    ginibreHamiltonianOUReferenceHorizon n ((n : ℝ) ^ 2) z B T sample ∈
        bakryEmeryGibbsCompactSurvival n T R ↔
      ∀ t ≤ T, ‖ginibreHamiltonianOUReferenceProcess n ((n : ℝ) ^ 2) z B t sample‖ < R := by
  rw [bakryEmeryGibbsCompactSurvival_mem]
  constructor
  · intro h t ht
    have h' := h ⟨(t : ℝ), ⟨t.property, by exact_mod_cast ht⟩⟩
    rw [killedLaw_referenceHorizon_apply] at h'
    simpa only [Real.toNNReal_coe] using h'
  · intro h t
    rw [killedLaw_referenceHorizon_apply]
    exact h t.val.toNNReal (Real.toNNReal_le_iff_le_coe.mpr t.property.2)

/-- Actual finite-horizon ordinary-gradient law on literal compact survival,
identified by its internally constructed stopped Girsanov likelihood against
actual OU, for an initial state strictly inside the killing ball. -/
theorem bakryEmeryGibbs_fixed_initial_killed_law_inside {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i sample t => B i t sample) P)
    (z : Configuration n) (T : ℝ≥0) (hT : 0 < T) (R : ℝ) (hR : ‖z‖ < R) :
    (P.map (fun sample => bakryEmeryGibbsPath W hW κ hκ hc T
      (z, bakryEmeryOriginalCompactDriver n B T sample))).restrict
        (bakryEmeryGibbsCompactSurvival n T R) =
      (P.withDensity (fun sample =>
        ENNReal.ofReal (Real.exp (bakryEmeryGibbsRelativePotential W z)) *
        bakryEmeryGibbsKilledOUAction W T R
          (ginibreHamiltonianOUReferenceHorizon n ((n : ℝ)^2) z B T sample))).map
            (ginibreHamiltonianOUReferenceHorizon n ((n : ℝ)^2) z B T) := by
  classical
  let r := R+‖z‖
  have hr : 0 < r := by dsimp [r]; linarith [norm_nonneg z]
  obtain ⟨Y, hYC, hYR, hY0, hY, θ, hStop, hθ, hStopped, hExit, M, hM, hDi, hD1, hLaw, hAction⟩ :=
    bakryEmeryGibbsOU_relative_action_density_exists hn W hW B P hB hind z r hr T hT
  let F := fun i s sample => bakryEmeryGibbsPotentialTilt n ((n : ℝ)^2)
    (bakryEmeryGibbsRelativePotential W) (Y s sample) i
  let D := brownianVectorExponentialIntegralDensity F T (fun i => M i T)
  let d := fun sample => ENNReal.ofReal (D sample)
  let Q := P.withDensity d
  let N := bakryEmeryCorrectedCompactDriver n W hW B T Y hYC
  let C := fun sample => bakryEmeryGibbsPath W hW κ hκ hc T (z, N sample)
  let O := ginibreHamiltonianOUReferenceHorizon n ((n : ℝ)^2) z B T
  let G := bakryEmeryGibbsCompactSurvival n T R
  let S := O ⁻¹' G
  let e := fun sample => ENNReal.ofReal (Real.exp (bakryEmeryGibbsRelativePotential W z)) *
    bakryEmeryGibbsOUAction W T T.property (O sample)
  have hNm : Measurable N := bakryEmeryCorrectedCompactDriver_measurable n W hW B P hB T Y hYC hY
  have hCm : Measurable C := (bakryEmeryGibbsPath_measurable W hW κ hκ hc T).comp
    (measurable_const.prodMk hNm)
  have hOm : Measurable O :=
    ginibreHamiltonianOUReferenceHorizon_measurable n ((n : ℝ)^2) z B P hB T
  have hG : MeasurableSet G := bakryEmeryGibbsCompactSurvival_measurableSet n T R
  have hS : MeasurableSet S := hG.preimage hOm
  have hFlowLaw : Q.map C = P.map (fun sample => bakryEmeryGibbsPath W hW κ hκ hc T
      (z, bakryEmeryOriginalCompactDriver n B T sample)) := by
    have h := bakryEmeryCorrectedCompactDriver_law n W hW B P hB T Y hYC hY d hLaw
    have hm : Measurable (fun path => bakryEmeryGibbsPath W hW κ hκ hc T (z, path)) :=
      (bakryEmeryGibbsPath_measurable W hW κ hκ hc T).comp (measurable_const.prodMk measurable_id)
    have hh := congrArg (Measure.map (fun path => bakryEmeryGibbsPath W hW κ hκ hc T (z, path))) h
    rw [Measure.map_map hm hNm, Measure.map_map hm
      (bakryEmeryOriginalCompactDriver_measurable n B P hB T)] at hh
    exact hh
  have hCouple := bakryEmeryGibbs_actual_stopped_coupling hn W hW κ hκ hc z B T Y hYC θ
    (fun sample => (hθ sample).2) hStopped
  have hOStay (sample : Ω) : sample ∈ S ↔ ∀ t ≤ T,
      ‖ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t sample‖ < R :=
    killedLaw_reference_survival_iff n z B T R sample
  have hEnd (sample : Ω) (hSurv : sample ∈ S) : θ sample = T := by
    have he := congrFun hExit sample
    rw [he]
    unfold hittingBtwn
    rw [ite_eq_right]
    rintro ⟨t, ht, hmem⟩
    have htNorm := (hOStay sample).mp hSurv t ht.2
    have hb : ‖ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t sample-z‖ < r := by
      have hb := norm_sub_le (ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t sample) z
      dsimp only [r]
      linarith
    exact (not_le_of_gt hb) hmem
  have hCO (sample : Ω) (hSurv : sample ∈ S) : C sample = O sample := by
    apply ContinuousMap.ext
    intro t
    have he := hCouple sample t.val.toNNReal (by
      rw [hEnd sample hSurv]; exact Real.toNNReal_le_iff_le_coe.mpr t.property.2)
    change C sample t = ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t.val.toNNReal sample
    simpa only [C, Real.coe_toNNReal _ t.property.1] using he
  have hSetEq : C ⁻¹' G = S := by
    ext sample
    constructor
    · intro hC
      let U := fun t => ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t sample
      let X := fun t : ℝ≥0 => C sample (projIcc (0 : ℝ) (T : ℝ) T.property (t : ℝ))
      have hPrefix : ∀ t ≤ hittingBtwn (fun s (_ : Unit) => U s-z) {v | r ≤ ‖v‖} 0 T (),
          X t = U t := by
        intro t ht
        have he := congrFun hExit sample
        change θ sample = hittingBtwn (fun s (_ : Unit) => U s-z) {v | r ≤ ‖v‖} 0 T () at he
        have htt : t ≤ θ sample := by rw [he]; exact ht
        have htT : (t : ℝ) ∈ Icc (0 : ℝ) (T : ℝ) :=
          ⟨t.property, by exact_mod_cast htt.trans (hθ sample).2⟩
        exact (congrArg (C sample) (projIcc_of_mem T.property htT)).trans (hCouple sample t htt)
      have hb : ∀ v ∈ {v : Configuration n | ‖v‖ < R}, ‖v-z‖ < r := by
        intro v hv
        have hnle := norm_sub_le v z
        change ‖v‖ < R at hv
        dsimp only [r]
        linarith
      have hSurvive := (bakryEmeryGibbs_closed_exit_domain_survival U X
        (ginibreHamiltonianOUReferenceProcess_continuous n ((n : ℝ)^2) z B sample) z r T
          {v : Configuration n | ‖v‖ < R} hb hPrefix).mp
      apply (hOStay sample).mpr
      apply hSurvive
      intro t ht
      exact (bakryEmeryGibbsCompactSurvival_mem n T R (C sample)).mp hC _
    · intro h
      change C sample ∈ G
      rw [hCO sample h]
      exact h
  have hde : ∀ᵐ sample ∂P, sample ∈ S → d sample = e sample := by
    filter_upwards [hAction] with sample hA
    intro hSurv
    have hYPrefix : ∀ t ≤ T, Y t sample =
        ginibreHamiltonianOUReferenceProcess n ((n : ℝ)^2) z B t sample := by
      intro t ht
      rw [hStopped, min_eq_left (by rw [hEnd sample hSurv]; exact ht)]
    have hAeq := bakryEmeryGibbsOUReference_action_of_prefix W z B T sample Y hYPrefix
    have hd := hA T (by rw [hEnd sample hSurv])
    change ENNReal.ofReal (D sample) =
      ENNReal.ofReal (Real.exp (bakryEmeryGibbsRelativePotential W z))*
      bakryEmeryGibbsOUAction W T T.property (O sample)
    dsimp only [D, F]
    rw [hd, ENNReal.ofReal_mul (Real.exp_pos _).le]
    change _ = ENNReal.ofReal (Real.exp (bakryEmeryGibbsRelativePotential W z))*
      bakryEmeryGibbsOUAction W T T.property
        (ginibreHamiltonianOUReferenceHorizon n ((n : ℝ)^2) z B T sample)
    rw [hAeq]
    congr 1
    unfold gradientPathReversalWeight
    simp only [hY0, Real.toNNReal_zero, Real.toNNReal_coe]
  have hIndicator : S.indicator e = fun sample =>
      ENNReal.ofReal (Real.exp (bakryEmeryGibbsRelativePotential W z))*
        bakryEmeryGibbsKilledOUAction W T R (O sample) := by
    funext sample
    by_cases hmem : sample ∈ S
    · have hg : O sample ∈ bakryEmeryGibbsCompactSurvival n T R := hmem
      simp only [indicator_of_mem hmem, bakryEmeryGibbsKilledOUAction, indicator_of_mem hg, e]
    · have hg : O sample ∉ bakryEmeryGibbsCompactSurvival n T R := hmem
      simp only [indicator_of_notMem hmem, bakryEmeryGibbsKilledOUAction, indicator_of_notMem hg,
        mul_zero]
  rw [← hFlowLaw, Measure.restrict_map hCm hG, hSetEq]
  have hMap := actualTiltedKilledPath_map P d e S hS C O
    (Eventually.of_forall hCO) hde
  rw [hIndicator] at hMap
  exact hMap

/-- Actual fixed-initial killed identity on the full configuration domain,
including arbitrary killing radii and initial states outside the ball. -/
theorem bakryEmeryGibbs_fixed_initial_killed_law {Ω : Type*} [MeasurableSpace Ω]
    {n : ℕ} (hn : 0 < n) (W : Configuration n → ℝ) (hW : ContDiff ℝ 2 W)
    (κ : ℝ) (hκ : 0 < κ)
    (hc : ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin n × Fin 2) =>
      W ((configurationEuclideanEquiv n).symm x)-κ/2*‖x‖^2))
    (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i sample t => B i t sample) P)
    (z : Configuration n) (T : ℝ≥0) (hT : 0 < T) (R : ℝ) :
    (P.map (fun sample => bakryEmeryGibbsPath W hW κ hκ hc T
      (z, bakryEmeryOriginalCompactDriver n B T sample))).restrict
        (bakryEmeryGibbsCompactSurvival n T R) =
      (P.withDensity (fun sample =>
        ENNReal.ofReal (Real.exp (bakryEmeryGibbsRelativePotential W z)) *
        bakryEmeryGibbsKilledOUAction W T R
          (ginibreHamiltonianOUReferenceHorizon n ((n : ℝ)^2) z B T sample))).map
            (ginibreHamiltonianOUReferenceHorizon n ((n : ℝ)^2) z B T) := by
  classical
  by_cases hR : ‖z‖ < R
  · exact bakryEmeryGibbs_fixed_initial_killed_law_inside hn W hW κ hκ hc P B hB hind z T hT R hR
  · let X := fun sample => bakryEmeryGibbsPath W hW κ hκ hc T
      (z, bakryEmeryOriginalCompactDriver n B T sample)
    let O := ginibreHamiltonianOUReferenceHorizon n ((n : ℝ)^2) z B T
    let G := bakryEmeryGibbsCompactSurvival n T R
    have hXm : Measurable X := (bakryEmeryGibbsPath_measurable W hW κ hκ hc T).comp
      (measurable_const.prodMk (bakryEmeryOriginalCompactDriver_measurable n B P hB T))
    have hG : MeasurableSet G := bakryEmeryGibbsCompactSurvival_measurableSet n T R
    have hXnot (sample : Ω) : X sample ∉ G := by
      intro h
      have hz := (bakryEmeryGibbsCompactSurvival_mem n T R (X sample)).mp h
        ⟨0, ⟨le_rfl, T.property⟩⟩
      have hN0 : bakryEmeryOriginalCompactDriver n B T sample ⟨0, ⟨le_rfl, T.property⟩⟩ = 0 := by
        change (configurationEuclideanEquiv n)
          ((ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) sample).val 0) = 0
        rw [(ginibreBrownianFullContinuousNoise n B ((n : ℝ)^2) sample).property, map_zero]
      simp only [X, bakryEmeryGibbsPath_initial, hN0, map_zero, add_zero] at hz
      exact hR hz
    have hOnot (sample : Ω) : O sample ∉ G := by
      intro h
      have hz := (bakryEmeryGibbsCompactSurvival_mem n T R (O sample)).mp h
        ⟨0, ⟨le_rfl, T.property⟩⟩
      have hzero := ginibreHamiltonianOUReferenceProcess_zero n ((n : ℝ)^2) z B sample
      have hOz : O sample ⟨0, ⟨le_rfl, T.property⟩⟩ = z :=
        (killedLaw_referenceHorizon_apply n z B T sample _).trans
          ((congrArg (fun s => ginibreHamiltonianOUReferenceProcess n ((n : ℝ) ^ 2) z B s sample)
            Real.toNNReal_zero).trans hzero)
      rw [hOz] at hz
      exact hR hz
    have hPre : X ⁻¹' G = ∅ := eq_empty_iff_forall_notMem.mpr hXnot
    have hLeft : (P.map X).restrict G = 0 := by
      apply Measure.restrict_eq_zero.mpr
      rw [Measure.map_apply hXm hG, hPre, measure_empty]
    have hZero : (fun sample => ENNReal.ofReal (Real.exp (bakryEmeryGibbsRelativePotential W z)) *
        bakryEmeryGibbsKilledOUAction W T R (O sample)) = 0 := by
      funext sample
      have hh : O sample ∉ bakryEmeryGibbsCompactSurvival n T R := hOnot sample
      simp only [bakryEmeryGibbsKilledOUAction, indicator_of_notMem hh, mul_zero, Pi.zero_apply]
    change (P.map X).restrict G = (P.withDensity _).map O
    rw [hLeft, hZero]
    simp

end
end GinibrePoincare
