/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
module

public import LeanPool.Vlasov.OT.CharacteristicFlow
import Mathlib.Algebra.Order.Ring.Star

/-!
# Local well-posedness for the Vlasov equation

The Picard fixed point supplies the local characteristic flow, its moment bound,
and the local Lagrangian solution. Continuation and stability use these results
without retaining their elaboration in the same compilation unit.
-/

@[expose] public section

namespace Vlasov

open MeasureTheory ENNReal

/-! ## §9  Theorem (Existence and uniqueness for Vlasov)   (tex: thm:vlasov-wp) -/
-- The proof composes directly with the characteristic-flow infrastructure
-- developed in `LeanPool/Vlasov/OT/CharacteristicFlow.lean`: `exists_vlasov_characteristicFlow`,
-- `flow_distance_growth_bound`, and
-- `vlasovSolutionViaPushforward_isLagrangianVlasovSolution`.  The
-- `HasFiniteFirstMoment` predicate remains in `Basic.lean`.

/-- **Project-internal: AEMeasurability of the Vlasov characteristic flow's
joint map** `z ↦ (charX s z, charV s z)` on the window `Icc 0 T`.

The window-restricted statement (`Icc 0 T`) is exactly what is needed: the
Vlasov flow satisfies `HasDerivAt` only on `Ioo 0 T` (off-window it is
uncontrolled `Classical.choose` data), and the sole consumer applies this
only at `clampToIcc T s ∈ Icc 0 T`.  On the window the joint flow's
measurability follows from `charFlow_measurable_via_gronwall` (genuine
`Measurable`, via the boundary bundle through
`characteristicFlow_boundary_regularity`).

**In-project consumer**: `vlasovWellPosedness_local_picard_fixedPointFlow`'s
AEMeasurable conjunct, applied at clamp times `clampToIcc T s ∈ Icc 0 T`. -/
private lemma picardCharFlow_aemeasurable
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    {T : ℝ} (hT : 0 ≤ T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (hbdry : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) (Set.Icc 0 T) t)
    (μ : Measure (PhaseSpace d)) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) μ := by
  intro s hs
  obtain ⟨h_init, h_cont, h_deriv⟩ :=
    characteristicFlow_boundary_regularity gradW ρ charX charV T hT hflow hbdry
  exact (charFlow_measurable_via_gronwall gradW L hL ρ h_int charX charV T hT
    h_init h_cont h_deriv s hs).aemeasurable

/-- **Contraction-input helper**: from a flow's exposed facts (`IsCharacteristicFlowOn`
on `Ioo` + the boundary bundle on `Icc` — the `Phi_step_envelope` output shape)
against a curve `ν`, derive the six per-`z` regularity facts that
`Phi_supW1_contraction` consumes.  Chains `characteristicFlow_boundary_regularity`
(→ init/cont/deriv, the last three EXACT), `charFlow_measurable_via_gronwall`
(→ AEMeasurable), and `flow_distance_growth_bound_on` (→ growth bound, integrated
to the two integrability facts). -/
private lemma envelopeStep_contractionInputs {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d) (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 ≤ T) {m : ℝ → ℝ}
    (ν : VlasovMeasureCurve d T m)
    (Mbar : ℝ) (hMbar_nn : 0 ≤ Mbar)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ν.extend t) ≤ Mbar)
    (cX cV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow : IsCharacteristicFlowOn gradW ν.extend cX cV (Set.Ioo 0 T) Set.univ)
    (hbdry : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => cX s z) (cV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => cV s z)
          (-(convolveFunctionMeasure gradW (ν.extend t) (cX t z))) (Set.Icc 0 T) t)
    (h_int_ext : ∀ t (x : PhysSpace d),
        Integrable (fun y => gradW (x - y)) (ν.extend t)) :
    (∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (fun z : PhaseSpace d => cX t z) f₀) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun z : PhaseSpace d => ‖cX t z‖) f₀) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => cX t z) f₀)) ∧
    (∀ z : PhaseSpace d, (cX 0 z, cV 0 z) = z) ∧
    (∀ z : PhaseSpace d,
      ContinuousOn (fun s => (cX s z, cV s z)) (Set.Icc (0 : ℝ) T)) ∧
    (∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (cX s' z, cV s' z))
        (vlasovVectorField gradW (ν.extend) s (cX s z, cV s z))
        (Set.Ici s) s) := by
  have : ∀ t, IsProbabilityMeasure (ν.extend t) := VlasovMeasureCurve.extend_isProb ν
  obtain ⟨h_init, h_cont, h_deriv⟩ :=
    characteristicFlow_boundary_regularity gradW ν.extend cX cV T hT hflow hbdry
  have h_meas : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => cX t z) f₀ := by
    have h_meas_Icc := charFlow_measurable_via_gronwall gradW L hL ν.extend h_int_ext
      cX cV T hT h_init h_cont h_deriv
    exact fun t ht => (measurable_fst.comp (h_meas_Icc t ht)).aemeasurable
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL ν.extend cX cV T hT
      h_init h_cont h_deriv Mbar hMbar_nn hM_ρ
      (fun t _ => VlasovMeasureCurve.extend_yIntegrable hT ν t) h_int_ext
  have h_int_charX : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖cX t z‖) f₀ := by
    intro t ht
    have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
      have h1 : Integrable (fun z : PhaseSpace d => C_T * ‖z‖) f₀ := h_f₀_int.const_mul C_T
      have h2 : Integrable (fun _ : PhaseSpace d => C_T) f₀ := integrable_const _
      have h_eq : (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) = fun z => C_T * ‖z‖ + C_T := by
        funext z; ring
      rw [h_eq]; exact h1.add h2
    refine h_dom_int.mono' (h_meas t ht).norm.aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact le_trans (norm_fst_le (cX t z, cV t z)) (h_growth t ht z)
  have h_yint_Phi : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => cX t z) f₀) := by
    intro t ht
    rw [integrable_map_measure continuous_norm.aestronglyMeasurable (h_meas t ht)]
    exact h_int_charX t ht
  exact ⟨h_meas, h_int_charX, h_yint_Phi, h_init, h_cont, h_deriv⟩

/-- Lipschitz growth of the force plus a first moment of the measure make the
shifted force integrable.  The workhorse integrability fact behind every
`convolveFunctionMeasure` estimate. -/
lemma integrable_gradW_shift
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (μ : Measure (PhysSpace d)) [MeasureTheory.IsFiniteMeasure μ]
    (h_yint : Integrable (fun y : PhysSpace d => ‖y‖) μ)
    (xp : PhysSpace d) :
    Integrable (fun y => gradW (xp - y)) μ := by
  have h_aesm : AEStronglyMeasurable (fun y : PhysSpace d => gradW (xp - y)) μ :=
    (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have h_dom : ∀ y : PhysSpace d, ‖gradW (xp - y)‖ ≤
      ‖gradW 0‖ + (L : ℝ) * ‖xp‖ + (L : ℝ) * ‖y‖ := by
    intro y
    have hd := hL.dist_le_mul (xp - y) 0
    simp only [dist_eq_norm, sub_zero] at hd
    have h_tri : ‖gradW (xp - y)‖ ≤ ‖gradW 0‖ + ‖gradW (xp - y) - gradW 0‖ := by
      have := norm_add_le (gradW (xp - y) - gradW 0) (gradW 0)
      simp only [sub_add_cancel] at this; linarith
    have h_sub_le : ‖xp - y‖ ≤ ‖xp‖ + ‖y‖ := norm_sub_le xp y
    have h_mul := mul_le_mul_of_nonneg_left h_sub_le L.coe_nonneg
    linarith
  have h_dom_int : Integrable
      (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖xp‖ + (L : ℝ) * ‖y‖) μ := by
    have h_eq : (fun y : PhysSpace d => ‖gradW 0‖ + (L : ℝ) * ‖xp‖ + (L : ℝ) * ‖y‖) =
                fun y => (‖gradW 0‖ + (L : ℝ) * ‖xp‖) + (L : ℝ) * ‖y‖ := by funext y; ring
    rw [h_eq]; exact (integrable_const _).add (h_yint.const_mul _)
  exact h_dom_int.mono' h_aesm (Filter.Eventually.of_forall fun y => h_dom y)

/-- `LocalSmallnessContraction L T` IS the Grönwall contraction factor
`gronwallBound 0 (max 1 L) L T < 1`, after unfolding both definitions. -/
lemma LocalSmallnessContraction.gronwallBound_lt_one
    {L : NNReal} {T : ℝ} (hTL_con : LocalSmallnessContraction L T) :
    gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L : ℝ) T < 1 := by
  have hK_pos : (0 : ℝ) < ((max 1 L : NNReal) : ℝ) := by
    have : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
      rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _
    linarith
  have hK_ne : ((max 1 L : NNReal) : ℝ) ≠ 0 := ne_of_gt hK_pos
  rw [gronwallBound_of_K_ne_0 hK_ne]
  simp only [zero_mul, zero_add]
  have h_eq : (L : ℝ) / ((max 1 L : NNReal) : ℝ) *
      (Real.exp (((max 1 L : NNReal) : ℝ) * T) - 1) =
      (L : ℝ) * (Real.exp ((max 1 (L : ℝ)) * T) - 1) / (max 1 (L : ℝ)) := by
    rw [NNReal.coe_max, NNReal.coe_one]
    ring
  rw [h_eq]
  exact hTL_con

/-- The Picard sequence of the local fixed-point construction, with its exposed
per-step flows and the geometric contraction bound.  Extracted from
`vlasovWellPosedness_local_picard_fixedPointFlow`; the parameters `q` (the
contraction factor) and `D₀` (the initial `W₁`-input bound) are threaded with
their defining equations so the parent's `let`-definitions supply `rfl`. -/
private lemma vlasovWellPosedness_local_picard_sequence
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hTL_PL : LocalSmallnessPLBuffer L T)
    (m : ℝ → ℝ) (hm_mono : MonotoneOn m (Set.Icc 0 T))
    (hm_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ m t)
    (hm_inv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      gronwallBound (∫ z, ‖z‖ ∂f₀) (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * m t) t ≤ m t)
    (hMbar_nn : 0 ≤ m T) (hMbar_mono : ∀ t ∈ Set.Icc (0 : ℝ) T, m t ≤ m T)
    (hμ₀_prob : IsProbabilityMeasure (spatialMarginal f₀))
    (hμ₀_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal f₀))
    (hμ₀_le_m : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal f₀) ≤ m t)
    (q : ℝ) (hq_nn : 0 ≤ q)
    (hq_def : q = gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L : ℝ) T)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀) (hD₀_def : D₀ = 2 * (m T)) :
    ∃ (x : ℕ → VlasovMeasureCurve d T m)
      (charXs charVs : ℕ → ℝ → PhaseSpace d → PhysSpace d),
      (∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
            ENNReal.ofReal (q ^ k * D₀)) ∧
      (∀ k,
        IsCharacteristicFlowOn gradW (x k).extend (charXs k) (charVs k)
          (Set.Ioo 0 T) Set.univ ∧
        (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
          HasDerivWithinAt (fun s => charXs k s z) (charVs k t z) (Set.Icc 0 T) t ∧
          HasDerivWithinAt (fun s => charVs k s z)
            (-(convolveFunctionMeasure gradW ((x k).extend t) (charXs k t z)))
            (Set.Icc 0 T) t) ∧
        (∀ t ∈ Set.Icc (0 : ℝ) T,
          (x (k + 1)).ρ t
            = Measure.map (fun z : PhaseSpace d => charXs k t z) f₀)) := by
  have h_int_ext_gen : ∀ (ν : VlasovMeasureCurve d T m) (t : ℝ) (xp : PhysSpace d),
      Integrable (fun y => gradW (xp - y)) (ν.extend t) := fun ν t xp =>
    integrable_gradW_shift gradW L hL (ν.extend t)
      (VlasovMeasureCurve.extend_yIntegrable hT.le ν t) xp
  have step : ∀ (ν : VlasovMeasureCurve d T m),
      ∃ (σ : VlasovMeasureCurve d T m) (cX cV : ℝ → PhaseSpace d → PhysSpace d),
        (∀ t ∈ Set.Icc (0 : ℝ) T, σ.ρ t = Measure.map (fun z => cX t z) f₀) ∧
        IsCharacteristicFlowOn gradW ν.extend cX cV (Set.Ioo 0 T) Set.univ ∧
        (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
          HasDerivWithinAt (fun s => cX s z) (cV t z) (Set.Icc 0 T) t ∧
          HasDerivWithinAt (fun s => cV s z)
            (-(convolveFunctionMeasure gradW (ν.extend t) (cX t z))) (Set.Icc 0 T) t) := by
    intro ν
    obtain ⟨cX, cV, hflow, hbdry, σ, hσ⟩ :=
      Phi_step_envelope W gradW hgradW L hL f₀ hf₀_int hT.le m hm_mono hm_nn hm_inv hTL_PL
        ν (h_int_ext_gen ν)
    exact ⟨σ, cX, cV, hσ, hflow, hbdry⟩
  have hμ₀_prob_inst : IsProbabilityMeasure (spatialMarginal f₀) := hμ₀_prob
  let base : VlasovMeasureCurve d T m := constantCurve (spatialMarginal f₀) hμ₀_int hμ₀_le_m
  let x : ℕ → VlasovMeasureCurve d T m :=
    fun n => Nat.rec base (fun _ ν => Classical.choose (step ν)) n
  let charXs : ℕ → ℝ → PhaseSpace d → PhysSpace d :=
    fun k => Classical.choose (Classical.choose_spec (step (x k)))
  let charVs : ℕ → ℝ → PhaseSpace d → PhysSpace d :=
    fun k => Classical.choose (Classical.choose_spec (Classical.choose_spec (step (x k))))
  have hx_succ : ∀ k, x (k + 1) = Classical.choose (step (x k)) := fun _ => rfl
  have hspec : ∀ k,
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        (Classical.choose (step (x k))).ρ t = Measure.map (fun z => charXs k t z) f₀) ∧
      IsCharacteristicFlowOn gradW (x k).extend (charXs k) (charVs k)
        (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charXs k s z) (charVs k t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charVs k s z)
          (-(convolveFunctionMeasure gradW ((x k).extend t) (charXs k t z)))
          (Set.Icc 0 T) t) :=
    fun k => Classical.choose_spec
      (Classical.choose_spec (Classical.choose_spec (step (x k))))
  have h_flow : ∀ k,
      IsCharacteristicFlowOn gradW (x k).extend (charXs k) (charVs k)
        (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charXs k s z) (charVs k t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charVs k s z)
          (-(convolveFunctionMeasure gradW ((x k).extend t) (charXs k t z)))
          (Set.Icc 0 T) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        (x (k + 1)).ρ t = Measure.map (fun z : PhaseSpace d => charXs k t z) f₀) := by
    intro k
    obtain ⟨hpush, hcf, hbd⟩ := hspec k
    refine ⟨hcf, hbd, fun t ht => ?_⟩
    rw [hx_succ k]; exact hpush t ht
  have hCI : ∀ k,
      (∀ t ∈ Set.Icc (0 : ℝ) T, AEMeasurable (fun z : PhaseSpace d => charXs k t z) f₀) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun z : PhaseSpace d => ‖charXs k t z‖) f₀) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => charXs k t z) f₀)) ∧
      (∀ z : PhaseSpace d, (charXs k 0 z, charVs k 0 z) = z) ∧
      (∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charXs k s z, charVs k s z)) (Set.Icc (0 : ℝ) T)) ∧
      (∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun s' => (charXs k s' z, charVs k s' z))
          (vlasovVectorField gradW ((x k).extend) s (charXs k s z, charVs k s z))
          (Set.Ici s) s) :=
    fun k => envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le (x k) (m T) hMbar_nn
      (fun t _ => le_trans (VlasovMeasureCurve.extend_hasMoment hT.le (x k) t)
        (hMbar_mono (clampToIcc T t) (clampToIcc_mem hT.le t)))
      (charXs k) (charVs k) (h_flow k).1 (h_flow k).2.1 (h_int_ext_gen (x k))
  have hK_ne : ((max 1 L : NNReal) : ℝ) ≠ 0 := by
    have h1 : (1:ℝ) ≤ ((max 1 L : NNReal):ℝ) := by
      rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _
    linarith
  have hq_scale : ∀ D : ℝ,
      gronwallBound 0 ((max 1 L : NNReal):ℝ) ((L:ℝ)*D) T = D * q := by
    intro D
    rw [hq_def, gronwallBound_of_K_ne_0 hK_ne, gronwallBound_of_K_ne_0 hK_ne]; ring
  have hPext : ∀ (ν : VlasovMeasureCurve d T m) (t : ℝ),
      IsProbabilityMeasure (ν.extend t) :=
    fun ν => VlasovMeasureCurve.extend_isProb ν
  have h_contract : ∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
      ENNReal.ofReal (q ^ k * D₀) := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, one_mul]
      rw [hD₀_def]
      exact supW1On_le_two_moment_of_VlasovMeasureCurve (m T) hMbar_mono (x 0) (x 1)
    | succ k ih =>
      set D : ℝ := q ^ k * D₀ with hD_def
      have hD_nn : 0 ≤ D := mul_nonneg (pow_nonneg hq_nn k) hD₀_nn
      have he : ∀ (ν : VlasovMeasureCurve d T m) s, s ∈ Set.Icc (0 : ℝ) T → ν.extend s = ν.ρ s := by
        intro ν s hs
        unfold VlasovMeasureCurve.extend clampToIcc; congr 1
        rw [min_eq_left hs.2, max_eq_right hs.1]
      have h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T,
          wasserstein1 ((x k).extend s) ((x (k+1)).extend s) ≠ ⊤ := by
        intro s hs
        rw [he (x k) s hs, he (x (k+1)) s hs]
        have := (x k).isProb s; have := (x (k+1)).isProb s
        exact wasserstein1_ne_top_of_finite_moment _ _
          ((x k).yIntegrable s hs) ((x (k+1)).yIntegrable s hs)
      have h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T,
          (wasserstein1 ((x k).extend s) ((x (k+1)).extend s)).toReal ≤ D := by
        intro s hs
        rw [he (x k) s hs, he (x (k+1)) s hs]
        have h_le : wasserstein1 ((x k).ρ s) ((x (k+1)).ρ s)
            ≤ ENNReal.ofReal D :=
          le_trans (wasserstein1_le_supW1On _ _ _ s hs) ih
        have h_ne : wasserstein1 ((x k).ρ s) ((x (k+1)).ρ s) ≠ ⊤ := by
          have := (x k).isProb s; have := (x (k+1)).isProb s
          exact wasserstein1_ne_top_of_finite_moment _ _
            ((x k).yIntegrable s hs) ((x (k+1)).yIntegrable s hs)
        calc (wasserstein1 ((x k).ρ s) ((x (k+1)).ρ s)).toReal
            ≤ (ENNReal.ofReal D).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_le
          _ = D := ENNReal.toReal_ofReal hD_nn
      have h_contr := @Phi_supW1_contraction d gradW L hL ((x k).extend) ((x (k+1)).extend)
        (hPext (x k)) (hPext (x (k+1)))
        (h_int_ext_gen (x k)) (h_int_ext_gen (x (k+1))) T hT.le D hD_nn h_W1_fin h_W1_bound
        (charXs k) (charVs k) (charXs (k+1)) (charVs (k+1)) f₀ _
        (hCI k).1 (hCI (k+1)).1 (hCI k).2.1 (hCI (k+1)).2.1
        (hCI k).2.2.1 (hCI (k+1)).2.2.1 (hCI k).2.2.2.1 (hCI (k+1)).2.2.2.1
        (hCI k).2.2.2.2.1 (hCI (k+1)).2.2.2.2.1 (hCI k).2.2.2.2.2 (hCI (k+1)).2.2.2.2.2
      rw [hq_scale D] at h_contr
      have h_supW1_eq : supW1On (Set.Icc 0 T) (x (k+1)).ρ (x (k+1+1)).ρ
          = supW1On (Set.Icc 0 T)
              (fun t => Measure.map (fun z => charXs k t z) f₀)
              (fun t => Measure.map (fun z => charXs (k+1) t z) f₀) := by
        unfold supW1On
        exact iSup_congr fun t => iSup_congr fun ht => by
          rw [(h_flow k).2.2 t ht, (h_flow (k+1)).2.2 t ht]
      have hDq : D * q = q ^ (k + 1) * D₀ := by rw [hD_def, pow_succ]; ring
      rw [hDq] at h_contr
      have h_ne_top : supW1On (Set.Icc 0 T)
          (fun t => Measure.map (fun z => charXs k t z) f₀)
          (fun t => Measure.map (fun z => charXs (k+1) t z) f₀) ≠ ⊤ := by
        rw [← h_supW1_eq]
        exact supW1On_ne_top_of_VlasovMeasureCurve (m T) hMbar_mono (x (k+1)) (x (k+1+1))
      have h_pow_nn : 0 ≤ q ^ (k + 1) * D₀ := mul_nonneg (pow_nonneg hq_nn _) hD₀_nn
      rw [h_supW1_eq]
      rw [← ENNReal.toReal_le_toReal h_ne_top ENNReal.ofReal_ne_top,
          ENNReal.toReal_ofReal h_pow_nn]
      exact h_contr
  exact ⟨x, charXs, charVs, h_contract, h_flow⟩

/-- Pointwise contraction of the Picard step between an iterate and the limit
curve: the pushforwards under the two flows are `D·q`-close whenever the curves
are uniformly `D`-close in `W₁`.  Wraps `Phi_pointwise_contraction` +
`gronwallBound` monotonicity for a single curve pair. -/
private lemma picardLimit_flow_pointwise_contraction
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (m : ℝ → ℝ) (hMbar_nn : 0 ≤ m T)
    (hMbar_mono : ∀ t ∈ Set.Icc (0 : ℝ) T, m t ≤ m T)
    (ν ρl : VlasovMeasureCurve d T m)
    (cX cV charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow_ν : IsCharacteristicFlowOn gradW ν.extend cX cV (Set.Ioo 0 T) Set.univ)
    (hbdry_ν : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => cX s z) (cV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => cV s z)
        (-(convolveFunctionMeasure gradW (ν.extend t) (cX t z))) (Set.Icc 0 T) t)
    (hflow_l : IsCharacteristicFlowOn gradW ρl.extend charX charV (Set.Ioo 0 T) Set.univ)
    (hbdry_l : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρl.extend t) (charX t z))) (Set.Icc 0 T) t)
    (D : ℝ) (hD_nn : 0 ≤ D)
    (h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T, wasserstein1 (ν.extend s) (ρl.extend s) ≠ ⊤)
    (h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (wasserstein1 (ν.extend s) (ρl.extend s)).toReal ≤ D)
    (q : ℝ) (hq_def : q = gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L : ℝ) T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      (wasserstein1 (Measure.map (fun z => cX t z) f₀)
                    (Measure.map (fun z => charX t z) f₀)).toReal ≤ D * q := by
  have hK_ge1 : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
    rw [NNReal.coe_max, NNReal.coe_one]; exact le_max_left _ _
  have hK_ne : ((max 1 L : NNReal) : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hK_pos : (0 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by linarith
  have hMm : ∀ (μ : VlasovMeasureCurve d T m), ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(μ.extend t) ≤ m T :=
    fun μ t _ => le_trans (VlasovMeasureCurve.extend_hasMoment hT.le μ t)
      (hMbar_mono (clampToIcc T t) (clampToIcc_mem hT.le t))
  have h_int_ν : ∀ t (xp : PhysSpace d),
      Integrable (fun y => gradW (xp - y)) (ν.extend t) := fun t xp =>
    integrable_gradW_shift gradW L hL (ν.extend t)
      (VlasovMeasureCurve.extend_yIntegrable hT.le ν t) xp
  have h_int_l : ∀ t (xp : PhysSpace d),
      Integrable (fun y => gradW (xp - y)) (ρl.extend t) := fun t xp =>
    integrable_gradW_shift gradW L hL (ρl.extend t)
      (VlasovMeasureCurve.extend_yIntegrable hT.le ρl t) xp
  have hCI_ν := envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le ν
    (m T) hMbar_nn (hMm ν) cX cV hflow_ν hbdry_ν h_int_ν
  have hCI_l := envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le ρl
    (m T) hMbar_nn (hMm ρl) charX charV hflow_l hbdry_l h_int_l
  have hq_scale : gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L:ℝ) * D) T = D * q := by
    rw [hq_def, gronwallBound_of_K_ne_0 hK_ne, gronwallBound_of_K_ne_0 hK_ne]; ring
  intro t ht
  have hpt := @Phi_pointwise_contraction d gradW L hL (ν.extend) (ρl.extend)
    (VlasovMeasureCurve.extend_isProb ν) (VlasovMeasureCurve.extend_isProb ρl)
    h_int_ν h_int_l T hT.le D hD_nn h_W1_fin h_W1_bound
    cX cV charX charV f₀ _
    hCI_ν.1 hCI_l.1 hCI_ν.2.1 hCI_l.2.1
    hCI_ν.2.2.2.1 hCI_l.2.2.2.1 hCI_ν.2.2.2.2.1 hCI_l.2.2.2.2.1
    hCI_ν.2.2.2.2.2 hCI_l.2.2.2.2.2 t ht
  have h_mono : gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L:ℝ) * D) t
      ≤ gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L:ℝ) * D) T :=
    gronwallBound_mono (le_refl 0) (mul_nonneg L.coe_nonneg hD_nn) hK_pos ht.2
  rw [hq_scale] at h_mono
  exact le_trans hpt h_mono

/-- The Picard fixed-point equation at the limit: if the iterates converge to the
limit curve in `W₁` and each step's pushforward is `Dₙ·q`-close to the limit
flow's pushforward with `Dₙ·q → 0`, the limit curve equals the limit flow's
pushforward.  Triangle through the iterates + the `W₁` separation lemma. -/
private lemma picardLimit_fixed_point_eq
    {d : ℕ} [NeZero d]
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    {T : ℝ}
    (m : ℝ → ℝ) (x : ℕ → VlasovMeasureCurve d T m) (ρl : VlasovMeasureCurve d T m)
    (charXs : ℕ → ℝ → PhaseSpace d → PhysSpace d)
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (h_push : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) T,
      (x (n + 1)).ρ t = Measure.map (fun z : PhaseSpace d => charXs n t z) f₀)
    (h_tendsto : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) (ρl.ρ t)) Filter.atTop (nhds 0))
    (h_aem_n : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charXs n t z) f₀)
    (h_aem_lim : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (h_mom_n : ∀ n, ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => charXs n t z) f₀))
    (h_mom_lim : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (Measure.map (fun z => charX t z) f₀))
    (Dn : ℕ → ℝ) (q : ℝ)
    (hDnq_tendsto : Filter.Tendsto (fun n => Dn n * q) Filter.atTop (nhds 0))
    (h_term2 : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      (wasserstein1 (Measure.map (fun z => charXs n t z) f₀)
                    (Measure.map (fun z => charX t z) f₀)).toReal ≤ Dn n * q) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ρl.ρ t = Measure.map (fun z => charX t z) f₀ := by
  intro t ht
  have hP1 : IsProbabilityMeasure (ρl.ρ t) := ρl.isProb t
  have hP2 : IsProbabilityMeasure (Measure.map (fun z => charX t z) f₀) :=
    (Measure.isProbabilityMeasure_map_iff (h_aem_lim t ht)).mpr inferInstance
  refine (wasserstein1_eq_zero_iff_measure_eq (ρl.ρ t)
    (Measure.map (fun z => charX t z) f₀)).mp ?_
  have h_le_seq : ∀ n, wasserstein1 (ρl.ρ t) (Measure.map (fun z => charX t z) f₀)
      ≤ wasserstein1 ((x (n+1)).ρ t) (ρl.ρ t) + ENNReal.ofReal (Dn n * q) := by
    intro n
    have h_mid : (x (n+1)).ρ t = Measure.map (fun z => charXs n t z) f₀ := h_push n t ht
    calc wasserstein1 (ρl.ρ t) (Measure.map (fun z => charX t z) f₀)
        ≤ wasserstein1 (ρl.ρ t) ((x (n+1)).ρ t)
            + wasserstein1 ((x (n+1)).ρ t) (Measure.map (fun z => charX t z) f₀) :=
          wasserstein1_triangle _ _ _
      _ = wasserstein1 ((x (n+1)).ρ t) (ρl.ρ t)
            + wasserstein1 ((x (n+1)).ρ t) (Measure.map (fun z => charX t z) f₀) := by
          rw [wasserstein1_comm (ρl.ρ t) ((x (n+1)).ρ t)]
      _ ≤ wasserstein1 ((x (n+1)).ρ t) (ρl.ρ t) + ENNReal.ofReal (Dn n * q) := by
          gcongr
          rw [h_mid]
          have h_fin : wasserstein1 (Measure.map (fun z => charXs n t z) f₀)
              (Measure.map (fun z => charX t z) f₀) ≠ ⊤ := by
            have : IsProbabilityMeasure (Measure.map (fun z => charXs n t z) f₀) :=
              (Measure.isProbabilityMeasure_map_iff (h_aem_n n t ht)).mpr inferInstance
            exact wasserstein1_ne_top_of_finite_moment _ _
              (h_mom_n n t ht) (h_mom_lim t ht)
          rw [← ENNReal.ofReal_toReal h_fin]
          exact ENNReal.ofReal_le_ofReal (h_term2 n t ht)
  have hA : Filter.Tendsto (fun n => wasserstein1 ((x (n+1)).ρ t) (ρl.ρ t))
      Filter.atTop (nhds 0) :=
    (h_tendsto t ht).comp (Filter.tendsto_add_atTop_nat 1)
  have hB : Filter.Tendsto (fun n => ENNReal.ofReal (Dn n * q)) Filter.atTop (nhds 0) := by
    have := (ENNReal.continuous_ofReal.tendsto 0).comp hDnq_tendsto
    simpa [Function.comp_def] using this
  have h_seq : Filter.Tendsto
      (fun n => wasserstein1 ((x (n+1)).ρ t) (ρl.ρ t) + ENNReal.ofReal (Dn n * q))
      Filter.atTop (nhds 0) := by
    have := hA.add hB
    simpa using this
  exact le_antisymm (ge_of_tendsto' h_seq h_le_seq) (zero_le)

/-- Bundle the self-consistent Picard-limit flow, CLAMPED to the window, into the
seven-conjunct conclusion of `vlasovWellPosedness_local_picard_fixedPointFlow`.
The raw flow is controlled only on `[0, T]`; clamping (`clampToIcc`) makes every
universal-in-`s` conjunct reduce to the window, where the clamp is the identity. -/
private lemma picardFlow_clamp_bundle
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d))
    {T : ℝ} (hT : 0 < T)
    (m : ℝ → ℝ) (hMbar_nn : 0 ≤ m T)
    (hMbar_mono : ∀ t ∈ Set.Icc (0 : ℝ) T, m t ≤ m T)
    (ρ_lim : VlasovMeasureCurve d T m)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow_on_ρlim : IsCharacteristicFlowOn gradW ρ_lim.extend charX charV
      (Set.Ioo 0 T) Set.univ)
    (h_boundary_ρlim : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρ_lim.extend t) (charX t z))) (Set.Icc 0 T) t)
    (h_int_ρ_lim : ∀ t (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (ρ_lim.extend t))
    (h_self_consist : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ρ_lim.extend t =
      spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) :
    ∃ (charX' charV' : ℝ → PhaseSpace d → PhysSpace d) (M_ρ : ℝ), 0 ≤ M_ρ ∧
      IsCharacteristicFlowOn gradW
        (fun t => spatialMarginal (vlasovSolutionViaPushforward charX' charV' f₀ t))
        charX' charV' (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX' s z) (charV' t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV' s z)
          (-(convolveFunctionMeasure gradW
              (spatialMarginal (vlasovSolutionViaPushforward charX' charV' f₀ t))
              (charX' t z)))
          (Set.Icc 0 T) t) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX' charV' f₀ s)) ≤ M_ρ) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y : PhysSpace d => ‖y‖)
          (spatialMarginal (vlasovSolutionViaPushforward charX' charV' f₀ s))) ∧
      (∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX' charV' f₀ s)) x)) ∧
      (∀ s, AEMeasurable (fun z : PhaseSpace d => (charX' s z, charV' s z)) f₀) ∧
      (∀ s (x : PhysSpace d),
        Integrable (fun y => gradW (x - y))
          (spatialMarginal (vlasovSolutionViaPushforward charX' charV' f₀ s))) := by
  have hclamp_id : ∀ s ∈ Set.Icc (0 : ℝ) T, clampToIcc T s = s := fun s hs => by
    unfold clampToIcc; rw [min_eq_left hs.2, max_eq_right hs.1]
  have hclamp0 : clampToIcc T 0 = 0 := hclamp_id 0 ⟨le_refl 0, hT.le⟩
  have h_rho_clamp : ∀ s : ℝ,
      spatialMarginal (vlasovSolutionViaPushforward
        (fun s' z => charX (clampToIcc T s') z)
        (fun s' z => charV (clampToIcc T s') z) f₀ s) =
      ρ_lim.extend (clampToIcc T s) := by
    intro s
    have h1 : spatialMarginal (vlasovSolutionViaPushforward
        (fun s' z => charX (clampToIcc T s') z)
        (fun s' z => charV (clampToIcc T s') z) f₀ s) =
        spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ (clampToIcc T s)) :=
      rfl
    rw [h1, ← h_self_consist (clampToIcc T s) (clampToIcc_mem hT.le s)]
  refine ⟨fun s z => charX (clampToIcc T s) z, fun s z => charV (clampToIcc T s) z,
    m T, hMbar_nn, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨fun z _hz => ?_, fun t ht z _hz => ?_, fun t ht z _hz => ?_⟩
    · change charX (clampToIcc T 0) z = z.1 ∧ charV (clampToIcc T 0) z = z.2
      rw [hclamp0]; exact hflow_on_ρlim.1 z (Set.mem_univ z)
    · have hEv : (fun s => charX (clampToIcc T s) z) =ᶠ[nhds t]
          (fun s => charX s z) := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        rw [hclamp_id s (Set.Ioo_subset_Icc_self hs)]
      change HasDerivAt (fun s => charX (clampToIcc T s) z) (charV (clampToIcc T t) z) t
      rw [hclamp_id t (Set.Ioo_subset_Icc_self ht)]
      exact (hflow_on_ρlim.2.1 t ht z (Set.mem_univ z)).congr_of_eventuallyEq hEv
    · have hEv : (fun s => charV (clampToIcc T s) z) =ᶠ[nhds t]
          (fun s => charV s z) := by
        filter_upwards [Ioo_mem_nhds ht.1 ht.2] with s hs
        rw [hclamp_id s (Set.Ioo_subset_Icc_self hs)]
      change HasDerivAt (fun s => charV (clampToIcc T s) z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward
              (fun s' z' => charX (clampToIcc T s') z')
              (fun s' z' => charV (clampToIcc T s') z') f₀ t))
            (charX (clampToIcc T t) z))) t
      rw [h_rho_clamp t, hclamp_id t (Set.Ioo_subset_Icc_self ht)]
      exact (hflow_on_ρlim.2.2 t ht z (Set.mem_univ z)).congr_of_eventuallyEq hEv
  · intro z t ht
    have hEqOn : Set.EqOn (fun s => charX (clampToIcc T s) z) (fun s => charX s z)
        (Set.Icc 0 T) := fun s hs => by
      change charX (clampToIcc T s) z = charX s z; rw [hclamp_id s hs]
    have hEqOnV : Set.EqOn (fun s => charV (clampToIcc T s) z) (fun s => charV s z)
        (Set.Icc 0 T) := fun s hs => by
      change charV (clampToIcc T s) z = charV s z; rw [hclamp_id s hs]
    obtain ⟨h1, h2⟩ := h_boundary_ρlim z t ht
    refine ⟨?_, ?_⟩
    · change HasDerivWithinAt (fun s => charX (clampToIcc T s) z)
        (charV (clampToIcc T t) z) (Set.Icc 0 T) t
      rw [hclamp_id t ht]
      exact h1.congr hEqOn (hEqOn ht)
    · change HasDerivWithinAt (fun s => charV (clampToIcc T s) z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward
              (fun s' z' => charX (clampToIcc T s') z')
              (fun s' z' => charV (clampToIcc T s') z') f₀ t))
            (charX (clampToIcc T t) z))) (Set.Icc 0 T) t
      rw [h_rho_clamp t, hclamp_id t ht]
      exact h2.congr hEqOnV (hEqOnV ht)
  · intro s hs
    rw [h_rho_clamp s, hclamp_id s hs]
    exact le_trans (VlasovMeasureCurve.extend_hasMoment hT.le ρ_lim s)
      (hMbar_mono (clampToIcc T s) (clampToIcc_mem hT.le s))
  · intro s hs
    rw [h_rho_clamp s, hclamp_id s hs]
    exact VlasovMeasureCurve.extend_yIntegrable hT.le ρ_lim s
  · intro s
    rw [h_rho_clamp s]
    have : IsProbabilityMeasure (ρ_lim.extend (clampToIcc T s)) :=
      VlasovMeasureCurve.extend_isProb ρ_lim (clampToIcc T s)
    exact (convolveFunctionMeasure_lipschitz_in_x gradW L hL
      (ρ_lim.extend (clampToIcc T s)) (h_int_ρ_lim (clampToIcc T s))).continuous
  · intro s
    exact picardCharFlow_aemeasurable gradW L hL ρ_lim.extend h_int_ρ_lim charX charV hT.le
      hflow_on_ρlim h_boundary_ρlim f₀ (clampToIcc T s) (clampToIcc_mem hT.le s)
  · intro s x
    rw [h_rho_clamp s]
    exact h_int_ρ_lim (clampToIcc T s) x

/-- **Sub-helper for `_picard_fixedPointFlow`** — the Picard fixed-point
self-consistency equation.  For `t ∈ Icc 0 T`,

`ρ_lim.extend t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)`,

proved by the triangle through the iterates `x n`: the marginal-vs-limit leg
tends to `0` by `h_tendsto`, the flow-pushforward leg is `≤ Dn n · q` by the
pointwise contraction `picardLimit_flow_pointwise_contraction` (with
`Dn n := (supW1On (Icc 0 T) (x n).ρ ρ_lim.ρ).toReal → 0` from the
supW1On-Cauchy structure), and `picardLimit_fixed_point_eq` closes.  The
contraction ratio `q` is threaded by its defining equation `hq_def`
(let-bound parent supplies `rfl`). -/
private lemma picardLimit_self_consistency
    {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (m : ℝ → ℝ) (hMbar_nn : 0 ≤ m T)
    (hMbar_mono : ∀ t ∈ Set.Icc (0 : ℝ) T, m t ≤ m T)
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (hq_def : q = gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L : ℝ) T)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀)
    (x : ℕ → VlasovMeasureCurve d T m)
    (charXs charVs : ℕ → ℝ → PhaseSpace d → PhysSpace d)
    (h_contract : ∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
      ENNReal.ofReal (q ^ k * D₀))
    (h_flow : ∀ k,
      IsCharacteristicFlowOn gradW (x k).extend (charXs k) (charVs k)
        (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charXs k s z) (charVs k t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charVs k s z)
          (-(convolveFunctionMeasure gradW ((x k).extend t) (charXs k t z)))
          (Set.Icc 0 T) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        (x (k + 1)).ρ t = Measure.map (fun z : PhaseSpace d => charXs k t z) f₀))
    (ρ_lim : VlasovMeasureCurve d T m)
    (h_tendsto : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) (ρ_lim.ρ t))
        Filter.atTop (nhds 0))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (hflow_on_ρlim : IsCharacteristicFlowOn gradW ρ_lim.extend charX charV
      (Set.Ioo 0 T) Set.univ)
    (h_boundary_ρlim : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρ_lim.extend t) (charX t z)))
        (Set.Icc 0 T) t)
    (h_int_ρ_lim : ∀ t (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (ρ_lim.extend t)) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ρ_lim.extend t =
      spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t) := by
  have he : ∀ (ν : VlasovMeasureCurve d T m) s, s ∈ Set.Icc (0 : ℝ) T →
      ν.extend s = ν.ρ s := by
    intro ν s hs
    unfold VlasovMeasureCurve.extend clampToIcc; congr 1
    rw [min_eq_left hs.2, max_eq_right hs.1]
  have hMm : ∀ (ν : VlasovMeasureCurve d T m), ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(ν.extend t) ≤ m T :=
    fun ν t _ => le_trans (VlasovMeasureCurve.extend_hasMoment hT.le ν t)
      (hMbar_mono (clampToIcc T t) (clampToIcc_mem hT.le t))
  have h_int_ext_gen : ∀ (ν : VlasovMeasureCurve d T m) (t : ℝ) (xp : PhysSpace d),
      Integrable (fun y => gradW (xp - y)) (ν.extend t) := fun ν t xp =>
    integrable_gradW_shift gradW L hL (ν.extend t)
      (VlasovMeasureCurve.extend_yIntegrable hT.le ν t) xp
  have hCI := fun k => envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le (x k)
    (m T) hMbar_nn (hMm (x k)) (charXs k) (charVs k)
    (h_flow k).1 (h_flow k).2.1 (h_int_ext_gen (x k))
  have hCI_lim := envelopeStep_contractionInputs gradW L hL f₀ hf₀_int hT.le ρ_lim
    (m T) hMbar_nn (hMm ρ_lim) charX charV hflow_on_ρlim h_boundary_ρlim h_int_ρ_lim
  have h_marg : ∀ s ∈ Set.Icc (0 : ℝ) T,
      spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)
        = Measure.map (fun z => charX s z) f₀ := by
    intro s hs
    have h_pair_meas := charFlow_measurable_via_gronwall gradW L hL ρ_lim.extend h_int_ρ_lim
      charX charV T hT.le hCI_lim.2.2.2.1 hCI_lim.2.2.2.2.1 hCI_lim.2.2.2.2.2 s hs
    unfold spatialMarginal vlasovSolutionViaPushforward
    rw [Measure.map_map measurable_fst h_pair_meas]
    rfl
  have h_cauchy := picard_iterate_isCauchy_of_contraction
    (Set.Icc (0 : ℝ) T) (fun n => (x n).ρ) q hq_nn hq_lt D₀ hD₀_nn h_contract
  have h_uniform := picard_iterate_limit_uniform_tendsto
    (Set.Icc (0 : ℝ) T) (fun n => (x n).ρ) ρ_lim.ρ h_cauchy h_tendsto
  have h_sup_ne_top : ∀ n, supW1On (Set.Icc 0 T) (x n).ρ ρ_lim.ρ ≠ ⊤ :=
    fun n => supW1On_ne_top_of_VlasovMeasureCurve (m T) hMbar_mono (x n) ρ_lim
  have h_sup_tendsto : Filter.Tendsto
      (fun n => supW1On (Set.Icc 0 T) (x n).ρ ρ_lim.ρ) Filter.atTop (nhds 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    obtain ⟨N, hN⟩ := h_uniform ε hε
    refine ⟨N, fun n hn => ?_⟩
    unfold supW1On
    exact iSup_le fun s => iSup_le fun hs => hN n hn s hs
  set Dn : ℕ → ℝ := fun n => (supW1On (Set.Icc 0 T) (x n).ρ ρ_lim.ρ).toReal with hDn_def
  have hDn_nn : ∀ n, 0 ≤ Dn n := fun n => ENNReal.toReal_nonneg
  have hDn_tendsto : Filter.Tendsto Dn Filter.atTop (nhds 0) := by
    have h := (ENNReal.tendsto_toReal (show (0:ENNReal) ≠ ⊤ by simp)).comp h_sup_tendsto
    rw [ENNReal.toReal_zero] at h
    exact h
  have h_W1_fin_curve : ∀ n, ∀ s ∈ Set.Icc (0 : ℝ) T,
      wasserstein1 ((x n).extend s) (ρ_lim.extend s) ≠ ⊤ := by
    intro n s hs
    rw [he (x n) s hs, he ρ_lim s hs]
    have := (x n).isProb s; have := ρ_lim.isProb s
    exact wasserstein1_ne_top_of_finite_moment _ _
      ((x n).yIntegrable s hs) (ρ_lim.yIntegrable s hs)
  have h_W1_bound_curve : ∀ n, ∀ s ∈ Set.Icc (0 : ℝ) T,
      (wasserstein1 ((x n).extend s) (ρ_lim.extend s)).toReal ≤ Dn n := by
    intro n s hs
    rw [he (x n) s hs, he ρ_lim s hs]
    exact ENNReal.toReal_mono (h_sup_ne_top n)
      (wasserstein1_le_supW1On (Set.Icc 0 T) (x n).ρ ρ_lim.ρ s hs)
  have h_term2 : ∀ n t, t ∈ Set.Icc (0 : ℝ) T →
      (wasserstein1 (Measure.map (fun z => charXs n t z) f₀)
                    (Measure.map (fun z => charX t z) f₀)).toReal ≤ Dn n * q :=
    fun n t ht => picardLimit_flow_pointwise_contraction gradW L hL f₀ hf₀_int hT
      m hMbar_nn hMbar_mono (x n) ρ_lim (charXs n) (charVs n) charX charV
      (h_flow n).1 (h_flow n).2.1 hflow_on_ρlim h_boundary_ρlim
      (Dn n) (hDn_nn n) (h_W1_fin_curve n) (h_W1_bound_curve n) q hq_def t ht
  intro t ht
  rw [he ρ_lim t ht, h_marg t ht]
  exact picardLimit_fixed_point_eq f₀ m x ρ_lim charXs charX
    (fun n t' ht' => (h_flow n).2.2 t' ht') h_tendsto
    (fun n t' ht' => (hCI n).1 t' ht') (fun t' ht' => hCI_lim.1 t' ht')
    (fun n t' ht' => (hCI n).2.2.1 t' ht') (fun t' ht' => hCI_lim.2.2.1 t' ht')
    Dn q (by simpa using hDn_tendsto.mul_const q) h_term2 t ht

/-- **Sub-helper for `vlasovWellPosedness_local`** — the Picard fixed-point
self-consistent flow.

Given `f₀ : Measure (PhaseSpace d)` with finite first moment, produces a
characteristic flow `(charX, charV)` whose **own pushforward's spatial
marginal** is the reference measure the flow is built against — i.e., the
Picard fixed point at the spatial-marginal-curve level:

  `ρ_t := spatialMarginal (Measure.map (z ↦ (charX t z, charV t z)) f₀)`
  `charX, charV solve the Vlasov ODE against this ρ`.

The body carries the substantive Picard analysis:

* M-fixed-point: pick a moment bound `M ≥ A/(1 - B)` where
  `A = gronwallBound 1 (1+L) ‖gradW 0‖ T · (M_f₀ + 1)` and
  `B = L · (exp((1+L)·T) - 1)/(1+L) · (M_f₀ + 1)`.  Requires `B < 1`,
  which is the genuine convergence criterion for the moment iteration
  (stronger than the contraction predicate `LocalSmallnessContraction
  L T` alone for large `M_f₀` — the contraction predicate gates the q
  factor; the M-fixed-point additionally requires the moment iteration
  to converge).
* Picard sequence `x_n : ℕ → VlasovMeasureCurve d T M` starting from
  `x_0 := constantCurve (spatialMarginal f₀)` and `x_{n+1} := Phi_step(x_n)`.
* Contraction via `Phi_supW1_contraction`: `supW1On (Φρ) (Φσ) ≤ q · D`
  with `q < 1`.  Apply `picard_iterate_isCauchy_of_contraction` +
  `picard_iterate_exists_limit` to get the W₁-limit
  `ρ_lim : VlasovMeasureCurve d T M`.
* Self-consistency `Φ(ρ_lim) = ρ_lim`: triangle through `x_n`.
* Apply `exists_vlasov_characteristicFlow_global_smallT` to `ρ_lim.extend`
  to get the flow.

**Metric-dependence note**.  The convergence rests on two independent
predicates:
* `LocalSmallnessContraction L T := L · (exp((max 1 L)·T) - 1) / (max 1 L) < 1`
  — exponential in T, from `Phi_supW1_contraction`'s W₁-based shape.
* `LocalSmallnessPLBuffer L T := L · T² < 1` — quadratic, from
  per-ball Picard-Lindelöf's ball geometry.

These are genuinely independent (neither universally implies the other), so
each predicate matches its own sub-argument.

Under the Wbar refactor (Dobrushin 1979, §5), both constraints become
linear-in-T and align: `LocalSmallnessContraction` reduces to
`C₂(L)·T < 1`, and the single algebraic constraint then suffices and is
satisfiable for any `L > 0` by taking `T < 1/C₂(L)`.

**Output bundle** (designed to feed
`vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn` directly):

* Flow `(charX, charV)` against the *spatial marginal of the pushforward*
  — the load-bearing self-consistency conjunct.
* Boundary regularity.
* Uniform moment bound `M_ρ` on the spatial marginal trajectory. -/
theorem vlasovWellPosedness_local_picard_fixedPointFlow
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hTL_PL : LocalSmallnessPLBuffer L T)
    (hTL_con : LocalSmallnessContraction L T)
    (hB : (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T) - 1) < 1) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d) (M_ρ : ℝ), 0 ≤ M_ρ ∧
      -- Self-consistent characteristic flow: against the spatial marginal
      -- of its own phase-space pushforward.
      IsCharacteristicFlowOn gradW
        (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
        charX charV (Set.Ioo 0 T) Set.univ ∧
      -- Boundary regularity: HasDerivWithinAt on `Icc 0 T` for every z and
      -- t ∈ Icc 0 T.
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW
              (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
              (charX t z)))
          (Set.Icc 0 T) t) ∧
      -- Uniform first-moment bound on the spatial-marginal trajectory.
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ) ∧
      -- First-moment integrability on the spatial-marginal trajectory.
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y : PhysSpace d => ‖y‖)
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))) ∧
      -- Continuity of the convolution force in `x` (uniformly in `s`).
      (∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x)) ∧
      -- **AEMeasurable witness**, projected from the Picard fixed-point
      -- construction's continuity-in-z — supplies the `h_aemeas` conjunct
      -- in downstream `_finalAssembly_*`.
      (∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀) ∧
      -- **Universal-in-s convolution integrability**.  For `s ∈ Icc 0 T`
      -- follows from `h_y_int_ρ` + Lipschitz of `gradW`; the extension to
      -- all `s` uses constant-extension (clamp) past T inside the Picard
      -- construction.  Supplies the `h_int_conv` conjunct in downstream
      -- `_finalAssembly_*`.
      (∀ s (x : PhysSpace d),
        Integrable (fun y => gradW (x - y))
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))) := by
  -- ============================================================
  -- Step 1: Spatial marginal setup.
  -- μ₀ := spatialMarginal f₀ = Measure.map Prod.fst f₀.
  -- IsProbabilityMeasure μ₀ via Measure.isProbabilityMeasure_map.
  -- Integrable ‖·‖ μ₀ from hf₀_int via integral_map on Prod.fst.
  -- ============================================================
  have hμ₀_prob : IsProbabilityMeasure (spatialMarginal f₀) :=
    (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  have hμ₀_int : Integrable (fun y : PhysSpace d => ‖y‖) (spatialMarginal f₀) := by
    unfold spatialMarginal
    rw [integrable_map_measure
      (Continuous.aestronglyMeasurable continuous_norm) measurable_fst.aemeasurable]
    -- Need: Integrable (‖·‖ ∘ Prod.fst) f₀ = Integrable (fun z => ‖z.1‖) f₀.
    -- This follows from hf₀_int (Integrable ‖·‖ f₀) and ‖z.1‖ ≤ ‖z‖.
    refine hf₀_int.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact (measurable_fst.norm.aestronglyMeasurable)
    · simp only [Function.comp_def, Real.norm_of_nonneg (norm_nonneg _)]
      exact (norm_fst_le z)
  -- **F1 (phase-space anchor)**: `M_f₀` is the *phase-space* first moment
  -- `∫z‖z‖∂f₀`, NOT the spatial marginal — matching `phi_moment_envelope_le`'s
  -- (A.2) `integral_map` initial value, so the envelope dominates both the
  -- pushforward moments (A.2) and the spatial base case (`∫‖x‖∂μ₀ ≤ M_f₀`).
  let M_f₀ : ℝ := ∫ z : PhaseSpace d, ‖z‖ ∂f₀
  have hM_f₀_nn : 0 ≤ M_f₀ := integral_nonneg (fun z => norm_nonneg z)
  -- ============================================================
  -- Step 2: time-dependent moment envelope `m` (option 2, dissolving the
  -- constant-`M` fixed-point).  `gronwall_envelope_exists` (Piece A.3) under
  -- `hB := B(T) < 1` yields a monotone `m` that is `Φ`-invariant at the moment
  -- level, so `Φ : space(m) → space(m)` and the Picard sequence stays in one
  -- fixed curve space.
  -- ============================================================
  obtain ⟨m, hm_mono, hm_ge, hm_inv⟩ :=
    gronwall_envelope_exists M_f₀ ‖gradW 0‖ hM_f₀_nn (norm_nonneg _) L T hT.le hB
  have hm_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ m t :=
    fun t ht => le_trans hM_f₀_nn (hm_ge t ht)
  have hMbar_nn : 0 ≤ m T := hm_nn T ⟨hT.le, le_refl T⟩
  have hMbar_mono : ∀ t ∈ Set.Icc (0 : ℝ) T, m t ≤ m T :=
    fun t ht => hm_mono ht ⟨hT.le, le_refl T⟩ ht.2
  -- ============================================================
  -- Step 3: Convolution integrability for constantCurve.
  -- For the base case x 0 = constantCurve μ₀, need h_int_ext:
  --   ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) ((constantCurve μ₀).extend t).
  -- This reduces to: Integrable (fun y => gradW (x - y)) μ₀, which follows
  -- from hμ₀_int + Lipschitz bound on gradW.
  -- Integrability of gradW against μ₀.
  -- ============================================================
  have h_int_gradW_μ₀ : ∀ (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (spatialMarginal f₀) :=
    fun x_pt => integrable_gradW_shift gradW L hL (spatialMarginal f₀) hμ₀_int x_pt
  -- ============================================================
  -- Step 4: Picard sequence + contraction bound.
  -- The sequence x : ℕ → VlasovMeasureCurve d T M is built by Phi_step +
  -- induction; the contraction estimate uses Phi_supW1_contraction applied
  -- to consecutive iterates.
  -- ============================================================
  -- `q` is the M-INDEPENDENT genuine contraction ratio (not 2M·q_true).
  -- `Phi_supW1_contraction` outputs `q · D` per step, so `q^k · D₀ =
  -- q^k · (2M)` is the iterated contraction bound; the contraction factor
  -- `q = gronwallBound 0 (max 1 L) L T = (L/(max 1 L)) · (exp((max 1 L)·T) - 1)`
  -- is separated from the W₁-input bound `D₀ = 2M`.  `hq_lt` closes by direct
  -- citation of `hTL_con` (LocalSmallnessContraction) after one unfold.
  let q : ℝ := gronwallBound 0 ((max 1 L : NNReal) : ℝ) (L : ℝ) T
  have hq_nn : 0 ≤ q := by
    have hK_nn : (0 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := NNReal.coe_nonneg _
    have hε_nn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
    have := gronwallBound_mono (δ := (0 : ℝ)) (K := ((max 1 L : NNReal) : ℝ))
      (ε := (L : ℝ)) (le_refl 0) hε_nn hK_nn hT.le
    rw [gronwallBound_x0] at this; exact this
  -- Direct citation: `LocalSmallnessContraction L T` IS `q < 1` after
  -- unfolding both definitions.  No local derivation; the named-lemma
  -- pattern from the soundness-fix mechanism.
  have hq_lt : q < 1 := hTL_con.gronwallBound_lt_one
  -- D₀: initial supW1On bound = supW1On (x 0).ρ (x 1).ρ ≤ 2 * M.
  let D₀ : ℝ := 2 * (m T)
  have hD₀_nn : 0 ≤ D₀ := by linarith [hMbar_nn]
  -- Picard sequence + contraction, in the fixed envelope space `m`.  The
  -- recursion uses `Phi_step_envelope` per step + `Phi_supW1_contraction`
  -- for the geometric bound.
  -- **Enriched existential**: the Picard sequence exposes, per
  -- step `k`, the flow `(charXs k, charVs k)` against `(x k).extend` — exactly
  -- `Phi_step_envelope`'s output shape — plus the pushforward identity
  -- `(x(k+1)).ρ t = map (charXs k t) f₀`.  Exposing the flows lets the
  -- self-consistency proof (Step 8) feed them directly to `Phi_supW1_contraction`,
  -- dissolving the (un-banked) ODE-uniqueness that re-deriving them would need.
  have hμ₀_int_fst : Integrable (fun z : PhaseSpace d => ‖z.1‖) f₀ :=
    hf₀_int.mono' measurable_fst.norm.aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact norm_fst_le z)
  have hμ₀_le_m : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal f₀) ≤ m t := by
    intro t ht
    have h_eq : ∫ y, ‖y‖ ∂(spatialMarginal f₀) = ∫ z, ‖z.1‖ ∂f₀ := by
      unfold spatialMarginal
      rw [integral_map measurable_fst.aemeasurable continuous_norm.aestronglyMeasurable]
    have h_le : ∫ z, ‖z.1‖ ∂f₀ ≤ M_f₀ :=
      integral_mono hμ₀_int_fst hf₀_int (fun z => norm_fst_le z)
    rw [h_eq]; exact le_trans h_le (hm_ge t ht)
  obtain ⟨x, charXs, charVs, h_contract, h_flow⟩ :=
    vlasovWellPosedness_local_picard_sequence W gradW hgradW L hL f₀ hf₀_int hT hTL_PL
      m hm_mono hm_nn hm_inv hMbar_nn hMbar_mono hμ₀_prob hμ₀_int hμ₀_le_m
      q hq_nn rfl D₀ hD₀_nn rfl
  -- ============================================================
  -- Step 5: Extract limit ρ_lim via picard_iterate_exists_limit.
  -- ============================================================
  obtain ⟨ρ_lim, h_tendsto⟩ :=
    picard_iterate_exists_limit x q hq_nn hq_lt D₀ hD₀_nn h_contract
  -- ============================================================
  -- Step 6: Convolution integrability for ρ_lim.extend.
  -- Needed by exists_vlasov_characteristicFlow_global_smallT.
  -- Integrability of gradW against ρ_lim.extend t.
  -- ============================================================
  have h_int_ρ_lim : ∀ t (x_pt : PhysSpace d),
      Integrable (fun y => gradW (x_pt - y)) (ρ_lim.extend t) := fun t x_pt =>
    integrable_gradW_shift gradW L hL (ρ_lim.extend t)
      (VlasovMeasureCurve.extend_yIntegrable hT.le ρ_lim t) x_pt
  -- Convolution continuity for ρ_lim.extend, universal in t.
  -- Deduced from ρ_lim.extend_convCont + h_int_ρ_lim restricted to Icc 0 T.
  have h_conv_cont_ρ_lim : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ_lim.extend t) x) := by
    intro x_pt
    have h_int_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y => gradW (x_pt - y)) (ρ_lim.ρ t) := by
      intro t ht
      have h_eq : ρ_lim.extend t = ρ_lim.ρ t := by
        unfold VlasovMeasureCurve.extend clampToIcc
        congr 1
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [← h_eq]; exact h_int_ρ_lim t x_pt
    exact VlasovMeasureCurve.extend_convCont gradW L hL hT.le ρ_lim x_pt h_int_Icc
  -- ============================================================
  -- Step 7: Flow construction via exists_vlasov_characteristicFlow_global_smallT.
  -- Build (charX, charV) against ρ_lim.extend.
  -- ============================================================
  obtain ⟨charX, charV, hflow_on_ρlim, h_boundary_ρlim⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL
      ρ_lim.extend h_int_ρ_lim h_conv_cont_ρ_lim
      (fun t => VlasovMeasureCurve.extend_yIntegrable hT.le ρ_lim t)
      (m T) hMbar_nn
      (fun t => le_trans (VlasovMeasureCurve.extend_hasMoment hT.le ρ_lim t)
        (hMbar_mono (clampToIcc T t) (clampToIcc_mem hT.le t)))
      T hT.le hTL_PL
  -- ============================================================
  -- Step 8: Self-consistency.  For t ∈ Icc 0 T,
  --   ρ_lim.ρ t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t).
  -- This is the Picard fixed-point equation: Phi charX f₀ t = ρ_lim.ρ t,
  -- proved by triangle through x n using contraction + tendsto.
  -- ============================================================
  -- ============================================================
  -- Self-consistency on Icc 0 T.
  -- For t ∈ Icc 0 T:
  --   ρ_lim.extend t = ρ_lim.ρ t   (by clampToIcc identity on Icc)
  --   ρ_lim.ρ t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)
  -- The second equality is the Picard fixed-point equation, proved by triangle
  -- through x n using contraction + tendsto.
  -- ============================================================
  have h_self_consist : ∀ t ∈ Set.Icc (0 : ℝ) T,
      ρ_lim.extend t =
      spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t) :=
    -- Step 8 extracted as `picardLimit_self_consistency`; the let-bound `q`'s
    -- defining equation is supplied by `rfl`.
    picardLimit_self_consistency gradW L hL f₀ hf₀_int hT m hMbar_nn hMbar_mono
      q hq_nn hq_lt rfl D₀ hD₀_nn x charXs charVs h_contract h_flow
      ρ_lim h_tendsto charX charV hflow_on_ρlim h_boundary_ρlim h_int_ρ_lim
  -- ============================================================
  -- Step 9: Bundle with a CLAMPED flow `cX s := charX (clampToIcc T s)`.
  --
  -- The raw flow from `exists_vlasov_characteristicFlow_global_smallT` is
  -- controlled only on `[0, T]`; off-window it is uncontrolled
  -- `Classical.choose` data with no growth bound.  The conclusion's
  -- universal-in-`s` conjuncts (convolution integrability + continuity-in-x
  -- for ALL `s`) therefore cannot hold for the raw flow.  We return instead
  -- the clamped flow, whose pushforward at any `s` equals the on-window
  -- pushforward at `clampToIcc T s ∈ [0, T]` — hence globally controlled.
  -- On `[0, T]` the clamp is the identity (`clampToIcc T s = s`), so every
  -- window conjunct (flow ODE on Ioo, boundary on Icc, moment, integrability)
  -- transfers from the raw flow via `clampToIcc`-congruence.
  -- ============================================================
  exact picardFlow_clamp_bundle gradW L hL f₀ hT m hMbar_nn hMbar_mono ρ_lim
    charX charV hflow_on_ρlim h_boundary_ρlim h_int_ρ_lim h_self_consist

/-- **Sub-helper for `vlasovWellPosedness_local`** — moment-bound transport.

Given the Picard fixed-point flow's bundle (from
`_picard_fixedPointFlow`), produces `HasFiniteFirstMoment (f t)` for
`t ∈ Icc 0 T`, where `f := vlasovSolutionViaPushforward charX charV f₀`.

**Proof strategy**:

1. Boundary transport: extract `h_init / h_cont_Icc / h_deriv_Ico` from
   `hflow_on + h_boundary` via `characteristicFlow_boundary_regularity`.
2. `flow_distance_growth_bound_on` applied to `(charX, charV)` produces
   the growth constant `C_T` with `‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1)`.
3. Probability of `f t = Measure.map (z ↦ (charX t z, charV t z)) f₀` from
   the AEMeasurable witness.
4. Integrable `‖·‖` on `f t`: via `integrable_map_measure` + growth bound +
   `Integrable ‖·‖ f₀`.

Factored out to keep `vlasovWellPosedness_local`'s body a clean glue. -/
theorem vlasovWellPosedness_local_moment
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (_hTL_PL : LocalSmallnessPLBuffer L T)
    (_hTL_con : LocalSmallnessContraction L T)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hflow_on : IsCharacteristicFlowOn gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV (Set.Ioo 0 T) Set.univ)
    (h_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
            (charX t z)))
        (Set.Icc 0 T) t)
    (hM_ρ_bound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ)
    (h_y_int_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (_hconv_cont : ∀ s, Continuous (fun x =>
      convolveFunctionMeasure gradW
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x))
    -- Passed from `_picard_fixedPointFlow`'s enriched output: the
    -- AEMeasurable witness + universal-in-s convolution integrability.
    (h_aemeas : ∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (h_int_conv : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    HasFiniteFirstMoment (vlasovSolutionViaPushforward charX charV f₀ t) := by
  -- IsProbabilityMeasure for the spatial marginal (needed for the flow typeclass).
  -- spatialMarginal μ = Measure.map Prod.fst μ, so IsProbabilityMeasure_map needs
  -- AEMeasurable Prod.fst (Measure.map ... f₀). Since Prod.fst is measurable,
  -- it is AEMeasurable wrt any measure.
  have hρ_prob : ∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s
    unfold spatialMarginal vlasovSolutionViaPushforward
    -- Need IsProbabilityMeasure (Measure.map Prod.fst (Measure.map (fun z => ...) f₀))
    -- Use Measure.map_map to compose, then isProbabilityMeasure_map_iff on the composition.
    have h_aemeas_pair : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀ :=
      h_aemeas s
    have h_prob_inner : IsProbabilityMeasure
        (Measure.map (fun z : PhaseSpace d => (charX s z, charV s z)) f₀) :=
      (Measure.isProbabilityMeasure_map_iff h_aemeas_pair).mpr inferInstance
    exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  -- Step 1: Extract h_init, h_cont_Icc, h_deriv_Ico via boundary transport.
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    characteristicFlow_boundary_regularity gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV T hT.le hflow_on h_boundary
  -- Step 2: Growth bound from flow_distance_growth_bound_on.
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL
      (fun s => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))
      charX charV T hT.le
      h_init h_cont_Icc h_deriv_Ico
      M_ρ hM_ρ_nn hM_ρ_bound h_y_int_ρ h_int_conv
  -- Step 3: Conclude HasFiniteFirstMoment.
  unfold HasFiniteFirstMoment vlasovSolutionViaPushforward
  refine ⟨(Measure.isProbabilityMeasure_map_iff (h_aemeas t)).mpr inferInstance, ?_⟩
  -- Integrable ‖·‖ wrt Measure.map (fun z => (charX t z, charV t z)) f₀.
  rw [integrable_map_measure
    (Continuous.aestronglyMeasurable continuous_norm) (h_aemeas t)]
  -- Now need: Integrable (fun z : PhaseSpace d => ‖(charX t z, charV t z)‖) f₀.
  have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
    have h1 : Integrable (fun z : PhaseSpace d => C_T * ‖z‖) f₀ :=
      hf₀_int.const_mul C_T
    have h2 : Integrable (fun _ : PhaseSpace d => C_T) f₀ := integrable_const _
    have h_eq : (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) =
                fun z => C_T * ‖z‖ + C_T := by funext z; ring
    rw [h_eq]; exact h1.add h2
  -- The goal after rw is: Integrable (‖·‖ ∘ fun z => (charX t z, charV t z)) f₀
  -- = Integrable (fun z => ‖(charX t z, charV t z)‖) f₀.
  -- Dominator: C_T * (‖z‖ + 1); AE bound from h_growth.
  have h_norm_aesm : AEStronglyMeasurable
      (fun z : PhaseSpace d => ‖(charX t z, charV t z)‖) f₀ :=
    (h_aemeas t).norm.aestronglyMeasurable
  refine h_dom_int.mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
  · -- AEStronglyMeasurable of ‖·‖ ∘ (charX t, charV t).
    -- After integrable_map_measure rewrite, goal is for the composition form.
    convert h_norm_aesm using 1
    rfl
  · -- Pointwise bound: ‖(charX t z, charV t z)‖ ≤ C_T * (‖z‖ + 1).
    -- The norm in the goal is ‖(‖·‖ ∘ ...)(z)‖ = ‖‖(charX t z, charV t z)‖‖.
    simp only [Function.comp_def, Real.norm_of_nonneg (norm_nonneg _)]
    exact h_growth t ht z

/-- **Sub-helper for `vlasovWellPosedness_local`** — IsLagrangianVlasovSolutionOn
threading.

Given the Picard fixed-point flow's bundle (from
`_picard_fixedPointFlow`), produces the
`IsLagrangianVlasovSolutionOn gradW f T` conjunct via the 20-hypothesis
threading through
`vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`.

**Proof strategy**:

1. Boundary transport: extract `h_init / h_cont_Icc / h_deriv_Ico`.
2. Universal-in-`s` convolution integrability (handling `s` outside
   `[0, T]` via the clamp-extension argument).
3. AEMeasurable witness.
4. `IsCharacteristicFlowSelfConsistent`: `∀ t, ρ_lim t = Φ charX f₀ t`,
   which expands by definition since `ρ_lim = spatialMarginal ∘ f` and
   `f = vlasovSolutionViaPushforward charX charV f₀`; spatial marginal
   of pushforward = pushforward under `Prod.fst ∘ ...` = `Φ charX f₀`.
   The composition is the `Measure.map_map`-with-AEMeasurable bridge.
5. Continuity of `gradW`: `hL.continuous`.
6. Probability instance of `spatialMarginal ∘ f`: derived from
   AEMeasurable + IsProbabilityMeasure f₀.
7. Final invocation: `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`
   with the full hypothesis bundle.

Factored out to keep `vlasovWellPosedness_local`'s body a clean glue. -/
theorem vlasovWellPosedness_local_isLagrangian
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (_hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (_hTL_PL : LocalSmallnessPLBuffer L T)
    (_hTL_con : LocalSmallnessContraction L T)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hflow_on : IsCharacteristicFlowOn gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV (Set.Ioo 0 T) Set.univ)
    (h_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
      HasDerivWithinAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW
            (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
            (charX t z)))
        (Set.Icc 0 T) t)
    (hM_ρ_bound : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ)
    (h_y_int_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (hconv_cont : ∀ s, Continuous (fun x =>
      convolveFunctionMeasure gradW
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x))
    -- Passed from `_picard_fixedPointFlow`'s enriched output: the
    -- AEMeasurable witness + universal-in-s convolution integrability.
    (h_aemeas : ∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (h_int_conv : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))) :
    IsLagrangianVlasovSolutionOn gradW
      (vlasovSolutionViaPushforward charX charV f₀) T := by
  -- IsProbabilityMeasure for the spatial marginal (needed for the target typeclass).
  have hρ_prob : ∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) := by
    intro s
    unfold spatialMarginal vlasovSolutionViaPushforward
    have h_aemeas_pair : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀ :=
      h_aemeas s
    have _h_prob_inner : IsProbabilityMeasure
        (Measure.map (fun z : PhaseSpace d => (charX s z, charV s z)) f₀) :=
      (Measure.isProbabilityMeasure_map_iff h_aemeas_pair).mpr inferInstance
    exact (Measure.isProbabilityMeasure_map_iff measurable_fst.aemeasurable).mpr inferInstance
  -- Step 1: Extract h_init, h_cont_Icc, h_deriv_Ico via boundary transport.
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    characteristicFlow_boundary_regularity gradW
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
      charX charV T hT.le hflow_on h_boundary
  -- Step 2: IsCharacteristicFlowSelfConsistent
  -- ρ t = spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)
  --     = Measure.map Prod.fst (Measure.map (fun z => (charX t z, charV t z)) f₀)
  --     = Measure.map (Prod.fst ∘ fun z => (charX t z, charV t z)) f₀
  --         [by map_map_of_aemeasurable]
  --     = Measure.map (charX t) f₀
  have hself : IsCharacteristicFlowSelfConsistent charX f₀
      (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) := by
    intro t
    simp only []
    unfold spatialMarginal vlasovSolutionViaPushforward
    -- Goal: Measure.map Prod.fst (Measure.map (fun z => (charX t z, charV t z)) f₀)
    --     = Measure.map (fun z => charX t z) f₀
    have h_comp : Measure.map Prod.fst
        (Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) f₀) =
        Measure.map (Prod.fst ∘ fun z : PhaseSpace d => (charX t z, charV t z)) f₀ := by
      apply AEMeasurable.map_map_of_aemeasurable
      · exact measurable_fst.aemeasurable
      · exact h_aemeas t
    rw [h_comp]; congr 1
  -- Step 3: Apply the main threading theorem.
  exact vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn
    gradW L hL charX charV f₀ hf₀_int hT
    hflow_on h_init h_cont_Icc h_deriv_Ico
    M_ρ hM_ρ_nn hM_ρ_bound h_y_int_ρ h_int_conv
    hself h_aemeas hL.continuous hconv_cont

/-- **Local existence of a Vlasov solution on `[0, T]`.**

Under the joint constraint `LocalSmallnessPLBuffer L T` (`L · T² < 1`) +
`LocalSmallnessContraction L T`, produces a local-time Vlasov solution
`f : ℝ → Measure (PhaseSpace d)` on `[0, T]` satisfying initial
condition + local finite first moment + `IsLagrangianVlasovSolutionOn`.

The forward-iteration continuation extends from local `T` to arbitrary
`T_target` via **fixed-`T_0`** iteration: the contraction time `T_0`
depends only on `L` (not on the moment bound `M_n` propagating through
iterations), because `Phi_supW1_contraction`'s `q` is
`gronwallBound 0 (max 1 L) (L · D) T` — independent of `M_n`.  So the
continuation iterates `[0, T_0], [T_0, 2 T_0], …` with constant step `T_0`,
reaching any `T_target` in `⌈T_target / T_0⌉` windows; gluing then bridges
from `IsLagrangianVlasovSolutionOn` (local) to `IsLagrangianVlasovSolution`
(global).

**Proof strategy**:

1. Initial spatial marginal: `μ₀ := spatialMarginal f₀`.  By
   `HasFiniteFirstMoment f₀`, `μ₀` is a probability measure with
   `Integrable ‖·‖`.  Let `M_f₀ := ∫ ‖z‖ ∂f₀` (finite by
   `hf₀.2.integral_norm_le`).

2. Picard sequence on spatial marginals:
   - `ρ_0 := constantCurve μ₀`.
   - `ρ_{n+1}` obtained via `Phi_step` applied to `ρ_n`'s flow.

   Each `ρ_n` lives in `VlasovMeasureCurve d T M` for an appropriate
   `M` chosen so that the growth bound from
   `flow_distance_growth_bound_on` stays within `M` across iterations
   (the M-preservation constraint).

3. Contraction estimate via `Phi_supW1_contraction`:
   `supW1On (ρ_n.ρ) (ρ_{n+1}.ρ) ≤ ENNReal.ofReal (q^n * D₀)`
   for `q := gronwallBound 0 (max 1 L) (L · D) T < 1` (since `T` is
   small enough per the joint constraint).

4. Apply `picard_iterate_isCauchy_of_contraction` to get the ENNReal-form
   Cauchy condition on the `supW1On` pseudodistance.

5. Apply `picard_iterate_exists_limit` to extract the
   limit `ρ_lim : VlasovMeasureCurve d T M` plus pointwise W₁-tendsto.

6. Self-consistency `Φ(ρ_lim) = ρ_lim`: triangle through `ρ_n` using
   the uniform-tendsto helper, contraction, and pointwise tendsto.

7. Apply `exists_vlasov_characteristicFlow_global_smallT`
   to `ρ_lim.extend` to get the characteristic flow `(charX, charV)`
   against the self-consistent limit.

8. Define `f := vlasovSolutionViaPushforward charX charV f₀`.  Verify:
   - `f 0 = f₀` (from `IsCharacteristicFlowOn`'s initial-condition
     clause + `Measure.map_id`).
   - `HasFiniteFirstMoment (f t)` on `[0, T]` (from
     `flow_distance_growth_bound_on` applied to `(charX, charV)` +
     `hf₀.2`).
   - `IsLagrangianVlasovSolutionOn gradW f T` via
     `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`.

The body invokes `vlasovWellPosedness_local_picard_fixedPointFlow` for the
Picard fixed-point flow, then `vlasovWellPosedness_local_finalAssembly_*`
for the moment and Lagrangian conjuncts, deriving `f 0 = f₀` inline. -/
theorem vlasovWellPosedness_local
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d))
    (hf₀ : HasFiniteFirstMoment f₀)
    {T : ℝ} (hT : 0 < T)
    (hTL_PL : LocalSmallnessPLBuffer L T)
    (hTL_con : LocalSmallnessContraction L T)
    (hB : (L : ℝ) / (1 + (L : ℝ)) * (Real.exp ((1 + (L : ℝ)) * T) - 1) < 1) :
    ∃ (f : ℝ → Measure (PhaseSpace d))
      (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      f 0 = f₀ ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T, HasFiniteFirstMoment (f t)) ∧
      -- FLAT (window-constant) uniform first-moment bound on the spatial marginal.
      (∃ M : ℝ, 0 ≤ M ∧
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(spatialMarginal (f t)) ≤ M) ∧
      IsLagrangianVlasovSolutionOn gradW f T ∧
      -- Explicit flow bundle: pushforward, AEMeasurable, and boundary derivatives.
      -- These use the SAME charX charV as the outer ∃ (not the hidden witnesses
      -- inside IsLagrangianVlasovSolutionOn), enabling downstream consumers to
      -- use them without witness-identity issues.
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) T,
        AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) (f 0)) ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (spatialMarginal (f t)) (charX t z)))
          (Set.Icc 0 T) t) ∧
      -- Initial condition for the outer charX charV (same witnesses as boundary bundle above).
      (∀ z : PhaseSpace d, charX 0 z = z.1 ∧ charV 0 z = z.2) := by
  -- The body is decomposed into two sub-helpers plus an inline glue:
  --   * `vlasovWellPosedness_local_picard_fixedPointFlow` carries the Picard
  --     mathematics — spatial-marginal setup, the Picard sequence via
  --     `Phi_step`, the contraction estimate via `Phi_supW1_contraction`,
  --     the limit via `picard_iterate_exists_limit`,
  --     self-consistency `Φ(ρ_lim) = ρ_lim`, and the flow construction via
  --     `exists_vlasov_characteristicFlow_global_smallT`.
  --   * `vlasovWellPosedness_local_finalAssembly_*` thread the moment and
  --     `IsLagrangianVlasovSolutionOn` conjuncts through
  --     `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`.
  --   * This body invokes both, derives `f 0 = f₀` inline, and assembles.
  obtain ⟨hf₀_prob, hf₀_int⟩ := hf₀
  have : IsProbabilityMeasure f₀ := hf₀_prob
  -- Sub-helper invocation: produces the self-consistent flow + regularity
  -- + AEMeasurable witness + universal-in-s convolution integrability.
  obtain ⟨charX, charV, _M_ρ, _hM_ρ_nn, _hflow_on, _h_boundary,
          _hM_ρ_bound, _h_y_int_ρ, _hconv_cont, _h_aemeas, _h_int_conv⟩ :=
    vlasovWellPosedness_local_picard_fixedPointFlow W gradW hgradW L hL
      f₀ hf₀_int hT hTL_PL hTL_con hB
  -- Bundle the f-shape result.
  refine ⟨vlasovSolutionViaPushforward charX charV f₀, charX, charV, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- (a) f 0 = f₀.  The flow's initial-condition clause gives
    -- (charX 0 z, charV 0 z) = z for every z, so the pushforward at t = 0
    -- is `Measure.map id f₀ = f₀`.  Proved inline via the sub-helper's
    -- initial-condition projection at t = 0.
    have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z := by
      intro z
      have := (_hflow_on.1 z (Set.mem_univ z))
      exact Prod.ext this.1 this.2
    change vlasovSolutionViaPushforward charX charV f₀ 0 = f₀
    unfold vlasovSolutionViaPushforward
    have h_at_0 : (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id := by
      funext z; exact h_init z
    rw [h_at_0, Measure.map_id]
  · -- (b) HasFiniteFirstMoment (f t) on Icc 0 T.  Deferred to the
    -- _finalAssembly sub-helper (since it requires C_T from
    -- flow_distance_growth_bound_on, plus the integral_map +
    -- pushforward-moment-bound chain — exactly the threading work that
    -- the _finalAssembly sub-helper handles).
    intro t ht
    exact vlasovWellPosedness_local_moment W gradW hgradW L hL
      f₀ hf₀_int hT hTL_PL hTL_con charX charV
      _M_ρ _hM_ρ_nn _hflow_on _h_boundary _hM_ρ_bound _h_y_int_ρ _hconv_cont
      _h_aemeas _h_int_conv
      t ht
  · -- (b′) FLAT uniform first-moment bound on the spatial marginal.
    -- The picard fixed-point flow already exposes exactly this bound
    -- (`_hM_ρ_bound`) for `M_ρ := _M_ρ` against
    -- `spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ ·)`,
    -- which is `spatialMarginal (f ·)` by definition of `f` here.
    exact ⟨_M_ρ, _hM_ρ_nn, _hM_ρ_bound⟩
  · -- (c) IsLagrangianVlasovSolutionOn gradW f T.  Handled by the
    -- _finalAssembly sub-helper: it derives the AEMeasurable witness, the
    -- IsCharacteristicFlowSelfConsistent discharge, the universal-in-s
    -- convolution integrability (extension of `_hconv_cont`'s implications),
    -- and threads all the hypotheses through
    -- `vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn`.
    exact vlasovWellPosedness_local_isLagrangian W gradW hgradW L hL
      f₀ hf₀_int hT hTL_PL hTL_con charX charV
      _M_ρ _hM_ρ_nn _hflow_on _h_boundary _hM_ρ_bound _h_y_int_ρ _hconv_cont
      _h_aemeas _h_int_conv
  · -- (d) Explicit pushforward equation for the outer charX charV.
    -- vlasovSolutionViaPushforward charX charV f₀ t = Measure.map (charX t, charV t) f₀
    -- by DEFINITION. And f 0 = f₀ (from goal (a), which used the initial condition).
    -- So f t = Measure.map (charX t, charV t) (f 0) by congruence on f 0 = f₀.
    have h_f0_eq : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z :=
        fun z => Prod.ext (_hflow_on.1 z (Set.mem_univ z)).1 (_hflow_on.1 z (Set.mem_univ z)).2
      simp [vlasovSolutionViaPushforward,
            show (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id from funext h_init]
    intro t _
    show vlasovSolutionViaPushforward charX charV f₀ t =
      Measure.map (fun z : PhaseSpace d => (charX t z, charV t z))
        (vlasovSolutionViaPushforward charX charV f₀ 0)
    rw [h_f0_eq]
    -- After rw, goal is: vlasovSolutionViaPushforward charX charV f₀ t = Measure.map ... f₀
    -- This is rfl by definition of vlasovSolutionViaPushforward.
    rfl
  · -- (e) Explicit AEMeasurable for the outer charX charV.
    -- AEMeasurable (fun z => (charX s z, charV s z)) f₀ comes from _h_aemeas.
    -- The expected type uses (f 0) = vlasovSolutionViaPushforward charX charV f₀ 0 = f₀.
    have h_f0_eq : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      have h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z :=
        fun z => Prod.ext (_hflow_on.1 z (Set.mem_univ z)).1 (_hflow_on.1 z (Set.mem_univ z)).2
      simp [vlasovSolutionViaPushforward,
            show (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id from funext h_init]
    intro s _
    rw [h_f0_eq]
    exact _h_aemeas s
  · -- (f) Boundary regularity bundle: HasDerivWithinAt on Icc 0 T for all z, t.
    -- Directly from `_h_boundary` (the picard fixed-point flow's boundary output).
    -- The measure in the velocity derivative uses spatialMarginal (f t) where
    -- f = vlasovSolutionViaPushforward charX charV f₀, which is the same as
    -- what _h_boundary was built against.
    exact _h_boundary
  · -- (g) Initial condition for the outer charX charV witnesses.
    -- From _hflow_on.1 (IsCharacteristicFlowOn's first conjunct).
    intro z
    exact _hflow_on.1 z (Set.mem_univ z)

end Vlasov
