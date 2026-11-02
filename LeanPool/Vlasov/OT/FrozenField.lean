/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
module


public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import LeanPool.Vlasov.OT.CharacteristicFlow
public import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# Frozen-field weak solutions and convolution derivatives

The linear weak equation, frozen-flow existence, and differentiation of the convolution
field support the weak-to-Lagrangian argument without its transported-test machinery.
-/

@[expose] public section

namespace Vlasov

open MeasureTheory

variable {d : ℕ} [NeZero d]

/-! ## Linear (external-field) weak Vlasov solutions

The self-consistent weak predicate `IsVlasovSolutionOn` drives the convolution field by the
solution's *own* spatial marginal.  For the superposition argument we need the **linear**
version, where the field is driven by an *external* (frozen) measure curve `ρ` — both the given
weak solution `f` (with `ρ := spatialMarginal ∘ f`) and the pushforward `g` along the
frozen-field flow solve the *same* `IsLinearVlasovSolutionOn gradW ρ · T`, and uniqueness for it
(the crux, C3) forces `f = g`. -/

/-- Linear weak Vlasov evolution on `Ioo 0 T` for a test function `φ`, with the convolution field
driven by an **external** measure curve `ρ` (frozen), not the solution's own spatial marginal.
The self-consistent `WeakEvolutionEqOn gradW μ φ … (fun _ => 0) T` is the special case
`ρ = spatialMarginal ∘ μ` (modulo the `+ 0` remainder term). -/
def LinearWeakEvolutionEqOn
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (μ : ℝ → Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (T : ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) T,
    HasDerivAt (fun s => ∫ z, φ z ∂μ s)
      (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (ρ t) z.1)
                (gradVφ z))
        ∂μ t) t

/-- A measure curve `μ` solves the **linear** Vlasov equation on `[0,T]` driven by the external
field `ρ`: the distributional identity `LinearWeakEvolutionEqOn` holds for every `C_c^∞` test
function.  Mirror of `IsVlasovSolutionOn` with the field externalized. -/
def IsLinearVlasovSolutionOn
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (μ : ℝ → Measure (PhaseSpace d)) (T : ℝ) : Prop :=
  ∀ (φ : PhaseSpace d → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ (gradXφ gradVφ : PhaseSpace d → PhysSpace d),
      (∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1) →
      (∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) →
      LinearWeakEvolutionEqOn gradW ρ μ φ gradXφ gradVφ T

omit [NeZero d] in
/-- A self-consistent weak solution is a linear solution driven by its **own** spatial marginal.
The two differ only by `WeakEvolutionEqOn`'s `+ (fun _ => 0) t = + 0` remainder. -/
lemma IsVlasovSolutionOn.toLinearSelf
    {gradW : PhysSpace d → PhysSpace d} {f : ℝ → Measure (PhaseSpace d)} {T : ℝ}
    (h : IsVlasovSolutionOn gradW f T) :
    IsLinearVlasovSolutionOn gradW (fun t => spatialMarginal (f t)) f T := by
  intro φ hφ hφc gradXφ gradVφ hgradXφ hgradVφ t ht
  simpa using h φ hφ hφc gradXφ gradVφ hgradXφ hgradVφ t ht

omit [NeZero d] in
/-- **C1 #1 — pushforward solves the frozen linear weak equation.**

For a characteristic flow `(charX, charV)` solving the ODE with an **external** field `ρ` on
`Ioo 0 T`, the pushforward `g := (charX t, charV t)_# f₀` solves the linear Vlasov equation
driven by that same `ρ`.  Proof: the generic SC.1–SC.3 machinery (change of variables +
chain rule + differentiation-under-the-integral, all parametric in `ρ`) recomposed at this `ρ`,
with SC.4's push-back inlined as `integral_map` (SC.4's packaged form hard-codes the
self-consistent marginal).  This is `vlasovSolutionViaPushforward_isVlasovSolutionOn` with `ρ`
left free — the `_hself` self-consistency hypothesis is unused. -/
theorem vlasov_frozenField_pushforward_isLinearVlasovSolutionOn
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hflow_on : IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ s) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc (0 : ℝ) T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ s))
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (h_flow_meas : ∀ s, AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x => convolveFunctionMeasure gradW (ρ s) x)) :
    IsLinearVlasovSolutionOn gradW ρ (vlasovSolutionViaPushforward charX charV f₀) T := by
  intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have hφ_aesm_general : ∀ μ : Measure (PhaseSpace d), AEStronglyMeasurable φ μ :=
    fun μ => hφ_cont.aestronglyMeasurable
  -- SC.1: ∫ φ d(pushforward s) = ∫ (φ ∘ flow_s) df₀.
  have h_compose : ∀ s, ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s) =
      ∫ z, φ (charX s z, charV s z) ∂f₀ := fun s =>
    vlasov_pushforward_integral_eq_compose charX charV f₀ s (h_flow_meas s) φ (hφ_aesm_general _)
  -- SC.2 `_at`: pointwise chain rule at every z, at this t.
  have h_pointwise : ∀ z, HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t := by
    intro z
    have hX_at := hflow_on.2.1 t ht z (Set.mem_univ z)
    have hV_at := hflow_on.2.2 t ht z (Set.mem_univ z)
    exact vlasov_traj_chain_rule_at gradW ρ charX charV φ hφ_smooth
      gradXφ gradVφ hgradXφ hgradVφ t z hX_at hV_at
  -- SC.3: differentiation under the integral via the DiffUnderIntegralData bundle.
  have h_diff_data : DiffUnderIntegralData gradW ρ charX charV f₀ φ gradXφ gradVφ t := by
    obtain ⟨nhd, bound, hnhd, h_lipsch, h_bound_int⟩ :=
      vlasov_trajectory_lipschitz_bound_on gradW L hL ρ charX charV f₀
        hf₀_fm φ hφ_smooth hφ_compact hT hflow_on h_init h_cont_Icc h_deriv_Ico
        hgradW_cont hconv_cont t ht M_ρ hM_ρ_nn hM_ρ h_y_int h_int
    refine ⟨nhd, bound, hnhd, ?_, ?_, ?_, h_lipsch, h_bound_int⟩
    · exact vlasov_compose_flow_aestronglymeas charX charV f₀ φ hφ_cont h_flow_meas t
    · exact vlasov_compose_flow_integrable_at charX charV f₀ φ hφ_cont hφ_compact t (h_flow_meas t)
    · exact vlasov_pointwise_deriv_aestronglymeas gradW ρ charX charV f₀
        φ hφ_smooth gradXφ gradVφ hgradXφ hgradVφ hconv_cont t (h_flow_meas t)
  have h_under_integral :=
    vlasov_pushforward_hasDerivAt_under_integral gradW ρ charX charV f₀
      φ gradXφ gradVφ t h_pointwise h_diff_data
  -- SC.4 (inlined; the packaged form hard-codes the self-consistent marginal): AE-strong-meas
  -- of the dot-product integrand, then push back through `integral_map`.
  have h_integrand_aesm : AEStronglyMeasurable
      (fun y : PhaseSpace d =>
        @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
        - @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW (ρ t) y.1) (gradVφ y))
      (vlasovSolutionViaPushforward charX charV f₀ t) := by
    apply Continuous.aestronglyMeasurable
    apply Continuous.sub
    · apply Continuous.inner continuous_snd
      have hfderiv_X : ∀ z : PhaseSpace d,
          fderiv ℝ (fun x => φ (x, z.2)) z.1 =
          (fderiv ℝ φ z).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) :=
        fun z => by
          have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
            (hφ_smooth.differentiable (by simp) z).hasFDerivAt
          have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z.2))
              (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z.1 :=
            hasFDerivAt_prodMk_left z.1 z.2
          exact (h1.comp z.1 h2).fderiv
      have heqX : gradXφ = fun z => gradient (fun x => φ (x, z.2)) z.1 := funext hgradXφ
      simp_rw [heqX, gradient, hfderiv_X]
      exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
        ((ContinuousLinearMap.isBoundedLinearMap_comp_right
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
          (hφ_smooth.continuous_fderiv (by simp)))
    · apply Continuous.inner
      · exact (hconv_cont t).comp continuous_fst
      · have hfderiv_V : ∀ z : PhaseSpace d,
            fderiv ℝ (fun v => φ (z.1, v)) z.2 =
            (fderiv ℝ φ z).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) :=
          fun z => by
            have h1 : HasFDerivAt φ (fderiv ℝ φ z) z :=
              (hφ_smooth.differentiable (by simp) z).hasFDerivAt
            have h2 : HasFDerivAt (fun v : PhysSpace d => (z.1, v))
                (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z.2 :=
              hasFDerivAt_prodMk_right z.1 z.2
            exact (h1.comp z.2 h2).fderiv
        have heqV : gradVφ = fun z => gradient (fun v => φ (z.1, v)) z.2 := funext hgradVφ
        simp_rw [heqV, gradient, hfderiv_V]
        exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
          ((ContinuousLinearMap.isBoundedLinearMap_comp_right
            (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
            (hφ_smooth.continuous_fderiv (by simp)))
  -- Assemble: rewrite LHS via SC.1; push the derivative integral back through `integral_map`.
  have hLHS : (fun s => ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s)) =
              (fun s => ∫ z, φ (charX s z, charV s z) ∂f₀) := funext h_compose
  have h_map_eq :
      ∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z)
            - @inner ℝ (PhysSpace d) _ (convolveFunctionMeasure gradW (ρ t) z.1) (gradVφ z))
        ∂(vlasovSolutionViaPushforward charX charV f₀ t)
      = ∫ z, (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
            - @inner ℝ (PhysSpace d) _ (convolveFunctionMeasure gradW (ρ t) (charX t z))
                (gradVφ (charX t z, charV t z)))
        ∂f₀ := by
    unfold vlasovSolutionViaPushforward at h_integrand_aesm ⊢
    exact integral_map (h_flow_meas t) h_integrand_aesm
  rw [hLHS, h_map_eq]
  exact h_under_integral

omit [NeZero d] in
/-- **C1 #2 — characteristic flow for a frozen field from window data (L11 clamp).**

Build the characteristic flow for the *given* external curve `ρ` on `Ioo 0 T` (with boundary
regularity), from probability/moment/integrability/continuity data on the window `[0,T]` only.
`exists_vlasov_characteristicFlow_global_smallT` demands *universal*-in-`t` instances; we clamp
`t ↦ ρ (max 0 (min t T))` into the window (L11), apply the universal producer to the clamped
curve, and transfer on `[0,T]` where the clamp is the identity. -/
theorem exists_frozenField_charFlow_On
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    (T : ℝ) (hT : 0 < T) (hTL_PL : LocalSmallnessPLBuffer L T)
    (hρ_prob : ∀ t ∈ Set.Icc (0 : ℝ) T, IsProbabilityMeasure (ρ t))
    (h_int : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ (x : PhysSpace d),
      Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      ContinuousOn (fun t => convolveFunctionMeasure gradW (ρ t) x) (Set.Icc (0 : ℝ) T))
    (h_y_int : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ) :
    ∃ charX charV : ℝ → PhaseSpace d → PhysSpace d,
      IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z) ∧
      (∀ z : PhaseSpace d,
        ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) ∧
      (∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
        HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
          (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s) := by
  classical
  -- L11 clamp: `clampT t ∈ [0,T]` for every `t`, and `clampT t = t` on `[0,T]`.
  set clampT : ℝ → ℝ := fun t => max 0 (min t T) with hclampT_def
  have hclampT_mem : ∀ t, clampT t ∈ Set.Icc (0 : ℝ) T := by
    intro t
    simp only [hclampT_def, Set.mem_Icc]
    exact ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  have hclampT_id : ∀ t ∈ Set.Icc (0 : ℝ) T, clampT t = t := by
    intro t ht
    simp only [hclampT_def, min_eq_left ht.2, max_eq_right ht.1]
  have hclampT_cont : Continuous clampT := by
    simp only [hclampT_def]
    exact continuous_const.max (continuous_id.min continuous_const)
  -- Clamped curve `ρ' := ρ ∘ clampT`, which satisfies the universal hypotheses.
  set ρ' : ℝ → Measure (PhysSpace d) := fun t => ρ (clampT t) with hρ'_def
  have hρ'_prob : ∀ t, IsProbabilityMeasure (ρ' t) :=
    fun t => hρ_prob (clampT t) (hclampT_mem t)
  have h_int' : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ' t) :=
    fun t x => h_int (clampT t) (hclampT_mem t) x
  have h_y_int' : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ' t) :=
    fun t => h_y_int (clampT t) (hclampT_mem t)
  have hM_ρ' : ∀ t, ∫ y, ‖y‖ ∂(ρ' t) ≤ M_ρ := fun t => hM_ρ (clampT t) (hclampT_mem t)
  have hρ'_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ' t) x) :=
    fun x => (hρ_cont x).comp_continuous hclampT_cont (fun t => hclampT_mem t)
  -- Apply the universal producer to `ρ'`.
  obtain ⟨charX, charV, hflow', h_bdry'⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL ρ'
      h_int' hρ'_cont h_y_int' M_ρ hM_ρ_nn hM_ρ' T hT.le hTL_PL
  -- On `Ioo`/`Icc 0 T`, `clampT = id` so `ρ' = ρ`: transfer the flow back to `ρ`.
  refine ⟨charX, charV, ⟨hflow'.1, hflow'.2.1, ?_⟩, ?_, ?_, ?_⟩
  · -- velocity ODE for `ρ` on `Ioo 0 T`
    intro t ht z hz
    have h := hflow'.2.2 t ht z hz
    have hρeq : ρ' t = ρ t := by
      simp only [hρ'_def, hclampT_id t (Set.Ioo_subset_Icc_self ht)]
    rwa [hρeq] at h
  · -- initial condition
    intro z
    have h := hflow'.1 z (Set.mem_univ z)
    exact Prod.ext h.1 h.2
  · -- `ContinuousOn` on `Icc 0 T` from the producer's boundary derivatives
    intro z t ht
    obtain ⟨hX, hV⟩ := h_bdry' z t ht
    exact (hX.prodMk hV).continuousWithinAt
  · -- `h_deriv_Ico` (Ici-joint) from the producer's `Icc`-component derivatives
    intro z s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := Set.Ico_subset_Icc_self hs
    obtain ⟨hX, hV⟩ := h_bdry' z s hsIcc
    have hρeq : ρ' s = ρ s := by simp only [hρ'_def, hclampT_id s hsIcc]
    have hpair : HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (charV s z, -(convolveFunctionMeasure gradW (ρ' s) (charX s z)))
        (Set.Icc 0 T) s := hX.prodMk hV
    rw [hρeq] at hpair
    -- convert the set `Icc 0 T` to `Ici s` (local subset near `s`, since `s < T`)
    have hmem : Set.Iic ((s + T) / 2) ∈ nhds s := Iic_mem_nhds (by linarith [hs.2])
    have hsub : Set.Ici s ∩ Set.Iic ((s + T) / 2) ⊆ Set.Icc 0 T := by
      rintro u ⟨hu1, hu2⟩
      exact ⟨le_trans hs.1 hu1, le_trans hu2 (by linarith [hs.2])⟩
    exact (hasDerivWithinAt_inter hmem).mp (hpair.mono hsub)

/-! ## Final-step layer (crux-independent): constancy + measure extensionality -/

/-- **C2 #7 — constancy from a vanishing derivative.**

If a real function is continuous on `[0,T]` and has zero derivative throughout the open
interval, its endpoint values agree.  This is the dual argument's payoff step: `s ↦ ∫ ψ_s dμ_s`
is constant, so its value at `T` (= `∫ φ dμ_T`) equals its value at `0` (= `∫ ψ_0 dμ_0`). Mean
value theorem (`exists_hasDerivAt_eq_slope`). -/
lemma transportedIntegral_const_On {h : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hcont : ContinuousOn h (Set.Icc 0 T))
    (hderiv : ∀ s ∈ Set.Ioo (0 : ℝ) T, HasDerivAt h 0 s) :
    h 0 = h T := by
  obtain ⟨c, _hc, hc'⟩ :=
    exists_hasDerivAt_eq_slope h (fun _ => 0) hT hcont (fun s hs => hderiv s hs)
  have hc0 : (0 : ℝ) = (h T - h 0) / (T - 0) := hc'
  rcases div_eq_zero_iff.mp hc0.symm with h1 | h2
  · exact (sub_eq_zero.mp h1).symm
  · exact absurd h2 (ne_of_gt (by linarith : (0 : ℝ) < T - 0))

omit [NeZero d] in
/-- **C2 #9 — `C_c^∞` test functions determine a finite measure.**

If `∫ φ dμ = ∫ φ dν` for every smooth compactly-supported `φ`, then `μ = ν` (finite measures on
phase space).  The dual argument yields equality of integrals against the `IsVlasovSolution` test
class `C_c^∞`; this closes the bridge's final step `f T = g T`.  Route: extend `C_c^∞ →`
bounded-continuous (smooth approximation), then the in-house bounded-continuous extensionality
`ext_of_forall_integral_eq_of_IsFiniteMeasure` (cf. `Wasserstein.lean`). -/
lemma measure_eq_of_forall_Cc_integral_eq {μ ν : Measure (PhaseSpace d)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ φ : PhaseSpace d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∫ z, φ z ∂μ = ∫ z, φ z ∂ν) :
    μ = ν := by
  -- Haar instance on the ambient volume via the product reduction.
  have hHaar : (volume : Measure (PhaseSpace d)).IsAddHaarMeasure := by
    rw [show (volume : Measure (PhaseSpace d)) = (volume : Measure (PhysSpace d)).prod volume from
      Measure.volume_eq_prod _ _]
    infer_instance
  have hvolReg : (volume : Measure (PhaseSpace d)).Regular :=
    Measure.Regular.of_sigmaCompactSpace_of_isLocallyFiniteMeasure _
  have hμreg : μ.Regular := inferInstance
  have hνreg : ν.Regular := inferInstance
  -- Reduce `μ = ν` to equality of integrals against continuous compactly-supported `g`.
  refine MeasureTheory.Measure.ext_of_integral_eq_on_compactlySupported (fun g => ?_)
  set gf : PhaseSpace d → ℝ := ⇑g with hgf
  have hg_cont : Continuous gf := map_continuous g
  have hg_cs : HasCompactSupport gf := CompactlySupportedContinuousMap.hasCompactSupport g
  -- Uniform sup bound on `g`.
  obtain ⟨C, hC⟩ := hg_cont.bounded_above_of_compact_support hg_cs
  have hCnn : 0 ≤ C := le_trans (norm_nonneg _) (hC 0)
  -- A mollifier family `φ n` with outer radius `2/(n+2) → 0`.
  set φ : ℕ → ContDiffBump (0 : PhaseSpace d) :=
    fun n => ⟨1 / (n + 2), 2 / (n + 2), by positivity, by
      rw [div_lt_div_iff_of_pos_right (by positivity)]; norm_num⟩ with hφ
  have hrout : ∀ n, (φ n).rOut = 2 / (n + 2) := fun n => rfl
  have hrout_tendsto : Filter.Tendsto (fun n => (φ n).rOut) Filter.atTop (nhds 0) := by
    simp only [hrout]
    apply Filter.Tendsto.div_atTop (tendsto_const_nhds)
    exact Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
  -- The mollified functions.
  set gn : ℕ → PhaseSpace d → ℝ :=
    fun n => convolution ((φ n).normed volume) gf (ContinuousLinearMap.lsmul ℝ ℝ) volume with hgn
  -- Each `gn n` is `C^∞` with compact support, hence covered by the hypothesis `h`.
  have hgn_smooth : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (gn n) := fun n =>
    ((φ n).hasCompactSupport_normed).contDiff_convolution_left _
      (φ n).contDiff_normed (hg_cont.locallyIntegrable)
  have hgn_cs : ∀ n, HasCompactSupport (gn n) := fun n =>
    HasCompactSupport.convolution _ (φ n).hasCompactSupport_normed hg_cs
  have hgn_eq : ∀ n, ∫ z, gn n z ∂μ = ∫ z, gn n z ∂ν := fun n =>
    h (gn n) (hgn_smooth n) (hgn_cs n)
  -- Pointwise convergence `gn n → gf` (continuous `g`, shrinking bumps).
  have hgn_lim : ∀ x, Filter.Tendsto (fun n => gn n x) Filter.atTop (nhds (gf x)) := fun x =>
    ContDiffBump.convolution_tendsto_right_of_continuous hrout_tendsto hg_cont x
  -- Uniform bound `‖gn n x‖ ≤ C` (averaging keeps the sup bound).
  have hgn_bound : ∀ n, ∀ x, ‖gn n x‖ ≤ C := by
    intro n x
    rw [hgn]
    simp only
    rw [convolution_lsmul]
    calc ‖∫ t, (φ n).normed volume t • gf (x - t) ∂volume‖
        ≤ ∫ t, ‖(φ n).normed volume t • gf (x - t)‖ ∂volume := norm_integral_le_integral_norm _
      _ ≤ ∫ t, (φ n).normed volume t * C ∂volume := by
          apply integral_mono_of_nonneg
          · exact Filter.Eventually.of_forall (fun t => norm_nonneg _)
          · exact ((φ n).integrable_normed).mul_const C
          · refine Filter.Eventually.of_forall (fun t => ?_)
            simp only
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ((φ n).nonneg_normed t)]
            exact mul_le_mul_of_nonneg_left (hC _) ((φ n).nonneg_normed t)
      _ = C := by rw [integral_mul_const, (φ n).integral_normed, one_mul]
  -- DCT: `∫ gn n dμ → ∫ gf dμ` and likewise for `ν`.
  have hconv_μ : Filter.Tendsto (fun n => ∫ z, gn n z ∂μ) Filter.atTop (nhds (∫ z, gf z ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · exact fun n => (hgn_smooth n).continuous.aestronglyMeasurable
    · exact integrable_const C
    · exact fun n => Filter.Eventually.of_forall (fun x => hgn_bound n x)
    · exact Filter.Eventually.of_forall hgn_lim
  have hconv_ν : Filter.Tendsto (fun n => ∫ z, gn n z ∂ν) Filter.atTop (nhds (∫ z, gf z ∂ν)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => C)
    · exact fun n => (hgn_smooth n).continuous.aestronglyMeasurable
    · exact integrable_const C
    · exact fun n => Filter.Eventually.of_forall (fun x => hgn_bound n x)
    · exact Filter.Eventually.of_forall hgn_lim
  -- The two limits coincide because the prelimit sequences are equal.
  have hμν : Filter.Tendsto (fun n => ∫ z, gn n z ∂μ) Filter.atTop (nhds (∫ z, gf z ∂ν)) := by
    simpa only [hgn_eq] using hconv_ν
  exact tendsto_nhds_unique hconv_μ hμν

omit [NeZero d] in
/-- Convenience extractor: under `[AssW2 W]`, a gradient field `gradW= ∇W` is `C¹`.

`AssW2.gradContDiff` gives `ContDiff ℝ 1 (fun x => fderiv ℝ W x)`; composing with the (smooth,
linear) Riesz isometry `gradient W x = (toDual ℝ _).symm (fderiv ℝ W x)` and rewriting by `hgradW`
yields `ContDiff ℝ 1 gradW`. -/
lemma assW2_contDiff_gradW (W : PhysSpace d → ℝ) [AssW2 W]
    (gradW : PhysSpace d → PhysSpace d) (hgradW : ∀ x, gradW x = gradient W x) :
    ContDiff ℝ 1 gradW := by
  have heq : gradW =
      fun x => (InnerProductSpace.toDual ℝ (PhysSpace d)).symm (fderiv ℝ W x) := by
    funext x; rw [hgradW]; rfl
  rw [heq]
  have hriesz : ContDiff ℝ 1 fun u => (InnerProductSpace.toDual ℝ (PhysSpace d)).symm u :=
    (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.toContinuousLinearEquiv.contDiff
  exact hriesz.comp ‹AssW2 W›.gradContDiff

/-! ## Crux layer (C3): the variational equation and the dual-transport assembly

The two interfaces below were the load-bearing pieces of the bridge — both now proven and
axiom-clean.  `#3` was the genuine research gap (C¹ dependence of an ODE flow on its initial point
— absent from Mathlib), closed via route (b) (difference-quotient + Gronwall); `#8` is the
bridge-specific dual-transported-test-function assembly that consumes it.  `#10` (the public
theorem) composes the reuse layer (`exists_frozenField_charFlow_On`, #2) with `#8`.

The dual-argument *internals* `#4`/`#5`/`#6` (test-class enlargement `C_c^∞ → C¹_c`, the
transported test function `ψ_s = φ ∘ Φ_{s→t}` and its transport identity, and the zero-derivative
of `s ↦ ∫ ψ_s dμ_s`) are realized against the two-time-flow representation `Φ_{s→t} = Φ_t ∘ Φ_s⁻¹`
and proven below (`weakEvolution_test_C1c_On`, `transportedTest_transport_identity`,
`transportedIntegral_hasDerivAt_zero`). -/

omit [NeZero d] in
/-- **C3 F1 — the convolution force field is `C¹` in space (Fréchet derivative under the
integral).**  For `gradW ∈ C¹` (and `L`-Lipschitz, a probability measure `ρ` with the kernel
integrable), `x ↦ ∫ y, gradW (x − y) ∂ρ` is Fréchet-differentiable with derivative
`∫ y, fderiv ℝ gradW (x₀ − y) ∂ρ`.  This is the field-regularity foundation of the variational
equation (#3): it makes `D_z (vlasovVectorField …)` exist and continuous, so the variational ODE
`M' = (D_z b)·M` has continuous coefficients.

Differentiation under the integral sign (`hasFDerivAt_integral_of_dominated_loc_of_lip`): the
per-fibre map `x ↦ gradW (x − y)` is `L`-Lipschitz (a uniform, integrable bound against a
probability measure) and differentiable, so the parametric integral differentiates with derivative
the integral of the fibrewise derivatives. -/
theorem convolveFunctionMeasure_hasFDerivAt
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : Measure (PhysSpace d)) [IsProbabilityMeasure ρ]
    (h_int : ∀ x : PhysSpace d, Integrable (fun y => gradW (x - y)) ρ)
    (x₀ : PhysSpace d) :
    HasFDerivAt (fun x => convolveFunctionMeasure gradW ρ x)
      (∫ y, fderiv ℝ gradW (x₀ - y) ∂ρ) x₀ := by
  have hdiff : Differentiable ℝ gradW := hgradW_C1.differentiable one_ne_zero
  have hfderiv_cont : Continuous (fun z => fderiv ℝ gradW z) :=
    hgradW_C1.continuous_fderiv one_ne_zero
  have key := hasFDerivAt_integral_of_dominated_loc_of_lip
    (μ := ρ) (s := (Set.univ : Set (PhysSpace d))) (x₀ := x₀)
    (F := fun x y => gradW (x - y))
    (F' := fun y => fderiv ℝ gradW (x₀ - y))
    (bound := fun _ => (L : ℝ))
    (Filter.univ_mem)
    (Filter.Eventually.of_forall fun x =>
      (hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (h_int x₀)
    ((hfderiv_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun a => ?_)
    (integrable_const _)
    (Filter.Eventually.of_forall fun a => ?_)
  · have h2 := key.2
    simpa only [convolveFunctionMeasure] using h2
  · -- h_lip: `fun x => gradW (x - a)` is `L`-Lipschitz, hence `LipschitzOnWith (nnabs L)` on univ
    have hLip : LipschitzWith L (fun x : PhysSpace d => gradW (x - a)) := by
      refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
      have hd : dist (x - a) (y - a) = dist x y := by
        rw [dist_eq_norm, dist_eq_norm]; congr 1; abel
      calc dist (gradW (x - a)) (gradW (y - a))
          ≤ (L : ℝ) * dist (x - a) (y - a) := hL.dist_le_mul _ _
        _ = (L : ℝ) * dist x y := by rw [hd]
    rw [Real.nnabs_coe L]
    exact hLip.lipschitzOnWith
  · -- h_diff: `HasFDerivAt (fun x => gradW (x - a)) (fderiv ℝ gradW (x₀ - a)) x₀`
    have h1 : HasFDerivAt gradW (fderiv ℝ gradW (x₀ - a)) (x₀ - a) :=
      (hdiff (x₀ - a)).hasFDerivAt
    have h2 : HasFDerivAt (fun x : PhysSpace d => x - a)
        (ContinuousLinearMap.id ℝ (PhysSpace d)) x₀ :=
      (hasFDerivAt_id x₀).sub_const a
    have hc := h1.comp x₀ h2
    simpa [Function.comp_def] using hc

omit [NeZero d] in
/-- **C3 F2 — the Vlasov field is `C¹` in the phase-space variable, with the block Jacobian.**
At fixed time `t`, `vlasovVectorField gradW ρ t = fun (x,v) ↦ (v, −conv(x))` is
Fréchet-differentiable in `z = (x,v)` with derivative the block continuous-linear map
`δ ↦ (δ.2, −(D_x conv)(δ.1))`, where `D_x conv = ∫ y, fderiv ℝ gradW (z.1 − y) ∂(ρ t)` (F1).
This is the coefficient `A(t) := D_z b(t, Φ_t z)` of the variational ODE `M' = A(t)·M`. -/
theorem vlasovVectorField_hasFDerivAt_in_z
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d)) [∀ s, IsProbabilityMeasure (ρ s)]
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s))
    (t : ℝ) (z : PhaseSpace d) :
    HasFDerivAt (vlasovVectorField gradW ρ t)
      ((ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
        (-((∫ y, fderiv ℝ gradW (z.1 - y) ∂(ρ t)).comp
            (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))) z := by
  have hconv : HasFDerivAt (fun x => convolveFunctionMeasure gradW (ρ t) x)
      (∫ y, fderiv ℝ gradW (z.1 - y) ∂(ρ t)) z.1 :=
    convolveFunctionMeasure_hasFDerivAt gradW hgradW_C1 L hL (ρ t) (h_int t) z.1
  have hfst : HasFDerivAt (fun w : PhaseSpace d => w.1)
      (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)) z :=
    (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)).hasFDerivAt
  have h1 : HasFDerivAt (fun w : PhaseSpace d => w.2)
      (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)) z :=
    (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).hasFDerivAt
  have h2 : HasFDerivAt (fun w : PhaseSpace d => convolveFunctionMeasure gradW (ρ t) w.1)
      ((∫ y, fderiv ℝ gradW (z.1 - y) ∂(ρ t)).comp
        (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))) z :=
    hconv.comp z hfst
  have hprod := h1.prodMk h2.neg
  exact hprod

omit [NeZero d] in
/-- **C3 F1c — the convolution derivative is continuous in space.**  `x ↦ ∫ y, fderiv ℝ gradW
(x − y) ∂ρ` (the Fréchet derivative of the convolution field, F1) is continuous, by dominated
convergence: the integrand is continuous in `x` and bounded by `‖fderiv gradW‖ ≤ L` (a constant,
integrable against the probability measure `ρ`).  Continuity of the variational coefficient
`A(t)` in its spatial argument — half of the `t`-continuity of `A` (the other half is the
measure-curve regularity `t ↦ ρ t`, supplied at the V1c ODE-existence step). -/
theorem convolveFunctionMeasure_fderiv_continuous
    (gradW : PhysSpace d → PhysSpace d) (hgradW_C1 : ContDiff ℝ 1 gradW)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : Measure (PhysSpace d)) [IsProbabilityMeasure ρ] :
    Continuous (fun x => ∫ y, fderiv ℝ gradW (x - y) ∂ρ) := by
  have hfderiv_cont : Continuous (fun z => fderiv ℝ gradW z) :=
    hgradW_C1.continuous_fderiv one_ne_zero
  refine continuous_of_dominated
    (F := fun x y => fderiv ℝ gradW (x - y)) (bound := fun _ => (L : ℝ)) ?_ ?_ ?_ ?_
  · intro x
    exact (hfderiv_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  · intro x
    exact Filter.Eventually.of_forall (fun y => norm_fderiv_le_of_lipschitz (𝕜 := ℝ) hL)
  · exact integrable_const _
  · exact Filter.Eventually.of_forall (fun y =>
      hfderiv_cont.comp (continuous_id.sub continuous_const))

omit [NeZero d] in
/-- **C3 A-cont — the variational coefficient is continuous in time.**
Compose the convolution-derivative continuity with the flow, then express the block map as a
sum of continuous compositions.  This supplies the coefficient regularity for
`exists_fundamentalMatrix`. -/
lemma vlasovVariationalCoeff_continuousOn
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d) (T : ℝ) (z : PhaseSpace d)
    (hcontIcc : ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (hρD_cont : ContinuousOn
      (fun p : ℝ × PhysSpace d => ∫ y, fderiv ℝ gradW (p.2 - y) ∂(ρ p.1))
      (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d)))) :
    ContinuousOn (fun s => (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
      (-((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
          (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))) (Set.Icc 0 T) := by
  have hX : ContinuousOn (fun s => charX s z) (Set.Icc (0 : ℝ) T) :=
    continuous_fst.comp_continuousOn hcontIcc
  have hpair : ContinuousOn (fun s => ((s, charX s z) : ℝ × PhysSpace d)) (Set.Icc (0 : ℝ) T) :=
    continuousOn_id.prodMk hX
  have hmaps : Set.MapsTo (fun s => ((s, charX s z) : ℝ × PhysSpace d))
      (Set.Icc (0 : ℝ) T) (Set.Icc 0 T ×ˢ (Set.univ : Set (PhysSpace d))) :=
    fun s hs => ⟨hs, Set.mem_univ _⟩
  have hD : ContinuousOn (fun s => ∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)) (Set.Icc 0 T) :=
    hρD_cont.comp hpair hmaps
  have hDcomp : ContinuousOn (fun s => -((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
      (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))) (Set.Icc 0 T) :=
    (hD.clm_comp continuousOn_const).neg
  have heq : (fun s => (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d)).prod
        (-((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
            (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d)))))
      = (fun s => (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)).comp
            (ContinuousLinearMap.snd ℝ (PhysSpace d) (PhysSpace d))
          + (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)).comp
            (-((∫ y, fderiv ℝ gradW (charX s z - y) ∂(ρ s)).comp
                (ContinuousLinearMap.fst ℝ (PhysSpace d) (PhysSpace d))))) := by
    funext s; ext x <;> simp
  rw [heq]
  exact continuousOn_const.add (continuousOn_const.clm_comp hDcomp)

end Vlasov
