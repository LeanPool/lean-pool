/-
Copyright (c) 2026 Joseph K. Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph K. Miller
-/
module

public import LeanPool.Vlasov.OT.CharacteristicConstruction
import all LeanPool.Vlasov.OT.CharacteristicConstruction
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Characteristic flow for the Vlasov ODE + Lagrangian-Eulerian equivalence

This file builds on `LeanPool/Vlasov/OT/Coupling.lean` and provides the flow-side
infrastructure of the development:

* existence of the characteristic flow for the Vlasov field
  (`exists_vlasov_characteristicFlow`), via the vendored Picard–Lindelöf
  wrapper and a tight per-window construction valid for arbitrary Lipschitz
  constant;
* the Lagrangian → Eulerian equivalence — the pushforward of `f₀` under the
  characteristic flow satisfies the weak Vlasov equation;
* the localized solution predicates and the pushforward operator `Φ` feeding
  the well-posedness ladder, which lives in `LeanPool/Vlasov/OT/WellPosedness.lean`
  together with the marquee results.

The Grönwall step rests on the force estimate
‖∇W∗ρ − ∇W∗σ‖ ≤ L·W₁(ρ, σ) (`norm_convolveFunctionMeasure_sub_le`) and on
`wasserstein1_pushforward_le_iInf` from Coupling.lean.

**Mathlib-upstream targeting note.**  The position-Lipschitz of
convolution against a probability measure and the Picard-Lindelöf
wrapper for a phase-space ODE are domain-independent and Mathlib-
worthy; they would naturally live alongside the OT chapter in
`Mathlib/MeasureTheory/Wasserstein/CharacteristicFlow.lean` or split
between `Mathlib/Analysis/ODE/` and the OT chapter.  The Lagrangian →
Eulerian equivalence (pushforward of `f₀` under the characteristic
flow satisfies the weak Vlasov equation) is the genuine project
responsibility — a Fubini + measure-map +
differentiation-under-integral check that is not in Mathlib.

See `formalize/DESIGN.md` (in the source repository) for the overall design.
-/

@[expose] public section

namespace Vlasov

open MeasureTheory ENNReal

-- Preserve existing private names when moving their proofs.
private alias charFlowTight_perZ_trajectory :=
  _root_.Vlasov.charFlowTight_perZ_trajectory

private alias charFlowTight_piecewise_ode :=
  _root_.Vlasov.charFlowTight_piecewise_ode

private alias charFlowTight_window_forceBound :=
  _root_.Vlasov.charFlowTight_window_forceBound

private alias charFlowTight_window_step :=
  _root_.Vlasov.charFlowTight_window_step

private alias charFlowTight_window_velocity_carry :=
  _root_.Vlasov.charFlowTight_window_velocity_carry

private alias exists_vlasov_characteristicFlow_twoWindow._simp_1_2 :=
  _root_.Vlasov.exists_vlasov_characteristicFlow_twoWindow._simp_1_2

private alias exists_vlasov_characteristicFlow_twoWindow._simp_1_3 :=
  _root_.Vlasov.exists_vlasov_characteristicFlow_twoWindow._simp_1_3

private alias exists_vlasov_characteristicFlow_twoWindow._simp_1_4 :=
  _root_.Vlasov.exists_vlasov_characteristicFlow_twoWindow._simp_1_4

private alias exists_vlasov_characteristicFlow_twoWindow._simp_1_5 :=
  _root_.Vlasov.exists_vlasov_characteristicFlow_twoWindow._simp_1_5

private alias exists_vlasov_characteristicFlow_twoWindow._simp_1_6 :=
  _root_.Vlasov.exists_vlasov_characteristicFlow_twoWindow._simp_1_6

private alias exists_vlasov_characteristicFlow_twoWindow._simp_1_7 :=
  _root_.Vlasov.exists_vlasov_characteristicFlow_twoWindow._simp_1_7

private alias exists_vlasov_characteristicFlow_twoWindow._simp_1_8 :=
  _root_.Vlasov.exists_vlasov_characteristicFlow_twoWindow._simp_1_8

private alias flow_difference_growth_bound._abel_1_1 :=
  _root_.Vlasov.flow_difference_growth_bound._abel_1_1

private alias flow_difference_mild_bound._abel_1_1 :=
  _root_.Vlasov.flow_difference_mild_bound._abel_1_1

private alias flow_difference_mild_bound._abel_1_2 :=
  _root_.Vlasov.flow_difference_mild_bound._abel_1_2

private alias gronwall_envelope_exists._simp_1_1 :=
  _root_.Vlasov.gronwall_envelope_exists._simp_1_1

private alias gronwall_envelope_exists._simp_1_2 :=
  _root_.Vlasov.gronwall_envelope_exists._simp_1_2

private alias gronwall_envelope_exists._simp_1_3 :=
  _root_.Vlasov.gronwall_envelope_exists._simp_1_3

private alias gronwall_envelope_exists._simp_1_4 :=
  _root_.Vlasov.gronwall_envelope_exists._simp_1_4

private alias gronwall_envelope_exists._simp_1_5 :=
  _root_.Vlasov.gronwall_envelope_exists._simp_1_5

private alias gronwall_envelope_exists._simp_1_6 :=
  _root_.Vlasov.gronwall_envelope_exists._simp_1_6

private alias gronwall_envelope_exists._simp_1_7 :=
  _root_.Vlasov.gronwall_envelope_exists._simp_1_7

private alias hasDerivWithinAt_Icc_self :=
  _root_.Vlasov.hasDerivWithinAt_Icc_self

/-! ### Localized Vlasov-solution predicates on `[0, T]`

The globally-quantified predicates `IsVlasovSolution` and
`IsLagrangianVlasovSolution` (both in `Basic.lean`) require the weak PDE and
the characteristic flow to hold *universally in `t : ℝ`*.  For local existence
(`vlasovWellPosedness_local`), the Picard iteration only produces a solution
on a small time window `[0, T₀]`; the underlying characteristic flow comes
from `exists_vlasov_characteristicFlow_global_smallT`, which exposes
`IsCharacteristicFlowOn ... (Ioo 0 T) Set.univ` — open-interval ODE
behaviour, not the universal-in-`t` form `IsCharacteristicFlow` demands.

The `_On`-localized predicates below mirror the global ones with their
quantification restricted to `[0, T]`.  Local existence produces the
localized predicate; the forward-iteration continuation glues local windows
to recover the universal-in-`t` `IsLagrangianVlasovSolution` required by the
marquee `vlasovWellPosedness` theorem.

The `_On` family lives in this file so it can compose with
`IsCharacteristicFlowOn` (which lives here too); the global versions stay in
`Basic.lean` as the abstract endpoints. -/

/-- Localized weak Vlasov evolution equation on `Ioo 0 T`.  Same as
`WeakEvolutionEq` (`Basic.lean`) but with the derivative claim
restricted to the *open* interval `t ∈ Set.Ioo 0 T`.

**Why `Ioo` not `Icc`**: the characteristic flow only provides
ODE behaviour on `Ioo 0 T` (the boundary derivatives at `t = 0` and
`t = T` are genuinely unavailable from open-interval HasDerivAt alone).
The Vlasov solution's weak PDE inherits the same regularity: it holds on
the open interval where the characteristic flow is differentiable, and
the initial condition at `t = 0` is captured separately by the
pushforward equation in `IsLagrangianVlasovSolutionOn`. -/
def WeakEvolutionEqOn {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (μ : ℝ → Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (R_N : ℝ → ℝ) (T : ℝ) : Prop :=
  ∀ t ∈ Set.Ioo (0 : ℝ) T,
    HasDerivAt (fun s => ∫ z, φ z ∂μ s)
      (∫ z, (@inner ℝ (PhysSpace d) _ z.2 (gradXφ z) -
              @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (spatialMarginal (μ t)) z.1)
                (gradVφ z))
        ∂μ t
        + R_N t) t

/-- Localized Vlasov solution on `[0, T]`.  Mirror of `IsVlasovSolution`
with the weak PDE restricted to `[0, T]` via `WeakEvolutionEqOn`. -/
def IsVlasovSolutionOn {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) : Prop :=
  ∀ (φ : PhaseSpace d → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∀ (gradXφ gradVφ : PhaseSpace d → PhysSpace d),
      (∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1) →
      (∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2) →
      WeakEvolutionEqOn gradW f φ gradXφ gradVφ (fun _ => 0) T

/-- Localized Lagrangian Vlasov solution on `[0, T]`.  Mirror of
`IsLagrangianVlasovSolution` (`Basic.lean`) with:

* the weak PDE restricted to `[0, T]` (via `IsVlasovSolutionOn`),
* the characteristic flow restricted to `IsCharacteristicFlowOn ... (Ioo 0 T)
  Set.univ` (the natural output shape of the flow construction),
* the initial-condition clause stated explicitly (since `IsCharacteristicFlowOn`'s
  initial-condition clause is over `s_z`, here `Set.univ`, so it gives the
  same content; we restate it for direct usability),
* the pushforward equation restricted to `t ∈ Set.Icc 0 T`,
* the AEMeasurability clause restricted to `s ∈ Set.Icc 0 T`.

Every conjunct is the localized analogue of `IsLagrangianVlasovSolution`'s.
The forward-iteration continuation bridges to the global predicate by gluing
local windows. -/
def IsLagrangianVlasovSolutionOn {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (f : ℝ → Measure (PhaseSpace d)) (T : ℝ) : Prop :=
  IsVlasovSolutionOn gradW f T ∧
  ∃ charX charV : ℝ → PhaseSpace d → PhysSpace d,
    IsCharacteristicFlowOn gradW (fun t => spatialMarginal (f t)) charX charV
      (Set.Ioo 0 T) Set.univ ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      f t = Measure.map (fun z : PhaseSpace d => (charX t z, charV t z)) (f 0)) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) (f 0)) ∧
    -- **Boundary regularity**: the flow is continuous up to the *closed*
    -- window `[0, T]`.  This is the weakest-sufficient boundary fact for
    -- closed-window W₁-continuity soundness — closed-window W₁-continuity <==
    -- closed-window narrow continuity of `f` <== `ContinuousOn` of the flow
    -- (pushforward + DCT).  Exposed because the `Ioo`-only flow conjunct
    -- above leaves the endpoints `t ∈ {0,T}` unconstrained; producers supply
    -- this from data already in hand.
    (∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))

/-- A global `IsVlasovSolution` restricts to `IsVlasovSolutionOn T` for any
`T : ℝ`.  Projects the universal HasDerivAt claim onto `Ioo 0 T` by direct
specialization (the restricted set is open, so HasDerivAt and
HasDerivWithinAt coincide there). -/
lemma IsVlasovSolution.toOn {d : ℕ}
    {gradW : PhysSpace d → PhysSpace d}
    {f : ℝ → Measure (PhaseSpace d)} (h : IsVlasovSolution gradW f) (T : ℝ) :
    IsVlasovSolutionOn gradW f T := by
  intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t _ht
  exact h φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t

/-- A global `IsLagrangianVlasovSolution` restricts to
`IsLagrangianVlasovSolutionOn T` for any `T : ℝ`.

The flow witness restricts via `IsCharacteristicFlowOn`'s natural relationship
to the universal `IsCharacteristicFlow` (open Ioo ⊆ ℝ).  The pushforward and
AEMeasurability conjuncts restrict trivially since the originals are
universal. -/
lemma IsLagrangianVlasovSolution.toOn {d : ℕ}
    {gradW : PhysSpace d → PhysSpace d}
    {f : ℝ → Measure (PhaseSpace d)}
    (h : IsLagrangianVlasovSolution gradW f) (T : ℝ) :
    IsLagrangianVlasovSolutionOn gradW f T := by
  obtain ⟨h_sol, charX, charV, h_flow, h_push, h_meas⟩ := h
  refine ⟨h_sol.toOn T, charX, charV, ?_, ?_, ?_, ?_⟩
  · -- IsCharacteristicFlowOn from IsCharacteristicFlow.
    exact ⟨fun z _ => h_flow.1 z,
           fun t _ z _ => h_flow.2.1 t z,
           fun t _ z _ => h_flow.2.2 t z⟩
  · intro t _; exact h_push t
  · intro s _; exact h_meas s
  · -- Boundary ContinuousOn from universal HasDerivAt → continuity everywhere.
    intro z
    have hX : Continuous (fun s => charX s z) :=
      continuous_iff_continuousAt.mpr (fun t => (h_flow.2.1 t z).continuousAt)
    have hV : Continuous (fun s => charV s z) :=
      continuous_iff_continuousAt.mpr (fun t => (h_flow.2.2 t z).continuousAt)
    exact (hX.prodMk hV).continuousOn

/-! ## Lagrangian → Eulerian: pushforward solves weak Vlasov

The pushforward `vlasovSolutionViaPushforward charX charV f₀` satisfies
`IsVlasovSolution`.  This connects the ODE side (`IsCharacteristicFlow`,
pointwise `HasDerivAt`) to the PDE side (`IsVlasovSolution`,
`WeakEvolutionEq` distributional formulation), closing the Lagrangian-
Eulerian loop that Mathlib does not provide.

**Decomposition.**  Four named helpers, used as black boxes by the wrapper:

  * **SC.1** `vlasov_pushforward_integral_eq_compose` — change of
    variables: `∫ φ d(map flow_s f₀) = ∫ (φ ∘ flow_s) df₀`.  Direct
    `integral_map`.
  * **SC.2** `vlasov_traj_chain_rule` — pointwise chain rule:
    `HasDerivAt (s ↦ φ (charX s z, charV s z)) [formula] t`, using
    `hflow`'s ODE pointwise `HasDerivAt`s and the chain rule on `φ`.
  * **SC.3** `vlasov_pushforward_hasDerivAt_under_integral` —
    differentiation-under-integral via
    `hasDerivAt_integral_of_dominated_loc_of_lip`.  Requires a
    dominated-integrable Lipschitz bound on `s ↦ φ ∘ flow_s` uniform
    in `z`; this is the diff-under-integral technical heart.
  * **SC.4** `vlasov_rhs_pushforward_back` — push the chain-rule RHS
    back through `integral_map` to match `WeakEvolutionEq`'s shape.
    Symmetric to SC.1.

The wrapper composes them: SC.1 (rewrite LHS) → SC.3 (diff-under-integral,
consuming SC.2 pointwise) → SC.4 (rewrite RHS), together with the
AE-strong-measurability of the dot-product integrand (continuity threading
via smoothness of `φ` and Lipschitz of `gradW`). -/

/-- **SC.1: integral change-of-variables for the Vlasov pushforward.**
Direct application of `integral_map`. -/
lemma vlasov_pushforward_integral_eq_compose
    {d : ℕ}
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (s : ℝ)
    (h_meas : AEMeasurable (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (φ : PhaseSpace d → ℝ)
    (hφ_aesm : AEStronglyMeasurable φ
                  (vlasovSolutionViaPushforward charX charV f₀ s)) :
    ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s) =
      ∫ z, φ (charX s z, charV s z) ∂f₀ := by
  unfold vlasovSolutionViaPushforward
  exact integral_map h_meas hφ_aesm

/-- **SC.2: pointwise chain rule along the characteristic trajectory.**

For fixed `t` and fixed `z`, the curve `s ↦ φ (charX s z, charV s z)`
has derivative
`⟨charV t z, gradXφ (charX t z, charV t z)⟩
 − ⟨(∇W ∗ ρ_t)(charX t z), gradVφ (charX t z, charV t z)⟩`
at `t`.  Proof: chain rule on `φ ∘ (charX · z, charV · z)`, using
`hflow`'s pointwise `HasDerivAt`s and the gradient formula for `φ`'s
directional derivative. -/
lemma vlasov_traj_chain_rule
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (hX_deriv : ∀ t z, HasDerivAt (fun s => charX s z) (charV t z) t)
    (hV_deriv : ∀ t z, HasDerivAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) t)
    (t : ℝ) (z : PhaseSpace d) :
    HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t := by
  -- Strategy: (a) Joint pair has HasDerivAt with derivative
  -- `(charV t z, -(∇W∗ρ_t)(charX t z))`.
  -- (b) `φ` is `ContDiff` so has an FDeriv at the image point.
  -- (c) Chain rule (`HasFDerivAt.comp_hasDerivAt`) gives HasDerivAt of
  -- the composite, with derivative `fderiv φ (flow_t z) (charV t z, -(∇W∗ρ_t)(charX t z))`.
  -- (d) The product fderiv splits via the gradient formula:
  --     `fderiv φ (x,v) (a,b) = ⟨gradXφ (x,v), a⟩ + ⟨gradVφ (x,v), b⟩`.
  -- (e) Substituting `(a,b) := (charV t z, -(∇W∗ρ_t)(charX t z))` and using
  --     bilinearity of inner product with the negation gives the claimed formula.
  --
  -- Step (a): joint pair HasDerivAt
  have hpair : HasDerivAt (fun s => (charX s z, charV s z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) t :=
    (hX_deriv t z).prodMk (hV_deriv t z)
  -- Step (b): φ has FDeriv at the image point
  have hFDeriv : HasFDerivAt φ (fderiv ℝ φ (charX t z, charV t z)) (charX t z, charV t z) :=
    (hφ_smooth.differentiable (by simp) _).hasFDerivAt
  -- Step (c): chain rule
  have hchain : HasDerivAt (fun s => φ (charX s z, charV s z))
      ((fderiv ℝ φ (charX t z, charV t z))
        (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z)))) t :=
    hFDeriv.comp_hasDerivAt t hpair
  -- Step (d): compute the value equality
  have hval : (fderiv ℝ φ (charX t z, charV t z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) =
      @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z)) := by
    -- Set up partial derivative identities (same pattern as h_integrand_aesm)
    set z₀ := (charX t z, charV t z)
    have hdiffφ : DifferentiableAt ℝ φ z₀ :=
      hφ_smooth.differentiable (by simp) z₀
    have hfderiv_X : fderiv ℝ (fun x => φ (x, z₀.2)) z₀.1 =
        (fderiv ℝ φ z₀).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z₀) z₀ := hdiffφ.hasFDerivAt
      have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z₀.2))
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z₀.1 :=
        hasFDerivAt_prodMk_left z₀.1 z₀.2
      exact (h1.comp z₀.1 h2).fderiv
    have hfderiv_V : fderiv ℝ (fun v => φ (z₀.1, v)) z₀.2 =
        (fderiv ℝ φ z₀).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z₀) z₀ := hdiffφ.hasFDerivAt
      have h2 : HasFDerivAt (fun v : PhysSpace d => (z₀.1, v))
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z₀.2 :=
        hasFDerivAt_prodMk_right z₀.1 z₀.2
      exact (h1.comp z₀.2 h2).fderiv
    -- Decompose fderiv φ z₀ applied to (a, b) via inl/inr
    set F := fderiv ℝ φ z₀
    set a := charV t z
    set b := -(convolveFunctionMeasure gradW (ρ t) (charX t z))
    have hdecomp : F (a, b) = F (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) +
        F (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) := by
      rw [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
      simp [← F.map_add]
    -- Differentiability of partial functions
    have hdiffX : DifferentiableAt ℝ (fun x => φ (x, z₀.2)) z₀.1 :=
      hdiffφ.comp z₀.1 (differentiableAt_id.prodMk (differentiableAt_const z₀.2))
    have hdiffV : DifferentiableAt ℝ (fun v => φ (z₀.1, v)) z₀.2 :=
      hdiffφ.comp z₀.2 ((differentiableAt_const z₀.1).prodMk differentiableAt_id)
    -- The two partial gradient inner products
    have hX_inner : (fderiv ℝ φ z₀) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) =
        @inner ℝ (PhysSpace d) _ a (gradXφ z₀) := by
      have hstep : (fderiv ℝ φ z₀) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) =
          fderiv ℝ (fun x => φ (x, z₀.2)) z₀.1 a := by rw [hfderiv_X]; rfl
      rw [hstep, ← inner_gradient_left, ← hgradXφ z₀, real_inner_comm]
    have hV_inner : (fderiv ℝ φ z₀) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) =
        @inner ℝ (PhysSpace d) _ b (gradVφ z₀) := by
      have hstep : (fderiv ℝ φ z₀) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) =
          fderiv ℝ (fun v => φ (z₀.1, v)) z₀.2 b := by rw [hfderiv_V]; rfl
      rw [hstep, ← inner_gradient_left, ← hgradVφ z₀, real_inner_comm]
    rw [hdecomp, hX_inner, hV_inner, show b = -(convolveFunctionMeasure gradW (ρ t) (charX t z))
        from rfl, inner_neg_left]
    ring
  rwa [hval] at hchain

/-- **`_at` variant of SC.2: pointwise chain rule at a specific `(t, z)`**.

Mirror of `vlasov_traj_chain_rule` (just above), generalized to take the
flow's HasDerivAt hypotheses at the specific `(t, z)` of interest rather
than universally `∀ t z`.  This is the form needed by the `_On` PDE
transport: the flow construction produces `IsCharacteristicFlowOn
... (Ioo 0 T) Set.univ` which gives HasDerivAt only at `t ∈ Ioo 0 T`, so
the universal-`t` form can't be supplied.

This `_at` variant is the foundation; downstream `_on` variants of the
SC.5-SC.8 helpers and the `vlasov_pushforward_hasDerivAt_under_integral`
consumer all compose against this one.

**Proof body**: identical to `vlasov_traj_chain_rule`'s body modulo the
hypothesis-naming.  The original uses `hX_deriv t z`, `hV_deriv t z`
exactly once each (at the `prodMk` step); we replace these with
`hX_deriv_at`, `hV_deriv_at` directly.  All other steps are
specific-`(t, z)` already. -/
lemma vlasov_traj_chain_rule_at
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (t : ℝ) (z : PhaseSpace d)
    (hX_deriv_at : HasDerivAt (fun s => charX s z) (charV t z) t)
    (hV_deriv_at : HasDerivAt (fun s => charV s z)
        (-(convolveFunctionMeasure gradW (ρ t) (charX t z))) t) :
    HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t := by
  -- Step (a): joint pair HasDerivAt — uses hX_deriv_at, hV_deriv_at directly.
  have hpair : HasDerivAt (fun s => (charX s z, charV s z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) t :=
    hX_deriv_at.prodMk hV_deriv_at
  -- Step (b): φ has FDeriv at the image point.
  have hFDeriv : HasFDerivAt φ (fderiv ℝ φ (charX t z, charV t z)) (charX t z, charV t z) :=
    (hφ_smooth.differentiable (by simp) _).hasFDerivAt
  -- Step (c): chain rule.
  have hchain : HasDerivAt (fun s => φ (charX s z, charV s z))
      ((fderiv ℝ φ (charX t z, charV t z))
        (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z)))) t :=
    hFDeriv.comp_hasDerivAt t hpair
  -- Step (d): compute the value equality (identical to original).
  have hval : (fderiv ℝ φ (charX t z, charV t z))
      (charV t z, -(convolveFunctionMeasure gradW (ρ t) (charX t z))) =
      @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z)) := by
    set z₀ := (charX t z, charV t z)
    have hdiffφ : DifferentiableAt ℝ φ z₀ :=
      hφ_smooth.differentiable (by simp) z₀
    have hfderiv_X : fderiv ℝ (fun x => φ (x, z₀.2)) z₀.1 =
        (fderiv ℝ φ z₀).comp (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z₀) z₀ := hdiffφ.hasFDerivAt
      have h2 : HasFDerivAt (fun x : PhysSpace d => (x, z₀.2))
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d)) z₀.1 :=
        hasFDerivAt_prodMk_left z₀.1 z₀.2
      exact (h1.comp z₀.1 h2).fderiv
    have hfderiv_V : fderiv ℝ (fun v => φ (z₀.1, v)) z₀.2 =
        (fderiv ℝ φ z₀).comp (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) := by
      have h1 : HasFDerivAt φ (fderiv ℝ φ z₀) z₀ := hdiffφ.hasFDerivAt
      have h2 : HasFDerivAt (fun v : PhysSpace d => (z₀.1, v))
          (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d)) z₀.2 :=
        hasFDerivAt_prodMk_right z₀.1 z₀.2
      exact (h1.comp z₀.2 h2).fderiv
    set F := fderiv ℝ φ z₀
    set a := charV t z
    set b := -(convolveFunctionMeasure gradW (ρ t) (charX t z))
    have hdecomp : F (a, b) = F (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) +
        F (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) := by
      rw [ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply]
      simp [← F.map_add]
    have hdiffX : DifferentiableAt ℝ (fun x => φ (x, z₀.2)) z₀.1 :=
      hdiffφ.comp z₀.1 (differentiableAt_id.prodMk (differentiableAt_const z₀.2))
    have hdiffV : DifferentiableAt ℝ (fun v => φ (z₀.1, v)) z₀.2 :=
      hdiffφ.comp z₀.2 ((differentiableAt_const z₀.1).prodMk differentiableAt_id)
    have hX_inner : (fderiv ℝ φ z₀) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) =
        @inner ℝ (PhysSpace d) _ a (gradXφ z₀) := by
      have hstep : (fderiv ℝ φ z₀) (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d) a) =
          fderiv ℝ (fun x => φ (x, z₀.2)) z₀.1 a := by rw [hfderiv_X]; rfl
      rw [hstep, ← inner_gradient_left, ← hgradXφ z₀, real_inner_comm]
    have hV_inner : (fderiv ℝ φ z₀) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) =
        @inner ℝ (PhysSpace d) _ b (gradVφ z₀) := by
      have hstep : (fderiv ℝ φ z₀) (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d) b) =
          fderiv ℝ (fun v => φ (z₀.1, v)) z₀.2 b := by rw [hfderiv_V]; rfl
      rw [hstep, ← inner_gradient_left, ← hgradVφ z₀, real_inner_comm]
    rw [hdecomp, hX_inner, hV_inner, show b = -(convolveFunctionMeasure gradW (ρ t) (charX t z))
        from rfl, inner_neg_left]
    ring
  rwa [hval] at hchain

/-- **Dominated-bundle data for SC.3.**

Packages the four ancillary hypotheses required by Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_lip` (excluding the pointwise
`HasDerivAt` which SC.2 already provides):
  * a neighborhood `nhd ∈ nhds t` on which the dominated Lipschitz bound holds;
  * eventual AE-strong-measurability of `(z ↦ φ ∘ flow_s)` for `s` near `t`;
  * integrability of the integrand at `s = t`;
  * AE-strong-measurability of the pointwise derivative as a function of `z`;
  * a `bound : PhaseSpace d → ℝ` with `Integrable bound f₀` such that, ae-z,
    the curve `s ↦ φ(charX s z, charV s z)` is `Real.nnabs (bound z)`-Lipschitz
    on `nhd`.

The dominated-bound clause is the technical heart: deriving it requires
a uniform-in-`z` bound on the flow speed `(charV s z, V'(s,z))` on the
support of `φ`, which the eventual `vlasovWellPosedness` caller will
produce from Picard-Lindelof local-flow boundedness + `HasCompactSupport φ`. -/
def DiffUnderIntegralData
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (t : ℝ) : Prop :=
  ∃ (nhd : Set ℝ) (bound : PhaseSpace d → ℝ),
    nhd ∈ nhds t ∧
    (∀ᶠ s' in nhds t,
      AEStronglyMeasurable (fun z => φ (charX s' z, charV s' z)) f₀) ∧
    Integrable (fun z => φ (charX t z, charV t z)) f₀ ∧
    AEStronglyMeasurable
      (fun z => @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
                - @inner ℝ (PhysSpace d) _
                    (convolveFunctionMeasure gradW (ρ t) (charX t z))
                    (gradVφ (charX t z, charV t z))) f₀ ∧
    (∀ᵐ z ∂f₀,
      LipschitzOnWith (Real.nnabs (bound z))
        (fun s' => φ (charX s' z, charV s' z)) nhd) ∧
    Integrable bound f₀

/-- **SC.3: differentiation under the integral for the pushforward integral.**

`HasDerivAt (s ↦ ∫ z, φ (charX s z, charV s z) ∂f₀) (∫ z, [pointwise deriv] ∂f₀) t`,
where the pointwise derivative at `t` is the chain-rule formula from SC.2.

Proven by direct application of Mathlib's
`hasDerivAt_integral_of_dominated_loc_of_lip`, given the
`DiffUnderIntegralData` bundle and the pointwise derivative from SC.2.

Taking `h_data : DiffUnderIntegralData ...` as a hypothesis keeps SC.3's
body a one-line Mathlib application; the burden of producing the
dominated-bundle data moves to the caller (discharged from compact support
of `φ` plus Picard regularity). -/
lemma vlasov_pushforward_hasDerivAt_under_integral
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (t : ℝ)
    (h_pointwise : ∀ z, HasDerivAt (fun s => φ (charX s z, charV s z))
      (@inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
       - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) (charX t z))
          (gradVφ (charX t z, charV t z))) t)
    (h_data : DiffUnderIntegralData gradW ρ charX charV f₀ φ gradXφ gradVφ t) :
    HasDerivAt (fun s => ∫ z, φ (charX s z, charV s z) ∂f₀)
      (∫ z, @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
            - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW (ρ t) (charX t z))
                (gradVφ (charX t z, charV t z))
          ∂f₀) t := by
  obtain ⟨nhd, bound, hnhd, hF_meas, hF_int, hF'_meas, h_lipsch, h_bound_int⟩ := h_data
  exact (hasDerivAt_integral_of_dominated_loc_of_lip
    (μ := f₀) (x₀ := t) (bound := bound) (s := nhd)
    (F := fun s' z => φ (charX s' z, charV s' z))
    hnhd hF_meas hF_int hF'_meas
    h_lipsch h_bound_int
    (Filter.Eventually.of_forall h_pointwise)).2

/-- **SC.4: push the chain-rule RHS back through `integral_map`.**

`∫ z, [formula(charX t z, charV t z)] df₀ = ∫ y, [formula(y)] d(map flow_t f₀)`.

Symmetric to SC.1; the same `integral_map` invocation, applied to the
dot-product integrand.  Closes by `integral_map` after establishing AE-
strong-measurability of the integrand. -/
lemma vlasov_rhs_pushforward_back
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (t : ℝ)
    (h_meas : AEMeasurable (fun z : PhaseSpace d => (charX t z, charV t z)) f₀)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (h_integrand_aesm : AEStronglyMeasurable
      (fun y : PhaseSpace d =>
        @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
        - @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW
              (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) y.1)
            (gradVφ y))
      (vlasovSolutionViaPushforward charX charV f₀ t)) :
    ∫ z, @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
         - @inner ℝ (PhysSpace d) _
            (convolveFunctionMeasure gradW
              (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
              (charX t z))
            (gradVφ (charX t z, charV t z))
        ∂f₀
      = ∫ y, @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
             - @inner ℝ (PhysSpace d) _
                (convolveFunctionMeasure gradW
                  (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) y.1)
                (gradVφ y)
            ∂(vlasovSolutionViaPushforward charX charV f₀ t) := by
  -- Direct application of integral_map in reverse direction, on the dot-product
  -- integrand.  The integrand at `(charX t z, charV t z)` is precisely the
  -- pre-image of the y-integrand under the pushforward map.
  unfold vlasovSolutionViaPushforward at h_integrand_aesm ⊢
  exact (integral_map h_meas h_integrand_aesm).symm

/-! ## Lagrangian → Eulerian bundle sub-helpers (SC.5 – SC.8)

The `DiffUnderIntegralData` bundle inside the wrapper is decomposed
into four named regularity sub-helpers:

  * **SC.5** `vlasov_compose_flow_aestronglymeas` — eventual
    AE-strong-measurability of `φ ∘ flow_s` near `t`.
  * **SC.6** `vlasov_compose_flow_integrable_at` — integrability of
    `φ ∘ flow_t` against `f₀` (uses `HasCompactSupport φ`).
  * **SC.7** `vlasov_pointwise_deriv_aestronglymeas` — AE-strong-
    measurability of the chain-rule pointwise derivative (same shape
    as the wrapper's `h_integrand_aesm` proof).
  * **SC.8** `vlasov_trajectory_lipschitz_bound` — the dominated
    Lipschitz bound on `s ↦ φ(charX s z, charV s z)` with an
    `f₀`-integrable Lipschitz coefficient, from a uniform velocity bound
    on `nhd × (flow_t)⁻¹(supp φ)`. -/

/-- **SC.5: AE-strong-measurability of `φ ∘ flow_s` for s near t.**

The composition `z ↦ φ (charX s' z, charV s' z)` is AE-strongly-
measurable wrt `f₀` for every `s'`, in particular for `s'` in any
neighborhood of `t`.  Uses continuity of `φ` plus
`h_flow_meas`'s AE-measurability of the flow pair. -/
lemma vlasov_compose_flow_aestronglymeas
    {d : ℕ}
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ) (hφ_cont : Continuous φ)
    (h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (t : ℝ) :
    ∀ᶠ s' in nhds t, AEStronglyMeasurable
      (fun z => φ (charX s' z, charV s' z)) f₀ := by
  apply Filter.Eventually.of_forall
  intro s'
  exact hφ_cont.comp_aestronglyMeasurable (h_flow_meas s').aestronglyMeasurable

/-- **SC.6: Integrability of `φ ∘ flow_t` against `f₀`.**

`HasCompactSupport φ` + `Continuous φ` give boundedness; combined with
`[IsProbabilityMeasure f₀]` this yields integrability. -/
lemma vlasov_compose_flow_integrable_at
    {d : ℕ}
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (φ : PhaseSpace d → ℝ)
    (hφ_cont : Continuous φ)
    (hφ_compact : HasCompactSupport φ)
    (t : ℝ)
    (h_flow_meas_t : AEMeasurable
      (fun z : PhaseSpace d => (charX t z, charV t z)) f₀) :
    Integrable (fun z => φ (charX t z, charV t z)) f₀ := by
  obtain ⟨C, hC⟩ := hφ_cont.bounded_above_of_compact_support hφ_compact
  exact Integrable.of_bound
    (hφ_cont.comp_aestronglyMeasurable h_flow_meas_t.aestronglyMeasurable)
    C (Filter.Eventually.of_forall (fun z => hC _))

/-- **SC.7: AE-strong-measurability of the pointwise derivative.**

The chain-rule pointwise derivative integrand
`⟨charV t z, gradXφ(flow_t z)⟩ - ⟨convolve_t(charX t z), gradVφ(flow_t z)⟩`
is AE-strongly-measurable wrt `f₀`.  Same continuity argument as the
wrapper's `h_integrand_aesm` proof. -/
lemma vlasov_pointwise_deriv_aestronglymeas
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d))
    (φ : PhaseSpace d → ℝ) (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (gradXφ gradVφ : PhaseSpace d → PhysSpace d)
    (hgradXφ : ∀ z, gradXφ z = gradient (fun x => φ (x, z.2)) z.1)
    (hgradVφ : ∀ z, gradVφ z = gradient (fun v => φ (z.1, v)) z.2)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW (ρ s) x))
    (t : ℝ)
    (h_flow_meas_t : AEMeasurable
      (fun z : PhaseSpace d => (charX t z, charV t z)) f₀) :
    AEStronglyMeasurable
      (fun z => @inner ℝ (PhysSpace d) _ (charV t z) (gradXφ (charX t z, charV t z))
                - @inner ℝ (PhysSpace d) _
                    (convolveFunctionMeasure gradW (ρ t) (charX t z))
                    (gradVφ (charX t z, charV t z))) f₀ := by
  -- The integrand factors as g ∘ (fun z => (charX t z, charV t z)), where
  -- g : PhaseSpace d → ℝ is the same continuous function as in the wrapper's
  -- h_integrand_aesm (g y = ⟨y.2, gradXφ y⟩ - ⟨convolve y.1, gradVφ y⟩).
  -- Step 1: establish that gradXφ and gradVφ are continuous (same argument as wrapper).
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
  have hfderiv_V : ∀ z : PhaseSpace d,
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
  -- Step 2: show that g : PhaseSpace d → ℝ is continuous.
  have hg_cont : Continuous (fun y : PhaseSpace d =>
      @inner ℝ (PhysSpace d) _ y.2 (gradXφ y)
      - @inner ℝ (PhysSpace d) _
          (convolveFunctionMeasure gradW (ρ t) y.1) (gradVφ y)) := by
    apply Continuous.sub
    · apply Continuous.inner continuous_snd
      simp_rw [heqX, gradient, hfderiv_X]
      exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
        ((ContinuousLinearMap.isBoundedLinearMap_comp_right
          (ContinuousLinearMap.inl ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
          (hφ_smooth.continuous_fderiv (by simp)))
    · apply Continuous.inner
      · exact (hconv_cont t).comp continuous_fst
      · simp_rw [heqV, gradient, hfderiv_V]
        exact (InnerProductSpace.toDual ℝ (PhysSpace d)).symm.continuous.comp
          ((ContinuousLinearMap.isBoundedLinearMap_comp_right
            (ContinuousLinearMap.inr ℝ (PhysSpace d) (PhysSpace d))).continuous.comp
            (hφ_smooth.continuous_fderiv (by simp)))
  -- Step 3: the integrand equals g ∘ flow. Apply Continuous.comp_aestronglyMeasurable.
  exact hg_cont.comp_aestronglyMeasurable h_flow_meas_t.aestronglyMeasurable


/-- **`_on` variant of SC.8** — `vlasov_trajectory_lipschitz_bound` with
`IsCharacteristicFlowOn ... (Ioo 0 T) Set.univ` instead of universal
`IsCharacteristicFlow`, and with boundary regularity hypotheses
(`h_init`, `h_cont_Icc`, `h_deriv_Ico`) supplied explicitly.  Required by
the `_On` PDE transport (`vlasovSolutionViaPushforward_isVlasovSolutionOn`).

The proof combines `flow_distance_growth_bound_on` with the flow's local
ODE and a uniform derivative bound for the compactly supported test function.
The global `vlasov_trajectory_lipschitz_bound_lag` follows by restricting its
flow to a suitable finite interval.

The neighborhood `nhd` is chosen to stay within `Ioo 0 T` (where `hflow_on`
is defined), e.g. `Ioo (max 0 (t/2)) (min T (t + 1/2))`. -/
lemma vlasov_trajectory_lipschitz_bound_on
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    {T : ℝ} (hT : 0 < T)
    (hflow_on : IsCharacteristicFlowOn gradW ρ charX charV
                                       (Set.Ioo 0 T) Set.univ)
    -- Boundary regularity for `flow_distance_growth_bound_on`.
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc 0 T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z))
        (Set.Ici s) s)
    (_hgradW_cont : Continuous gradW)
    (_hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW (ρ s) x))
    (t : ℝ) (ht : t ∈ Set.Ioo (0 : ℝ) T)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc 0 T, ∫ y, ‖y‖ ∂(ρ s) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc 0 T,
      Integrable (fun y : PhysSpace d => ‖y‖) (ρ s))
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s)) :
    ∃ (nhd : Set ℝ) (bound : PhaseSpace d → ℝ),
      nhd ∈ nhds t ∧
      (∀ᵐ z ∂f₀, LipschitzOnWith (Real.nnabs (bound z))
        (fun s' => φ (charX s' z, charV s' z)) nhd) ∧
      Integrable bound f₀ := by
  -- Step 1: Get Gronwall growth bound C_T on [0, T].
  obtain ⟨C_T, hC_T_nn, hC_T⟩ := flow_distance_growth_bound_on gradW L hL ρ charX charV
      T (le_of_lt hT) h_init h_cont_Icc h_deriv_Ico M_ρ hM_ρ_nn hM_ρ h_y_int h_int
  -- Step 2: Bound ‖fderiv ℝ φ‖ uniformly (compact support + continuous fderiv).
  have hφ_diff : Differentiable ℝ φ := hφ_smooth.differentiable (by norm_num)
  have hfderiv_cont : Continuous (fderiv ℝ φ) :=
    hφ_smooth.continuous_fderiv (by norm_num)
  have hfderiv_compact : HasCompactSupport (fderiv ℝ φ) :=
    HasCompactSupport.fderiv (𝕜 := ℝ) hφ_compact
  obtain ⟨M_φ, hM_φ⟩ := hfderiv_cont.bounded_above_of_compact_support hfderiv_compact
  have hM_φ_nn : 0 ≤ M_φ :=
    le_trans (norm_nonneg (fderiv ℝ φ (0 : PhaseSpace d))) (hM_φ _)
  -- Gronwall constants: K = 1 + L, ε₀ = ‖gradW 0‖ + L * M_ρ.
  set K := 1 + (L : ℝ)
  set ε₀ := ‖gradW 0‖ + (L : ℝ) * M_ρ
  have hK_pos : 0 < K := by positivity
  have hε₀_nn : 0 ≤ ε₀ := by positivity
  -- Convolution bound on [0, T].
  have h_conv_bound : ∀ s ∈ Set.Icc 0 T, ∀ x : PhysSpace d,
      ‖convolveFunctionMeasure gradW (ρ s) x‖ ≤ ε₀ + (L : ℝ) * ‖x‖ := by
    intro s hs x
    exact norm_convolveFunctionMeasure_le_affine gradW L hL (ρ s) (h_int s)
      (h_y_int s hs) M_ρ (hM_ρ s hs) x
  -- Step 3: Choose nhd = Ioo (t/2) ((t+T)/2) ⊆ Ioo 0 T.  t/2 < t (since t>0) and
  -- t < (t+T)/2 (since t < T), so t ∈ nhd; further nhd ⊆ Icc 0 T for bounding.
  refine ⟨Set.Ioo (t / 2) ((t + T) / 2),
    fun z => M_φ * (K * C_T + ε₀) * (‖z‖ + 1), ?_, ?_, ?_⟩
  · -- nhd ∈ nhds t.
    exact Ioo_mem_nhds (by linarith [ht.1]) (by linarith [ht.2])
  · -- LipschitzOnWith for ae-z, via MVT on the convex nhd.
    apply Filter.Eventually.of_forall
    intro z
    let deriv_val : ℝ → PhaseSpace d → ℝ := fun s z =>
      (fderiv ℝ φ (charX s z, charV s z))
        (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))
    apply Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_Ioo _ _)
      (f' := fun s => deriv_val s z)
    · -- HasDerivWithinAt for each s ∈ nhd; uses hflow_on at s ∈ Ioo 0 T.
      intro s hs
      have hs_Ioo : s ∈ Set.Ioo (0 : ℝ) T :=
        ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
      have hX_at := hflow_on.2.1 s hs_Ioo z (Set.mem_univ z)
      have hV_at := hflow_on.2.2 s hs_Ioo z (Set.mem_univ z)
      have h_flow_deriv : HasDerivAt (fun s' => (charX s' z, charV s' z))
          (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z))) s :=
        hX_at.prodMk hV_at
      have h_φ_fderiv : HasFDerivAt φ (fderiv ℝ φ (charX s z, charV s z))
          (charX s z, charV s z) :=
        hφ_diff (charX s z, charV s z) |>.hasFDerivAt
      exact (h_φ_fderiv.comp_hasDerivAt s h_flow_deriv).hasDerivWithinAt
    · -- Bound ‖deriv_val s z‖₊ ≤ M_φ * (K * C_T + ε₀) * (‖z‖ + 1).
      intro s hs
      rw [← NNReal.coe_le_coe]
      simp only []
      have hs_mem : s ∈ Set.Icc 0 T :=
        ⟨le_of_lt (by linarith [hs.1, ht.1]),
         le_of_lt (by linarith [hs.2, ht.2])⟩
      have h_flow_bnd : ‖(charX s z, charV s z)‖ ≤ C_T * (‖z‖ + 1) :=
        hC_T s hs_mem z
      have h_x_bnd : ‖charX s z‖ ≤ C_T * (‖z‖ + 1) := by
        have hpn : ‖(charX s z, charV s z)‖ = max ‖charX s z‖ ‖charV s z‖ :=
          Prod.norm_def _
        linarith [le_max_left ‖charX s z‖ ‖charV s z‖, hpn ▸ h_flow_bnd]
      have h_v_bnd2 : ‖charV s z‖ ≤ C_T * (‖z‖ + 1) := by
        have hpn : ‖(charX s z, charV s z)‖ = max ‖charX s z‖ ‖charV s z‖ :=
          Prod.norm_def _
        linarith [le_max_right ‖charX s z‖ ‖charV s z‖, hpn ▸ h_flow_bnd]
      have h_c_bnd : ‖convolveFunctionMeasure gradW (ρ s) (charX s z)‖ ≤
          ε₀ + (L : ℝ) * C_T * (‖z‖ + 1) := by
        have := h_conv_bound s hs_mem (charX s z)
        linarith [mul_le_mul_of_nonneg_left h_x_bnd (NNReal.coe_nonneg L)]
      have h_vel_bnd : ‖(charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))‖
          ≤ K * C_T * (‖z‖ + 1) + ε₀ := by
        rw [Prod.norm_def]
        simp only [norm_neg]
        have hK1 : (1 : ℝ) ≤ K := by linarith [NNReal.coe_nonneg L]
        have hz1 : (0 : ℝ) ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
        apply max_le
        · have h1 : C_T * (‖z‖ + 1) ≤ K * C_T * (‖z‖ + 1) := by
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK1 hC_T_nn) hz1
            linarith
          linarith
        · have hLK : (L : ℝ) ≤ K := by linarith [NNReal.coe_nonneg L]
          have h2 : (L : ℝ) * C_T * (‖z‖ + 1) ≤ K * C_T * (‖z‖ + 1) := by
            have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hLK hC_T_nn) hz1
            linarith
          linarith
      rw [Real.coe_nnabs, abs_of_nonneg (by positivity)]
      calc ‖deriv_val s z‖
          ≤ ‖fderiv ℝ φ (charX s z, charV s z)‖ *
            ‖(charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ M_φ * (K * C_T * (‖z‖ + 1) + ε₀) := by
            apply mul_le_mul (hM_φ _) h_vel_bnd (norm_nonneg _) hM_φ_nn
        _ ≤ M_φ * (K * C_T + ε₀) * (‖z‖ + 1) := by
            have hz1 : 1 ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
            nlinarith [mul_nonneg hM_φ_nn hε₀_nn,
                       mul_nonneg (mul_nonneg hM_φ_nn hε₀_nn)
                         (by linarith [norm_nonneg z] : (0 : ℝ) ≤ ‖z‖),
                       mul_nonneg hM_φ_nn hC_T_nn]
  · -- Integrable bound.
    have h_bound_eq : (fun z : PhaseSpace d => M_φ * (K * C_T + ε₀) * (‖z‖ + 1)) =
        fun z => M_φ * (K * C_T + ε₀) * ‖z‖ + M_φ * (K * C_T + ε₀) := by
      ext z; ring
    rw [h_bound_eq]
    exact (hf₀_fm.const_mul _).add (integrable_const _)

/-- **`_lag` variant of SC.8** — `vlasov_trajectory_lipschitz_bound` with the
flow-growth prerequisites supplied as explicit hypotheses, enabling the
dominated Lipschitz bound to be derived via Gronwall on the characteristic
ODE (see `flow_distance_growth_bound` above).  Used by `_lag` variants
of the Lagrangian → Eulerian chain that route through
`IsLagrangianVlasovSolution`. -/
lemma vlasov_trajectory_lipschitz_bound_lag
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ s, IsProbabilityMeasure (ρ s)]
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (φ : PhaseSpace d → ℝ)
    (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_compact : HasCompactSupport φ)
    (hflow : IsCharacteristicFlow gradW ρ charX charV)
    (_hgradW_cont : Continuous gradW)
    (_hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW (ρ s) x))
    (t : ℝ) (ht_pos : 0 < t)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc 0 (t + 1), ∫ y, ‖y‖ ∂(ρ s) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc 0 (t + 1),
      Integrable (fun y : PhysSpace d => ‖y‖) (ρ s))
    (h_int : ∀ s (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ s)) :
    ∃ (nhd : Set ℝ) (bound : PhaseSpace d → ℝ),
      nhd ∈ nhds t ∧
      (∀ᵐ z ∂f₀, LipschitzOnWith (Real.nnabs (bound z))
        (fun s' => φ (charX s' z, charV s' z)) nhd) ∧
      Integrable bound f₀ := by
  obtain ⟨hflow_init, hflow_x, hflow_v⟩ := hflow
  refine vlasov_trajectory_lipschitz_bound_on gradW L hL ρ charX charV f₀ hf₀_fm
    φ hφ_smooth hφ_compact (T := t + 1) (by linarith)
    ⟨fun z _ => hflow_init z, fun s _ z _ => hflow_x s z,
      fun s _ z _ => hflow_v s z⟩
    (fun z => Prod.ext (hflow_init z).1 (hflow_init z).2) ?_ ?_
    _hgradW_cont _hconv_cont t ⟨ht_pos, lt_add_one t⟩ M_ρ hM_ρ_nn hM_ρ h_y_int h_int
  · intro z
    exact continuousOn_of_forall_continuousAt fun s _ =>
      (hflow_x s z).continuousAt.prodMk (hflow_v s z).continuousAt
  · intro z s _
    exact ((hflow_x s z).prodMk (hflow_v s z)).hasDerivWithinAt

/-- **`_On`-flavored Lagrangian → Eulerian producer for `IsVlasovSolutionOn`**.

The `_on` analog of `vlasovSolutionViaPushforward_isVlasovSolution`,
taking the characteristic flow in `IsCharacteristicFlowOn ...
(Set.Ioo 0 T) Set.univ` form (the flow construction's natural output) and
producing the weak Vlasov PDE in localized `IsVlasovSolutionOn` form (also
on `Ioo 0 T`).

The global proof's structure transports to the `_On` form:
* `intro t` becomes `intro t ht` with `ht : t ∈ Set.Ioo 0 T`.
* `hflow.2.1 t z` (HasDerivAt universal) becomes
  `hflow_on.2.1 t ht z (Set.mem_univ z)` (HasDerivAt at the specific
  `t ∈ Ioo 0 T`, `z ∈ Set.univ`).
* The conclusion stays at `HasDerivAt` (since `t ∈ Ioo` is an interior
  point of the predicate's quantification set; no `HasDerivWithinAt`
  conversion needed).
* The sub-helpers `vlasov_traj_chain_rule`, `vlasov_compose_flow_*`,
  `vlasov_pushforward_hasDerivAt_under_integral`,
  `vlasov_rhs_pushforward_back` all consume flow hypotheses at a
  *specific `t`*, not universally, so they transport unchanged after
  threading the `ht : t ∈ Ioo 0 T` constraint. -/
theorem vlasovSolutionViaPushforward_isVlasovSolutionOn
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hflow_on : IsCharacteristicFlowOn gradW
                (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
                charX charV (Set.Ioo 0 T) Set.univ)
    -- Boundary regularity (discharged by the boundary-regularity helper at the call site).
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW
          (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) s
          (charX s z, charV s z))
        (Set.Ici s) s)
    -- ρ-regularity on Icc 0 T (the pushforward's spatial marginal).
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (h_int : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    [∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))]
    (_hself : IsCharacteristicFlowSelfConsistent charX f₀
              (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)))
    (h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x)) :
    IsVlasovSolutionOn gradW (vlasovSolutionViaPushforward charX charV f₀) T := by
  -- Unfold IsVlasovSolutionOn; for each test function φ, prove WeakEvolutionEqOn at t ∈ Ioo 0 T.
  intro φ hφ_smooth hφ_compact gradXφ gradVφ hgradXφ hgradVφ t ht
  -- Notation aliases (same as L2735).
  set ρ : ℝ → Measure (PhysSpace d) :=
    fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t) with hρ_def
  have hφ_cont : Continuous φ := hφ_smooth.continuous
  have hφ_aesm_general : ∀ μ : Measure (PhaseSpace d),
      AEStronglyMeasurable φ μ := fun μ => hφ_cont.aestronglyMeasurable
  -- SC.1 (same): unify ∫ φ d(vlasov s) with ∫ (φ ∘ flow_s) df₀.
  have h_compose : ∀ s, ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s) =
      ∫ z, φ (charX s z, charV s z) ∂f₀ := fun s =>
    vlasov_pushforward_integral_eq_compose charX charV f₀ s
      (h_flow_meas s) φ (hφ_aesm_general _)
  -- SC.2 `_at`: pointwise chain rule at every z, AT the specific t ∈ Ioo 0 T.
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
  -- SC.3: DiffUnderIntegralData via SC.5-SC.8 (`_on` for SC.8).
  have h_diff_data : DiffUnderIntegralData gradW ρ charX charV f₀
      φ gradXφ gradVφ t := by
    -- Use `_on` variant of SC.8.
    obtain ⟨nhd, bound, hnhd, h_lipsch, h_bound_int⟩ :=
      vlasov_trajectory_lipschitz_bound_on gradW L hL ρ charX charV f₀
        hf₀_fm φ hφ_smooth hφ_compact hT hflow_on h_init h_cont_Icc h_deriv_Ico
        hgradW_cont hconv_cont t ht M_ρ hM_ρ_nn hM_ρ h_y_int h_int
    refine ⟨nhd, bound, hnhd, ?_, ?_, ?_, h_lipsch, h_bound_int⟩
    · exact vlasov_compose_flow_aestronglymeas charX charV f₀ φ
        hφ_cont h_flow_meas t
    · exact vlasov_compose_flow_integrable_at charX charV f₀ φ
        hφ_cont hφ_compact t (h_flow_meas t)
    · exact vlasov_pointwise_deriv_aestronglymeas gradW ρ charX charV f₀
        φ hφ_smooth gradXφ gradVφ hgradXφ hgradVφ hconv_cont t (h_flow_meas t)
  have h_under_integral :=
    vlasov_pushforward_hasDerivAt_under_integral gradW ρ charX charV f₀
      φ gradXφ gradVφ t h_pointwise h_diff_data
  -- SC.4: push the integrand back through `integral_map`.
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
  have h_push_back :=
    vlasov_rhs_pushforward_back gradW charX charV f₀ t
      (h_flow_meas t) gradXφ gradVφ h_integrand_aesm
  -- Compose: rewrite LHS via h_compose, apply h_under_integral, then rewrite via h_push_back.
  have hLHS : (fun s => ∫ z, φ z ∂(vlasovSolutionViaPushforward charX charV f₀ s)) =
              (fun s => ∫ z, φ (charX s z, charV s z) ∂f₀) := funext h_compose
  rw [hLHS]
  rw [show (∫ z, @inner ℝ (PhysSpace d) _ z.2 (gradXφ z)
              - @inner ℝ (PhysSpace d) _
                  (convolveFunctionMeasure gradW
                    (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) z.1)
                  (gradVφ z)
            ∂(vlasovSolutionViaPushforward charX charV f₀ t)
            + (fun _ => (0 : ℝ)) t)
          = ∫ z, @inner ℝ (PhysSpace d) _ z.2 (gradXφ z)
                  - @inner ℝ (PhysSpace d) _
                      (convolveFunctionMeasure gradW
                        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) z.1)
                      (gradVφ z)
                ∂(vlasovSolutionViaPushforward charX charV f₀ t) from by ring]
  rw [← h_push_back]
  exact h_under_integral

/-- **`_On`-flavored Lagrangian → Eulerian producer for `IsLagrangianVlasovSolutionOn`**.

Same hypothesis package as the global
`vlasovSolutionViaPushforward_isLagrangianVlasovSolution`, but takes the
characteristic flow in `IsCharacteristicFlowOn ... (Set.Ioo 0 T) Set.univ`
form (the flow construction's natural output) and produces the strictly
stronger `IsLagrangianVlasovSolutionOn` predicate.

**Composes**:
* `vlasovSolutionViaPushforward_isVlasovSolutionOn` (above) for the
  weak-PDE conjunct.
* the flow construction's output for the flow-witness conjunct.
* Trivial pushforward + AEMeasurability bundling for the remaining
  conjuncts (identical to the global wrapper's body, adapted to use
  `IsCharacteristicFlowOn`'s initial-condition clause).

This is the **packaging layer**; the substantive PDE proof lives in
`vlasovSolutionViaPushforward_isVlasovSolutionOn` above. -/
theorem vlasovSolutionViaPushforward_isLagrangianVlasovSolutionOn
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (hf₀_fm : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 < T)
    (hflow_on : IsCharacteristicFlowOn gradW
                (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t))
                charX charV (Set.Ioo 0 T) Set.univ)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW
          (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)) s
          (charX s z, charV s z))
        (Set.Ici s) s)
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ∫ y, ‖y‖ ∂(spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) ≤ M_ρ)
    (h_y_int : ∀ s ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    (h_int : ∀ s (x : PhysSpace d),
      Integrable (fun y => gradW (x - y))
        (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)))
    [∀ s, IsProbabilityMeasure
      (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s))]
    (hself : IsCharacteristicFlowSelfConsistent charX f₀
              (fun t => spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ t)))
    (h_flow_meas : ∀ s, AEMeasurable
      (fun z : PhaseSpace d => (charX s z, charV s z)) f₀)
    (hgradW_cont : Continuous gradW)
    (hconv_cont : ∀ s, Continuous (fun x =>
        convolveFunctionMeasure gradW
          (spatialMarginal (vlasovSolutionViaPushforward charX charV f₀ s)) x)) :
    IsLagrangianVlasovSolutionOn gradW
      (vlasovSolutionViaPushforward charX charV f₀) T := by
  refine ⟨vlasovSolutionViaPushforward_isVlasovSolutionOn gradW L hL charX charV f₀
            hf₀_fm hT hflow_on h_init h_cont_Icc h_deriv_Ico M_ρ hM_ρ_nn hM_ρ
            h_y_int h_int hself h_flow_meas hgradW_cont hconv_cont,
          charX, charV, hflow_on, ?_, ?_, h_cont_Icc⟩
  · -- Pushforward equation: f t = (flow_t)_# (f 0) for t ∈ Icc 0 T.
    -- Identical to the global wrapper's body, using IsCharacteristicFlowOn's
    -- initial-condition clause `hflow_on.1 z (Set.mem_univ z)`.
    have h_init : (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id := by
      funext z
      have h := hflow_on.1 z (Set.mem_univ z)
      exact Prod.ext h.1 h.2
    have h0 : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      simp [vlasovSolutionViaPushforward, h_init, Measure.map_id]
    intro t _ht
    rw [h0]
    rfl
  · -- AEMeasurability on Icc 0 T.  Same h0 step as above.
    intro s _hs
    have h_init : (fun z : PhaseSpace d => (charX 0 z, charV 0 z)) = id := by
      funext z
      have h := hflow_on.1 z (Set.mem_univ z)
      exact Prod.ext h.1 h.2
    have h0 : vlasovSolutionViaPushforward charX charV f₀ 0 = f₀ := by
      simp [vlasovSolutionViaPushforward, h_init, Measure.map_id]
    rw [h0]
    exact h_flow_meas s

/-! ## Integration smoke test

A small theorem demonstrating that the three OT files compose: given
two characteristic flows on the same initial probability measures
with finite first moment, the Wasserstein-1 distance between the
pushed-forward measures at time `t` is bounded by the infimum (over
couplings of the *initial* measures) of the pushed-forward edist
cost.

This is **exactly the shape** the USC and derivBound closures in
`LeanPool/Vlasov/Basic.lean` need: it turns a coupling at time 0 into a
W₁-upper-bound at time t.  The Gronwall-on-the-joint-ODE step (which
controls the cost growth) is the next piece — orthogonal to OT,
sits in the dynamics layer.

The theorem is a direct application of `wasserstein1_pushforward_le_iInf`
from `Coupling.lean`; the integration test confirms the type chain
composes correctly when the maps are characteristic flows. -/

theorem wasserstein1_lagrangian_pushforward_bound
    {d : ℕ}
    (charX_f charV_f charX_g charV_g : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ g₀ : Measure (PhaseSpace d))
    (t : ℝ)
    (h_meas_f : Measurable (fun z : PhaseSpace d => (charX_f t z, charV_f t z)))
    (h_meas_g : Measurable (fun z : PhaseSpace d => (charX_g t z, charV_g t z)))
    (h_fmpr_f : IsProbabilityMeasure
                (Measure.map (fun z : PhaseSpace d => (charX_f t z, charV_f t z)) f₀))
    (h_fmpr_g : IsProbabilityMeasure
                (Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) g₀))
    (x₀ : PhaseSpace d)
    (h_fm_f : Integrable (fun y : PhaseSpace d => dist y x₀)
              (Measure.map (fun z : PhaseSpace d => (charX_f t z, charV_f t z)) f₀))
    (h_fm_g : Integrable (fun y : PhaseSpace d => dist y x₀)
              (Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) g₀)) :
    wasserstein1
      (Measure.map (fun z : PhaseSpace d => (charX_f t z, charV_f t z)) f₀)
      (Measure.map (fun z : PhaseSpace d => (charX_g t z, charV_g t z)) g₀) ≤
      ⨅ (π : Measure (PhaseSpace d × PhaseSpace d)) (_ : IsCoupling π f₀ g₀),
        ∫⁻ z, edist (charX_f t z.1, charV_f t z.1)
                    (charX_g t z.2, charV_g t z.2) ∂π :=
  wasserstein1_pushforward_le_iInf
    (fun z => (charX_f t z, charV_f t z))
    (fun z => (charX_g t z, charV_g t z))
    h_meas_f h_meas_g f₀ g₀ x₀ h_fmpr_f h_fmpr_g h_fm_f h_fm_g

/-! ## Banach fixed-point scaffolding for `vlasovWellPosedness` -/
-- The infrastructure here makes the Φ-well-definedness, Gronwall-contraction
-- and Picard-iteration steps compose cleanly:
--   * `VlasovMeasureCurve T M`: admissible curves of probability measures
--     on `PhysSpace d` with uniform first-moment bound `M` on `[0, T]`.
--     The four structural fields are exactly what `Φ` preserves.
--   * `supW1On`: sup-W₁ pseudodistance over a set of times; the natural
--     contraction metric for the Picard iteration.
--   * `vlasovMeasureCurve_convCont`: convolution continuity in `t` derived
--     from the W₁-continuity field via `norm_convolveFunctionMeasure_sub_le`.
--   * `constantCurve`: the constant curve `t ↦ μ₀`, used as the Picard
--     iteration's starting point and as a sanity-check witness that the
--     structure is inhabited.

/-- The sup-W₁ pseudodistance between two curves of measures over a set of
times `S`.  Returns `⨆ t ∈ S, wasserstein1 (ρ t) (σ t)` in `ℝ≥0∞`.

* Symmetric (`supW1On_comm`) and satisfies the triangle inequality
  (`supW1On_triangle`).
* Finite (≠ ⊤) when both curves are `VlasovMeasureCurve`s on `[0, T]` with
  the same moment bound, via `supW1On_ne_top_of_VlasovMeasureCurve`.

Used as the contraction metric for the Picard iteration. -/
noncomputable def supW1On {d : ℕ}
    (S : Set ℝ) (ρ σ : ℝ → Measure (PhysSpace d)) : ℝ≥0∞ :=
  ⨆ (t : ℝ) (_ : t ∈ S), wasserstein1 (ρ t) (σ t)

lemma supW1On_comm {d : ℕ} (S : Set ℝ)
    (ρ σ : ℝ → Measure (PhysSpace d)) :
    supW1On S ρ σ = supW1On S σ ρ := by
  unfold supW1On
  refine iSup_congr fun t => ?_
  refine iSup_congr fun _ => ?_
  exact wasserstein1_comm _ _

lemma supW1On_self {d : ℕ} (S : Set ℝ)
    (ρ : ℝ → Measure (PhysSpace d)) :
    supW1On S ρ ρ = 0 := by
  unfold supW1On
  simp [wasserstein1_self]

lemma supW1On_triangle {d : ℕ} (S : Set ℝ)
    (ρ σ τ : ℝ → Measure (PhysSpace d)) :
    supW1On S ρ τ ≤ supW1On S ρ σ + supW1On S σ τ := by
  unfold supW1On
  refine iSup_le fun t => iSup_le fun ht => ?_
  calc wasserstein1 (ρ t) (τ t)
      ≤ wasserstein1 (ρ t) (σ t) + wasserstein1 (σ t) (τ t) :=
        wasserstein1_triangle _ _ _
    _ ≤ (⨆ s ∈ S, wasserstein1 (ρ s) (σ s))
        + (⨆ s ∈ S, wasserstein1 (σ s) (τ s)) := by
        gcongr
        · exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)
        · exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)

/-- **Iterated triangle inequality for `supW1On` over a sequence**.

For any sequence `x : ℕ → ℝ → Measure (PhysSpace d)` and `m ≤ n`:
`supW1On S (x m) (x n) ≤ ∑ k ∈ Ico m n, supW1On S (x k) (x (k+1))`.

**Generic structural lemma** — stated over an arbitrary sequence and time
set `S`, not specialised to Picard iteration.  Downstream consumers (the
Cauchy-from-contraction argument, the forward-iteration continuation, window
uniqueness) compose against this generic form.

The entire proof stays in ENNReal — `supW1On` is ENNReal-valued, the sum is
in ENNReal, ENNReal addition is well-defined with `⊤` as absorbing element,
so no finiteness side conditions arise.  Project to ℝ via `.toReal` only at
the boundary (or not at all, as in the ENNReal-form Cauchy argument).

Proof: induction on `n` starting from `n = m` via `Nat.le_induction`.
Base case is the empty sum via `supW1On_self`.  Inductive step combines
`supW1On_triangle` with `Finset.sum_Ico_succ_top`. -/
lemma supW1On_iterated_triangle {d : ℕ} (S : Set ℝ)
    (x : ℕ → ℝ → Measure (PhysSpace d))
    (m n : ℕ) (hmn : m ≤ n) :
    supW1On S (x m) (x n) ≤
      ∑ k ∈ Finset.Ico m n, supW1On S (x k) (x (k+1)) := by
  induction n, hmn using Nat.le_induction with
  | base =>
    -- Empty sum: Ico m m = ∅.
    rw [Finset.Ico_self, Finset.sum_empty]
    rw [supW1On_self]
  | succ n hmn ih =>
    calc supW1On S (x m) (x (n+1))
        ≤ supW1On S (x m) (x n) + supW1On S (x n) (x (n+1)) :=
          supW1On_triangle S (x m) (x n) (x (n+1))
      _ ≤ (∑ k ∈ Finset.Ico m n, supW1On S (x k) (x (k+1))) +
          supW1On S (x n) (x (n+1)) := by
          exact add_le_add ih (le_refl _)
      _ = ∑ k ∈ Finset.Ico m (n+1), supW1On S (x k) (x (k+1)) := by
          rw [Finset.sum_Ico_succ_top hmn]

/-! ## Metric-dependent smallness predicates -/
--
-- The existence-and-contraction analysis uses TWO independent smallness
-- constraints, captured as two separate predicates:
--   * `LocalSmallnessPLBuffer L T := L · T² < 1` — per-ball
--     Picard-Lindelöf flow ball-geometry (the L-Lipschitz R-existence
--     fixed-point).
--   * `LocalSmallnessContraction L T := L · (exp((max 1 L)·T) - 1) / (max 1 L) < 1`
--     — supW1On contraction-ratio (Gronwall on the W₁-based flow).
--
-- These are kept as two predicates because they are genuinely independent
-- mathematical constraints from distinct sub-arguments: the ball-geometry
-- shape does NOT imply the exponential contraction constraint, and is not
-- implied by it.  Carrying them separately keeps each predicate matched to
-- its own sub-argument rather than fusing two distinct claims.
--
-- The truncated-distance Wasserstein `Wbar = W_{min(|x-y|,1)}` (Dobrushin 1979,
-- §5) is an alternative metric that replaces the `LocalSmallnessContraction`
-- exponential with a linear-in-T form.

/-- **Smallness predicate for the per-ball Picard-Lindelöf flow's
ball-geometry constraint.**

Defined as `(L : ℝ) * T ^ 2 < 1`, this is the smallness condition
the per-ball flow's R-selection requires: `R · (1 - L·T²) ≥ N(z)`
forces R > 0 only when `L·T² < 1`.  It comes from the tight
adaptive-window Picard-Lindelöf geometry + L-Lipschitz fixed-point
analysis, NOT from contraction.

This is kept separate from the supW1On *contraction-ratio* constraint
`LocalSmallnessContraction` (below): the two are genuinely independent
mathematical constraints from distinct sub-arguments, so each predicate
stays matched to its own sub-argument. -/
def LocalSmallnessPLBuffer (L : NNReal) (T : ℝ) : Prop :=
  (L : ℝ) * T ^ 2 < 1

/-- **Smallness predicate for the supW1On contraction-ratio constraint.**

For `Phi_supW1_contraction`'s output to satisfy `q < 1` — the genuine
M-independent contraction ratio — the constraint is
`L · (exp((max 1 L)·T) - 1) / (max 1 L) < 1`.  This comes from Gronwall
on the W₁-based contraction analysis, inherited off
`vlasovVectorField_lipschitzWith` (the joint phase-space
`max(1, L)`-Lipschitz constant).

When `max(1, L) = 1` the constraint simplifies to `L · (exp T - 1) < 1`. -/
def LocalSmallnessContraction (L : NNReal) (T : ℝ) : Prop :=
  (L : ℝ) * (Real.exp ((max 1 (L : ℝ)) * T) - 1) / (max 1 (L : ℝ)) < 1

/-- The curve metric used by the `VlasovMeasureCurve` Banach iteration:
`supW1On` (sup of `W₁` distances over the time window).

Defined as `abbrev` so the abbreviation unfolds transparently — proofs that
reference `supW1On` work against `CurveMetric` without modification.  New
consumers can use `CurveMetric` directly for explicit metric-agnosticism. -/
noncomputable abbrev CurveMetric {d : ℕ}
    (S : Set ℝ) (ρ σ : ℝ → Measure (PhysSpace d)) : ℝ≥0∞ :=
  supW1On S ρ σ

/-- Admissible Vlasov measure curves on `[0, T]`: a curve of probability
measures on `PhysSpace d` with uniform first-moment bound `M`, pointwise
integrability of `‖·‖`, and W₁-continuity at every time in `[0, T]`.

The W₁-continuity field is phrased per-base-point `s ∈ [0, T]` as
`ContinuousWithinAt` of `t ↦ W₁(ρ s, ρ t).toReal` at `s` (which equals 0 at
`t = s`).  This is strictly stronger than naive ContinuousOn on the diagonal
— it gives the dominator we need for derived convolution continuity
(`vlasovMeasureCurve_convCont`) and for the Picard limit's bundling.

`d` is an explicit parameter so that `VlasovMeasureCurve d T M` is fully
determined at use sites (otherwise `NeZero d` cannot be resolved from the
non-discriminating real-valued T, M alone). -/
structure VlasovMeasureCurve (d : ℕ) [NeZero d] (T : ℝ) (M : ℝ → ℝ) where
  /-- The underlying curve of spatial measures, `t ↦ ρ t`. -/
  ρ : ℝ → Measure (PhysSpace d)
  isProb : ∀ t, IsProbabilityMeasure (ρ t)
  hasMoment : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ t) ≤ M t
  yIntegrable : ∀ t ∈ Set.Icc (0 : ℝ) T, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t)
  hW1Cont : ∀ s ∈ Set.Icc (0 : ℝ) T,
    ContinuousWithinAt (fun t => (wasserstein1 (ρ s) (ρ t)).toReal)
                       (Set.Icc 0 T) s

/-- `supW1On` of two `VlasovMeasureCurve`s on `[0, T]` with moment bound `M`
is bounded by `2M`, hence finite.

Combines pointwise `wasserstein1_le_moments_sum` with `iSup_le` over the
compact time set. -/
lemma supW1On_le_two_moment_of_VlasovMeasureCurve {d : ℕ} [NeZero d]
    {T : ℝ} {M : ℝ → ℝ} (Mbar : ℝ) (hMbar : ∀ t ∈ Set.Icc 0 T, M t ≤ Mbar)
    (ρ σ : VlasovMeasureCurve d T M) :
    supW1On (Set.Icc 0 T) ρ.ρ σ.ρ ≤ ENNReal.ofReal (2 * Mbar) := by
  unfold supW1On
  refine iSup_le fun t => iSup_le fun ht => ?_
  -- Pointwise: W₁(ρ_t, σ_t) ≤ ofReal(∫‖y‖d(ρ_t) + ∫‖y‖d(σ_t)) ≤ ofReal(M + M)
  have h_bound : wasserstein1 (ρ.ρ t) (σ.ρ t) ≤
      ENNReal.ofReal (∫ y, ‖y‖ ∂(ρ.ρ t) + ∫ y, ‖y‖ ∂(σ.ρ t)) := by
    have : IsProbabilityMeasure (ρ.ρ t) := ρ.isProb t
    have : IsProbabilityMeasure (σ.ρ t) := σ.isProb t
    exact wasserstein1_le_moments_sum (ρ.ρ t) (σ.ρ t)
      (ρ.yIntegrable t ht) (σ.yIntegrable t ht)
  refine h_bound.trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hρ_t : ∫ y, ‖y‖ ∂(ρ.ρ t) ≤ M t := ρ.hasMoment t ht
  have hσ_t : ∫ y, ‖y‖ ∂(σ.ρ t) ≤ M t := σ.hasMoment t ht
  linarith [hMbar t ht]

/-- `supW1On` of two `VlasovMeasureCurve`s is finite (≠ ⊤). -/
lemma supW1On_ne_top_of_VlasovMeasureCurve {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (Mbar : ℝ) (hMbar : ∀ t ∈ Set.Icc 0 T, M t ≤ Mbar)
    (ρ σ : VlasovMeasureCurve d T M) :
    supW1On (Set.Icc 0 T) ρ.ρ σ.ρ ≠ ⊤ :=
  ne_of_lt ((supW1On_le_two_moment_of_VlasovMeasureCurve Mbar hMbar ρ σ).trans_lt
            ENNReal.ofReal_lt_top)

/-- Convolution continuity in time, derived from the structural
`hW1Cont` field via `norm_convolveFunctionMeasure_sub_le`.

For each `x ∈ PhysSpace d`, the map `t ↦ (∇W ∗ ρ_t)(x)` is continuous on
`[0, T]`.  Used inside `Φ`'s well-definedness proof to discharge the
convolution-continuity hypothesis of `exists_vlasov_characteristicFlow`. -/
lemma vlasovMeasureCurve_convCont {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    {T : ℝ} {M : ℝ → ℝ} (ρ : VlasovMeasureCurve d T M)
    (x : PhysSpace d)
    (h_int : ∀ t ∈ Set.Icc (0 : ℝ) T,
              Integrable (fun y => gradW (x - y)) (ρ.ρ t)) :
    ContinuousOn (fun t => convolveFunctionMeasure gradW (ρ.ρ t) x)
                 (Set.Icc 0 T) := by
  -- Strategy: at every base `s ∈ [0, T]`, the Lipschitz convolution estimate
  --   ‖conv(ρ_s, x) - conv(ρ_t, x)‖ ≤ L · W₁(ρ_s, ρ_t).toReal
  -- composes with the hW1Cont field (W₁(ρ_s, ρ_t).toReal → 0 as t → s within
  -- [0, T]) to give ContinuousWithinAt at s.
  intro s hs
  have hPs : IsProbabilityMeasure (ρ.ρ s) := ρ.isProb s
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have hCont := ρ.hW1Cont s hs
  rw [Metric.continuousWithinAt_iff] at hCont
  have h_self : (wasserstein1 (ρ.ρ s) (ρ.ρ s)).toReal = 0 := by
    rw [wasserstein1_self]; rfl
  -- Pick δ from hCont for tolerance ε / (L + 1)  (so that L · δ < ε)
  set η : ℝ := ε / ((L : ℝ) + 1) with hη_def
  have hLp1_pos : (0 : ℝ) < (L : ℝ) + 1 := by
    have : (0 : ℝ) ≤ L := L.coe_nonneg
    linarith
  have hη_pos : 0 < η := div_pos hε hLp1_pos
  obtain ⟨δ, hδ_pos, hδ_bound⟩ := hCont η hη_pos
  refine ⟨δ, hδ_pos, fun t ht hdist => ?_⟩
  have hδb := hδ_bound ht hdist
  rw [h_self, Real.dist_eq, sub_zero] at hδb
  have hW1_nn : 0 ≤ (wasserstein1 (ρ.ρ s) (ρ.ρ t)).toReal := ENNReal.toReal_nonneg
  have hW1_lt : (wasserstein1 (ρ.ρ s) (ρ.ρ t)).toReal < η := by
    rwa [abs_of_nonneg hW1_nn] at hδb
  have hPt : IsProbabilityMeasure (ρ.ρ t) := ρ.isProb t
  have h_finite : wasserstein1 (ρ.ρ s) (ρ.ρ t) ≠ ⊤ :=
    wasserstein1_ne_top_of_finite_moment _ _
      (ρ.yIntegrable s hs) (ρ.yIntegrable t ht)
  have h_lip := norm_convolveFunctionMeasure_sub_le gradW L hL
    (ρ.ρ s) (ρ.ρ t) x h_finite (h_int s hs) (h_int t ht)
  -- h_lip : ‖conv(ρ_s, x) - conv(ρ_t, x)‖ ≤ L · W₁(ρ_s, ρ_t).toReal
  rw [dist_eq_norm]
  calc ‖convolveFunctionMeasure gradW (ρ.ρ t) x
        - convolveFunctionMeasure gradW (ρ.ρ s) x‖
      = ‖convolveFunctionMeasure gradW (ρ.ρ s) x
          - convolveFunctionMeasure gradW (ρ.ρ t) x‖ := norm_sub_rev _ _
    _ ≤ (L : ℝ) * (wasserstein1 (ρ.ρ s) (ρ.ρ t)).toReal := h_lip
    _ ≤ (L : ℝ) * η := by
        apply mul_le_mul_of_nonneg_left (le_of_lt hW1_lt) L.coe_nonneg
    _ < ((L : ℝ) + 1) * η := by nlinarith
    _ = ε := by
        rw [hη_def]
        field_simp

/-! ### Constant extension past `[0, T]`

A `VlasovMeasureCurve d T M` has its structural properties (moment bound,
integrability of `‖·‖`, W₁-continuity) only on `Icc 0 T`.
`exists_vlasov_characteristicFlow_global_smallT` takes universal-in-`t`
hypotheses (the proof internally accesses `ρ` at `t ∈ Icc 0 (T + 1)` —
see `exists_vlasov_trajectory`'s `hbound_local` — but the exposed
signature is universal).

The constant-extension wrapper `VlasovMeasureCurve.extend` produces a
curve on all of `ℝ` by clamping `t` to `Icc 0 T`: `extend t := ρ.ρ (clamp t)`
where `clamp t := max 0 (min t T)`.  Outside `Icc 0 T` the extended
curve takes the boundary value (`ρ.ρ 0` for `t < 0`; `ρ.ρ T` for
`t > T`).  This is the canonical mathematical extension — a Vlasov
solution defined on a finite horizon is naturally extended by holding
the endpoint value past the horizon — and it makes the structural
properties hold universally without modifying the flow construction itself.

Discharge of `hρ_cont` (universal convolveFunctionMeasure continuity)
routes through `vlasovMeasureCurve_convCont` precomposed with the
continuous clamp via `ContinuousOn.comp_continuous`. -/

/-- Clamp `t : ℝ` to `Icc 0 T`.  Used by `VlasovMeasureCurve.extend` to
extend a curve from `Icc 0 T` to all of `ℝ`. -/
def clampToIcc (T t : ℝ) : ℝ := max 0 (min t T)

lemma clampToIcc_mem {T : ℝ} (hT : 0 ≤ T) (t : ℝ) :
    clampToIcc T t ∈ Set.Icc (0 : ℝ) T := by
  unfold clampToIcc
  refine Set.mem_Icc.mpr ⟨le_max_left _ _, max_le hT (min_le_right _ _)⟩

lemma clampToIcc_continuous (T : ℝ) : Continuous (clampToIcc T) := by
  unfold clampToIcc
  exact continuous_const.max (continuous_id.min continuous_const)

/-- Constant extension of a `VlasovMeasureCurve d T M`'s underlying curve
`ρ.ρ` from `Icc 0 T` to all of `ℝ`.  Defined as `ρ.ρ` composed with the
clamp `max 0 (min t T)`.

For `t ∈ Icc 0 T`: `extend t = ρ.ρ t`.
For `t < 0`: `extend t = ρ.ρ 0`.
For `t > T`: `extend t = ρ.ρ T`.

The extension preserves all structural properties (`IsProbabilityMeasure`,
moment bound, integrability of `‖·‖`) universally in `t`, and extends
W₁-continuity to convolveFunctionMeasure-continuity universally in `t`
via `clampToIcc_continuous` + `vlasovMeasureCurve_convCont`. -/
noncomputable def VlasovMeasureCurve.extend {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (ρ : VlasovMeasureCurve d T M) : ℝ → Measure (PhysSpace d) :=
  fun t => ρ.ρ (clampToIcc T t)

/-- The extended curve is a probability measure at every `t : ℝ`. -/
instance VlasovMeasureCurve.extend_isProb {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (ρ : VlasovMeasureCurve d T M) (t : ℝ) :
    IsProbabilityMeasure (ρ.extend t) :=
  ρ.isProb _

/-- The extended curve has `‖·‖` integrable at every `t : ℝ`. -/
lemma VlasovMeasureCurve.extend_yIntegrable {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (hT : 0 ≤ T) (ρ : VlasovMeasureCurve d T M) (t : ℝ) :
    Integrable (fun y : PhysSpace d => ‖y‖) (ρ.extend t) :=
  ρ.yIntegrable _ (clampToIcc_mem hT t)

/-- The extended curve preserves the moment bound `M` universally in `t`. -/
lemma VlasovMeasureCurve.extend_hasMoment {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (hT : 0 ≤ T) (ρ : VlasovMeasureCurve d T M) (t : ℝ) :
    ∫ y, ‖y‖ ∂(ρ.extend t) ≤ M (clampToIcc T t) :=
  ρ.hasMoment _ (clampToIcc_mem hT t)

/-- Convolution continuity on the extended curve, universal in `t`.

Composed from `vlasovMeasureCurve_convCont` (ContinuousOn on `Icc 0 T`)
with `clampToIcc_continuous` via `ContinuousOn.comp_continuous`.  This
provides the flow construction's universal `hρ_cont` hypothesis directly
from a `VlasovMeasureCurve`'s structural fields. -/
lemma VlasovMeasureCurve.extend_convCont {d : ℕ} [NeZero d]
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    {T : ℝ} {M : ℝ → ℝ} (hT : 0 ≤ T) (ρ : VlasovMeasureCurve d T M)
    (x : PhysSpace d)
    (h_int : ∀ t ∈ Set.Icc (0 : ℝ) T,
              Integrable (fun y => gradW (x - y)) (ρ.ρ t)) :
    Continuous (fun t => convolveFunctionMeasure gradW (ρ.extend t) x) := by
  -- The function decomposes as `(fun s => convolveFunctionMeasure gradW (ρ.ρ s) x) ∘ clamp`.
  -- Inner is ContinuousOn (Icc 0 T) via vlasovMeasureCurve_convCont.
  -- Clamp is continuous and lands in Icc 0 T.
  have h_convCont := vlasovMeasureCurve_convCont gradW L hL ρ x h_int
  exact h_convCont.comp_continuous (clampToIcc_continuous T) (clampToIcc_mem hT)

/-- The constant curve at a probability measure with finite first moment is
a valid `VlasovMeasureCurve` on `[0, T]` for any `T` and any moment
bound `M ≥ ∫‖y‖dμ₀`. -/
def constantCurve {d : ℕ} [NeZero d] {T : ℝ} {M : ℝ → ℝ}
    (μ₀ : Measure (PhysSpace d)) [IsProbabilityMeasure μ₀]
    (hμ_int : Integrable (fun y : PhysSpace d => ‖y‖) μ₀)
    (hM : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂μ₀ ≤ M t) :
    VlasovMeasureCurve d T M where
  ρ := fun _ => μ₀
  isProb := fun _ => inferInstance
  hasMoment := hM
  yIntegrable := fun _ _ => hμ_int
  hW1Cont := fun s _ => by
    -- The function `t ↦ (wasserstein1 μ₀ μ₀).toReal` is identically 0;
    -- ContinuousWithinAt of a constant is immediate.
    have h_zero : (fun t : ℝ => (wasserstein1 μ₀ μ₀).toReal)
                  = fun _ => (0 : ℝ) := by
      funext _; rw [wasserstein1_self]; rfl
    rw [h_zero]
    exact continuousWithinAt_const

/-- **Per-z trajectory existence for small T.**

For each `z : PhaseSpace d`, produces a trajectory `γ : ℝ → PhaseSpace d` with
`γ 0 = z` satisfying the Vlasov ODE on `Ioo 0 T`.

**Smallness constraint**: `L · T² < 1`.  Comes from `exists_vlasov_characteristicFlow`'s
`hR` inequality, whose `M·T²` term has quadratic-in-T growth.  Solving
the algebraic constraint per-z yields a finite `R(z)` and `M(z)`, with the
existence-bound on `T` driven by `L·T² < 1`.

The forward-iteration continuation extends to arbitrary T via shifted
initial data; the small-T regime here is where the contraction operates. -/
theorem exists_vlasov_trajectory
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (h_y_int : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ)
    (T : ℝ) (hT : 0 ≤ T)
    (hTL_PL : LocalSmallnessPLBuffer L T)
    (z : PhaseSpace d) :
    ∃ γ : ℝ → PhaseSpace d,
      γ 0 = z ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun s => (γ s).1) (γ t).2 t ∧
        HasDerivAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1)) t) ∧
      -- **Boundary regularity**: HasDerivWithinAt on `Icc 0 T` for every
      -- t ∈ Icc 0 T, derived from the per-ball flow's boundary conjunct.
      -- Closes the t = 0 (and t = T) boundary case for consumers like
      -- `flow_distance_growth_bound_on`.
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => (γ s).1) (γ t).2 (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1)) (Set.Icc 0 T) t) := by
  -- ============================================================
  -- Compute R(z), M(z) from the algebraic constraint:
  --   R ≥ 2 + (‖z.2‖ + 1/2)·T + M·T²
  --   M ≤ ‖gradW(0)‖ + L·(R + ‖z.1‖ + M_ρ)         (from L-Lipschitz)
  -- Substituting: R·(1 - L·T²) ≥ N(z)
  --   where N(z) := 2 + (‖z.2‖ + 1/2)·T
  --                + (‖gradW(0)‖ + L·‖z.1‖ + L·M_ρ)·T²
  -- Use R := N(z) / (1 - L·T²)  (positive since `hTL_PL`).
  -- ============================================================
  -- **`LocalSmallnessPLBuffer` unfold site.**  This body consumes the
  -- PL-buffer constraint `L · T² < 1` directly for R-existence — the
  -- linarith on the next line derives `hTL_pos := 1 - L·T² > 0` from
  -- `hTL_PL`'s algebraic form, and the subsequent `R := N(z) / (1 - L·T²)`
  -- selection depends on the quadratic shape.  This is a SINGLE-PURPOSE use
  -- of the PL-buffer predicate: no contraction-flavored step in this body
  -- discharges off the same hypothesis.  The `LocalSmallnessContraction`
  -- predicate is governed separately at `_picard_fixedPointFlow`'s `hq_lt`
  -- close, NOT here.
  have hTL : (L : ℝ) * T ^ 2 < 1 := hTL_PL
  set hTL_pos : (0 : ℝ) < 1 - (L : ℝ) * T ^ 2 := by linarith with hTL_pos_def
  -- N(z) is the right-hand-side numerator; non-negative.
  set N_z : ℝ := 2 + (‖z.2‖ + 1 / 2) * T
                 + (‖gradW 0‖ + (L : ℝ) * ‖z.1‖ + (L : ℝ) * M_ρ) * T ^ 2
    with hN_z_def
  have hN_z_nn : 0 ≤ N_z := by
    have h1 : 0 ≤ ‖z.2‖ + 1 / 2 := by positivity
    have h2 : 0 ≤ ‖gradW 0‖ + (L : ℝ) * ‖z.1‖ + (L : ℝ) * M_ρ := by
      have hgW : 0 ≤ ‖gradW 0‖ := norm_nonneg _
      have hLz1 : 0 ≤ (L : ℝ) * ‖z.1‖ := mul_nonneg L.coe_nonneg (norm_nonneg _)
      have hLMρ : 0 ≤ (L : ℝ) * M_ρ := mul_nonneg L.coe_nonneg hM_ρ_nn
      linarith
    have hT1nn : 0 ≤ T + 1 := by linarith
    have hT1sq : 0 ≤ T ^ 2 := sq_nonneg _
    have := mul_nonneg h1 hT1nn
    have := mul_nonneg h2 hT1sq
    rw [hN_z_def]; positivity
  -- R_real := N(z) / (1 - L·T²)
  set R_real : ℝ := N_z / (1 - (L : ℝ) * T ^ 2) with hR_real_def
  have hR_real_nn : 0 ≤ R_real := div_nonneg hN_z_nn (le_of_lt hTL_pos)
  set R : NNReal := Real.toNNReal R_real with hR_def
  have hR_eq : (R : ℝ) = R_real := Real.coe_toNNReal _ hR_real_nn
  -- M_real := ‖gradW(0)‖ + L · (R + ‖z.1‖ + M_ρ)
  set M_real : ℝ :=
    ‖gradW 0‖ + (L : ℝ) * ((R : ℝ) + ‖z.1‖ + M_ρ) with hM_real_def
  have hM_real_nn : 0 ≤ M_real := by
    have : 0 ≤ (L : ℝ) * ((R : ℝ) + ‖z.1‖ + M_ρ) := by
      apply mul_nonneg L.coe_nonneg
      have hR_nn : 0 ≤ (R : ℝ) := NNReal.coe_nonneg R
      have : 0 ≤ ‖z.1‖ := norm_nonneg _
      linarith
    linarith [norm_nonneg (gradW 0)]
  set M : NNReal := Real.toNNReal M_real with hM_def
  have hM_eq : (M : ℝ) = M_real := Real.coe_toNNReal _ hM_real_nn
  -- ============================================================
  -- Verify hR_local: 2·a + (‖z.2‖ + a/2)·T + M·T² ≤ R
  -- with a = 1.
  -- After substitution: this is N_z ≤ R = R_real * (1 - L·T²) + correction.
  -- The construction gives R · (1 - L·T²) = N_z, so the inequality is tight.
  -- ============================================================
  have ha : (0 : NNReal) < 1 := by norm_num
  have hR_local : 2 * ((1 : NNReal) : ℝ)
                  + (‖z.2‖ + ((1 : NNReal) : ℝ) / 2) * T
                  + (M : ℝ) * T ^ 2 ≤ R := by
    -- Prove the equivalent inequality in real form, then transport via hM_eq, hR_eq.
    have hne : 1 - (L : ℝ) * T ^ 2 ≠ 0 := ne_of_gt hTL_pos
    have h_R_rel : R_real * (1 - (L : ℝ) * T ^ 2) = N_z := by
      simp only [hR_real_def]
      field_simp
    have h_LHS_eq : (2 : ℝ) + (‖z.2‖ + 1 / 2) * T + M_real * T ^ 2
                  = N_z + (L : ℝ) * R_real * T ^ 2 := by
      -- M_real contains (R : ℝ); substitute via hR_eq before ring.
      simp only [hM_real_def, hN_z_def, hR_eq]; ring
    have h_target_eq : N_z + (L : ℝ) * R_real * T ^ 2 = R_real := by
      nlinarith [h_R_rel]
    have h_real : (2 : ℝ) + (‖z.2‖ + 1 / 2) * T + M_real * T ^ 2 ≤ R_real := by
      linarith [h_LHS_eq, h_target_eq]
    -- Cast to NNReal form: ((1 : NNReal) : ℝ) = 1 and 2 * 1 = 2.
    have h_one : ((1 : NNReal) : ℝ) = 1 := by norm_cast
    rw [hM_eq, hR_eq, h_one]
    linarith [h_real]
  -- ============================================================
  -- Verify hbound_local: force bound on closedBall z.1 R for t ∈ Icc 0 T.
  -- Uses ‖conv(ρ t, x)‖ ≤ ‖gradW(0)‖ + L · ∫‖x-y‖ dρ_t ≤ ‖gradW(0)‖ + L·(‖x‖ + M_ρ).
  -- For x ∈ closedBall z.1 R: ‖x‖ ≤ R + ‖z.1‖, so bound ≤ M_real = M.
  -- ============================================================
  have hbound_local : ∀ t ∈ Set.Icc (0 : ℝ) T,
                     ∀ x ∈ Metric.closedBall z.1 (R : ℝ),
                     ‖convolveFunctionMeasure gradW (ρ t) x‖ ≤ M := by
    intro t _ht x hx
    have hx_norm : ‖x‖ ≤ (R : ℝ) + ‖z.1‖ := by
      have hdx : dist x z.1 ≤ (R : ℝ) := hx
      have hxz : ‖x - z.1‖ ≤ (R : ℝ) := by rwa [dist_eq_norm] at hdx
      have h_tri := norm_add_le (x - z.1) z.1
      rw [sub_add_cancel] at h_tri
      linarith
    -- ‖∫ gradW(x - y) dρ_t(y)‖ ≤ ∫ ‖gradW(x - y)‖ dρ_t(y).
    have h_sub_int : Integrable (fun y => ‖x - y‖) (ρ t) := by
      have habs_meas : AEStronglyMeasurable (fun y : PhysSpace d => ‖x - y‖) (ρ t) :=
        ((aestronglyMeasurable_const (b := x)).sub aestronglyMeasurable_id).norm
      refine Integrable.mono' ((integrable_const ‖x‖).add (h_y_int t)) habs_meas ?_
      refine Filter.Eventually.of_forall fun y => ?_
      simp only [Real.norm_of_nonneg (norm_nonneg _)]
      exact norm_sub_le x y
    have h_bnd_int : Integrable (fun y => ‖gradW 0‖ + (L : ℝ) * ‖x - y‖) (ρ t) :=
      (integrable_const _).add (h_sub_int.const_mul _)
    have h_pt : ∀ y : PhysSpace d,
        ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + (L : ℝ) * ‖x - y‖ := by
      intro y
      have hd := hL.dist_le_mul (x - y) 0
      simp only [dist_eq_norm, sub_zero] at hd
      have h_tri : ‖gradW (x - y)‖ ≤ ‖gradW 0‖ + ‖gradW (x - y) - gradW 0‖ := by
        have := norm_add_le (gradW (x - y) - gradW 0) (gradW 0)
        simp only [sub_add_cancel] at this
        linarith
      linarith
    rw [hM_eq, hM_real_def]
    calc ‖convolveFunctionMeasure gradW (ρ t) x‖
        = ‖∫ y, gradW (x - y) ∂(ρ t)‖ := rfl
      _ ≤ ∫ y, ‖gradW (x - y)‖ ∂(ρ t) := norm_integral_le_integral_norm _
      _ ≤ ∫ y, (‖gradW 0‖ + (L : ℝ) * ‖x - y‖) ∂(ρ t) :=
          integral_mono (h_int t x).norm h_bnd_int h_pt
      _ = ‖gradW 0‖ + (L : ℝ) * ∫ y, ‖x - y‖ ∂(ρ t) := by
          rw [integral_add (integrable_const _) (h_sub_int.const_mul _)]
          simp [integral_const, measureReal_def, measure_univ, integral_const_mul]
      _ ≤ ‖gradW 0‖ + (L : ℝ) * (‖x‖ + M_ρ) := by
          have hint_bd : ∫ y, ‖x - y‖ ∂(ρ t) ≤ ‖x‖ + M_ρ := by
            calc ∫ y, ‖x - y‖ ∂(ρ t)
                ≤ ∫ y, (‖x‖ + ‖y‖) ∂(ρ t) :=
                  integral_mono h_sub_int
                    ((integrable_const _).add (h_y_int t))
                    (fun y => norm_sub_le x y)
              _ = ‖x‖ + ∫ y, ‖y‖ ∂(ρ t) := by
                  rw [integral_add (integrable_const _) (h_y_int t)]
                  simp [integral_const, measureReal_def, measure_univ]
              _ ≤ ‖x‖ + M_ρ := by linarith [hM_ρ t]
          have := mul_le_mul_of_nonneg_left hint_bd L.coe_nonneg
          linarith
      _ ≤ ‖gradW 0‖ + (L : ℝ) * ((R : ℝ) + ‖z.1‖ + M_ρ) := by
          have hL_nn : 0 ≤ (L : ℝ) := L.coe_nonneg
          have hMρ_nn : 0 ≤ M_ρ := hM_ρ_nn
          have h_bound : ‖x‖ + M_ρ ≤ (R : ℝ) + ‖z.1‖ + M_ρ := by linarith
          have := mul_le_mul_of_nonneg_left h_bound hL_nn
          linarith
  -- ============================================================
  -- Apply exists_vlasov_characteristicFlow with z₀ = z, a = 1.
  -- ============================================================
  obtain ⟨charX, charV, hflow, h_boundary⟩ :=
    exists_vlasov_characteristicFlow_tight W gradW hgradW L hL
      ρ h_int hρ_cont z 1 ha M T hT R hR_local hbound_local
  -- Extract trajectory at w = z (z is the center of the ball, trivially in it).
  have hz_in : z ∈ Metric.closedBall z (((1 : NNReal) : ℝ) / 2) := by
    rw [Metric.mem_closedBall, dist_self]
    have : ((1 : NNReal) : ℝ) / 2 = (1 : ℝ) / 2 := by push_cast; ring
    linarith
  obtain ⟨hinit, hode_x, hode_v⟩ := hflow
  refine ⟨fun t => (charX t z, charV t z), ?_, ?_, ?_⟩
  · -- γ 0 = z
    have h0 := hinit z hz_in
    exact Prod.ext h0.1 h0.2
  · -- ODE on Ioo 0 T.
    intro t ht
    exact ⟨hode_x t ht z hz_in, hode_v t ht z hz_in⟩
  · -- Boundary regularity on Icc 0 T: lifted from the per-ball flow's
    -- enriched conjunct h_boundary.
    intro t ht
    exact h_boundary z hz_in t ht

/-- **True global-in-z characteristic flow on a small-T interval.**

For `L · T² < 1`, produces a characteristic flow `(charX, charV)` defined
for *every* `z : PhaseSpace d` (not just z in a ball), satisfying the Vlasov
ODE on `Ioo 0 T`.

This is the foundation the Φ pushforward construction depends on; the
forward-iteration continuation extends to arbitrary T via shifted-initial-data
iteration.

**Architecture**: per-z application of `exists_vlasov_characteristicFlow`
with `z₀ = z, a = 1` (via `exists_vlasov_trajectory` helper), bundled
into a global flow via `Classical.choose`.  See helper's docstring for the
algebraic R(z), M(z) computation.

**Measurability**: NOT exposed.  The per-z Classical.choose bundling
doesn't propagate continuity-in-z.  A measurable variant
(`exists_vlasov_characteristicFlow_global_on_ball_measurable`) covers
the analogous question for the ball-localized flow; a parallel
`_global_smallT_measurable` companion can be added when needed. -/
theorem exists_vlasov_characteristicFlow_global_smallT
    {d : ℕ}
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ t) x))
    (h_y_int : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ t))
    (M_ρ : ℝ) (hM_ρ_nn : 0 ≤ M_ρ)
    (hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ t) ≤ M_ρ)
    (T : ℝ) (hT : 0 ≤ T)
    (hTL_PL : LocalSmallnessPLBuffer L T) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ charX charV (Set.Ioo 0 T) Set.univ ∧
      -- **Boundary regularity bundle**: expose the HasDerivWithinAt on
      -- `Icc 0 T` for every z and t ∈ Icc 0 T.  Lifted from the per-z
      -- trajectory's boundary-regularity conjunct.
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (ρ t) (charX t z)))
          (Set.Icc 0 T) t) := by
  classical
  -- Per-z trajectory existence (with boundary regularity).
  have h_perZ : ∀ z : PhaseSpace d, ∃ γ : ℝ → PhaseSpace d,
      γ 0 = z ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) T,
        HasDerivAt (fun s => (γ s).1) (γ t).2 t ∧
        HasDerivAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1)) t) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => (γ s).1) (γ t).2 (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => (γ s).2)
          (-(convolveFunctionMeasure gradW (ρ t) (γ t).1)) (Set.Icc 0 T) t) := by
    intro z
    exact exists_vlasov_trajectory W gradW hgradW L hL ρ h_int hρ_cont
      h_y_int M_ρ hM_ρ_nn hM_ρ T hT hTL_PL z
  -- Bundle via Classical.choose.
  let γ_func : PhaseSpace d → ℝ → PhaseSpace d := fun z =>
    Classical.choose (h_perZ z)
  refine ⟨fun t z => (γ_func z t).1, fun t z => (γ_func z t).2,
         ⟨?_, ?_, ?_⟩, ?_⟩
  · -- (i) Initial condition: γ_func z 0 = z for all z (Set.univ).
    intro z _
    have h_init : γ_func z 0 = z := (Classical.choose_spec (h_perZ z)).1
    exact ⟨congrArg Prod.fst h_init, congrArg Prod.snd h_init⟩
  · -- (ii) Position ODE at t ∈ Ioo 0 T.
    intro t ht z _
    exact ((Classical.choose_spec (h_perZ z)).2.1 t ht).1
  · -- (iii) Velocity ODE at t ∈ Ioo 0 T.
    intro t ht z _
    exact ((Classical.choose_spec (h_perZ z)).2.1 t ht).2
  · -- (iv) Boundary regularity bundle on Icc 0 T for every z.
    intro z t ht
    exact (Classical.choose_spec (h_perZ z)).2.2 t ht

/-! ## The pushforward operator Φ and its well-definedness -/
-- The pushforward operator Φ takes a characteristic flow `charX : ℝ → PhaseSpace
-- d → PhysSpace d` and an initial measure `f₀ : Measure (PhaseSpace d)`, and
-- produces a time-indexed curve of measures on `PhysSpace d` via
-- `Φ charX f₀ t := Measure.map (fun z => charX t z) f₀`.
--
-- Its well-definedness comprises:
--   * `Phi`: the bare definition.
--   * `Phi_isProbabilityMeasure`: under AEMeasurable hypothesis.
--   * `Phi_hasMoment_le`: under measurability + per-z growth-bound hypothesis.
--   * `Phi_yIntegrable`: derived from hasMoment_le.
--   * `Phi_hW1Cont`: W₁-continuity via DCT.
--   * `PhiAsVlasovMeasureCurve`: the full bundling into a `VlasovMeasureCurve d T M`.
--
-- The measurability + growth-bound hypotheses are passed through as inputs; their
-- discharge happens at the call site (the Picard iteration), where the concrete
-- flow is constructed and the hypotheses follow from the construction.

/-- The Φ pushforward operator: maps a characteristic flow + initial measure to
the time-indexed pushforward measure on `PhysSpace d`. -/
noncomputable def Phi {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) : ℝ → Measure (PhysSpace d) :=
  fun t => Measure.map (fun z => charX t z) f₀

/-- `Phi charX f₀ t` is a probability measure when `charX t` is AE-measurable
wrt `f₀`. -/
theorem Phi_isProbabilityMeasure {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (t : ℝ) :
    IsProbabilityMeasure (Phi charX f₀ t) := by
  unfold Phi
  exact (MeasureTheory.Measure.isProbabilityMeasure_map_iff (h_meas t)).mpr inferInstance

/-- Uniform first-moment bound on `Phi charX f₀` under a per-z position growth
hypothesis `‖charX t z‖ ≤ C_T · (‖z‖ + 1)`.

Composes `integral_map` (which exchanges the pushforward) with the pointwise
growth bound + linearity of integration over `f₀`. -/
theorem Phi_hasMoment_le {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (T : ℝ) (_hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (M_f₀ : ℝ) (hM_f₀ : ∫ z, ‖z‖ ∂f₀ ≤ M_f₀)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∫ y, ‖y‖ ∂(Phi charX f₀ t) ≤ C_T * (M_f₀ + 1) := by
  unfold Phi
  -- ∫ y ‖y‖ ∂(Measure.map (charX t) f₀) = ∫ z ‖charX t z‖ ∂f₀  via integral_map.
  rw [integral_map (h_meas t) (Continuous.aestronglyMeasurable continuous_norm)]
  -- ≤ ∫ z (C_T·(‖z‖+1)) ∂f₀  via pointwise growth bound.
  have h_growth_t := h_growth t ht
  -- Both sides integrable; use integral_mono.
  have h_growth_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
    have : Integrable (fun z : PhaseSpace d => ‖z‖ + 1) f₀ :=
      h_f₀_int.add (integrable_const _)
    exact this.const_mul _
  have h_lhs_int : Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀ := by
    refine Integrable.mono' h_growth_int ((h_meas t).norm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    have hbd := h_growth_t z
    have h_rhs_nn : 0 ≤ C_T * (‖z‖ + 1) := by
      apply mul_nonneg hC_T_nn
      linarith [norm_nonneg z]
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    linarith
  calc ∫ z, ‖charX t z‖ ∂f₀
      ≤ ∫ z, C_T * (‖z‖ + 1) ∂f₀ :=
        integral_mono h_lhs_int h_growth_int (fun z => h_growth_t z)
    _ = C_T * ∫ z, (‖z‖ + 1) ∂f₀ := by
        rw [integral_const_mul]
    _ = C_T * (∫ z, ‖z‖ ∂f₀ + 1) := by
        congr 1
        rw [integral_add h_f₀_int (integrable_const _)]
        simp [integral_const, measureReal_def, measure_univ]
    _ ≤ C_T * (M_f₀ + 1) := by
        have h_M_nn : 0 ≤ M_f₀ + 1 := by
          have : 0 ≤ ∫ z, ‖z‖ ∂f₀ := integral_nonneg (fun _ => norm_nonneg _)
          linarith [hM_f₀]
        apply mul_le_mul_of_nonneg_left _ hC_T_nn
        linarith

/-- `‖·‖` is integrable wrt `Phi charX f₀ t` under the growth hypothesis. -/
theorem Phi_yIntegrable {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (T : ℝ) (_hT : 0 ≤ T)
    (C_T : ℝ) (_hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Integrable (fun y : PhysSpace d => ‖y‖) (Phi charX f₀ t) := by
  -- Integrable wrt pushforward iff ‖·‖ ∘ (charX t) is integrable wrt f₀.
  unfold Phi
  rw [integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      (h_meas t)]
  -- Now integrable wrt f₀.
  have h_growth_t := h_growth t ht
  have h_growth_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
    have : Integrable (fun z : PhaseSpace d => ‖z‖ + 1) f₀ :=
      h_f₀_int.add (integrable_const _)
    exact this.const_mul _
  refine Integrable.mono' h_growth_int ?_ ?_
  · -- AEStronglyMeasurable of ‖·‖ ∘ charX t.
    exact ((h_meas t).aestronglyMeasurable.norm)
  · refine Filter.Eventually.of_forall fun z => ?_
    have hbd := h_growth_t z
    -- Goal shape: ‖((fun a => ‖a‖) ∘ (fun z => charX t z)) z‖ ≤ C_T * (‖z‖ + 1).
    -- The composition simplifies to ‖‖charX t z‖‖, then Real.norm_of_nonneg.
    simp only [Function.comp_apply]
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hbd

/-- **W₁ bound on Φ pushforwards via 1-Lipschitz test functions.**

For any two time points `s, t`, the Wasserstein-1 distance between
`Phi charX f₀ s` and `Phi charX f₀ t` is bounded by the integral
`∫ z, ‖charX s z - charX t z‖ ∂f₀`.

**Proof strategy** (KR-dual direct): for each 1-Lipschitz `φ : PhysSpace d → ℝ`,
`integral_map` converts `∫ φ d(charX_·)#f₀` to `∫ z, φ(charX_· z) ∂f₀`.
The integral diff is bounded pointwise by `‖charX s z - charX t z‖` (1-Lipschitz
of φ), then by integral monotonicity.

**Architectural note**: `wasserstein1_pushforward_le_iInf` (`Coupling.lean`)
requires endomaps `Φ Ψ : α → α`.  Our `charX t : PhaseSpace d → PhysSpace d`
is cross-type, so we work directly with the KR-dual sup — cleaner than
re-deriving the coupling theory.

All `Integrable.mono'` dominator facts are built as named `have` statements
before the call (no inline `?_`).  The `integrable_map_measure` bridge uses
`.mpr` to handle the `g ∘ f` ↔ `fun z => g (f z)` syntactic mismatch.

Used by `Phi_hW1Cont` to bound W₁(Φ_s, Φ_t) by an integral that DCT controls
as `t → s`. -/
theorem wasserstein1_Phi_le_integral_diff {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    -- ‖charX t z‖ integrable wrt f₀ for each t.
    (h_int_charX : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀)
    (s t : ℝ)
    -- ‖charX s z - charX t z‖ integrable wrt f₀ (follows from h_int_charX s, t + triangle).
    (h_diff_int : Integrable (fun z : PhaseSpace d => ‖charX s z - charX t z‖) f₀) :
    wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t) ≤
      ENNReal.ofReal (∫ z, ‖charX s z - charX t z‖ ∂f₀) := by
  simp only [wasserstein1_eq_iSup_lipschitz]
  unfold Phi
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  apply ENNReal.ofReal_le_ofReal
  -- ============================================================
  -- Setup: φ is 1-Lipschitz; AEStronglyMeasurable wrt each pushforward.
  -- ============================================================
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_meas_νs : AEStronglyMeasurable φ (Measure.map (fun z => charX s z) f₀) :=
    hφ_cont.aestronglyMeasurable
  have hφ_meas_νt : AEStronglyMeasurable φ (Measure.map (fun z => charX t z) f₀) :=
    hφ_cont.aestronglyMeasurable
  -- ============================================================
  -- 1-Lipschitz dominator: |φ y| ≤ |φ 0| + ‖y‖.
  -- ============================================================
  have hφ_abs_bound : ∀ y : PhysSpace d, |φ y| ≤ |φ 0| + ‖y‖ := fun y => by
    have h_lip := hφ.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right, NNReal.coe_one, one_mul] at h_lip
    calc |φ y| = |(φ y - φ 0) + φ 0| := by ring_nf
      _ ≤ |φ y - φ 0| + |φ 0| := abs_add_le _ _
      _ ≤ ‖y‖ + |φ 0| := by linarith
      _ = |φ 0| + ‖y‖ := by ring
  -- ============================================================
  -- EXPLICIT DOMINATOR CONSTRUCTION (CLAUDE.md L7).
  -- Build h_norm_int_νs and h_norm_int_νt via `.mpr` (CLAUDE.md L8) —
  -- this avoids the `g ∘ f` ↔ `fun z => g (f z)` rewrite mismatch.
  -- ============================================================
  have h_norm_int_νs : Integrable (fun y : PhysSpace d => ‖y‖)
      (Measure.map (fun z => charX s z) f₀) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      (h_meas s)).mpr (h_int_charX s)
  have h_norm_int_νt : Integrable (fun y : PhysSpace d => ‖y‖)
      (Measure.map (fun z => charX t z) f₀) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      (h_meas t)).mpr (h_int_charX t)
  -- Dominator `|φ 0| + ‖y‖` integrable wrt each pushforward.
  have h_dom_νs : Integrable (fun y : PhysSpace d => |φ 0| + ‖y‖)
      (Measure.map (fun z => charX s z) f₀) :=
    (integrable_const _).add h_norm_int_νs
  have h_dom_νt : Integrable (fun y : PhysSpace d => |φ 0| + ‖y‖)
      (Measure.map (fun z => charX t z) f₀) :=
    (integrable_const _).add h_norm_int_νt
  -- φ integrable wrt each pushforward (via `Integrable.mono'` with explicit dominator).
  have hφ_int_νs : Integrable φ (Measure.map (fun z => charX s z) f₀) := by
    refine Integrable.mono' h_dom_νs hφ_meas_νs ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have h_dom_nn : 0 ≤ |φ 0| + ‖y‖ :=
      add_nonneg (abs_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact hφ_abs_bound y
  have hφ_int_νt : Integrable φ (Measure.map (fun z => charX t z) f₀) := by
    refine Integrable.mono' h_dom_νt hφ_meas_νt ?_
    refine Filter.Eventually.of_forall fun y => ?_
    have h_dom_nn : 0 ≤ |φ 0| + ‖y‖ :=
      add_nonneg (abs_nonneg _) (norm_nonneg _)
    rw [Real.norm_eq_abs]
    exact hφ_abs_bound y
  -- ============================================================
  -- Convert pushforward integrals via `integral_map`.
  -- The RHS of `integral_map` is point-full `f (g x)` (NOT `(f ∘ g) x`),
  -- so no L8 bridge needed here.
  -- ============================================================
  rw [integral_map (h_meas s) hφ_meas_νs,
      integral_map (h_meas t) hφ_meas_νt]
  -- Goal: ∫ z, φ (charX s z) ∂f₀ - ∫ z, φ (charX t z) ∂f₀
  --        ≤ ∫ z, ‖charX s z - charX t z‖ ∂f₀.
  -- ============================================================
  -- Pull-back integrability of `fun z => φ (charX · z)` to wrt f₀ via `.mp`.
  -- ============================================================
  have hφ_comp_int_s : Integrable (fun z : PhaseSpace d => φ (charX s z)) f₀ :=
    (integrable_map_measure hφ_meas_νs (h_meas s)).mp hφ_int_νs
  have hφ_comp_int_t : Integrable (fun z : PhaseSpace d => φ (charX t z)) f₀ :=
    (integrable_map_measure hφ_meas_νt (h_meas t)).mp hφ_int_νt
  -- Combine into single integral; bound by Lipschitz inequality.
  rw [← integral_sub hφ_comp_int_s hφ_comp_int_t]
  have h_pt : ∀ z : PhaseSpace d,
      φ (charX s z) - φ (charX t z) ≤ ‖charX s z - charX t z‖ := fun z => by
    have h_lip := hφ.dist_le_mul (charX s z) (charX t z)
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] at h_lip
    -- h_lip : |φ (charX s z) - φ (charX t z)| ≤ ‖charX s z - charX t z‖.
    linarith [abs_le.mp h_lip |>.2]
  exact integral_mono (hφ_comp_int_s.sub hφ_comp_int_t) h_diff_int h_pt

/-- **DCT step — the integral `∫ z, ‖charX s z - charX t z‖ ∂f₀`
tends to 0 as `t → s` within `Icc 0 T`.**

Combines pointwise continuity `t ↦ charX t z` (from the flow's HasDerivAt
→ ContinuousAt) with a uniform dominator `2·C_T·(‖z‖+1)` (from the per-z
growth bound) via Mathlib's filter-DCT.  The dominator integrability is
built as a named `have` before the DCT call. -/
theorem Phi_integral_diff_tendsto_zero {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (T : ℝ) (_hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    -- Continuity of t ↦ charX t z at base s (from HasDerivAt).
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) T)
    (h_charX_cont : ∀ z, ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s) :
    Filter.Tendsto (fun t => ∫ z, ‖charX s z - charX t z‖ ∂f₀)
      (nhdsWithin s (Set.Icc 0 T)) (nhds 0) := by
  -- ============================================================
  -- Dominator: `bound z := 2 * C_T * (‖z‖ + 1)` integrable wrt f₀.
  -- ============================================================
  set bound : PhaseSpace d → ℝ :=
    fun z => 2 * C_T * (‖z‖ + 1) with hbound_def
  have h_bound_int : Integrable bound f₀ := by
    have h1 : Integrable (fun z : PhaseSpace d => ‖z‖ + 1) f₀ :=
      h_f₀_int.add (integrable_const _)
    exact h1.const_mul _
  -- ============================================================
  -- AE strong measurability of (fun z => ‖charX s z - charX t z‖) wrt f₀, eventually in t.
  -- ============================================================
  have h_F_meas : ∀ᶠ t in nhdsWithin s (Set.Icc 0 T),
      AEStronglyMeasurable (fun z : PhaseSpace d => ‖charX s z - charX t z‖) f₀ := by
    refine Filter.Eventually.of_forall fun t => ?_
    exact ((h_meas s).sub (h_meas t)).norm.aestronglyMeasurable
  -- ============================================================
  -- Pointwise bound: ‖‖charX s z - charX t z‖‖ ≤ bound z eventually.
  -- ============================================================
  have h_F_bound : ∀ᶠ t in nhdsWithin s (Set.Icc 0 T),
      ∀ᵐ z ∂f₀, ‖‖charX s z - charX t z‖‖ ≤ bound z := by
    refine Filter.eventually_iff_exists_mem.mpr ⟨Set.Icc 0 T, ?_, ?_⟩
    · exact self_mem_nhdsWithin
    · intro t ht
      refine Filter.Eventually.of_forall fun z => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      have h_tri := norm_sub_le (charX s z) (charX t z)
      have h_s := h_growth s hs z
      have h_t := h_growth t ht z
      have h_C_nn_2 : 0 ≤ 2 * C_T := by linarith
      have hz_nn : 0 ≤ ‖z‖ + 1 := by linarith [norm_nonneg z]
      calc ‖charX s z - charX t z‖
          ≤ ‖charX s z‖ + ‖charX t z‖ := h_tri
        _ ≤ C_T * (‖z‖ + 1) + C_T * (‖z‖ + 1) := by linarith
        _ = 2 * C_T * (‖z‖ + 1) := by ring
  -- ============================================================
  -- Pointwise limit: ‖charX s z - charX t z‖ → 0 as t → s within Icc 0 T.
  -- ============================================================
  have h_F_lim : ∀ᵐ z ∂f₀, Filter.Tendsto
      (fun t => ‖charX s z - charX t z‖) (nhdsWithin s (Set.Icc 0 T)) (nhds 0) := by
    refine Filter.Eventually.of_forall fun z => ?_
    -- t ↦ charX s z - charX t z → 0 as t → s, because charX(·) z → charX s z.
    have h_tendsto : Filter.Tendsto (fun t => charX t z) (nhdsWithin s (Set.Icc 0 T))
                       (nhds (charX s z)) := h_charX_cont z
    have h_sub : Filter.Tendsto (fun t => charX s z - charX t z)
                   (nhdsWithin s (Set.Icc 0 T)) (nhds 0) := by
      have h_cancel : (charX s z - charX s z : PhysSpace d) = 0 := sub_self _
      rw [← h_cancel]
      exact (tendsto_const_nhds (x := charX s z)).sub h_tendsto
    have h_norm_tendsto :
        Filter.Tendsto (fun t => ‖charX s z - charX t z‖)
          (nhdsWithin s (Set.Icc 0 T)) (nhds ‖(0 : PhysSpace d)‖) :=
      (continuous_norm.tendsto 0).comp h_sub
    simpa using h_norm_tendsto
  -- ============================================================
  -- Apply Mathlib's filter-DCT.
  -- ============================================================
  have h_dct := MeasureTheory.tendsto_integral_filter_of_dominated_convergence (μ := f₀)
    bound h_F_meas h_F_bound h_bound_int h_F_lim
  -- h_dct : Tendsto (fun t => ∫ z, ‖charX s z - charX t z‖ ∂f₀)
  --   (nhdsWithin s (Icc 0 T)) (nhds (∫ z, 0 ∂f₀))
  -- ∫ z, 0 ∂f₀ = 0
  simp only [integral_zero] at h_dct
  exact h_dct

/-- **W₁-continuity of `t ↦ Phi charX f₀ t` at every base point `s ∈ Icc 0 T`.**

Composes the W₁ bound (`wasserstein1_Phi_le_integral_diff`) with the DCT step
(`Phi_integral_diff_tendsto_zero`) to conclude that
`(wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal → 0` as `t → s`. -/
theorem Phi_hW1Cont {d : ℕ}
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (h_int_charX : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀)
    (T : ℝ) (hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (h_charX_cont : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z,
      ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s) :
    ∀ s ∈ Set.Icc (0 : ℝ) T,
      ContinuousWithinAt
        (fun t => (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal)
        (Set.Icc 0 T) s := by
  intro s hs
  -- ContinuousWithinAt at s ↔ Tendsto · → value-at-s within filter.
  -- Value at t = s: wasserstein1_self = 0.
  rw [ContinuousWithinAt]
  have h_value_at_s : (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ s)).toReal = 0 := by
    rw [wasserstein1_self]; rfl
  rw [h_value_at_s]
  -- DCT gives ∫-tendsto-zero.
  have h_dct := Phi_integral_diff_tendsto_zero charX f₀ h_meas T hT C_T hC_T_nn
    h_growth h_f₀_int s hs (h_charX_cont s hs)
  -- Combine: W₁ bound ⇒ toReal bound ⇒ tendsto-zero.
  -- Strategy: bound the W₁.toReal by the integral via wasserstein1_Phi_le_integral_diff.
  -- Then use squeeze on Tendsto.
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  -- From h_dct: ∃ δ, ∀ t ∈ Icc 0 T, dist t s < δ → |∫ ...| < ε.
  rw [Metric.tendsto_nhdsWithin_nhds] at h_dct
  obtain ⟨δ, hδ_pos, hδ_bd⟩ := h_dct ε hε
  -- Use the same δ.
  refine ⟨δ, hδ_pos, fun t ht hdt => ?_⟩
  -- Goal: dist ((wasserstein1 (Phi s) (Phi t)).toReal) 0 < ε.
  rw [Real.dist_eq, sub_zero]
  -- |(W₁ s t).toReal| ≤ |∫ ...|.
  have hΦs_prob : IsProbabilityMeasure (Phi charX f₀ s) :=
    Phi_isProbabilityMeasure charX f₀ h_meas s
  have hΦt_prob : IsProbabilityMeasure (Phi charX f₀ t) :=
    Phi_isProbabilityMeasure charX f₀ h_meas t
  have h_yint_s : Integrable (fun y : PhysSpace d => ‖y‖) (Phi charX f₀ s) :=
    Phi_yIntegrable charX f₀ h_meas T hT C_T hC_T_nn h_growth h_f₀_int s hs
  have h_yint_t : Integrable (fun y : PhysSpace d => ‖y‖) (Phi charX f₀ t) :=
    Phi_yIntegrable charX f₀ h_meas T hT C_T hC_T_nn h_growth h_f₀_int t ht
  have h_W1_finite : wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t) ≠ ⊤ :=
    wasserstein1_ne_top_of_finite_moment _ _ h_yint_s h_yint_t
  have h_diff_int_t : Integrable (fun z : PhaseSpace d => ‖charX s z - charX t z‖) f₀ := by
    -- Inline the integrability proof to avoid the `Filter.eventually_iff_exists_mem`
    -- destructuring's metavariable mismatch.
    have h_dom_int : Integrable (fun z : PhaseSpace d => 2 * C_T * (‖z‖ + 1)) f₀ :=
      (h_f₀_int.add (integrable_const _)).const_mul _
    refine Integrable.mono' h_dom_int
      (((h_meas s).sub (h_meas t)).norm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have h_tri := norm_sub_le (charX s z) (charX t z)
    have h_s := h_growth s hs z
    have h_t := h_growth t ht z
    calc ‖charX s z - charX t z‖
        ≤ ‖charX s z‖ + ‖charX t z‖ := h_tri
      _ ≤ C_T * (‖z‖ + 1) + C_T * (‖z‖ + 1) := by linarith
      _ = 2 * C_T * (‖z‖ + 1) := by ring
  have h_W1_le := wasserstein1_Phi_le_integral_diff charX f₀ h_meas h_int_charX
    s t h_diff_int_t
  -- |∫ ‖charX s z - charX t z‖ ∂f₀| < ε from hδ_bd.
  have h_int_bd := hδ_bd ht hdt
  rw [Real.dist_eq, sub_zero] at h_int_bd
  -- Combine: (W₁ s t).toReal ≤ ofReal(∫ ‖...‖).toReal ≤ |∫ ‖...‖| < ε.
  have h_int_nn : 0 ≤ ∫ z, ‖charX s z - charX t z‖ ∂f₀ :=
    integral_nonneg (fun _ => norm_nonneg _)
  have h_toReal_le : (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal ≤
      ∫ z, ‖charX s z - charX t z‖ ∂f₀ := by
    have h_ofReal_eq : (ENNReal.ofReal (∫ z, ‖charX s z - charX t z‖ ∂f₀)).toReal
                      = ∫ z, ‖charX s z - charX t z‖ ∂f₀ := by
      rw [ENNReal.toReal_ofReal h_int_nn]
    rw [← h_ofReal_eq]
    exact ENNReal.toReal_mono ENNReal.ofReal_ne_top h_W1_le
  have h_toReal_nn : 0 ≤ (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal :=
    ENNReal.toReal_nonneg
  rw [abs_of_nonneg h_toReal_nn]
  calc (wasserstein1 (Phi charX f₀ s) (Phi charX f₀ t)).toReal
      ≤ ∫ z, ‖charX s z - charX t z‖ ∂f₀ := h_toReal_le
    _ < ε := by
        have h_abs_eq : |∫ z, ‖charX s z - charX t z‖ ∂f₀|
                      = ∫ z, ‖charX s z - charX t z‖ ∂f₀ := abs_of_nonneg h_int_nn
        linarith [h_int_bd, h_abs_eq.symm.le, abs_nonneg (∫ z, ‖charX s z - charX t z‖ ∂f₀)]

/-- **Full bundling of Φ into a `VlasovMeasureCurve`.**

Given the four hypothesis bundles (measurability, growth, f₀'s integrability,
flow continuity), bundles the three pushforward well-definedness properties +
`Phi_hW1Cont` into a `VlasovMeasureCurve d T M'` where `M' := C_T · (M_f₀ + 1)`.

This is the structured output that the contraction estimate and Banach
iteration consume. -/
noncomputable def PhiAsVlasovMeasureCurve {d : ℕ} [NeZero d]
    (charX : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas : ∀ t, AEMeasurable (fun z : PhaseSpace d => charX t z) f₀)
    (h_int_charX : ∀ t, Integrable (fun z : PhaseSpace d => ‖charX t z‖) f₀)
    (T : ℝ) (hT : 0 ≤ T)
    (C_T : ℝ) (hC_T_nn : 0 ≤ C_T)
    (h_growth : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX t z‖ ≤ C_T * (‖z‖ + 1))
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (M_f₀ : ℝ) (hM_f₀ : ∫ z, ‖z‖ ∂f₀ ≤ M_f₀)
    (h_charX_cont : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z,
      ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s) :
    VlasovMeasureCurve d T (fun _ => C_T * (M_f₀ + 1)) where
  ρ := Phi charX f₀
  isProb := Phi_isProbabilityMeasure charX f₀ h_meas
  hasMoment := fun t ht =>
    Phi_hasMoment_le charX f₀ h_meas T hT C_T hC_T_nn h_growth h_f₀_int M_f₀ hM_f₀ t ht
  yIntegrable := fun t ht =>
    Phi_yIntegrable charX f₀ h_meas T hT C_T hC_T_nn h_growth h_f₀_int t ht
  hW1Cont :=
    Phi_hW1Cont charX f₀ h_meas h_int_charX T hT C_T hC_T_nn h_growth h_f₀_int
      h_charX_cont

/-- **Measurability of a characteristic flow given Picard-style boundary
regularity.**

Given a flow `(charX, charV)` that:
* matches the initial condition at `t = 0`,
* is continuous in `t` on `Icc 0 T` for each `z` (i.e. Picard-solution
  regularity at the boundary),
* satisfies the Vlasov ODE in `HasDerivWithinAt`-on-`Ico` form,

we prove that for each `t ∈ Icc 0 T`, the map `z ↦ (charX t z, charV t z)`
is Borel-measurable on `PhaseSpace d`.

**Proof strategy** (Gronwall on flow difference, via Mathlib's
`dist_le_of_trajectories_ODE`):  the Vlasov vector field is
`max(1, L)`-Lipschitz uniformly in `t` (`vlasovVectorField_lipschitzWith`),
so two trajectories `f, g : ℝ → PhaseSpace d` starting from `z₁, z₂` satisfy
`dist (f t) (g t) ≤ dist(z₁, z₂) · exp(max(1, L) · t)` for `t ∈ Icc 0 T`.
This is exp(K·t)-Lipschitz-in-`z`, hence continuous in `z`, hence Borel-
measurable.

**Why the boundary regularity is taken as hypothesis**: the flow
construction's `IsCharacteristicFlowOn ... (Ioo 0 T) Set.univ` gives
`HasDerivAt` only on the open interval `Ioo 0 T`.  Mathlib's
`dist_le_of_trajectories_ODE` requires `ContinuousOn` on `Icc 0 T` plus
`HasDerivWithinAt` on `Ico 0 T` (closed at the left endpoint).  The boundary
regularity at `t = 0` is a property of the underlying Picard construction,
not derivable from `IsCharacteristicFlowOn` alone.  The Picard iteration
discharges these hypotheses from the concrete construction.

This is what the Picard construction plugs into the Φ pipeline. -/
theorem charFlow_measurable_via_gronwall
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (_hT : 0 ≤ T)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ico : ∀ z, ∀ t ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ t (charX t z, charV t z))
        (Set.Ici t) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
        Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) := by
  intro t ht
  -- ============================================================
  -- Vector field is max(1, L)-Lipschitz uniformly in t.
  -- ============================================================
  set K : NNReal := max 1 L with hK_def
  have h_vf_lip : ∀ s, LipschitzWith K (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  -- ============================================================
  -- Gronwall on flow difference: dist-bound on Icc 0 T.
  -- ============================================================
  have h_dist_bound : ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX t z₁, charV t z₁) : PhaseSpace d) (charX t z₂, charV t z₂) ≤
      dist z₁ z₂ * Real.exp ((K : ℝ) * (t - 0)) := by
    intro z₁ z₂
    -- Apply dist_le_of_trajectories_ODE with f, g = per-z trajectories.
    have h := dist_le_of_trajectories_ODE
      (v := fun s => vlasovVectorField gradW ρ s)
      (f := fun s => (charX s z₁, charV s z₁))
      (g := fun s => (charX s z₂, charV s z₂))
      (K := K) (a := 0) (b := T)
      (δ := dist z₁ z₂)
      h_vf_lip
      (h_cont_Icc z₁) (h_deriv_Ico z₁)
      (h_cont_Icc z₂) (h_deriv_Ico z₂)
      ?_ t ht
    · exact h
    · -- dist (f 0) (g 0) = dist z₁ z₂ via h_init.  Need to beta-reduce first.
      change dist ((charX 0 z₁, charV 0 z₁) : PhaseSpace d) (charX 0 z₂, charV 0 z₂)
           ≤ dist z₁ z₂
      rw [h_init z₁, h_init z₂]
  -- ============================================================
  -- Convert dist-bound to continuity in z via Metric.continuous_iff.
  -- ============================================================
  have h_cont_z : Continuous (fun z : PhaseSpace d => (charX t z, charV t z)) := by
    rw [Metric.continuous_iff]
    intro z₀ ε hε
    -- Lipschitz constant exp(K * t); pick δ := ε / exp(K * t).
    have h_exp_pos : 0 < Real.exp ((K : ℝ) * (t - 0)) := Real.exp_pos _
    refine ⟨ε / Real.exp ((K : ℝ) * (t - 0)), div_pos hε h_exp_pos, ?_⟩
    intro z hz
    -- dist (f z₀) (f z) ≤ exp(K*t) * dist z₀ z < exp(K*t) * (ε / exp(K*t)) = ε.
    have h_bd := h_dist_bound z₀ z
    -- Note: dist_bound gives `dist (f z₀) (f z)`, but `Metric.continuous_iff`
    -- gives `dist z z₀ < δ → dist (f z) (f z₀) < ε`.  Symmetric: use dist_comm.
    rw [dist_comm] at hz
    have h_chain : dist ((charX t z₀, charV t z₀) : PhaseSpace d) (charX t z, charV t z)
                  < ε := by
      calc dist ((charX t z₀, charV t z₀) : PhaseSpace d) (charX t z, charV t z)
          ≤ dist z₀ z * Real.exp ((K : ℝ) * (t - 0)) := h_bd
        _ < (ε / Real.exp ((K : ℝ) * (t - 0))) * Real.exp ((K : ℝ) * (t - 0)) :=
            mul_lt_mul_of_pos_right hz h_exp_pos
        _ = ε := div_mul_cancel₀ ε (ne_of_gt h_exp_pos)
    rwa [dist_comm] at h_chain
  exact h_cont_z.measurable

/-- **Step 0b — the flow's Lipschitz-in-`z` bound (open-interval form).**

Extracted from `charFlow_measurable_via_gronwall_Ioo`'s internal
`h_dist_bound`.  Given the open-interval flow ODE, the characteristic flow
`z ↦ (charX t z, charV t z)` is Lipschitz in the initial datum `z` with
constant `exp((max 1 L) · (t − 0))`, uniformly for `t ∈ [0, T]`.

Same hypotheses as `charFlow_measurable_via_gronwall_Ioo`; the conclusion
is the Grönwall distance bound used by both that lemma (to derive
continuity-in-`z` hence measurability) and the moment-free dominator in
`dobrushin_uniqueness_On`. -/
theorem charFlow_lipschitzInZ_via_gronwall_Ioo
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 ≤ T)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ioo : ∀ z, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ t (charX t z, charV t z))
        (Set.Ici t) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z₁ z₂ : PhaseSpace d,
        dist ((charX t z₁, charV t z₁) : PhaseSpace d) (charX t z₂, charV t z₂) ≤
        dist z₁ z₂ * Real.exp (((max 1 L : NNReal) : ℝ) * (t - 0)) := by
  intro t ht
  -- Vector field is max(1, L)-Lipschitz uniformly in s.
  set K : NNReal := max 1 L with hK_def
  have h_vf_lip : ∀ s, LipschitzWith K (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  intro z₁ z₂
  -- Abbreviations for the two per-z trajectories.
  set F : ℝ → PhaseSpace d := fun s => (charX s z₁, charV s z₁) with hF_def
  set G : ℝ → PhaseSpace d := fun s => (charX s z₂, charV s z₂) with hG_def
  -- Split on whether t = 0 or 0 < t.
  rcases eq_or_lt_of_le ht.1 with h_t0 | h_pos
  · -- t = 0: both trajectories evaluate to their initial conditions.
    subst h_t0
    simp only [h_init z₁, h_init z₂, sub_self, mul_zero,
      Real.exp_zero, mul_one, le_refl]
  · -- 0 < t: take the s₀ → 0⁺ limit of Grönwall bounds on [s₀, t].
    -- Per-s₀ Grönwall bound on the window [s₀, t] ⊆ [0, T].
    have h_perS0 : ∀ s₀ ∈ Set.Ioo (0 : ℝ) t,
        dist (F t) (G t) ≤ dist (F s₀) (G s₀) * Real.exp ((K : ℝ) * (t - s₀)) := by
      intro s₀ hs₀
      -- Window inclusions.
      have hsub_Ico : Set.Ico s₀ t ⊆ Set.Ioo (0 : ℝ) T := fun s hs =>
        ⟨lt_of_lt_of_le hs₀.1 hs.1, lt_of_lt_of_le hs.2 ht.2⟩
      have hsub_Icc : Set.Icc s₀ t ⊆ Set.Icc (0 : ℝ) T :=
        Set.Icc_subset_Icc hs₀.1.le ht.2
      have h := dist_le_of_trajectories_ODE
        (v := fun s => vlasovVectorField gradW ρ s)
        (f := F) (g := G)
        (K := K) (a := s₀) (b := t)
        (δ := dist (F s₀) (G s₀))
        h_vf_lip
        ((h_cont_Icc z₁).mono hsub_Icc)
        (fun s hs => h_deriv_Ioo z₁ s (hsub_Ico hs))
        ((h_cont_Icc z₂).mono hsub_Icc)
        (fun s hs => h_deriv_Ioo z₂ s (hsub_Ico hs))
        (le_refl _) t ⟨hs₀.2.le, le_refl t⟩
      exact h
    -- The filter 𝓝[Ioo 0 t] 0 is NeBot since 0 < t.
    have : (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)).NeBot :=
      left_nhdsWithin_Ioo_neBot h_pos
    -- Tendsto F to z₁ along 𝓝[Ioo 0 t] 0.
    have hIoo_sub_Icc : Set.Ioo (0 : ℝ) t ⊆ Set.Icc (0 : ℝ) T := fun s hs =>
      ⟨hs.1.le, le_trans hs.2.le ht.2⟩
    have hF0 : F 0 = z₁ := h_init z₁
    have hG0 : G 0 = z₂ := h_init z₂
    have h_tendsto_F : Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
        (nhds z₁) := by
      have hcw : ContinuousWithinAt F (Set.Icc (0 : ℝ) T) 0 :=
        (h_cont_Icc z₁) 0 ⟨le_refl 0, hT⟩
      have : Filter.Tendsto F (nhdsWithin (0 : ℝ) (Set.Icc 0 T)) (nhds (F 0)) :=
        hcw
      rw [hF0] at this
      exact this.mono_left (nhdsWithin_mono 0 hIoo_sub_Icc)
    have h_tendsto_G : Filter.Tendsto G (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
        (nhds z₂) := by
      have hcw : ContinuousWithinAt G (Set.Icc (0 : ℝ) T) 0 :=
        (h_cont_Icc z₂) 0 ⟨le_refl 0, hT⟩
      have : Filter.Tendsto G (nhdsWithin (0 : ℝ) (Set.Icc 0 T)) (nhds (G 0)) :=
        hcw
      rw [hG0] at this
      exact this.mono_left (nhdsWithin_mono 0 hIoo_sub_Icc)
    -- Tendsto of dist (F s₀) (G s₀) to dist z₁ z₂.
    have h_tendsto_dist :
        Filter.Tendsto (fun s₀ => dist (F s₀) (G s₀))
          (nhdsWithin (0 : ℝ) (Set.Ioo 0 t)) (nhds (dist z₁ z₂)) :=
      h_tendsto_F.dist h_tendsto_G
    -- Tendsto of exp(K*(t-s₀)) to exp(K*(t-0)).
    have h_tendsto_exp :
        Filter.Tendsto (fun s₀ => Real.exp ((K : ℝ) * (t - s₀)))
          (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
          (nhds (Real.exp ((K : ℝ) * (t - 0)))) := by
      have hcont : Continuous (fun s₀ : ℝ => Real.exp ((K : ℝ) * (t - s₀))) := by
        fun_prop
      exact (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
    -- Product of the two limits.
    have h_lim :
        Filter.Tendsto (fun s₀ => dist (F s₀) (G s₀) * Real.exp ((K : ℝ) * (t - s₀)))
          (nhdsWithin (0 : ℝ) (Set.Ioo 0 t))
          (nhds (dist z₁ z₂ * Real.exp ((K : ℝ) * (t - 0)))) :=
      h_tendsto_dist.mul h_tendsto_exp
    -- The per-s₀ bound holds eventually along the filter.
    have h_event :
        ∀ᶠ s₀ in nhdsWithin (0 : ℝ) (Set.Ioo 0 t),
          dist (F t) (G t) ≤ dist (F s₀) (G s₀) * Real.exp ((K : ℝ) * (t - s₀)) :=
      eventually_nhdsWithin_of_forall h_perS0
    -- Pass to the limit.
    exact ge_of_tendsto h_lim h_event

/-- **Open-interval variant of `charFlow_measurable_via_gronwall`.**

Identical to `charFlow_measurable_via_gronwall` except the derivative
hypothesis is on the OPEN interval `Set.Ioo 0 T` instead of the
half-open `Set.Ico 0 T`.  This matches the regularity that an
`IsCharacteristicFlowOn ... (Set.Ioo 0 T)` predicate directly produces
(the ODE holds on the open interval, with the endpoints handled by
continuity).

The proof reuses the per-window Grönwall distance bound, but obtains the
`t = 0` endpoint distance bound by taking a one-sided limit
`s₀ → 0⁺` of the Grönwall bounds on `[s₀, t]` (each of which only needs
the derivative on `Set.Ico s₀ t ⊆ Set.Ioo 0 T`), rather than applying
Grönwall directly on `[0, t]`. -/
theorem charFlow_measurable_via_gronwall_Ioo
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)]
    (h_int : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (hT : 0 ≤ T)
    (h_init : ∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z)
    (h_cont_Icc : ∀ z,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_Ioo : ∀ z, ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivWithinAt (fun s => (charX s z, charV s z))
        (vlasovVectorField gradW ρ t (charX t z, charV t z))
        (Set.Ici t) t) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
        Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) := by
  intro t ht
  -- ============================================================
  -- Vector field is max(1, L)-Lipschitz uniformly in t.
  -- ============================================================
  set K : NNReal := max 1 L with hK_def
  have h_vf_lip : ∀ s, LipschitzWith K (vlasovVectorField gradW ρ s) := fun s =>
    vlasovVectorField_lipschitzWith gradW L hL ρ h_int s
  -- ============================================================
  -- Gronwall on flow difference: dist-bound on Icc 0 T (step 0b, extracted
  -- to `charFlow_lipschitzInZ_via_gronwall_Ioo`).
  -- ============================================================
  have h_dist_bound : ∀ z₁ z₂ : PhaseSpace d,
      dist ((charX t z₁, charV t z₁) : PhaseSpace d) (charX t z₂, charV t z₂) ≤
      dist z₁ z₂ * Real.exp ((K : ℝ) * (t - 0)) :=
    charFlow_lipschitzInZ_via_gronwall_Ioo gradW L hL ρ h_int charX charV T hT
      h_init h_cont_Icc h_deriv_Ioo t ht
  -- ============================================================
  -- Convert dist-bound to continuity in z via Metric.continuous_iff.
  -- ============================================================
  have h_cont_z : Continuous (fun z : PhaseSpace d => (charX t z, charV t z)) := by
    rw [Metric.continuous_iff]
    intro z₀ ε hε
    -- Lipschitz constant exp(K * t); pick δ := ε / exp(K * t).
    have h_exp_pos : 0 < Real.exp ((K : ℝ) * (t - 0)) := Real.exp_pos _
    refine ⟨ε / Real.exp ((K : ℝ) * (t - 0)), div_pos hε h_exp_pos, ?_⟩
    intro z hz
    -- dist (f z₀) (f z) ≤ exp(K*t) * dist z₀ z < exp(K*t) * (ε / exp(K*t)) = ε.
    have h_bd := h_dist_bound z₀ z
    -- Note: dist_bound gives `dist (f z₀) (f z)`, but `Metric.continuous_iff`
    -- gives `dist z z₀ < δ → dist (f z) (f z₀) < ε`.  Symmetric: use dist_comm.
    rw [dist_comm] at hz
    have h_chain : dist ((charX t z₀, charV t z₀) : PhaseSpace d) (charX t z, charV t z)
                  < ε := by
      calc dist ((charX t z₀, charV t z₀) : PhaseSpace d) (charX t z, charV t z)
          ≤ dist z₀ z * Real.exp ((K : ℝ) * (t - 0)) := h_bd
        _ < (ε / Real.exp ((K : ℝ) * (t - 0))) * Real.exp ((K : ℝ) * (t - 0)) :=
            mul_lt_mul_of_pos_right hz h_exp_pos
        _ = ε := div_mul_cancel₀ ε (ne_of_gt h_exp_pos)
    rwa [dist_comm] at h_chain
  exact h_cont_z.measurable

/-- **Boundary regularity of a global-in-z flow.**

Given a flow `(charX, charV)` produced by
`exists_vlasov_characteristicFlow_global_smallT` with the open-interval
predicate `IsCharacteristicFlowOn ... (Set.Ioo 0 T) Set.univ`, this helper
extracts the closed-interval boundary regularity package needed by both
`flow_distance_growth_bound_on` and `charFlow_measurable_via_gronwall`:

* `h_init` — the initial-condition clause at `t = 0`,
* `h_cont_Icc` — continuity of `(charX, charV)(·, z)` on the closed
  interval `Icc 0 T`,
* `h_deriv_Ico` — HasDerivWithinAt on `Ico 0 T` (closed at the left
  endpoint).

The open-interval predicate `IsCharacteristicFlowOn` exposes only the
`Ioo`-HasDerivAt clause, while `flow_distance_growth_bound_on` and the
measurability lemma need `Icc`-ContinuousOn + `Ico`-HasDerivWithinAt.
The per-ball flow → per-z trajectory → global-in-z chain carries the
closed-interval `HasDerivWithinAt`-on-`Icc 0 T` data as a separate
conjunct; this theorem takes it as the explicit hypothesis `h_boundary`
and transports it into the precise form needed:

* `h_init` from `hflow.1 z (Set.mem_univ z)` (initial-condition clause).
* `h_cont_Icc` from `h_boundary`'s HasDerivWithinAt → ContinuousWithinAt
  → ContinuousOn (joining components via `Prod`).
* `h_deriv_Ico` from `h_boundary`'s HasDerivWithinAt-on-Icc lifted to
  HasDerivWithinAt-on-Ici at boundary points via `mono_of_mem_nhdsWithin`
  (the local-equivalence-of-filters argument). -/
theorem characteristicFlow_boundary_regularity
    {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (ρ : ℝ → Measure (PhysSpace d))
    (charX charV : ℝ → PhaseSpace d → PhysSpace d)
    (T : ℝ) (_hT : 0 ≤ T)
    (hflow : IsCharacteristicFlowOn gradW ρ charX charV
                                    (Set.Ioo 0 T) Set.univ)
    -- The boundary regularity is an explicit input.  The global-in-z →
    -- per-z → per-ball chain produces it as a separate conjunct alongside
    -- `IsCharacteristicFlowOn`; this helper transports the input forward
    -- into the precise form the Gronwall growth bound needs.
    (h_boundary : ∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (ρ t) (charX t z)))
          (Set.Icc 0 T) t) :
    (∀ z : PhaseSpace d, (charX 0 z, charV 0 z) = z) ∧
    (∀ z : PhaseSpace d,
      ContinuousOn (fun s => (charX s z, charV s z)) (Set.Icc (0 : ℝ) T)) ∧
    (∀ z : PhaseSpace d, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
        (vlasovVectorField gradW ρ s (charX s z, charV s z))
        (Set.Ici s) s) := by
  refine ⟨?_, ?_, ?_⟩
  · -- h_init: from hflow's initial-condition clause at every z ∈ univ.
    intro z
    obtain ⟨hX, hV⟩ := hflow.1 z (Set.mem_univ z)
    exact Prod.ext hX hV
  · -- h_cont_Icc: from h_boundary's HasDerivWithinAt → ContinuousWithinAt →
    -- ContinuousOn, joined componentwise via Prod.
    intro z s hs
    obtain ⟨h_pos_dw, h_vel_dw⟩ := h_boundary z s hs
    have h_pos_cwn : ContinuousWithinAt (fun s' => charX s' z) (Set.Icc 0 T) s :=
      h_pos_dw.continuousWithinAt
    have h_vel_cwn : ContinuousWithinAt (fun s' => charV s' z) (Set.Icc 0 T) s :=
      h_vel_dw.continuousWithinAt
    exact h_pos_cwn.prodMk h_vel_cwn
  · -- h_deriv_Ico: from h_boundary's HasDerivWithinAt-on-Icc lifted to Ici.
    -- For s ∈ Ico 0 T, Icc 0 T ∈ 𝓝[Ici s] s (since [s, s+ε) ⊆ Icc 0 T
    -- for small ε), so HasDerivWithinAt _ _ (Icc 0 T) s implies
    -- HasDerivWithinAt _ _ (Ici s) s via mono_of_mem_nhdsWithin.
    intro z s hs
    have hs_Icc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, le_of_lt hs.2⟩
    obtain ⟨h_pos_dw, h_vel_dw⟩ := h_boundary z s hs_Icc
    -- Membership: Icc 0 T ∈ nhdsWithin (Ici s) s.  Witness: take the
    -- open neighborhood `Iio T` ∋ s (since s < T from hs.2); then
    -- `Iio T ∩ Ici s = [s, T) ⊆ [0, T] = Icc 0 T`.
    have h_mem : Set.Icc (0 : ℝ) T ∈ nhdsWithin s (Set.Ici s) := by
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter]
      refine ⟨Set.Iio T, Iio_mem_nhds hs.2, ?_⟩
      intro u hu
      refine ⟨?_, ?_⟩
      · -- u ≥ 0: from u ∈ Ici s ⊆ Ici 0 (since s ≥ 0 by hs.1).
        exact le_trans hs.1 hu.2
      · -- u ≤ T: from u ∈ Iio T (so u < T).
        exact le_of_lt hu.1
    have h_pos_Ici : HasDerivWithinAt (fun s' => charX s' z) (charV s z)
                       (Set.Ici s) s :=
      h_pos_dw.mono_of_mem_nhdsWithin h_mem
    have h_vel_Ici : HasDerivWithinAt (fun s' => charV s' z)
                       (-(convolveFunctionMeasure gradW (ρ s) (charX s z)))
                       (Set.Ici s) s :=
      h_vel_dw.mono_of_mem_nhdsWithin h_mem
    -- Join componentwise into the joint Prod-valued HasDerivWithinAt.
    -- vlasovVectorField gradW ρ s (charX s z, charV s z)
    --   = (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z))).
    have h_prod : HasDerivWithinAt
        (fun s' : ℝ => (charX s' z, charV s' z))
        (charV s z, -(convolveFunctionMeasure gradW (ρ s) (charX s z)))
        (Set.Ici s) s := h_pos_Ici.prodMk h_vel_Ici
    -- Convert from componentwise to the vector-field form.
    change HasDerivWithinAt (fun s' => (charX s' z, charV s' z))
            (vlasovVectorField gradW ρ s (charX s z, charV s z)) (Set.Ici s) s
    convert h_prod using 1
    rfl

/-- **Single Picard step `VlasovMeasureCurve d T M → VlasovMeasureCurve d T M'`**.

Composes `exists_vlasov_characteristicFlow_global_smallT` +
`characteristicFlow_boundary_regularity` + `flow_distance_growth_bound_on` +
`charFlow_measurable_via_gronwall` + `PhiAsVlasovMeasureCurve` into a
single Picard step.

**Output bundle** (sigma form): the flow + growth constant + bundled
output curve + local pushforward equation on `Icc 0 T`.  Internally,
`σ.ρ = Phi charX_clamped f₀` where `charX_clamped t := charX (clampToIcc T t)`;
on `Icc 0 T` the clamp is the identity so the pushforward equation
holds with the un-clamped `charX`. -/
theorem Phi_step
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    (M_f₀ : ℝ) (hM_f₀ : ∫ z, ‖z‖ ∂f₀ ≤ M_f₀)
    {T : ℝ} {M : ℝ → ℝ} (hT : 0 ≤ T)
    (Mbar : ℝ) (hMbar_nn : 0 ≤ Mbar) (hMbar : ∀ t ∈ Set.Icc 0 T, M t ≤ Mbar)
    (hM_mono : MonotoneOn M (Set.Icc 0 T))
    (hTL_PL : LocalSmallnessPLBuffer L T)
    (ρ : VlasovMeasureCurve d T M)
    (h_int_ext : ∀ t (x : PhysSpace d),
                  Integrable (fun y => gradW (x - y)) (ρ.extend t)) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d) (C_T : ℝ),
      0 ≤ C_T ∧
      IsCharacteristicFlowOn gradW ρ.extend charX charV (Set.Ioo 0 T) Set.univ ∧
      -- **Piece A (time-local envelope) growth bound** — exposes the per-`z`
      -- bound `flow_distance_growth_bound_on_timedep` produces against the input
      -- moment envelope `M`.  Piece D integrates this (A.2) and closes it against
      -- the canonical envelope (A.3) to re-bundle `σ` into the fixed envelope
      -- space, dissolving the M-fixed-point.
      (∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
        ‖(charX t z, charV t z)‖ ≤
          gronwallBound ‖z‖ (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * M t) t) ∧
      ∃ σ : VlasovMeasureCurve d T (fun _ => C_T * (M_f₀ + 1)),
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          σ.ρ t = Measure.map (fun z : PhaseSpace d => charX t z) f₀ := by
  have hExt_prob : ∀ t, IsProbabilityMeasure (ρ.extend t) :=
    VlasovMeasureCurve.extend_isProb ρ
  have hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ.extend t) x) := by
    intro x
    have h_int_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y => gradW (x - y)) (ρ.ρ t) := by
      intro t ht
      have h_eq : ρ.extend t = ρ.ρ t := by
        unfold VlasovMeasureCurve.extend clampToIcc
        congr 1
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [← h_eq]; exact h_int_ext t x
    exact VlasovMeasureCurve.extend_convCont gradW L hL hT ρ x h_int_Icc
  have h_y_int : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ.extend t) :=
    fun t => VlasovMeasureCurve.extend_yIntegrable hT ρ t
  have hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ Mbar :=
    fun t => le_trans (VlasovMeasureCurve.extend_hasMoment hT ρ t)
      (hMbar (clampToIcc T t) (clampToIcc_mem hT t))
  obtain ⟨charX, charV, hflow_on, h_boundary⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL
      ρ.extend h_int_ext hρ_cont h_y_int Mbar hMbar_nn hM_ρ T hT hTL_PL
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    characteristicFlow_boundary_regularity gradW ρ.extend charX charV T hT
      hflow_on h_boundary
  -- Piece A (time-local envelope) per-`z` growth bound against the input
  -- envelope `M` (on `Icc`, `ρ.extend t = ρ.ρ t`, so `ρ`'s moment bound `M t`
  -- feeds the time-local Gronwall forcing).
  have hm_M : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ M t := by
    intro t ht
    have h_eq : ρ.extend t = ρ.ρ t := by
      unfold VlasovMeasureCurve.extend clampToIcc
      congr 1
      rw [min_eq_left ht.2, max_eq_right ht.1]
    rw [h_eq]; exact ρ.hasMoment t ht
  have h_growth_timedep : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤
        gronwallBound ‖z‖ (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * M t) t :=
    flow_distance_growth_bound_on_timedep gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico M hM_mono hm_M (fun t _ => h_y_int t) h_int_ext
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico Mbar hMbar_nn
      (fun t _ => hM_ρ t) (fun t _ => h_y_int t) h_int_ext
  have h_meas_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) :=
    charFlow_measurable_via_gronwall gradW L hL ρ.extend h_int_ext charX charV
      T hT h_init h_cont_Icc h_deriv_Ico
  let charX_clamped : ℝ → PhaseSpace d → PhysSpace d :=
    fun t z => charX (clampToIcc T t) z
  have h_meas_clamped : ∀ t,
      AEMeasurable (fun z : PhaseSpace d => charX_clamped t z) f₀ := by
    intro t
    have h_clamp_mem := clampToIcc_mem hT t
    have h_meas_full := h_meas_Icc (clampToIcc T t) h_clamp_mem
    exact (measurable_fst.comp h_meas_full).aemeasurable
  have h_growth_clamped : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX_clamped t z‖ ≤ C_T * (‖z‖ + 1) := by
    intro t ht z
    have h_clamp_eq : clampToIcc T t = t := by
      unfold clampToIcc
      rw [min_eq_left ht.2, max_eq_right ht.1]
    change ‖charX (clampToIcc T t) z‖ ≤ _
    rw [h_clamp_eq]
    have h_full := h_growth t ht z
    have h_proj : ‖charX t z‖ ≤ ‖(charX t z, charV t z)‖ := by
      simp [Prod.norm_def]
    linarith
  have h_int_charX_clamped : ∀ t,
      Integrable (fun z : PhaseSpace d => ‖charX_clamped t z‖) f₀ := by
    intro t
    have h_clamp_mem := clampToIcc_mem hT t
    have h_bound : ∀ z, ‖charX_clamped t z‖ ≤ C_T * (‖z‖ + 1) := by
      intro z
      change ‖charX (clampToIcc T t) z‖ ≤ _
      have h_full := h_growth (clampToIcc T t) h_clamp_mem z
      have h_proj : ‖charX (clampToIcc T t) z‖ ≤
                    ‖(charX (clampToIcc T t) z, charV (clampToIcc T t) z)‖ := by
        simp [Prod.norm_def]
      linarith
    have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
      have h1 : Integrable (fun z : PhaseSpace d => C_T * ‖z‖) f₀ :=
        h_f₀_int.const_mul C_T
      have h2 : Integrable (fun _ : PhaseSpace d => C_T) f₀ := integrable_const _
      have h_eq : (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) =
                  fun z => C_T * ‖z‖ + C_T := by funext z; ring
      rw [h_eq]; exact h1.add h2
    have h_aesm : AEStronglyMeasurable
        (fun z : PhaseSpace d => ‖charX_clamped t z‖) f₀ :=
      (h_meas_clamped t).norm.aestronglyMeasurable
    refine h_dom_int.mono' h_aesm ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact h_bound z
  have h_charX_cont_clamped : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z,
      ContinuousWithinAt (fun t => charX_clamped t z) (Set.Icc 0 T) s := by
    intro s hs z
    have h_full := (h_cont_Icc z).continuousWithinAt hs
    have h_charX_cwn : ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s :=
      h_full.fst
    have h_eq_on : ∀ t ∈ Set.Icc (0 : ℝ) T, charX_clamped t z = charX t z := by
      intro t ht
      change charX (clampToIcc T t) z = charX t z
      have h_clamp_eq : clampToIcc T t = t := by
        unfold clampToIcc
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [h_clamp_eq]
    exact h_charX_cwn.congr h_eq_on (h_eq_on s hs)
  let σ : VlasovMeasureCurve d T (fun _ => C_T * (M_f₀ + 1)) :=
    PhiAsVlasovMeasureCurve charX_clamped f₀ h_meas_clamped h_int_charX_clamped
      T hT C_T hC_T_nn h_growth_clamped h_f₀_int M_f₀ hM_f₀ h_charX_cont_clamped
  refine ⟨charX, charV, C_T, hC_T_nn, hflow_on, h_growth_timedep, σ, ?_⟩
  intro t ht
  change Phi charX_clamped f₀ t = Measure.map (fun z => charX t z) f₀
  unfold Phi
  have h_clamp_eq : clampToIcc T t = t := by
    unfold clampToIcc
    rw [min_eq_left ht.2, max_eq_right ht.1]
  congr 1
  funext z
  change charX (clampToIcc T t) z = charX t z
  rw [h_clamp_eq]

/-- **`Φ`-step landing in the fixed envelope space.**

`Phi_step` produces a flow `(charX, charV)` against `ρ.extend` and bundles its
position pushforward into the *constant* space `VlasovMeasureCurve d T (fun _ =>
C_T·(M_f₀+1))`.  The constant bound grows with each `Φ`-iteration (the moment
fixed-point pathology).  This wrapper **re-bundles the same pushforward into
the fixed envelope space** `VlasovMeasureCurve d T m`, where `m` is the
canonical Gronwall envelope of `gronwall_envelope_exists`: because `m` is
`Φ`-invariant at the moment level, `Φ` maps `space(m)` to itself, so the Picard
sequence stays in one fixed curve space — dissolving the fixed-point in `M`.

The moment re-bundling is the measure-level data-free escape:
`∫‖x‖∂(map (charX t) f₀) ≤ gronwallBound (∫z‖z‖∂f₀) (1+L) (‖gradW 0‖ + L·m t) t`
(`phi_moment_envelope_le`, fed the per-`z` growth bound `Phi_step`
exposes) `≤ m t` (envelope invariance `hm_inv`).

Output also exposes the **boundary-regularity bundle** (as
`exists_vlasov_characteristicFlow_global_smallT`) so the Picard recursion can
discharge `Phi_supW1_contraction`'s per-`z` regularity hypotheses at each step.

The envelope's anchor moment is the **phase-space** `∫z‖z‖∂f₀` (matching the
`integral_map` initial value), NOT the spatial marginal. -/
theorem Phi_step_envelope
    {d : ℕ} [NeZero d]
    (W : PhysSpace d → ℝ)
    (gradW : PhysSpace d → PhysSpace d)
    (hgradW : ∀ x, gradW x = gradient W x)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_f₀_int : Integrable (fun z : PhaseSpace d => ‖z‖) f₀)
    {T : ℝ} (hT : 0 ≤ T)
    (m : ℝ → ℝ) (hm_mono : MonotoneOn m (Set.Icc 0 T))
    (hm_nn : ∀ t ∈ Set.Icc (0 : ℝ) T, 0 ≤ m t)
    (hm_inv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      gronwallBound (∫ z, ‖z‖ ∂f₀) (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * m t) t ≤ m t)
    (hTL_PL : LocalSmallnessPLBuffer L T)
    (ρ : VlasovMeasureCurve d T m)
    (h_int_ext : ∀ t (x : PhysSpace d),
                  Integrable (fun y => gradW (x - y)) (ρ.extend t)) :
    ∃ (charX charV : ℝ → PhaseSpace d → PhysSpace d),
      IsCharacteristicFlowOn gradW ρ.extend charX charV (Set.Ioo 0 T) Set.univ ∧
      (∀ z : PhaseSpace d, ∀ t ∈ Set.Icc (0 : ℝ) T,
        HasDerivWithinAt (fun s => charX s z) (charV t z) (Set.Icc 0 T) t ∧
        HasDerivWithinAt (fun s => charV s z)
          (-(convolveFunctionMeasure gradW (ρ.extend t) (charX t z)))
          (Set.Icc 0 T) t) ∧
      ∃ σ : VlasovMeasureCurve d T m,
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          σ.ρ t = Measure.map (fun z : PhaseSpace d => charX t z) f₀ := by
  have hExt_prob : ∀ t, IsProbabilityMeasure (ρ.extend t) :=
    VlasovMeasureCurve.extend_isProb ρ
  have hρ_cont : ∀ x : PhysSpace d,
      Continuous (fun t => convolveFunctionMeasure gradW (ρ.extend t) x) := by
    intro x
    have h_int_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
        Integrable (fun y => gradW (x - y)) (ρ.ρ t) := by
      intro t ht
      have h_eq : ρ.extend t = ρ.ρ t := by
        unfold VlasovMeasureCurve.extend clampToIcc
        congr 1
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [← h_eq]; exact h_int_ext t x
    exact VlasovMeasureCurve.extend_convCont gradW L hL hT ρ x h_int_Icc
  have h_y_int : ∀ t, Integrable (fun y : PhysSpace d => ‖y‖) (ρ.extend t) :=
    fun t => VlasovMeasureCurve.extend_yIntegrable hT ρ t
  have hMbar_nn : 0 ≤ m T := hm_nn T ⟨hT, le_refl T⟩
  have hMbar : ∀ t ∈ Set.Icc (0 : ℝ) T, m t ≤ m T :=
    fun t ht => hm_mono ht ⟨hT, le_refl T⟩ ht.2
  have hM_ρ : ∀ t, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ m T :=
    fun t => le_trans (VlasovMeasureCurve.extend_hasMoment hT ρ t)
      (hMbar (clampToIcc T t) (clampToIcc_mem hT t))
  obtain ⟨charX, charV, hflow_on, h_boundary⟩ :=
    exists_vlasov_characteristicFlow_global_smallT W gradW hgradW L hL
      ρ.extend h_int_ext hρ_cont h_y_int (m T) hMbar_nn hM_ρ T hT hTL_PL
  obtain ⟨h_init, h_cont_Icc, h_deriv_Ico⟩ :=
    characteristicFlow_boundary_regularity gradW ρ.extend charX charV T hT
      hflow_on h_boundary
  have hm_M : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ.extend t) ≤ m t := by
    intro t ht
    have h_eq : ρ.extend t = ρ.ρ t := by
      unfold VlasovMeasureCurve.extend clampToIcc
      congr 1
      rw [min_eq_left ht.2, max_eq_right ht.1]
    rw [h_eq]; exact ρ.hasMoment t ht
  have h_growth_timedep : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖(charX t z, charV t z)‖ ≤
        gronwallBound ‖z‖ (1 + (L : ℝ)) (‖gradW 0‖ + (L : ℝ) * m t) t :=
    flow_distance_growth_bound_on_timedep gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico m hm_mono hm_M (fun t _ => h_y_int t) h_int_ext
  obtain ⟨C_T, hC_T_nn, h_growth⟩ :=
    flow_distance_growth_bound_on gradW L hL ρ.extend charX charV T hT
      h_init h_cont_Icc h_deriv_Ico (m T) hMbar_nn
      (fun t _ => hM_ρ t) (fun t _ => h_y_int t) h_int_ext
  have h_meas_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Measurable (fun z : PhaseSpace d => (charX t z, charV t z)) :=
    charFlow_measurable_via_gronwall gradW L hL ρ.extend h_int_ext charX charV
      T hT h_init h_cont_Icc h_deriv_Ico
  let charX_clamped : ℝ → PhaseSpace d → PhysSpace d :=
    fun t z => charX (clampToIcc T t) z
  have h_meas_clamped : ∀ t,
      AEMeasurable (fun z : PhaseSpace d => charX_clamped t z) f₀ := by
    intro t
    have h_clamp_mem := clampToIcc_mem hT t
    have h_meas_full := h_meas_Icc (clampToIcc T t) h_clamp_mem
    exact (measurable_fst.comp h_meas_full).aemeasurable
  have h_growth_clamped : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ z : PhaseSpace d,
      ‖charX_clamped t z‖ ≤ C_T * (‖z‖ + 1) := by
    intro t ht z
    have h_clamp_eq : clampToIcc T t = t := by
      unfold clampToIcc
      rw [min_eq_left ht.2, max_eq_right ht.1]
    change ‖charX (clampToIcc T t) z‖ ≤ _
    rw [h_clamp_eq]
    have h_full := h_growth t ht z
    have h_proj : ‖charX t z‖ ≤ ‖(charX t z, charV t z)‖ := by
      simp [Prod.norm_def]
    linarith
  have h_int_charX_clamped : ∀ t,
      Integrable (fun z : PhaseSpace d => ‖charX_clamped t z‖) f₀ := by
    intro t
    have h_clamp_mem := clampToIcc_mem hT t
    have h_bound : ∀ z, ‖charX_clamped t z‖ ≤ C_T * (‖z‖ + 1) := by
      intro z
      change ‖charX (clampToIcc T t) z‖ ≤ _
      have h_full := h_growth (clampToIcc T t) h_clamp_mem z
      have h_proj : ‖charX (clampToIcc T t) z‖ ≤
                    ‖(charX (clampToIcc T t) z, charV (clampToIcc T t) z)‖ := by
        simp [Prod.norm_def]
      linarith
    have h_dom_int : Integrable (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) f₀ := by
      have h1 : Integrable (fun z : PhaseSpace d => C_T * ‖z‖) f₀ :=
        h_f₀_int.const_mul C_T
      have h2 : Integrable (fun _ : PhaseSpace d => C_T) f₀ := integrable_const _
      have h_eq : (fun z : PhaseSpace d => C_T * (‖z‖ + 1)) =
                  fun z => C_T * ‖z‖ + C_T := by funext z; ring
      rw [h_eq]; exact h1.add h2
    have h_aesm : AEStronglyMeasurable
        (fun z : PhaseSpace d => ‖charX_clamped t z‖) f₀ :=
      (h_meas_clamped t).norm.aestronglyMeasurable
    refine h_dom_int.mono' h_aesm ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact h_bound z
  have h_charX_cont_clamped : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ z,
      ContinuousWithinAt (fun t => charX_clamped t z) (Set.Icc 0 T) s := by
    intro s hs z
    have h_full := (h_cont_Icc z).continuousWithinAt hs
    have h_charX_cwn : ContinuousWithinAt (fun t => charX t z) (Set.Icc 0 T) s :=
      h_full.fst
    have h_eq_on : ∀ t ∈ Set.Icc (0 : ℝ) T, charX_clamped t z = charX t z := by
      intro t ht
      change charX (clampToIcc T t) z = charX t z
      have h_clamp_eq : clampToIcc T t = t := by
        unfold clampToIcc
        rw [min_eq_left ht.2, max_eq_right ht.1]
      rw [h_clamp_eq]
    exact h_charX_cwn.congr h_eq_on (h_eq_on s hs)
  let σ_const := PhiAsVlasovMeasureCurve charX_clamped f₀ h_meas_clamped
    h_int_charX_clamped T hT C_T hC_T_nn h_growth_clamped h_f₀_int
    (∫ z, ‖z‖ ∂f₀) (le_refl _) h_charX_cont_clamped
  -- On `Icc`, the clamped pushforward equals the raw pushforward.
  have h_rho_eq : ∀ t ∈ Set.Icc (0 : ℝ) T,
      σ_const.ρ t = Measure.map (fun z : PhaseSpace d => charX t z) f₀ := by
    intro t ht
    change Phi charX_clamped f₀ t = Measure.map (fun z => charX t z) f₀
    unfold Phi
    have h_clamp_eq : clampToIcc T t = t := by
      unfold clampToIcc
      rw [min_eq_left ht.2, max_eq_right ht.1]
    congr 1
    funext z
    change charX (clampToIcc T t) z = charX t z
    rw [h_clamp_eq]
  -- Moment re-bundle (the data-free escape): A.2 integrates the per-`z`
  -- envelope growth to a moment bound, A.3's `hm_inv` closes it against `m`.
  have h_meas_charX_Icc : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX t z) f₀ :=
    fun t ht => (measurable_fst.comp (h_meas_Icc t ht)).aemeasurable
  have h_moment_m : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(σ_const.ρ t) ≤ m t := by
    intro t ht
    rw [h_rho_eq t ht]
    calc ∫ y, ‖y‖ ∂(Measure.map (fun z : PhaseSpace d => charX t z) f₀)
        ≤ gronwallBound (∫ z, ‖z‖ ∂f₀) (1 + (L : ℝ))
            (‖gradW 0‖ + (L : ℝ) * m t) t :=
          phi_moment_envelope_le L charX charV (‖gradW 0‖) T m h_growth_timedep
            f₀ h_f₀_int h_meas_charX_Icc t ht
      _ ≤ m t := hm_inv t ht
  -- Re-bundle `σ_const` (constant space) into the fixed envelope space `m`:
  -- only `hasMoment` changes; the other fields are `m`-independent.
  let σ : VlasovMeasureCurve d T m :=
    { ρ := σ_const.ρ
      isProb := σ_const.isProb
      hasMoment := h_moment_m
      yIntegrable := σ_const.yIntegrable
      hW1Cont := σ_const.hW1Cont }
  exact ⟨charX, charV, hflow_on, h_boundary, σ, h_rho_eq⟩

/-- **Pointwise Gronwall on flow difference.**

Given two characteristic flow trajectories `γ_ρ, γ_σ : ℝ → PhaseSpace d`
starting at the same initial condition `z`, driven by *different* measure
curves `ρ, σ` with `supW1On(Icc 0 T) ρ σ ≤ D`, the pointwise difference
satisfies a Gronwall-type bound:
`‖γ_ρ(t) - γ_σ(t)‖ ≤ gronwallBound 0 K (L · D) t`
where `K := max(1, L)`.

**Proof strategy** (Gronwall on the trajectory-difference function):
* Set `f(s) := γ_ρ(s) - γ_σ(s)`.  Then `f(0) = 0` (both start at `z`).
* `f'(s) = vlasovVectorField gradW ρ s (γ_ρ s) − vlasovVectorField gradW σ s (γ_σ s)`.
* Split via triangle:
  `f'(s) = [VF_ρ γ_ρ − VF_ρ γ_σ]  +  [VF_ρ γ_σ − VF_σ γ_σ]`
* First bracket bounded by `K · ‖γ_ρ - γ_σ‖ = K · ‖f s‖` via
  `vlasovVectorField_lipschitzWith`.
* Second bracket: the velocity components cancel (`VF`'s first component is
  `z.2`, identical in both); only the force components differ.  Bounded by
  `L · W₁(ρ_s, σ_s).toReal ≤ L · D` via `norm_convolveFunctionMeasure_sub_le`.
* Apply `norm_le_gronwallBound_of_norm_deriv_right_le` with `δ := 0`,
  `K := max(1, L)`, `ε := L · D`.

**Boundary regularity** identical to `charFlow_measurable_via_gronwall`:
`ContinuousOn (Icc 0 T)` + `HasDerivWithinAt` on `Ico 0 T` for each
trajectory.  The Picard construction discharges these hypotheses.

Used by the main contraction lemma to bound
`supW1On(Icc 0 T)(Phi ρ)(Phi σ)` by `K_contract(T) · supW1On(Icc 0 T) ρ σ`
where `K_contract(T) := (L/K) · (exp(K·T) - 1) → 0` as `T → 0`. -/
theorem flow_difference_gronwall_bound {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)] [∀ t, IsProbabilityMeasure (σ t)]
    (h_int_ρ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (h_int_σ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (σ t))
    (T : ℝ) (_hT : 0 ≤ T)
    (D : ℝ) (_hD_nn : 0 ≤ D)
    (h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T, wasserstein1 (ρ s) (σ s) ≠ ⊤)
    (h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, (wasserstein1 (ρ s) (σ s)).toReal ≤ D)
    (γ_ρ γ_σ : ℝ → PhaseSpace d)
    (z : PhaseSpace d)
    (h_init_ρ : γ_ρ 0 = z) (h_init_σ : γ_σ 0 = z)
    (h_cont_ρ : ContinuousOn γ_ρ (Set.Icc (0 : ℝ) T))
    (h_cont_σ : ContinuousOn γ_σ (Set.Icc (0 : ℝ) T))
    (h_deriv_ρ : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt γ_ρ (vlasovVectorField gradW ρ s (γ_ρ s)) (Set.Ici s) s)
    (h_deriv_σ : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt γ_σ (vlasovVectorField gradW σ s (γ_σ s)) (Set.Ici s) s) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖γ_ρ t - γ_σ t‖ ≤
        gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L : ℝ) * D) t := by
  -- ============================================================
  -- Setup: K = max(1, L), f(s) = γ_ρ(s) - γ_σ(s).
  -- ============================================================
  set K_NN : NNReal := max 1 L with hK_NN_def
  set K_lip : ℝ := (K_NN : ℝ) with hK_lip_def
  have hK_NN_eq : K_lip = ((max 1 L : NNReal) : ℝ) := rfl
  set f : ℝ → PhaseSpace d := fun s => γ_ρ s - γ_σ s with hf_def
  set f' : ℝ → PhaseSpace d := fun s =>
    vlasovVectorField gradW ρ s (γ_ρ s) - vlasovVectorField gradW σ s (γ_σ s)
    with hf'_def
  -- ============================================================
  -- Continuity + right-derivative of f on the relevant intervals.
  -- ============================================================
  have h_f_cont : ContinuousOn f (Set.Icc (0 : ℝ) T) := h_cont_ρ.sub h_cont_σ
  have h_f_deriv : ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt f (f' s) (Set.Ici s) s := fun s hs =>
    (h_deriv_ρ s hs).sub (h_deriv_σ s hs)
  -- ============================================================
  -- Initial: ‖f 0‖ = 0.
  -- ============================================================
  have h_f0 : ‖f 0‖ ≤ 0 := by
    change ‖γ_ρ 0 - γ_σ 0‖ ≤ 0
    rw [h_init_ρ, h_init_σ, sub_self, norm_zero]
  -- ============================================================
  -- Differential bound: ‖f'(s)‖ ≤ K_lip · ‖f(s)‖ + L · D for s ∈ Ico 0 T.
  -- ============================================================
  have h_f'_bound : ∀ s ∈ Set.Ico (0 : ℝ) T,
      ‖f' s‖ ≤ K_lip * ‖f s‖ + (L : ℝ) * D := by
    intro s hs
    -- s ∈ Icc 0 T from s ∈ Ico 0 T
    have hs_Icc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1, le_of_lt hs.2⟩
    -- ============================================================
    -- Triangle split: f'(s) = [VF_ρ γ_ρ − VF_ρ γ_σ] + [VF_ρ γ_σ − VF_σ γ_σ]
    -- ============================================================
    have h_split : f' s =
        (vlasovVectorField gradW ρ s (γ_ρ s) -
         vlasovVectorField gradW ρ s (γ_σ s)) +
        (vlasovVectorField gradW ρ s (γ_σ s) -
         vlasovVectorField gradW σ s (γ_σ s)) := by
      simp only [hf'_def]; abel
    have h_tri : ‖f' s‖ ≤
        ‖vlasovVectorField gradW ρ s (γ_ρ s) - vlasovVectorField gradW ρ s (γ_σ s)‖ +
        ‖vlasovVectorField gradW ρ s (γ_σ s) - vlasovVectorField gradW σ s (γ_σ s)‖ := by
      rw [h_split]; exact norm_add_le _ _
    -- ============================================================
    -- First bracket: ‖VF_ρ γ_ρ − VF_ρ γ_σ‖ ≤ K_lip · ‖γ_ρ - γ_σ‖.
    -- ============================================================
    have h_vf_lip := vlasovVectorField_lipschitzWith gradW L hL ρ h_int_ρ s
    have h_first : ‖vlasovVectorField gradW ρ s (γ_ρ s) -
                    vlasovVectorField gradW ρ s (γ_σ s)‖ ≤
                   K_lip * ‖γ_ρ s - γ_σ s‖ := by
      have h := h_vf_lip.dist_le_mul (γ_ρ s) (γ_σ s)
      rw [dist_eq_norm, dist_eq_norm] at h
      exact h
    -- ============================================================
    -- Second bracket: VF_ρ γ_σ − VF_σ γ_σ = (0, conv σ - conv ρ at γ_σ.1).
    -- Norm = ‖conv ρ - conv σ at γ_σ.1‖ ≤ L * W₁(ρ_s, σ_s).toReal ≤ L * D.
    -- ============================================================
    have h_VF_diff_explicit :
        vlasovVectorField gradW ρ s (γ_σ s) - vlasovVectorField gradW σ s (γ_σ s) =
        (0, convolveFunctionMeasure gradW (σ s) (γ_σ s).1 -
            convolveFunctionMeasure gradW (ρ s) (γ_σ s).1) := by
      simp only [vlasovVectorField, Prod.mk_sub_mk, sub_self, neg_sub_neg]
    have h_second_norm :
        ‖vlasovVectorField gradW ρ s (γ_σ s) - vlasovVectorField gradW σ s (γ_σ s)‖ =
        ‖convolveFunctionMeasure gradW (σ s) (γ_σ s).1 -
         convolveFunctionMeasure gradW (ρ s) (γ_σ s).1‖ := by
      rw [h_VF_diff_explicit]
      simp [Prod.norm_def]
    have h_conv_lip := norm_convolveFunctionMeasure_sub_le gradW L hL
      (σ s) (ρ s) (γ_σ s).1
      (by rw [wasserstein1_comm]; exact h_W1_fin s hs_Icc)
      (h_int_σ s _) (h_int_ρ s _)
    have h_W1_comm : (wasserstein1 (σ s) (ρ s)).toReal =
                     (wasserstein1 (ρ s) (σ s)).toReal := by
      rw [wasserstein1_comm]
    have h_second : ‖vlasovVectorField gradW ρ s (γ_σ s) -
                     vlasovVectorField gradW σ s (γ_σ s)‖ ≤ (L : ℝ) * D := by
      rw [h_second_norm]
      calc ‖convolveFunctionMeasure gradW (σ s) (γ_σ s).1 -
            convolveFunctionMeasure gradW (ρ s) (γ_σ s).1‖
          ≤ (L : ℝ) * (wasserstein1 (σ s) (ρ s)).toReal := h_conv_lip
        _ = (L : ℝ) * (wasserstein1 (ρ s) (σ s)).toReal := by rw [h_W1_comm]
        _ ≤ (L : ℝ) * D := by
            apply mul_le_mul_of_nonneg_left (h_W1_bound s hs_Icc) L.coe_nonneg
    -- ============================================================
    -- Combine: ‖f'(s)‖ ≤ K_lip · ‖f(s)‖ + L · D.
    -- ============================================================
    calc ‖f' s‖
        ≤ ‖vlasovVectorField gradW ρ s (γ_ρ s) -
            vlasovVectorField gradW ρ s (γ_σ s)‖ +
          ‖vlasovVectorField gradW ρ s (γ_σ s) -
            vlasovVectorField gradW σ s (γ_σ s)‖ := h_tri
      _ ≤ K_lip * ‖γ_ρ s - γ_σ s‖ + (L : ℝ) * D := by
          linarith [h_first, h_second]
      _ = K_lip * ‖f s‖ + (L : ℝ) * D := by
          simp only [hf_def]
  -- ============================================================
  -- Apply norm_le_gronwallBound_of_norm_deriv_right_le.
  -- ============================================================
  intro t ht
  have h := norm_le_gronwallBound_of_norm_deriv_right_le
    h_f_cont h_f_deriv h_f0 h_f'_bound t ht
  -- h : ‖f t‖ ≤ gronwallBound 0 K_lip (L · D) (t - 0)
  simp only [sub_zero] at h
  exact h

/-- **W₁ pushforward bound for two arbitrary maps.**

Generalizes `wasserstein1_Phi_le_integral_diff` (which handled a single
flow at two times) to two arbitrary maps `f, g : PhaseSpace d → PhysSpace d`.
For pushforwards of the same initial measure `f₀`:
`W₁(f_# f₀, g_# f₀) ≤ ENNReal.ofReal (∫ z, ‖f z - g z‖ ∂f₀)`.

**Proof structure** parallel to `wasserstein1_Phi_le_integral_diff`: KR-
dual direct, with `integral_map` converting pushforward integrals + the
1-Lipschitz bound `|φ y - φ y'| ≤ ‖y - y'‖`.  Dominators are built as named
`have`s, and the `_map_measure` family is bridged via `.mp`/`.mpr`.

Used by `Phi_pointwise_contraction` (below) with
`f := charX_ρ t, g := charX_σ t` to bound the pushforward W₁ in terms of
the pointwise flow difference. -/
theorem wasserstein1_pushforward_pair_le_integral_norm_diff {d : ℕ}
    (f g : PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas_f : AEMeasurable f f₀) (h_meas_g : AEMeasurable g f₀)
    (h_int_f : Integrable (fun z : PhaseSpace d => ‖f z‖) f₀)
    (h_int_g : Integrable (fun z : PhaseSpace d => ‖g z‖) f₀)
    (h_diff_int : Integrable (fun z : PhaseSpace d => ‖f z - g z‖) f₀) :
    wasserstein1 (Measure.map f f₀) (Measure.map g f₀) ≤
      ENNReal.ofReal (∫ z, ‖f z - g z‖ ∂f₀) := by
  simp only [wasserstein1_eq_iSup_lipschitz]
  refine iSup_le fun φ => iSup_le fun hφ => ?_
  apply ENNReal.ofReal_le_ofReal
  have hφ_cont : Continuous φ := hφ.continuous
  have hφ_meas_νf : AEStronglyMeasurable φ (Measure.map f f₀) :=
    hφ_cont.aestronglyMeasurable
  have hφ_meas_νg : AEStronglyMeasurable φ (Measure.map g f₀) :=
    hφ_cont.aestronglyMeasurable
  have hφ_abs_bound : ∀ y : PhysSpace d, |φ y| ≤ |φ 0| + ‖y‖ := fun y => by
    have h_lip := hφ.dist_le_mul y 0
    rw [Real.dist_eq, dist_zero_right, NNReal.coe_one, one_mul] at h_lip
    calc |φ y| = |(φ y - φ 0) + φ 0| := by ring_nf
      _ ≤ |φ y - φ 0| + |φ 0| := abs_add_le _ _
      _ ≤ ‖y‖ + |φ 0| := by linarith
      _ = |φ 0| + ‖y‖ := by ring
  have h_norm_int_νf : Integrable (fun y : PhysSpace d => ‖y‖)
      (Measure.map f f₀) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      h_meas_f).mpr h_int_f
  have h_norm_int_νg : Integrable (fun y : PhysSpace d => ‖y‖)
      (Measure.map g f₀) :=
    (integrable_map_measure (Continuous.aestronglyMeasurable continuous_norm)
      h_meas_g).mpr h_int_g
  have h_dom_νf : Integrable (fun y : PhysSpace d => |φ 0| + ‖y‖)
      (Measure.map f f₀) :=
    (integrable_const _).add h_norm_int_νf
  have h_dom_νg : Integrable (fun y : PhysSpace d => |φ 0| + ‖y‖)
      (Measure.map g f₀) :=
    (integrable_const _).add h_norm_int_νg
  have hφ_int_νf : Integrable φ (Measure.map f f₀) := by
    refine Integrable.mono' h_dom_νf hφ_meas_νf ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    exact hφ_abs_bound y
  have hφ_int_νg : Integrable φ (Measure.map g f₀) := by
    refine Integrable.mono' h_dom_νg hφ_meas_νg ?_
    refine Filter.Eventually.of_forall fun y => ?_
    rw [Real.norm_eq_abs]
    exact hφ_abs_bound y
  rw [integral_map h_meas_f hφ_meas_νf, integral_map h_meas_g hφ_meas_νg]
  have hφ_comp_int_f : Integrable (fun z : PhaseSpace d => φ (f z)) f₀ :=
    (integrable_map_measure hφ_meas_νf h_meas_f).mp hφ_int_νf
  have hφ_comp_int_g : Integrable (fun z : PhaseSpace d => φ (g z)) f₀ :=
    (integrable_map_measure hφ_meas_νg h_meas_g).mp hφ_int_νg
  rw [← integral_sub hφ_comp_int_f hφ_comp_int_g]
  have h_pt : ∀ z : PhaseSpace d,
      φ (f z) - φ (g z) ≤ ‖f z - g z‖ := fun z => by
    have h_lip := hφ.dist_le_mul (f z) (g z)
    rw [Real.dist_eq, dist_eq_norm, NNReal.coe_one, one_mul] at h_lip
    linarith [abs_le.mp h_lip |>.2]
  exact integral_mono (hφ_comp_int_f.sub hφ_comp_int_g) h_diff_int h_pt

/-- **Pointwise contraction estimate at time t.**

Composes the pointwise Gronwall (`flow_difference_gronwall_bound`)
with the W₁ pair bound to get:
`(wasserstein1 (charX_ρ t # f₀) (charX_σ t # f₀)).toReal ≤ gronwallBound 0 K (L·D) t`
for `t ∈ Icc 0 T`, where `K := max(1, L)` and `D := supW1On(Icc 0 T) ρ σ`.

**Proof**: the pointwise Gronwall gives
`‖charX_ρ t z - charX_σ t z‖ ≤ gronwallBound 0 K (L·D) t`
uniformly in z.  Integrating over f₀ (a probability measure) gives the same
bound on `∫ ‖charX_ρ t z - charX_σ t z‖ ∂f₀`.  The W₁ pair bound then
transfers to the Wasserstein side.

Taking sup over `t ∈ Icc 0 T` derives the contraction
`supW1On(Phi_ρ)(Phi_σ) ≤ K_contract(T) · D` where
`K_contract(T) := (L/K)·(exp(K·T)−1) → 0` as `T → 0`. -/
theorem Phi_pointwise_contraction {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)] [∀ t, IsProbabilityMeasure (σ t)]
    (h_int_ρ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (h_int_σ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (σ t))
    (T : ℝ) (hT : 0 ≤ T)
    (D : ℝ) (hD_nn : 0 ≤ D)
    (h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T, wasserstein1 (ρ s) (σ s) ≠ ⊤)
    (h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, (wasserstein1 (ρ s) (σ s)).toReal ≤ D)
    -- Two flows (ρ-driven and σ-driven) starting at f₀-distributed initials.
    (charX_ρ charV_ρ charX_σ charV_σ : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_ρ t z) f₀)
    (h_meas_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_σ t z) f₀)
    (h_int_charX_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖charX_ρ t z‖) f₀)
    (h_int_charX_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖charX_σ t z‖) f₀)
    -- Per-z trajectories satisfy boundary regularity (the Picard construction
    -- discharges these).  Phrased per-z, but uniformly across z : PhaseSpace d.
    (h_init_ρ : ∀ z, (charX_ρ 0 z, charV_ρ 0 z) = z)
    (h_init_σ : ∀ z, (charX_σ 0 z, charV_σ 0 z) = z)
    (h_cont_ρ : ∀ z,
      ContinuousOn (fun s => (charX_ρ s z, charV_ρ s z)) (Set.Icc (0 : ℝ) T))
    (h_cont_σ : ∀ z,
      ContinuousOn (fun s => (charX_σ s z, charV_σ s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_ρ : ∀ z, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_ρ s' z, charV_ρ s' z))
        (vlasovVectorField gradW ρ s (charX_ρ s z, charV_ρ s z))
        (Set.Ici s) s)
    (h_deriv_σ : ∀ z, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_σ s' z, charV_σ s' z))
        (vlasovVectorField gradW σ s (charX_σ s z, charV_σ s z))
        (Set.Ici s) s)
    (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    (wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                  (Measure.map (fun z => charX_σ t z) f₀)).toReal ≤
      gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L : ℝ) * D) t := by
  -- ============================================================
  -- Pointwise Gronwall bound: applies for each z, uniformly.
  -- ============================================================
  set K_lip : ℝ := ((max 1 L : NNReal) : ℝ) with hK_lip_def
  set C_T : ℝ := gronwallBound 0 K_lip ((L : ℝ) * D) t with hC_T_def
  have h_pt_bound : ∀ z : PhaseSpace d,
      ‖(charX_ρ t z, charV_ρ t z) - (charX_σ t z, charV_σ t z)‖ ≤ C_T := by
    intro z
    have h := flow_difference_gronwall_bound gradW L hL ρ σ h_int_ρ h_int_σ
      T hT D hD_nn h_W1_fin h_W1_bound
      (fun s => (charX_ρ s z, charV_ρ s z))
      (fun s => (charX_σ s z, charV_σ s z))
      z (h_init_ρ z) (h_init_σ z) (h_cont_ρ z) (h_cont_σ z)
      (h_deriv_ρ z) (h_deriv_σ z) t ht
    exact h
  -- ============================================================
  -- Project to position component: ‖charX_ρ t z - charX_σ t z‖ ≤ C_T.
  -- ============================================================
  have h_proj_bound : ∀ z : PhaseSpace d,
      ‖charX_ρ t z - charX_σ t z‖ ≤ C_T := fun z => by
    have h := h_pt_bound z
    -- ‖charX_ρ - charX_σ‖ ≤ ‖(charX_ρ, charV_ρ) - (charX_σ, charV_σ)‖.
    have h_proj :
        ‖charX_ρ t z - charX_σ t z‖ ≤
        ‖((charX_ρ t z, charV_ρ t z) - (charX_σ t z, charV_σ t z) : PhaseSpace d)‖ := by
      rw [Prod.norm_def]
      simp only [Prod.fst_sub]
      exact le_max_left _ _
    linarith
  -- ============================================================
  -- C_T is non-negative (gronwallBound at 0 with δ = 0 and ε ≥ 0).
  -- ============================================================
  have hC_T_nn : 0 ≤ C_T := by
    have h_LD_nn : 0 ≤ (L : ℝ) * D := mul_nonneg L.coe_nonneg hD_nn
    have h_K_pos : 0 ≤ K_lip := by
      have h_max_le : (1 : ℝ) ≤ ((max 1 L : NNReal) : ℝ) := by
        push_cast
        exact le_max_left _ _
      linarith
    have ht_nn : 0 ≤ t := ht.1
    -- gronwallBound monotone in x from x = 0
    have := gronwallBound_mono (δ := (0 : ℝ)) (K := K_lip) (ε := (L : ℝ) * D)
      (le_refl 0) h_LD_nn h_K_pos ht_nn
    rw [gronwallBound_x0] at this
    exact this
  -- ============================================================
  -- Integrability of `‖charX_ρ t z - charX_σ t z‖` wrt f₀.
  -- ============================================================
  have h_diff_int_f₀ : Integrable (fun z : PhaseSpace d =>
      ‖charX_ρ t z - charX_σ t z‖) f₀ := by
    -- Bounded by C_T (constant), integrable on probability measure.
    refine Integrable.mono' (integrable_const C_T)
      (((h_meas_ρ t ht).sub (h_meas_σ t ht)).norm.aestronglyMeasurable) ?_
    refine Filter.Eventually.of_forall fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact h_proj_bound z
  -- ============================================================
  -- Apply the W₁ pair bound.
  -- ============================================================
  have h_W1 := wasserstein1_pushforward_pair_le_integral_norm_diff
    (fun z => charX_ρ t z) (fun z => charX_σ t z) f₀
    (h_meas_ρ t ht) (h_meas_σ t ht) (h_int_charX_ρ t ht) (h_int_charX_σ t ht) h_diff_int_f₀
  -- ============================================================
  -- ∫ z, ‖charX_ρ t z - charX_σ t z‖ ∂f₀ ≤ C_T.
  -- ============================================================
  have h_integral_bound : ∫ z, ‖charX_ρ t z - charX_σ t z‖ ∂f₀ ≤ C_T := by
    calc ∫ z, ‖charX_ρ t z - charX_σ t z‖ ∂f₀
        ≤ ∫ _, C_T ∂f₀ := integral_mono h_diff_int_f₀ (integrable_const _) h_proj_bound
      _ = C_T := by
          simp [integral_const, measureReal_def, measure_univ]
  -- ============================================================
  -- Convert ENNReal.ofReal bound to .toReal bound.
  -- ============================================================
  have h_W1_le_ofReal : (wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                                       (Measure.map (fun z => charX_σ t z) f₀)).toReal ≤
                       (ENNReal.ofReal C_T).toReal := by
    apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
    refine le_trans h_W1 ?_
    exact ENNReal.ofReal_le_ofReal h_integral_bound
  rw [ENNReal.toReal_ofReal hC_T_nn] at h_W1_le_ofReal
  exact h_W1_le_ofReal

/-- **sup-W₁ contraction estimate over `Icc 0 T`.**

Combines the pointwise contraction (`Phi_pointwise_contraction`) with
`gronwallBound`'s monotonicity in `t` to derive:
`(supW1On(Icc 0 T) Phi_ρ Phi_σ).toReal ≤ gronwallBound 0 K (L·D) T`
where `K := max(1, L)` and `D := supW1On(Icc 0 T) ρ σ` bound.

**For the Banach fixed-point**: expanding `gronwallBound`'s explicit
form `(ε/K)·(exp(K·t) − 1)`, the bound is `(L·D/K) · (exp(K·T) − 1) =
D · K_contract(T)` where `K_contract(T) := (L/K)·(exp(K·T) − 1) → 0` as
`T → 0`.  This is the contraction factor the Banach iteration exploits.

**Metric-dependence note**:
The contraction factor `K_contract(T) := (L/K)·(exp(K·T) − 1)` is
*exponential in T*.  For contraction (`K_contract < 1`), this requires
`L · (exp T - 1) < 1` when `K = 1` — exactly the
`LocalSmallnessContraction L T` predicate.  This is genuinely independent
of the per-ball Picard-Lindelöf flow's quadratic-in-`T` ball-geometry
constraint `LocalSmallnessPLBuffer L T := L·T² < 1`; the two predicates
match the two distinct sub-arguments.

Under the `Wbar` refactor (Dobrushin 1979, §5), the contraction factor
becomes `C₂(L) · T` — *linear in T*, no exponential.
`LocalSmallnessContraction` would reduce to `C₂(L) · T < 1`;
`LocalSmallnessPLBuffer` is independent of that change. -/
theorem Phi_supW1_contraction {d : ℕ}
    (gradW : PhysSpace d → PhysSpace d)
    (L : NNReal) (hL : LipschitzWith L gradW)
    (ρ σ : ℝ → Measure (PhysSpace d))
    [∀ t, IsProbabilityMeasure (ρ t)] [∀ t, IsProbabilityMeasure (σ t)]
    (h_int_ρ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (ρ t))
    (h_int_σ : ∀ t (x : PhysSpace d), Integrable (fun y => gradW (x - y)) (σ t))
    (T : ℝ) (hT : 0 ≤ T)
    (D : ℝ) (hD_nn : 0 ≤ D)
    (h_W1_fin : ∀ s ∈ Set.Icc (0 : ℝ) T, wasserstein1 (ρ s) (σ s) ≠ ⊤)
    (h_W1_bound : ∀ s ∈ Set.Icc (0 : ℝ) T, (wasserstein1 (ρ s) (σ s)).toReal ≤ D)
    (charX_ρ charV_ρ charX_σ charV_σ : ℝ → PhaseSpace d → PhysSpace d)
    (f₀ : Measure (PhaseSpace d)) [IsProbabilityMeasure f₀]
    (h_meas_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_ρ t z) f₀)
    (h_meas_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      AEMeasurable (fun z : PhaseSpace d => charX_σ t z) f₀)
    (h_int_charX_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖charX_ρ t z‖) f₀)
    (h_int_charX_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun z : PhaseSpace d => ‖charX_σ t z‖) f₀)
    -- The pushforwards have finite first moments (for W₁ finiteness).
    (h_yint_Phi_ρ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (Measure.map (fun z => charX_ρ t z) f₀))
    (h_yint_Phi_σ : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖)
        (Measure.map (fun z => charX_σ t z) f₀))
    -- Per-z trajectory regularity (the Picard construction discharges these).
    (h_init_ρ : ∀ z, (charX_ρ 0 z, charV_ρ 0 z) = z)
    (h_init_σ : ∀ z, (charX_σ 0 z, charV_σ 0 z) = z)
    (h_cont_ρ : ∀ z,
      ContinuousOn (fun s => (charX_ρ s z, charV_ρ s z)) (Set.Icc (0 : ℝ) T))
    (h_cont_σ : ∀ z,
      ContinuousOn (fun s => (charX_σ s z, charV_σ s z)) (Set.Icc (0 : ℝ) T))
    (h_deriv_ρ : ∀ z, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_ρ s' z, charV_ρ s' z))
        (vlasovVectorField gradW ρ s (charX_ρ s z, charV_ρ s z))
        (Set.Ici s) s)
    (h_deriv_σ : ∀ z, ∀ s ∈ Set.Ico (0 : ℝ) T,
      HasDerivWithinAt (fun s' => (charX_σ s' z, charV_σ s' z))
        (vlasovVectorField gradW σ s (charX_σ s z, charV_σ s z))
        (Set.Ici s) s) :
    (supW1On (Set.Icc (0 : ℝ) T)
        (fun t => Measure.map (fun z => charX_ρ t z) f₀)
        (fun t => Measure.map (fun z => charX_σ t z) f₀)).toReal ≤
      gronwallBound 0 ((max 1 L : NNReal) : ℝ) ((L : ℝ) * D) T := by
  -- ============================================================
  -- Setup.
  -- ============================================================
  set K_lip : ℝ := ((max 1 L : NNReal) : ℝ) with hK_lip_def
  set C_T : ℝ := gronwallBound 0 K_lip ((L : ℝ) * D) T with hC_T_def
  have h_LD_nn : 0 ≤ (L : ℝ) * D := mul_nonneg L.coe_nonneg hD_nn
  have h_K_pos : 0 ≤ K_lip := by
    have h_max_le : (1 : ℝ) ≤ K_lip := by exact le_max_left _ _
    linarith
  have hC_T_nn : 0 ≤ C_T := by
    have := gronwallBound_mono (δ := (0 : ℝ)) (K := K_lip) (ε := (L : ℝ) * D)
      (le_refl 0) h_LD_nn h_K_pos hT
    rw [gronwallBound_x0] at this
    exact this
  -- ============================================================
  -- Pointwise bound (from `Phi_pointwise_contraction`): for each t ∈ Icc 0 T,
  --   wasserstein1 (Phi_ρ t) (Phi_σ t) ≤ ENNReal.ofReal C_T.
  -- ============================================================
  have h_pt_bound : ∀ t ∈ Set.Icc (0 : ℝ) T,
      wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                   (Measure.map (fun z => charX_σ t z) f₀) ≤
      ENNReal.ofReal C_T := by
    intro t ht
    have hΦρ_t : IsProbabilityMeasure (Measure.map (fun z => charX_ρ t z) f₀) :=
      (MeasureTheory.Measure.isProbabilityMeasure_map_iff (h_meas_ρ t ht)).mpr inferInstance
    have hΦσ_t : IsProbabilityMeasure (Measure.map (fun z => charX_σ t z) f₀) :=
      (MeasureTheory.Measure.isProbabilityMeasure_map_iff (h_meas_σ t ht)).mpr inferInstance
    -- W₁ is finite (probability + finite first moment).
    have h_W1_t_ne_top :
        wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                     (Measure.map (fun z => charX_σ t z) f₀) ≠ ⊤ :=
      wasserstein1_ne_top_of_finite_moment _ _ (h_yint_Phi_ρ t ht) (h_yint_Phi_σ t ht)
    -- Pointwise contraction at time t.
    have h_pt := Phi_pointwise_contraction gradW L hL ρ σ h_int_ρ h_int_σ
      T hT D hD_nn h_W1_fin h_W1_bound
      charX_ρ charV_ρ charX_σ charV_σ f₀
      h_meas_ρ h_meas_σ h_int_charX_ρ h_int_charX_σ
      h_init_ρ h_init_σ h_cont_ρ h_cont_σ h_deriv_ρ h_deriv_σ t ht
    -- h_pt : (W₁ ...).toReal ≤ gronwallBound 0 K_lip (L*D) t
    -- Monotonicity of gronwallBound in t: t ≤ T ⇒ value at t ≤ value at T = C_T.
    have h_gronwall_mono : gronwallBound 0 K_lip ((L : ℝ) * D) t ≤ C_T := by
      apply gronwallBound_mono (le_refl 0) h_LD_nn h_K_pos ht.2
    have h_W1_real_le : (wasserstein1 (Measure.map (fun z => charX_ρ t z) f₀)
                                       (Measure.map (fun z => charX_σ t z) f₀)).toReal ≤ C_T :=
      le_trans h_pt h_gronwall_mono
    -- Lift from .toReal-bound to ENNReal bound (using W₁ ≠ ⊤).
    rw [← ENNReal.ofReal_toReal h_W1_t_ne_top]
    exact ENNReal.ofReal_le_ofReal h_W1_real_le
  -- ============================================================
  -- supW1On ≤ ENNReal.ofReal C_T.
  -- ============================================================
  have h_sup_bound : supW1On (Set.Icc (0 : ℝ) T)
        (fun t => Measure.map (fun z => charX_ρ t z) f₀)
        (fun t => Measure.map (fun z => charX_σ t z) f₀) ≤
      ENNReal.ofReal C_T := by
    unfold supW1On
    refine iSup_le fun t => iSup_le fun ht => h_pt_bound t ht
  -- ============================================================
  -- .toReal: (supW1On ...).toReal ≤ C_T.
  -- ============================================================
  calc (supW1On (Set.Icc (0 : ℝ) T)
          (fun t => Measure.map (fun z => charX_ρ t z) f₀)
          (fun t => Measure.map (fun z => charX_σ t z) f₀)).toReal
      ≤ (ENNReal.ofReal C_T).toReal :=
        ENNReal.toReal_mono ENNReal.ofReal_ne_top h_sup_bound
    _ = C_T := ENNReal.toReal_ofReal hC_T_nn

/-- **Picard-iteration geometric bound.**

Given a sequence with geometric contraction `supW1On (x k) (x (k+1)) ≤
ENNReal.ofReal (q^k * D₀)` for `0 ≤ q < 1`, the iterated triangle
inequality + `ENNReal.ofReal_sum_of_nonneg` + Mathlib's `geom_sum_Ico_le_of_lt_one`
gives:
`supW1On (x m) (x n) ≤ ENNReal.ofReal (D₀ * q^m / (1 - q))` for `m ≤ n`.

The argument is pure ENNReal modulo one cleanly-localized `ENNReal.ofReal`
boundary at the bridge between the structural argument (supW1On in ENNReal)
and the closed-form algebra (real geometric series).  The Finset partial sum
bound comes from `Mathlib/Algebra/Order/Field/GeomSum.lean`'s
`geom_sum_Ico_le_of_lt_one` — no case-split on `q = 0` vs `q > 0` needed,
no shifting tricks via `Finset.sum_Ico_eq_sum_range`. -/
lemma picard_iterate_geometric_bound {d : ℕ} (S : Set ℝ)
    (x : ℕ → ℝ → Measure (PhysSpace d))
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀)
    (h_contract : ∀ k, supW1On S (x k) (x (k + 1)) ≤ ENNReal.ofReal (q ^ k * D₀))
    (m n : ℕ) (hmn : m ≤ n) :
    supW1On S (x m) (x n) ≤ ENNReal.ofReal (D₀ * q^m / (1 - q)) := by
  -- Iterated triangle gives the sum bound.
  have h_tri := supW1On_iterated_triangle S x m n hmn
  have h_sum_bound :
      ∑ k ∈ Finset.Ico m n, supW1On S (x k) (x (k+1)) ≤
      ∑ k ∈ Finset.Ico m n, ENNReal.ofReal (q^k * D₀) :=
    Finset.sum_le_sum (fun k _ => h_contract k)
  -- ENNReal.ofReal of finite sum (all non-negative).
  have h_qk_D₀_nn : ∀ k ∈ Finset.Ico m n, (0 : ℝ) ≤ q^k * D₀ := fun k _ =>
    mul_nonneg (pow_nonneg hq_nn k) hD₀_nn
  have h_sum_eq :
      ∑ k ∈ Finset.Ico m n, ENNReal.ofReal (q^k * D₀) =
      ENNReal.ofReal (∑ k ∈ Finset.Ico m n, q^k * D₀) :=
    (ENNReal.ofReal_sum_of_nonneg h_qk_D₀_nn).symm
  -- Real-valued geometric bound: factor D₀ + apply geom_sum_Ico_le_of_lt_one.
  have h1mq_pos : 0 < 1 - q := by linarith
  have h_real_bound : ∑ k ∈ Finset.Ico m n, q^k * D₀ ≤ D₀ * q^m / (1 - q) := by
    have h_factor : ∑ k ∈ Finset.Ico m n, q^k * D₀ =
                    D₀ * ∑ k ∈ Finset.Ico m n, q^k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    rw [h_factor]
    calc D₀ * ∑ k ∈ Finset.Ico m n, q^k
        ≤ D₀ * (q^m / (1 - q)) :=
          mul_le_mul_of_nonneg_left (geom_sum_Ico_le_of_lt_one hq_nn hq_lt) hD₀_nn
      _ = D₀ * q^m / (1 - q) := by ring
  -- Chain everything.
  calc supW1On S (x m) (x n)
      ≤ ∑ k ∈ Finset.Ico m n, supW1On S (x k) (x (k+1)) := h_tri
    _ ≤ ∑ k ∈ Finset.Ico m n, ENNReal.ofReal (q^k * D₀) := h_sum_bound
    _ = ENNReal.ofReal (∑ k ∈ Finset.Ico m n, q^k * D₀) := h_sum_eq
    _ ≤ ENNReal.ofReal (D₀ * q^m / (1 - q)) :=
        ENNReal.ofReal_le_ofReal h_real_bound

/-- **Picard iteration is Cauchy from contraction.**

Standard Banach-fixed-point Cauchy condition derived from the geometric
contraction.

**Output form** matches `exists_wasserstein1_limit_of_cauchy`'s ENNReal-form
Cauchy hypothesis: for every `ε : ENNReal` with `0 < ε`, there is `N` such
that `supW1On (x m) (x n) < ε` for all `m, n ≥ N`.

**Proof sketch**: for the symmetric case (m > n), use `supW1On_comm`.
For `ε = ⊤`, any N works.  For `ε < ⊤`, pick N such that
`D₀ * q^N / (1-q) < ε.toReal`; combine with the geometric bound. -/
theorem picard_iterate_isCauchy_of_contraction {d : ℕ} (S : Set ℝ)
    (x : ℕ → ℝ → Measure (PhysSpace d))
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀)
    (h_contract : ∀ k, supW1On S (x k) (x (k + 1)) ≤ ENNReal.ofReal (q ^ k * D₀)) :
    ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n → supW1On S (x m) (x n) < ε := by
  intro ε hε
  have h1mq_pos : 0 < 1 - q := by linarith
  -- Helper: bound supW1On(x m, x n) in both orderings.
  have h_bound_both : ∀ m n, supW1On S (x m) (x n) ≤
      ENNReal.ofReal (D₀ * q^(min m n) / (1 - q)) := by
    intro m n
    by_cases h_order : m ≤ n
    · rw [min_eq_left h_order]
      exact picard_iterate_geometric_bound S x q hq_nn hq_lt D₀ hD₀_nn h_contract m n h_order
    · rw [supW1On_comm, min_eq_right (le_of_lt (not_le.mp h_order))]
      exact picard_iterate_geometric_bound S x q hq_nn hq_lt D₀ hD₀_nn h_contract n m
        (le_of_lt (not_le.mp h_order))
  -- Case split on ε = ⊤.
  by_cases hε_top : ε = ⊤
  · refine ⟨0, fun m n _ _ => ?_⟩
    rw [hε_top]
    exact lt_of_le_of_lt (h_bound_both m n) ENNReal.ofReal_lt_top
  · -- ε < ⊤ case.
    have hε_real_pos : 0 < ε.toReal := by
      rw [ENNReal.toReal_pos_iff]
      exact ⟨hε, lt_top_iff_ne_top.mpr hε_top⟩
    -- Tendsto of q^N → 0 gives existence of N.
    have h_pow_tendsto : Filter.Tendsto (fun n : ℕ => D₀ * q^n / (1 - q))
                          Filter.atTop (nhds 0) := by
      have h_pow : Filter.Tendsto (fun n : ℕ => q^n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one hq_nn hq_lt
      have h_factored : (fun n : ℕ => D₀ * q^n / (1 - q)) =
                       fun n : ℕ => (D₀ / (1 - q)) * q^n := by
        funext n; ring
      rw [h_factored]
      have h_zero_eq : (0 : ℝ) = (D₀ / (1 - q)) * 0 := by ring
      rw [h_zero_eq]
      exact h_pow.const_mul _
    rw [Metric.tendsto_atTop] at h_pow_tendsto
    obtain ⟨N, hN⟩ := h_pow_tendsto ε.toReal hε_real_pos
    refine ⟨N, fun m n hm hn => ?_⟩
    -- Apply the bound and the tendsto-induced threshold.
    have h_min_ge : N ≤ min m n := le_min hm hn
    have h_bound_real_lt : D₀ * q^(min m n) / (1 - q) < ε.toReal := by
      have h_dist := hN (min m n) h_min_ge
      rw [Real.dist_eq] at h_dist
      have h_val_nn : 0 ≤ D₀ * q^(min m n) / (1 - q) :=
        div_nonneg (mul_nonneg hD₀_nn (pow_nonneg hq_nn _)) (le_of_lt h1mq_pos)
      rw [abs_sub_lt_iff] at h_dist
      linarith [h_dist.1]
    calc supW1On S (x m) (x n)
        ≤ ENNReal.ofReal (D₀ * q^(min m n) / (1 - q)) := h_bound_both m n
      _ < ENNReal.ofReal ε.toReal :=
          (ENNReal.ofReal_lt_ofReal_iff hε_real_pos).mpr h_bound_real_lt
      _ = ε := ENNReal.ofReal_toReal hε_top

/-- **Pointwise W₁ bounded by `supW1On`**.

For `t ∈ S`, the per-`t` Wasserstein-1 distance is bounded by the sup-W₁
over `S`.  Routine `le_iSup` chain.  Mirror image of the `supW1On`-shape
lemmas (`supW1On_triangle`, `supW1On_self`) — the per-point extraction
from the sup. -/
lemma wasserstein1_le_supW1On {d : ℕ}
    (S : Set ℝ) (ρ σ : ℝ → Measure (PhysSpace d))
    (t : ℝ) (ht : t ∈ S) :
    wasserstein1 (ρ t) (σ t) ≤ supW1On S ρ σ := by
  unfold supW1On
  exact le_iSup_of_le t (le_iSup_of_le ht le_rfl)

/-- **Uniform-in-`t` W₁-tendsto from supW1On Cauchy + per-`t`
pointwise W₁-tendsto**.

Given a sequence `x n : ℝ → Measure (PhysSpace d)` Cauchy in `supW1On S` and
per-`t` pointwise W₁-tendsto to `y t`, the convergence is uniform in `t ∈ S`:
for every `ε : ENNReal` with `0 < ε`, there is `N` such that
`wasserstein1 (x n t) (y t) ≤ ε` for all `n ≥ N` and `t ∈ S`.

**Proof idea**: triangle through `x m t` for arbitrarily large `m`:
`wasserstein1 (x n t) (y t) ≤ wasserstein1 (x n t) (x m t) + wasserstein1 (x m t) (y t)`.
The first term `≤ supW1On (x n) (x m) < ε` by Cauchy; the second `→ 0` by
pointwise tendsto.  Apply `ENNReal.le_of_forall_pos_le_add` for the limit
passage. -/
lemma picard_iterate_limit_uniform_tendsto {d : ℕ}
    (S : Set ℝ) (x : ℕ → ℝ → Measure (PhysSpace d))
    (y : ℝ → Measure (PhysSpace d))
    (h_cauchy : ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ m n, N ≤ m → N ≤ n →
                supW1On S (x m) (x n) < ε)
    (h_pointwise : ∀ t ∈ S,
        Filter.Tendsto (fun n => wasserstein1 (x n t) (y t)) Filter.atTop (nhds 0)) :
    ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ n, N ≤ n → ∀ t ∈ S,
        wasserstein1 (x n t) (y t) ≤ ε := by
  intro ε hε
  obtain ⟨N, hN⟩ := h_cauchy ε hε
  refine ⟨N, fun n hn t ht => ?_⟩
  -- Use ENNReal.le_of_forall_pos_le_add to reduce to `≤ ε + ε'` for ε' > 0.
  apply ENNReal.le_of_forall_pos_le_add
  intro ε' hε'_pos _
  -- Pick m ≥ N such that wasserstein1 (x m t) (y t) ≤ ε'.
  have h_tend := h_pointwise t ht
  rw [ENNReal.tendsto_atTop_zero] at h_tend
  have hε'_ennreal_pos : (0 : ENNReal) < (ε' : ENNReal) := by
    exact_mod_cast hε'_pos
  obtain ⟨M, hM⟩ := h_tend (ε' : ENNReal) hε'_ennreal_pos
  let m := max N M
  have hmN : N ≤ m := le_max_left _ _
  have hmM : M ≤ m := le_max_right _ _
  -- Apply triangle inequality.
  calc wasserstein1 (x n t) (y t)
      ≤ wasserstein1 (x n t) (x m t) + wasserstein1 (x m t) (y t) :=
        wasserstein1_triangle _ _ _
    _ ≤ supW1On S (x n) (x m) + wasserstein1 (x m t) (y t) :=
        add_le_add (wasserstein1_le_supW1On S (x n) (x m) t ht) le_rfl
    _ ≤ ε + (ε' : ENNReal) := by
        gcongr
        · exact le_of_lt (hN n m hn hmN)
        · exact hM m hmM

/-- **Bundle the Picard iteration's W₁-limit as a `VlasovMeasureCurve`**.

Given a sequence of `VlasovMeasureCurve d T M` iterates with the geometric
contraction property `supW1On (x k) (x (k+1)) ≤ ofReal (q^k * D₀)`,
produce a limit `ρ_lim : VlasovMeasureCurve d T M` such that
`wasserstein1 ((x n).ρ t) (ρ_lim.ρ t) → 0` pointwise (and, by the helper
`picard_iterate_limit_uniform_tendsto`, uniformly) in `t ∈ Icc 0 T`.

**Proof strategy**:

1. Apply `picard_iterate_isCauchy_of_contraction` to get supW1On Cauchy.
2. Per-`t ∈ Icc 0 T`, the pointwise sequence `n ↦ (x n).ρ t` is Cauchy in
   W₁ (by `wasserstein1_le_supW1On` from the sup-Cauchy).
3. Invoke `exists_wasserstein1_limit_of_cauchy` per-`t` to obtain the
   pointwise limit `ρ_lim t` (with probability, integrability, moment bound,
   W₁-tendsto, all from the strengthened placeholder).
4. Extend `ρ_lim` to all of `ℝ` by `(x 0).ρ` outside `Icc 0 T` (so the
   `isProb` field — universal in `t` — holds).
5. Verify the four `VlasovMeasureCurve` fields:
   * `isProb`: from the placeholder (inside `Icc 0 T`) + `(x 0).isProb`
     (outside).
   * `hasMoment`: from the placeholder's strengthened moment-preservation
     conjunct (`∫‖y‖ ∂μ ≤ M`).
   * `yIntegrable`: from the placeholder.
   * `hW1Cont`: ε/3 triangle through `x N`, using
     `picard_iterate_limit_uniform_tendsto` for the uniform tendsto +
     `(x N).hW1Cont` for the middle term. -/
theorem picard_iterate_exists_limit {d : ℕ} [NeZero d]
    {T : ℝ} {M : ℝ → ℝ}
    (x : ℕ → VlasovMeasureCurve d T M)
    (q : ℝ) (hq_nn : 0 ≤ q) (hq_lt : q < 1)
    (D₀ : ℝ) (hD₀_nn : 0 ≤ D₀)
    (h_contract : ∀ k, supW1On (Set.Icc 0 T) (x k).ρ (x (k + 1)).ρ ≤
                       ENNReal.ofReal (q ^ k * D₀)) :
    ∃ ρ_lim : VlasovMeasureCurve d T M,
      ∀ t ∈ Set.Icc (0 : ℝ) T,
        Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) (ρ_lim.ρ t))
          Filter.atTop (nhds 0) := by
  -- Step 1: supW1On-Cauchy from the contraction.
  have h_cauchy := picard_iterate_isCauchy_of_contraction
    (Set.Icc (0 : ℝ) T) (fun n => (x n).ρ) q hq_nn hq_lt D₀ hD₀_nn h_contract
  -- Step 2: per-t Cauchy from the supW1On bound.
  have h_per_t_cauchy : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ ε : ENNReal, 0 < ε →
      ∃ N, ∀ m n, N ≤ m → N ≤ n →
        wasserstein1 ((x m).ρ t) ((x n).ρ t) < ε := by
    intro t ht ε hε
    obtain ⟨N, hN⟩ := h_cauchy ε hε
    refine ⟨N, fun m n hm hn => ?_⟩
    exact lt_of_le_of_lt (wasserstein1_le_supW1On _ _ _ t ht) (hN m n hm hn)
  -- Step 3: per-t Classical.choose to extract the limit measure.
  have h_per_t : ∀ t ∈ Set.Icc (0 : ℝ) T, ∃ μ : Measure (PhysSpace d),
      IsProbabilityMeasure μ ∧
      Integrable (fun y : PhysSpace d => ‖y‖) μ ∧
      ∫ y, ‖y‖ ∂μ ≤ M t ∧
      Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) μ) Filter.atTop (nhds 0) := by
    intro t ht
    have : ∀ n, IsProbabilityMeasure ((x n).ρ t) := fun n => (x n).isProb t
    exact exists_wasserstein1_limit_of_cauchy (fun n => (x n).ρ t) (M t)
      (fun n => (x n).hasMoment t ht) (fun n => (x n).yIntegrable t ht)
      (h_per_t_cauchy t ht)
  -- Step 4: define ρ_lim via dependent choice on whether t ∈ Icc 0 T.
  let ρ_lim : ℝ → Measure (PhysSpace d) := fun t =>
    if ht : t ∈ Set.Icc (0 : ℝ) T then Classical.choose (h_per_t t ht)
    else (x 0).ρ t
  -- Helper accessor on Icc.
  have hρ_spec : ∀ t (ht : t ∈ Set.Icc (0 : ℝ) T),
      ρ_lim t = Classical.choose (h_per_t t ht) := by
    intro t ht
    simp only [ρ_lim, dite_eq_left ht]
  -- Step 5: verify the four VlasovMeasureCurve fields.
  -- isProb: universal in t.
  have h_isProb : ∀ t, IsProbabilityMeasure (ρ_lim t) := by
    intro t
    by_cases ht : t ∈ Set.Icc (0 : ℝ) T
    · rw [hρ_spec t ht]
      exact (Classical.choose_spec (h_per_t t ht)).1
    · simp only [ρ_lim, dite_eq_right ht]
      exact (x 0).isProb t
  -- hasMoment: from the placeholder's strengthened conclusion.
  have h_hasMoment : ∀ t ∈ Set.Icc (0 : ℝ) T, ∫ y, ‖y‖ ∂(ρ_lim t) ≤ M t := by
    intro t ht
    rw [hρ_spec t ht]
    exact (Classical.choose_spec (h_per_t t ht)).2.2.1
  -- yIntegrable: from the placeholder.
  have h_yIntegrable : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Integrable (fun y : PhysSpace d => ‖y‖) (ρ_lim t) := by
    intro t ht
    rw [hρ_spec t ht]
    exact (Classical.choose_spec (h_per_t t ht)).2.1
  -- Pointwise tendsto on Icc 0 T (also part of the conclusion).
  have h_tendsto : ∀ t ∈ Set.Icc (0 : ℝ) T,
      Filter.Tendsto (fun n => wasserstein1 ((x n).ρ t) (ρ_lim t))
        Filter.atTop (nhds 0) := by
    intro t ht
    have h_spec := (Classical.choose_spec (h_per_t t ht)).2.2.2
    rw [hρ_spec t ht]
    exact h_spec
  -- Uniform tendsto from the helper.
  have h_uniform := picard_iterate_limit_uniform_tendsto
    (Set.Icc (0 : ℝ) T) (fun n => (x n).ρ) ρ_lim h_cauchy h_tendsto
  -- hW1Cont: ε/3 argument through x N.
  have h_hW1Cont : ∀ s ∈ Set.Icc (0 : ℝ) T,
      ContinuousWithinAt (fun t => (wasserstein1 (ρ_lim s) (ρ_lim t)).toReal)
                         (Set.Icc 0 T) s := by
    intro s hs
    rw [Metric.continuousWithinAt_iff]
    intro ε hε
    -- Self-distance at t = s is 0.
    have h_self : (wasserstein1 (ρ_lim s) (ρ_lim s)).toReal = 0 := by
      rw [wasserstein1_self]; rfl
    -- Pick N via uniform tendsto for tolerance ENNReal.ofReal (ε/3).
    have hε3 : 0 < ε / 3 := by linarith
    have hε3_nn : 0 < ENNReal.ofReal (ε / 3) := by
      exact_mod_cast ENNReal.ofReal_pos.mpr hε3
    obtain ⟨N, hN_uniform⟩ := h_uniform (ENNReal.ofReal (ε / 3)) hε3_nn
    -- Use (x N).hW1Cont for the middle term.
    have hN_cont := (x N).hW1Cont s hs
    rw [Metric.continuousWithinAt_iff] at hN_cont
    have h_self_N : (wasserstein1 ((x N).ρ s) ((x N).ρ s)).toReal = 0 := by
      rw [wasserstein1_self]; rfl
    obtain ⟨δ, hδ_pos, hδ_bound⟩ := hN_cont (ε / 3) hε3
    refine ⟨δ, hδ_pos, fun t ht hdist => ?_⟩
    -- Triangle bound in ENNReal then toReal.
    have h_W1_first : wasserstein1 (ρ_lim s) ((x N).ρ s) ≤ ENNReal.ofReal (ε / 3) := by
      rw [wasserstein1_comm]
      exact hN_uniform N le_rfl s hs
    have h_W1_third : wasserstein1 ((x N).ρ t) (ρ_lim t) ≤ ENNReal.ofReal (ε / 3) :=
      hN_uniform N le_rfl t ht
    -- Finiteness of the limit's W₁.
    have hPs_inf : IsProbabilityMeasure (ρ_lim s) := h_isProb s
    have hPt_inf : IsProbabilityMeasure (ρ_lim t) := h_isProb t
    have h_finite : wasserstein1 (ρ_lim s) (ρ_lim t) ≠ ⊤ :=
      wasserstein1_ne_top_of_finite_moment _ _
        (h_yIntegrable s hs) (h_yIntegrable t ht)
    -- Triangle.
    have h_tri : wasserstein1 (ρ_lim s) (ρ_lim t) ≤
        wasserstein1 (ρ_lim s) ((x N).ρ s) + wasserstein1 ((x N).ρ s) ((x N).ρ t) +
          wasserstein1 ((x N).ρ t) (ρ_lim t) := by
      calc wasserstein1 (ρ_lim s) (ρ_lim t)
          ≤ wasserstein1 (ρ_lim s) ((x N).ρ t) + wasserstein1 ((x N).ρ t) (ρ_lim t) :=
            wasserstein1_triangle _ _ _
        _ ≤ (wasserstein1 (ρ_lim s) ((x N).ρ s) + wasserstein1 ((x N).ρ s) ((x N).ρ t))
              + wasserstein1 ((x N).ρ t) (ρ_lim t) :=
            add_le_add (wasserstein1_triangle _ _ _) le_rfl
    -- Bound the middle term via hδ_bound.
    have h_mid_lt : (wasserstein1 ((x N).ρ s) ((x N).ρ t)).toReal < ε / 3 := by
      have hδb := hδ_bound ht hdist
      rw [h_self_N, Real.dist_eq, sub_zero] at hδb
      have h_nn : 0 ≤ (wasserstein1 ((x N).ρ s) ((x N).ρ t)).toReal :=
        ENNReal.toReal_nonneg
      rwa [abs_of_nonneg h_nn] at hδb
    -- Convert toReal and bound by ε/3 + ε/3 + ε/3 = ε.
    have h_W1_first_ne_top : wasserstein1 (ρ_lim s) ((x N).ρ s) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_W1_first
    have h_W1_third_ne_top : wasserstein1 ((x N).ρ t) (ρ_lim t) ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top h_W1_third
    have hPNs : IsProbabilityMeasure ((x N).ρ s) := (x N).isProb s
    have hPNt : IsProbabilityMeasure ((x N).ρ t) := (x N).isProb t
    have h_mid_ne_top : wasserstein1 ((x N).ρ s) ((x N).ρ t) ≠ ⊤ :=
      wasserstein1_ne_top_of_finite_moment _ _
        ((x N).yIntegrable s hs) ((x N).yIntegrable t ht)
    have h_W1_first_real : (wasserstein1 (ρ_lim s) ((x N).ρ s)).toReal ≤ ε / 3 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_W1_first
      rwa [ENNReal.toReal_ofReal hε3.le] at this
    have h_W1_third_real : (wasserstein1 ((x N).ρ t) (ρ_lim t)).toReal ≤ ε / 3 := by
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h_W1_third
      rwa [ENNReal.toReal_ofReal hε3.le] at this
    -- Apply ENNReal.toReal to the triangle.
    have h_tri_real : (wasserstein1 (ρ_lim s) (ρ_lim t)).toReal ≤
        (wasserstein1 (ρ_lim s) ((x N).ρ s)).toReal +
          (wasserstein1 ((x N).ρ s) ((x N).ρ t)).toReal +
          (wasserstein1 ((x N).ρ t) (ρ_lim t)).toReal := by
      have h_add_ne_top : wasserstein1 (ρ_lim s) ((x N).ρ s) +
                          wasserstein1 ((x N).ρ s) ((x N).ρ t) +
                          wasserstein1 ((x N).ρ t) (ρ_lim t) ≠ ⊤ := by
        simp [h_W1_first_ne_top, h_mid_ne_top, h_W1_third_ne_top]
      have := ENNReal.toReal_mono h_add_ne_top h_tri
      rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨h_W1_first_ne_top, h_mid_ne_top⟩)
            h_W1_third_ne_top,
          ENNReal.toReal_add h_W1_first_ne_top h_mid_ne_top] at this
      exact this
    rw [Real.dist_eq, h_self, sub_zero,
        abs_of_nonneg ENNReal.toReal_nonneg]
    linarith [h_tri_real, h_mid_lt, h_W1_first_real, h_W1_third_real]
  -- Bundle.
  refine ⟨{ρ := ρ_lim, isProb := h_isProb, hasMoment := h_hasMoment,
           yIntegrable := h_yIntegrable, hW1Cont := h_hW1Cont}, ?_⟩
  intro t ht
  exact h_tendsto t ht

end Vlasov
