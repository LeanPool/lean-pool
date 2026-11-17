/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Brownian.Existence
public import LeanPool.KLS.LevyStochCalc.Brownian.Martingale
public import LeanPool.KLS.LevyStochCalc.Probability.Transport

/-!
# d-dimensional Brownian motion

A `d`-dimensional Brownian motion is a `Fin d`-tuple of independent 1-D
Brownian motions on the same probability space. Constructed via
`Probability.Independence.InfinitePi`.

## References

* Karatzas–Shreve, *Brownian Motion and Stochastic Calculus*, 1991, §2.1.
* User's dissertation, ch02 §"Probability-space prerequisites", line 13
  (defines `d`-dim standard Brownian motion).

## Contents

* `MultidimBrownianMotion` — the structure; `components_independent` is
  stated with `iIndepFun`, and `joint_continuous_paths` makes the almost-sure
  continuity of the vector-valued path explicit.
* `MultidimBrownianMotion.exists` — existence, via `Measure.pi` (finite
  product of probability spaces) and the independence of coordinate
  evaluations on a product measure; each coordinate is a 1-D Brownian motion
  lifted along the corresponding projection.
* `MultidimBrownianMotion.joint_increment_gaussian_diagonal` — each
  coordinate increment is Gaussian and the coordinate increments are
  independent.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Brownian.Multidim

universe u

section Definition
variable {Ω : Type u} [MeasurableSpace Ω]

/-- A `d`-dimensional Brownian motion: a `Fin d`-tuple of independent
1-dimensional Brownian motions on the same probability space. -/
structure MultidimBrownianMotion (P : Measure Ω) [IsProbabilityMeasure P]
    (d : ℕ) where
  /-- The component-wise Brownian motions. -/
  W : Fin d → LevyStochCalc.Brownian.BrownianMotion P
  /-- The components are mutually independent — each component, viewed as a
  random variable into the path space `ℝ → ℝ` (with the product measurable
  structure), is jointly independent across `i : Fin d`. -/
  components_independent :
    ProbabilityTheory.iIndepFun
      (fun (i : Fin d) (ω : Ω) (t : ℝ) => (W i).W t ω) P
  /-- The joint d-dim
  path `t ↦ (W i ω t)_{i ∈ Fin d}` is continuous a.s. P. Follows from
  the component-wise `continuous_paths` + the finite-intersection-of-
  a.s.-sets being a.s., plus `continuous_pi_iff`: a `Fin d → ℝ`-valued
  map is continuous iff each component is. Previously this was implicit
  (a downstream caller had to derive it from `(W i).continuous_paths`
  for each i); now made explicit per Karatzas-Shreve §2.5's definition
  of multidim BM as "vector-valued process with continuous paths". -/
  joint_continuous_paths :
    ∀ᵐ ω ∂P, Continuous (fun (t : ℝ) (i : Fin d) => (W i).W t ω)

end Definition

section MeasurePreserving
variable {Ω : Type u} [MeasurableSpace Ω]

/-- Lift a 1-dimensional Brownian motion `W₀` on `(Ω₀, P₀)` to a 1-D BM on the
product space `(Fin d → Ω₀, Measure.pi)` along the `i`-th coordinate. -/
private noncomputable def project_BM
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]
    (W₀ : LevyStochCalc.Brownian.BrownianMotion P₀)
    (d : ℕ) (i : Fin d) :
    @LevyStochCalc.Brownian.BrownianMotion (Fin d → Ω₀) MeasurableSpace.pi
      (MeasureTheory.Measure.pi (fun _ => P₀))
      (by infer_instance) where
  W := fun t (ω : Fin d → Ω₀) => W₀.W t (ω i)
  measurable_eval := fun t =>
    (W₀.measurable_eval t).comp (measurable_pi_apply i)
  joint_measurable := by
    -- Joint measurability inherits from 1D BM's joint measurability via
    -- the measurable evaluation map at coordinate i.
    have h₀ := W₀.joint_measurable
    -- Function.uncurry (fun t ω => W₀.W t (ω i)) = (fun p => W₀.W p.1 (p.2 i))
    -- = h₀ ∘ (fun p => (p.1, p.2 i))
    have h_eval_meas : Measurable (fun (p : ℝ × (Fin d → Ω₀)) => (p.1, p.2 i)) := by
      refine Measurable.prodMk (measurable_fst) ?_
      exact (measurable_pi_apply i).comp measurable_snd
    exact h₀.comp h_eval_meas
  initial_zero := by
    -- W₀.initial_zero : ∀ᵐ ω₀ ∂P₀, W₀.W 0 ω₀ = 0; lift via
    --   measure-preserving eval i.
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    exact mp.quasiMeasurePreserving.ae W₀.initial_zero
  increment_gaussian := by
    intro s t hs hst
    -- Pushforward through eval_i preserves the Gaussian increment law.
    have h_eval : (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)).map
        (Function.eval i) = P₀ :=
      (MeasureTheory.measurePreserving_eval (fun _ : Fin d => P₀) i).map_eq
    have h_inc := W₀.increment_gaussian hs hst
    rw [show (fun ω : Fin d → Ω₀ => W₀.W t (ω i) - W₀.W s (ω i))
        = (W₀.W t - W₀.W s) ∘ Function.eval i from rfl,
      ← MeasureTheory.Measure.map_map
        ((W₀.measurable_eval t).sub (W₀.measurable_eval s))
        (measurable_pi_apply i),
      h_eval]
    exact h_inc
  continuous_paths := by
    -- W₀.continuous_paths lifts via measure-preserving eval i.
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    exact mp.quasiMeasurePreserving.ae W₀.continuous_paths
  negative_zero := by
    -- W₀.negative_zero lifts via measure-preserving eval i.
    intro s hs
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    exact mp.quasiMeasurePreserving.ae (W₀.negative_zero s hs)
  joint_increment_independent := by
    -- W₀.joint_increment_independent + `indep_comap_of_measurePreserving`.
    intro s t hs hst
    have mp : MeasureTheory.MeasurePreserving (Function.eval i)
        (MeasureTheory.Measure.pi (fun _ : Fin d => P₀)) P₀ :=
      MeasureTheory.measurePreserving_eval (fun _ => P₀) i
    have h_inc_comap :
        MeasurableSpace.comap
          (fun (ω : Fin d → Ω₀) => W₀.W t (ω i) - W₀.W s (ω i)) inferInstance
        = (MeasurableSpace.comap (fun ω => W₀.W t ω - W₀.W s ω) inferInstance).comap
            (Function.eval i) := by
      rw [MeasurableSpace.comap_comp]
      rfl
    have h_past_comap :
        (⨆ j ∈ Set.Iic s, MeasurableSpace.comap
          (fun (ω : Fin d → Ω₀) => W₀.W j (ω i)) inferInstance)
        = (⨆ j ∈ Set.Iic s, MeasurableSpace.comap (W₀.W j) inferInstance).comap
            (Function.eval i) := by
      rw [MeasurableSpace.comap_iSup]
      refine iSup_congr (fun j => ?_)
      rw [MeasurableSpace.comap_iSup]
      refine iSup_congr (fun _ => ?_)
      rw [MeasurableSpace.comap_comp]
      rfl
    rw [h_past_comap, h_inc_comap]
    apply Probability.indep_comap_of_measurePreserving mp
    · -- past σ-algebra ≤ ambient
      refine iSup₂_le ?_
      intro j _ u hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact (W₀.measurable_eval j) hv
    · -- increment σ-algebra ≤ ambient
      intro u hu
      obtain ⟨v, hv, rfl⟩ := hu
      exact ((W₀.measurable_eval t).sub (W₀.measurable_eval s)) hv
    · exact W₀.joint_increment_independent hs hst

end MeasurePreserving

section Existence
variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Existence of d-dimensional Brownian motion.** For any `d ≥ 0`, there
exists a probability space carrying a `d`-dimensional Brownian motion.

Proof: take `d` independent copies of the construction from
`LevyStochCalc.Brownian.BrownianMotion.exists`, joined via the product
probability space. -/
theorem MultidimBrownianMotion.exists (d : ℕ) :
    ∃ (Ω : Type u) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (MultidimBrownianMotion P d) := by
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, ⟨W₀⟩⟩ :=
    LevyStochCalc.Brownian.BrownianMotion.exists
  refine ⟨Fin d → Ω₀, MeasurableSpace.pi,
    MeasureTheory.Measure.pi (fun _ => P₀), inferInstance, ?_⟩
  refine ⟨{
    W := fun i => project_BM W₀ d i
    components_independent := ?_
    joint_continuous_paths := ?_
  }⟩
  pick_goal 2
  · -- joint continuity from per-component continuity (a.s. over the product
    -- measure) via `continuous_pi_iff`: a `Fin d → ℝ`-valued function of `t`
    -- is continuous iff each projection `(fun t => f t i)` is.  Each
    -- `(project_BM W₀ d i).continuous_paths` is already an a.s. statement, and
    -- the conjunction over the finite set `Fin d` remains a.s.
    have h_each : ∀ i : Fin d, ∀ᵐ ω ∂(MeasureTheory.Measure.pi (fun _ : Fin d => P₀)),
        Continuous (fun (t : ℝ) => (project_BM W₀ d i).W t ω) :=
      fun i => (project_BM W₀ d i).continuous_paths
    have h_all : ∀ᵐ ω ∂(MeasureTheory.Measure.pi (fun _ : Fin d => P₀)),
        ∀ i : Fin d, Continuous (fun (t : ℝ) => (project_BM W₀ d i).W t ω) :=
      MeasureTheory.ae_all_iff.mpr h_each
    filter_upwards [h_all] with ω hω
    exact continuous_pi (fun i => hω i)
  -- Components are independent: use ProbabilityTheory.iIndepFun_pi
  -- with X_i = (fun ω : Ω₀ => fun t => W₀.W t ω) for each i.
  have h_meas_W₀ : ∀ _ : Fin d,
      AEMeasurable (fun ω₀ : Ω₀ => fun t : ℝ => W₀.W t ω₀) P₀ := by
    intro _
    -- Function into ℝ → ℝ is measurable iff each evaluation is measurable.
    refine (measurable_pi_iff.mpr ?_).aemeasurable
    intro t
    exact W₀.measurable_eval t
  have := ProbabilityTheory.iIndepFun_pi
    (X := fun _ : Fin d => fun ω₀ : Ω₀ => fun t : ℝ => W₀.W t ω₀)
    (μ := fun _ : Fin d => P₀) h_meas_W₀
  convert this using 1
  rfl

/-- **Joint increment Gaussianity with diagonal covariance.**

For a multidim Brownian motion `W`, the joint vector of component increments
`(ω ↦ fun i => (W i).W t ω − (W i).W s ω) : Ω → (Fin d → ℝ)` has joint
distribution that satisfies BOTH:

* per-component: each scalar increment `(W i).W t − (W i).W s` has law
  `gaussianReal 0 (t − s)`;
* mutual independence across `i ∈ Fin d`.

This is the multivariate-Gaussian-with-diagonal-covariance `(t − s) · I_d`
in spelled-out form (per Karatzas-Shreve §2.5 / Le Gall Def 2.12). -/
theorem MultidimBrownianMotion.joint_increment_gaussian_diagonal
    {Ω : Type u} [MeasurableSpace Ω]
    {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
    {d : ℕ} (W : MultidimBrownianMotion P d)
    {s t : ℝ} (hs : 0 ≤ s) (hst : s < t) :
    -- Per-component Gaussian law of each increment:
    (∀ i : Fin d,
      P.map (fun ω => (W.W i).W t ω - (W.W i).W s ω)
        = ProbabilityTheory.gaussianReal 0 ⟨t - s, by linarith⟩) ∧
    -- Joint independence of the increments across i:
    ProbabilityTheory.iIndepFun
      (fun (i : Fin d) (ω : Ω) => (W.W i).W t ω - (W.W i).W s ω) P := by
  refine ⟨fun i => (W.W i).increment_gaussian hs hst, ?_⟩
  -- Apply iIndepFun.comp to components_independent with `g i := fun path => path t - path s`.
  -- Each `g i` is measurable (eval_t and eval_s are measurable on ℝ → ℝ,
  --   and sub is measurable).
  have h_g_meas : ∀ _ : Fin d,
      Measurable (fun (path : ℝ → ℝ) => path t - path s) := by
    intro _
    exact (measurable_pi_apply t).sub (measurable_pi_apply s)
  exact W.components_independent.comp
    (fun (_ : Fin d) (path : ℝ → ℝ) => path t - path s) h_g_meas

end Existence

end LevyStochCalc.Brownian.Multidim
