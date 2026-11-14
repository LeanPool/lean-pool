/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.MarkovProcess.MarkovProcess.Killed.GluingC0
public import LeanPool.MarkovProcess.MarkovProcess.Trajectory.PenalizationDomination

/-!
# ProcessInterface

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Interface from a cubic supremum resolvent to a whole-space process

This file records the exact abstract interface used after the analytic cubic
supremum has been identified with a family of transported local resolvents.
Continuity at infinity, dense range, conservativity, and the analytic
penalized-resolvent properties remain explicit inputs.
-/

open MeasureTheory Set
open scoped ENNReal ZeroAtInfty

noncomputable section

namespace DivergenceFormProcess.Form

open MarkovProcess MarkovProcess.Semigroup

variable {alpha : Type*} [MetricSpace alpha] [LocallyCompactSpace alpha]
  [SecondCountableTopology alpha] [MeasurableSpace alpha] [BorelSpace alpha]
  {X : ℕ → Type*} [∀ m, MetricSpace (X m)] [∀ m, LocallyCompactSpace (X m)]
  [∀ m, SecondCountableTopology (X m)] [∀ m, MeasurableSpace (X m)]
  [∀ m, BorelSpace (X m)]

/-- The analytic obligations on a real penalized resolvent family used by
the killed-resolvent comparison theorem. -/
structure PenalizedResolventFamilyAssumptions
    (P : SubMarkovKernelSemigroup alpha) (q : alpha → ℝ) (C : ℝ)
    (Y : ℝ → (alpha → ℝ) → alpha → ℝ) : Prop where
  measurable : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
    (∃ D, ∀ x, |f x| ≤ D) → Measurable (Y lam f)
  bounded : ∀ {lam : ℝ}, 0 < lam → ∀ {f : alpha → ℝ}, Measurable f →
    (∃ D, ∀ x, |f x| ≤ D) → ∃ D, ∀ x, |Y lam f x| ≤ D
  resolvent : ∀ {mu lam : ℝ}, 0 < mu → 0 < lam → ∀ {f : alpha → ℝ},
    Measurable f → (∃ D, ∀ x, |f x| ≤ D) →
    Y mu f = Y lam f + (lam - mu) • Y lam (Y mu f)
  perturbation : ∀ {lam : ℝ}, C < lam → ∀ {f : alpha → ℝ}, Measurable f →
    (∃ D, ∀ x, |f x| ≤ D) →
    Y lam f = P.kernelResolventReal lam f -
      P.kernelResolventReal lam (fun y ↦ q y * Y lam f y)

variable [CompleteSpace alpha] [Nonempty alpha]

/-- A family satisfying the explicit analytic interface dominates the killed
resolvent on every open set where its potential vanishes. -/
theorem killedResolvent_le_of_penalizedResolventFamily
    (P : SubMarkovKernelSemigroup alpha) (hP : P.IsConservative)
    (hFeller : P.IsFellerKernelSemigroup) (hK : P.KolmogorovRegular hP)
    {U : Set alpha} (hU : IsOpen U) {q : alpha → ℝ} (hq : Measurable q)
    (hqU : ∀ y ∈ U, q y = 0) {C : ℝ} (hq0 : ∀ y, 0 ≤ q y)
    (hqC : ∀ y, q y ≤ C) (Y : ℝ → (alpha → ℝ) → alpha → ℝ)
    (hY : PenalizedResolventFamilyAssumptions P q C Y)
    {f : alpha → ℝ} (hf : Measurable f) (hf0 : ∀ y, 0 ≤ f y)
    {D : ℝ} (hfD : ∀ y, |f y| ≤ D) {lam : ℝ} (hlam : 0 < lam) (x : alpha) :
    hP.killedResolvent P U hU lam (fun y ↦ ENNReal.ofReal (f y)) x ≤
      ENNReal.ofReal (Y lam f x) :=
  hFeller.killedResolvent_le_of_perturbed_resolventFamily P hP hK hU hq hqU
    hq0 hqC Y hY.measurable hY.bounded hY.resolvent hY.perturbation
    hf hf0 hfD hlam x

end DivergenceFormProcess.Form
