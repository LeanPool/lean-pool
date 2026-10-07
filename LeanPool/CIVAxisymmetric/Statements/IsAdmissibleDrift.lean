/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Ambient.Basis
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Is Admissible Drift

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory
open scoped NNReal
open CKN


noncomputable section

namespace CIV

/-- The drift class `eq:aniso:comparison:drift`: `B` measurable with measurable divergence
`div B`, and for every compact `J ⊆ I` one constant `Λ` such that for a.e. `τ ∈ J` the slice
`B(·, τ)` is bounded and Lipschitz with constant `Λ`, and `divB(·, τ)` is bounded by `Λ` and is
the weak divergence of `B(·, τ)`. -/
@[expose] def IsAdmissibleDrift (m : ℕ) (I : Set ℝ) (B : Vec m × ℝ → Vec m) (divB : Vec m × ℝ → ℝ) :
    Prop :=
  Measurable B ∧ Measurable divB ∧
    ∀ J : Set ℝ, IsCompact J → J ⊆ I → ∃ Λ : NNReal,
      ∀ᵐ τ ∂(volume.restrict J),
        (∀ x, ‖B (x, τ)‖ ≤ Λ) ∧ LipschitzWith Λ (fun x => B (x, τ)) ∧
        (∀ x, |divB (x, τ)| ≤ Λ) ∧
        ∀ ψ : Vec m → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          ∫ x, divB (x, τ) * ψ x = -∫ x, ∑ i, B (x, τ) i * fderiv ℝ ψ x (basisVec i)

end CIV
