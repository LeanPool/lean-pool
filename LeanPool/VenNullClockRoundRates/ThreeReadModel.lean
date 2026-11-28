/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: AbPh project (AI-generated Lean proofs)
-/

-- Modified for Lean Pool: adapted the module name and imports.

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The split-read model on an angular probability space. The projections `A,B`
are the two signed axis cosines. `AxisProjectionLaw` records the usual one-dimensional
even projection moments of a uniformly distributed point on the unit two-sphere:
the squared length of `u n + v m` is `u² + 2 u v c + v²`, with `c = n · m`.
These unweighted marginal moments are inputs, not measurements of the contrast. -/
@[expose] public section
noncomputable section
open MeasureTheory
namespace VenSplit
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Quartic energy in the scalar coordinate along one control axis. -/
def energy (a : ℝ) : ℝ := (1 - a^2)^2

/-- Pointwise weighted exponential response at the two calibrated strengths. -/
def ray (A B w : Ω → ℝ) (x s : ℝ) (y : Ω) : ℝ :=
  w y * Real.exp (x * energy (A y) + s * energy (B y))

/-- The integrated read of the given weighted exponential response. -/
def clock (μ : Measure Ω) (A B w : Ω → ℝ) (x s : ℝ) : ℝ :=
  ∫ y, ray A B w x s y ∂μ

/-- The signed second difference of the three reads. -/
def contrast (hi mid lo : ℝ) : ℝ := hi - 2 * mid + lo

/-- The symmetric three-read contrast at strengths (2t, 0), (t, t), and (0, 2t). -/
def split (μ : Measure Ω) (A B w : Ω → ℝ) (t : ℝ) : ℝ :=
  contrast (clock μ A B w (2*t) 0) (clock μ A B w t t) (clock μ A B w 0 (2*t))

/-- The explicit lower bound on the calibrated contrast in terms of the axis overlap. -/
def margin (t c : ℝ) : ℝ := (16*t^2/315) * (1-c^2) * (7+c^2)

/-- Supplied fourth, sixth, and eighth moments of every linear combination of the axes. -/
def AxisProjectionLaw (μ : Measure Ω) (A B : Ω → ℝ) (c : ℝ) : Prop :=
  ∀ (u v : ℝ) (k : ℕ), 2 ≤ k → k ≤ 4 →
    Integrable (fun y ↦ (u*A y + v*B y)^(2*k)) μ ∧
    (∫ y, (u*A y + v*B y)^(2*k) ∂μ) =
      (u^2 + 2*u*v*c + v^2)^k / (2*(k : ℝ)+1)

/-- Integrability of each weighted response used in the symmetric three-read contrast. -/
def ThreeIntegrable (μ : Measure Ω) (A B w : Ω → ℝ) (t : ℝ) : Prop :=
  Integrable (ray A B w (2*t) 0) μ ∧ Integrable (ray A B w t t) μ ∧
  Integrable (ray A B w 0 (2*t)) μ

/-- One calibrated symmetric design, not arbitrary finite designs. No claim of
reconstructing a nonaligned angle, or of constructing the acquisition protocol. -/
def SplitCertificate : Prop :=
  ∀ {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A B w : Ω → ℝ) (c t : ℝ),
    AxisProjectionLaw μ A B c → c^2 ≤ 1 → 0 < t → (∀ y, 1 ≤ w y) →
    ThreeIntegrable μ A B w t →
    margin t c ≤ split μ A B w t ∧
    (split μ A B w t = 0 ↔ c^2 = 1) ∧
    (∀ (hi mid lo ε : ℝ),
      |hi - clock μ A B w (2*t) 0| ≤ ε →
      |mid - clock μ A B w t t| ≤ ε →
      |lo - clock μ A B w 0 (2*t)| ≤ ε →
      (contrast hi mid lo > 4*ε → c^2 ≠ 1) ∧
      (8*ε < margin t c → 4*ε < contrast hi mid lo))
end VenSplit
end
