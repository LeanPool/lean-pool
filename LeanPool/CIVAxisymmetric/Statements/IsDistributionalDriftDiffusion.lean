/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Statements.GradPair
public import LeanPool.CIVAxisymmetric.Statements.PartialLaplacian
public import LeanPool.CIVAxisymmetric.Statements.TestFunctions
public import LeanPool.CIVAxisymmetric.Statements.TimeDeriv
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Prod

/-!
# Is Distributional Drift Diffusion

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory
open CKN


noncomputable section

namespace CIV

/-- `∂_τ q + B·∇q = Δ_X q` on `Vec m × I` in the sense of distributions, with
`B·∇q = div(Bq) - (div B) q` (footnote to `eq:aniso:comparison:equation`), the divergence
`div B` of the drift being carried as data (design note N5). -/
@[expose] def IsDistributionalDriftDiffusion (m d : ℕ) (I : Set ℝ) (B : Vec m × ℝ → Vec m)
    (divB : Vec m × ℝ → ℝ) (q : Vec m × ℝ → ℝ) : Prop :=
  ∀ φ ∈ testFunctions m I,
    IntegrableOn (fun z => q z * (-(timeDeriv m φ z) - gradPair m φ z (B z) - divB z * φ z -
      partialLaplacian m d φ z)) (tsupport φ) volume ∧
    ∫ z, q z * (-(timeDeriv m φ z) - gradPair m φ z (B z) - divB z * φ z -
      partialLaplacian m d φ z) = 0

end CIV
