/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Main.Comparison
public import LeanPool.CIVAxisymmetric.Statements.IsAdmissibleDrift
public import LeanPool.CIVAxisymmetric.Statements.IsDistributionalDriftDiffusion
public import LeanPool.CIVAxisymmetric.Statements.IsLocallyBoundedOn
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.Order.Interval.Set.OrdConnected

/-!
# Comparison

Supporting results for the Constantin–Ignatova–Vicol axisymmetric regularity theorem.
-/


public section

open MeasureTheory Set
open CKN


noncomputable section

namespace CIV

/-- Lemma 3.3 (`lem:aniso:comparison`), first assertion. -/
theorem comparison (m d : ℕ) (hd : 1 ≤ d ∧ d ≤ m) (I : Set ℝ)
    (hI : IsOpen I ∧ I.OrdConnected)
    (B : Vec m × ℝ → Vec m) (divB : Vec m × ℝ → ℝ) (hB : IsAdmissibleDrift m I B divB)
    (q : Vec m × ℝ → ℝ) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) :
    ∀ᵐ τ₀ ∂(volume.restrict I), ∀ᵐ τ ∂(volume.restrict I), τ₀ < τ →
      eLpNorm (fun x => q (x, τ)) ⊤ volume ≤ eLpNorm (fun x => q (x, τ₀)) ⊤ volume := by
  exact CIV.Main.comparison m d hd I hI B divB hB q hq heq

end CIV
