/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import LeanPool.Superdiffusion.Algsuperdiff.Assumptions.ShellField.Actions

/-!
# SequenceLaw

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Canonical laws and transformations of shell sequences

The manuscript's probability space is the canonical sequence carrier
`ℤ → ShellField d`.  This file provides its coordinate marginal laws and the
literal componentwise transformations used by J1 and J3.  It introduces no
probabilistic assumptions.

## Main definitions

* `shellMarginalLaw`: the law of one specified shell coordinate.
* `zeroShellLaw`: the law of shell zero.
* `translateSequence`: simultaneous real translation of every shell.
* `negateSequence`: simultaneous negation of every shell.
* `rotateSequence`: simultaneous signed-permutation conjugation of every shell.
-/

namespace Algsuperdiff.Frozen.Assumptions.ShellField

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## Coordinate laws -/

/-- Evaluation of a shell sequence at a fixed integer coordinate is measurable. -/
theorem measurable_shellCoordinate (k : ℤ) :
    Measurable (fun F : ℤ → ShellField d ↦ F k) :=
  measurable_pi_apply k

/-- Measurability of the literal zero-coordinate map on shell sequences. -/
theorem measurable_zeroShellMap :
    Measurable (fun F : ℤ → ShellField d ↦ F 0) :=
  measurable_shellCoordinate 0

/-- The exact marginal law of shell coordinate `k`. -/
noncomputable def shellMarginalLaw
    (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d)) (k : ℤ) :
    MeasureTheory.ProbabilityMeasure (ShellField d) :=
  P.map (fun F : ℤ → ShellField d ↦ F k)

/-- The literal zero-coordinate shell-field law. -/
noncomputable def zeroShellLaw
    (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d)) :
    MeasureTheory.ProbabilityMeasure (ShellField d) :=
  P.map (fun F : ℤ → ShellField d ↦ F 0)

@[simp]
theorem shellMarginalLaw_zero
    (P : MeasureTheory.ProbabilityMeasure (ℤ → ShellField d)) :
    shellMarginalLaw P 0 = zeroShellLaw P :=
  rfl

/-! ## Componentwise whole-sequence transformations -/

/-- Simultaneously translate every shell by the same real vector. -/
def translateSequence (z : Vec d) (F : ℤ → ShellField d) :
    ℤ → ShellField d := fun k ↦ translate z (F k)

@[simp]
theorem translateSequence_apply (z : Vec d) (F : ℤ → ShellField d) (k : ℤ) :
    translateSequence z F k = translate z (F k) :=
  rfl

/-- Componentwise real translation is measurable on the whole sequence. -/
theorem measurable_translateSequence (z : Vec d) :
    Measurable (translateSequence (d := d) z) := by
  exact Measurable.of_eval fun k ↦
    (measurable_translate z).comp (measurable_pi_apply k)

/-- Simultaneously negate every shell in the sequence. -/
def negateSequence (F : ℤ → ShellField d) : ℤ → ShellField d :=
  fun k ↦ negate (F k)

@[simp]
theorem negateSequence_apply (F : ℤ → ShellField d) (k : ℤ) :
    negateSequence F k = negate (F k) :=
  rfl

/-- Componentwise negation is measurable on the whole sequence. -/
theorem measurable_negateSequence :
    Measurable (negateSequence (d := d)) := by
  exact Measurable.of_eval fun k ↦
    measurable_negate.comp (measurable_pi_apply k)

/-- Simultaneously apply one signed-permutation conjugation to every shell. -/
def rotateSequence (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (F : ℤ → ShellField d) : ℤ → ShellField d :=
  fun k ↦ rotate R hR (F k)

@[simp]
theorem rotateSequence_apply (R : Mat d) (hR : IsSignedPermutationMatrix R)
    (F : ℤ → ShellField d) (k : ℤ) :
    rotateSequence R hR F k = rotate R hR (F k) :=
  rfl

/-- Componentwise signed-permutation conjugation is measurable on the whole sequence. -/
theorem measurable_rotateSequence (R : Mat d) (hR : IsSignedPermutationMatrix R) :
    Measurable (rotateSequence (d := d) R hR) := by
  exact Measurable.of_eval fun k ↦
    (measurable_rotate R hR).comp (measurable_pi_apply k)

end

end Algsuperdiff.Frozen.Assumptions.ShellField

/-! Migration cache (mathlib v4.33.1). Under the elementwise matrix norm, blind typeclass search
for `ContinuousENorm (Matrix m n ℝ)` wanders through `CStarAlgebra`/`NormedRing` branches and gives
up even though the instance exists. The frozen assumption files (`Frozen/Assumptions/ShellLawJ*`)
open `Matrix.Norms.Elementwise` and integrate matrix-valued observables, so the cache lives here,
scoped to that norm, and never inside a manifest-pinned file. -/
namespace Matrix.Norms.Elementwise

scoped instance instContinuousENormMatrixElementwise {m n : Type*} [Fintype m] [Fintype n] :
    ContinuousENorm (Matrix m n ℝ) := by
  show ContinuousENorm (m → n → ℝ)
  infer_instance

end Matrix.Norms.Elementwise
