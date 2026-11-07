/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Copulas as probability measures

A copula is a probability measure on a finite power of the unit interval with
uniform coordinate marginals. Dimension zero is allowed. The usual copula
distribution function is derived in `Copula.CDF`.
-/

public section

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory

/-- A `d`-dimensional copula, represented by a probability measure on `[0, 1]^d`
whose coordinate marginals are the canonical uniform probability measure. -/
structure Copula (d : ℕ) where
  /-- The probability measure underlying the copula. -/
  measure : ProbabilityMeasure (Fin d → I)
  /-- Every coordinate has the uniform distribution on the unit interval. -/
  marginal_eq (i : Fin d) : measure.toMeasure.map (fun x => x i) = volume

namespace Copula

variable {d : ℕ}

/-- The underlying measure, for use with mathlib's measure-theoretic API. -/
@[expose]
def toMeasure (C : Copula d) : Measure (Fin d → I) := C.measure.toMeasure

instance (C : Copula d) : IsProbabilityMeasure C.toMeasure :=
  inferInstanceAs (IsProbabilityMeasure C.measure.toMeasure)

@[ext]
theorem ext {C D : Copula d} (h : C.toMeasure = D.toMeasure) : C = D := by
  have hmeasure : C.measure = D.measure := ProbabilityMeasure.toMeasure_injective h
  cases C
  cases D
  cases hmeasure
  rfl

theorem toMeasure_injective : Function.Injective (toMeasure (d := d)) :=
  fun _ _ h => ext h

@[simp]
theorem map_eval (C : Copula d) (i : Fin d) :
    C.toMeasure.map (fun x => x i) = volume :=
  C.marginal_eq i

/-- Coordinate projections preserve the uniform measure. -/
theorem measurePreserving_eval (C : Copula d) (i : Fin d) :
    MeasurePreserving (fun x => x i) C.toMeasure volume :=
  ⟨measurable_pi_apply i, C.map_eval i⟩

/-- The probability of a measurable coordinate event is its uniform volume. -/
theorem measure_preimage_eval (C : Copula d) (i : Fin d) {s : Set I}
    (hs : MeasurableSet s) : C.toMeasure ((fun x => x i) ⁻¹' s) = volume s := by
  rw [← Measure.map_apply (measurable_pi_apply i) hs, C.map_eval]

@[simp]
theorem measure_eval_le (C : Copula d) (i : Fin d) (u : I) :
    C.toMeasure {x | x i ≤ u} = ENNReal.ofReal (u : ℝ) := by
  exact (C.measure_preimage_eval i measurableSet_Iic).trans (unitInterval.volume_Iic u)

@[simp]
theorem measureReal_eval_le (C : Copula d) (i : Fin d) (u : I) :
    C.toMeasure.real {x | x i ≤ u} = (u : ℝ) := by
  simp [Measure.real, C.measure_eval_le, u.property.1]

/-- Construct a copula from a random vector with uniform coordinate laws. -/
@[expose]
noncomputable def ofMap {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (X : Ω → Fin d → I) (hX : Measurable X)
    (hmarg : ∀ i, μ.toMeasure.map (fun ω => X ω i) = volume) : Copula d where
  measure := μ.map X
  marginal_eq i := by
    rw [ProbabilityMeasure.toMeasure_map, Measure.map_map (measurable_pi_apply i) hX]
    exact hmarg i

@[simp]
theorem toMeasure_ofMap {Ω : Type*} [MeasurableSpace Ω]
    (μ : ProbabilityMeasure Ω) (X : Ω → Fin d → I) (hX : Measurable X)
    (hmarg : ∀ i, μ.toMeasure.map (fun ω => X ω i) = volume) :
    (ofMap μ X hX hmarg).toMeasure = μ.toMeasure.map X := rfl

end Copula
end ProbabilityTheory
