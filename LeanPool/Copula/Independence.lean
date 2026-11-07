/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.CDF

/-!
# The independence copula

The independence copula is the product of the uniform probability measures.
Its CDF is the product of the coordinates, including the empty product in
dimension zero.
-/

public section

open MeasureTheory Set
open scoped unitInterval BigOperators

namespace ProbabilityTheory.Copula

/-- The independence (product) copula. -/
@[expose]
noncomputable def independence (d : ℕ) : Copula d where
  measure := ⟨Measure.pi (fun _ : Fin d => (volume : Measure I)), inferInstance⟩
  marginal_eq i := (MeasureTheory.measurePreserving_eval (fun _ => volume) i).map_eq

@[simp]
theorem toMeasure_independence (d : ℕ) :
    (independence d).toMeasure = Measure.pi (fun _ : Fin d => (volume : Measure I)) := rfl

noncomputable instance (d : ℕ) : Inhabited (Copula d) := ⟨independence d⟩

@[simp]
theorem cdf_independence {d : ℕ} (u : Fin d → I) :
    (independence d).cdf u = ∏ i, (u i : ℝ) := by
  have h : Iic u = Set.pi univ (fun i => Iic (u i)) := by
    ext x
    simp [mem_Iic, Pi.le_def]
  simp only [cdf, Measure.real, toMeasure_independence, h, Measure.pi_pi,
    unitInterval.volume_Iic, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun i _ => ENNReal.toReal_ofReal (u i).property.1)

end ProbabilityTheory.Copula
