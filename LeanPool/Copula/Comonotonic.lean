/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.CDF

/-!
# The comonotonic copula

Pushing uniform volume forward along the diagonal gives a copula whose
coordinates agree almost surely.
-/

public section

open MeasureTheory
open scoped unitInterval

namespace ProbabilityTheory.Copula

/-- The comonotonic copula, the law of a repeated uniform random variable. -/
@[expose]
noncomputable def comonotonic (d : ℕ) : Copula d :=
  ofMap ⟨volume, inferInstance⟩ (fun u _ => u)
    (Measurable.of_eval fun _ => measurable_id) (fun _ => Measure.map_id)

@[simp]
theorem toMeasure_comonotonic (d : ℕ) :
    (comonotonic d).toMeasure =
      (volume : Measure I).map (fun u (_ : Fin d) => u) := rfl

/-- The comonotonic CDF is the minimum coordinate, with empty infimum equal to one. -/
@[simp]
theorem cdf_comonotonic {d : ℕ} (u : Fin d → I) :
    (comonotonic d).cdf u = ((⨅ i, u i : I) : ℝ) := by
  have h : (fun t (_ : Fin d) => t) ⁻¹' Set.Iic u = Set.Iic (⨅ i, u i) := by
    ext t
    simp [Set.mem_Iic, Pi.le_def, le_iInf_iff]
  have hdiag : Measurable (fun (t : I) (_ : Fin d) => t) :=
    Measurable.of_eval fun _ => measurable_id
  rw [cdf, toMeasure_comonotonic, map_measureReal_apply hdiag measurableSet_Iic, h]
  simp [Measure.real, (iInf u).property.1]

end ProbabilityTheory.Copula
