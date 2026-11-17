/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.Rectangle
import LeanPool.Copula.Unique
import LeanPool.Copula.CDF.Extensionality

/-! # The classical copula conditions

This module states the classical boundary and rectangle conditions and proves
them for the CDF of every bundled copula. Normalization is explicit so that
dimension zero is covered. The converse is proved in `Copula.Classical.Characterization`.
-/

public section

open MeasureTheory Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- The classical conditions on a copula function. Continuity is not assumed. -/
structure IsClassical (F : (Fin d → I) → ℝ) : Prop where
  /-- The top corner has mass one, including in dimension zero. -/
  normalized : F (fun _ => 1) = 1
  /-- A zero coordinate makes the function vanish. -/
  grounded : ∀ (u : Fin d → I) (i : Fin d), u i = 0 → F u = 0
  /-- The one-coordinate boundary faces are uniform. -/
  marginal : ∀ (i : Fin d) (u : I), F (Function.update (fun _ => 1) i u) = (u : ℝ)
  /-- Every ordered rectangle has a nonnegative increment. -/
  increasing : ∀ a b, a ≤ b → 0 ≤ rectangleIncrement F a b

/-- Every measure-based copula satisfies the classical copula conditions. -/
theorem isClassical_cdf (C : Copula d) : IsClassical C.cdf where
  normalized := C.cdf_one
  grounded := C.cdf_eq_zero_of_coord_eq_zero
  marginal := C.cdf_update_one
  increasing := C.rectangleIncrement_cdf_nonneg

/-- There can be at most one copula measure representing a given function. -/
theorem unique_representation (F : (Fin d → I) → ℝ) {C D : Copula d}
    (hC : C.cdf = F) (hD : D.cdf = F) : C = D :=
  cdf_injective (hC.trans hD.symm)

/-- Turn a probability-measure representation of classical CDF data into a copula.
This is the marginal-identification step; it does not assume or assert an extension theorem. -/
@[expose]
noncomputable def IsClassical.ofMeasure {F : (Fin d → I) → ℝ} (hF : IsClassical F)
    (μ : ProbabilityMeasure (Fin d → I)) (hμ : ∀ u, μ.toMeasure.real (Iic u) = F u) : Copula d where
  measure := μ
  marginal_eq i := by
    apply Measure.ext_of_Iic
    intro t
    apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
    change (μ.toMeasure.map (fun x => x i)).real (Iic t) = volume.real (Iic t)
    rw [map_measureReal_apply (measurable_pi_apply i) measurableSet_Iic]
    have he : (fun x : Fin d → I => x i) ⁻¹' Iic t =
        Iic (Function.update (fun _ => 1) i t) := by
      ext x
      constructor
      · intro hx j
        by_cases hji : j = i
        · subst j; simpa using hx
        · simpa [Function.update_of_ne hji] using (unitInterval.le_one' (t := x j))
      · intro hx
        simpa using hx i
    rw [he, hμ, hF.marginal]
    simp [Measure.real, t.property.1]

theorem IsClassical.cdf_ofMeasure {F : (Fin d → I) → ℝ} (hF : IsClassical F)
    (μ : ProbabilityMeasure (Fin d → I)) (hμ : ∀ u, μ.toMeasure.real (Iic u) = F u) :
    (hF.ofMeasure μ hμ).cdf = F := funext hμ

/-- In the empty dimension the classical characterization is complete. -/
theorem IsClassical.existsUnique_dim_zero {F : (Fin 0 → I) → ℝ} (hF : IsClassical F) :
    ∃! C : Copula 0, C.cdf = F := by
  refine ⟨independence 0, ?_, fun C _ => Subsingleton.elim C _⟩
  funext u
  have hu : u = fun _ => 1 := Subsingleton.elim _ _
  rw [hu, cdf_one, hF.normalized]

/-- In dimension one the classical conditions force the uniform CDF. -/
theorem IsClassical.existsUnique_dim_one {F : (Fin 1 → I) → ℝ} (hF : IsClassical F) :
    ∃! C : Copula 1, C.cdf = F := by
  refine ⟨independence 1, ?_, fun C _ => Subsingleton.elim C _⟩
  funext u
  have hu : u = Function.update (fun _ => 1) 0 (u 0) := by
    funext i
    fin_cases i
    simp
  calc
    (independence 1).cdf u = (u 0 : ℝ) := cdf_dim_one _ _
    _ = F (Function.update (fun _ => 1) 0 (u 0)) := (hF.marginal 0 (u 0)).symm
    _ = F u := congrArg F hu.symm

end ProbabilityTheory.Copula
