/-
Copyright (c) 2026 Marcus Rockel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marcus Rockel
-/
module

public import LeanPool.Copula.CDF

/-!
# Copulas are determined by their distribution functions

Coordinate lower intervals generate the Borel sigma algebra of the unit
interval. Their finite products form a generating pi-system on the cube.
Consequently, two copulas with equal CDFs have equal underlying measures.
-/

public section

open MeasureTheory MeasurableSpace Set
open scoped unitInterval

namespace ProbabilityTheory.Copula

variable {d : ℕ}

/-- Two copulas are equal if their distribution functions agree at every point. -/
theorem ext_cdf {C D : Copula d} (h : ∀ u, C.cdf u = D.cdf u) : C = D := by
  classical
  apply ext
  let S : Fin d → Set (Set I) := fun _ => range Iic
  have hgen (i : Fin d) : generateFrom (S i) = (inferInstance : MeasurableSpace I) :=
    (BorelSpace.measurable_eq.trans (borel_eq_generateFrom_Iic I)).symm
  have hspan (i : Fin d) : IsCountablySpanning (S i) := by
    refine ⟨fun _ : ℕ => univ, fun _ => ?_, ?_⟩
    · refine ⟨1, ?_⟩
      ext x
      simp [unitInterval.le_one']
    · apply Subset.antisymm (subset_univ _)
      intro x _
      exact mem_iUnion.mpr ⟨0, mem_univ x⟩
  refine ext_of_generate_finite _ (generateFrom_eq_pi hgen hspan).symm
    (IsPiSystem.pi fun _ => isPiSystem_Iic) ?_ (by simp)
  rintro _ ⟨s, hs, rfl⟩
  have hs' : ∀ i, ∃ u : I, Iic u = s i := fun i => hs i (mem_univ i)
  choose u hu using hs'
  have hbox : Set.pi univ s = Iic u := by
    ext x
    simp only [mem_univ_pi, ← hu, mem_Iic, Pi.le_def]
  rw [hbox]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (h u)

/-- The CDF representation is injective. -/
theorem cdf_injective : Function.Injective (cdf (d := d)) :=
  fun _ _ h => ext_cdf (congrFun h)

theorem cdf_eq_iff {C D : Copula d} : C.cdf = D.cdf ↔ C = D :=
  cdf_injective.eq_iff

end ProbabilityTheory.Copula
