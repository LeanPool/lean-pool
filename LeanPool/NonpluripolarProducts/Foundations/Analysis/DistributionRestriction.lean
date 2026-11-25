/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.Distribution.Distribution

/-! # Restricting distributions to open domains -/

@[expose] public section

noncomputable section

open TopologicalSpace
open scoped Distributions

namespace SGPT.Foundations.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {Ω U : Opens E}

/-- Restriction by the continuous inclusion of test functions. The explicit
domain inclusion excludes the zero fallback of `TestFunction.monoCLM`. -/
def restrictDistribution (T : 𝓓'(Ω, ℝ)) (_hUΩ : U ≤ Ω) : 𝓓'(U, ℝ) :=
  T.comp (TestFunction.monoCLM ℝ)

/-- Inclusion into a larger open domain does not change a test function's values. -/
theorem testFunction_inclusion_coe (hUΩ : U ≤ Ω) (φ : 𝓓(U, ℝ)) :
    ((TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) : E → ℝ) = φ := by
  simp only [TestFunction.monoCLM_apply, le_refl, hUΩ, and_self, ite_true]

theorem restrictDistribution_apply (T : 𝓓'(Ω, ℝ)) (hUΩ : U ≤ Ω)
    (φ : 𝓓(U, ℝ)) :
    restrictDistribution T hUΩ φ = T (TestFunction.monoCLM ℝ φ) := rfl

theorem restrictDistribution_self (T : 𝓓'(Ω, ℝ)) :
    restrictDistribution T le_rfl = T := by
  ext φ
  rw [restrictDistribution_apply]
  congr 1
  apply TestFunction.ext
  intro x
  exact congrFun (testFunction_inclusion_coe le_rfl φ) x

/-- Restriction of distributions is transitive.  Although the bundled test
functions are included in two stages on the left, both inclusions have the
same underlying function as the direct inclusion on the right. -/
theorem restrictDistribution_trans {V : Opens E} (T : 𝓓'(Ω, ℝ))
    (hVU : V ≤ U) (hUΩ : U ≤ Ω) :
    restrictDistribution (restrictDistribution T hUΩ) hVU =
      restrictDistribution T (hVU.trans hUΩ) := by
  ext φ
  simp only [restrictDistribution_apply]
  congr 1
  apply TestFunction.ext
  intro x
  calc
    ((TestFunction.monoCLM ℝ (TestFunction.monoCLM ℝ φ) : 𝓓(Ω, ℝ)) : E → ℝ) x =
        ((TestFunction.monoCLM ℝ φ : 𝓓(U, ℝ)) : E → ℝ) x :=
      congrFun (testFunction_inclusion_coe hUΩ (TestFunction.monoCLM ℝ φ)) x
    _ = φ x := congrFun (testFunction_inclusion_coe hVU φ) x
    _ = ((TestFunction.monoCLM ℝ φ : 𝓓(Ω, ℝ)) : E → ℝ) x :=
      (congrFun (testFunction_inclusion_coe (hVU.trans hUΩ) φ) x).symm

end SGPT.Foundations.Analysis
