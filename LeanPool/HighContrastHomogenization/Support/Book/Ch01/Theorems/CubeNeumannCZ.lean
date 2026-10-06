/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch01.Definitions
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeNeumannW22CZ.Regularity

/-!
# Coarse-graining support: Support.Book.Ch01.Theorems.CubeNeumannCZ

Imported from the Apache-2.0 CoarseGraining development at commit
`c7ddd76c08ade64fed1b8d2ca51be14dfee8deb4`.
-/

public section

/-!
# Legacy Chapter 1 Neumann compatibility facade

This module is deliberately quarantined in
`HCPolySupport.Book.Ch01.Legacy`.  Its selected constant and regularity
theorem alias a downstream positive-test estimate; they are not the literal
weak-Hessian Calderon--Zygmund statement from the manuscript.
-/

namespace HCPolySupport
namespace Book
namespace Ch01

noncomputable section

namespace Legacy

open scoped ENNReal

/-- Legacy selected constant for the downstream Neumann positive-test
compatibility package on cubes. -/
noncomputable abbrev cubeNeumannW22Constant (d : ℕ) [NeZero d] : ℝ :=
  HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant d

theorem cubeNeumannW22Constant_nonneg (d : ℕ) [NeZero d] :
    0 ≤ cubeNeumannW22Constant d := by
  simpa [cubeNeumannW22Constant] using
    HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d

/-- Legacy cube Neumann positive-test compatibility theorem.  This is not the
literal weak-Hessian Calderon--Zygmund theorem. -/
theorem cubeNeumannW22Regularity {d : ℕ} [NeZero d] (Q : Cube d) :
    HCPolySupport.Legacy.CubeNeumannW22CalderonZygmundRegularity Q
      (cubeNeumannW22Constant d) := by
  simpa [cubeNeumannW22Constant] using
    HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundRegularity Q

/-- Dimension-uniform existence form of the legacy cube Neumann positive-test
compatibility package. -/
theorem exists_cubeNeumannW22RegularityInDimension (d : ℕ) [NeZero d] :
    ∃ C : ℝ,
      HCPolySupport.Legacy.CubeNeumannW22CalderonZygmundRegularityInDimension d C :=
  HCPolySupport.Legacy.exists_cubeNeumannW22CalderonZygmundRegularityInDimension d

end Legacy

end

end Ch01
end Book
end HCPolySupport
