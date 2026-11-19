/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

/-
Adapted from gpartin/LeanDiracDerivation, file `LeanDirac/Foundation.lean`, at commit
867004142ada3eec464d5bd3088d7313fdad1613.
Upstream copyright (c) 2026 G. D. Partin, dual-licensed at the recipient's
option under the MIT License or CC0 1.0 (see the upstream `LICENSE`,
`LICENSE-CC0` and `LICENSING.md`); used here under the MIT License.
-/

module

public import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
public import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.RealSqrt

/-! The two native complex-C3 fields and their ordinary positive kinetic law. -/

@[expose] public section

namespace LeanDirac

variable {Site : Type} {Edge : Type*}

noncomputable section
open BigOperators Complex

abbrev C3 := Fin 3 → ℂ

def chi0 : ℝ := 19
def kappa : ℝ := 1 / 63
def chiKineticNormalization : ℝ := chi0 / kappa

theorem chi_kinetic_normalization_eq_1197 :
    chiKineticNormalization = 1197 := by
  norm_num [chiKineticNormalization, chi0, kappa]

structure State (Site : Type) where
  psi : Site → C3
  chi : Site → C3

structure Velocity (Site : Type) where
  psiDot : Site → C3
  chiDot : Site → C3

structure Bond (Site : Type) where
  source : Site
  target : Site
  weight : ℝ

def density (v : C3) : ℝ :=
  ∑ component, Complex.normSq (v component)

def inner (u v : C3) : ℂ :=
  ∑ component, star (u component) * v component

def difference (u v : C3) : C3 :=
  fun component => v component - u component

def kinetic [Fintype Site] (B : ℝ) (velocity : Velocity Site) : ℝ :=
  (∑ site, density (velocity.psiDot site)) / 2 +
    B * (∑ site, density (velocity.chiDot site)) / 2

theorem density_nonnegative (v : C3) : 0 ≤ density v := by
  unfold density
  exact Finset.sum_nonneg (fun component _ =>
    Complex.normSq_nonneg (v component))

theorem kinetic_nonnegative [Fintype Site]
    (B : ℝ) (velocity : Velocity Site) (hB : 0 ≤ B) :
    0 ≤ kinetic B velocity := by
  unfold kinetic
  have hp : 0 ≤ ∑ site, density (velocity.psiDot site) :=
    Finset.sum_nonneg (fun site _ =>
      density_nonnegative (velocity.psiDot site))
  have hx : 0 ≤ ∑ site, density (velocity.chiDot site) :=
    Finset.sum_nonneg (fun site _ =>
      density_nonnegative (velocity.chiDot site))
  positivity

theorem state_has_exactly_two_field_families (state : State Site) :
    state = ⟨state.psi, state.chi⟩ := by
  cases state
  rfl

end
end LeanDirac
