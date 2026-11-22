/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.NativeAction
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Generic first variation of the native two-field action

This module derives the directional derivative of the full native potential.
It uses the native action and the ordinary derivative rules for its polynomial terms.
-/

@[expose] public section

namespace LeanDirac.V2

variable {Site : Type} {Edge : Type*}

noncomputable section
open BigOperators

/-- The ordinary real derivative used for first and second variations of the action. -/
abbrev AnalyticHasDerivAt (f : ℝ → ℝ) (f' x : ℝ) : Prop :=
  @HasDerivAt ℝ inferInstance ℝ
    Real.normedAddCommGroup.toAddCommGroup
    RCLike.toInnerProductSpaceReal.toModule
    inferInstance inferInstance f f' x

/-- The real bilinear pairing underlying the Hermitian product on the native fields. -/
def c3RealPair (u v : C3) : ℝ :=
  ∑ component, (u component * star (v component)).re

/-- Componentwise addition of native complex three-vectors. -/
def c3Add (u v : C3) : C3 := fun component => u component + v component

/-- Multiply a complex three-vector by a real variation parameter. -/
def c3ScaleReal (a : ℝ) (u : C3) : C3 :=
  fun component => (a : ℂ) * u component

/-- A second-order test curve with specified constant, linear, and quadratic coefficients. -/
def c3QuadraticLine (u v q : C3) (eps : ℝ) : C3 :=
  c3Add (c3Add u (c3ScaleReal eps v)) (c3ScaleReal (eps ^ 2) q)

theorem density_quadratic_line_exact (u v q : C3) (eps : ℝ) :
    density (c3QuadraticLine u v q eps) =
      density u + 2 * eps * c3RealPair u v +
      eps ^ 2 * (density v + 2 * c3RealPair u q) +
      2 * eps ^ 3 * c3RealPair v q + eps ^ 4 * density q := by
  simp [density, c3QuadraticLine, c3Add, c3ScaleReal, c3RealPair,
    Fin.sum_univ_succ, Complex.normSq]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re, Complex.ofReal_im]
  ring_nf

theorem density_quadratic_line_hasDerivAt (u v q : C3) :
    AnalyticHasDerivAt (fun eps : ℝ => density (c3QuadraticLine u v q eps))
      (2 * c3RealPair u v) 0 := by
  have hfun :
      (fun eps : ℝ => density (c3QuadraticLine u v q eps)) =
      (fun eps : ℝ =>
        density u + 2 * eps * c3RealPair u v +
        eps ^ 2 * (density v + 2 * c3RealPair u q) +
        2 * eps ^ 3 * c3RealPair v q + eps ^ 4 * density q) := by
    funext eps
    exact density_quadratic_line_exact u v q eps
  rw [hfun]
  have hconst := hasDerivAt_const (𝕜 := ℝ) 0 (density u)
  have hlinear := (HasDerivAt.const_mul (2 : ℝ)
    (hasDerivAt_id (0 : ℝ))).mul_const (c3RealPair u v)
  have hquad := (hasDerivAt_pow 2 (0 : ℝ)).mul_const
    (density v + 2 * c3RealPair u q)
  have hcubic := (HasDerivAt.const_mul (2 : ℝ)
    (hasDerivAt_pow 3 (0 : ℝ))).mul_const (c3RealPair v q)
  have hquartic := (hasDerivAt_pow 4 (0 : ℝ)).mul_const (density q)
  have hsum := (((hconst.add hlinear).add hquad).add hcubic).add hquartic
  convert hsum using 1
  · funext eps
    simp only [Pi.add_apply, id_eq]
  · norm_num

/-- The zero complex three-vector used outside the chosen native field direction. -/
def c3Zero : C3 := fun _ => 0

@[simp] theorem c3_scale_zero (a : ℝ) : c3ScaleReal a c3Zero = c3Zero := by
  funext component
  simp [c3ScaleReal, c3Zero]

@[simp] theorem c3_zero_scale (u : C3) : c3ScaleReal 0 u = c3Zero := by
  funext component
  simp [c3ScaleReal, c3Zero]

@[simp] theorem c3_add_zero_right (u : C3) : c3Add u c3Zero = u := by
  funext component
  simp [c3Add, c3Zero]

/-- The affine line through a native three-vector in a given direction. -/
def c3Line (u v : C3) (eps : ℝ) : C3 :=
  c3Add u (c3ScaleReal eps v)

/-- The componentwise affine perturbation of both native configuration fields. -/
def stateLine (state direction : State Site) (eps : ℝ) : State Site where
  psi site := c3Line (state.psi site) (direction.psi site) eps
  chi site := c3Line (state.chi site) (direction.chi site) eps

/-- The coefficient linear in the perturbation in the exterior product of two fields. -/
def wedgeFirstVariation (state direction : State Site) (site : Site) : C3 :=
  c3Add
    (wedge (direction.chi site) (state.psi site))
    (wedge (state.chi site) (direction.psi site))

/-- The quadratic coefficient in the exterior product along a linear perturbation. -/
def wedgeSecondVariation (direction : State Site) (site : Site) : C3 :=
  wedge (direction.chi site) (direction.psi site)

theorem wedge_state_line_exact (state direction : State Site)
    (site : Site) (eps : ℝ) :
    wedge ((stateLine state direction eps).chi site)
      ((stateLine state direction eps).psi site) =
      c3QuadraticLine
        (wedge (state.chi site) (state.psi site))
        (wedgeFirstVariation state direction site)
        (wedgeSecondVariation direction site) eps := by
  funext component
  fin_cases component <;>
    simp [stateLine, c3Line, c3Add, c3ScaleReal, c3QuadraticLine,
      wedgeFirstVariation, wedgeSecondVariation, wedge] <;>
    ring

/-- The change of the exterior-area quantities between the two ends of a bond. -/
def bondAreaDifference (state : State Site) (edge : Bond Site) : C3 :=
  difference
    (wedge (state.chi edge.source) (state.psi edge.source))
    (wedge (state.chi edge.target) (state.psi edge.target))

/-- The first variation of the exterior-area difference of a bond. -/
def bondAreaFirstVariation (state direction : State Site)
    (edge : Bond Site) : C3 :=
  difference
    (wedgeFirstVariation state direction edge.source)
    (wedgeFirstVariation state direction edge.target)

/-- The quadratic coefficient of the exterior-area difference along an affine state line. -/
def bondAreaSecondVariation (direction : State Site)
    (edge : Bond Site) : C3 :=
  difference
    (wedgeSecondVariation direction edge.source)
    (wedgeSecondVariation direction edge.target)

theorem bond_area_state_line_exact (state direction : State Site)
    (edge : Bond Site) (eps : ℝ) :
    bondAreaDifference (stateLine state direction eps) edge =
      c3QuadraticLine
        (bondAreaDifference state edge)
        (bondAreaFirstVariation state direction edge)
        (bondAreaSecondVariation direction edge) eps := by
  funext component
  simp only [bondAreaDifference, difference,
    wedge_state_line_exact, c3QuadraticLine, c3Add, c3ScaleReal,
    bondAreaFirstVariation, bondAreaSecondVariation]
  ring_nf

/-- The real first variation of the weighted exterior-area bond energy. -/
def exteriorAreaBondFirstVariation (chi0 : ℝ)
    (state direction : State Site) (edge : Bond Site) : ℝ :=
  edge.weight / chi0 ^ 2 *
    c3RealPair (bondAreaDifference state edge)
      (bondAreaFirstVariation state direction edge)

theorem exterior_area_bond_hasDerivAt (chi0 : ℝ)
    (state direction : State Site) (edge : Bond Site) :
    AnalyticHasDerivAt
      (fun eps : ℝ => exteriorAreaBond chi0 (stateLine state direction eps) edge)
      (exteriorAreaBondFirstVariation chi0 state direction edge) 0 := by
  have h := HasDerivAt.const_mul (edge.weight / (2 * chi0 ^ 2))
    (density_quadratic_line_hasDerivAt
      (bondAreaDifference state edge)
      (bondAreaFirstVariation state direction edge)
      (bondAreaSecondVariation direction edge))
  convert h using 1
  · funext eps
    unfold exteriorAreaBond
    change edge.weight / (2 * chi0 ^ 2) *
      density (bondAreaDifference (stateLine state direction eps) edge) = _
    rw [bond_area_state_line_exact]
  · unfold exteriorAreaBondFirstVariation
    ring

/-- The directional derivative of the on-site part of the reciprocal potential. -/
def sitePotentialFirstVariation (chi0 : ℝ)
    (state direction : State Site) (site : Site) : ℝ :=
  let rhoPsi := density (state.psi site)
  let rhoChi := density (state.chi site)
  (rhoChi - chi0 ^ 2 + rhoPsi) *
      c3RealPair (state.chi site) (direction.chi site) +
    (rhoChi + rhoPsi) *
      c3RealPair (state.psi site) (direction.psi site)

theorem site_potential_hasDerivAt (chi0 : ℝ)
    (state direction : State Site) (site : Site) :
    AnalyticHasDerivAt
      (fun eps : ℝ => sitePotential chi0 (stateLine state direction eps) site)
      (sitePotentialFirstVariation chi0 state direction site) 0 := by
  have hChi := density_quadratic_line_hasDerivAt
    (state.chi site) (direction.chi site) c3Zero
  have hPsi := density_quadratic_line_hasDerivAt
    (state.psi site) (direction.psi site) c3Zero
  have hChi' : AnalyticHasDerivAt
      (fun eps : ℝ => density ((stateLine state direction eps).chi site))
      (2 * c3RealPair (state.chi site) (direction.chi site)) 0 := by
    convert hChi using 1
    funext eps
    simp [stateLine, c3Line, c3QuadraticLine]
  have hPsi' : AnalyticHasDerivAt
      (fun eps : ℝ => density ((stateLine state direction eps).psi site))
      (2 * c3RealPair (state.psi site) (direction.psi site)) 0 := by
    convert hPsi using 1
    funext eps
    simp [stateLine, c3Line, c3QuadraticLine]
  have h :=
    ((((hChi'.sub_const (chi0 ^ 2)).pow 2).div_const 4).add
      ((hChi'.mul hPsi').div_const 2)).add
      ((hPsi'.pow 2).div_const 4)
  convert h using 1
  · funext eps
    simp [sitePotential, Pi.add_apply, Pi.mul_apply, Pi.pow_apply]
  · unfold sitePotentialFirstVariation
    dsimp
    simp [stateLine, c3Line]
    ring

/-- The sum of the on-site and bond variations of the native potential. -/
def potentialFirstVariation [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state direction : State Site)
    (bond : Edge → Bond Site) : ℝ :=
  (∑ site, sitePotentialFirstVariation chi0 state direction site) +
    ∑ edge, exteriorAreaBondFirstVariation chi0 state direction (bond edge)

theorem potential_hasDerivAt [Fintype Site] [Fintype Edge]
    (chi0 : ℝ) (state direction : State Site)
    (bond : Edge → Bond Site) :
    AnalyticHasDerivAt
      (fun eps : ℝ => potential chi0 (stateLine state direction eps) bond)
      (potentialFirstVariation chi0 state direction bond) 0 := by
  have hsites := HasDerivAt.fun_sum
    (u := Finset.univ)
    (fun site _ => site_potential_hasDerivAt chi0 state direction site)
  have hedges := HasDerivAt.fun_sum
    (u := Finset.univ)
    (fun edge _ => exterior_area_bond_hasDerivAt
      chi0 state direction (bond edge))
  have h := hsites.add hedges
  convert h using 1
  · funext eps
    simp [potential]
  · rfl

end
end LeanDirac.V2
