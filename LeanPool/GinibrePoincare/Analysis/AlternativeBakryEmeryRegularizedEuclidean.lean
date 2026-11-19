/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/AlternativeBakryEmeryRegularizedEuclidean.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module
public import LeanPool.GinibrePoincare.Analysis.AlternativeBakryEmeryRegularizedLift
public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticRadialGradient
public import LeanPool.GinibrePoincare.Analysis.BakryEmeryNormalizedLift
/-!
# Alternative Bakry Emery regularized Euclidean

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `bakryEmeryRegularizedConfigurationPotential_contDiff`,
`bakryEmeryRegularizedConfigurationPotential_euclidean_strongConvex`.
-/

@[expose] public section
open Set
namespace GinibrePoincare
noncomputable section

/-- The regularised potential `z ↦ n * V (√(configurationNormSq z + ε²))` on configurations,
the potential `V` being evaluated at a real point. -/
def bakryEmeryRegularizedConfigurationPotential (n d : ℕ) (V : Potential)
    (ε : ℝ) (z : Configuration d) : ℝ :=
  (n : ℝ)*V (Real.sqrt (configurationNormSq z+ε^2) : ℂ)

/-- Literal identification of the physical radial potential in actual real
Euclidean coordinates. Configuration's sup norm never enters the identity. -/
theorem bakryEmeryRegularizedConfigurationPotential_euclidean
    (n d : ℕ) (V : Potential) (ε : ℝ) :
    bakryEmeryRegularizedConfigurationPotential n d V ε ∘
      (configurationEuclideanEquiv d).symm =
    bakryEmeryRegularizedLiftPotential (E := EuclideanSpace ℝ (Fin d×Fin 2)) n V ε := by
  funext x
  have hh := ginibre_configurationEuclidean_norm_sq d ((configurationEuclideanEquiv d).symm x)
  simp only [ContinuousLinearEquiv.apply_symm_apply] at hh
  simp only [Function.comp_def, bakryEmeryRegularizedConfigurationPotential,
    bakryEmeryRegularizedLiftPotential,←hh]

theorem bakryEmeryRegularizedConfigurationPotential_euclidean_contDiff
    (n d : ℕ) (V : Potential) (ε : ℝ) (hV : ContDiff ℝ 2 V) (hε : 0 < ε) :
    ContDiff ℝ 2 (bakryEmeryRegularizedConfigurationPotential n d V ε ∘
      (configurationEuclideanEquiv d).symm) := by
  rw [bakryEmeryRegularizedConfigurationPotential_euclidean]
  exact bakryEmeryRegularizedLift_contDiff n V ε hV hε

theorem bakryEmeryRegularizedConfigurationPotential_contDiff
    (n d : ℕ) (V : Potential) (ε : ℝ) (hV : ContDiff ℝ 2 V) (hε : 0 < ε) :
    ContDiff ℝ 2 (bakryEmeryRegularizedConfigurationPotential n d V ε) := by
  have h := (bakryEmeryRegularizedConfigurationPotential_euclidean_contDiff n d V ε hV hε).comp
    (configurationEuclideanEquiv d).contDiff
  simpa only [Function.comp_def, ContinuousLinearEquiv.symm_apply_apply] using h

theorem bakryEmeryRegularizedConfigurationPotential_euclidean_strongConvex
    (n d : ℕ) (ρ ε : ℝ) (V : Potential)
    (hrot : IsRotationalPotential V) (hc : IsRhoConvexPotential ρ V) :
    ConvexOn ℝ univ (fun x : EuclideanSpace ℝ (Fin d×Fin 2) =>
      bakryEmeryRegularizedConfigurationPotential n d V ε
        ((configurationEuclideanEquiv d).symm x) - ((n : ℝ)*ρ)/2*‖x‖^2) := by
  have he := bakryEmeryRegularizedConfigurationPotential_euclidean n d V ε
  have he' (x : EuclideanSpace ℝ (Fin d×Fin 2)) := congrFun he x
  simp only [Function.comp_def] at he'
  simp_rw [he']
  exact bakryEmeryRegularizedLift_strongConvex n ρ ε hrot hc

/-- Exact real Euclidean to complex Hilbert block isometry. -/
def bakryEmeryRealComplexHilbertEquiv (k : ℕ) :
    EuclideanSpace ℝ (Fin (k+1)×Fin 2) ≃ₗᵢ[ℝ] BakryEmeryHilbertBlock k where
  toLinearEquiv := ((configurationEuclideanEquiv (k+1)).symm.trans
    (bakryEmeryBlockHilbertEquiv k)).toLinearEquiv
  norm_map' x := by
    have hr := ginibre_configurationEuclidean_norm_sq (k+1)
      ((configurationEuclideanEquiv (k+1)).symm x)
    simp only [ContinuousLinearEquiv.apply_symm_apply] at hr
    have hc : ‖bakryEmeryBlockHilbertEquiv k ((configurationEuclideanEquiv (k+1)).symm x)‖^2 =
        configurationNormSq ((configurationEuclideanEquiv (k+1)).symm x) := by
      change ‖(WithLp.toLp 2 ((configurationEuclideanEquiv (k+1)).symm x) :
        BakryEmeryHilbertBlock k)‖^2 = _
      rw [PiLp.norm_sq_eq_of_L2]
      simp only [configurationNormSq, Complex.normSq_eq_norm_sq]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (hc.trans hr.symm)

end
end GinibrePoincare
