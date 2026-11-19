/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/NonQuadraticPiBergman.lean.
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

public import LeanPool.GinibrePoincare.Analysis.NonQuadraticL2PiDensity
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticBergmanComplex
public import LeanPool.GinibrePoincare.Analysis.NonQuadraticFiniteProjection
public import Mathlib.Data.List.FinRange

/-!
# Non quadratic pi Bergman

Part of the nonquadratic potentials development of the
Ginibre Poincaré formalization.

Main results: `planarPiBergmanProjection_error`, `planarPiBergmanProjection_fixed`.
-/

@[expose] public section

open MeasureTheory
open scoped ContDiff InnerProductSpace
namespace GinibrePoincare
noncomputable section

/-- The Hilbert space `L²(ℂ^d)` for the product of Lebesgue measures on `d` copies of `ℂ`. -/
abbrev PlanarPiLebesgueL2 (d : ℕ) := Lp ℂ 2 (Measure.pi (fun _ : Fin d => (volume : Measure ℂ)))

/-- The planar Bergman projection `planarBergmanProjection n V` acting in the `i`-th coordinate
of `L²(ℂ^(m+1))`. -/
def planarPiBergmanCoordinate {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V)
    (i : Fin (m + 1)) : PlanarPiLebesgueL2 (m+1) →L[ℂ] PlanarPiLebesgueL2 (m+1) :=
  l2PiCoordinateOperator (fun _ => (volume : Measure ℂ)) i (planarBergmanProjection n V hV)

theorem planarPiBergmanCoordinate_adjoint {m : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) (i : Fin (m + 1)) :
    (planarPiBergmanCoordinate n V hV i).adjoint = planarPiBergmanCoordinate n V hV i := by
  rw [planarPiBergmanCoordinate, l2PiCoordinateOperator_adjoint]
  congr 1
  exact isSelfAdjoint_starProjection (planarBergmanKernelClosed n V hV).toSubmodule

theorem planarPiBergmanCoordinate_idempotent {m : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) (i : Fin (m + 1)) :
    (planarPiBergmanCoordinate n V hV i).comp (planarPiBergmanCoordinate n V hV i) =
      planarPiBergmanCoordinate n V hV i := by
  apply l2PiCoordinateOperator_idempotent
  exact (planarBergmanKernelClosed n V hV).toSubmodule.isIdempotentElem_starProjection

theorem planarPiBergmanCoordinate_norm_le {m : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) (i : Fin (m + 1)) : ‖planarPiBergmanCoordinate n V hV i‖ ≤ 1 :=
  (l2PiCoordinateOperator_norm_le _ _ _).trans
    (planarBergmanKernelClosed n V hV).toSubmodule.starProjection_norm_le

theorem planarPiBergmanCoordinates_commute {m : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) (i j : Fin (m + 1)) :
    (planarPiBergmanCoordinate n V hV i).comp (planarPiBergmanCoordinate n V hV j) =
      (planarPiBergmanCoordinate n V hV j).comp (planarPiBergmanCoordinate n V hV i) := by
  by_cases hij : i = j
  · subst j; rfl
  · exact l2PiCoordinateOperators_commute _ i j hij _ _

/-- The product Bergman projection on `L²(ℂ^(m+1))`: the composition of the coordinatewise
Bergman projections `planarPiBergmanCoordinate` over all coordinates. -/
def planarPiBergmanProjection {m : ℕ} (n : ℕ) (V : ℂ → ℝ) (hV : ContDiff ℝ 2 V) :
    PlanarPiLebesgueL2 (m+1) →L[ℂ] PlanarPiLebesgueL2 (m+1) :=
  complexSuccessiveProjections ((List.finRange (m+1)).map (planarPiBergmanCoordinate n V hV))

theorem planarPiBergmanProjection_error {m : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) (F : PlanarPiLebesgueL2 (m + 1)) :
    ‖F - planarPiBergmanProjection n V hV F‖ ^ 2 ≤
      ((List.finRange (m+1)).map (fun i => ‖F - planarPiBergmanCoordinate n V hV i F‖ ^ 2)).sum :=
          by
  have hp : ∀ P ∈ (List.finRange (m+1)).map (planarPiBergmanCoordinate n V hV),
      P.adjoint = P ∧ P.comp P = P ∧ ‖P‖ ≤ 1 := by
    intro P hP
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hP
    exact ⟨planarPiBergmanCoordinate_adjoint n V hV i,
      planarPiBergmanCoordinate_idempotent n V hV i, planarPiBergmanCoordinate_norm_le n V hV i⟩
  simpa only [planarPiBergmanProjection, List.map_map, Function.comp_def] using
    complexSuccessiveProjections_error _ hp F

theorem planarPiBergmanProjection_fixed {m : ℕ} (n : ℕ) (V : ℂ → ℝ)
    (hV : ContDiff ℝ 2 V) (F : PlanarPiLebesgueL2 (m + 1)) (i : Fin (m + 1)) :
    planarPiBergmanCoordinate n V hV i (planarPiBergmanProjection n V hV F) =
      planarPiBergmanProjection n V hV F := by
  apply complexSuccessiveProjections_fixed
  · intro P hP
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hP
    exact planarPiBergmanCoordinate_idempotent n V hV j
  · intro P hP Q hQ
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hP
    obtain ⟨k, _, rfl⟩ := List.mem_map.mp hQ
    exact planarPiBergmanCoordinates_commute n V hV j k
  · exact List.mem_map.mpr ⟨i, List.mem_finRange i, rfl⟩
end
end GinibrePoincare
