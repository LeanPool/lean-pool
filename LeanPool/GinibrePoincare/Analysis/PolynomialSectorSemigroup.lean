/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/PolynomialSectorSemigroup.lean.
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

public import LeanPool.GinibrePoincare.Analysis.PolynomialSpectralContraction
public import Mathlib.Analysis.Normed.Operator.Extend

/-! # Bounded spectral evolution on the closed polynomial sector

The maps below are dense extensions in actual Ginibre L². Identification
with the full diffusion is not asserted.
-/

@[expose] public section
open scoped BigOperators NNReal
open Topology
namespace GinibrePoincare
noncomputable section

instance polynomialSector_completeSpace (n : ℕ) (hn : 2 ≤ n) :
    CompleteSpace (closedPolynomialSector n hn) :=
  (Submodule.span ℂ (Set.range (polynomialEigenfunctionL2 n
      hn))).isClosed_topologicalClosure.completeSpace_coe

/-- The polynomial eigenfunction with indices `i`, as an element of the closed polynomial
sector. -/
def polynomialSectorEigenvector (n : ℕ) (hn : 2 ≤ n) (i : PolynomialEigenfunctionData n) :
    closedPolynomialSector n hn :=
  ⟨polynomialEigenfunctionL2 n hn i,
    (Submodule.span ℂ (Set.range (polynomialEigenfunctionL2 n hn))).le_topologicalClosure
      (Submodule.subset_span ⟨i, rfl⟩)⟩

/-- The linear map sending finitely supported coefficients to the corresponding finite
combination of polynomial eigenfunctions in the closed polynomial sector. -/
def polynomialSectorCombination (n : ℕ) (hn : 2 ≤ n) :
    (PolynomialEigenfunctionData n →₀ ℂ) →ₗ[ℂ] closedPolynomialSector n hn :=
  Finsupp.linearCombination ℂ (polynomialSectorEigenvector n hn)

theorem polynomialSectorCombination_coe (n : ℕ) (hn : 2 ≤ n)
    (c : PolynomialEigenfunctionData n →₀ ℂ) :
    (polynomialSectorCombination n hn c : GinibrePolynomialL2 n) =
      Finsupp.linearCombination ℂ (polynomialEigenfunctionL2 n hn) c := by
  simp [polynomialSectorCombination, Finsupp.linearCombination_apply,
    Finsupp.sum, polynomialSectorEigenvector]

theorem polynomialSectorCombination_dense (n : ℕ) (hn : 2 ≤ n) :
    DenseRange (polynomialSectorCombination n hn) := by
  change Dense (Set.range (polynomialSectorCombination n hn))
  apply (IsInducing.subtypeVal (t := (closedPolynomialSector n hn : Set (GinibrePolynomialL2
      n)))).dense_iff.mpr
  intro x
  have himage : (fun y : closedPolynomialSector n hn => (y : GinibrePolynomialL2 n)) '' Set.range
      (polynomialSectorCombination n hn) =
      (Submodule.span ℂ (Set.range (polynomialEigenfunctionL2 n hn)) : Set (GinibrePolynomialL2 n))
          := by
    rw [← Set.range_comp]
    have heq : ((fun y : closedPolynomialSector n hn => (y : GinibrePolynomialL2 n)) ∘
        polynomialSectorCombination n hn) =
        Finsupp.linearCombination ℂ (polynomialEigenfunctionL2 n hn) := by
      funext c
      exact polynomialSectorCombination_coe n hn c
    rw [heq, ← Finsupp.range_linearCombination]
    rfl
  change (x : GinibrePolynomialL2 n) ∈ closure ((fun y : closedPolynomialSector n hn => (y :
      GinibrePolynomialL2 n)) '' Set.range (polynomialSectorCombination n hn))
  rw [himage]
  exact x.property

/-- The spectral evolution at time `t` of finite combinations: the coefficient of each
eigenfunction is multiplied by `exp (-eigenvalue n a b m * t)`. -/
def polynomialSectorFiniteEvolution (n : ℕ) (hn : 2 ≤ n) (t : ℝ) :
    (PolynomialEigenfunctionData n →₀ ℂ) →ₗ[ℂ] closedPolynomialSector n hn :=
  Finsupp.linearCombination ℂ fun i =>
    (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) • polynomialSectorEigenvector n hn i

theorem polynomialSectorFiniteEvolution_contracts (n : ℕ) (hn : 2 ≤ n)
    {t : ℝ} (ht : 0 ≤ t) (c : PolynomialEigenfunctionData n →₀ ℂ) :
    ‖polynomialSectorFiniteEvolution n hn t c‖ ≤ ‖polynomialSectorCombination n hn c‖ := by
  have h := finitePolynomialSpectralEvolution_contracts n hn ht c.support c
  simpa [polynomialSectorFiniteEvolution, polynomialSectorCombination,
    Finsupp.linearCombination_apply, Finsupp.sum, finitePolynomialSpectralEvolution,
    polynomialSectorEigenvector, smul_smul, mul_comm] using h

/-- Genuine bounded operator on the complete closed polynomial sector. -/
def polynomialSectorEvolution (n : ℕ) (hn : 2 ≤ n) (t : ℝ≥0) :
    closedPolynomialSector n hn →L[ℂ] closedPolynomialSector n hn :=
  (polynomialSectorFiniteEvolution n hn t).extendOfNorm (polynomialSectorCombination n hn)

theorem polynomialSectorEvolution_combination (n : ℕ) (hn : 2 ≤ n) (t : ℝ≥0)
    (c : PolynomialEigenfunctionData n →₀ ℂ) :
    polynomialSectorEvolution n hn t (polynomialSectorCombination n hn c) =
      polynomialSectorFiniteEvolution n hn t c := by
  apply LinearMap.extendOfNorm_eq (polynomialSectorCombination_dense n hn)
  exact ⟨1, fun c => by simpa using polynomialSectorFiniteEvolution_contracts n hn t.coe_nonneg c⟩

theorem polynomialSectorEvolution_contracts (n : ℕ) (hn : 2 ≤ n) (t : ℝ≥0)
    (x : closedPolynomialSector n hn) :
    ‖polynomialSectorEvolution n hn t x‖ ≤ ‖x‖ := by
  simpa only [polynomialSectorEvolution, one_mul] using LinearMap.norm_extendOfNorm_apply_le
    (f := polynomialSectorFiniteEvolution n hn t) (polynomialSectorCombination_dense n hn)
    1 (fun c => by simpa using polynomialSectorFiniteEvolution_contracts n hn t.coe_nonneg c) x

@[simp] theorem polynomialSectorEvolution_eigenvector (n : ℕ) (hn : 2 ≤ n)
    (t : ℝ≥0) (i : PolynomialEigenfunctionData n) :
    polynomialSectorEvolution n hn t (polynomialSectorEigenvector n hn i) =
      (Real.exp (-eigenvalue n i.a i.b i.m * t) : ℂ) • polynomialSectorEigenvector n hn i := by
  have h := polynomialSectorEvolution_combination n hn t (Finsupp.single i 1)
  simpa [polynomialSectorCombination, polynomialSectorFiniteEvolution,
    Finsupp.linearCombination_single] using h

@[simp] theorem polynomialSectorEvolution_zero (n : ℕ) (hn : 2 ≤ n) :
    polynomialSectorEvolution n hn 0 = ContinuousLinearMap.id ℂ _ := by
  apply ContinuousLinearMap.ext
  intro x
  refine (polynomialSectorCombination_dense n hn).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro c
    rw [polynomialSectorEvolution_combination]
    simp [polynomialSectorFiniteEvolution, polynomialSectorCombination]

/-- Semigroup law on the closed sector, obtained by density from eigenvectors. -/
theorem polynomialSectorEvolution_add (n : ℕ) (hn : 2 ≤ n) (s t : ℝ≥0) :
    polynomialSectorEvolution n hn (s + t) =
      (polynomialSectorEvolution n hn s).comp (polynomialSectorEvolution n hn t) := by
  apply ContinuousLinearMap.ext
  intro x
  refine (polynomialSectorCombination_dense n hn).induction_on x ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  · intro c
    simp only [ContinuousLinearMap.comp_apply, polynomialSectorEvolution_combination]
    simp [polynomialSectorFiniteEvolution, Finsupp.linearCombination_apply, Finsupp.sum,
      smul_smul, mul_add, Real.exp_add, mul_comm, mul_assoc]

theorem polynomialSectorEvolution_dist_le (n : ℕ) (hn : 2 ≤ n) (t : ℝ≥0)
    (x y : closedPolynomialSector n hn) :
    dist (polynomialSectorEvolution n hn t x) (polynomialSectorEvolution n hn t y) ≤
      dist x y := by
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  exact polynomialSectorEvolution_contracts n hn t (x - y)

theorem continuous_polynomialSectorEvolution_combination (n : ℕ) (hn : 2 ≤ n)
    (c : PolynomialEigenfunctionData n →₀ ℂ) :
    Continuous (fun t : ℝ≥0 => polynomialSectorEvolution n hn t (polynomialSectorCombination n hn
        c)) := by
  simp only [polynomialSectorEvolution_combination, polynomialSectorFiniteEvolution,
    Finsupp.linearCombination_apply, Finsupp.sum]
  apply continuous_finsetSum
  intro i _
  fun_prop

/-- Strong continuity at every nonnegative time on the actual closed L² sector. -/
theorem continuous_polynomialSectorEvolution (n : ℕ) (hn : 2 ≤ n)
    (x : closedPolynomialSector n hn) :
    Continuous (fun t : ℝ≥0 => polynomialSectorEvolution n hn t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.continuousAt_iff.mpr
  intro ε hε
  obtain ⟨c, hc⟩ := (polynomialSectorCombination_dense n hn).exists_dist_lt x
    (show 0 < ε / 3 by positivity)
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp
    (continuous_polynomialSectorEvolution_combination n hn c).continuousAt
    (ε / 3) (by positivity)
  refine ⟨δ, hδ, ?_⟩
  intro s hs
  have hmid := hnear hs
  have hfirst := polynomialSectorEvolution_dist_le n hn s x (polynomialSectorCombination n hn c)
  have hlast := polynomialSectorEvolution_dist_le n hn t (polynomialSectorCombination n hn c) x
  rw [dist_comm (polynomialSectorCombination n hn c) x] at hlast
  have htriangle := dist_triangle (polynomialSectorEvolution n hn s x)
    (polynomialSectorEvolution n hn s (polynomialSectorCombination n hn c))
    (polynomialSectorEvolution n hn t x)
  have htriangle' := dist_triangle
    (polynomialSectorEvolution n hn s (polynomialSectorCombination n hn c))
    (polynomialSectorEvolution n hn t (polynomialSectorCombination n hn c))
    (polynomialSectorEvolution n hn t x)
  linarith

end
end GinibrePoincare
