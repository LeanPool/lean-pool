/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch03.Theorems.CoarseCaccioppoliRHS.ZeroTraceValue
public import LeanPool.HighContrastHomogenization.Support.Besov.Duality.GlobalComparison
public import LeanPool.HighContrastHomogenization.Support.Sobolev.Foundations.CubeBesovPoincare

/-!
# OscillationPoincare

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# The function-level multiscale Poincare estimate on a triadic cube

This module bounds the normalized `L^2` oscillation of a `W^{1,2}` function on a
triadic cube directly by the multiscale sum of the cube averages of its
gradient, without passing through any negative Sobolev or negative Besov norm of
the gradient.

The manuscript reaches the same right-hand side in two moves: the duality step,
`‖v-(v)_{\cu_m}‖_{\underline L^2(\cu_m)} ≤ C‖∇v‖_{\Hminusul(\cu_m)}`, followed
by the multiscale Poincare inequality of AK.Book, Proposition 1.10.  The first
move is a Necas-type inequality that is not available upstream at the
zero-boundary primitive.  The composition of the two moves, however, is
available upstream in one piece, and that composition is what this module
assembles.

## Route

1. `Homogenization.CubeDualFullVectorPoincareEstimate.of_h1Function`
   (`Homogenization/Sobolev/Foundations/CubeBesovPoincare.lean`) bounds
   `cubeBesovOscillation Q 2 u` by `fullVectorPoincareCubeConstant Q` times the
   coordinate sum of the full negative Besov dual norms
   `cubeBesovDualFullNorm Q 1 2 1 (∂_i u)`.  This is the upstream
   oscillation-by-dual-gradient estimate: its own proof solves the cube Neumann
   Poisson problem and pays the Neumann Calderon-Zygmund constant, so it is the
   analytic content of the manuscript's duality step, at the negative Besov dual
   rather than at `\Hminusul`.  Its constant is dimension-only and independent
   of the cube (`fullVectorPoincareCubeConstant_eq_dimensionConstant`).
2.
   `Homogenization.cubeBesovDualFullNorm_le_note_constant_mul_cubeBesovCircNorm`
   (`Homogenization/Besov/Duality/GlobalComparison.lean`) at `(s,p,q) =
   (1,2,1)` bounds each such dual norm by `3^{d+1}` times the negative circ
   norm `cubeBesovCircNorm Q 1 2 1 (∂_i u)`.  This is the same upstream
   comparison, at the same exponents, that the proved multiscale Poincare
   bridge of `MultiscalePoincareBridge.lean` uses on its own right-hand side.
3. Multiplying by the cube scale weight `3^{-m}` puts the estimate in the
   manuscript's scaled display.
4. The normalized `L^2` square carried by the coarse-grained Caccioppoli
   right-hand side, `Ch03.interiorCaccioppoliParentOscillationL2Sq`, is the
   square of that oscillation, so the last two theorems deliver the Caccioppoli
   right-hand side in multiscale form for an arbitrary Chapter 2 cube solution.

## Upstream sibling

`Homogenization.Book.Ch01.Legacy.h1_descendantLocalFullCircPoincare`
(`Homogenization/Book/Ch01/Theorems/MultiscalePoincare.lean`) composes the same
two upstream steps, with the same constant, on every descendant of a cube at
once, for the parent fluctuation of the function.  This module therefore takes
the two upstream endpoints directly, at the single cube and for the function
itself, rather than specializing that lane.

## Correspondence with the printed display

`MultiscalePoincareBridge.cubeBesovCircDepthWeight_one` records that at `s = 1`
the depth-`j` negative circ weight of a cube of scale `m` is `3^{m-j}`, so
`3^{-m}·cubeBesovCircNorm Q 1 2 1 f` is the printed sum `Σ_{n ≤ m}
3^{-(m-n)}(avsum_z |(f)_{z+\cu_n}|^2)^{1/2}` under the reindexing `n = m - j`.
That identification is a formalization reading of the upstream definitions,
inherited unchanged from the proved bridge and not re-derived here.

The coordinate aggregation here is the plain sum over coordinates of the
per-coordinate multiscale sums.  The printed display aggregates the coordinates
inside each depth term, in the Euclidean norm of the vector average.  Cauchy's
inequality in the coordinate index converts the aggregation used here into the
printed one at the cost of a factor `\sqrt d`, which a dimension-only constant
absorbs; that conversion is not formalized here.

## What is and is not estimated here

The estimate proved here has the multiscale average sum on its right-hand side,
not the manuscript's `3^{-2m}‖∇v‖_{\Hminusul(\cu_m)}^2`.  The two are not
interchangeable: the proved bridge
`MultiscalePoincareBridge.scaledNegHMinusOne_le_multiscaleAverageSum` bounds
the negative Sobolev object by the multiscale sum, so the right-hand side here
is the upstream bound of the printed one and is therefore weaker.  No reverse
comparison is claimed, and no negative Sobolev or negative Besov norm occurs in
any statement of this module.  The bridge's own right-hand side is the
Euclidean coordinate aggregate of the same circ norms, which lies below the
coordinate sum used here; the comparison is therefore in the stated direction
only up to the `√d` coordinate aggregation, and no declaration in this
directory compares the negative Sobolev object to the multiscale average sum
directly.

The centred variant, in which each coordinate circ norm is taken of `∂_i v -
c_i` for a comparison vector `c`, is not proved here.  It follows from the
estimate proved here together with the depthwise triangle inequality `(avsum_z
|(f)_{z+\cu_n}|^2)^{1/2} ≤ (avsum_z |(f-c)_{z+\cu_n}|^2)^{1/2} + |c|` summed
against the circ weights, whose total is at most `(3/2)·3^m`; that step is left
to the consumer, where the `|c|` term meets the term the manuscript already
carries.
-/

namespace Algsuperdiff.Section3.Provider.Besov

open MeasureTheory
open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-! ## The dimensional constant -/

/-- The scale-free dimensional constant of the function-level multiscale
Poincare estimate: the cube full-dual vector Poincare constant times the
upstream full-dual-to-circ comparison constant at `s = 1`. -/
noncomputable def oscillationMultiscalePoincareConstant (d : ℕ) [NeZero d] : ℝ :=
  (d : ℝ) * HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant d *
    (3 : ℝ) ^ ((d : ℝ) + 1)

theorem oscillationMultiscalePoincareConstant_nonneg (d : ℕ) [NeZero d] :
    0 ≤ oscillationMultiscalePoincareConstant d := by
  unfold oscillationMultiscalePoincareConstant
  exact mul_nonneg
    (mul_nonneg (Nat.cast_nonneg d)
      (HCPolySupport.Legacy.cubeNeumannW22CalderonZygmundConstant_nonneg d))
    (Real.rpow_nonneg (by norm_num) _)

variable [NeZero d]

/-! ## The oscillation bound -/

private theorem conjExponent_two_eq : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
  simpa [cubeBesovConjExponent] using
    (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))

/-- **The function-level multiscale Poincare estimate.**  The normalized `L²`
oscillation of a `W^{1,2}` function on a triadic cube is bounded by a scale-free
dimensional constant times the sum over coordinates of the negative circ Besov
norm at `(s,p,q) = (1,2,1)` of the corresponding partial derivative, which is
the manuscript's multiscale sum of gradient cube averages for that coordinate,
weighted by `3^{Q.scale}`. -/
theorem cubeBesovOscillation_le_oscillationMultiscalePoincareConstant_mul_sum_cubeBesovCircNorm
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toFun x) ≤
      oscillationMultiscalePoincareConstant d *
        ∑ i : Fin d, cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) := by
  have hC0 : 0 ≤ fullVectorPoincareCubeConstant Q := fullVectorPoincareCubeConstant_nonneg Q
  have hcoord : ∀ i : Fin d,
      cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) ≤
        (3 : ℝ) ^ ((d : ℝ) + 1) *
          cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) := by
    intro i
    exact cubeBesovDualFullNorm_le_note_constant_mul_cubeBesovCircNorm
      Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) (by norm_num)
      (u.grad_memL2_normalizedCubeMeasure i) (by norm_num) (by norm_num)
      (by rw [conjExponent_two_eq]; norm_num) (by norm_num)
  calc
    cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toFun x)
        ≤ fullVectorPoincareCubeConstant Q *
            ∑ i : Fin d,
              cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) :=
          CubeDualFullVectorPoincareEstimate.of_h1Function Q u
    _ ≤ fullVectorPoincareCubeConstant Q *
            ∑ i : Fin d,
              (3 : ℝ) ^ ((d : ℝ) + 1) *
                cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hcoord i) hC0
    _ = oscillationMultiscalePoincareConstant d *
            ∑ i : Fin d, cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => u.grad x i) := by
          rw [← Finset.mul_sum, oscillationMultiscalePoincareConstant,
            fullVectorPoincareCubeConstant_eq_dimensionConstant Q]
          ring

/-! ## The Caccioppoli right-hand side -/

omit [NeZero d] in
/-- The normalized `L²` square of the centred function on the open cube, which
is the carrier of the Caccioppoli right-hand side, is the square of the cube
oscillation. -/
theorem normalizedL2SqOnSet_openCubeSet_centred_eq_cubeBesovOscillation_sq
    (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) :
    normalizedL2SqOnSet (openCubeSet Q)
        (fun x => u.toFun x - cubeAverage Q (fun x => u.toFun x)) =
      cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u.toFun x) ^ 2 := by
  let : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  have hmem := u.memL2_normalizedCubeMeasure
  have hfluc :
      MemLp (fun x => u.toFun x - cubeAverage Q (fun x => u.toFun x)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    hmem.sub (memLp_const _)
  simpa [cubeBesovOscillation, cubeFluctuation] using!
    normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq Q _ hfluc

/-- **The Caccioppoli right-hand side in multiscale form.**  The parent-cube
oscillation `L²` square that the coarse-grained Caccioppoli estimate leaves on
the right is bounded by the square of the coordinate-summed multiscale average
sum of the solution gradient. -/
theorem interiorCaccioppoliParentOscillationL2Sq_le_sq_sum_cubeBesovCircNorm
    (Q : TriadicCube d) (a : CoeffFamily d) (v : CubeSolution Q a) :
    interiorCaccioppoliParentOscillationL2Sq Q a v ≤
      (oscillationMultiscalePoincareConstant d *
          ∑ i : Fin d,
            cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) (fun x => v.toH1.grad x i)) ^ 2 := by
  have heq :
      interiorCaccioppoliParentOscillationL2Sq Q a v =
        cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => v.toH1.toFun x) ^ 2 :=
    normalizedL2SqOnSet_openCubeSet_centred_eq_cubeBesovOscillation_sq Q v.toH1
  rw [heq]
  exact pow_le_pow_left₀ (cubeBesovOscillation_nonneg Q (2 : ℝ≥0∞) _)
    (cubeBesovOscillation_le_oscillationMultiscalePoincareConstant_mul_sum_cubeBesovCircNorm
      Q v.toH1) 2

end

end Algsuperdiff.Section3.Provider.Besov
