/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.CoarseGrainingP2

/-!
# CoarseGrainingEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `s`-envelope of the coarse-graining right-hand side at the §4.3 slot

## The slot

ABK26's `e.homogenization.L2.interior` is `p.general.coarse.graining` read at
`p = 2` and `m = n` — i.e. at **depth `j = 0`** — with the manuscript exponents
`(s_prop, s_1, s_2) = (s/2, s/4, s)`.

CoarseGraining's package asks `r < s_prop / 2` where the printed proposition
asks only `s_1 < s_prop`.  Keeping the printed error index `s_1 = s/4` (the
index the `q = 1 ← q = 2` comparison converts into the good event's own `s/8`)
therefore forces the comparison exponent **above** the printed `s/2`.

```text
   s_prop := 3s/4 ,      r := s/4 ,      r₂ := s ,      j := 0 ,
```

which satisfies every CoarseGraining hypothesis on the whole anchor range `s ∈
(0,1]` (`3s/4 < 1` even at the endpoint `s = 1`), keeps the printed
`𝓔_{s/4,∞,1}`, and costs only the harmless factor `4/3` on the `s_prop^{-1}`
prefactor: the comparison exponent enters CoarseGraining's right-hand side
**only** through `s_prop⁻¹`.

## The honest envelope (reported, not hidden)

The `s`-powers proved below are

| term | printed  | proved here |
| --- | --- | --- |
| `𝓔 ·  ν^{1/2}‖∇u‖` | `C s^{-3/2}` | `(1024/3) s^{-4}` |
| forcing `[g]_{H^s}` | `C s^{-11/2}` | `(16384/3) s^{-6}` |

Both are *weaker* than the printed envelopes, so nothing here may be presented
as the printed display.  Two of the three forcing summands land on the printed
`s^{-11/2}` exactly; only the `|a₀| λ^{-1}_{r/2,2}` summand costs `s^{-6}`.

## The forcing bracket

The printed proposition writes the forcing prefactor as `(1 + 𝓔²_{s_1/2,∞,2})`;
CoarseGraining writes it through the coarse-grained ellipticity factors.  Both
are capped by `C(d)` on the good event `𝒢` — the first by
`e.good.set.giveth.v2`, the second by `e.bound.Lambdas.by.Es.v2` (the
`l.mathcal.E.to.Lambdas` leg proved in `LambdaCaps.lean`/`GoodEventCaps.lean`)
— so the two forms are interchangeable exactly where §4.3 uses them.
`coarseGrainingForceBracket` below is CoarseGraining's form, carried
explicitly.

## References

* ABK26, `p.general.coarse.graining`.
* ABK26, `e.homogenization.L2.interior`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book

noncomputable section

variable {d : ℕ}

/-! ## 1. The two development-facing right-hand terms -/

/-- The energy term of `e.homogenization.L2.interior`, at depth `0`:
`|a₀|^{1/2} 𝓔_{r,∞,1}(Q; a, a₀) ‖∇u‖_{a,L²(Q)}`.  For the ABK operator
`a_L = ν Id + κ_L` with `κ_L` antisymmetric, the coefficient-energy norm on the
right *is* `ν^{1/2}‖∇u‖_{L²}`, which is what the display prints. -/
def coarseGrainingEnergyTerm [NeZero d] (Q : TriadicCube d) (a : Ch03.CoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) (r : ℝ)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) : ℝ :=
  Ch03.constantCoeffMatrixNormHalf a0 *
    Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r 0 *
    Ch03.h1EnergyNormOnCube Q a u

/-- CoarseGraining's forcing bracket, the replacement for the printed `(1 +
𝓔²_{s_1/2,∞,2})`: it is built from the coarse-grained ellipticity factors
`λ^{-1/2}_{r/2,2}`, `Λ^{1/2}_{r/2,2}` and `λ^{-1}_{r/2,2}`. -/
def coarseGrainingForceBracket [NeZero d] (Q : TriadicCube d) (a : Ch03.CoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) (r : ℝ) : ℝ :=
  Ch03.constantCoeffMatrixNormHalf a0 *
      Ch03.poincareLowerEllipticityFactor Q a (r / 2) (.finite 2) *
      Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r 0 +
    Ch03.poincareUpperEllipticityFactor Q a (r / 2) (.finite 2) *
      Ch03.poincareLowerEllipticityFactor Q a (r / 2) (.finite 2) +
    Ch03.constantCoeffMatrixNorm a0 *
      Real.rpow (Ch02.lambdaSq Q (r / 2) (.finite 2) a) (-1 : ℝ)

/-- The forcing term of `e.homogenization.L2.interior`, at depth `0`. -/
def coarseGrainingForceTerm [NeZero d] (Q : TriadicCube d) (a : Ch03.CoeffFamily d)
    (a0 : Ch03.ConstantCoeffMatrix d) (r r₂ : ℝ) (g : Vec d → Vec d) : ℝ :=
  coarseGrainingForceBracket Q a a0 r *
    Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q r₂ g

/-! ## 2. Nonnegativity -/

theorem matrixNorm_nonneg (A : Mat d) : 0 ≤ Ch02.matrixNorm A := by
  rw [Ch02.matrixNorm]
  exact norm_nonneg _

theorem constantCoeffMatrixNormHalf_nonneg (a0 : Ch03.ConstantCoeffMatrix d) :
    0 ≤ Ch03.constantCoeffMatrixNormHalf a0 := by
  rw [Ch03.constantCoeffMatrixNormHalf]
  exact Real.rpow_nonneg (matrixNorm_nonneg a0.matrix) _

theorem constantCoeffMatrixNorm_nonneg (a0 : Ch03.ConstantCoeffMatrix d) :
    0 ≤ Ch03.constantCoeffMatrixNorm a0 :=
  matrixNorm_nonneg a0.matrix

theorem h1EnergyNormOnCube_nonneg (Q : TriadicCube d) (a : Ch03.CoeffFamily d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    0 ≤ Ch03.h1EnergyNormOnCube Q a u := by
  rw [Ch03.h1EnergyNormOnCube]
  exact Real.sqrt_nonneg _

/-- Nonnegativity of the coarse-graining homogenization error at depth `j`. -/
theorem coarseGrainingHomogenizationErrorAtDepth_nonneg [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d) {r : ℝ} (hr : 0 < r)
    (j : ℕ) :
    0 ≤ Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r j := by
  rw [Ch03.coarseGrainingHomogenizationErrorAtDepth]
  exact Ch02.finsetSupReal_nonneg (descendantsAtDepth Q j) _
    fun R _hR => Ch02.HomogenizationErrorOnCube_infinity_one_nonneg R a a0.matrix hr

theorem poincareLowerEllipticityFactor_nonneg [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) {t : ℝ} (ht : 0 < t) :
    0 ≤ Ch03.poincareLowerEllipticityFactor Q a t (.finite 2) := by
  rw [Ch03.poincareLowerEllipticityFactor]
  exact Real.rpow_nonneg (Ch02.lambdaSq_finite_pos Q a ht (by norm_num)).le _

theorem poincareUpperEllipticityFactor_nonneg [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) {t : ℝ} (ht : 0 < t) :
    0 ≤ Ch03.poincareUpperEllipticityFactor Q a t (.finite 2) := by
  rw [Ch03.poincareUpperEllipticityFactor]
  exact Real.rpow_nonneg (Ch02.LambdaSq_finite_pos Q a ht (by norm_num)).le _

theorem coarseGrainingEnergyTerm_nonneg [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d) {r : ℝ} (hr : 0 < r)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    0 ≤ coarseGrainingEnergyTerm Q a a0 r u :=
  mul_nonneg (mul_nonneg (constantCoeffMatrixNormHalf_nonneg a0)
    (coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 hr 0))
    (h1EnergyNormOnCube_nonneg Q a u)

theorem coarseGrainingForceBracket_nonneg [NeZero d] (Q : TriadicCube d)
    (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d) {r : ℝ} (hr : 0 < r) :
    0 ≤ coarseGrainingForceBracket Q a a0 r := by
  have hr2 : (0 : ℝ) < r / 2 := by linarith only [hr]
  have h1 : 0 ≤ Ch03.constantCoeffMatrixNormHalf a0 *
      Ch03.poincareLowerEllipticityFactor Q a (r / 2) (.finite 2) *
      Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r 0 :=
    mul_nonneg (mul_nonneg (constantCoeffMatrixNormHalf_nonneg a0)
      (poincareLowerEllipticityFactor_nonneg Q a hr2))
      (coarseGrainingHomogenizationErrorAtDepth_nonneg Q a a0 hr 0)
  have h2 : 0 ≤ Ch03.poincareUpperEllipticityFactor Q a (r / 2) (.finite 2) *
      Ch03.poincareLowerEllipticityFactor Q a (r / 2) (.finite 2) :=
    mul_nonneg (poincareUpperEllipticityFactor_nonneg Q a hr2)
      (poincareLowerEllipticityFactor_nonneg Q a hr2)
  have h3 : 0 ≤ Ch03.constantCoeffMatrixNorm a0 *
      Real.rpow (Ch02.lambdaSq Q (r / 2) (.finite 2) a) (-1 : ℝ) :=
    mul_nonneg (constantCoeffMatrixNorm_nonneg a0)
      (Real.rpow_nonneg (Ch02.lambdaSq_finite_pos Q a hr2 (by norm_num)).le _)
  rw [coarseGrainingForceBracket]
  linarith only [h1, h2, h3]

/-! ## 3. Depth-zero weights -/

theorem coarseGrainingDepthWeight_zero (r : ℝ) : Ch03.coarseGrainingDepthWeight r 0 = 1 := by
  rw [Ch03.coarseGrainingDepthWeight]
  norm_num

theorem coarseGrainingDepthHalfWeight_zero (r : ℝ) :
    Ch03.coarseGrainingDepthHalfWeight r 0 = 1 := by
  rw [Ch03.coarseGrainingDepthHalfWeight]
  norm_num

theorem coarseGrainingDepthInvWeight_zero (r : ℝ) :
    Ch03.coarseGrainingDepthInvWeight r 0 = 1 := by
  rw [Ch03.coarseGrainingDepthInvWeight, coarseGrainingDepthWeight_zero, inv_one]

/-! ## 4. The depth-zero right-hand side, unpacked -/

/-- CoarseGraining's right-hand side at depth `0`, with its three forcing summands
displayed and their individual `r`-powers intact. -/
theorem generalCoarseGrainingL2TwoExponentRHS_depth_zero_eq [NeZero d]
    (Q : TriadicCube d) (a : Ch03.CoeffFamily d) (a0 : Ch03.ConstantCoeffMatrix d)
    (t r r₂ : ℝ) (g : Vec d → Vec d)
    (u : H1Function (Ch02.cubeDomain Q : Set (Vec d))) :
    Ch03.generalCoarseGrainingL2TwoExponentRHS 1 Q a a0 t r r₂ 0 g u =
      t⁻¹ * (r⁻¹) ^ (2 : ℕ) * ((1 / 2 : ℝ) - r)⁻¹ *
        (r⁻¹ * coarseGrainingEnergyTerm Q a a0 r u +
          (Real.rpow r (-(5 / 2 : ℝ)) *
                (Ch03.constantCoeffMatrixNormHalf a0 *
                  Ch03.poincareLowerEllipticityFactor Q a (r / 2) (.finite 2) *
                  Ch03.coarseGrainingHomogenizationErrorAtDepth Q a a0 r 0) +
              Real.rpow r (-(5 / 2 : ℝ)) *
                (Ch03.poincareUpperEllipticityFactor Q a (r / 2) (.finite 2) *
                  Ch03.poincareLowerEllipticityFactor Q a (r / 2) (.finite 2)) +
              Real.rpow r (-3 : ℝ) *
                (Ch03.constantCoeffMatrixNorm a0 *
                  Real.rpow (Ch02.lambdaSq Q (r / 2) (.finite 2) a) (-1 : ℝ))) *
            Ch03.scaleNormalizedPositiveBesovVectorSeminormTwo Q r₂ g) := by
  rw [Ch03.generalCoarseGrainingL2TwoExponentRHS,
    Ch03.generalCoarseGrainingL2TwoExponentFluxDefectRHS,
    coarseGrainingDepthWeight_zero, coarseGrainingDepthHalfWeight_zero,
    coarseGrainingDepthInvWeight_zero, coarseGrainingEnergyTerm]
  ring

end

end Algsuperdiff.Section4.Provider.ExcessDecay
