/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.CoarseEllipticity.DoubledPairingGauge
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.MatrixOperatorNorm

/-!
# DoubledPairingCross

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The cross term of Step 2 by the depth-zero Besov identity

Source display in ABK26: the cross-term estimate of Step 2 of
`l.approximate.recurrence.formula`,

```
P_z . fint_{z+cu_n} bfA_m tilde S_z
  <= C | bfAhom^{1/2} P_z | Lambda-tilde 3^n [ bfAhom^{1/2} bfF_z ]_{H^1(z+cu_n)} .
```

## The route

The manuscript reaches this display by Cauchy--Schwarz in the `bfA_m`-form
followed by `e.bound.one.cube.by.lambdas`.  That term is the plain cube
average:

```
cubeBesovNegativeVectorPartialSeminormTwo Q s 0 u = || fint_Q u || ,
```

recorded here as `cubeBesovNegativeVectorPartialSeminormTwo_zero`.  Hence any
envelope `Bu` of the finite-depth negative seminorms of `bfA_0^{-1/2} bfA_m
tilde S_z` already controls its cube average, and the cross term follows from
Cauchy--Schwarz alone.  Strictly fewer inputs than the printed route: no
one-cube ellipticity comparison is spent here.

The statement below is gauge-neutral: it is proved for an arbitrary block
vector `P` and an arbitrary block field `Y`.  A caller instantiates it at `P:=
bfAhom^{1/2} P_z` and `Y:= bfAhom^{-1/2} bfA_m tilde S_z` after applying
`DoubledPairingGauge.blockVecDot_blockGaugeDown_blockGaugeUp`, so that `normP`
becomes the manuscript's `|bfAhom^{1/2} P_z|` in the component-sum rendering.
That instantiation is not performed here.

## Binders

`Bu` is a caller-supplied envelope of the finite-depth negative seminorms.  No
smallness, moment, measurability or integrability proposition occurs: everything
below is pointwise linear algebra and one identity of the seminorm at depth
zero.

## Scope

No anchor, frozen theorem or external input is consumed, and there is no
`sorry`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport
open HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ}

/-! ## The depth-zero identity -/

/-- The depth-zero negative Besov block average is the squared norm of the cube
average. -/
theorem cubeBesovNegativeVectorDepthAverage_zero (Q : TriadicCube d) (u : Vec d → Vec d) :
    cubeBesovNegativeVectorDepthAverage Q u 0 = vecNormSq (cubeAverageVec Q u) := by
  unfold cubeBesovNegativeVectorDepthAverage descendantsAverage
  simp

/-- **The identity.**  The finite-depth negative `q = 2` Besov seminorm at depth
`0` is the norm of the cube average. -/
theorem cubeBesovNegativeVectorPartialSeminormTwo_zero (Q : TriadicCube d) (s : ℝ)
    (u : Vec d → Vec d) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s 0 u = vecNorm (cubeAverageVec Q u) := by
  have hz : Real.rpow (3 : ℝ) (-s * ((0 : ℕ) : ℝ)) = 1 := by simp
  have hnorm : Real.sqrt (vecNormSq (cubeAverageVec Q u)) = vecNorm (cubeAverageVec Q u) := by
    rw [← vecNorm_sq_eq_vecNormSq, Real.sqrt_sq (vecNorm_nonneg _)]
  unfold cubeBesovNegativeVectorPartialSeminormTwo cubeBesovNegativeVectorDepthSeminorm
  rw [Finset.sum_range_one, cubeBesovNegativeVectorDepthAverage_zero, hz, one_mul,
    Real.sq_sqrt (vecNormSq_nonneg _), hnorm]

/-- A negative-seminorm envelope controls the cube average. -/
theorem vecNorm_cubeAverageVec_le_of_partialSeminormTwo_le (Q : TriadicCube d) (s : ℝ)
    (u : Vec d → Vec d) {Bu : ℝ}
    (h : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤ Bu) :
    vecNorm (cubeAverageVec Q u) ≤ Bu := by
  have h0 := h 0
  rwa [cubeBesovNegativeVectorPartialSeminormTwo_zero] at h0

/-! ## The cross term -/

/-- The doubled block norm in the component-sum rendering. -/
def blockVecNormSum (P : BlockVec d) : ℝ := vecNorm P.1 + vecNorm P.2

theorem blockVecNormSum_nonneg (P : BlockVec d) : 0 ≤ blockVecNormSum P :=
  add_nonneg (vecNorm_nonneg _) (vecNorm_nonneg _)

/-- **The cross term by the depth-zero route.**

```
| P . fint_Q Y |  <=  blockVecNormSum P * Bu
```

for any envelope `Bu` of the finite-depth negative `q = 2` Besov seminorms of
the two legs of `Y`.  Per the only ingredients are the depth-zero identity and
Cauchy--Schwarz. -/
theorem abs_blockVecDot_cubeAverage_le (Q : TriadicCube d) (s : ℝ) (P : BlockVec d)
    (Y : Vec d → BlockVec d) {Bu : ℝ}
    (hneg1 : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N
      (fun x => (Y x).1) ≤ Bu)
    (hneg2 : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q s N
      (fun x => (Y x).2) ≤ Bu) :
    |vecDot P.1 (cubeAverageVec Q (fun x => (Y x).1)) +
        vecDot P.2 (cubeAverageVec Q (fun x => (Y x).2))| ≤
      blockVecNormSum P * Bu := by
  have h1 : vecNorm (cubeAverageVec Q (fun x => (Y x).1)) ≤ Bu :=
    vecNorm_cubeAverageVec_le_of_partialSeminormTwo_le Q s _ hneg1
  have h2 : vecNorm (cubeAverageVec Q (fun x => (Y x).2)) ≤ Bu :=
    vecNorm_cubeAverageVec_le_of_partialSeminormTwo_le Q s _ hneg2
  have hcs1 : |vecDot P.1 (cubeAverageVec Q (fun x => (Y x).1))| ≤
      vecNorm P.1 * vecNorm (cubeAverageVec Q (fun x => (Y x).1)) :=
    abs_vecDot_le_vecNorm_mul_vecNorm _ _
  have hcs2 : |vecDot P.2 (cubeAverageVec Q (fun x => (Y x).2))| ≤
      vecNorm P.2 * vecNorm (cubeAverageVec Q (fun x => (Y x).2)) :=
    abs_vecDot_le_vecNorm_mul_vecNorm _ _
  have hb1 : vecNorm P.1 * vecNorm (cubeAverageVec Q (fun x => (Y x).1)) ≤
      vecNorm P.1 * Bu := mul_le_mul_of_nonneg_left h1 (vecNorm_nonneg _)
  have hb2 : vecNorm P.2 * vecNorm (cubeAverageVec Q (fun x => (Y x).2)) ≤
      vecNorm P.2 * Bu := mul_le_mul_of_nonneg_left h2 (vecNorm_nonneg _)
  have hsum := abs_add_le (vecDot P.1 (cubeAverageVec Q (fun x => (Y x).1)))
    (vecDot P.2 (cubeAverageVec Q (fun x => (Y x).2)))
  unfold blockVecNormSum
  linarith only [hsum, hcs1, hcs2, hb1, hb2]

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
