/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Regularity.StepSevenWireCgMatching

/-!
# StepSevenWireBridge

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# `t.regularity` Step 7d: the summability conversion `B^{-1}_{2,1} ← B^{-t}_{2,2}`

## The maneuver, on the proved carriers

Both sides are already scale-normalized in CoarseGraining, with depth weight
`3^{-s j}` and the same depth average `A_j = ⨍_{R ⊂ Q, depth j} |(F)_R|²`:

```text
  q = 1 at index 1 :  Σ_j 3^{-j}   √A_j          =  3^{-m}‖F‖_{B^{-1}_{2,1}(Q)}
  q = 2 at index t :  (Σ_j (3^{-tj}√A_j)²)^{1/2} =  3^{-tm}‖F‖_{B^{-t}_{2,2}(Q)}
```

Split the weight `3^{-j} = 3^{-(1-t)j}·3^{-tj}` (`depthSeminorm_one_eq`),
Cauchy--Schwarz the scale sum, and evaluate the geometric factor:

```text
  Σ_j 3^{-j}√A_j  ≤  (Σ_j 3^{-2(1-t)j})^{1/2} · (Σ_j (3^{-tj}√A_j)²)^{1/2}
                  ≤  (1 - 3^{-2(1-t)})^{-1/2} · 3^{-tm}‖F‖_{B^{-t}_{2,2}(Q)} .
```

The `3^{-m}` outer weight stays on the `B^{-1}_{2,1}` side and the `3^{-tm}` on
the `B^{-t}_{2,2}` side, because both CoarseGraining carriers put their whole
scale dependence in the depth index `j` and none in the cube; no `3`-power and
no exponent moves anywhere.

## What this discharges

The scale-normalized bridge is the `hbridge` slot in CoarseGraining's
carriers:

```text
  scaleNormalizedNegativeBesovVectorNorm Q 1 (.finite 1) F
    ≤ Cbr(t) · scaleNormalizedNegativeBesovVectorNorm Q t (.finite 2) F ,
```

the left side being exactly what `Algsuperdiff.Section3.Provider.Besov`'s
embedding consumes (through `cubeBesovNegativeVectorSeminorm`, CoarseGraining's
proved
`scaleNormalizedNegativeBesovVectorNorm_finite_one_eq_cubeBesovNegativeVectorSeminorm`)
and the right side exactly what `coarsePoincareRHSTheory` produces.  `hbridge` is
therefore no longer a conditional input.

## References

* ABK26, the summability conversion; Step 7d.
* CoarseGraining,
  `Homogenization/Deterministic/WeakNormInterfaces/Definitions.lean`;
  `Homogenization/Book/Ch03/Theorems/PublicInternalBridges/EndPoints.lean`.
-/

namespace Algsuperdiff.Section4.Provider.Regularity

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch03

noncomputable section

variable {d : ℕ}

/-! ## 1. The geometric factor -/

/-- The partial geometric sum is below its limit. -/
theorem geomPartialSum_le_inv {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, r ^ j ≤ (1 - r)⁻¹ := by
  have h1 : (0 : ℝ) < 1 - r := by linarith only [hr1]
  have hkey : (∑ j ∈ Finset.range n, r ^ j) * (r - 1) = r ^ n - 1 := geom_sum_mul r n
  have hring : (∑ j ∈ Finset.range n, r ^ j) * (1 - r) =
      -((∑ j ∈ Finset.range n, r ^ j) * (r - 1)) := by ring
  have hpow : (0 : ℝ) ≤ r ^ n := pow_nonneg hr0 n
  rw [← one_div, le_div_iff₀ h1]
  linarith only [hring.ge, hring.le, hkey.ge, hkey.le, hpow]

/-- **The conversion constant** `(1 - 3^{-2(1-t)})^{-1/2}`.  At the §4.4 pin `t
= 1/4` it is `(1 - 3^{-3/2})^{-1/2} ≈ 1.1128`, absolute. -/
noncomputable def stepSevenBridgeConst (t : ℝ) : ℝ :=
  Real.sqrt ((1 - Real.rpow (3 : ℝ) (-(1 - t)) ^ 2)⁻¹)

theorem stepSevenBridgeConst_nonneg (t : ℝ) : 0 ≤ stepSevenBridgeConst t :=
  Real.sqrt_nonneg _

/-! ## 2. The weight split -/

/-- **The scale-weight split**: `3^{-j} = 3^{-(1-t)j}·3^{-tj}` on the proved depth
seminorms. -/
theorem depthSeminorm_one_eq (Q : TriadicCube d) (t : ℝ) (F : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthSeminorm Q 1 F j =
      Real.rpow (3 : ℝ) (-(1 - t)) ^ j *
        cubeBesovNegativeVectorDepthSeminorm Q t F j := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hw : Real.rpow (3 : ℝ) (-(1 - t)) ^ j =
      Real.rpow (3 : ℝ) (-(1 - t) * (j : ℝ)) := by
    have hnat : Real.rpow (Real.rpow (3 : ℝ) (-(1 - t))) ((j : ℕ) : ℝ) =
        Real.rpow (3 : ℝ) (-(1 - t)) ^ j := Real.rpow_natCast _ j
    have hmul : Real.rpow (3 : ℝ) (-(1 - t) * ((j : ℕ) : ℝ)) =
        Real.rpow (Real.rpow (3 : ℝ) (-(1 - t))) ((j : ℕ) : ℝ) := Real.rpow_mul h3.le _ _
    rw [← hnat, ← hmul]
  have hadd : Real.rpow (3 : ℝ) (-(1 - t) * (j : ℝ)) * Real.rpow (3 : ℝ) (-t * (j : ℝ)) =
      Real.rpow (3 : ℝ) (-1 * (j : ℝ)) := by
    have he : (-1 : ℝ) * (j : ℝ) = -(1 - t) * (j : ℝ) + -t * (j : ℝ) := by ring
    have h : Real.rpow (3 : ℝ) (-(1 - t) * (j : ℝ) + -t * (j : ℝ)) =
        Real.rpow (3 : ℝ) (-(1 - t) * (j : ℝ)) * Real.rpow (3 : ℝ) (-t * (j : ℝ)) :=
      Real.rpow_add h3 _ _
    rw [he, h]
  unfold cubeBesovNegativeVectorDepthSeminorm
  rw [hw]
  calc Real.rpow (3 : ℝ) (-1 * (j : ℝ)) *
        Real.sqrt (cubeBesovNegativeVectorDepthAverage Q F j)
      = (Real.rpow (3 : ℝ) (-(1 - t) * (j : ℝ)) * Real.rpow (3 : ℝ) (-t * (j : ℝ))) *
          Real.sqrt (cubeBesovNegativeVectorDepthAverage Q F j) := by rw [hadd]
    _ = Real.rpow (3 : ℝ) (-(1 - t) * (j : ℝ)) *
          (Real.rpow (3 : ℝ) (-t * (j : ℝ)) *
            Real.sqrt (cubeBesovNegativeVectorDepthAverage Q F j)) := by ring

/-! ## 3. The conversion at every finite depth -/

/-- **The summability conversion, at every finite depth**.  The scale-sum
Cauchy--Schwarz, with the geometric factor evaluated. -/
theorem cubeBesovNegativeVectorPartialSeminorm_le_bridgeConst_mul (Q : TriadicCube d)
    {t : ℝ} (ht1 : t < 1) (F : Vec d → Vec d) (N : ℕ) :
    cubeBesovNegativeVectorPartialSeminorm Q 1 N F ≤
      stepSevenBridgeConst t * cubeBesovNegativeVectorPartialSeminormTwo Q t N F := by
  set w : ℝ := Real.rpow (3 : ℝ) (-(1 - t)) with hwdef
  have hw0 : 0 < w := Real.rpow_pos_of_pos (by norm_num) _
  have hw1 : w < 1 := by
    rw [hwdef]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [ht1])
  have hwsq0 : (0 : ℝ) ≤ w ^ 2 := sq_nonneg w
  have hwsq1 : w ^ 2 < 1 := by nlinarith only [hw0, hw1]
  -- the geometric factor
  have hgeom : ∑ j ∈ Finset.range (N + 1), (w ^ j) ^ 2 ≤ (1 - w ^ 2)⁻¹ := by
    have hrw : ∀ j : ℕ, (w ^ j) ^ 2 = (w ^ 2) ^ j := by
      intro j; rw [← pow_mul, ← pow_mul, Nat.mul_comm]
    calc ∑ j ∈ Finset.range (N + 1), (w ^ j) ^ 2
        = ∑ j ∈ Finset.range (N + 1), (w ^ 2) ^ j :=
          Finset.sum_congr rfl fun j _ => hrw j
      _ ≤ (1 - w ^ 2)⁻¹ := geomPartialSum_le_inv hwsq0 hwsq1 (N + 1)
  have hgeomSqrt : Real.sqrt (∑ j ∈ Finset.range (N + 1), (w ^ j) ^ 2) ≤
      stepSevenBridgeConst t := by
    rw [stepSevenBridgeConst, ← hwdef]
    exact Real.sqrt_le_sqrt hgeom
  -- the Cauchy--Schwarz step
  have hCS := Real.sum_mul_le_sqrt_mul_sqrt (Finset.range (N + 1))
    (fun j => w ^ j) (fun j => cubeBesovNegativeVectorDepthSeminorm Q t F j)
  have hsplit : cubeBesovNegativeVectorPartialSeminorm Q 1 N F =
      ∑ j ∈ Finset.range (N + 1),
        w ^ j * cubeBesovNegativeVectorDepthSeminorm Q t F j := by
    unfold cubeBesovNegativeVectorPartialSeminorm
    exact Finset.sum_congr rfl fun j _ => depthSeminorm_one_eq Q t F j
  have htwo : cubeBesovNegativeVectorPartialSeminormTwo Q t N F =
      Real.sqrt (∑ j ∈ Finset.range (N + 1),
        cubeBesovNegativeVectorDepthSeminorm Q t F j ^ 2) := rfl
  have hnn : (0 : ℝ) ≤ Real.sqrt (∑ j ∈ Finset.range (N + 1),
      cubeBesovNegativeVectorDepthSeminorm Q t F j ^ 2) := Real.sqrt_nonneg _
  rw [hsplit, htwo]
  exact le_trans hCS (mul_le_mul_of_nonneg_right hgeomSqrt hnn)

/-! ## 4. `hbridge`, discharged -/

/-- **`hbridge` from a uniform bound.**  Whenever `B` dominates every finite-depth
`B^{-t}_{2,2}` partial seminorm of `F`, the note-normalized `B^{-1}_{2,1}`
seminorm is at most `C(t)·B`. -/
theorem stepSevenBesovBridge_of_partialBound (Q : TriadicCube d) {t : ℝ} (ht1 : t < 1)
    (F : Vec d → Vec d) {B : ℝ}
    (hB : ∀ N : ℕ, cubeBesovNegativeVectorPartialSeminormTwo Q t N F ≤ B) :
    cubeBesovNegativeVectorSeminorm Q 1 F ≤ stepSevenBridgeConst t * B := by
  unfold cubeBesovNegativeVectorSeminorm
  refine csSup_le (Set.range_nonempty _) ?_
  rintro x ⟨N, rfl⟩
  exact le_trans (cubeBesovNegativeVectorPartialSeminorm_le_bridgeConst_mul Q ht1 F N)
    (mul_le_mul_of_nonneg_left (hB N) (stepSevenBridgeConst_nonneg t))

theorem stepSevenBesovBridge (Q : TriadicCube d) {t : ℝ} (ht1 : t < 1)
    (F : Vec d → Vec d)
    (hbdd : BddAbove
      (Set.range fun N : ℕ => cubeBesovNegativeVectorPartialSeminormTwo Q t N F)) :
    cubeBesovNegativeVectorSeminorm Q 1 F ≤
      stepSevenBridgeConst t * cubeBesovNegativeVectorSeminormTwo Q t F := by
  refine stepSevenBesovBridge_of_partialBound Q ht1 F ?_
  intro N
  exact le_csSup hbdd (Set.mem_range_self N)

end

end Algsuperdiff.Section4.Provider.Regularity
