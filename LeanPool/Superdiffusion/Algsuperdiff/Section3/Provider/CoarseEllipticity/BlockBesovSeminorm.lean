/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincareRHS.SeminormRecurrence
public import LeanPool.HighContrastHomogenization.Support.Deterministic.CoarsePoincareRHS.TerminalBounds

/-!
# BlockBesovSeminorm

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The block negative-Besov seminorm on `R^{2d}`-valued fields

ABK26 Remark `r.cg.poincare.doubled.variables` states the coarse-grained
Poincare inequality `e.CG.Poincare.doubled.vars` for the *doubled* fields `X in
S(cu_m)`.  Its left-hand side is a negative Besov seminorm of two
`R^{2d}`-valued fields, `bfA_0^{1/2} X` and `bfA_0^{-1/2} bfA X`, whereas
CoarseGraining only carries the `Vec d`-valued negative Besov seminorms.  This
module supplies the missing block seminorm -- item (alpha) of the
infrastructure list recorded in `DoubledEnergyIdentity.lean`.

## The seminorm choice

For `F : Vec d -> BlockVec d` we take the **sum** of the two `Vec d`-valued
negative `q = 2` seminorms of the two halves,

```
blockNegativeBesovTwo Q s F
  = [F.1]_{B^{-s}_{2,2}(Q)} + [F.2]_{B^{-s}_{2,2}(Q)} .
```

The display's own left-hand side is already a *sum* of two block seminorms, and
the sum rendering lets the diagonal `bfA_0^{+-1/2}` scaling factor out through
`Vec d`-homogeneity with no combination loss.  The Euclidean block seminorm is
dominated by this one (`sqrt(a^2+b^2) <= a+b`), so any bound proved here is a
bound for it as well.

## Main results

* `blockNegativeBesovTwo` -- the block seminorm, and its nonnegativity.
* `cubeBesovNegativeVectorSeminormTwo_const_smul_add_le` / `_const_smul_sub_le`
  -- the scaled two-term triangle steps, from the scalar homogeneity chain
  `cubeAverage_const_mul -> cubeAverageVec_const_smul ->
  cubeBesovNegativeVectorDepthSeminorm_const_smul ->
  cubeBesovNegativeVectorPartialSeminormTwo_const_smul` and CoarseGraining's
  `sqrt 2`-triangle inequality.
* `blockNegativeBesovTwo_doubledState_le` and
  `blockNegativeBesovTwo_doubledFlux_le` -- the two splits of the display's
  left-hand side into the four single-variable seminorms.

## Scope

It consumes no anchor, no frozen theorem and no external input, and contains no
`sorry`.

## References

* ABK26, `r.cg.poincare.doubled.variables`, display `e.CG.Poincare.doubled.vars`;
  `e.form.of.A.naught`; `e.bfA.magic.swapping`.
-/

namespace Algsuperdiff.Section3.Provider.CoarseEllipticity

open HCPolySupport

noncomputable section

variable {d : ℕ}

/-! ## Scalar homogeneity of the negative `q = 2` Besov seminorm -/

/-- `cubeAverage` is `ℝ`-linear under a constant scalar factor. -/
theorem cubeAverage_const_mul (R : TriadicCube d) (c : ℝ) (f : Vec d → ℝ) :
    cubeAverage R (fun x => c * f x) = c * cubeAverage R f := by
  unfold cubeAverage
  rw [MeasureTheory.integral_const_mul]
  ring

/-- `cubeAverageVec` commutes with a constant scalar `smul`. -/
theorem cubeAverageVec_const_smul (R : TriadicCube d) (c : ℝ) (u : Vec d → Vec d) :
    cubeAverageVec R (fun x => c • u x) = c • cubeAverageVec R u := by
  funext i
  change cubeAverage R (fun x => (c • u x) i) = (c • cubeAverageVec R u) i
  have h1 : (fun x => (c • u x) i) = (fun x => c * u x i) := by
    funext x; simp [Pi.smul_apply, smul_eq_mul]
  rw [h1, cubeAverage_const_mul]
  simp [cubeAverageVec, Pi.smul_apply, smul_eq_mul]

/-- Depth-`j` seminorm homogeneity under a nonnegative constant `smul`. -/
theorem cubeBesovNegativeVectorDepthSeminorm_const_smul (Q : TriadicCube d) (s c : ℝ)
    (hc : 0 ≤ c) (u : Vec d → Vec d) (j : ℕ) :
    cubeBesovNegativeVectorDepthSeminorm Q s (fun x => c • u x) j =
      c * cubeBesovNegativeVectorDepthSeminorm Q s u j := by
  unfold cubeBesovNegativeVectorDepthSeminorm cubeBesovNegativeVectorDepthAverage
  have hrw :
      (fun R => vecNormSq (cubeAverageVec R (fun x => c • u x))) =
        (fun R => vecNormSq (c • cubeAverageVec R u)) := by
    funext R; rw [cubeAverageVec_const_smul]
  rw [hrw,
    sqrt_descendantsAverage_vecNormSq_const_smul_eq Q j c (fun R => cubeAverageVec R u) hc]
  ring

/-- Finite-depth `q = 2` seminorm homogeneity under a nonnegative constant `smul`. -/
theorem cubeBesovNegativeVectorPartialSeminormTwo_const_smul (Q : TriadicCube d) (s : ℝ)
    (N : ℕ) (c : ℝ) (hc : 0 ≤ c) (u : Vec d → Vec d) :
    cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun x => c • u x) =
      c * cubeBesovNegativeVectorPartialSeminormTwo Q s N u := by
  unfold cubeBesovNegativeVectorPartialSeminormTwo
  have hsum :
      (Finset.range (N + 1)).sum
          (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s (fun x => c • u x) j) ^ 2) =
        c ^ 2 *
          (Finset.range (N + 1)).sum
            (fun j => (cubeBesovNegativeVectorDepthSeminorm Q s u j) ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [cubeBesovNegativeVectorDepthSeminorm_const_smul Q s c hc u j]
    ring
  rw [hsum, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_nonneg hc]

/-! ## The two scaled triangle steps -/

/-- `[c (u + v)] <= c sqrt 2 ([u] + [v])`: homogeneity pulls `c` out,
CoarseGraining's `sqrt 2`-triangle bounds the sum. -/
theorem cubeBesovNegativeVectorSeminormTwo_const_smul_add_le (Q : TriadicCube d) (s c : ℝ)
    (hc : 0 ≤ c) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v)
    (hbu : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hbv : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) :
    cubeBesovNegativeVectorSeminormTwo Q s (fun x => c • (u x + v x)) ≤
      c * Real.sqrt 2 *
        (cubeBesovNegativeVectorSeminormTwo Q s u +
          cubeBesovNegativeVectorSeminormTwo Q s v) := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro x ⟨N, rfl⟩
  dsimp only
  rw [cubeBesovNegativeVectorPartialSeminormTwo_const_smul Q s N c hc (fun y => u y + v y)]
  have hpad :=
    cubeBesovNegativeVectorPartialSeminormTwo_add_le_sqrtTwo_mul_add Q s u v hu hv N
  have hu' : cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤
      cubeBesovNegativeVectorSeminormTwo Q s u := le_csSup hbu ⟨N, rfl⟩
  have hv' : cubeBesovNegativeVectorPartialSeminormTwo Q s N v ≤
      cubeBesovNegativeVectorSeminormTwo Q s v := le_csSup hbv ⟨N, rfl⟩
  have hnn2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  calc
    c * cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun y => u y + v y)
        ≤ c * (Real.sqrt 2 *
            (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
              cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) :=
          mul_le_mul_of_nonneg_left hpad hc
    _ ≤ c * (Real.sqrt 2 *
            (cubeBesovNegativeVectorSeminormTwo Q s u +
              cubeBesovNegativeVectorSeminormTwo Q s v)) := by
          refine mul_le_mul_of_nonneg_left ?_ hc
          refine mul_le_mul_of_nonneg_left ?_ hnn2
          linarith
    _ = c * Real.sqrt 2 *
            (cubeBesovNegativeVectorSeminormTwo Q s u +
              cubeBesovNegativeVectorSeminormTwo Q s v) := by ring

/-- `[c (u - v)] <= c sqrt 2 ([u] + [v])`. -/
theorem cubeBesovNegativeVectorSeminormTwo_const_smul_sub_le (Q : TriadicCube d) (s c : ℝ)
    (hc : 0 ≤ c) (u v : Vec d → Vec d)
    (hu : MemVectorL2 (cubeSet Q) u) (hv : MemVectorL2 (cubeSet Q) v)
    (hbu : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N u))
    (hbv : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) :
    cubeBesovNegativeVectorSeminormTwo Q s (fun x => c • (u x - v x)) ≤
      c * Real.sqrt 2 *
        (cubeBesovNegativeVectorSeminormTwo Q s u +
          cubeBesovNegativeVectorSeminormTwo Q s v) := by
  refine csSup_le (Set.range_nonempty _) ?_
  rintro x ⟨N, rfl⟩
  dsimp only
  rw [cubeBesovNegativeVectorPartialSeminormTwo_const_smul Q s N c hc (fun y => u y - v y)]
  have hpsub :=
    cubeBesovNegativeVectorPartialSeminormTwo_sub_le_sqrtTwo_mul_add Q s u v hu hv N
  have hu' : cubeBesovNegativeVectorPartialSeminormTwo Q s N u ≤
      cubeBesovNegativeVectorSeminormTwo Q s u := le_csSup hbu ⟨N, rfl⟩
  have hv' : cubeBesovNegativeVectorPartialSeminormTwo Q s N v ≤
      cubeBesovNegativeVectorSeminormTwo Q s v := le_csSup hbv ⟨N, rfl⟩
  have hnn2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  calc
    c * cubeBesovNegativeVectorPartialSeminormTwo Q s N (fun y => u y - v y)
        ≤ c * (Real.sqrt 2 *
            (cubeBesovNegativeVectorPartialSeminormTwo Q s N u +
              cubeBesovNegativeVectorPartialSeminormTwo Q s N v)) :=
          mul_le_mul_of_nonneg_left hpsub hc
    _ ≤ c * (Real.sqrt 2 *
            (cubeBesovNegativeVectorSeminormTwo Q s u +
              cubeBesovNegativeVectorSeminormTwo Q s v)) := by
          refine mul_le_mul_of_nonneg_left ?_ hc
          refine mul_le_mul_of_nonneg_left ?_ hnn2
          linarith
    _ = c * Real.sqrt 2 *
            (cubeBesovNegativeVectorSeminormTwo Q s u +
              cubeBesovNegativeVectorSeminormTwo Q s v) := by ring

/-! ## The block seminorm -/

/-- **The block negative `q = 2` Besov seminorm** of a `BlockVec d`-valued field:
the sum of the two `Vec d`-valued half-seminorms.  This is the `[.
]_{B^{-s}_{2,2}(Q)}` of `e.CG.Poincare.doubled.vars`. -/
def blockNegativeBesovTwo (Q : TriadicCube d) (s : ℝ) (F : Vec d → BlockVec d) : ℝ :=
  cubeBesovNegativeVectorSeminormTwo Q s (fun x => (F x).1) +
    cubeBesovNegativeVectorSeminormTwo Q s (fun x => (F x).2)

theorem blockNegativeBesovTwo_nonneg (Q : TriadicCube d) (s : ℝ)
    (F : Vec d → BlockVec d) : 0 ≤ blockNegativeBesovTwo Q s F := by
  unfold blockNegativeBesovTwo
  refine add_nonneg ?_ ?_ <;>
    · unfold cubeBesovNegativeVectorSeminormTwo
      refine Real.sSup_nonneg ?_
      rintro y ⟨N, rfl⟩
      exact cubeBesovNegativeVectorPartialSeminormTwo_nonneg _ _ _ _

/-! ## The two splits of `e.CG.Poincare.doubled.vars` -/

/-- **The `bfA_0^{1/2} X` split.**  With `bfA_0 = diag(sigma0, sigma0^{-1})`
(`e.form.of.A.naught` at scalar `sigma0` and `kappa0 = 0`) and
`X = (grad v + grad v*, a grad v - a^t grad v*)` (`e.findSfull`),

```
bfA_0^{1/2} X = (sigma0^{1/2}(grad v + grad v*),
                 sigma0^{-1/2}(a grad v - a^t grad v*)) ,
```

and its block seminorm splits into the four single-variable seminorms with the
honest `sqrt 2` triangle loss. -/
theorem blockNegativeBesovTwo_doubledState_le (Q : TriadicCube d) (s : ℝ)
    (G Gs Fv Fvs : Vec d → Vec d) (sig0Half sig0InvHalf : ℝ)
    (h0 : 0 ≤ sig0Half) (h0' : 0 ≤ sig0InvHalf)
    (hmG : MemVectorL2 (cubeSet Q) G) (hmGs : MemVectorL2 (cubeSet Q) Gs)
    (hmF : MemVectorL2 (cubeSet Q) Fv) (hmFs : MemVectorL2 (cubeSet Q) Fvs)
    (hbG : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N G))
    (hbGs : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N Gs))
    (hbF : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N Fv))
    (hbFs : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N Fvs)) :
    blockNegativeBesovTwo Q s
        (fun x => (sig0Half • (G x + Gs x), sig0InvHalf • (Fv x - Fvs x))) ≤
      Real.sqrt 2 *
        (sig0Half *
            (cubeBesovNegativeVectorSeminormTwo Q s G +
              cubeBesovNegativeVectorSeminormTwo Q s Gs) +
          sig0InvHalf *
            (cubeBesovNegativeVectorSeminormTwo Q s Fv +
              cubeBesovNegativeVectorSeminormTwo Q s Fvs)) := by
  have hg :=
    cubeBesovNegativeVectorSeminormTwo_const_smul_add_le Q s sig0Half h0 G Gs
      hmG hmGs hbG hbGs
  have hf :=
    cubeBesovNegativeVectorSeminormTwo_const_smul_sub_le Q s sig0InvHalf h0' Fv Fvs
      hmF hmFs hbF hbFs
  unfold blockNegativeBesovTwo
  calc
    cubeBesovNegativeVectorSeminormTwo Q s (fun x => sig0Half • (G x + Gs x)) +
        cubeBesovNegativeVectorSeminormTwo Q s (fun x => sig0InvHalf • (Fv x - Fvs x))
        ≤ sig0Half * Real.sqrt 2 *
              (cubeBesovNegativeVectorSeminormTwo Q s G +
                cubeBesovNegativeVectorSeminormTwo Q s Gs) +
            sig0InvHalf * Real.sqrt 2 *
              (cubeBesovNegativeVectorSeminormTwo Q s Fv +
                cubeBesovNegativeVectorSeminormTwo Q s Fvs) := add_le_add hg hf
    _ = Real.sqrt 2 *
          (sig0Half *
              (cubeBesovNegativeVectorSeminormTwo Q s G +
                cubeBesovNegativeVectorSeminormTwo Q s Gs) +
            sig0InvHalf *
              (cubeBesovNegativeVectorSeminormTwo Q s Fv +
                cubeBesovNegativeVectorSeminormTwo Q s Fvs)) := by ring

/-- **The `bfA_0^{-1/2} bfA X` split.**  By the swapping identity
`e.bfA.magic.swapping`,

```
bfA X = (a grad v + a^t grad v*, grad v - grad v*) ,
```

so `bfA_0^{-1/2} bfA X = (sigma0^{-1/2}(a grad v + a^t grad v*),
sigma0^{1/2}(grad v - grad v*))`, and its block seminorm splits into the same
four single-variable seminorms. -/
theorem blockNegativeBesovTwo_doubledFlux_le (Q : TriadicCube d) (s : ℝ)
    (G Gs Fv Fvs : Vec d → Vec d) (sig0Half sig0InvHalf : ℝ)
    (h0 : 0 ≤ sig0Half) (h0' : 0 ≤ sig0InvHalf)
    (hmG : MemVectorL2 (cubeSet Q) G) (hmGs : MemVectorL2 (cubeSet Q) Gs)
    (hmF : MemVectorL2 (cubeSet Q) Fv) (hmFs : MemVectorL2 (cubeSet Q) Fvs)
    (hbG : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N G))
    (hbGs : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N Gs))
    (hbF : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N Fv))
    (hbFs : BddAbove (Set.range fun N : ℕ =>
      cubeBesovNegativeVectorPartialSeminormTwo Q s N Fvs)) :
    blockNegativeBesovTwo Q s
        (fun x => (sig0InvHalf • (Fv x + Fvs x), sig0Half • (G x - Gs x))) ≤
      Real.sqrt 2 *
        (sig0Half *
            (cubeBesovNegativeVectorSeminormTwo Q s G +
              cubeBesovNegativeVectorSeminormTwo Q s Gs) +
          sig0InvHalf *
            (cubeBesovNegativeVectorSeminormTwo Q s Fv +
              cubeBesovNegativeVectorSeminormTwo Q s Fvs)) := by
  have hf :=
    cubeBesovNegativeVectorSeminormTwo_const_smul_add_le Q s sig0InvHalf h0' Fv Fvs
      hmF hmFs hbF hbFs
  have hg :=
    cubeBesovNegativeVectorSeminormTwo_const_smul_sub_le Q s sig0Half h0 G Gs
      hmG hmGs hbG hbGs
  unfold blockNegativeBesovTwo
  calc
    cubeBesovNegativeVectorSeminormTwo Q s (fun x => sig0InvHalf • (Fv x + Fvs x)) +
        cubeBesovNegativeVectorSeminormTwo Q s (fun x => sig0Half • (G x - Gs x))
        ≤ sig0InvHalf * Real.sqrt 2 *
              (cubeBesovNegativeVectorSeminormTwo Q s Fv +
                cubeBesovNegativeVectorSeminormTwo Q s Fvs) +
            sig0Half * Real.sqrt 2 *
              (cubeBesovNegativeVectorSeminormTwo Q s G +
                cubeBesovNegativeVectorSeminormTwo Q s Gs) := add_le_add hf hg
    _ = Real.sqrt 2 *
          (sig0Half *
              (cubeBesovNegativeVectorSeminormTwo Q s G +
                cubeBesovNegativeVectorSeminormTwo Q s Gs) +
            sig0InvHalf *
              (cubeBesovNegativeVectorSeminormTwo Q s Fv +
                cubeBesovNegativeVectorSeminormTwo Q s Fvs)) := by ring

end

end Algsuperdiff.Section3.Provider.CoarseEllipticity
