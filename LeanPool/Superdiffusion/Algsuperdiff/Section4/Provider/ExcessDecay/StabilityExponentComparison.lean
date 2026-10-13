/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.StabilityIndexCube

/-!
# StabilityExponentComparison

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `q = 1 ← q = 2` comparison of the homogenization error

This module proves the manuscript's own scale-exponent comparison
`e.compareEqs` (ABK26) at the endpoint pair `(q, p) = (1, 2)`:

```
𝓔_{s,∞,1}(Q; a, a₀)  ≤  𝓔_{s/2,∞,2}(Q; a, a₀) ,          s > 0 ,
```

with **no constant**.  The printed statement is
`𝓔_{s,∞,q} ≤ 𝓔_{sq/p,∞,p}` for `1 ≤ q ≤ p < ∞`; only the pair the §4.3 chain
uses is formalized here.

## Why this matters for §4.3

**The comparison is not missing from the manuscript**: `e.compareEqs`, proved
in Section 2 by Jensen's inequality immediately before `l.lambdas.stability`,
supplies it — and it proves on the index `s/8` rather than the printed `s/6`:

```
𝓔_{s/4,∞,1}(W)  ≤  𝓔_{s/8,∞,2}(W)          (this module, at `s := s/4`)
```

which is *exactly* the index at which the frozen annular anchor delivers its
cap.  So the printed intermediate rung `𝓔_{s/6,∞,2}` is removable, and with it
the only place where the §4.3 chain used `l.lambdas.stability` for an
index/exponent change.

Recorded deviation from print: the printed first inequality of
`e.good.set.giveth.v2` (`𝓔_{s/4,∞,1} ≤ C 𝓔_{s/6,∞,2}` at the *same* cube) is
**not** proved here and is not derivable from Jensen plus index monotonicity —
the index `s/6` is too large for the Jensen pairing and too small for
antitonicity.  It is true, by a weighted Cauchy--Schwarz with an absolute
constant, but it is not needed: the route through `s/8` reaches the same
endpoint with constant `1`.

## The proof, in one line

Both sides are the same weighted series, because the weights agree:

```
w_{s,1}(l) = (1 − 3^{-s}) 3^{-sl} = w_{s/2,2}(l),
𝓔_{s,∞,1}   = ∑_l w_{s,1}(l) · Rₗ,        𝓔_{s/2,∞,2}² = ∑_l w_{s,1}(l) · Rₗ² ,
```

and `∑_l w_{s,1}(l) = 1`.  With `A := 𝓔_{s/2,∞,2}` the pointwise inequality
`2 A Rₗ ≤ Rₗ² + A²` (i.e. `0 ≤ (Rₗ − A)²`) summed against the unit-mass weights
gives `∑ w R ≤ (A² + A²)/(2A) = A`.  No Cauchy--Schwarz machinery is needed.

## References

* ABK26, `e.compareEqs`, (statement, Jensen proof); its `Λ`/`λ` siblings
  `e.compareLambdaqs`.
* ABK26, `e.good.set.giveth.v2`.
* ABK26, `d.mathcal.E`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02

noncomputable section

variable {d : ℕ} [NeZero d]

/-! ## 1. The two series and their common weights -/

/-- The `(∞,2)` weight at index `s/2` is the `(∞,1)` weight at index `s`. -/
private theorem weight_two_half_eq (s : ℝ) (l : ℕ) :
    Ch02.geometricWeight (s / 2) 2 l = Ch02.geometricWeight s 1 l := by
  have h := HCPolySupport.geometricWeight_eq_mul_one (s / 2) 2 l
  have hss : s / 2 * 2 = s := by ring
  rw [hss] at h
  simpa [Ch02.geometricWeight_eq_old] using h

/-- The shells of `𝓔_{s/2,∞,2}²` are the squares of the `(∞,1)` scale
responses, and the weights are the `(∞,1)` weights. -/
private theorem sq_eq_tsum_weight_mul_sq (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    HomogenizationErrorOnCube Q (s / 2) .infinity (.finite 2) a a0 ^ 2 =
      ∑' l : ℕ, Ch02.geometricWeight s 1 l *
        scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity a a0 ^ 2 := by
  rw [homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q (by linarith only [hs]) a a0]
  refine tsum_congr fun l => ?_
  rw [weight_two_half_eq s l,
    scaleResponseAtScale_infinity_sq_eq Q (sub_le_self _ (Int.natCast_nonneg l)) a a0]

/-- The squared-response series converges. -/
private theorem summable_weight_mul_sq (Q : TriadicCube d) (a : TriadicCoeffFamily d)
    (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    Summable fun l : ℕ => Ch02.geometricWeight s 1 l *
      scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity a a0 ^ 2 := by
  have hbase : Summable fun l : ℕ => HCPolySupport.geometricWeight s 1 l *
      maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ)) a a0 :=
    HCPolySupport.summable_geometricWeight_mul_of_nonneg_of_le
      (s := s) (q := 1) (C := normalizedBlockResponseUniformBound Q a a0)
      (by linarith only [hs])
      (fun l => maxDescendantNormalizedBlockResponseAtScale_nonneg Q
        (sub_le_self _ (Int.natCast_nonneg l)) a a0)
      (fun l => maxDescendantNormalizedBlockResponseAtScale_le_uniform Q
        (sub_le_self _ (Int.natCast_nonneg l)) a a0)
  refine hbase.congr fun l => ?_
  rw [Ch02.geometricWeight_eq_old,
    scaleResponseAtScale_infinity_sq_eq Q (sub_le_self _ (Int.natCast_nonneg l)) a a0]

/-! ## 2. `e.compareEqs` at `(q, p) = (1, 2)` -/

/-- **The manuscript's `e.compareEqs` at the endpoint pair `(q, p) = (1, 2)`.**

```
𝓔_{s,∞,1}(Q; a, a₀)  ≤  𝓔_{s/2,∞,2}(Q; a, a₀) .
```

Same cube, same coefficient family, same comparator, no constant: only the
scale-exponent and the index move, and they move together (`s ↦ s/2` when
`q = 1 ↦ 2`), which is exactly Jensen's inequality for the unit-mass geometric
weights.

At `s := s/4` this reads `𝓔_{s/4,∞,1} ≤ 𝓔_{s/8,∞,2}`, i.e. it converts the
`q = 1` quantity of the coarse-graining display `e.homogenization.L2.interior`
into the `q = 2` quantity at the annular anchor's own index `s/8`. -/
theorem homogenizationErrorOnCube_infinity_one_le_infinity_two_half (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 ≤
      HomogenizationErrorOnCube Q (s / 2) .infinity (.finite 2) a a0 := by
  classical
  set A : ℝ := HomogenizationErrorOnCube Q (s / 2) .infinity (.finite 2) a a0 with hA
  set W : ℕ → ℝ := fun l => Ch02.geometricWeight s 1 l with hW
  set R : ℕ → ℝ := fun l => scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity a a0 with hR
  have hWpos : ∀ l : ℕ, 0 < W l := by
    intro l
    simpa [hW, Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_pos (s := s) (q := 1) l (by linarith only [hs])
  have hWsum : Summable W := by
    simpa [hW, Ch02.geometricWeight_eq_old] using
      HCPolySupport.summable_geometricWeight (s := s) (q := 1) (by linarith only [hs])
  have hWone : ∑' l : ℕ, W l = 1 := by
    simpa [hW, Ch02.geometricWeight_eq_old] using
      HCPolySupport.tsum_geometricWeight_eq_one (s := s) (q := 1) (by linarith only [hs])
  have hRnonneg : ∀ l : ℕ, 0 ≤ R l := fun l =>
    scaleResponseAtScale_infinity_nonneg Q (sub_le_self _ (Int.natCast_nonneg l)) a a0
  have hAnonneg : 0 ≤ A :=
    homogenizationErrorOnCube_infinity_two_nonneg Q a a0 (by linarith only [hs])
  have hAsq : A ^ 2 = ∑' l : ℕ, W l * R l ^ 2 := sq_eq_tsum_weight_mul_sq Q a a0 hs
  have hsumSq : Summable fun l : ℕ => W l * R l ^ 2 := summable_weight_mul_sq Q a a0 hs
  have hsumOne : Summable fun l : ℕ => W l * R l := by
    have hbase := Ch02.summable_homogenizationErrorOnCube_infinity_one_terms Q a a0 hs
    exact hbase
  have hgoal : HomogenizationErrorOnCube Q s .infinity (.finite 1) a a0 =
      ∑' l : ℕ, W l * R l := homogenizationErrorOnCube_infinity_one_eq_tsum Q s a a0
  rw [hgoal]
  rcases eq_or_lt_of_le hAnonneg with hA0 | hApos
  · -- `A = 0` forces every response to vanish
    have hzero : ∀ l : ℕ, W l * R l ^ 2 = 0 := by
      intro l
      have hle : W l * R l ^ 2 ≤ ∑' k : ℕ, W k * R k ^ 2 :=
        hsumSq.le_tsum l fun k _ => mul_nonneg (hWpos k).le (by positivity)
      have hsum0 : ∑' k : ℕ, W k * R k ^ 2 = 0 := by
        rw [← hAsq, ← hA0]
        norm_num
      have hnn : 0 ≤ W l * R l ^ 2 := mul_nonneg (hWpos l).le (by positivity)
      linarith only [hle, hsum0, hnn]
    have hR0 : ∀ l : ℕ, R l = 0 := by
      intro l
      have h := hzero l
      rcases mul_eq_zero.1 h with hw | hr
      · exact absurd hw (hWpos l).ne'
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hr
    have hfun : (fun l : ℕ => W l * R l) = fun _ : ℕ => (0 : ℝ) := by
      funext l
      rw [hR0 l]
      ring
    rw [hfun, tsum_zero, ← hA0]
  · -- `A > 0`: sum the pointwise `2 A R ≤ R² + A²`
    have h2A : 0 < 2 * A := by linarith only [hApos]
    have hcomp : Summable fun l : ℕ =>
        (2 * A)⁻¹ * (W l * R l ^ 2) + A / 2 * W l :=
      (hsumSq.mul_left _).add (hWsum.mul_left _)
    have hterm : ∀ l : ℕ,
        W l * R l ≤ (2 * A)⁻¹ * (W l * R l ^ 2) + A / 2 * W l := by
      intro l
      have hsq : (R l - A) ^ 2 = R l ^ 2 - 2 * A * R l + A ^ 2 := by ring
      have hkey : 2 * A * R l ≤ R l ^ 2 + A ^ 2 := by
        linarith only [sq_nonneg (R l - A), hsq]
      have hmul : W l * (2 * A * R l) ≤ W l * (R l ^ 2 + A ^ 2) :=
        mul_le_mul_of_nonneg_left hkey (hWpos l).le
      have hexp : 2 * A * ((2 * A)⁻¹ * (W l * R l ^ 2) + A / 2 * W l) =
          W l * R l ^ 2 + A ^ 2 * W l := by
        field_simp
      refine le_of_mul_le_mul_left ?_ h2A
      rw [hexp]
      linarith only [hmul]
    have hle : ∑' l : ℕ, W l * R l ≤
        ∑' l : ℕ, ((2 * A)⁻¹ * (W l * R l ^ 2) + A / 2 * W l) :=
      Summable.tsum_le_tsum hterm hsumOne hcomp
    have hval : ∑' l : ℕ, ((2 * A)⁻¹ * (W l * R l ^ 2) + A / 2 * W l) = A := by
      rw [Summable.tsum_add (hsumSq.mul_left _) (hWsum.mul_left _), hsumSq.tsum_mul_left,
        hWsum.tsum_mul_left, hWone, ← hAsq]
      field_simp
      ring
    linarith only [hle, hval]

end

end Algsuperdiff.Section4.Provider.ExcessDecay
