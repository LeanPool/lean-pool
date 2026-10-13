/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.InfinityOne
public import LeanPool.HighContrastHomogenization.Support.Book.Ch02.Theorems.HomogenizationError.Finite

/-!
# StabilityIndexCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Index and one-scale cube stability of the `(∞,2)` homogenization error

Two elementary stability properties of CoarseGraining's `𝓔_{s,∞,2}` at a fixed
coefficient family and comparator, both derived here (not assumed) at the `q =
2` exponent that the Section 4.3 good-event caps use:

* **index antitonicity** — `𝓔` *decreases* when its first index increases;
* **one-scale cube descent** — passing from a cube to a triadic descendant
  costs the single factor `3^{s·(depth)}`.

## What this module does and does not do

`l.lambdas.stability` is a **one-scale descent for an arbitrary translate**:
its target cube is `x + □_{-1}` for a real `x` with `x + □_{-1} ⊆ □_0`, and its
proof is a greedy Whitney-type decomposition of that off-grid cube by *grid*
subcubes at all deeper scales, combined with subadditivity of `σ_*^{-1}` and a
packing count.  Nothing of that kind is proved here.

What is proved here is the **grid** case: the target cube is a triadic
descendant, so the shell maxima of the smaller cube are literally a subfamily
of the shell maxima of the larger one and the whole estimate is the
reindexing `w_{s,2}(l) = 3^{2s·h} w_{s,2}(l+h)` of the geometric weights.  In
that case the constant is not the printed `C(d)/(1−2s)` but the explicit
`3^{s·h}`, which for a one-scale descent (`h = 1`) and `s ≤ 1` is at most `3`.

It is not smuggled in anywhere below: every statement quantifies over
`descendantsAtScale`, never over translates.

## Monotonicity directions, derived

Both directions matter for the §4.3 chain and both are read off the same shell
representation

```
𝓔_{s,∞,2}(Q; a, a₀)²  =  ∑_{l≥0} w_{s,2}(l) · M_l(Q),
      w_{s,2}(l) = (1 − 3^{-2s}) 3^{-2sl},   M_l(Q) = max_{R ⊆ Q, scale Q.scale−l} J(R),
```

in which `l ↦ M_l(Q)` is **nondecreasing** (deeper shells maximize over more
cubes) and `∑_l w_{s,2}(l) = 1`:

* larger `s` concentrates the unit mass on small `l`, i.e. on the *smaller*
  terms of a nondecreasing sequence, hence `𝓔` is **antitone in the index**;
* descending to a depth-`h` descendant deletes the `h` shallowest shells and
  shifts the rest, hence the factor `3^{2s·h}` on the square.

The first item is the one the §4.3 chain needs: the annular anchor delivers the
cap at the *small* index `s/8`, while the consumers ask for the *larger*
indices `s/6` and `s/4`, so the index change is **free** (constant `1`) and in
particular needs no part of `l.lambdas.stability`.

## Main results

* `homogenizationErrorOnCube_infinity_two_nonneg` — `0 ≤ 𝓔_{s,∞,2}`.
* `homogenizationErrorOnCube_infinity_two_le_of_lt` — index antitonicity.
* `homogenizationErrorOnCube_infinity_two_le_of_mem_descendantsAtScale` — the
  fixed-index descent, with factor `3^{s·depth}`.
* `homogenizationErrorOnCube_infinity_two_descendant_index_le` — the composite
  the §4.3 caps chain performs.

## References

* ABK26, `e.mathcalE.stability.applied`.
* ABK26, `l.lambdas.stability`.
* ABK26, `d.mathcal.E`; the shell display.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02

noncomputable section

/-! ## 0. Two arithmetic helpers -/

/-- Squares may be cancelled between nonnegative reals. -/
private theorem le_of_sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a ^ 2 ≤ b ^ 2) : a ≤ b :=
  calc a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt h
    _ = b := Real.sqrt_sq hb

/-- The square of a real power of `3`. -/
private theorem rpow_three_sq (y : ℝ) :
    Real.rpow (3 : ℝ) y ^ 2 = Real.rpow (3 : ℝ) (y * 2) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hadd : Real.rpow (3 : ℝ) (y + y) = Real.rpow (3 : ℝ) y * Real.rpow (3 : ℝ) y := by
    simpa using Real.rpow_add h3 y y
  have hy : y * 2 = y + y := by ring
  rw [hy, hadd]
  ring

variable {d : ℕ} [NeZero d]

/-! ## 1. The shell series of the `(∞,2)` square -/

/-- Every shell of the `(∞,2)` square is nonnegative. -/
private theorem shell_nonneg (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d)
    (l : ℕ) :
    0 ≤ maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ)) a a0 :=
  maxDescendantNormalizedBlockResponseAtScale_nonneg Q
    (sub_le_self _ (Int.natCast_nonneg l)) a a0

/-- Deeper shells maximize over more cubes, so the shell sequence is monotone. -/
private theorem shell_monotone (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d) :
    Monotone fun l : ℕ =>
      maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ)) a a0 := by
  intro m n hmn
  have hmnz : (m : ℤ) ≤ (n : ℤ) := by exact_mod_cast hmn
  exact maxDescendantNormalizedBlockResponseAtScale_le_of_le Q
    (by linarith only [hmnz] : Q.scale - (n : ℤ) ≤ Q.scale - (m : ℤ))
    (sub_le_self _ (Int.natCast_nonneg m)) a a0

/-- The shell series converges: every shell sits below the one-cube uniform
response bound of `Q`. -/
private theorem summable_shell (Q : TriadicCube d) (a : TriadicCoeffFamily d) (a0 : Mat d)
    {s : ℝ} (hs : 0 < s) :
    Summable fun l : ℕ =>
      HCPolySupport.geometricWeight s 2 l *
        maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ)) a a0 :=
  HCPolySupport.summable_geometricWeight_mul_of_nonneg_of_le
    (s := s) (q := 2) (C := normalizedBlockResponseUniformBound Q a a0)
    (by linarith only [hs]) (fun l => shell_nonneg Q a a0 l)
    (fun l => maxDescendantNormalizedBlockResponseAtScale_le_uniform Q
      (sub_le_self _ (Int.natCast_nonneg l)) a a0)

theorem homogenizationErrorOnCube_infinity_two_nonneg (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ} (hs : 0 < s) :
    0 ≤ HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 := by
  have hterm : ∀ l : ℕ,
      0 ≤ Ch02.geometricWeight s 2 l *
        Real.rpow (scaleResponseAtScale Q (Q.scale - (l : ℤ)) .infinity a a0) 2 := by
    intro l
    refine mul_nonneg ?_ (Real.rpow_nonneg ?_ _)
    · simpa [Ch02.geometricWeight_eq_old] using
        HCPolySupport.geometricWeight_nonneg (s := s) (q := 2) l (by linarith only [hs])
    · exact scaleResponseAtScale_infinity_nonneg Q
        (sub_le_self _ (Int.natCast_nonneg l)) a a0
  change 0 ≤ Ch02.HomogenizationErrorFinite Q Q.scale s .infinity 2 a a0
  unfold Ch02.HomogenizationErrorFinite
  exact Real.rpow_nonneg (tsum_nonneg hterm) _

/-! ## 2. Index antitonicity -/

/-- **`𝓔_{·,∞,2}` is antitone in its first index.**

For `0 < t < s` the smaller index dominates:

```
𝓔_{s,∞,2}(Q; a, a₀)  ≤  𝓔_{t,∞,2}(Q; a, a₀) .
```

This is the direction the §4.3 caps chain needs — the annular anchor delivers
its cap at `s/8`, the consumers ask for `s/6` and `s/4` — and it costs no
constant at all.  It is the `q = 2` sibling of CoarseGraining's
`Ch02.homogenizationErrorOnCube_infinity_one_le_of_lt`. -/
theorem homogenizationErrorOnCube_infinity_two_le_of_lt (Q : TriadicCube d)
    (a : TriadicCoeffFamily d) (a0 : Mat d) {t s : ℝ} (ht : 0 < t) (hts : t < s) :
    HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 ≤
      HomogenizationErrorOnCube Q t .infinity (.finite 2) a a0 := by
  have hs : 0 < s := ht.trans hts
  refine le_of_sq_le_sq_of_nonneg (homogenizationErrorOnCube_infinity_two_nonneg Q a a0 hs)
    (homogenizationErrorOnCube_infinity_two_nonneg Q a a0 ht) ?_
  rw [homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs a a0,
    homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q ht a a0]
  simp only [Ch02.geometricWeight_eq_old]
  exact HCPolySupport.tsum_geometricWeight_le_of_monotone
    (shell_monotone Q a a0) (shell_nonneg Q a a0) (by norm_num) ht hts
    (summable_shell Q a a0 ht)

/-! ## 3. One-scale cube descent at a fixed index -/

/-- **Fixed-index descent to a triadic descendant.**

If `R` is a triadic descendant of `Q` at scale `k`, then

```
𝓔_{s,∞,2}(R; a, a₀)  ≤  3^{s·(Q.scale − k)} · 𝓔_{s,∞,2}(Q; a, a₀) ,
```

with the *same* coefficient family and comparator on both sides — which is
exactly how the printed transport `e.mathcalE.stability.applied` uses the
flux-corrected field `ã_{L,n+2}` and the comparator `σ_{n+2}` of the parent
cube on the smaller cube as well.

For a one-scale descent and `s ≤ 1` the factor is at most `3`; the printed
constant `C(d)(1−2s)^{-1}` is never needed in the grid case.  This is the `q =
2` sibling of CoarseGraining's
`Ch02.homogenizationErrorOnCube_infinity_one_le_of_mem_descendantsAtScale`. -/
theorem homogenizationErrorOnCube_infinity_two_le_of_mem_descendantsAtScale
    {Q R : TriadicCube d} {k : ℤ} (a : TriadicCoeffFamily d) (a0 : Mat d) {s : ℝ}
    (hs : 0 < s) (hR : R ∈ descendantsAtScale Q k) :
    HomogenizationErrorOnCube R s .infinity (.finite 2) a a0 ≤
      Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
        HomogenizationErrorOnCube Q s .infinity (.finite 2) a a0 := by
  classical
  set h : ℕ := Int.toNat (Q.scale - k) with hdef
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hh : (h : ℤ) = Q.scale - k := by
    rw [hdef]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hR
  set fQ : ℕ → ℝ := fun l =>
    HCPolySupport.geometricWeight s 2 l *
      maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - (l : ℤ)) a a0 with hfQ
  set fR : ℕ → ℝ := fun l =>
    HCPolySupport.geometricWeight s 2 l *
      maxDescendantNormalizedBlockResponseAtScale R (R.scale - (l : ℤ)) a a0 with hfR
  set factor : ℝ := Real.rpow (3 : ℝ) (s * (h : ℝ)) with hfactor
  have hfactor_nonneg : 0 ≤ factor := Real.rpow_nonneg (by norm_num) _
  have hsumQ : Summable fQ := summable_shell Q a a0 hs
  have hsumR : Summable fR := summable_shell R a a0 hs
  have hQnonneg : ∀ l : ℕ, 0 ≤ fQ l := by
    intro l
    refine mul_nonneg ?_ (shell_nonneg Q a a0 l)
    exact HCPolySupport.geometricWeight_nonneg l (by linarith only [hs])
  have htail : Summable fun l : ℕ => fQ (l + h) := (summable_nat_add_iff h).2 hsumQ
  have hterm : ∀ l : ℕ, fR l ≤ factor ^ 2 * fQ (l + h) := by
    intro l
    have hscale : R.scale - (l : ℤ) = Q.scale - ((l + h : ℕ) : ℤ) := by
      rw [hRscale, Nat.cast_add, hh]
      ring
    have hshell :
        maxDescendantNormalizedBlockResponseAtScale R (R.scale - (l : ℤ)) a a0 ≤
          maxDescendantNormalizedBlockResponseAtScale Q (Q.scale - ((l + h : ℕ) : ℤ)) a a0 := by
      rw [← hscale]
      exact maxDescendantNormalizedBlockResponseAtScale_le_of_mem_descendantsAtScale a a0 hR
        (sub_le_self _ (Int.natCast_nonneg l))
    have hshift : HCPolySupport.geometricWeight s 2 l =
        factor ^ 2 * HCPolySupport.geometricWeight s 2 (l + h) := by
      have hexp : s * 2 * (h : ℝ) = s * (h : ℝ) * 2 := by ring
      rw [hfactor, rpow_three_sq, ← hexp]
      exact HCPolySupport.geometricWeight_shift h l
    have hwnonneg : 0 ≤ HCPolySupport.geometricWeight s 2 (l + h) :=
      HCPolySupport.geometricWeight_nonneg (l + h) (by linarith only [hs])
    have hsq_nonneg : 0 ≤ factor ^ 2 := by positivity
    calc fR l = factor ^ 2 *
          (HCPolySupport.geometricWeight s 2 (l + h) *
            maxDescendantNormalizedBlockResponseAtScale R (R.scale - (l : ℤ)) a a0) := by
          rw [hfR]
          dsimp only
          rw [hshift]
          ring
      _ ≤ factor ^ 2 *
          (HCPolySupport.geometricWeight s 2 (l + h) *
            maxDescendantNormalizedBlockResponseAtScale Q
              (Q.scale - ((l + h : ℕ) : ℤ)) a a0) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hshell hwnonneg) hsq_nonneg
      _ = factor ^ 2 * fQ (l + h) := by rw [hfQ]
  have hscaled : Summable fun l : ℕ => factor ^ 2 * fQ (l + h) := htail.mul_left _
  have hsumLe : ∑' l : ℕ, fR l ≤ ∑' l : ℕ, factor ^ 2 * fQ (l + h) :=
    Summable.tsum_le_tsum hterm hsumR hscaled
  have htailLe : ∑' l : ℕ, fQ (l + h) ≤ ∑' l : ℕ, fQ l := by
    have hsplit := hsumQ.sum_add_tsum_nat_add h
    have hprefix : 0 ≤ ∑ i ∈ Finset.range h, fQ i :=
      Finset.sum_nonneg fun i _ => hQnonneg i
    linarith only [hsplit, hprefix]
  refine le_of_sq_le_sq_of_nonneg (homogenizationErrorOnCube_infinity_two_nonneg R a a0 hs)
    (mul_nonneg hfactor_nonneg (homogenizationErrorOnCube_infinity_two_nonneg Q a a0 hs)) ?_
  rw [mul_pow, homogenizationErrorOnCube_infinity_two_sq_eq_tsum R hs a a0,
    homogenizationErrorOnCube_infinity_two_sq_eq_tsum Q hs a a0]
  simp only [Ch02.geometricWeight_eq_old]
  calc ∑' l : ℕ, fR l ≤ ∑' l : ℕ, factor ^ 2 * fQ (l + h) := hsumLe
    _ = factor ^ 2 * ∑' l : ℕ, fQ (l + h) := htail.tsum_mul_left _
    _ ≤ factor ^ 2 * ∑' l : ℕ, fQ l := by
        exact mul_le_mul_of_nonneg_left htailLe (by positivity)

/-! ## 4. The composite the §4.3 chain uses -/

/-- **The two moves composed, in the order the §4.3 chain performs them.**

From a cap at the *parent* cube `Q` and the *small* index `t`, one reads off the
same cap at every triadic descendant `R` and every *larger* index `u`, at the
single cost `3^{t·(Q.scale − k)}`:

```
𝓔_{u,∞,2}(R; a, a₀)  ≤  3^{t·(Q.scale − k)} · 𝓔_{t,∞,2}(Q; a, a₀)   (t ≤ u).
``` -/
theorem homogenizationErrorOnCube_infinity_two_descendant_index_le
    {Q R : TriadicCube d} {k : ℤ} (a : TriadicCoeffFamily d) (a0 : Mat d) {t u : ℝ}
    (ht : 0 < t) (htu : t ≤ u) (hR : R ∈ descendantsAtScale Q k) :
    HomogenizationErrorOnCube R u .infinity (.finite 2) a a0 ≤
      Real.rpow (3 : ℝ) (t * (Int.toNat (Q.scale - k) : ℝ)) *
        HomogenizationErrorOnCube Q t .infinity (.finite 2) a a0 := by
  rcases eq_or_lt_of_le htu with heq | hlt
  · rw [← heq]
    exact homogenizationErrorOnCube_infinity_two_le_of_mem_descendantsAtScale a a0 ht hR
  · exact le_trans (homogenizationErrorOnCube_infinity_two_le_of_lt R a a0 ht hlt)
      (homogenizationErrorOnCube_infinity_two_le_of_mem_descendantsAtScale a a0 ht hR)

end

end Algsuperdiff.Section4.Provider.ExcessDecay
