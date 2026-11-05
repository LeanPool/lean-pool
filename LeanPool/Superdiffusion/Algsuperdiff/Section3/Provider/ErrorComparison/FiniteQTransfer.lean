/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.InftyToQ
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.MaxFormInfinity

/-!
# FiniteQTransfer

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the finite-`q` multiscale transfer of the cube-maximum form

The printed step

```
lambda^{-1}_{s,q}(square_m; a) <= max_{z in 3^n Z^d cap square_m}
  lambda^{-1}_{s,q}(z + square_n; a)
```

(ABK26, reused in `p.bfA.multiscalebound` Step 1) is for finite `q`:
definition (2.23) puts a *sum of per-depth maxima* on the left and a *maximum
of sums* on the right.

Two routes are proved here, both with the exponent drop `s -> t` as their only
structural cost:

```
G(s,t,q) = [c_{sq} / c_{(s-t)q}]^{2/q}                    (gap route, headline)
K(s,t,q) = G(s,t,q) . c_{tq}^{-2/q}                       (endpoint route)
   c_{aq} = 1 - 3^{-aq} = geometricDiscount a q .
```

## The transfers

`lambdaSq_finite_inv_le_gapConst_mul_max_descendants` (the sharp route): for `0 < t < s`,
`q >= 1` finite, `n <= Q.scale`,

```
lambda^{-1}_{s,q}(Q; a)
  <= G(s,t,q) . max_{R in descendantsAtScale Q n} lambda^{-1}_{t,q}(R; a) .
```

## Why the sharp route is sharper

The endpoint detour prices the per-depth maxima of `Q` twice: once going into
`lambda^{-1}_{t,infinity}` and once coming out of it, and the second passage
costs `c_{tq}^{-2/q}` (`= 7.79...` at `t = 1/16`, `q = 2`).  CoarseGraining's
`e.bound.one.cube.by.lambdas` (`maxDescendant_lambdaSq_inv_le`) supplies the
same geometric profile

```
M_i(Q) <= 3^{2ti} . max_{R in descendantsAtScale Q n} lambda^{-1}_{t,q}(R; a)
```

directly from the subcube gauges, with the descendant weight `3^{2t(R.scale -
k)}` for the deep scales and `e.subadda.nosymm` at the norm level for the
shallow ones, so the endpoint is never entered and only `G` survives.

## The canonical instantiation `s = 1/8`, `t = 1/16`, `q = 2`

At `q = 2` (so `2/q = 1`), with `u := 3^{-1/8} = 0.8716...` (so
`1 - u = 0.1283...`):

```
G(1/8, 1/16, 2) = (1 - 3^{-1/4}) / (1 - 3^{-1/8}) = 1 + 3^{-1/8} = 1.871... <= 2 ,
K(1/8, 1/16, 2) = (1 - 3^{-1/4}) / (1 - 3^{-1/8})^2  = 14.58...        <= 15 .
```

`maxFormGapConst_eighth_sixteenth_two_le` records the machine-checked bound on
`G`.  `K(s,t,2)` is symmetric under `t <-> s - t` and therefore minimized at
the midpoint `t = s/2`, which is why `t = 1/16` is canonical; `G(s,t,2)`
increases strictly in `t` (`G → 1` as `t → 0⁺`, `G → ∞` as `t → s⁻`, so the
sharp route gets cheaper at smaller `t`); `t = 1/16` is therefore admissible but
not extremal for the sharp route.  It is kept because the `s`-window and the
frozen `hsWindow` are checked at one fixed `t`.

## Cube indices

Every statement below quantifies over a cube `Q` with `n <= Q.scale`, i.e. the
subcube scale lies at or below the cube scale.

## Main results

* `maxFormGapConst`: the explicit `G`.
* `lambdaSq_finite_inv_le_gapConst_mul_of_maxDescendant_le`: the summation core,
  from any geometric profile `M_i(Q) <= 3^{2ti} D`.
* `maxDescendantSigmaStarInv_le_rpow_mul_max_descendants_lambdaSq_inv`: the
  geometric profile supplied by the subcube gauges.
* `lambdaSq_finite_inv_le_gapConst_mul_max_descendants`: the sharp transfer.
* `maxFormGapConst_eighth_sixteenth_two_le`: the machine-checked bound
  `G(1/8, 1/16, 2) <= 2`.
* `lambdaSq_eighth_inv_le_two_mul_max_descendants_sixteenth`: the consumer-facing
  instance `lambda^{-1}_{1/8,2}(Q) <= 2 max_R lambda^{-1}_{1/16,2}(R)`.

## References

* ABK26, (2.22)--(2.23), `l.bad.event.lemma`, case `n < m`,
  `p.bfA.multiscalebound`.
-/

namespace Algsuperdiff.Section3.Provider.ErrorComparison

open HCPolySupport

variable {d : ℕ}

/-! ## The transfer constant -/

/-- **The exponent-gap constant** `G(s,t,q) = [c_{sq} / c_{(s-t)q}]^{2/q}`, the
first factor of `K(s,t,q)`.  It is the constant of the sharp route below, which
never leaves the finite-`q` gauge and therefore never pays the endpoint factor
`c_{tq}^{-2/q}`. -/
noncomputable def maxFormGapConst (s t q : ℝ) : ℝ :=
  Real.rpow
    (Book.Ch02.geometricDiscount s q / Book.Ch02.geometricDiscount (s - t) q)
    (2 / q)

/-! ## Real-power and geometric-weight bookkeeping in CoarseGraining's spelling

CoarseGraining states its multiscale definitions with explicit `Real.rpow`
applications, while Mathlib's `rpow` A is phrased with the `^` notation.  The
restatements below keep every rewrite inside CoarseGraining's spelling; they
are the analogues, for the lemmas used here, of the `mul_rpow'` /
`rpow_natCast'` restatements already in `InftyToQ.lean`. -/

/-- `Real.rpow_le_rpow`, restated with explicit `Real.rpow` applications. -/
theorem rpow_le_rpow' {x y z : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hz : 0 ≤ z) :
    Real.rpow x z ≤ Real.rpow y z :=
  Real.rpow_le_rpow hx hxy hz

/-- `Real.rpow_nonneg`, restated with an explicit `Real.rpow` application. -/
theorem rpow_nonneg' {x : ℝ} (hx : 0 ≤ x) (y : ℝ) : 0 ≤ Real.rpow x y :=
  Real.rpow_nonneg hx y

/-- `Real.rpow_neg`, restated with explicit `Real.rpow` applications. -/
theorem rpow_neg' {x : ℝ} (hx : 0 ≤ x) (y : ℝ) :
    Real.rpow x (-y) = (Real.rpow x y)⁻¹ :=
  Real.rpow_neg hx y

/-- `Real.rpow_one`, restated with an explicit `Real.rpow` application. -/
theorem rpow_one' (x : ℝ) : Real.rpow x 1 = x :=
  Real.rpow_one x

/-- The defining form of CoarseGraining's `geometricWeight`. -/
theorem geometricWeight_eq' (x y : ℝ) (k : ℕ) :
    Book.Ch02.geometricWeight x y k =
      Book.Ch02.geometricDiscount x y * Real.rpow (3 : ℝ) (-x * y * (k : ℝ)) :=
  rfl

/-! ## Leg one: the finite-`q` gauge at `s` against the endpoint gauge at `t` -/

/-- **Leg one of the transfer.**  For `0 < t < s` and `0 < q`,

`lambda^{-1}_{s,q}(Q; a) <= [c_{sq} / c_{(s-t)q}]^{2/q}.
lambda^{-1}_{t,infinity}(Q; a)`.

This is (2.23) summed against the geometric density `c_{(s-t)q} 3^{-(s-t)qj}`;
the gap `s - t > 0` is exactly what makes that density summable. -/
theorem lambdaSq_finite_inv_le_gapConst_mul_of_maxDescendant_le
    [NeZero d] (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d)
    {t s q D : ℝ} (ht : 0 < t) (hts : t < s) (hq : 0 < q) (hDnonneg : 0 ≤ D)
    (hprof : ∀ i : ℕ,
      Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (i : ℤ)) a ≤ Real.rpow (3 : ℝ) (2 * t * (i : ℝ)) * D) :
    (Book.Ch02.lambdaSq Q s (.finite q) a)⁻¹ ≤ maxFormGapConst s t q * D := by
  have hs : 0 < s := ht.trans hts
  have hst : 0 < s - t := by linarith
  have hqne : q ≠ 0 := ne_of_gt hq
  have hcs : 0 < Book.Ch02.geometricDiscount s q :=
    HCPolySupport.geometricDiscount_pos (mul_pos hs hq)
  have hcst : 0 < Book.Ch02.geometricDiscount (s - t) q :=
    HCPolySupport.geometricDiscount_pos (mul_pos hst hq)
  have hcstne : Book.Ch02.geometricDiscount (s - t) q ≠ 0 := ne_of_gt hcst
  rw [maxFormGapConst]
  set A : ℝ :=
    Book.Ch02.geometricDiscount s q / Book.Ch02.geometricDiscount (s - t) q
    with hAdef
  have hAnonneg : 0 ≤ A := by
    rw [hAdef]
    exact (div_pos hcs hcst).le
  have hMnonneg : ∀ n : ℕ,
      0 ≤ Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (n : ℤ)) a := by
    intro n
    have hn : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast Nat.zero_le n
    exact Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q
      (sub_le_self _ hn) a
  -- the algebraic core of the termwise comparison, over abstract reals
  have halg : ∀ X Y : ℝ,
      Book.Ch02.geometricDiscount s q * X * Y =
        Book.Ch02.geometricDiscount s q /
            Book.Ch02.geometricDiscount (s - t) q * Y *
          (Book.Ch02.geometricDiscount (s - t) q * X) := by
    intro X Y
    field_simp
  -- the termwise comparison against the geometric density at `s - t`
  have hkey : ∀ n : ℕ,
      Book.Ch02.geometricWeight s q n *
          Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a) (q / 2) ≤
        A * Real.rpow D (q / 2) * Book.Ch02.geometricWeight (s - t) q n := by
    intro n
    have hMle :
        Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a ≤
          Real.rpow (3 : ℝ) (2 * t * (n : ℝ)) * D := hprof n
    have hRHS :
        Real.rpow (Real.rpow (3 : ℝ) (2 * t * (n : ℝ)) * D) (q / 2) =
          Real.rpow (3 : ℝ) (t * q * (n : ℝ)) * Real.rpow D (q / 2) := by
      rw [mul_rpow' (rpow_nonneg' (by norm_num : (0 : ℝ) ≤ 3) _) hDnonneg,
        rpow_rpow (by norm_num : (0 : ℝ) ≤ 3),
        show 2 * t * (n : ℝ) * (q / 2) = t * q * (n : ℝ) by ring]
    have hpow :
        Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a) (q / 2) ≤
          Real.rpow (3 : ℝ) (t * q * (n : ℝ)) * Real.rpow D (q / 2) := by
      rw [← hRHS]
      exact rpow_le_rpow' (hMnonneg n) hMle (by positivity)
    have hexp :
        Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) *
            Real.rpow (3 : ℝ) (t * q * (n : ℝ)) =
          Real.rpow (3 : ℝ) (-(s - t) * q * (n : ℝ)) := by
      rw [← rpow_three_add]
      congr 1
      ring
    calc Book.Ch02.geometricWeight s q n *
          Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a) (q / 2)
        ≤ Book.Ch02.geometricWeight s q n *
            (Real.rpow (3 : ℝ) (t * q * (n : ℝ)) * Real.rpow D (q / 2)) := by
          refine mul_le_mul_of_nonneg_left hpow ?_
          exact HCPolySupport.geometricWeight_nonneg n (mul_nonneg hs.le hq.le)
      _ = Book.Ch02.geometricDiscount s q *
            (Real.rpow (3 : ℝ) (-s * q * (n : ℝ)) *
              Real.rpow (3 : ℝ) (t * q * (n : ℝ))) * Real.rpow D (q / 2) := by
          rw [geometricWeight_eq' s q n]
          ring
      _ = Book.Ch02.geometricDiscount s q *
            Real.rpow (3 : ℝ) (-(s - t) * q * (n : ℝ)) * Real.rpow D (q / 2) := by
          rw [hexp]
      _ = A * Real.rpow D (q / 2) * Book.Ch02.geometricWeight (s - t) q n := by
          rw [geometricWeight_eq' (s - t) q n, hAdef]
          exact halg _ _
  -- summing against the geometric probability density
  have hsumL :=
    Book.Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q a hs hq
  have hsumW : Summable (fun n : ℕ => Book.Ch02.geometricWeight (s - t) q n) :=
    HCPolySupport.summable_geometricWeight (mul_pos hst hq)
  have hsumR : Summable (fun n : ℕ =>
      A * Real.rpow D (q / 2) * Book.Ch02.geometricWeight (s - t) q n) :=
    hsumW.mul_left _
  have hone : ∑' n : ℕ, Book.Ch02.geometricWeight (s - t) q n = 1 :=
    HCPolySupport.tsum_geometricWeight_eq_one (mul_pos hst hq)
  have hTle :
      (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
          Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a) (q / 2)) ≤ A * Real.rpow D (q / 2) := by
    calc (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
            Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
              (Q.scale - (n : ℤ)) a) (q / 2))
        ≤ ∑' n : ℕ,
            A * Real.rpow D (q / 2) * Book.Ch02.geometricWeight (s - t) q n :=
          Summable.tsum_le_tsum hkey hsumL hsumR
      _ = A * Real.rpow D (q / 2) *
            ∑' n : ℕ, Book.Ch02.geometricWeight (s - t) q n := tsum_mul_left
      _ = A * Real.rpow D (q / 2) := by rw [hone, mul_one]
  -- converting the sum back to the gauge
  have hTnonneg :
      0 ≤ ∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) a) (q / 2) :=
    Book.Ch02.lambdaSqFinite_series_nonneg Q s q a hq.le (mul_nonneg hs.le hq.le)
  have hlam : (Book.Ch02.lambdaSq Q s (.finite q) a)⁻¹ =
      Real.rpow (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
        Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
          (Q.scale - (n : ℤ)) a) (q / 2)) (2 / q) := by
    have hdef : Book.Ch02.lambdaSq Q s (.finite q) a =
        Real.rpow (∑' n : ℕ, Book.Ch02.geometricWeight s q n *
          Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
            (Q.scale - (n : ℤ)) a) (q / 2)) (-(2 / q)) := rfl
    rw [hdef, rpow_neg' hTnonneg, inv_inv]
  rw [hlam]
  refine le_trans (rpow_le_rpow' hTnonneg hTle (by positivity)) ?_
  rw [mul_rpow' hAnonneg (rpow_nonneg' hDnonneg _),
    rpow_rpow_of_mul_eq_one hDnonneg (by field_simp : q / 2 * (2 / q) = 1)]

/-! ## The sharp route: the geometric profile from the subcube gauges

The endpoint detour of the two legs above is not needed.  CoarseGraining's
`e.bound.one.cube.by.lambdas` (`maxDescendant_lambdaSq_inv_le`) prices the
per-depth maxima of a subcube directly by that subcube's own finite-`q` gauge,
with the descendant weight `3^{2t . depth}` — exactly the geometric profile
that the summation lemma consumes.  The endpoint factor `c_{tq}^{-2/q}`
therefore never appears, and the constant drops from `K` to `G`. -/

/-- **The geometric profile of the subcube gauges.**  For `n <= Q.scale`,
`t > 0` and admissible `q`, every per-depth maximum of `Q` is priced by the
scale-`n` subcube gauges at exponent `t`:

`max_{depth-i descendants R' of Q} |sigma_*^{-1}(R'; a)| <= 3^{2ti}. max_{R in
descendantsAtScale Q n} lambda^{-1}_{t,q}(R; a)`.

Deep scales (`Q.scale - i <= n`) are priced inside the relevant subcube by
`e.bound.one.cube.by.lambdas`; shallow scales by `e.subadda.nosymm` at the norm
level, which puts an ancestor's one-cube norm below the maximum over its
scale-`n` descendants. -/
theorem maxDescendantSigmaStarInv_le_rpow_mul_max_descendants_lambdaSq_inv
    [NeZero d] (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Book.Ch02.TriadicCoeffFamily d) {t : ℝ}
    {q : Book.Ch02.MultiscaleExponent} (ht : 0 < t) (hq : q.IsAdmissible)
    (i : ℕ) :
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q (Q.scale - (i : ℤ)) a ≤
      Real.rpow (3 : ℝ) (2 * t * (i : ℝ)) *
        Book.Ch02.finsetSupReal (descendantsAtScale Q n) fun R =>
          (Book.Ch02.lambdaSq R t q a)⁻¹ := by
  set Lb : ℝ :=
    Book.Ch02.finsetSupReal (descendantsAtScale Q n) fun R =>
      (Book.Ch02.lambdaSq R t q a)⁻¹ with hLbdef
  have hLbnonneg : 0 ≤ Lb := by
    rw [hLbdef]
    exact Book.Ch02.finsetSupReal_nonneg _ _ fun R _ =>
      inv_nonneg.mpr (Book.Ch02.lambdaSq_nonneg R a ht hq)
  have hw1 : (1 : ℝ) ≤ Real.rpow (3 : ℝ) (2 * t * (i : ℝ)) := by
    refine Real.one_le_rpow (by norm_num) ?_
    positivity
  have hki : Q.scale - (i : ℤ) ≤ Q.scale := by omega
  refine Book.Ch02.finsetSupReal_le (descendantsAtScale Q (Q.scale - (i : ℤ)))
    (descendantsAtScale_nonempty Q hki) ?_
  intro R' hR'
  by_cases hdeep : Q.scale - (i : ℤ) ≤ n
  · -- deep scales: price the descendant inside its scale-`n` ancestor
    obtain ⟨R, hR, hR'R⟩ :=
      exists_mem_descendantsAtScale_of_mem_descendantsAtScale hn hdeep hR'
    have hRscale : R.scale = n :=
      HCPolySupport.descendant_scale_eq_of_mem_descendantsAtScale hR
    have hkR : Q.scale - (i : ℤ) ≤ R.scale := by
      rw [hRscale]
      exact hdeep
    have h1 :=
      Book.Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantNorm_atScale
        a hR'R
    have h2 :=
      Book.Ch02.maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_inv R a hkR ht hq
    have h3 := Book.Ch02.maxDescendant_lambdaSq_inv_le R a hkR ht hq
    have hw0 : 0 ≤ Book.Ch02.multiscaleDescendantWeight R (Q.scale - (i : ℤ)) t := by
      rw [Book.Ch02.multiscaleDescendantWeight]
      exact rpow_nonneg' (by norm_num) _
    have hwle : Book.Ch02.multiscaleDescendantWeight R (Q.scale - (i : ℤ)) t ≤
        Real.rpow (3 : ℝ) (2 * t * (i : ℝ)) := by
      rw [Book.Ch02.multiscaleDescendantWeight, hRscale]
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hz : ((n - (Q.scale - (i : ℤ)) : ℤ) : ℝ) ≤ (i : ℝ) := by
        have hzi : (n - (Q.scale - (i : ℤ)) : ℤ) ≤ (i : ℤ) := by omega
        exact_mod_cast hzi
      exact mul_le_mul_of_nonneg_left hz (by positivity)
    have hlam : (Book.Ch02.lambdaSq R t q a)⁻¹ ≤ Lb := by
      rw [hLbdef]
      exact le_finsetSupReal (descendantsAtScale Q n)
        (fun R => (Book.Ch02.lambdaSq R t q a)⁻¹) hR
    calc Book.Ch02.coarseSigmaStarInvMatrixNorm R' a
        ≤ Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale R
            (Q.scale - (i : ℤ)) a := h1
      _ ≤ Book.Ch02.maxDescendantLowerEllipticityInvAtScale R
            (Q.scale - (i : ℤ)) t q a := h2
      _ ≤ Book.Ch02.multiscaleDescendantWeight R (Q.scale - (i : ℤ)) t *
            (Book.Ch02.lambdaSq R t q a)⁻¹ := h3
      _ ≤ Book.Ch02.multiscaleDescendantWeight R (Q.scale - (i : ℤ)) t * Lb :=
          mul_le_mul_of_nonneg_left hlam hw0
      _ ≤ Real.rpow (3 : ℝ) (2 * t * (i : ℝ)) * Lb :=
          mul_le_mul_of_nonneg_right hwle hLbnonneg
  · -- shallow scales: `e.subadda.nosymm` at the norm level
    push Not at hdeep
    have hR'scale : R'.scale = Q.scale - (i : ℤ) :=
      HCPolySupport.descendant_scale_eq_of_mem_descendantsAtScale hR'
    have hnR' : n ≤ R'.scale := by
      rw [hR'scale]
      omega
    have h1 :=
      Book.Ch02.coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale
        R' hnR' a
    have h2 :=
      Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_le_of_mem_descendantsAtScale
        a hR' hnR'
    have h3 :=
      Book.Ch02.maxDescendant_sigmaStarInv_le_maxDescendant_lambdaSq_inv Q a hn ht hq
    have h4 : Book.Ch02.maxDescendantLowerEllipticityInvAtScale Q n t q a = Lb :=
      hLbdef.symm
    calc Book.Ch02.coarseSigmaStarInvMatrixNorm R' a
        ≤ Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale R' n a := h1
      _ ≤ Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q n a := h2
      _ ≤ Book.Ch02.maxDescendantLowerEllipticityInvAtScale Q n t q a := h3
      _ = Lb := h4
      _ ≤ Real.rpow (3 : ℝ) (2 * t * (i : ℝ)) * Lb :=
          le_mul_of_one_le_left hLbnonneg hw1

/-- For `0 < t < s`, `1 <= q` and `n <= Q.scale`,

```
lambda^{-1}_{s,q}(Q; a)
  <= G(s,t,q) . max_{R in descendantsAtScale Q n} lambda^{-1}_{t,q}(R; a) ,
G(s,t,q) = [c_{sq} / c_{(s-t)q}]^{2/q} .
```

The only cost of the transfer is therefore the exponent drop `s -> t`; the
constant is `G <= 2` at the canonical instantiation, so the threshold re-basing
it forces on `C_{(e.cg.ellip.lower)}` is a factor `2`. -/
theorem lambdaSq_finite_inv_le_gapConst_mul_max_descendants [NeZero d]
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Book.Ch02.TriadicCoeffFamily d) {t s q : ℝ} (ht : 0 < t) (hts : t < s)
    (hq : 1 ≤ q) :
    (Book.Ch02.lambdaSq Q s (.finite q) a)⁻¹ ≤
      maxFormGapConst s t q *
        Book.Ch02.finsetSupReal (descendantsAtScale Q n) fun R =>
          (Book.Ch02.lambdaSq R t (.finite q) a)⁻¹ := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hqadm : (Book.Ch02.MultiscaleExponent.finite q).IsAdmissible := hq
  refine lambdaSq_finite_inv_le_gapConst_mul_of_maxDescendant_le Q a ht hts hq0
    (Book.Ch02.finsetSupReal_nonneg _ _ fun R _ =>
      inv_nonneg.mpr (Book.Ch02.lambdaSq_nonneg R a ht hqadm)) ?_
  intro i
  exact maxDescendantSigmaStarInv_le_rpow_mul_max_descendants_lambdaSq_inv Q hn a
    ht hqadm i

/-! ## The canonical instantiation `s = 1/8`, `t = 1/16`, `q = 2` -/

/-- `3^{-1/8}` is at most `7/8`: equivalently `(8/7)^8 = 2.91... <= 3`. -/
theorem rpow_three_neg_eighth_le : Real.rpow (3 : ℝ) (-(1 / 8 : ℝ)) ≤ 7 / 8 := by
  have hpow : Real.rpow (3 : ℝ) (-(1 / 8 : ℝ)) ^ (8 : ℕ) = 3⁻¹ := by
    rw [← rpow_natCast' (Real.rpow (3 : ℝ) (-(1 / 8 : ℝ))) 8,
      rpow_rpow (by norm_num : (0 : ℝ) ≤ 3),
      show -(1 / 8 : ℝ) * ((8 : ℕ) : ℝ) = -1 by norm_num,
      rpow_neg' (by norm_num : (0 : ℝ) ≤ 3), rpow_one']
  by_contra hcon
  push Not at hcon
  have hlt : ((7 : ℝ) / 8) ^ (8 : ℕ) ≤ Real.rpow (3 : ℝ) (-(1 / 8 : ℝ)) ^ (8 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) hcon.le 8
  rw [hpow] at hlt
  norm_num at hlt

/-- **The sharp constant at the canonical instantiation is at most `2`.**  At
`s = 1/8`, `t = 1/16`, `q = 2`,

`G = (1 - 3^{-1/4}) / (1 - 3^{-1/8}) = 1 + 3^{-1/8} = 1.871... <= 2`,

and the inequality `G <= 2` is in fact the identity `(1 - u)^2 >= 0` at
`u = 3^{-1/8}`. -/
theorem maxFormGapConst_eighth_sixteenth_two_le :
    maxFormGapConst (1 / 8) (1 / 16) 2 ≤ 2 := by
  set u : ℝ := Real.rpow (3 : ℝ) (-(1 / 8 : ℝ)) with hudef
  have hunn : 0 ≤ u := by
    rw [hudef]
    exact rpow_nonneg' (by norm_num) _
  have hu : u ≤ 7 / 8 := by
    rw [hudef]
    exact rpow_three_neg_eighth_le
  have hct : Book.Ch02.geometricDiscount (1 / 16 : ℝ) 2 = 1 - u := by
    rw [Book.Ch02.geometricDiscount, hudef]
    norm_num
  have hcgap : Book.Ch02.geometricDiscount ((1 : ℝ) / 8 - 1 / 16) 2 = 1 - u := by
    rw [show (1 : ℝ) / 8 - 1 / 16 = 1 / 16 by norm_num]
    exact hct
  have hcs : Book.Ch02.geometricDiscount (1 / 8 : ℝ) 2 = 1 - u ^ 2 := by
    have hu2 : u ^ 2 = Real.rpow (3 : ℝ) (-(1 / 4 : ℝ)) := by
      rw [hudef, ← rpow_natCast' (Real.rpow (3 : ℝ) (-(1 / 8 : ℝ))) 2,
        rpow_rpow (by norm_num : (0 : ℝ) ≤ 3)]
      congr 1
      push_cast
      ring
    rw [Book.Ch02.geometricDiscount, hu2]
    norm_num
  have hden : (0 : ℝ) < 1 - u := by linarith
  rw [maxFormGapConst, show (2 : ℝ) / 2 = 1 by norm_num, rpow_one', hcs, hcgap,
    div_le_iff₀ hden]
  nlinarith [hunn, hu]

/-- **The transfer at the canonical instantiation** `s = 1/8`, `t = 1/16`, `q = 2`,
with the machine-checked numerical constant of the sharp route:

`lambda^{-1}_{1/8,2}(Q; a) <= 2. max_{R in descendantsAtScale Q n}
lambda^{-1}_{1/16,2}(R; a)`.

This is the shape in which the ellipticity branch `n < m` of
`l.bad.event.lemma` (ABK26) and Step 1 of `p.bfA.multiscalebound` consume the
transfer.  Both costs are visible: the right-hand gauge sits at `t = 1/16 <
1/8`, so `p.cg.ellipticity.bounds` must be read at `1/16`, and the factor `2`
re-bases the threshold constant `C_{(e.cg.ellip.lower)}` (module header,
disclosure).  The factor is independent of `d`, of `Q.scale - n` and of the
number `3^{d(Q.scale-n)}` of subcubes. -/
theorem lambdaSq_eighth_inv_le_two_mul_max_descendants_sixteenth [NeZero d]
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Book.Ch02.TriadicCoeffFamily d) :
    (Book.Ch02.lambdaSq Q (1 / 8) (.finite 2) a)⁻¹ ≤
      2 * Book.Ch02.finsetSupReal (descendantsAtScale Q n) fun R =>
        (Book.Ch02.lambdaSq R (1 / 16) (.finite 2) a)⁻¹ := by
  have hSnonneg : 0 ≤ Book.Ch02.finsetSupReal (descendantsAtScale Q n) fun R =>
      (Book.Ch02.lambdaSq R (1 / 16) (.finite 2) a)⁻¹ :=
    Book.Ch02.finsetSupReal_nonneg _ _ fun R _ =>
      inv_nonneg.mpr (Book.Ch02.lambdaSq_finite_nonneg R a (by norm_num)
        (by norm_num))
  refine le_trans
    (lambdaSq_finite_inv_le_gapConst_mul_max_descendants Q hn a
      (by norm_num : (0 : ℝ) < 1 / 16) (by norm_num : (1 : ℝ) / 16 < 1 / 8)
      (by norm_num : (1 : ℝ) ≤ 2)) ?_
  exact mul_le_mul_of_nonneg_right maxFormGapConst_eighth_sixteenth_two_le
    hSnonneg

end Algsuperdiff.Section3.Provider.ErrorComparison
