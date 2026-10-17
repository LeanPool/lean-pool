/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.FiniteQTransfer

/-!
# LambdaMatrixRoute

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The matrix route to a gap-free cube-raising for `lambda^{-1}`

ABK26, `e.subadda.nosymm`, and the cube-raising step of
`p.mathcalE.annular.decomp`.

## What is proved here

CoarseGraining's `lambdaSq` is **not** an abstract quantity: by
`Book.Ch02.lambdaSqFinite` it is a geometric aggregate of the matrix norms
`|sigma_*^{-1}(R; a)|` over the per-depth descendant maxima,

```
lambda^{-1}_{s,q}(Q; a) ^ {q/2}
  = sum_{i >= 0} c_{s,q} 3^{-s q i} . M_i(Q) ^ {q/2} ,
M_i(Q) = max_{R in descendantsAtScale Q (Q.scale - i)} |sigma_*^{-1}(R; a)| .
```

The `A_*^{-1}`-side subadditivity of the manuscript is therefore already
available inside the gauge: CoarseGraining proves, unconditionally at the
Chapter 2 `TriadicCoeffFamily` carrier,

* `coarseSigmaStarInvMatrixNorm_le_maxDescendantSigmaStarInvMatrixNormAtScale`
  (`|sigma_*^{-1}(Q)| <= M_i(Q)` for every depth — the norm-level reading of
  the Loewner-order subadditivity
  `sigmaStarInvCoarse_subadditive_openCubeSet_descendantsAtDepth_in_loewner_order_…`),
* `maxDescendantSigmaStarInvMatrixNormAtScale_le_of_le` (`M_i(Q)` is
  nondecreasing in the depth `i`), and
* `oneCube_sigmaStarInv_le_lambdaSq_finite_inv`
  (`|sigma_*^{-1}(R)| <= lambda^{-1}_{s,q}(R; a)`, constant `1`).

Splitting the gauge series of `Q` at the depth `p = Q.scale - n` and using the
two-level descendant factorization on the tail gives the **gap-free** (`t = s`)
cube-raising

```
lambda^{-1}_{s,q}(Q; a)
  <= (1 + N . 3^{-s q p}) ^ {2/q} . max_{R in descendantsAtScale Q n}
       lambda^{-1}_{s,q}(R; a) ,      N = #descendantsAtScale Q n = 3^{d p} .
```

The exponent is the same on both sides; the price is the explicit factor
`(1 + N 3^{-sqp})^{2/q}`, which is scale-free but grows with the separation
`p` like `3^{2p(d/q - s)}`.

## The constant is not uniform in the separation

The printed max form is false at constant `1`: it fails by `3^{2(m-n)(d/q -
s)}`, which is unbounded in the separation, so no absolute constant can rescue
the printed form.  Nothing here contradicts that:

* the statements below are **not** at constant `1`; and
* the constant delivered is `(1 + N 3^{-sqp})^{2/q} ~ 3^{2p(d/q - s)}`, i.e.
  exactly that failure rate, so it is **not** uniform in the separation `p`.
  It is a genuine constant only because the consumer's separation is the fixed
  number `p = 2`.

## Main results

* `sigmaStarInvSeries_le_cardConst_mul` — the summation core: the gauge series
  of `Q`, split at the raising depth, is priced by the scale-`n` descendant
  maximum at the factor `1 + N 3^{-sqp}`.
* `lambdaSq_finite_inv_le_cardConst_mul_max_descendants` — the gap-free
  cube-raising, at the explicit constant `(1 + N 3^{-sqp})^{2/q}`.
* `lambdaSq_finite_two_inv_le_nine_pow_mul_max_descendants_sub_two` — the
  consumer instance at `q = 2` and separation `2`: the constant is the bare
  numeral `1 + 9^d . 3^{-4s} <= 1 + 9^d`.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport
open Algsuperdiff.Section3.Provider.ErrorComparison

noncomputable section

variable {d : ℕ}

/-! ## The gauge series -/

/-- The finite-`q` multiscale series of `lambda^{-1}_{s,q}(Q; a)`: the
geometric aggregate of the per-depth maxima of `|sigma_*^{-1}|`. -/
def sigmaStarInvSeries (Q : TriadicCube d) (s q : ℝ)
    (a : Book.Ch02.TriadicCoeffFamily d) : ℝ :=
  ∑' i : ℕ, Book.Ch02.geometricWeight s q i *
    Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
      (Q.scale - (i : ℤ)) a) (q / 2)

theorem sigmaStarInvSeries_nonneg (Q : TriadicCube d) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) (a : Book.Ch02.TriadicCoeffFamily d) :
    0 ≤ sigmaStarInvSeries Q s q a :=
  Book.Ch02.lambdaSqFinite_series_nonneg Q s q a hq.le (mul_nonneg hs.le hq.le)

theorem summable_sigmaStarInvSeries [NeZero d] (Q : TriadicCube d)
    (a : Book.Ch02.TriadicCoeffFamily d) {s q : ℝ} (hs : 0 < s) (hq : 0 < q) :
    Summable (fun i : ℕ => Book.Ch02.geometricWeight s q i *
      Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (Q.scale - (i : ℤ)) a) (q / 2)) :=
  Book.Ch02.summable_sigmaStarInv_series_pointwiseCoeffField Q a hs hq

/-- The gauge is the `2/q` power of the series. -/
theorem inv_lambdaSq_finite_eq_rpow_sigmaStarInvSeries
    (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    (Book.Ch02.lambdaSq Q s (.finite q) a)⁻¹ =
      Real.rpow (sigmaStarInvSeries Q s q a) (2 / q) := by
  have hdef : Book.Ch02.lambdaSq Q s (.finite q) a =
      Real.rpow (sigmaStarInvSeries Q s q a) (-(2 / q)) := rfl
  rw [hdef, rpow_neg' (sigmaStarInvSeries_nonneg Q hs hq a), inv_inv]

/-- The series is the `q/2` power of the gauge. -/
theorem sigmaStarInvSeries_eq_rpow_inv_lambdaSq
    (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d) {s q : ℝ}
    (hs : 0 < s) (hq : 0 < q) :
    sigmaStarInvSeries Q s q a =
      Real.rpow ((Book.Ch02.lambdaSq Q s (.finite q) a)⁻¹) (q / 2) := by
  rw [inv_lambdaSq_finite_eq_rpow_sigmaStarInvSeries Q a hs hq,
    rpow_rpow (sigmaStarInvSeries_nonneg Q hs hq a),
    show 2 / q * (q / 2) = 1 by field_simp, rpow_one']

/-! ## Two `Finset`-sum bookkeeping helpers -/

/-- A finite sum of summable families is summable. -/
private theorem summable_finsetSum {iota : Type*} (s : Finset iota)
    (F : iota → ℕ → ℝ) (h : ∀ i ∈ s, Summable (F i)) :
    Summable (fun j : ℕ => ∑ i ∈ s, F i j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      have hF : Summable (F i) := h i (Finset.mem_insert_self i s)
      have hrest : Summable (fun j : ℕ => ∑ k ∈ s, F k j) :=
        ih fun k hk => h k (Finset.mem_insert_of_mem hk)
      have := hF.add hrest
      refine this.congr ?_
      intro j
      rw [Finset.sum_insert hi]

/-- The `tsum` of a finite sum is the finite sum of the `tsum`s. -/
private theorem tsum_finsetSum {iota : Type*} (s : Finset iota)
    (F : iota → ℕ → ℝ) (h : ∀ i ∈ s, Summable (F i)) :
    (∑' j : ℕ, ∑ i ∈ s, F i j) = ∑ i ∈ s, ∑' j : ℕ, F i j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      have hF : Summable (F i) := h i (Finset.mem_insert_self i s)
      have hrest : Summable (fun j : ℕ => ∑ k ∈ s, F k j) :=
        summable_finsetSum s F fun k hk => h k (Finset.mem_insert_of_mem hk)
      have hcongr : (∑' j : ℕ, ∑ k ∈ insert i s, F k j) =
          ∑' j : ℕ, (F i j + ∑ k ∈ s, F k j) := by
        refine tsum_congr ?_
        intro j
        rw [Finset.sum_insert hi]
      rw [hcongr, Summable.tsum_add hF hrest,
        ih fun k hk => h k (Finset.mem_insert_of_mem hk), Finset.sum_insert hi]

/-! ## The two structural inputs, at the descendant maxima -/

/-- **The head input.**  For a depth `i` above the raising depth `p`, the
per-depth maximum of `Q` is already below the descendant gauge maximum: the
matrix subadditivity `e.subadda.nosymm` at the norm level pushes `M_i(Q)`
down to `M_p(Q)`, and the one-cube bound prices each scale-`n` descendant by
its own gauge. -/
theorem maxDescendantSigmaStarInv_le_max_descendants_inv_lambdaSq [NeZero d]
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Book.Ch02.TriadicCoeffFamily d) {s q : ℝ} (hs : 0 < s) (hq : 1 ≤ q)
    {k : ℤ} (hk : n ≤ k) (hkQ : k ≤ Q.scale) :
    Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q k a ≤
      Book.Ch02.finsetSupReal (descendantsAtScale Q n) fun R =>
        (Book.Ch02.lambdaSq R s (.finite q) a)⁻¹ := by
  refine le_trans
    (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_le_of_le a Q hk hkQ) ?_
  refine Book.Ch02.finsetSupReal_le (descendantsAtScale Q n)
    (descendantsAtScale_nonempty Q hn) ?_
  intro R hR
  refine le_trans (Book.Ch02.oneCube_sigmaStarInv_le_lambdaSq_finite_inv R a hs hq) ?_
  exact le_finsetSupReal (descendantsAtScale Q n)
    (fun R => (Book.Ch02.lambdaSq R s (.finite q) a)⁻¹) hR

/-- **The tail input.**  Below the raising depth the per-depth maxima of `Q` factor
through the scale-`n` descendants: every scale-`(n - j)` descendant of `Q` sits
inside one of them, so its one-cube norm is priced by the `j`-th per-depth
maximum of that descendant.  Passing to the `q/2` power turns the maximum over
the descendants into a sum over them (the "max of sums versus sum of maxima"
defect, paid here in full). -/
theorem maxDescendantSigmaStarInv_rpow_le_sum_descendants
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Book.Ch02.TriadicCoeffFamily d) {q : ℝ} (hq : 0 < q) (j : ℕ) :
    Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
        (n - (j : ℤ)) a) (q / 2) ≤
      ∑ R ∈ descendantsAtScale Q n,
        Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale R
          (R.scale - (j : ℤ)) a) (q / 2) := by
  classical
  set T : ℝ := ∑ R ∈ descendantsAtScale Q n,
    Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale R
      (R.scale - (j : ℤ)) a) (q / 2) with hTdef
  have hjn : n - (j : ℤ) ≤ n := by
    have : (0 : ℤ) ≤ (j : ℤ) := by exact_mod_cast Nat.zero_le j
    omega
  have hterm0 : ∀ R ∈ descendantsAtScale Q n,
      0 ≤ Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale R
        (R.scale - (j : ℤ)) a) (q / 2) := by
    intro R _
    exact rpow_nonneg' (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg R
      (by omega) a) _
  have hT0 : 0 ≤ T := Finset.sum_nonneg hterm0
  -- it suffices to price the per-depth maximum by `T ^ {2/q}`
  have hmain : Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
      (n - (j : ℤ)) a ≤ Real.rpow T (2 / q) := by
    refine Book.Ch02.finsetSupReal_le (descendantsAtScale Q (n - (j : ℤ)))
      (descendantsAtScale_nonempty Q (hjn.trans hn)) ?_
    intro S hS
    obtain ⟨R, hR, hSR⟩ :=
      exists_mem_descendantsAtScale_of_mem_descendantsAtScale hn hjn hS
    have hRscale : R.scale = n :=
      HCPolySupport.descendant_scale_eq_of_mem_descendantsAtScale hR
    have hSle : Book.Ch02.coarseSigmaStarInvMatrixNorm S a ≤
        Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale R
          (R.scale - (j : ℤ)) a := by
      refine le_finsetSupReal (descendantsAtScale R (R.scale - (j : ℤ)))
        (fun S => Book.Ch02.coarseSigmaStarInvMatrixNorm S a) ?_
      rw [hRscale]
      exact hSR
    have hpow : Real.rpow (Book.Ch02.coarseSigmaStarInvMatrixNorm S a) (q / 2) ≤ T := by
      refine le_trans (rpow_le_rpow' (Book.Ch02.coarseSigmaStarInvMatrixNorm_nonneg S a)
        hSle (by positivity)) ?_
      rw [hTdef]
      exact Finset.single_le_sum hterm0 hR
    have hback : Book.Ch02.coarseSigmaStarInvMatrixNorm S a =
        Real.rpow (Real.rpow (Book.Ch02.coarseSigmaStarInvMatrixNorm S a) (q / 2))
          (2 / q) := by
      rw [rpow_rpow (Book.Ch02.coarseSigmaStarInvMatrixNorm_nonneg S a),
        show q / 2 * (2 / q) = 1 by field_simp, rpow_one']
    rw [hback]
    exact rpow_le_rpow' (rpow_nonneg' (Book.Ch02.coarseSigmaStarInvMatrixNorm_nonneg S a) _)
      hpow (by positivity)
  refine le_trans (rpow_le_rpow'
    (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q (hjn.trans hn) a)
    hmain (by positivity)) ?_
  rw [rpow_rpow hT0, show 2 / q * (q / 2) = 1 by field_simp, rpow_one']

/-! ## The summation core -/

/-- **The gap-free summation core.**  Splitting the gauge series of `Q` at the
raising depth `p` and using the two structural inputs above,

`S(Q) <= (1 + N . 3^{-s q p}) . D^{q/2}`,

where `D` is the maximum of the scale-`n` descendant gauges and `N =
#descendantsAtScale Q n`.  The head contributes at most `D^{q/2}` because the
geometric weights are a probability density; the tail contributes `3^{-sqp} .
sum_(R)` because the shifted weights factor exactly. -/
theorem sigmaStarInvSeries_le_cardConst_mul [NeZero d]
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Book.Ch02.TriadicCoeffFamily d) {s q : ℝ} (hs : 0 < s) (hq : 1 ≤ q) :
    sigmaStarInvSeries Q s q a ≤
      (1 + ((descendantsAtScale Q n).card : ℝ) *
          Real.rpow (3 : ℝ) (-(s * q * ((Q.scale - n : ℤ) : ℝ)))) *
        Real.rpow (Book.Ch02.finsetSupReal (descendantsAtScale Q n) fun R =>
          (Book.Ch02.lambdaSq R s (.finite q) a)⁻¹) (q / 2) := by
  classical
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set D : ℝ := Book.Ch02.finsetSupReal (descendantsAtScale Q n) fun R =>
    (Book.Ch02.lambdaSq R s (.finite q) a)⁻¹ with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact Book.Ch02.finsetSupReal_nonneg _ _ fun R _ =>
      inv_nonneg.mpr (Book.Ch02.lambdaSq_nonneg R a hs (by simpa using hq))
  set E : ℝ := Real.rpow D (q / 2) with hEdef
  have hE0 : 0 ≤ E := rpow_nonneg' hD0 _
  set f : ℕ → ℝ := fun i => Book.Ch02.geometricWeight s q i *
    Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale Q
      (Q.scale - (i : ℤ)) a) (q / 2) with hfdef
  have hsumf : Summable f := summable_sigmaStarInvSeries Q a hs hq0
  have hw0 : ∀ i : ℕ, 0 ≤ Book.Ch02.geometricWeight s q i := by
    intro i
    simpa [Book.Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg i (mul_nonneg hs.le hq0.le)
  have hsumw : Summable (fun i : ℕ => Book.Ch02.geometricWeight s q i) := by
    simpa [Book.Ch02.geometricWeight_eq_old] using
      HCPolySupport.summable_geometricWeight (mul_pos hs hq0)
  have hwone : ∑' i : ℕ, Book.Ch02.geometricWeight s q i = 1 := by
    simpa [Book.Ch02.geometricWeight_eq_old] using
      HCPolySupport.tsum_geometricWeight_eq_one (mul_pos hs hq0)
  -- the raising depth
  set p : ℕ := Int.toNat (Q.scale - n) with hpdef
  have hpz : ((p : ℤ)) = Q.scale - n := by
    rw [hpdef]
    omega
  -- the head
  have hhead : ∑ i ∈ Finset.range p, f i ≤ E := by
    have hle : ∀ i ∈ Finset.range p, f i ≤ Book.Ch02.geometricWeight s q i * E := by
      intro i hi
      have hip : (i : ℤ) ≤ (p : ℤ) := by
        have := Finset.mem_range.mp hi
        exact_mod_cast Nat.le_of_lt this
      have hnk : n ≤ Q.scale - (i : ℤ) := by omega
      have hkQ : Q.scale - (i : ℤ) ≤ Q.scale := by
        have : (0 : ℤ) ≤ (i : ℤ) := by exact_mod_cast Nat.zero_le i
        omega
      have hM := maxDescendantSigmaStarInv_le_max_descendants_inv_lambdaSq
        Q hn a hs hq hnk hkQ
      refine mul_le_mul_of_nonneg_left ?_ (hw0 i)
      rw [hEdef]
      exact rpow_le_rpow'
        (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale_nonneg Q hkQ a)
        (by rw [← hDdef] at hM; exact hM) (by positivity)
    refine le_trans (Finset.sum_le_sum hle) ?_
    calc ∑ i ∈ Finset.range p, Book.Ch02.geometricWeight s q i * E
        = (∑ i ∈ Finset.range p, Book.Ch02.geometricWeight s q i) * E := by
          rw [Finset.sum_mul]
      _ ≤ (∑' i : ℕ, Book.Ch02.geometricWeight s q i) * E := by
          refine mul_le_mul_of_nonneg_right ?_ hE0
          exact hsumw.sum_le_tsum (Finset.range p) (fun i _ => hw0 i)
      _ = E := by rw [hwone, one_mul]
  -- the tail: the weight shift
  have hshift : ∀ j : ℕ, Book.Ch02.geometricWeight s q (j + p) =
      Real.rpow (3 : ℝ) (-(s * q * (p : ℝ))) * Book.Ch02.geometricWeight s q j := by
    intro j
    rw [geometricWeight_eq' s q (j + p), geometricWeight_eq' s q j]
    rw [show -s * q * ((j + p : ℕ) : ℝ) = -(s * q * (p : ℝ)) + -s * q * (j : ℝ) by
      push_cast; ring, rpow_three_add]
    ring
  -- the tail: the descendant sum
  set g : ℕ → ℝ := fun j => Book.Ch02.geometricWeight s q j *
    (∑ R ∈ descendantsAtScale Q n,
      Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale R
        (R.scale - (j : ℤ)) a) (q / 2)) with hgdef
  have hsumR : ∀ R ∈ descendantsAtScale Q n, Summable (fun j : ℕ =>
      Book.Ch02.geometricWeight s q j *
        Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale R
          (R.scale - (j : ℤ)) a) (q / 2)) := by
    intro R _
    exact summable_sigmaStarInvSeries R a hs hq0
  have hsumg : Summable g := by
    rw [hgdef]
    simp only [Finset.mul_sum]
    exact summable_finsetSum (descendantsAtScale Q n)
      (fun R j => Book.Ch02.geometricWeight s q j *
        Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale R
          (R.scale - (j : ℤ)) a) (q / 2)) hsumR
  have htailterm : ∀ j : ℕ, f (j + p) ≤
      Real.rpow (3 : ℝ) (-(s * q * (p : ℝ))) * g j := by
    intro j
    have hidx : Q.scale - ((j + p : ℕ) : ℤ) = n - (j : ℤ) := by
      push_cast
      omega
    rw [hfdef, hgdef]
    simp only
    rw [hshift j, hidx, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (rpow_nonneg' (by norm_num) _)
    exact mul_le_mul_of_nonneg_left
      (maxDescendantSigmaStarInv_rpow_le_sum_descendants Q hn a hq0 j) (hw0 j)
  have hsumtail : Summable (fun j : ℕ => f (j + p)) := (summable_nat_add_iff p).2 hsumf
  have htail : ∑' j : ℕ, f (j + p) ≤
      Real.rpow (3 : ℝ) (-(s * q * (p : ℝ))) *
        (((descendantsAtScale Q n).card : ℝ) * E) := by
    have hstep : ∑' j : ℕ, f (j + p) ≤
        Real.rpow (3 : ℝ) (-(s * q * (p : ℝ))) * ∑' j : ℕ, g j := by
      calc ∑' j : ℕ, f (j + p)
          ≤ ∑' j : ℕ, Real.rpow (3 : ℝ) (-(s * q * (p : ℝ))) * g j :=
            Summable.tsum_le_tsum htailterm hsumtail (hsumg.mul_left _)
        _ = Real.rpow (3 : ℝ) (-(s * q * (p : ℝ))) * ∑' j : ℕ, g j := tsum_mul_left
    refine hstep.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (rpow_nonneg' (by norm_num) _)
    have hswap : ∑' j : ℕ, g j =
        ∑ R ∈ descendantsAtScale Q n, sigmaStarInvSeries R s q a := by
      rw [hgdef]
      simp only [Finset.mul_sum]
      rw [tsum_finsetSum (descendantsAtScale Q n)
        (fun R j => Book.Ch02.geometricWeight s q j *
          Real.rpow (Book.Ch02.maxDescendantSigmaStarInvMatrixNormAtScale R
            (R.scale - (j : ℤ)) a) (q / 2)) hsumR]
      rfl
    rw [hswap]
    have hRle : ∀ R ∈ descendantsAtScale Q n, sigmaStarInvSeries R s q a ≤ E := by
      intro R hR
      rw [sigmaStarInvSeries_eq_rpow_inv_lambdaSq R a hs hq0, hEdef]
      refine rpow_le_rpow' (inv_nonneg.mpr (Book.Ch02.lambdaSq_nonneg R a hs
        (by simpa using hq))) ?_ (by positivity)
      rw [hDdef]
      exact le_finsetSupReal (descendantsAtScale Q n)
        (fun R => (Book.Ch02.lambdaSq R s (.finite q) a)⁻¹) hR
    calc ∑ R ∈ descendantsAtScale Q n, sigmaStarInvSeries R s q a
        ≤ ∑ _R ∈ descendantsAtScale Q n, E := Finset.sum_le_sum hRle
      _ = ((descendantsAtScale Q n).card : ℝ) * E := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- combine
  have hsplit : sigmaStarInvSeries Q s q a =
      (∑ i ∈ Finset.range p, f i) + ∑' j : ℕ, f (j + p) := by
    rw [sigmaStarInvSeries]
    exact (hsumf.sum_add_tsum_nat_add p).symm
  rw [hsplit]
  have hgoal : (∑ i ∈ Finset.range p, f i) + ∑' j : ℕ, f (j + p) ≤
      E + Real.rpow (3 : ℝ) (-(s * q * (p : ℝ))) *
        (((descendantsAtScale Q n).card : ℝ) * E) := add_le_add hhead htail
  have hcast : (((Q.scale - n : ℤ)) : ℝ) = ((p : ℕ) : ℝ) := by
    rw [← hpz]
    push_cast
    ring
  rw [hcast]
  exact hgoal.trans (le_of_eq (by ring))

/-! ## The gap-free cube-raising -/

/-- **The gap-free cube-raising** (`e.subadda.nosymm`; the `hlam` slot).  For
`0 < s`, `1 <= q` and `n <= Q.scale`,

```
lambda^{-1}_{s,q}(Q; a)
  <= (1 + N . 3^{-s q (Q.scale - n)}) ^ {2/q} .
       max_{R in descendantsAtScale Q n} lambda^{-1}_{s,q}(R; a) ,
N = #descendantsAtScale Q n .
```

The exponent `s` is the same on both sides — this is what the proved
`FiniteQTransfer.lambdaSq_finite_inv_le_gapConst_mul_max_descendants` cannot
give, since its gap constant `[c_{sq}/c_{(s-t)q}]^{2/q}` blows up as `t -> s`. -/
theorem lambdaSq_finite_inv_le_cardConst_mul_max_descendants [NeZero d]
    (Q : TriadicCube d) {n : ℤ} (hn : n ≤ Q.scale)
    (a : Book.Ch02.TriadicCoeffFamily d) {s q : ℝ} (hs : 0 < s) (hq : 1 ≤ q) :
    (Book.Ch02.lambdaSq Q s (.finite q) a)⁻¹ ≤
      Real.rpow (1 + ((descendantsAtScale Q n).card : ℝ) *
          Real.rpow (3 : ℝ) (-(s * q * ((Q.scale - n : ℤ) : ℝ)))) (2 / q) *
        Book.Ch02.finsetSupReal (descendantsAtScale Q n) fun R =>
          (Book.Ch02.lambdaSq R s (.finite q) a)⁻¹ := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set D : ℝ := Book.Ch02.finsetSupReal (descendantsAtScale Q n) fun R =>
    (Book.Ch02.lambdaSq R s (.finite q) a)⁻¹ with hDdef
  have hD0 : 0 ≤ D := by
    rw [hDdef]
    exact Book.Ch02.finsetSupReal_nonneg _ _ fun R _ =>
      inv_nonneg.mpr (Book.Ch02.lambdaSq_nonneg R a hs (by simpa using hq))
  set K : ℝ := 1 + ((descendantsAtScale Q n).card : ℝ) *
    Real.rpow (3 : ℝ) (-(s * q * ((Q.scale - n : ℤ) : ℝ))) with hKdef
  have hK0 : 0 ≤ K := by
    rw [hKdef]
    have := rpow_nonneg' (by norm_num : (0 : ℝ) ≤ 3)
      (-(s * q * ((Q.scale - n : ℤ) : ℝ)))
    have hcard : (0 : ℝ) ≤ ((descendantsAtScale Q n).card : ℝ) := Nat.cast_nonneg _
    nlinarith [this, hcard]
  have hcore := sigmaStarInvSeries_le_cardConst_mul Q hn a hs hq
  rw [← hDdef, ← hKdef] at hcore
  rw [inv_lambdaSq_finite_eq_rpow_sigmaStarInvSeries Q a hs hq0]
  refine le_trans (rpow_le_rpow' (sigmaStarInvSeries_nonneg Q hs hq0 a) hcore
    (by positivity)) ?_
  rw [mul_rpow' hK0 (rpow_nonneg' hD0 _), rpow_rpow hD0,
    show q / 2 * (2 / q) = 1 by field_simp, rpow_one']

/-- **The consumer instance**: `q = 2` and separation `2` — the shape the `hlam`
slot needs, with the constant collapsed to the numeral `1 + 9^d . 3^{-4s}`. -/
theorem lambdaSq_finite_two_inv_le_nine_pow_mul_max_descendants_sub_two [NeZero d]
    (Q : TriadicCube d) (a : Book.Ch02.TriadicCoeffFamily d) {s : ℝ} (hs : 0 < s) :
    (Book.Ch02.lambdaSq Q s (.finite 2) a)⁻¹ ≤
      (1 + ((9 : ℝ) ^ d) * Real.rpow (3 : ℝ) (-(4 * s))) *
        Book.Ch02.finsetSupReal (descendantsAtScale Q (Q.scale - 2)) fun R =>
          (Book.Ch02.lambdaSq R s (.finite 2) a)⁻¹ := by
  have hn : Q.scale - 2 ≤ Q.scale := by omega
  have hmain := lambdaSq_finite_inv_le_cardConst_mul_max_descendants
    Q hn a hs (by norm_num : (1 : ℝ) ≤ 2)
  have hcard : ((descendantsAtScale Q (Q.scale - 2)).card : ℝ) = (9 : ℝ) ^ d := by
    rw [descendantsAtScale_eq_descendantsAtDepth Q hn, descendantsAtDepth_card,
      show Int.toNat (Q.scale - (Q.scale - 2)) = 2 by omega]
    push_cast
    rw [← pow_mul, mul_comm d 2, pow_mul]
    norm_num
  have hexp : (-(s * 2 * ((Q.scale - (Q.scale - 2) : ℤ) : ℝ))) = -(4 * s) := by
    rw [show (Q.scale - (Q.scale - 2) : ℤ) = 2 by omega]
    push_cast
    ring
  rw [hcard, hexp] at hmain
  refine hmain.trans_eq ?_
  congr 1
  rw [show (2 : ℝ) / 2 = 1 by norm_num, rpow_one']

end

end Algsuperdiff.Section4.Provider.Annular
