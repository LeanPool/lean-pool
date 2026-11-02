/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Homogenization.HomLiftScaleArith
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Support.Dirichlet

/-!
# HomLiftTelescope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Theorem B, §4.5, Step 3c: the telescoping Hölder lifting

## What this module proves

The intended mechanism of the Step-3c bridge is the following.

> "Obviously `W^{-s,∞}` for the gradient `∇u` implies `L^∞` for `u`.
> `W^{-s,∞}` for the gradient is like `C^{0,1-s}` for the function `u`.
> Which is stronger than `L^∞`."

The classical proof of that implication is a *telescoping* argument over the
triadic scales.  Write `W_n` for the regularization of `w` at scale `3^n`
(mollification, or the running cube average).  A negative-order bound on `∇w`
of order `-s` at the `(∞,∞)` indices is exactly the pair of scale-by-scale
estimates

```text
  (L)  |W_n(x) - W_n(y)| ≤ A · 3^{-ns} · |x - y|      (the scale-n gradient bound)
  (I)  |W_n(x) - W_{n-1}(x)| ≤ A · 3^{n(1-s)}         (the scale-n increment)
```

and `(L)` + `(I)` + `W_n → w` give the Hölder bound `[w]_{C^{0,1-s}} ≤ C A`
with an **absolute** constant.  This module proves exactly that implication,
in the Hölder carrier `Support.HolderSeminormBoundOn`.

The split is deliberate: `(L)` and `(I)` are the *only* places where the
negative-order gradient bound enters, and they are the classical mollifier
estimates.  Everything downstream of them — the scale cut, the geometric
series, the modulus — is proved here unconditionally.

## The carrier pin, and what is NOT discharged here

The manuscript never defines `‖·‖_{W_hat^{-s,∞}(□_m)}`: only the order `-1`
dual seminorms and the negative-order Besov seminorm
`[·]_{B^{-s}_{p,q}}` (the negative Besov seminorm definition) are defined.
Under the Besov--Sobolev dictionary `W^{-s,p} ≃ B^{-s}_{p,p}` the Step-3
object is the `(∞,∞)` member of that family,

```text
  3^{-ms} ‖F‖_{W_hat^{-s,∞}(□_m)} ≍ sup_{n ≤ m} 3^{-(m-n)s} max_{z} |(F)_{z+□_n}|,
```

which is exactly the *multiscale* negative norm.  The `(∞,∞)` inner index —
the maximum over the subcubes at each scale, not an `ℓ^p` average — is
essential: a bound on the `ℓ^2`-averaged variant `B^{-s}_{2,∞}` (`CoarseGraining`'s
`scaleNormalizedNegativeBesovVectorNorm Q s.infinity`) does *not* imply a
pointwise Hölder bound, since a gradient concentrated on one subcube at
depth `j` has its `ℓ^2` average smaller by `3^{-jd/2}`.

`(L)` and `(I)` are the two scale-by-scale estimates that the multiscale
negative norm supplies for the mollifications `W_n` of `w`.  **They are
caller-supplied obligations: this module does not derive them.**  Producing
them from the negative Besov bound is the classical mollifier calculus (`∇(w ⋆
φ_r) = (∇w) ⋆ φ_r` together with the kernel's negative-norm pairing), which is
not built in this tree.

## Main results

* `holderSeminormBoundOn_of_regularization` — `(L)` at constant `AL` and the
  approximation bound `|W_n - w| ≤ AA · 3^{n(1-s)}` give
  `[w]_{C^{0,1-s}(U)} ≤ 2·AA + 2·AL`.
* `regularizationApprox_of_increments` — `(I)` plus convergence gives the
  approximation bound at constant `A · liftGeomFactor s`.
* `holderSeminormBoundOn_of_increments` — the composition, at the absolute
  constant `8 · A` for `0 < s ≤ 1/2`.

## The `s`-dependence

Every constant produced here is `2·liftGeomFactor s + 2 ≤ 8` on the whole
range `0 < s ≤ 1/2`; see `HomLiftScaleArith`.  In particular the §4.5 pin
`s = |log γ|⁻¹` and Step 3's own `s < 1/10` sit deep
inside the range where the constant is absolute, and **no** `(1-s)^{-1}`
factor is incurred.

## References

* ABK26, Theorem B Step 3.
* ABK26 (the `W^{s,∞} ↔ C^{0,s}` identification).
-/

open HCPolySupport

namespace Algsuperdiff.Section4.Provider.Homogenization

open Algsuperdiff.Section4.Support

noncomputable section

variable {d : ℕ}

/-! ## 1. The lifting from the two scale estimates -/

/-- **The telescoping Hölder lifting.**

Let `w: Vec d → ℝ` and let `W: ℤ → Vec d → ℝ` be a family of
regularizations indexed by the triadic scales `n ≤ m`.  Assume, on a set `U`
of diameter at most `3^m`:

* `hLip` — the scale-`n` Lipschitz bound `|W_n(x) - W_n(y)| ≤ AL 3^{-ns}|x-y|`;
* `hApp` — the scale-`n` approximation bound `|W_n(x) - w(x)| ≤ AA 3^{n(1-s)}`.

Then `w` is Hölder continuous of exponent `1 - s` on `U`, with constant
`2·AA + 2·AL`.

This is the `(∞,∞)`-index lifting: `hLip` and `hApp` are
precisely what a negative-order bound of order `-s` on `∇w` supplies at scale
`3^n`.  The exponent `1 - s` is the Hölder exponent asserted in. -/
theorem holderSeminormBoundOn_of_regularization
    {U : Set (Vec d)} {w : Vec d → ℝ} {W : ℤ → Vec d → ℝ} {m : ℤ} {s AL AA : ℝ}
    (hs0 : 0 < s) (hs2 : s ≤ 1 / 2) (hAL : 0 ≤ AL) (hAA : 0 ≤ AA)
    (hdiam : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ (3 : ℝ) ^ ((m : ℤ) : ℝ))
    (hLip : ∀ n : ℤ, n ≤ m → ∀ x ∈ U, ∀ y ∈ U,
      |W n x - W n y| ≤ AL * (3 : ℝ) ^ (-(((n : ℤ) : ℝ) * s)) * ‖x - y‖)
    (hApp : ∀ n : ℤ, n ≤ m → ∀ x ∈ U,
      |W n x - w x| ≤ AA * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s))) :
    HolderSeminormBoundOn U (1 - s) (2 * AA + 2 * AL) w := by
  have h1s : (0 : ℝ) < 1 - s := by linarith only [hs2]
  intro x hx y hy
  rw [Real.norm_eq_abs]
  rcases eq_or_ne x y with hxy | hxy
  · subst hxy
    simp only [sub_self, abs_zero, norm_zero]
    rw [Real.zero_rpow h1s.ne', mul_zero]
  · have ht : (0 : ℝ) < ‖x - y‖ := by
      rw [norm_pos_iff]
      exact sub_ne_zero_of_ne hxy
    obtain ⟨n, hnm, hlow, hhigh⟩ := exists_triadic_scale ht (hdiam x hx y hy)
    have htn : (0 : ℝ) ≤ ‖x - y‖ ^ (1 - s) := Real.rpow_nonneg ht.le _
    /- the approximation weight is dominated by `‖x - y‖^{1-s}` -/
    have ha : (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) ≤ ‖x - y‖ ^ (1 - s) := by
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
      exact Real.rpow_le_rpow (three_rpow_nonneg _) hlow h1s.le
    /- the Lipschitz weight times the distance is dominated by `3^s ‖x - y‖^{1-s}` -/
    have hts : ‖x - y‖ ^ s ≤ (3 : ℝ) ^ (((n : ℤ) : ℝ) * s) * (3 : ℝ) ^ s := by
      have h1 : ‖x - y‖ ^ s ≤ ((3 : ℝ) ^ (((n + 1 : ℤ) : ℝ))) ^ s :=
        Real.rpow_le_rpow ht.le hhigh.le hs0.le
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
        show (((n + 1 : ℤ) : ℝ)) * s = ((n : ℤ) : ℝ) * s + s by push_cast; ring,
        Real.rpow_add (by norm_num : (0 : ℝ) < 3)] at h1
      exact h1
    have hsplit : ‖x - y‖ ^ s * ‖x - y‖ ^ (1 - s) = ‖x - y‖ := by
      rw [← Real.rpow_add ht, show s + (1 - s) = (1 : ℝ) by ring, Real.rpow_one]
    have hkey : (3 : ℝ) ^ (-(((n : ℤ) : ℝ) * s)) * ‖x - y‖ ^ s ≤ (3 : ℝ) ^ s := by
      have hcancel :
          (3 : ℝ) ^ (-(((n : ℤ) : ℝ) * s)) *
              ((3 : ℝ) ^ (((n : ℤ) : ℝ) * s) * (3 : ℝ) ^ s) = (3 : ℝ) ^ s := by
        rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3), neg_add_cancel,
          Real.rpow_zero, one_mul]
      calc (3 : ℝ) ^ (-(((n : ℤ) : ℝ) * s)) * ‖x - y‖ ^ s
          ≤ (3 : ℝ) ^ (-(((n : ℤ) : ℝ) * s)) *
              ((3 : ℝ) ^ (((n : ℤ) : ℝ) * s) * (3 : ℝ) ^ s) :=
            mul_le_mul_of_nonneg_left hts (three_rpow_nonneg _)
        _ = (3 : ℝ) ^ s := hcancel
    have hb : (3 : ℝ) ^ (-(((n : ℤ) : ℝ) * s)) * ‖x - y‖ ≤ (3 : ℝ) ^ s * ‖x - y‖ ^ (1 - s) := by
      calc (3 : ℝ) ^ (-(((n : ℤ) : ℝ) * s)) * ‖x - y‖
          = ((3 : ℝ) ^ (-(((n : ℤ) : ℝ) * s)) * ‖x - y‖ ^ s) * ‖x - y‖ ^ (1 - s) := by
            rw [mul_assoc, hsplit]
        _ ≤ (3 : ℝ) ^ s * ‖x - y‖ ^ (1 - s) := mul_le_mul_of_nonneg_right hkey htn
    /- assemb -/
    have hA1 : |W n x - w x| ≤ AA * ‖x - y‖ ^ (1 - s) :=
      (hApp n hnm x hx).trans (mul_le_mul_of_nonneg_left ha hAA)
    have hA2 : |W n y - w y| ≤ AA * ‖x - y‖ ^ (1 - s) :=
      (hApp n hnm y hy).trans (mul_le_mul_of_nonneg_left ha hAA)
    have hB : |W n x - W n y| ≤ AL * ((3 : ℝ) ^ s * ‖x - y‖ ^ (1 - s)) := by
      refine (hLip n hnm x hx y hy).trans ?_
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left hb hAL
    have htri : |w x - w y| ≤ |W n x - w x| + |W n x - W n y| + |W n y - w y| := by
      have h1 : |w x - w y| ≤ |w x - W n x| + |W n x - w y| := abs_sub_le _ _ _
      have h2 : |W n x - w y| ≤ |W n x - W n y| + |W n y - w y| := abs_sub_le _ _ _
      have h3 : |w x - W n x| = |W n x - w x| := abs_sub_comm _ _
      linarith only [h1, h2, h3]
    have hstep : AL * ((3 : ℝ) ^ s * ‖x - y‖ ^ (1 - s)) ≤ 2 * (AL * ‖x - y‖ ^ (1 - s)) := by
      calc AL * ((3 : ℝ) ^ s * ‖x - y‖ ^ (1 - s))
          ≤ AL * (2 * ‖x - y‖ ^ (1 - s)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (three_rpow_le_two hs2) htn) hAL
        _ = 2 * (AL * ‖x - y‖ ^ (1 - s)) := by ring
    calc |w x - w y|
        ≤ AA * ‖x - y‖ ^ (1 - s) + AL * ((3 : ℝ) ^ s * ‖x - y‖ ^ (1 - s)) +
            AA * ‖x - y‖ ^ (1 - s) :=
          htri.trans (add_le_add (add_le_add hA1 hB) hA2)
      _ ≤ AA * ‖x - y‖ ^ (1 - s) + 2 * (AL * ‖x - y‖ ^ (1 - s)) +
            AA * ‖x - y‖ ^ (1 - s) := by linarith only [hstep]
      _ = (2 * AA + 2 * AL) * ‖x - y‖ ^ (1 - s) := by ring

/-! ## 2. The approximation bound from the increments -/

/-- **The telescoping series.**  If the increments of the regularization
family obey `|W_n(x) - W_{n-1}(x)| ≤ A · 3^{n(1-s)}` and `W_{n-k}(x) → w(x)`
as `k → ∞`, then the approximation bound holds at the constant
`A · liftGeomFactor s`.

`liftGeomFactor s = (1 - 3^{-(1-s)})⁻¹` is the sum of the geometric series;
it is at most `3` on `s ≤ 1/2` (`liftGeomFactor_le_three`). -/
theorem regularizationApprox_of_increments
    {U : Set (Vec d)} {w : Vec d → ℝ} {W : ℤ → Vec d → ℝ} {m : ℤ} {s A : ℝ}
    (hs1 : s < 1) (hA : 0 ≤ A)
    (hInc : ∀ n : ℤ, n ≤ m → ∀ x ∈ U,
      |W n x - W (n - 1) x| ≤ A * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)))
    (hLim : ∀ x ∈ U, ∀ n : ℤ, n ≤ m →
      Filter.Tendsto (fun k : ℕ => W (n - (k : ℤ)) x) Filter.atTop (nhds (w x))) :
    ∀ n : ℤ, n ≤ m → ∀ x ∈ U,
      |W n x - w x| ≤ (A * liftGeomFactor s) * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) := by
  intro n hnm x hx
  have hB0 : (0 : ℝ) < (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) := three_rpow_pos _
  have hAB : (0 : ℝ) ≤ A * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) := mul_nonneg hA hB0.le
  have hpart : ∀ k : ℕ,
      |W n x - W (n - (k : ℤ)) x| ≤
        A * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) *
          (∑ i ∈ Finset.range k, ((3 : ℝ) ^ (-(1 - s))) ^ i) := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        have hjm : n - (j : ℤ) ≤ m := by omega
        have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
        have hidx : n - ((j : ℤ) + 1) = n - (j : ℤ) - 1 := by ring
        have hweight : A * (3 : ℝ) ^ ((((n - (j : ℤ)) : ℤ) : ℝ) * (1 - s))
            = A * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) * ((3 : ℝ) ^ (-(1 - s))) ^ j := by
          rw [show (((n - (j : ℤ)) : ℤ) : ℝ) = ((n : ℤ) : ℝ) - (j : ℝ) by push_cast; ring,
            three_rpow_sub_natCast_mul]
          ring
        have hstep : |W (n - (j : ℤ)) x - W (n - ((j + 1 : ℕ) : ℤ)) x| ≤
            A * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) * ((3 : ℝ) ^ (-(1 - s))) ^ j := by
          rw [hcast, hidx]
          exact (hInc (n - (j : ℤ)) hjm x hx).trans (le_of_eq hweight)
        calc |W n x - W (n - ((j + 1 : ℕ) : ℤ)) x|
            ≤ |W n x - W (n - (j : ℤ)) x| +
                |W (n - (j : ℤ)) x - W (n - ((j + 1 : ℕ) : ℤ)) x| := abs_sub_le _ _ _
          _ ≤ A * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) *
                (∑ i ∈ Finset.range j, ((3 : ℝ) ^ (-(1 - s))) ^ i) +
              A * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) * ((3 : ℝ) ^ (-(1 - s))) ^ j :=
              add_le_add ih hstep
          _ = A * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) *
                (∑ i ∈ Finset.range (j + 1), ((3 : ℝ) ^ (-(1 - s))) ^ i) := by
              rw [Finset.sum_range_succ]; ring
  have hfin : ∀ k : ℕ, |W n x - W (n - (k : ℤ)) x| ≤
      A * liftGeomFactor s * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) := by
    intro k
    refine (hpart k).trans ?_
    calc A * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) *
            (∑ i ∈ Finset.range k, ((3 : ℝ) ^ (-(1 - s))) ^ i)
        ≤ A * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) * liftGeomFactor s :=
          mul_le_mul_of_nonneg_left (geom_sum_three_rpow_le hs1 k) hAB
      _ = A * liftGeomFactor s * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)) := by ring
  have hcont : Filter.Tendsto (fun k : ℕ => |W n x - W (n - (k : ℤ)) x|)
      Filter.atTop (nhds |W n x - w x|) :=
    ((hLim x hx n hnm).const_sub (W n x)).abs
  exact le_of_tendsto hcont (Filter.Eventually.of_forall hfin)

/-! ## 3. The composed lifting -/

/-- **The lifting from the two primitive scale estimates.**  The Lipschitz
bound `(L)` and the increment bound `(I)`, both at constant `A`, give the
Hölder bound at the absolute constant `8 A` for `0 < s ≤ 1/2`. -/
theorem holderSeminormBoundOn_of_increments
    {U : Set (Vec d)} {w : Vec d → ℝ} {W : ℤ → Vec d → ℝ} {m : ℤ} {s A : ℝ}
    (hs0 : 0 < s) (hs2 : s ≤ 1 / 2) (hA : 0 ≤ A)
    (hdiam : ∀ x ∈ U, ∀ y ∈ U, ‖x - y‖ ≤ (3 : ℝ) ^ ((m : ℤ) : ℝ))
    (hLip : ∀ n : ℤ, n ≤ m → ∀ x ∈ U, ∀ y ∈ U,
      |W n x - W n y| ≤ A * (3 : ℝ) ^ (-(((n : ℤ) : ℝ) * s)) * ‖x - y‖)
    (hInc : ∀ n : ℤ, n ≤ m → ∀ x ∈ U,
      |W n x - W (n - 1) x| ≤ A * (3 : ℝ) ^ (((n : ℤ) : ℝ) * (1 - s)))
    (hLim : ∀ x ∈ U, ∀ n : ℤ, n ≤ m →
      Filter.Tendsto (fun k : ℕ => W (n - (k : ℤ)) x) Filter.atTop (nhds (w x))) :
    HolderSeminormBoundOn U (1 - s) (8 * A) w := by
  have hs1 : s < 1 := by linarith only [hs2]
  have hG : (0 : ℝ) ≤ liftGeomFactor s := liftGeomFactor_nonneg hs1
  have hApp := regularizationApprox_of_increments hs1 hA hInc hLim
  have hbase :=
    holderSeminormBoundOn_of_regularization (W := W) (w := w) (m := m)
      hs0 hs2 hA (mul_nonneg hA hG) hdiam hLip hApp
  refine hbase.mono_const ?_
  have h3 : liftGeomFactor s ≤ 3 := liftGeomFactor_le_three hs2
  have hprod : A * liftGeomFactor s ≤ A * 3 := mul_le_mul_of_nonneg_left h3 hA
  linarith only [hprod]

end

end Algsuperdiff.Section4.Provider.Homogenization
