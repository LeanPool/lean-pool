/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.CarrierIdentification

/-!
# Step1Assembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The two interchanges and the centre closure of Step 1

ABK26, Section 4.1, `e.mathcalE.annular.decomp.pre`, Step 1.
`Step1.annularDecompPre_of` reduces the Step-1 shape to three caller
obligations: `hgrid` (the cover split), `hcov` (the cover interchange) and
`hcen` (the resummed centre term).  This module proves the last two
**abstractly**, in the weight the manuscript uses, so that the concrete
producer only has to supply the geometry.

## What is proved

* `tsum_annFam_row` -- the `n`-row of the guarded annular family is a finite
  sum over `j ∈ [n+1, m]`.  This is the manuscript's interchange `Σ_{n ≤ m}
  Σ_{j=n+1}^m = Σ_{j ≤ m} Σ_{n ≤ j-1}`, and it is an **identity**, so the cover
  leg costs `C_cov = 1` with no loss.
* `annDouble_eq_tsum_rows`, `summable_annFam_rows` -- the transposed iterated form
  of the annular double sum, and the summability of its rows.
* `tsum_centre_le` -- the centre closure.  Given only the **one-step**
  subadditivity recursion `Jcen n ≤ A n + ρ^{-1} Jcen (n-1)` and a uniform
  bound on both families, the weighted centre sum is at most `3` times the
  diagonal slice of the annular double sum.  `C_cen = 3` is an absolute numeral
  on the printed window `s ≤ 1/4`, `ρ ≥ 9`.

## The centre closure, and why it does not iterate

The manuscript iterates the one-step recursion into an infinite series and then
computes `Σ_{n=k+1}^m 3^{-2s(m-n) - d(n-1-k)} ≤^{-2s(m-k)}`.  The same constant
is obtained here without any iteration: the weighted centre sum `S` is (the
uniform bound plus the geometric weight), the weight satisfies `w(n) = 3^{2s}
w(n-1)` exactly, and the `ℤ`-shift is a `tsum` bijection, so summing the
one-step recursion gives

```
S ≤ T + 3^{2s} ρ^{-1} S ,
```

with `T` the weighted diagonal sum.  On `s ≤ 1/4` and `ρ ≥ 9` the contraction
factor is at most `7/36`, whence `S ≤ (36/29) T`, and `T = 3^{2s}` times the
diagonal slice in the spelling `Step1.annularDecompPre_of` expects.  Since
`(36/29)·(7/4) = 63/29 < 3`, `C_cen = 3` closes it.  This is exactly the geometric
factor `3^{2s}(1 - 3^{2s-d})^{-1}` of the centre interchange, evaluated with
slack on the printed window; the honest convergence condition `2s < d` is what
`s ≤ 1/4 < 1 ≤ d/2` supplies.

## The tolerance

The printed `W(p) = 3^{-dp}` at `C₀ = 1` -- which is what the one-step
recursion at `ρ = 3^d` produces -- sits far inside that condition; the numerals
`7/4`, `1/9`, `7/36`, `36/29`, `3` above are the explicit margin.

## References

* ABK26, (Step 1); (the cover interchange); (the centre resummation).
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02

noncomputable section

/-! ## Part A -- the lower-half reindexing `n = m − u` -/

private theorem negIdx_injective (m : ℤ) :
    Function.Injective (fun u : ℕ => m - (u : ℤ)) := by
  intro a b hab
  simp only at hab
  omega

private theorem mem_range_negIdx {m n : ℤ} (hn : n ≤ m) :
    n ∈ Set.range (fun u : ℕ => m - (u : ℤ)) :=
  ⟨(m - n).toNat, by
    show m - ((m - n).toNat : ℤ) = n
    omega⟩

/-- A family on `ℤ` supported on `{n ≤ m}` is summable iff its `n = m − u`
reindexing is. -/
theorem summable_guarded_iff {m : ℤ} {f : ℤ → ℝ}
    (h0 : ∀ n : ℤ, ¬ n ≤ m → f n = 0) :
    Summable (fun u : ℕ => f (m - (u : ℤ))) ↔ Summable f :=
  Function.Injective.summable_iff (negIdx_injective m)
    (fun n hn => h0 n fun hle => hn (mem_range_negIdx hle))

/-- The corresponding sum identity. -/
theorem tsum_guarded_eq {m : ℤ} {f : ℤ → ℝ}
    (h0 : ∀ n : ℤ, ¬ n ≤ m → f n = 0) :
    ∑' u : ℕ, f (m - (u : ℤ)) = ∑' n : ℤ, f n :=
  Function.Injective.tsum_eq (negIdx_injective m) (by
    intro n hn
    by_contra hc
    exact hn (h0 n fun hle => hc (mem_range_negIdx hle)))

/-- **The guarded geometric criterion.**  A nonnegative family that is uniformly
bounded on `{n ≤ m}` is summable against the Step-1 weight `3^{−2s(m−n)}`. -/
theorem summable_guarded_geom {s B : ℝ} {m : ℤ} {F : ℤ → ℝ} (hs0 : 0 < s)
    (hF0 : ∀ n : ℤ, 0 ≤ F n) (hFB : ∀ n : ℤ, n ≤ m → F n ≤ B) :
    Summable (fun n : ℤ =>
      if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * F n else 0) := by
  refine (summable_guarded_iff (m := m) (fun n hn => ite_eq_right hn)).mp ?_
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * s)) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-(2 * s)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs0])
  have hgeo : Summable (fun u : ℕ => ((3 : ℝ) ^ (-(2 * s))) ^ u * B) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_right B
  refine Summable.of_nonneg_of_le (fun u => ?_) (fun u => ?_) hgeo
  · rw [ite_eq_left (by omega : m - (u : ℤ) ≤ m)]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hF0 _)
  · rw [ite_eq_left (by omega : m - (u : ℤ) ≤ m)]
    have hcast : ((m - (m - (u : ℤ)) : ℤ) : ℝ) = (u : ℝ) := by
      push_cast
      ring
    rw [hcast, threeRpow_neg_natMul (2 * s) u]
    exact mul_le_mul_of_nonneg_left (hFB _ (by omega)) (pow_nonneg hr0 u)

/-! ## Part B -- the cover interchange -/

/-- **The `n`-row of the guarded annular family**.  For `n ≤ m` the row is the
finite sum over the annulus indices `j ∈ [n+1, m]`; for `n > m` it vanishes.
The manuscript's interchange of the order of summation is exactly this identity
together with `annDouble_eq_tsum_rows`. -/
theorem tsum_annFam_row (m : ℤ) (h : ℤ → ℤ → ℝ) (n : ℤ) :
    ∑' j : ℤ, annFam m h (j, n)
      = if n ≤ m then ∑ j ∈ Finset.Icc (n + 1) m, h j n else 0 := by
  classical
  by_cases hn : n ≤ m
  · rw [ite_eq_left hn]
    have hz : ∀ j ∉ Finset.Icc (n + 1) m, annFam m h (j, n) = 0 := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      rw [annFam_apply]
      exact ite_eq_right fun hc => hj ⟨by omega, hc.1⟩
    rw [tsum_eq_sum hz]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_Icc] at hj
    rw [annFam_apply, ite_eq_left ⟨hj.2, by omega⟩]
  · rw [ite_eq_right hn]
    have hz : ∀ j : ℤ, annFam m h (j, n) = 0 := by
      intro j
      rw [annFam_apply]
      exact ite_eq_right fun hc => hn (by omega)
    calc ∑' j : ℤ, annFam m h (j, n) = ∑' _ : ℤ, (0 : ℝ) := tsum_congr hz
      _ = 0 := tsum_zero

private theorem summable_annFam_swap {m : ℤ} {h : ℤ → ℤ → ℝ}
    (hsum : Summable (annFam m h)) :
    Summable (fun p : ℤ × ℤ => annFam m h (p.2, p.1)) :=
  (Equiv.summable_iff (f := annFam m h) (Equiv.prodComm ℤ ℤ)).mpr hsum

/-- **The annular double sum, summed over scales first.** -/
theorem annDouble_eq_tsum_rows {m : ℤ} {h : ℤ → ℤ → ℝ}
    (hsum : Summable (annFam m h)) :
    annDouble m h = ∑' n : ℤ, ∑' j : ℤ, annFam m h (j, n) := by
  calc annDouble m h = ∑' p : ℤ × ℤ, annFam m h p := (tsum_annFam hsum).symm
    _ = ∑' p : ℤ × ℤ, annFam m h (p.2, p.1) :=
        (Equiv.tsum_eq (Equiv.prodComm ℤ ℤ) (annFam m h)).symm
    _ = ∑' n : ℤ, ∑' j : ℤ, annFam m h (j, n) := (summable_annFam_swap hsum).tsum_prod

/-- The rows of a summable guarded annular family are summable in the scale. -/
theorem summable_annFam_rows {m : ℤ} {h : ℤ → ℤ → ℝ}
    (hsum : Summable (annFam m h)) :
    Summable (fun n : ℤ => ∑' j : ℤ, annFam m h (j, n)) :=
  (summable_annFam_swap hsum).prod

/-! ## Part C -- the two numerals of the centre closure -/

/-- Abstract-real core: a real whose square is `3` is at most `7/4`.  No
transcendental atom is in sight here, by design. -/
private theorem le_seven_quarters_of_sq {x : ℝ} (h : x ^ 2 = 3) : x ≤ 7 / 4 := by
  by_contra hc
  push Not at hc
  have hlt : (7 / 4 : ℝ) ^ 2 < x ^ 2 := pow_lt_pow_left₀ hc (by norm_num) (by norm_num)
  rw [h] at hlt
  norm_num at hlt

/-- `3^{2s} ≤ 7/4` on the printed window `s ≤ 1/4`. -/
theorem threeRpow_two_mul_le {s : ℝ} (hs14 : s ≤ 1 / 4) :
    (3 : ℝ) ^ (2 * s) ≤ 7 / 4 := by
  have hmono : (3 : ℝ) ^ (2 * s) ≤ (3 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith only [hs14])
  refine hmono.trans ?_
  have hx2 : ((3 : ℝ) ^ ((1 : ℝ) / 2)) ^ 2 = 3 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((1 : ℝ) / 2)) 2,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  exact le_seven_quarters_of_sq hx2

/-! ## Part D -- the centre closure -/

/-- **The Step-1 centre closure**, at the absolute constant `3`.

`Jcen` is the centre leg `J(□_n)` and `A n` the annulus maximum at step `n`
(the manuscript's `max_{z' ∈ 3^{n-1}ℤ^d ∩ (□_n ∖ □_{n-1})} J(z' + □_{n-1})`).  The
only structural input is the one-step subadditivity recursion `hstep`; the uniform
bounds make the weighted sums finite, which is what lets the recursion be summed
instead of iterated.

The conclusion is exactly the `hcen` slot of `Step1.annularDecompPre_of` at
`Ccen = 3`, once `A` is instantiated at `fun n ↦ Jann n (n-1)`. -/
theorem tsum_centre_le {s rho B : ℝ} {m : ℤ} {Jcen A : ℤ → ℝ}
    (hs0 : 0 < s) (hs14 : s ≤ 1 / 4) (hrho : 9 ≤ rho)
    (hJcen0 : ∀ n : ℤ, 0 ≤ Jcen n) (hA0 : ∀ n : ℤ, 0 ≤ A n)
    (hJcenB : ∀ n : ℤ, n ≤ m → Jcen n ≤ B) (hAB : ∀ n : ℤ, n ≤ m → A n ≤ B)
    (hstep : ∀ n : ℤ, Jcen n ≤ A n + rho⁻¹ * Jcen (n - 1)) :
    ∑' n : ℤ, (if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jcen n else 0)
      ≤ 3 * ∑' u : ℕ,
          (3 : ℝ) ^ (-(2 * s * ((m - (m - (u : ℤ) - 1) : ℤ) : ℝ))) * A (m - (u : ℤ)) := by
  classical
  set theta : ℝ := (3 : ℝ) ^ (2 * s) with htheta
  have htheta0 : (0 : ℝ) < theta := by rw [htheta]; positivity
  have hthetale : theta ≤ 7 / 4 := threeRpow_two_mul_le hs14
  have hrho0 : (0 : ℝ) < rho := by linarith only [hrho]
  have hrhoinv : rho⁻¹ ≤ 1 / 9 := by
    have h := inv_anti₀ (show (0 : ℝ) < 9 by norm_num) hrho
    have h19 : (9 : ℝ)⁻¹ = 1 / 9 := by norm_num
    rw [h19] at h
    exact h
  have hrhoinv0 : (0 : ℝ) ≤ rho⁻¹ := le_of_lt (inv_pos.mpr hrho0)
  set g : ℤ → ℝ := fun n =>
    if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jcen n else 0
  set t : ℤ → ℝ := fun n =>
    if n ≤ m then (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * A n else 0
  have hgpos : ∀ n : ℤ, n ≤ m →
      g n = (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * Jcen n := fun n hn => ite_eq_left hn
  have hgneg : ∀ n : ℤ, ¬ n ≤ m → g n = 0 := fun n hn => ite_eq_right hn
  have htpos : ∀ n : ℤ, n ≤ m →
      t n = (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) * A n := fun n hn => ite_eq_left hn
  have htneg : ∀ n : ℤ, ¬ n ≤ m → t n = 0 := fun n hn => ite_eq_right hn
  have hg0 : ∀ n : ℤ, 0 ≤ g n := by
    intro n
    by_cases hn : n ≤ m
    · rw [hgpos n hn]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hJcen0 n)
    · rw [hgneg n hn]
  have ht0 : ∀ n : ℤ, 0 ≤ t n := by
    intro n
    by_cases hn : n ≤ m
    · rw [htpos n hn]
      exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hA0 n)
    · rw [htneg n hn]
  have hgs : Summable g := summable_guarded_geom hs0 hJcen0 hJcenB
  have hts : Summable t := summable_guarded_geom hs0 hA0 hAB
  have hshiftsum : Summable (fun n : ℤ => g (n - 1)) :=
    (Equiv.summable_iff (f := g) (Equiv.subRight (1 : ℤ))).mpr hgs
  have hshifttsum : ∑' n : ℤ, g (n - 1) = ∑' n : ℤ, g n :=
    Equiv.tsum_eq (Equiv.subRight (1 : ℤ)) g
  -- the weight recursion `w(n) = 3^{2s} w(n-1)`
  have hweight : ∀ n : ℤ, (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ)))
      = theta * (3 : ℝ) ^ (-(2 * s * ((m - (n - 1) : ℤ) : ℝ))) := by
    intro n
    rw [htheta, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    push_cast
    ring
  -- the one-step recursion, weighted
  have hpt : ∀ n : ℤ, g n ≤ t n + (theta * rho⁻¹) * g (n - 1) := by
    intro n
    by_cases hn : n ≤ m
    · have hgn := hgpos n hn
      have htn := htpos n hn
      have hgn1 := hgpos (n - 1) (by omega)
      have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * s * ((m - n : ℤ) : ℝ))) :=
        Real.rpow_nonneg (by norm_num) _
      have hmul := mul_le_mul_of_nonneg_left (hstep n) hw0
      rw [hgn, htn, hgn1]
      refine hmul.trans (le_of_eq ?_)
      rw [hweight n]
      ring
    · rw [hgneg n hn]
      have h1 : (0 : ℝ) ≤ (theta * rho⁻¹) * g (n - 1) :=
        mul_nonneg (mul_nonneg (le_of_lt htheta0) hrhoinv0) (hg0 (n - 1))
      linarith only [ht0 n, h1]
  have hsumRHS : Summable (fun n : ℤ => t n + (theta * rho⁻¹) * g (n - 1)) :=
    hts.add (hshiftsum.mul_left (theta * rho⁻¹))
  have hstep2 : ∑' n : ℤ, g n
      ≤ (∑' n : ℤ, t n) + (theta * rho⁻¹) * ∑' n : ℤ, g n := by
    refine (Summable.tsum_le_tsum hpt hgs hsumRHS).trans ?_
    rw [Summable.tsum_add hts (hshiftsum.mul_left (theta * rho⁻¹)),
      tsum_mul_left, hshifttsum]
  -- the diagonal identity `T = 3^{2s} D`
  set D : ℝ := ∑' u : ℕ,
    (3 : ℝ) ^ (-(2 * s * ((m - (m - (u : ℤ) - 1) : ℤ) : ℝ))) * A (m - (u : ℤ)) with hD
  have hD0 : (0 : ℝ) ≤ D := by
    rw [hD]
    exact tsum_nonneg fun u =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hA0 _)
  have htD : ∑' n : ℤ, t n = theta * D := by
    rw [← tsum_guarded_eq (m := m) (f := t) htneg, hD, ← tsum_mul_left]
    refine tsum_congr fun u => ?_
    have htu := htpos (m - (u : ℤ)) (by omega)
    rw [htu, hweight (m - (u : ℤ))]
    ring
  -- close: `S ≤ 3^{2s} D + (7/36) S` and `S ≥ 0`
  have hSg0 : (0 : ℝ) ≤ ∑' n : ℤ, g n := tsum_nonneg hg0
  have hcoef : theta * rho⁻¹ ≤ 7 / 36 := by
    have h1 : theta * rho⁻¹ ≤ (7 / 4) * rho⁻¹ :=
      mul_le_mul_of_nonneg_right hthetale hrhoinv0
    have h2 : (7 / 4 : ℝ) * rho⁻¹ ≤ (7 / 4) * (1 / 9) :=
      mul_le_mul_of_nonneg_left hrhoinv (by norm_num)
    linarith only [h1, h2]
  have hshrink : (theta * rho⁻¹) * (∑' n : ℤ, g n) ≤ (7 / 36) * ∑' n : ℤ, g n :=
    mul_le_mul_of_nonneg_right hcoef hSg0
  have hthetaD : theta * D ≤ (7 / 4) * D := mul_le_mul_of_nonneg_right hthetale hD0
  rw [htD] at hstep2
  linarith only [hstep2, hshrink, hthetaD, hD0]

end

end Algsuperdiff.Section4.Provider.Annular
