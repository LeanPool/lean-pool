/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge.NormalizedLoading
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ClauseOne
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Proportion.SeriesTail

/-!
# AssemblyFeed

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

open Algsuperdiff.Section24.Sensitivity.Provider.HomogBridge
  (responseJ_scalarLoading_le_normalizedBlockResponseMax)


/-!
# The assembly feed of the clause-(i) composite

`ClauseOne.clauseOne_bound` (ABK26, Section 4.1) carries seven summability
binders, two `J`-leg families and the `e.bfJ.general` slot `hbfJ`.  This module
supplies the mechanical half of that feed:

* **Part A** -- the polynomial-absorption layer.  `1 + x <= 3^x` is the single
  transcendental input; everything above it is `linarith only` on abstract
  reals.  The two consumers are `linear_le_threeRpow` and
  `sq_linear_le_threeRpow`, which convert the annulus multiplicity `(m-n)+2`
  (and its square, from the `sigma-bar` continuity term) into an arbitrarily
  small power of the triadic weight.
* **Part B** -- the summability criteria for the guarded annular family
  `Resum.annFam`.  `summable_annFam_of_le` is the raw geometric comparison;
  `summable_annFam_of_poly_le` is the polynomial-times-geometric form; the three
  named producers `summable_annFam_sig`, `summable_annFam_grad` and
  `summable_annFam_l2` are the `hsumS`, `hsumG` and `hsumL` binders of
  `clauseOne_bound`, each derived *from the binder that sits next to it in the
  same theorem* (`hshom`, `hcsGn`, `hcsL2`) plus one partial-sum budget for the
  shell family.  No probabilistic input enters Part B.
* **Part C** -- the two lattice `J`-maxima, and the `hbfJ` discharge.
  `jLegField` and `jLegTranspose` -- the `Jlegf` and `Jlegt` families of
  `clauseOne_bound` -- are defined as the `0`-floored lattice maxima `max_{z in
  3^n Z^d cap cu_m} max_{|e|=1} J(z + cu_n;.)`, for the field and for its
  transpose.  The inner maximum over the unit sphere is an honest `sSup`: it is
  bounded above because the scalar response at the normalized loading is one of
  the *block* response values (the Section 2.4 bridge for the field leg,
  `BlockResponse`'s mirror for the transpose leg), so no junk value can enter.
  `hbfJ_latticeMax` is then A4a's producer at these carriers, and
  `summable_jLegField` / `summable_jLegTranspose` are the `hsumFl` / `hsumTl`
  binders -- **unconditional**: CoarseGraining's
  `maxDescendantNormalizedBlockResponseAtScale_le_uniform` bounds every scale
  by one cube-`cu_m` ellipticity constant, so the two `J`-sums are dominated by
  a bare geometric series.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Section3.Observable

noncomputable section



/-! ## Part A -- polynomial absorption into the triadic weight -/

private theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  exact le_trans Real.exp_one_lt_d9.le (by norm_num)

/-- **`1 + x <= 3^x` for `x >= 0`.**  The one transcendental input of the
polynomial-absorption layer: `exp y >= 1 + y` together with `log 3 >= 1`. -/
theorem one_add_le_threeRpow {x : ℝ} (hx : 0 ≤ x) : 1 + x ≤ (3 : ℝ) ^ x := by
  have hE : (3 : ℝ) ^ x = Real.exp (Real.log 3 * x) :=
    Real.rpow_def_of_pos (by norm_num) x
  have hexp : 1 + Real.log 3 * x ≤ Real.exp (Real.log 3 * x) := by
    linarith only [Real.add_one_le_exp (Real.log 3 * x)]
  have hmul : 1 * x ≤ Real.log 3 * x :=
    mul_le_mul_of_nonneg_right one_le_log_three hx
  rw [one_mul] at hmul
  rw [hE]
  linarith only [hexp, hmul]

/-- **The annulus multiplicity is absorbed by an arbitrarily small power of the
triadic weight**: `q + 2 <= 2 c^(-1) 3^(c q)` for `q >= 0` and `c` in `(0,1]`. -/
theorem linear_le_threeRpow {c q : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hq : 0 ≤ q) :
    q + 2 ≤ 2 / c * (3 : ℝ) ^ (c * q) := by
  have hx : (0 : ℝ) ≤ c * q := mul_nonneg hc0.le hq
  have h1 : 1 + c * q ≤ (3 : ℝ) ^ (c * q) := one_add_le_threeRpow hx
  have hcpos : (0 : ℝ) < 2 / c := by positivity
  have h2 : 2 / c * (1 + c * q) ≤ 2 / c * (3 : ℝ) ^ (c * q) :=
    mul_le_mul_of_nonneg_left h1 hcpos.le
  have hkey : 2 / c * (1 + c * q) = 2 / c + 2 * q := by
    field_simp
  have hge : (2 : ℝ) ≤ 2 / c := by
    rw [le_div_iff₀ hc0]
    linarith only [hc1]
  linarith only [h2, hkey, hge, hq]

/-- The squared form of `linear_le_threeRpow`. -/
theorem sq_linear_le_threeRpow {c q : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (hq : 0 ≤ q) :
    (q + 2) ^ 2 ≤ (4 / c) ^ 2 * (3 : ℝ) ^ (c * q) := by
  have hhalf0 : (0 : ℝ) < c / 2 := by linarith only [hc0]
  have hhalf1 : c / 2 ≤ 1 := by linarith only [hc0, hc1]
  have hlin := linear_le_threeRpow hhalf0 hhalf1 hq
  have hcoef : 2 / (c / 2) = 4 / c := by
    field_simp
    norm_num
  rw [hcoef] at hlin
  have hq2 : (0 : ℝ) ≤ q + 2 := by linarith only [hq]
  have hsq := pow_le_pow_left₀ hq2 hlin 2
  refine hsq.trans (le_of_eq ?_)
  rw [mul_pow]
  congr 1
  rw [← Real.rpow_natCast ((3 : ℝ) ^ (c / 2 * q)) 2,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  congr 1
  push_cast
  ring

/-! ## Part B -- summability of the guarded annular families -/

/-- **The geometric comparison.**  A nonnegative guarded annular family
dominated on its region by `K 3^(-c(m-n))` is summable. -/
theorem summable_annFam_of_le {m : ℤ} {h : ℤ → ℤ → ℝ} {K c : ℝ} (hc0 : 0 < c)
    (hh0 : ∀ j n, 0 ≤ h j n)
    (hle : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      h j n ≤ K * (3 : ℝ) ^ (-(c * ((m - n : ℤ) : ℝ)))) :
    Summable (annFam m h) := by
  refine Summable.of_nonneg_of_le (annFam_nonneg hh0) ?_
    ((annWeightFam_summable hc0 m).mul_left K)
  rintro ⟨j, n⟩
  by_cases hg : j ≤ m ∧ n ≤ j - 1
  · rw [annFam_apply, ite_eq_left hg, annWeightFam_def, annFam_apply, ite_eq_left hg]
    exact hle j n hg.1 hg.2
  · rw [annFam_apply, ite_eq_right hg, annWeightFam_def, annFam_apply, ite_eq_right hg, mul_zero]

/-- **The polynomial-times-geometric comparison.**  If the family is dominated
by `K ((m-n)+2)^2 3^(b(m-n))` with `b + 2c <= 0` for some `c` in `(0,1]`, it is
summable: the square of the annulus multiplicity costs only `3^(c(m-n))`. -/
theorem summable_annFam_of_poly_le {m : ℤ} {h : ℤ → ℤ → ℝ} {K b c : ℝ}
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hK0 : 0 ≤ K) (hbc : b + 2 * c ≤ 0)
    (hh0 : ∀ j n, 0 ≤ h j n)
    (hle : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      h j n ≤ K * (((m - n : ℤ) : ℝ) + 2) ^ 2 * (3 : ℝ) ^ (b * ((m - n : ℤ) : ℝ))) :
    Summable (annFam m h) := by
  refine summable_annFam_of_le (K := K * (4 / c) ^ 2) hc0 hh0 ?_
  intro j n hj hn
  have hq : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by
    have hz : (0 : ℤ) ≤ m - n := by omega
    exact_mod_cast hz
  have hpoly := sq_linear_le_threeRpow (c := c) hc0 hc1 hq
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (b * ((m - n : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hprod : (3 : ℝ) ^ (c * ((m - n : ℤ) : ℝ)) * (3 : ℝ) ^ (b * ((m - n : ℤ) : ℝ))
      = (3 : ℝ) ^ ((c + b) * ((m - n : ℤ) : ℝ)) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  have hmono : (3 : ℝ) ^ ((c + b) * ((m - n : ℤ) : ℝ))
      ≤ (3 : ℝ) ^ (-(c * ((m - n : ℤ) : ℝ))) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hcb : c + b ≤ -c := by linarith only [hbc]
    have hstep := mul_le_mul_of_nonneg_right hcb hq
    calc (c + b) * ((m - n : ℤ) : ℝ) ≤ -c * ((m - n : ℤ) : ℝ) := hstep
      _ = -(c * ((m - n : ℤ) : ℝ)) := by ring
  have hK2 : (0 : ℝ) ≤ K * (4 / c) ^ 2 := by positivity
  calc h j n ≤ K * (((m - n : ℤ) : ℝ) + 2) ^ 2 * (3 : ℝ) ^ (b * ((m - n : ℤ) : ℝ)) :=
        hle j n hj hn
    _ = K * (3 : ℝ) ^ (b * ((m - n : ℤ) : ℝ)) * (((m - n : ℤ) : ℝ) + 2) ^ 2 := by ring
    _ ≤ K * (3 : ℝ) ^ (b * ((m - n : ℤ) : ℝ))
          * ((4 / c) ^ 2 * (3 : ℝ) ^ (c * ((m - n : ℤ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hpoly (mul_nonneg hK0 hw0)
    _ = K * (4 / c) ^ 2 * ((3 : ℝ) ^ (c * ((m - n : ℤ) : ℝ))
          * (3 : ℝ) ^ (b * ((m - n : ℤ) : ℝ))) := by ring
    _ = K * (4 / c) ^ 2 * (3 : ℝ) ^ ((c + b) * ((m - n : ℤ) : ℝ)) := by rw [hprod]
    _ ≤ K * (4 / c) ^ 2 * (3 : ℝ) ^ (-(c * ((m - n : ℤ) : ℝ))) :=
        mul_le_mul_of_nonneg_left hmono hK2

/-! ### The three named producers -/

private theorem add_two_le_sq {q : ℝ} (hq : 0 ≤ q) : q + 2 ≤ (q + 2) ^ 2 := by
  have h1 : (1 : ℝ) ≤ q + 2 := by linarith only [hq]
  calc q + 2 = (q + 2) * 1 := by ring
    _ ≤ (q + 2) * (q + 2) := mul_le_mul_of_nonneg_left h1 (by linarith only [hq])
    _ = (q + 2) ^ 2 := by ring

private theorem sig_pointwise {s gamma a B q sigv : ℝ} (hq : 0 ≤ q) (ha0 : 0 ≤ a)
    (hB0 : 0 ≤ B) (hsig : sigv ≤ (a * q + B) ^ 2 * (3 : ℝ) ^ (2 * gamma * q)) :
    (3 : ℝ) ^ (-(s * q)) * sigv
      ≤ (a + B) ^ 2 * (q + 2) ^ 2 * (3 : ℝ) ^ ((2 * gamma - s) * q) := by
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * q)) := Real.rpow_nonneg (by norm_num) _
  have hBq : (0 : ℝ) ≤ B * q := mul_nonneg hB0 hq
  have haq : (0 : ℝ) ≤ a * q := mul_nonneg ha0 hq
  have hexp : (a + B) * (q + 2) = a * q + 2 * a + B * q + 2 * B := by ring
  have hlin : a * q + B ≤ (a + B) * (q + 2) := by
    linarith only [hexp, ha0, hB0, hBq]
  have hnn : (0 : ℝ) ≤ a * q + B := by linarith only [haq, hB0]
  have hsq : (a * q + B) ^ 2 ≤ ((a + B) * (q + 2)) ^ 2 := pow_le_pow_left₀ hnn hlin 2
  have hprod : (3 : ℝ) ^ (-(s * q)) * (3 : ℝ) ^ (2 * gamma * q)
      = (3 : ℝ) ^ ((2 * gamma - s) * q) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  calc (3 : ℝ) ^ (-(s * q)) * sigv
      ≤ (3 : ℝ) ^ (-(s * q)) * ((a * q + B) ^ 2 * (3 : ℝ) ^ (2 * gamma * q)) :=
        mul_le_mul_of_nonneg_left hsig hw0
    _ ≤ (3 : ℝ) ^ (-(s * q)) * (((a + B) * (q + 2)) ^ 2 * (3 : ℝ) ^ (2 * gamma * q)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (by norm_num) _)) hw0
    _ = (a + B) ^ 2 * (q + 2) ^ 2
          * ((3 : ℝ) ^ (-(s * q)) * (3 : ℝ) ^ (2 * gamma * q)) := by ring
    _ = (a + B) ^ 2 * (q + 2) ^ 2 * (3 : ℝ) ^ ((2 * gamma - s) * q) := by rw [hprod]

/-- **The `hsumS` binder.**  The `sigma-bar` continuity family is summable over
the annular region: the `hshom` bound of `clauseOne_bound` is
`(a(m-n)+B)^2 3^{2 gamma (m-n)}`, and `8 gamma <= s` leaves the honest decay
`3^{-(3/4)s(m-n)}` after the weight. -/
theorem summable_annFam_sig {m : ℤ} {s gamma a B : ℝ} {sig : ℤ → ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hg0 : 0 ≤ gamma) (hsg : 8 * gamma ≤ s)
    (ha0 : 0 ≤ a) (hB0 : 0 ≤ B) (hsig0 : ∀ n, 0 ≤ sig n)
    (hshom : ∀ n : ℤ, n ≤ m - 1 →
      sig n ≤ (a * ((m - n : ℤ) : ℝ) + B) ^ 2
        * (3 : ℝ) ^ (2 * gamma * ((m - n : ℤ) : ℝ))) :
    Summable (annFam m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)) := by
  refine summable_annFam_of_poly_le (K := (a + B) ^ 2) (b := 2 * gamma - s) (c := s / 4)
    (by linarith only [hs0]) (by linarith only [hs1, hs0]) (by positivity)
    (by linarith only [hsg, hg0, hs0])
    (fun _ n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hsig0 n)) ?_
  intro j n _hj hn
  have hq : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by
    have hz : (0 : ℤ) ≤ m - n := by omega
    exact_mod_cast hz
  exact sig_pointwise hq ha0 hB0 (hshom n (by omega))

private theorem grad_pointwise {s Kgn Ksh q g S : ℝ} (hq : 0 ≤ q) (hKgn : 0 ≤ Kgn)
    (hKsh : 0 ≤ Ksh) (hg : g ≤ Kgn * (q + 2) * S)
    (hpart : S ≤ Ksh * (3 : ℝ) ^ (s / 4 * q)) :
    (3 : ℝ) ^ (-(s * q)) * g
      ≤ Kgn * Ksh * (q + 2) ^ 2 * (3 : ℝ) ^ ((s / 4 - s) * q) := by
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * q)) := Real.rpow_nonneg (by norm_num) _
  have hq2 : (0 : ℝ) ≤ q + 2 := by linarith only [hq]
  have hcoef : (0 : ℝ) ≤ Kgn * (q + 2) := mul_nonneg hKgn hq2
  have hstep : Kgn * (q + 2) * S ≤ Kgn * (q + 2) * (Ksh * (3 : ℝ) ^ (s / 4 * q)) :=
    mul_le_mul_of_nonneg_left hpart hcoef
  have hsqr : q + 2 ≤ (q + 2) ^ 2 := add_two_le_sq hq
  have hK0 : (0 : ℝ) ≤ Kgn * Ksh * (3 : ℝ) ^ (s / 4 * q) :=
    mul_nonneg (mul_nonneg hKgn hKsh) (Real.rpow_nonneg (by norm_num) _)
  have hgrow : Kgn * Ksh * (3 : ℝ) ^ (s / 4 * q) * (q + 2)
      ≤ Kgn * Ksh * (3 : ℝ) ^ (s / 4 * q) * (q + 2) ^ 2 :=
    mul_le_mul_of_nonneg_left hsqr hK0
  have hprod : (3 : ℝ) ^ (-(s * q)) * (3 : ℝ) ^ (s / 4 * q)
      = (3 : ℝ) ^ ((s / 4 - s) * q) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  calc (3 : ℝ) ^ (-(s * q)) * g
      ≤ (3 : ℝ) ^ (-(s * q)) * (Kgn * (q + 2) * S) := mul_le_mul_of_nonneg_left hg hw0
    _ ≤ (3 : ℝ) ^ (-(s * q)) * (Kgn * (q + 2) * (Ksh * (3 : ℝ) ^ (s / 4 * q))) :=
        mul_le_mul_of_nonneg_left hstep hw0
    _ = (3 : ℝ) ^ (-(s * q)) * (Kgn * Ksh * (3 : ℝ) ^ (s / 4 * q) * (q + 2)) := by ring
    _ ≤ (3 : ℝ) ^ (-(s * q)) * (Kgn * Ksh * (3 : ℝ) ^ (s / 4 * q) * (q + 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hgrow hw0
    _ = Kgn * Ksh * (q + 2) ^ 2
          * ((3 : ℝ) ^ (-(s * q)) * (3 : ℝ) ^ (s / 4 * q)) := by ring
    _ = Kgn * Ksh * (q + 2) ^ 2 * (3 : ℝ) ^ ((s / 4 - s) * q) := by rw [hprod]

/-- **The `hsumG` binder.**  From the `hcsGn` slot of `clauseOne_bound` and a
partial-sum budget `Ksh 3^{(s/4)(m-n)}` for the shell family. -/
theorem summable_annFam_grad {m : ℤ} {s Kgn Ksh : ℝ} {gradNf : ℤ → ℤ → ℝ} {A : ℤ → ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hKgn : 0 ≤ Kgn) (hKsh : 0 ≤ Ksh)
    (hgrad0 : ∀ j n, 0 ≤ gradNf j n)
    (hcsGn : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      gradNf j n ≤ Kgn * (((m - n : ℤ) : ℝ) + 2)
        * ∑ v ∈ Finset.range ((m - n).toNat + 2), A (m - (v : ℤ)) ^ 2)
    (hpart : ∀ n : ℤ, n ≤ m →
      ∑ v ∈ Finset.range ((m - n).toNat + 2), A (m - (v : ℤ)) ^ 2
        ≤ Ksh * (3 : ℝ) ^ (s / 4 * ((m - n : ℤ) : ℝ))) :
    Summable (annFam m
      (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * gradNf j n)) := by
  refine summable_annFam_of_poly_le (K := Kgn * Ksh) (b := s / 4 - s) (c := s / 4)
    (by linarith only [hs0]) (by linarith only [hs1, hs0]) (mul_nonneg hKgn hKsh)
    (by linarith only [hs0])
    (fun j n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hgrad0 j n)) ?_
  intro j n hj hn
  have hq : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by
    have hz : (0 : ℤ) ≤ m - n := by omega
    exact_mod_cast hz
  exact grad_pointwise hq hKgn hKsh (hcsGn j n hj hn) (hpart n (by omega))

private theorem l2_pointwise {s gamma Kl2 Ksh q g S : ℝ} (hq : 0 ≤ q) (hKl2 : 0 ≤ Kl2)
    (hKsh : 0 ≤ Ksh) (hg : g ≤ Kl2 * (q + 2) * (3 : ℝ) ^ (2 * gamma * q) * S)
    (hpart : S ≤ Ksh * (3 : ℝ) ^ (s / 4 * q)) :
    (3 : ℝ) ^ (-(s * q)) * g
      ≤ Kl2 * Ksh * (q + 2) ^ 2 * (3 : ℝ) ^ ((2 * gamma + s / 4 - s) * q) := by
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * q)) := Real.rpow_nonneg (by norm_num) _
  have hg0 : (0 : ℝ) ≤ (3 : ℝ) ^ (2 * gamma * q) := Real.rpow_nonneg (by norm_num) _
  have hq2 : (0 : ℝ) ≤ q + 2 := by linarith only [hq]
  have hcoef : (0 : ℝ) ≤ Kl2 * (q + 2) * (3 : ℝ) ^ (2 * gamma * q) :=
    mul_nonneg (mul_nonneg hKl2 hq2) hg0
  have hstep : Kl2 * (q + 2) * (3 : ℝ) ^ (2 * gamma * q) * S
      ≤ Kl2 * (q + 2) * (3 : ℝ) ^ (2 * gamma * q) * (Ksh * (3 : ℝ) ^ (s / 4 * q)) :=
    mul_le_mul_of_nonneg_left hpart hcoef
  have hsqr : q + 2 ≤ (q + 2) ^ 2 := add_two_le_sq hq
  have hK0 : (0 : ℝ) ≤ Kl2 * Ksh * ((3 : ℝ) ^ (2 * gamma * q) * (3 : ℝ) ^ (s / 4 * q)) :=
    mul_nonneg (mul_nonneg hKl2 hKsh)
      (mul_nonneg hg0 (Real.rpow_nonneg (by norm_num) _))
  have hgrow : Kl2 * Ksh * ((3 : ℝ) ^ (2 * gamma * q) * (3 : ℝ) ^ (s / 4 * q)) * (q + 2)
      ≤ Kl2 * Ksh * ((3 : ℝ) ^ (2 * gamma * q) * (3 : ℝ) ^ (s / 4 * q)) * (q + 2) ^ 2 :=
    mul_le_mul_of_nonneg_left hsqr hK0
  have hprod : (3 : ℝ) ^ (-(s * q))
        * ((3 : ℝ) ^ (2 * gamma * q) * (3 : ℝ) ^ (s / 4 * q))
      = (3 : ℝ) ^ ((2 * gamma + s / 4 - s) * q) := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
      ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    congr 1
    ring
  calc (3 : ℝ) ^ (-(s * q)) * g
      ≤ (3 : ℝ) ^ (-(s * q)) * (Kl2 * (q + 2) * (3 : ℝ) ^ (2 * gamma * q) * S) :=
        mul_le_mul_of_nonneg_left hg hw0
    _ ≤ (3 : ℝ) ^ (-(s * q)) * (Kl2 * (q + 2) * (3 : ℝ) ^ (2 * gamma * q)
          * (Ksh * (3 : ℝ) ^ (s / 4 * q))) := mul_le_mul_of_nonneg_left hstep hw0
    _ = (3 : ℝ) ^ (-(s * q)) * (Kl2 * Ksh
          * ((3 : ℝ) ^ (2 * gamma * q) * (3 : ℝ) ^ (s / 4 * q)) * (q + 2)) := by ring
    _ ≤ (3 : ℝ) ^ (-(s * q)) * (Kl2 * Ksh
          * ((3 : ℝ) ^ (2 * gamma * q) * (3 : ℝ) ^ (s / 4 * q)) * (q + 2) ^ 2) :=
        mul_le_mul_of_nonneg_left hgrow hw0
    _ = Kl2 * Ksh * (q + 2) ^ 2 * ((3 : ℝ) ^ (-(s * q))
          * ((3 : ℝ) ^ (2 * gamma * q) * (3 : ℝ) ^ (s / 4 * q))) := by ring
    _ = Kl2 * Ksh * (q + 2) ^ 2 * (3 : ℝ) ^ ((2 * gamma + s / 4 - s) * q) := by
        rw [hprod]

/-- **The `hsumL` binder.**  From the `hcsL2` slot of `clauseOne_bound` and the
same partial-sum budget; the extra `3^{2 gamma (m-n)}` of the value leg is
absorbed by `8 gamma <= s`. -/
theorem summable_annFam_l2 {m : ℤ} {s gamma Kl2 Ksh : ℝ} {L2f : ℤ → ℤ → ℝ} {A : ℤ → ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hsg : 8 * gamma ≤ s)
    (hKl2 : 0 ≤ Kl2) (hKsh : 0 ≤ Ksh) (hL20 : ∀ j n, 0 ≤ L2f j n)
    (hcsL2 : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      L2f j n ≤ Kl2 * (((m - n : ℤ) : ℝ) + 2)
        * (3 : ℝ) ^ (2 * gamma * ((m - n : ℤ) : ℝ))
        * ∑ v ∈ Finset.range ((m - n).toNat + 2), A (m - (v : ℤ)) ^ 2)
    (hpart : ∀ n : ℤ, n ≤ m →
      ∑ v ∈ Finset.range ((m - n).toNat + 2), A (m - (v : ℤ)) ^ 2
        ≤ Ksh * (3 : ℝ) ^ (s / 4 * ((m - n : ℤ) : ℝ))) :
    Summable (annFam m
      (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * L2f j n)) := by
  refine summable_annFam_of_poly_le (K := Kl2 * Ksh) (b := 2 * gamma + s / 4 - s)
    (c := s / 4) (by linarith only [hs0]) (by linarith only [hs1, hs0])
    (mul_nonneg hKl2 hKsh) (by linarith only [hsg])
    (fun j n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hL20 j n)) ?_
  intro j n hj hn
  have hq : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by
    have hz : (0 : ℤ) ≤ m - n := by omega
    exact_mod_cast hz
  exact l2_pointwise hq hKl2 hKsh (hcsL2 j n hj hn) (hpart n (by omega))

/-! ## Part C -- the two lattice `J`-maxima and the `hbfJ` discharge -/

variable {d : ℕ}

/-- The value set of the scalar response of one cube at the normalized unit
loadings `(sigma^{-1/2} e, sigma^{1/2} e)`, `|e| = 1` -- the quantity the
manuscript's `J`-maxima are taken over. -/
def scalarResponseSet {U : Domain d} (a : CoeffOn U) (sigma : PositiveScalar) : Set ℝ :=
  {x | ∃ e : Vec d, vecNorm e = 1 ∧
    x = responseJ U a (inverseSqrtLoad sigma e) (sqrtLoad sigma e)}

/-- The one-cube scalar response maximum.  It is an honest supremum: the value
set is bounded above at every cube of a triadic family, because each of its
elements is one of the *block* response values (`scalarResponseSet_bddAbove`
below). -/
def scalarResponseMax {U : Domain d} (a : CoeffOn U) (sigma : PositiveScalar) : ℝ :=
  sSup (scalarResponseSet a sigma)

/-- **The field-leg value set is bounded above**, by the Section 2.4 normalized
loading bridge. -/
theorem scalarResponseSet_bddAbove [NeZero d] (F : TriadicCoeffFamily d)
    (R : TriadicCube d) (sigma : PositiveScalar) :
    BddAbove (scalarResponseSet (F.coeffOn R) sigma) := by
  refine ⟨normalizedBlockResponseMax R F (isotropicComparatorMatrix sigma), ?_⟩
  intro x hx
  obtain ⟨e, he, rfl⟩ := hx
  exact
    responseJ_scalarLoading_le_normalizedBlockResponseMax
    F R sigma.2 he

/-- **The transpose-leg value set is bounded above**, by `BlockResponse`'s
mirror of the same bridge. -/
theorem scalarResponseSet_transpose_bddAbove [NeZero d] (F : TriadicCoeffFamily d)
    (R : TriadicCube d) (sigma : PositiveScalar) :
    BddAbove (scalarResponseSet (F.coeffOn R).transpose sigma) := by
  refine ⟨normalizedBlockResponseMax R F (isotropicComparatorMatrix sigma), ?_⟩
  intro x hx
  obtain ⟨e, he, rfl⟩ := hx
  exact responseJ_transpose_scalarLoading_le_normalizedBlockResponseMax F R sigma.2 he

theorem responseJ_le_scalarResponseMax [NeZero d] (F : TriadicCoeffFamily d)
    (R : TriadicCube d) (sigma : PositiveScalar) {e : Vec d} (he : vecNorm e = 1) :
    responseJ (cubeDomain R) (F.coeffOn R) (inverseSqrtLoad sigma e) (sqrtLoad sigma e)
      ≤ scalarResponseMax (F.coeffOn R) sigma :=
  le_csSup (scalarResponseSet_bddAbove F R sigma) ⟨e, he, rfl⟩

theorem responseJ_transpose_le_scalarResponseMax [NeZero d] (F : TriadicCoeffFamily d)
    (R : TriadicCube d) (sigma : PositiveScalar) {e : Vec d} (he : vecNorm e = 1) :
    responseJ (cubeDomain R) (F.coeffOn R).transpose
        (inverseSqrtLoad sigma e) (sqrtLoad sigma e)
      ≤ scalarResponseMax (F.coeffOn R).transpose sigma :=
  le_csSup (scalarResponseSet_transpose_bddAbove F R sigma) ⟨e, he, rfl⟩

theorem scalarResponseMax_le_normalizedBlockResponseMax [NeZero d]
    (F : TriadicCoeffFamily d) (R : TriadicCube d) (sigma : PositiveScalar) :
    scalarResponseMax (F.coeffOn R) sigma
      ≤ normalizedBlockResponseMax R F (isotropicComparatorMatrix sigma) := by
  refine Real.sSup_le ?_ (normalizedBlockResponseMax_nonneg R F _)
  intro x hx
  obtain ⟨e, he, rfl⟩ := hx
  exact
    responseJ_scalarLoading_le_normalizedBlockResponseMax
    F R sigma.2 he

theorem scalarResponseMax_transpose_le_normalizedBlockResponseMax [NeZero d]
    (F : TriadicCoeffFamily d) (R : TriadicCube d) (sigma : PositiveScalar) :
    scalarResponseMax (F.coeffOn R).transpose sigma
      ≤ normalizedBlockResponseMax R F (isotropicComparatorMatrix sigma) := by
  refine Real.sSup_le ?_ (normalizedBlockResponseMax_nonneg R F _)
  intro x hx
  obtain ⟨e, he, rfl⟩ := hx
  exact responseJ_transpose_scalarLoading_le_normalizedBlockResponseMax F R sigma.2 he

/-! ### The two lattice maxima -/

/-- **The field `J`-maximum of the manuscript's lattice enumeration**:
`max_{z in 3^n Z^d cap cu_m} max_{|e|=1} J(z + cu_n, a; sigma^{-1/2} e,
sigma^{1/2} e)`, `0`-floored (which changes nothing -- the entries are
nonnegative responses). -/
def jLegField (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d) (n : ℤ) : ℝ :=
  Proportion.fmax (latticeCubeFinset d n m) fun v =>
    scalarResponseMax
      ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
        (latticeCube n v))
      (Annealed.sigmaBar M m)

/-- The transposed-leg `J`-maximum. -/
def jLegTranspose (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d) (n : ℤ) :
    ℝ :=
  Proportion.fmax (latticeCubeFinset d n m) fun v =>
    scalarResponseMax
      ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
        (latticeCube n v)).transpose
      (Annealed.sigmaBar M m)

theorem jLegField_nonneg (M : ABKModel d) (L m : ℤ) (omega : Cutoff.CutoffSample d)
    (n : ℤ) : 0 ≤ jLegField M L m omega n :=
  Proportion.fmax_nonneg _ _

theorem jLegTranspose_nonneg (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) (n : ℤ) : 0 ≤ jLegTranspose M L m omega n :=
  Proportion.fmax_nonneg _ _

/-- The `hfld` slot of `ClauseOne.hbfJ_of_lattice_bounds`, by definition of the
lattice maximum. -/
theorem responseJ_le_jLegField [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {n : ℤ} (hnm : n ≤ m) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) {e : Vec d} (he : vecNorm e = 1) :
    responseJ (cubeDomain (latticeCube n v))
        ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
          (latticeCube n v))
        (inverseSqrtLoad (Annealed.sigmaBar M m) e)
        (sqrtLoad (Annealed.sigmaBar M m) e)
      ≤ jLegField M L m omega n := by
  refine le_trans
    (responseJ_le_scalarResponseMax
      (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
      (latticeCube n v) (Annealed.sigmaBar M m) he) ?_
  exact Proportion.le_fmax
    (f := fun w : Fin d → ℤ => scalarResponseMax
      ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
        (latticeCube n w)) (Annealed.sigmaBar M m))
    ((mem_latticeCubeFinset_iff hnm v).mpr hv)

/-- The `htrn` slot of `ClauseOne.hbfJ_of_lattice_bounds`. -/
theorem responseJ_transpose_le_jLegTranspose [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {n : ℤ} (hnm : n ≤ m) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) {e : Vec d} (he : vecNorm e = 1) :
    responseJ (cubeDomain (latticeCube n v))
        ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
          (latticeCube n v)).transpose
        (inverseSqrtLoad (Annealed.sigmaBar M m) e)
        (sqrtLoad (Annealed.sigmaBar M m) e)
      ≤ jLegTranspose M L m omega n := by
  refine le_trans
    (responseJ_transpose_le_scalarResponseMax
      (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
      (latticeCube n v) (Annealed.sigmaBar M m) he) ?_
  exact Proportion.le_fmax
    (f := fun w : Fin d → ℤ => scalarResponseMax
      ((Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega).coeffOn
        (latticeCube n w)).transpose (Annealed.sigmaBar M m))
    ((mem_latticeCubeFinset_iff hnm v).mpr hv)

/-- **The `hbfJ` binder of `ClauseOne.clauseOne_bound`, discharged.**  With the
two `J`-legs *defined* as the lattice maxima, A4a's producer applies with no
remaining hypothesis beyond the manuscript's `C >= 1`. -/
theorem hbfJ_latticeMax [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {Cbf : ℝ} (hCbf : 1 ≤ Cbf) :
    ∀ l : ℕ,
      maxDescendantNormalizedBlockResponseAtScale (originCube d m) (m - (l : ℤ))
          (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m))
        ≤ Cbf * (jLegField M L m omega (m - (l : ℤ))
            + jLegTranspose M L m omega (m - (l : ℤ))) :=
  hbfJ_of_lattice_bounds M L m omega hCbf (jLegField_nonneg M L m omega)
    (jLegTranspose_nonneg M L m omega)
    (fun l v hv e he => responseJ_le_jLegField M L m omega (by omega) hv he)
    (fun l v hv e he => responseJ_transpose_le_jLegTranspose M L m omega (by omega) hv he)

/-! ### The two `J`-sums are unconditionally summable -/

/-- Both lattice maxima are bounded by ONE cube-`cu_m` ellipticity constant,
uniformly in the scale: CoarseGraining's
`maxDescendantNormalizedBlockResponseAtScale_le_uniform` is scale free. -/
theorem jLegField_le_uniform [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {n : ℤ} (hnm : n ≤ m) :
    jLegField M L m omega n
      ≤ normalizedBlockResponseUniformBound (originCube d m)
          (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
  have hscale : (originCube d m).scale = m := rfl
  have hle := maxDescendantNormalizedBlockResponseAtScale_le_uniform (originCube d m)
    (k := n) (by rw [hscale]; exact hnm)
    (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
    (isotropicComparatorMatrix (Annealed.sigmaBar M m))
  have hnn := maxDescendantNormalizedBlockResponseAtScale_nonneg (originCube d m)
    (k := n) (by rw [hscale]; exact hnm)
    (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
    (isotropicComparatorMatrix (Annealed.sigmaBar M m))
  refine Proportion.fmax_le (by linarith only [hle, hnn]) ?_
  intro v hv
  refine le_trans (scalarResponseMax_le_normalizedBlockResponseMax _ _ _) ?_
  exact normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
    (a := Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
    (Q := originCube d m) (R := latticeCube n v) (k := n) _
    (latticeCube_mem_descendantsAtScale hnm ((mem_latticeCubeFinset_iff hnm v).mp hv))

theorem jLegTranspose_le_uniform [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {n : ℤ} (hnm : n ≤ m) :
    jLegTranspose M L m omega n
      ≤ normalizedBlockResponseUniformBound (originCube d m)
          (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) := by
  have hscale : (originCube d m).scale = m := rfl
  have hle := maxDescendantNormalizedBlockResponseAtScale_le_uniform (originCube d m)
    (k := n) (by rw [hscale]; exact hnm)
    (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
    (isotropicComparatorMatrix (Annealed.sigmaBar M m))
  have hnn := maxDescendantNormalizedBlockResponseAtScale_nonneg (originCube d m)
    (k := n) (by rw [hscale]; exact hnm)
    (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
    (isotropicComparatorMatrix (Annealed.sigmaBar M m))
  refine Proportion.fmax_le (by linarith only [hle, hnn]) ?_
  intro v hv
  refine le_trans (scalarResponseMax_transpose_le_normalizedBlockResponseMax _ _ _) ?_
  exact normalizedBlockResponseMax_le_uniform_of_mem_descendantsAtScale
    (a := Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
    (Q := originCube d m) (R := latticeCube n v) (k := n) _
    (latticeCube_mem_descendantsAtScale hnm ((mem_latticeCubeFinset_iff hnm v).mp hv))

private theorem summable_geom_const {s B : ℝ} (hs0 : 0 < s)
    {J : ℤ → ℝ} {m : ℤ} (hJ0 : ∀ n, 0 ≤ J n)
    (hJ : ∀ l : ℕ, J (m - (l : ℤ)) ≤ B) :
    Summable (fun l : ℕ => (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * J (m - (l : ℤ))) := by
  have hr0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(2 * s)) := Real.rpow_nonneg (by norm_num) _
  have hr1 : (3 : ℝ) ^ (-(2 * s)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hs0])
  have hpow : ∀ l : ℕ, (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) = ((3 : ℝ) ^ (-(2 * s))) ^ l := by
    intro l
    rw [← threeRpow_neg_natMul (2 * s) l]
    congr 1
    ring
  have hgeo : Summable (fun l : ℕ => ((3 : ℝ) ^ (-(2 * s))) ^ l * B) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_right B
  refine Summable.of_nonneg_of_le
    (fun l => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hJ0 _)) ?_ hgeo
  intro l
  rw [hpow l]
  exact mul_le_mul_of_nonneg_left (hJ l) (pow_nonneg hr0 l)

/-- **The `hsumFl` binder, unconditional.** -/
theorem summable_jLegField [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {s : ℝ} (hs0 : 0 < s) :
    Summable (fun l : ℕ =>
      (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * jLegField M L m omega (m - (l : ℤ))) := by
  have hB : ∀ l : ℕ, jLegField M L m omega (m - (l : ℤ))
      ≤ normalizedBlockResponseUniformBound (originCube d m)
          (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) :=
    fun l => jLegField_le_uniform M L m omega (by omega)
  exact summable_geom_const hs0 (jLegField_nonneg M L m omega) hB

/-- **The `hsumTl` binder, unconditional.** -/
theorem summable_jLegTranspose [NeZero d] (M : ABKModel d) (L m : ℤ)
    (omega : Cutoff.CutoffSample d) {s : ℝ} (hs0 : 0 < s) :
    Summable (fun l : ℕ =>
      (3 : ℝ) ^ (-(2 * s) * (l : ℝ)) * jLegTranspose M L m omega (m - (l : ℤ))) := by
  have hB : ∀ l : ℕ, jLegTranspose M L m omega (m - (l : ℤ))
      ≤ normalizedBlockResponseUniformBound (originCube d m)
          (Support.fluxCorrectedCoeffFamily M L m (originCube d m) omega)
          (isotropicComparatorMatrix (Annealed.sigmaBar M m)) :=
    fun l => jLegTranspose_le_uniform M L m omega (by omega)
  exact summable_geom_const hs0 (jLegTranspose_nonneg M L m omega) hB

end

end Algsuperdiff.Section4.Provider.Annular
