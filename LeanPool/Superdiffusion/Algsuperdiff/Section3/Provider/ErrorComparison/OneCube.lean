/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.ErrorComparison.Monotonicity

/-!
# OneCube

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Provider: the one-cube descendant bound for the homogenization error

This file proves a local version of the display `e.bound.one.cube.by.mathcalE` of
ABK26: for every `k ∈ (-∞,m] ∩ ℤ`,

> `max_{z ∈ 3^k ℤ^d ∩ □_m} 𝓔_{s,∞,q}(z + □_k; a, a₀)
>    ≤ 3^{s(m-k)} 𝓔_{s,∞,q}(□_m; a, a₀)`,
> `avg_{z ∈ 3^k ℤ^d ∩ □_m} 𝓔_{s,p,q}(z + □_k; a, a₀)
>    ≤ 3^{s(m-k)} 𝓔_{s,p,q}(□_m; a, a₀)`,

with the ambient quantifiers of the source, i.e. `m ∈ ℤ`, `p, q ∈ [1,∞]`
and `s ∈ (0,∞)`.

## Scope

The per-descendant form of the first line of the display is proved here at
`p = ∞` for every finite `q ∈ [1,∞)`; CoarseGraining previously had only the
case `q = 1`
(`Homogenization.Book.Ch02.homogenizationErrorOnCube_infinity_one_descendantsAtScale_le`).

## Main results

* `scaleResponse_depth_descendant_le`: the `p = ∞` one-scale responses of a
  cube and of one of its descendants compare, after the depth shift.
* `homogenizationErrorOnCube_infinity_finite_le_of_mem_descendantsAtScale`:
  the per-descendant form of the display at `p = ∞` and finite `q`.

## References

* ABK26, `e.bound.one.cube.by.mathcalE`.
-/

namespace Algsuperdiff.Section3.Provider.ErrorComparison

open HCPolySupport

/-! ## Comparing the scale responses of a cube and of a descendant -/

/-- Descending `l` scales below a descendant `R` of `Q` at scale `k` proves on the
scale `Q.scale - (l + (Q.scale - k))`, so the `p = ∞` one-scale responses
compare. -/
theorem scaleResponse_depth_descendant_le {d : ℕ} [NeZero d]
    {Q R : TriadicCube d} {k : ℤ} (F : Book.Ch02.TriadicCoeffFamily d)
    (a0 : Mat d) (hR : R ∈ descendantsAtScale Q k) (l : ℕ) :
    Book.Ch02.scaleResponseAtScale R (R.scale - (l : ℤ)) .infinity F a0 ≤
      Book.Ch02.scaleResponseAtScale Q
        (Q.scale - ((l + Int.toNat (Q.scale - k) : ℕ) : ℤ)) .infinity F a0 := by
  have hk : k ≤ Q.scale := descendant_scale_le_of_mem_descendantsAtScale hR
  have hh : ((Int.toNat (Q.scale - k) : ℕ) : ℤ) = Q.scale - k :=
    Int.toNat_of_nonneg (sub_nonneg.mpr hk)
  have hRscale : R.scale = k := descendant_scale_eq_of_mem_descendantsAtScale hR
  have hscale :
      R.scale - (l : ℤ) = Q.scale - ((l + Int.toNat (Q.scale - k) : ℕ) : ℤ) := by
    rw [hRscale, Nat.cast_add, hh]
    ring
  have hl : R.scale - (l : ℤ) ≤ R.scale :=
    sub_le_self R.scale (by exact_mod_cast Nat.zero_le l)
  simpa [hscale] using
    (Book.Ch02.scaleResponseAtScale_infinity_le_of_mem_descendantsAtScale
      (Q := Q) (R := R) (k := k) (l := R.scale - (l : ℤ)) F a0 hR hl)

/-! ## The finite-`q` endpoint `p = ∞` -/

/-- Per-descendant form of `e.bound.one.cube.by.mathcalE` (ABK26) at `p = ∞` and
finite `q`. -/
theorem homogenizationErrorOnCube_infinity_finite_le_of_mem_descendantsAtScale
    {d : ℕ} [NeZero d] {Q R : TriadicCube d} {k : ℤ}
    (F : Book.Ch02.TriadicCoeffFamily d) (a0 : Mat d) {s q : ℝ}
    (hs : 0 < s) (hq : 1 ≤ q) (hR : R ∈ descendantsAtScale Q k) :
    Book.Ch02.HomogenizationErrorOnCube R s .infinity (.finite q) F a0 ≤
      Real.rpow (3 : ℝ) (s * (Int.toNat (Q.scale - k) : ℝ)) *
        Book.Ch02.HomogenizationErrorOnCube Q s .infinity (.finite q) F a0 := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  set h : ℕ := Int.toNat (Q.scale - k) with hhdef
  set fQ : ℕ → ℝ := fun n =>
    Book.Ch02.geometricWeight s q n *
      Real.rpow
        (Book.Ch02.scaleResponseAtScale Q (Q.scale - (n : ℤ)) .infinity F a0) q
    with hfQdef
  set fR : ℕ → ℝ := fun n =>
    Book.Ch02.geometricWeight s q n *
      Real.rpow
        (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity F a0) q
    with hfRdef
  set factor : ℝ := Real.rpow (3 : ℝ) (s * q * (h : ℝ)) with hfactordef
  have hfactor_nonneg : 0 ≤ factor := by
    rw [hfactordef]
    exact Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _
  have hweight_nonneg : ∀ n : ℕ, 0 ≤ Book.Ch02.geometricWeight s q n := by
    intro n
    simpa [Book.Ch02.geometricWeight_eq_old] using
      HCPolySupport.geometricWeight_nonneg (s := s) (q := q) n
        (mul_pos hs hq0).le
  have hfQ_nonneg : ∀ n : ℕ, 0 ≤ fQ n := by
    intro n
    rw [hfQdef]
    exact mul_nonneg (hweight_nonneg n)
      (Real.rpow_nonneg (scaleResponse_depth_nonneg Q F a0 n) q)
  have hfR_nonneg : ∀ n : ℕ, 0 ≤ fR n := by
    intro n
    rw [hfRdef]
    exact mul_nonneg (hweight_nonneg n)
      (Real.rpow_nonneg (scaleResponse_depth_nonneg R F a0 n) q)
  have hsumQ : Summable fQ := by
    rw [hfQdef]
    exact summable_geometricWeight_mul_scaleResponse_rpow Q F a0 hs hq0
  have htail : Summable fun n : ℕ => fQ (n + h) := (summable_nat_add_iff h).2 hsumQ
  have hterm : ∀ n : ℕ, fR n ≤ factor * fQ (n + h) := by
    intro n
    have hshift :
        Book.Ch02.geometricWeight s q n =
          factor * Book.Ch02.geometricWeight s q (n + h) := by
      rw [hfactordef]
      simpa [Book.Ch02.geometricWeight_eq_old] using
        (HCPolySupport.geometricWeight_shift (s := s) (q := q) h n)
    have hresp :
        Real.rpow
            (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity F a0)
            q ≤
          Real.rpow
            (Book.Ch02.scaleResponseAtScale Q
              (Q.scale - ((n + h : ℕ) : ℤ)) .infinity F a0) q :=
      Real.rpow_le_rpow (scaleResponse_depth_nonneg R F a0 n)
        (scaleResponse_depth_descendant_le F a0 hR n) hq0.le
    calc
      fR n =
          factor *
            (Book.Ch02.geometricWeight s q (n + h) *
              Real.rpow
                (Book.Ch02.scaleResponseAtScale R (R.scale - (n : ℤ)) .infinity F a0)
                q) := by
        rw [hfRdef]
        dsimp only
        rw [hshift]
        ring
      _ ≤ factor *
          (Book.Ch02.geometricWeight s q (n + h) *
            Real.rpow
              (Book.Ch02.scaleResponseAtScale Q
                (Q.scale - ((n + h : ℕ) : ℤ)) .infinity F a0) q) := by
        refine mul_le_mul_of_nonneg_left ?_ hfactor_nonneg
        exact mul_le_mul_of_nonneg_left hresp (hweight_nonneg (n + h))
      _ = factor * fQ (n + h) := by
        rw [hfQdef]
  have hscaled : Summable fun n : ℕ => factor * fQ (n + h) := htail.mul_left factor
  have hsumR : Summable fR := Summable.of_nonneg_of_le hfR_nonneg hterm hscaled
  have hsumLe : ∑' n : ℕ, fR n ≤ ∑' n : ℕ, factor * fQ (n + h) :=
    Summable.tsum_le_tsum hterm hsumR hscaled
  have htailLe : (∑' n : ℕ, fQ (n + h)) ≤ ∑' n : ℕ, fQ n := by
    have hsplit := hsumQ.sum_add_tsum_nat_add h
    have hprefix : 0 ≤ ∑ i ∈ Finset.range h, fQ i :=
      Finset.sum_nonneg fun i _ => hfQ_nonneg i
    linarith
  have hAle : (∑' n : ℕ, fR n) ≤ factor * ∑' n : ℕ, fQ n := by
    calc
      (∑' n : ℕ, fR n) ≤ ∑' n : ℕ, factor * fQ (n + h) := hsumLe
      _ = factor * ∑' n : ℕ, fQ (n + h) := by
          simpa using (Summable.tsum_mul_left factor htail)
      _ ≤ factor * ∑' n : ℕ, fQ n := mul_le_mul_of_nonneg_left htailLe hfactor_nonneg
  have hA_nonneg : 0 ≤ ∑' n : ℕ, fR n := tsum_nonneg hfR_nonneg
  have hB_nonneg : 0 ≤ ∑' n : ℕ, fQ n := tsum_nonneg hfQ_nonneg
  have hfactor_rpow :
      Real.rpow factor (1 / q) = Real.rpow (3 : ℝ) (s * (h : ℝ)) := by
    have hqne : q ≠ 0 := hq0.ne'
    have hmul :=
      Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3) (s * q * (h : ℝ)) (1 / q)
    have hexp : s * q * (h : ℝ) * (1 / q) = s * (h : ℝ) := by
      field_simp
    rw [hexp] at hmul
    rw [hfactordef]
    exact hmul.symm
  rw [homogenizationErrorOnCube_infinity_finite_eq_rpow_tsum,
    homogenizationErrorOnCube_infinity_finite_eq_rpow_tsum]
  calc
    Real.rpow (∑' n : ℕ, fR n) (1 / q) ≤
        Real.rpow (factor * ∑' n : ℕ, fQ n) (1 / q) :=
      Real.rpow_le_rpow hA_nonneg hAle (by positivity)
    _ = Real.rpow factor (1 / q) * Real.rpow (∑' n : ℕ, fQ n) (1 / q) :=
      Real.mul_rpow hfactor_nonneg hB_nonneg
    _ = Real.rpow (3 : ℝ) (s * (h : ℝ)) *
        Real.rpow (∑' n : ℕ, fQ n) (1 / q) := by rw [hfactor_rpow]

end Algsuperdiff.Section3.Provider.ErrorComparison
