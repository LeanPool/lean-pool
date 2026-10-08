/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormFoundations
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SingularValueTheory
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.MeanInequalitiesPow

/-!
# High-contrast homogenization: Entry.Analysis.SchattenHolderInequalities

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# Schatten Holder Inequalities

The trace-Hölder inequality for non-commuting matrices, in Schatten norms.  For `N` factors
and their product `A_1 ⋯ A_N` it first establishes the dimension-free lossy bound
`|tr (A_1 ⋯ A_N)| ≤ N ∏ k, |A_k|_{S_N}`, whose constant is the word length `N` rather than
the matrix dimension, and then removes that loss to obtain the sharp bound
`|tr (A_1 ⋯ A_N)| ≤ ∏ k, |A_k|_{S_N}`.  The Hermitian block form of the sharp bound is the
trace estimate consumed by the matrix-averaging step `l.fixed.geometry.matrix.averaging`; the
file also records the elementary ingredients of the argument: the even trace identity
`tr(Y^N) = |Y|_{S_N}^N`, the `ℓ^p ⊆ ℓ^1` embedding, and finite Hölder with all exponents
equal to `N`.
-/

section
/-!
## The even trace bridge, the `ℓ^p ⊆ ℓ^1` embedding and finite Hölder

Three elementary ingredients of the printed proof of
`l.fixed.geometry.matrix.averaging`, all deterministic:

* `trace_even_pow_eq_absSchattenNorm_pow` — for even `N ≥ 2` and a symmetric block `H`,
  `tr ((toFullBlockMat H) ^ N) = |H|_{S_N} ^ N`, and that number is nonnegative.  This is the
  print's "since `N` is even, `tr(Y^N) = |Y|_{S_N}^N` for every symmetric matrix `Y`".  It is
  the existing `HCPoly.Entry.Analysis.SchattenSpectral.absSchattenNorm_even_pow_eq_trace` with the
  real
  index `2 * (k : ℝ)` reconciled with the natural index `N`; the identity is already
  proved there and no eigenvalue sum is restated here.

* `sum_rpow_le_rpow_sum` — the `ℓ^p ⊆ ℓ^1` embedding `∑ i, s i ^ p ≤ (∑ i, s i) ^ p` for
  `1 ≤ p` and nonnegative `s`.  This is the step that turns a block-size exponent `|B| / N`
  into the printed `2 / N` and `|B| / 2`, and it is exactly where "no singleton blocks"
  (`2 ≤ |B|`, hence `1 ≤ |B| / 2`) is consumed.

* `sum_prod_le_prod_sum_rpow` — generalized finite Hölder for `N` nonnegative families with
  all exponents equal to `N`, proved by normalising each family to unit `ℓ^N` mass and
  applying weighted AM-GM (`Real.geom_mean_le_arith_mean_weighted`) with equal weights `1/N`.

**What this file does not contain, and why.**  Trace Hölder
`|tr (A_1 ⋯ A_N)| ≤ ∏ k, |A_k|_{S_N}` for arbitrary noncommuting symmetric factors, is **not**
proved here and is **not** stated here as a `def`, an axiom or a `sorry`.  It is absent and is
neither used nor assumed by any declaration in this file.  The obstruction is genuine: even a
constant-factor variant of the inequality does not hold.  Nothing below depends on it.
-/

namespace HCPolySupport.HighContrast.Analysis

open scoped BigOperators

noncomputable section

variable {d : ℕ}

/-! ## The even trace identity -/

/-- **The even trace bridge.**  For an even natural `N ≥ 2` and a symmetric block `H`,
`tr ((toFullBlockMat H) ^ N) = |H|_{S_N} ^ N`.  The print's sentence "since `N` is even,
`tr(Y^N) = |Y|_{S_N}^N` for every symmetric matrix `Y`" (`l.fixed.geometry.matrix.averaging`).

Derived from `absSchattenNorm_even_pow_eq_trace`, which carries the real index `2 * (k : ℝ)`
and the natural power `2 * k`; `N = 2 * k` with `1 ≤ k` comes from `hNeven` and `hN`. -/
theorem trace_even_pow_eq_absSchattenNorm_pow {H : BlockMat d}
    (hH : (toFullBlockMat H).IsHermitian) {N : ℕ} (hN : 2 ≤ N) (hNeven : Even N) :
    Matrix.trace ((toFullBlockMat H) ^ N) = absSchattenNorm (N : ℝ) H ^ N := by
  obtain ⟨k, hk⟩ := hNeven
  have hNk : N = 2 * k := by omega
  have hk1 : 1 ≤ k := by omega
  have hcast : (N : ℝ) = 2 * (k : ℝ) := by rw [hNk]; push_cast; ring
  subst hNk
  rw [hcast]
  exact (absSchattenNorm_even_pow_eq_trace hH k hk1).symm

/-! ## The `ℓ^p ⊆ ℓ^1` embedding -/

/-- **`ℓ^p ⊆ ℓ^1`.**  For `1 ≤ p` and nonnegative `s`, `∑ i ∈ t, s i ^ p ≤ (∑ i ∈ t, s i) ^ p`
(real `rpow`).  Applied with `p = |B| / 2` and `2 ≤ |B|` this is the printed passage from a
block of size `|B|` to the exponent `|B| / 2` on the single sum `∑ i, (tr E[Y_i^N])^{2/N}`. -/
theorem sum_rpow_le_rpow_sum {ι : Type*} (t : Finset ι) (s : ι → ℝ)
    (hs : ∀ i ∈ t, 0 ≤ s i) {p : ℝ} (hp : 1 ≤ p) :
    ∑ i ∈ t, s i ^ p ≤ (∑ i ∈ t, s i) ^ p := by
  classical
  induction t using Finset.cons_induction with
  | empty => simp [Real.zero_rpow (by linarith only [hp] : p ≠ 0)]
  | cons a t ha ih =>
      have hsa : 0 ≤ s a := hs a (Finset.mem_cons_self a t)
      have hst : ∀ i ∈ t, 0 ≤ s i := fun i hi => hs i (Finset.mem_cons_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ t, s i := Finset.sum_nonneg hst
      rw [Finset.sum_cons, Finset.sum_cons]
      calc s a ^ p + ∑ i ∈ t, s i ^ p
          ≤ s a ^ p + (∑ i ∈ t, s i) ^ p := by linarith only [ih hst]
        _ ≤ (s a + ∑ i ∈ t, s i) ^ p := Real.add_rpow_le_rpow_add hsa hsum hp

/-! ## Generalized finite Hölder for `N` families -/

/-- **Generalized finite Hölder**, all `N` exponents equal to `N`.  For nonnegative families
`f 0, …, f (N-1)` on a finset `t`,
`∑ i ∈ t, ∏ k, f k i ≤ ∏ k, (∑ i ∈ t, f k i ^ N) ^ (1/N)`.

Route: if some family has zero `ℓ^N` mass it vanishes on `t` and both sides are `0`; otherwise
normalise each family to unit mass and apply weighted AM-GM with equal weights `1/N`. -/
theorem sum_prod_le_prod_sum_rpow {ι : Type*} {N : ℕ} (hN : 0 < N) (t : Finset ι)
    (f : Fin N → ι → ℝ) (hf : ∀ k, ∀ i ∈ t, 0 ≤ f k i) :
    ∑ i ∈ t, ∏ k : Fin N, f k i
      ≤ ∏ k : Fin N, (∑ i ∈ t, f k i ^ (N : ℝ)) ^ ((N : ℝ)⁻¹) := by
  classical
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the `ℓ^N` masses
  set S : Fin N → ℝ := fun k => (∑ i ∈ t, f k i ^ (N : ℝ)) ^ ((N : ℝ)⁻¹) with hS
  have hSnn : ∀ k, 0 ≤ S k := fun k =>
    Real.rpow_nonneg (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf k i hi) _) _
  by_cases hzero : ∃ k, S k = 0
  · -- a vanishing family kills both sides
    obtain ⟨k₀, hk₀⟩ := hzero
    have hsum0 : ∑ i ∈ t, f k₀ i ^ (N : ℝ) = 0 := by
      by_contra hne
      have hpos : 0 < ∑ i ∈ t, f k₀ i ^ (N : ℝ) :=
        lt_of_le_of_ne (Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf k₀ i hi) _)
          (Ne.symm hne)
      exact absurd hk₀ (ne_of_gt (Real.rpow_pos_of_pos hpos _))
    have hfi : ∀ i ∈ t, f k₀ i = 0 := by
      intro i hi
      have := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j hj => Real.rpow_nonneg (hf k₀ j hj) ((N : ℝ)))).1 hsum0 i hi
      by_contra hne
      exact hne (by
        have hpos : 0 < f k₀ i := lt_of_le_of_ne (hf k₀ i hi) (Ne.symm hne)
        exact absurd this (ne_of_gt (Real.rpow_pos_of_pos hpos _)))
    have hlhs : ∑ i ∈ t, ∏ k : Fin N, f k i = 0 :=
      Finset.sum_eq_zero fun i hi =>
        Finset.prod_eq_zero (Finset.mem_univ k₀) (hfi i hi)
    have hrhs : (0 : ℝ) ≤ ∏ k : Fin N, S k := Finset.prod_nonneg fun k _ => hSnn k
    rw [hlhs]
    exact hrhs
  · push Not at hzero
    have hSpos : ∀ k, 0 < S k := fun k => lt_of_le_of_ne (hSnn k) (Ne.symm (hzero k))
    -- normalised families
    set g : Fin N → ι → ℝ := fun k i => f k i / S k with hg
    have hgnn : ∀ k, ∀ i ∈ t, 0 ≤ g k i := fun k i hi =>
      div_nonneg (hf k i hi) (hSnn k)
    have hmass : ∀ k, ∑ i ∈ t, g k i ^ (N : ℝ) = 1 := by
      intro k
      have hbase : (0 : ℝ) ≤ ∑ i ∈ t, f k i ^ (N : ℝ) :=
        Finset.sum_nonneg fun i hi => Real.rpow_nonneg (hf k i hi) _
      have hSk : S k ^ (N : ℝ) = ∑ i ∈ t, f k i ^ (N : ℝ) := by
        change ((∑ i ∈ t, f k i ^ (N : ℝ)) ^ ((N : ℝ)⁻¹)) ^ (N : ℝ) = _
        rw [← Real.rpow_mul hbase, inv_mul_cancel₀ (ne_of_gt hNR), Real.rpow_one]
      have : ∑ i ∈ t, g k i ^ (N : ℝ) = (∑ i ∈ t, f k i ^ (N : ℝ)) / S k ^ (N : ℝ) := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [hg, Real.div_rpow (hf k i hi) (hSnn k)]
      rw [this, hSk, div_self]
      exact ne_of_gt (by
        have := hSpos k
        have hSkpow : 0 < S k ^ (N : ℝ) := Real.rpow_pos_of_pos this _
        rw [hSk] at hSkpow
        exact hSkpow)
    -- pointwise AM-GM with equal weights
    have hpt : ∀ i ∈ t, ∏ k : Fin N, g k i ≤ ∑ k : Fin N, ((N : ℝ)⁻¹) * g k i ^ (N : ℝ) := by
      intro i hi
      have hw : ∀ k : Fin N, k ∈ (Finset.univ : Finset (Fin N)) → (0 : ℝ) ≤ (N : ℝ)⁻¹ :=
        fun k _ => le_of_lt (inv_pos.2 hNR)
      have hw' : ∑ _k : Fin N, ((N : ℝ)⁻¹) = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact mul_inv_cancel₀ (ne_of_gt hNR)
      have hz : ∀ k : Fin N, k ∈ (Finset.univ : Finset (Fin N)) →
          (0 : ℝ) ≤ g k i ^ (N : ℝ) := fun k _ => Real.rpow_nonneg (hgnn k i hi) _
      have := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin N))
        (fun _ => (N : ℝ)⁻¹) (fun k => g k i ^ (N : ℝ)) hw hw' hz
      refine le_trans (le_of_eq ?_) this
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [← Real.rpow_mul (hgnn k i hi), mul_inv_cancel₀ (ne_of_gt hNR), Real.rpow_one]
    -- sum and exchange
    have hnorm : ∑ i ∈ t, ∏ k : Fin N, g k i ≤ 1 := by
      calc ∑ i ∈ t, ∏ k : Fin N, g k i
          ≤ ∑ i ∈ t, ∑ k : Fin N, ((N : ℝ)⁻¹) * g k i ^ (N : ℝ) :=
            Finset.sum_le_sum hpt
        _ = ∑ k : Fin N, ((N : ℝ)⁻¹) * ∑ i ∈ t, g k i ^ (N : ℝ) := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun k _ => by rw [Finset.mul_sum]
        _ = 1 := by
            simp only [hmass, mul_one]
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
            exact mul_inv_cancel₀ (ne_of_gt hNR)
    -- undo the normalisation
    have hfactor : ∀ i ∈ t, ∏ k : Fin N, f k i
        = (∏ k : Fin N, S k) * ∏ k : Fin N, g k i := by
      intro i _
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have hne : S k ≠ 0 := ne_of_gt (hSpos k)
      change f k i = S k * (f k i / S k)
      field_simp
    have hprodS : (0 : ℝ) ≤ ∏ k : Fin N, S k := Finset.prod_nonneg fun k _ => hSnn k
    calc ∑ i ∈ t, ∏ k : Fin N, f k i
        = (∏ k : Fin N, S k) * ∑ i ∈ t, ∏ k : Fin N, g k i := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl hfactor
      _ ≤ (∏ k : Fin N, S k) * 1 := by
          exact mul_le_mul_of_nonneg_left hnorm hprodS
      _ = ∏ k : Fin N, S k := mul_one _

end

end HCPolySupport.HighContrast.Analysis
end

section
/-!
## Lossy trace Holder for singular norms

This file proves the dimension-free lossy product bound used in the trace
Holder route. The loss is the word length `N`, not the matrix dimension.
-/

namespace HCPolySupport.HighContrast.Analysis

open scoped BigOperators Matrix.Norms.L2Operator

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem list_prod_norm_le {N : ℕ} (A : Fin N → Matrix n n ℝ) :
    ‖(List.ofFn A).prod‖ ≤ ∏ k : Fin N, ‖A k‖ := by
  induction N with
  | zero =>
      rw [List.ofFn_zero, List.prod_nil, Fintype.prod_empty]
      by_cases hn : Nonempty n
      · let := hn
        exact le_of_eq CStarRing.norm_one
      · let : IsEmpty n := not_nonempty_iff.mp hn
        have : Subsingleton (Matrix n n ℝ) := inferInstance
        rw [Subsingleton.elim (1 : Matrix n n ℝ) 0, norm_zero]
        norm_num
  | succ N ih =>
      rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
      exact (norm_mul_le _ _).trans
        (mul_le_mul_of_nonneg_left (ih (fun k => A k.succ)) (norm_nonneg _))

theorem rank_prod_sub_prod_le {N : ℕ}
    (A C : Fin N → Matrix n n ℝ) :
    ((List.ofFn A).prod - (List.ofFn C).prod).rank ≤
      ∑ k, (A k - C k).rank := by
  induction N with
  | zero =>
      simp [Matrix.rank_zero]
  | succ N ih =>
      let Atail : Fin N → Matrix n n ℝ := fun k => A k.succ
      let Ctail : Fin N → Matrix n n ℝ := fun k => C k.succ
      have hprodA :
          (List.ofFn A).prod = A 0 * (List.ofFn Atail).prod := by
        simp only [Atail]
        rw [List.ofFn_succ, List.prod_cons]
      have hprodC :
          (List.ofFn C).prod = C 0 * (List.ofFn Ctail).prod := by
        simp only [Ctail]
        rw [List.ofFn_succ, List.prod_cons]
      have hdecomp :
          (List.ofFn A).prod - (List.ofFn C).prod =
            (A 0 - C 0) * (List.ofFn Atail).prod +
              C 0 * ((List.ofFn Atail).prod - (List.ofFn Ctail).prod) := by
        rw [hprodA, hprodC]
        noncomm_ring
      rw [hdecomp, Fin.sum_univ_succ]
      calc
        ((A 0 - C 0) * (List.ofFn Atail).prod +
              C 0 * ((List.ofFn Atail).prod - (List.ofFn Ctail).prod)).rank
            ≤ ((A 0 - C 0) * (List.ofFn Atail).prod).rank +
                (C 0 * ((List.ofFn Atail).prod - (List.ofFn Ctail).prod)).rank :=
              rank_add_le _ _
        _ ≤ (A 0 - C 0).rank +
                ((List.ofFn Atail).prod - (List.ofFn Ctail).prod).rank := by
              exact Nat.add_le_add (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
        _ ≤ (A 0 - C 0).rank + ∑ k : Fin N, (Atail k - Ctail k).rank := by
              exact Nat.add_le_add_left (ih Atail Ctail) _
        _ = (A 0 - C 0).rank + ∑ k : Fin N, (A k.succ - C k.succ).rank := rfl

private theorem sum_comp_div_le_card_mul_sum {D N : ℕ} (hN : 0 < N)
    (v : ℕ → ℝ) (hv : ∀ i, 0 ≤ v i) :
    ∑ i ∈ Finset.range D, v (i / N) ≤
      (N : ℝ) * ∑ r ∈ Finset.range D, v r := by
  classical
  calc
    ∑ i ∈ Finset.range D, v (i / N)
        = ∑ r ∈ Finset.range D, ∑ i ∈ (Finset.range D).filter (fun i => i / N = r), v r := by
            exact (Finset.sum_fiberwise_of_maps_to'
              (s := Finset.range D) (t := Finset.range D)
              (g := fun i => i / N)
              (fun i hi => Finset.mem_range.2 ((Nat.div_le_self i N).trans_lt
                (Finset.mem_range.1 hi)))
              v).symm
    _ ≤ ∑ r ∈ Finset.range D, (N : ℝ) * v r := by
            refine Finset.sum_le_sum fun r hr => ?_
            have hcard :
                ((Finset.range D).filter (fun i => i / N = r)).card ≤ N := by
              have hcard' :
                  ((Finset.range D).filter (fun i => i / N = r)).card ≤
                    (Finset.range N).card := by
                refine Finset.card_le_card_of_injOn (fun i => i % N) ?_ ?_
                · intro i hi
                  exact Finset.mem_range.2 (Nat.mod_lt i hN)
                · intro a ha b hb hab
                  simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at ha hb
                  have hmod : a % N = b % N := hab
                  calc
                    a = N * (a / N) + a % N := (Nat.div_add_mod a N).symm
                    _ = N * (b / N) + b % N := by rw [ha.2, hb.2, hmod]
                    _ = b := Nat.div_add_mod b N
              simpa [Finset.card_range] using hcard'
            rw [Finset.sum_const, nsmul_eq_mul]
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (hv r)
    _ = (N : ℝ) * ∑ r ∈ Finset.range D, v r := by
            rw [Finset.mul_sum]

theorem sum_block_bound {D N : ℕ} (hN : 0 < N) (u v : ℕ → ℝ)
    (hu : Antitone u) (hv : ∀ i, 0 ≤ v i) (h : ∀ r, u (N * r) ≤ v r) :
    ∑ i ∈ Finset.range D, u i ≤ (N:ℝ) * ∑ r ∈ Finset.range D, v r := by
  calc
    ∑ i ∈ Finset.range D, u i ≤ ∑ i ∈ Finset.range D, v (i / N) := by
      refine Finset.sum_le_sum fun i _ => ?_
      exact (hu (Nat.mul_div_le i N)).trans (by simpa [Nat.mul_comm] using h (i / N))
    _ ≤ (N:ℝ) * ∑ r ∈ Finset.range D, v r :=
      sum_comp_div_le_card_mul_sum hN v hv

theorem singularValueAt_prod_le {N : ℕ} (hN : 0 < N)
    (A : Fin N → Matrix n n ℝ) (r : ℕ) :
    singularValueAt ((List.ofFn A).prod) (N*r) ≤ ∏ k, singularValueAt (A k) r := by
  classical
  cases N with
  | zero => omega
  | succ N =>
      choose R hRrank hRnorm using fun k : Fin (N + 1) => exists_rank_approximation (A k) r
      let C : Fin (N + 1) → Matrix n n ℝ := fun k => A k - R k
      let X : Matrix n n ℝ := (List.ofFn A).prod
      let Y : Matrix n n ℝ := X - (List.ofFn C).prod
      have hYrank : Y.rank ≤ (N + 1) * r := by
        calc
          Y.rank ≤ ∑ k, (A k - C k).rank := by
            simpa [X, Y] using rank_prod_sub_prod_le A C
          _ = ∑ k, (R k).rank := by
            refine Finset.sum_congr rfl fun k _ => ?_
            simp [C]
          _ ≤ ∑ _k : Fin (N + 1), r := Finset.sum_le_sum fun k _ => hRrank k
          _ = (N + 1) * r := by
            simp [Finset.sum_const]
      have happrox := singularValueAt_le_norm_sub X Y hYrank
      have hres : X - Y = (List.ofFn C).prod := by
        simp [Y]
      have hnorm :
          ‖X - Y‖ ≤ ∏ k, singularValueAt (A k) r := by
        rw [hres]
        exact (list_prod_norm_le C).trans
          (Finset.prod_le_prod₀ (fun k _ => norm_nonneg (C k)) fun k _ => by
            simpa [C] using hRnorm k)
      exact happrox.trans hnorm

private theorem sum_range_singularValueAt_eq_sum_singularValues₀
    (X : Matrix n n ℝ) (f : ℝ → ℝ) :
    ∑ r ∈ Finset.range (Fintype.card n), f (singularValueAt X r) =
      ∑ i : Fin (Fintype.card n), f (singularValues₀ X i) := by
  rw [← Fin.sum_univ_eq_sum_range]
  exact Finset.sum_congr rfl fun i _ => by
    simp [singularValueAt]

private theorem sum_range_singularValueAt_rpow_eq_sum_singularValues
    (X : Matrix n n ℝ) (p : ℝ) :
    ∑ r ∈ Finset.range (Fintype.card n), singularValueAt X r ^ p =
      ∑ i, singularValues X i ^ p := by
  calc
    ∑ r ∈ Finset.range (Fintype.card n), singularValueAt X r ^ p =
        ∑ i : Fin (Fintype.card n), singularValues₀ X i ^ p :=
      sum_range_singularValueAt_eq_sum_singularValues₀ X (fun x => x ^ p)
    _ = ∑ i, singularValues X i ^ p :=
      sum_singularValues₀ X (fun x => x ^ p)

theorem abs_trace_prod_le_card_mul_prod_singularNorm {N : ℕ} (hN : 0 < N)
    (A : Fin N → Matrix n n ℝ) :
    |Matrix.trace ((List.ofFn A).prod)| ≤
      (N:ℝ) * ∏ k, singularNorm (N:ℝ) (A k) := by
  let X : Matrix n n ℝ := (List.ofFn A).prod
  let D := Fintype.card n
  have hNRnonneg : (0 : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.zero_le N
  calc
    |Matrix.trace ((List.ofFn A).prod)|
        ≤ ∑ i : Fin D, singularValues₀ X i := by
            exact abs_trace_le_sum_singularValues₀ X
    _ = ∑ i ∈ Finset.range D, singularValueAt X i := by
            exact (sum_range_singularValueAt_eq_sum_singularValues₀ X (fun x => x)).symm
    _ ≤ (N:ℝ) * ∑ r ∈ Finset.range D, ∏ k, singularValueAt (A k) r :=
            sum_block_bound hN (singularValueAt X)
              (fun r => ∏ k, singularValueAt (A k) r)
              (singularValueAt_antitone X)
              (fun r => Finset.prod_nonneg fun k _ => singularValueAt_nonneg (A k) r)
              (fun r => singularValueAt_prod_le hN A r)
    _ ≤ (N:ℝ) * ∏ k, (∑ r ∈ Finset.range D,
            singularValueAt (A k) r ^ (N : ℝ)) ^ ((N : ℝ)⁻¹) := by
            exact mul_le_mul_of_nonneg_left
              (sum_prod_le_prod_sum_rpow hN (Finset.range D)
                (fun k r => singularValueAt (A k) r)
                (fun k r _ => singularValueAt_nonneg (A k) r))
              hNRnonneg
    _ = (N:ℝ) * ∏ k, singularNorm (N:ℝ) (A k) := by
            congr 1
            refine Finset.prod_congr rfl fun k _ => ?_
            unfold singularNorm
            rw [sum_range_singularValueAt_rpow_eq_sum_singularValues (A k) (N : ℝ)]

end

end HCPolySupport.HighContrast.Analysis
end

section
/-!
## Trace Holder for Schatten norms

This file removes the word-length constant in the lossy trace Holder bound by
applying it to tensor powers and using Archimedean growth of powers.
-/

namespace HCPolySupport.HighContrast.Analysis

open scoped BigOperators

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem le_of_all_pow_le_mul_pow {a b c : ℝ} (_ha : 0 ≤ a) (hb : 0 ≤ b)
    (_hc : 1 ≤ c) (h : ∀ q : ℕ, a^q ≤ c*b^q) : a ≤ b := by
  by_contra hab
  have hba : b < a := not_le.mp hab
  by_cases hb0 : b = 0
  · subst b
    have h1 := h 1
    have ha0 : a ≤ 0 := by simpa using h1
    exact (not_lt_of_ge ha0) hba
  · have hbpos : 0 < b := lt_of_le_of_ne' hb hb0
    have hratio : 1 < a / b := (one_lt_div hbpos).mpr hba
    obtain ⟨q, hq⟩ := pow_unbounded_of_one_lt c hratio
    have hbqpos : 0 < b^q := pow_pos hbpos q
    have hlt : c*b^q < a^q := by
      have hmul := mul_lt_mul_of_pos_right hq hbqpos
      have hdiv : (a / b)^q * b^q = a^q := by
        rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero q hbpos.ne')]
      simpa [hdiv] using hmul
    exact (not_lt_of_ge (h q)) hlt

theorem trace_prod_pow_le_card_mul_prod_singularNorm_pow {N : ℕ} (hN : 0 < N)
    (A : Fin N → Matrix n n ℝ) (q : ℕ) :
    |Matrix.trace ((List.ofFn A).prod)|^q ≤
      (N:ℝ) * (∏ k, singularNorm (N:ℝ) (A k))^q := by
  have h :=
    abs_trace_prod_le_card_mul_prod_singularNorm (n := Fin q → n) hN
      (fun k => tensorPower (A k) q)
  rw [← tensorPower_prod, trace_tensorPower, abs_pow] at h
  simpa only [singularNorm_tensorPower _ (Nat.cast_pos.mpr hN), Finset.prod_pow] using h

theorem abs_trace_prod_le_prod_singularNorm {N : ℕ} (hN : 0 < N)
    (A : Fin N → Matrix n n ℝ) :
    |Matrix.trace ((List.ofFn A).prod)| ≤ ∏ k, singularNorm (N:ℝ) (A k) := by
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast Nat.succ_le_of_lt hN
  exact le_of_all_pow_le_mul_pow (abs_nonneg _)
    (Finset.prod_nonneg fun k _ => singularNorm_nonneg (N:ℝ) (A k))
    hNreal
    (trace_prod_pow_le_card_mul_prod_singularNorm_pow hN A)

theorem abs_trace_prod_le_prod_absSchattenNorm {d N : ℕ} (hN : 2 ≤ N)
    (A : Fin N → BlockMat d)
    (hA : ∀ k, (toFullBlockMat (A k)).IsHermitian) :
    |Matrix.trace ((List.ofFn fun k => toFullBlockMat (A k)).prod)| ≤
      ∏ k : Fin N, absSchattenNorm (N:ℝ) (A k) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by decide : 0 < 2) hN
  have hNreal : (1 : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast le_trans (by decide : 1 ≤ 2) hN
  calc
    |Matrix.trace ((List.ofFn fun k => toFullBlockMat (A k)).prod)|
        ≤ ∏ k, singularNorm (N:ℝ) (toFullBlockMat (A k)) :=
          abs_trace_prod_le_prod_singularNorm hNpos (fun k => toFullBlockMat (A k))
    _ = ∏ k : Fin N, absSchattenNorm (N:ℝ) (A k) := by
          refine Finset.prod_congr rfl fun k _ => ?_
          exact singularNorm_eq_absSchattenNorm (hA k) hNreal

end

end HCPolySupport.HighContrast.Analysis
end
