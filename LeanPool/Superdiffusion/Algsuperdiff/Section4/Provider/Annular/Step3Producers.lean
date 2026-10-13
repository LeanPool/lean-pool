/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.Step3Arith
public import Mathlib.Algebra.Order.Chebyshev

/-!
# Step3Producers

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The three Step-3 resummation producers

Local helpers for ABK26, Section 4.1, proof of Proposition
`p.mathcalE.annular.decomp`, Step 3.  The manuscript's Step 3 consists of three
displays, each resumming one of the last three terms of
`e.mathcalE.annular.decomp.pre.zero`:

The three are produced here at abstract nonnegative fields, in the shapes the
Step-3 regrouping slots `hgrad`, `hL2` and `hsig` consume.  All the resummation arithmetic (the annulus multiplicity, the
scale-weight collapses, the geometric constants) is discharged by `Step3Arith`.
What is carried as an explicit caller hypothesis is exactly the manuscript's
own structural input at each display: the triangle inequality over the layer
sum `k_b - k_a = sum_{l in (a,b]} j_l` followed by Cauchy--Schwarz on the
finite `k`-block and the per-`k` cube comparison (for the two shell displays),
and the `e.shom.m.vs.shom.n` display (for the `sigma-bar` sum).

## The two shell producers share one core

`step3_shell_resummation` is the shared statement: the `(j,n)`-content is the
multiplicity `(m-n+2)` times a growth factor `3^(theta (m-n))` times the finite
`k`-block sum of squared shell brackets; the output is `72 (s/2 - theta)^(-3)`
times the target geometric shell sum.  The gradient display is `theta = 0` (its
`3^(2(1-gamma)(n-k)) <= 9` is absorbed into the caller's constant); the `L^2`
display is `theta = 2 gamma`, whose `(s - 4 gamma)^(-3)` is folded to `s^(-3)`
by the proved `sub_four_gamma_inv_cube_le`.

The manuscript pulls the `k`-block out of the annular double sum by an
interchange of summation.  The route here does the same work without a Fubini
step: the finite block is compared against the target sum's *own* geometric
weight (`shellBlock_le_zpow_mul_target`), which costs the factor
`3^(s(m-n+2)/2)` and is exactly absorbed by the annular weight `3^(-s(m-n))`,
leaving the residual rate `s/2 - theta`.

## The `k`-block index convention

The manuscript's inner block is `k in [n-1, m]`.  Everything below writes it in
the depth parametrization `k = m - v`, `v in {0, ..., m-n+1}`, i.e. as
`Finset.range ((m-n).toNat + 2)` -- the same block, and the parametrization in
which the target sum `sum_v 3^(-s v/2) A(m-v)^2` is written.
-/

namespace Algsuperdiff.Section4.Provider.Annular

noncomputable section

/-! ## The finite block against the target geometric shell sum -/

/-- **The finite `k`-block is dominated by the target shell sum.**

Every `A(m-v)^2` with `v < N` is `3^(s v / 2)` times the target's own term, and
`3^(s v / 2) <= 3^(s N / 2)`.  This is the step that lets the `k`-block be
pulled out of the annular double sum with no interchange of summation. -/
theorem shellBlock_le_zpow_mul_target {s : ℝ} {m : ℤ} {A : ℤ → ℝ}
    (hs0 : 0 < s)
    (hsum : Summable (fun v : ℕ => (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2))
    (N : ℕ) :
    ∑ v ∈ Finset.range N, A (m - (v : ℤ)) ^ 2
      ≤ (3 : ℝ) ^ ((s / 2) * (N : ℝ))
        * ∑' v : ℕ, (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2 := by
  have hterm0 : ∀ v : ℕ, 0 ≤ (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2 :=
    fun v => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)
  have hpart : ∑ v ∈ Finset.range N,
      (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2
      ≤ ∑' v : ℕ, (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2 :=
    Summable.sum_le_tsum _ (fun v _ => hterm0 v) hsum
  have hstep : ∀ v ∈ Finset.range N, A (m - (v : ℤ)) ^ 2
      ≤ (3 : ℝ) ^ ((s / 2) * (N : ℝ))
        * ((3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2) := by
    intro v hv
    have hvN : (v : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (Finset.mem_range.mp hv).le
    have hmono : (3 : ℝ) ^ ((s / 2) * (v : ℝ)) ≤ (3 : ℝ) ^ ((s / 2) * (N : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num)
        (mul_le_mul_of_nonneg_left hvN (by linarith only [hs0]))
    have hcancel : (3 : ℝ) ^ ((s / 2) * (v : ℝ)) * (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      norm_num
    calc A (m - (v : ℤ)) ^ 2
        = (3 : ℝ) ^ ((s / 2) * (v : ℝ))
            * ((3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2) := by
          rw [← mul_assoc, hcancel, one_mul]
      _ ≤ (3 : ℝ) ^ ((s / 2) * (N : ℝ))
            * ((3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2) :=
          mul_le_mul_of_nonneg_right hmono (hterm0 v)
  calc ∑ v ∈ Finset.range N, A (m - (v : ℤ)) ^ 2
      ≤ ∑ v ∈ Finset.range N, (3 : ℝ) ^ ((s / 2) * (N : ℝ))
          * ((3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2) :=
        Finset.sum_le_sum hstep
    _ = (3 : ℝ) ^ ((s / 2) * (N : ℝ))
          * ∑ v ∈ Finset.range N, (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (3 : ℝ) ^ ((s / 2) * (N : ℝ))
          * ∑' v : ℕ, (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2 :=
        mul_le_mul_of_nonneg_left hpart (Real.rpow_nonneg (by norm_num) _)

/-! ## The shared shell resummation -/

/-- **The shared Step-3 shell resummation**.

If the annular `(j,n)`-content obeys

```
T j n <= Kcs (m - n + 2) 3^(theta (m-n)) sum_{v < (m-n)+2} A(m-v)^2 ,
```

then the annular double sum of `3^(-s(m-n)) T j n` is at most
`72 Kcs (s/2 - theta)^(-3)` times the target shell sum
`sum_v 3^(-s v/2) A(m-v)^2`. -/
theorem step3_shell_resummation {m : ℤ} {s theta Kcs : ℝ} {A : ℤ → ℝ}
    {T : ℤ → ℤ → ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (htheta0 : 0 ≤ theta) (hc0 : 0 < s / 2 - theta)
    (hKcs : 0 ≤ Kcs)
    (hT0 : ∀ j n, 0 ≤ T j n)
    (hsum : Summable (fun v : ℕ => (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2))
    (hcs : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      T j n ≤ Kcs * (((m - n : ℤ) : ℝ) + 2) * (3 : ℝ) ^ (theta * ((m - n : ℤ) : ℝ))
        * ∑ v ∈ Finset.range ((m - n).toNat + 2), A (m - (v : ℤ)) ^ 2) :
    annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * T j n)
      ≤ 72 * Kcs / (s / 2 - theta) ^ 3
        * ∑' v : ℕ, (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2 := by
  classical
  set G : ℝ := ∑' v : ℕ, (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2 with hG
  have hG0 : 0 ≤ G := by
    rw [hG]
    exact tsum_nonneg fun v =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)
  have hKG : 0 ≤ Kcs * G := mul_nonneg hKcs hG0
  have hc1 : s / 2 - theta ≤ 1 := by linarith only [hs1, htheta0]
  have hthree : (3 : ℝ) ^ s ≤ 3 := by
    calc (3 : ℝ) ^ s ≤ (3 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hs1
      _ = 3 := Real.rpow_one 3
  have hh0 : ∀ j n : ℤ, 0 ≤ (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * T j n :=
    fun j n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hT0 j n)
  have hle : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * T j n
        ≤ (3 * (Kcs * G) * ((m - n : ℤ) : ℝ) + 6 * (Kcs * G))
          * (3 : ℝ) ^ (-((s / 2 - theta) * ((m - n : ℤ) : ℝ))) := by
    intro j n hj hn
    have hq0 : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ m - n := by omega
      exact_mod_cast this
    have hqcast : (((m - n).toNat : ℕ) : ℝ) = ((m - n : ℤ) : ℝ) := by
      have hz : ((m - n).toNat : ℤ) = m - n := by omega
      exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) hz
    have hblock := shellBlock_le_zpow_mul_target (A := A) (m := m) hs0 hsum
      ((m - n).toNat + 2)
    have hNcast : (((m - n).toNat + 2 : ℕ) : ℝ) = ((m - n : ℤ) : ℝ) + 2 := by
      push_cast [hqcast]
      ring
    rw [hNcast, ← hG] at hblock
    have hpre : 0 ≤ Kcs * (((m - n : ℤ) : ℝ) + 2)
        * (3 : ℝ) ^ (theta * ((m - n : ℤ) : ℝ)) :=
      mul_nonneg (mul_nonneg hKcs (by linarith only [hq0]))
        (Real.rpow_nonneg (by norm_num) _)
    have hstep : T j n ≤ Kcs * (((m - n : ℤ) : ℝ) + 2)
        * (3 : ℝ) ^ (theta * ((m - n : ℤ) : ℝ))
        * ((3 : ℝ) ^ ((s / 2) * (((m - n : ℤ) : ℝ) + 2)) * G) :=
      (hcs j n hj hn).trans (mul_le_mul_of_nonneg_left hblock hpre)
    have hwt0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_left hstep hwt0
    refine hmul.trans ?_
    have hcollapse : (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
        * ((3 : ℝ) ^ (theta * ((m - n : ℤ) : ℝ))
          * (3 : ℝ) ^ ((s / 2) * (((m - n : ℤ) : ℝ) + 2)))
        = (3 : ℝ) ^ s * (3 : ℝ) ^ (-((s / 2 - theta) * ((m - n : ℤ) : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3),
        ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    have hrw : (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
        * (Kcs * (((m - n : ℤ) : ℝ) + 2) * (3 : ℝ) ^ (theta * ((m - n : ℤ) : ℝ))
          * ((3 : ℝ) ^ ((s / 2) * (((m - n : ℤ) : ℝ) + 2)) * G))
        = (Kcs * G * (((m - n : ℤ) : ℝ) + 2))
          * ((3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
            * ((3 : ℝ) ^ (theta * ((m - n : ℤ) : ℝ))
              * (3 : ℝ) ^ ((s / 2) * (((m - n : ℤ) : ℝ) + 2)))) := by ring
    rw [hrw, hcollapse]
    have hbase0 : 0 ≤ Kcs * G * (((m - n : ℤ) : ℝ) + 2) :=
      mul_nonneg hKG (by linarith only [hq0])
    have hgeom0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-((s / 2 - theta) * ((m - n : ℤ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    calc (Kcs * G * (((m - n : ℤ) : ℝ) + 2))
          * ((3 : ℝ) ^ s * (3 : ℝ) ^ (-((s / 2 - theta) * ((m - n : ℤ) : ℝ))))
        ≤ (Kcs * G * (((m - n : ℤ) : ℝ) + 2))
            * (3 * (3 : ℝ) ^ (-((s / 2 - theta) * ((m - n : ℤ) : ℝ)))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hthree hgeom0) hbase0
      _ = (3 * (Kcs * G) * ((m - n : ℤ) : ℝ) + 6 * (Kcs * G))
            * (3 : ℝ) ^ (-((s / 2 - theta) * ((m - n : ℤ) : ℝ))) := by ring
  have hcore := annDouble_le_of_linear_geom (m := m)
    (h := fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * T j n)
    (K1 := 3 * (Kcs * G)) (K0 := 6 * (Kcs * G)) (c := s / 2 - theta)
    hc0 hc1 (by linarith only [hKG]) (by linarith only [hKG]) hh0 hle
  refine hcore.trans ?_
  have hc3 : (0 : ℝ) < (s / 2 - theta) ^ 3 := pow_pos hc0 3
  have hc2 : (0 : ℝ) < (s / 2 - theta) ^ 2 := pow_pos hc0 2
  have hcc : (s / 2 - theta) ^ 3 ≤ (s / 2 - theta) ^ 2 := by
    have hid : (s / 2 - theta) ^ 3 = (s / 2 - theta) ^ 2 * (s / 2 - theta) := by ring
    rw [hid]
    calc (s / 2 - theta) ^ 2 * (s / 2 - theta)
        ≤ (s / 2 - theta) ^ 2 * 1 := mul_le_mul_of_nonneg_left hc1 hc2.le
      _ = (s / 2 - theta) ^ 2 := mul_one _
  have hinvle : 1 / (s / 2 - theta) ^ 2 ≤ 1 / (s / 2 - theta) ^ 3 :=
    one_div_le_one_div_of_le hc3 hcc
  calc 16 * (3 * (Kcs * G)) / (s / 2 - theta) ^ 3
        + 4 * (6 * (Kcs * G)) / (s / 2 - theta) ^ 2
      = 48 * (Kcs * G) * (1 / (s / 2 - theta) ^ 3)
          + 24 * (Kcs * G) * (1 / (s / 2 - theta) ^ 2) := by ring
    _ ≤ 48 * (Kcs * G) * (1 / (s / 2 - theta) ^ 3)
          + 24 * (Kcs * G) * (1 / (s / 2 - theta) ^ 3) := by
        have := mul_le_mul_of_nonneg_left hinvle
          (by linarith only [hKG] : (0 : ℝ) ≤ 24 * (Kcs * G))
        linarith only [this]
    _ = 72 * Kcs / (s / 2 - theta) ^ 3 * G := by ring

/-! ## Step 3: the gradient resummation -/

/-- **The gradient resummation**.

The `theta = 0` instance of the shared core: the caller's `Kcs` carries the
manuscript's `3^(2(1-gamma)(n-k)) <= 9` cube comparison. -/
theorem step3_grad_resummation {m : ℤ} {s Kcs : ℝ} {A : ℤ → ℝ} {T : ℤ → ℤ → ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hKcs : 0 ≤ Kcs)
    (hT0 : ∀ j n, 0 ≤ T j n)
    (hsum : Summable (fun v : ℕ => (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2))
    (hcs : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      T j n ≤ Kcs * (((m - n : ℤ) : ℝ) + 2)
        * ∑ v ∈ Finset.range ((m - n).toNat + 2), A (m - (v : ℤ)) ^ 2) :
    annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * T j n)
      ≤ 576 * Kcs * (s ^ 3)⁻¹
        * ∑' v : ℕ, (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2 := by
  have hcs' : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      T j n ≤ Kcs * (((m - n : ℤ) : ℝ) + 2) * (3 : ℝ) ^ ((0 : ℝ) * ((m - n : ℤ) : ℝ))
        * ∑ v ∈ Finset.range ((m - n).toNat + 2), A (m - (v : ℤ)) ^ 2 := by
    intro j n hj hn
    have hz : (3 : ℝ) ^ ((0 : ℝ) * ((m - n : ℤ) : ℝ)) = 1 := by
      rw [zero_mul, Real.rpow_zero]
    rw [hz, mul_one]
    exact hcs j n hj hn
  have hbase := step3_shell_resummation (m := m) (s := s) (theta := 0) (Kcs := Kcs)
    (A := A) (T := T) hs0 hs1 le_rfl (by linarith only [hs0]) hKcs hT0 hsum hcs'
  refine hbase.trans (le_of_eq ?_)
  have hGnn : (0 : ℝ) ≤ ∑' v : ℕ,
      (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2 :=
    tsum_nonneg fun v => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)
  have hs3 : (s : ℝ) ^ 3 ≠ 0 := by positivity
  have hcube : (s / 2 - (0 : ℝ)) ^ 3 = s ^ 3 / 8 := by ring
  rw [hcube]
  field_simp
  ring

/-! ## Step 3: the `L^2` resummation -/

/-- **The `L^2` resummation**.

The `theta = 2 gamma` instance: the residual rate is `(s - 4 gamma)/2`, which
is the origin of the manuscript's `(s - 4 gamma)^(-3)`; the standing hypothesis
`s >= 8 gamma` folds it into `s^(-3)` through the proved
`sub_four_gamma_inv_cube_le`. -/
theorem step3_kL2_resummation {m : ℤ} {s gamma Kcs : ℝ} {A : ℤ → ℝ} {T : ℤ → ℤ → ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hgamma0 : 0 ≤ gamma) (hsg : 8 * gamma ≤ s)
    (hKcs : 0 ≤ Kcs)
    (hT0 : ∀ j n, 0 ≤ T j n)
    (hsum : Summable (fun v : ℕ => (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2))
    (hcs : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      T j n ≤ Kcs * (((m - n : ℤ) : ℝ) + 2)
        * (3 : ℝ) ^ (2 * gamma * ((m - n : ℤ) : ℝ))
        * ∑ v ∈ Finset.range ((m - n).toNat + 2), A (m - (v : ℤ)) ^ 2) :
    annDouble m (fun j n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * T j n)
      ≤ 4608 * Kcs * (s ^ 3)⁻¹
        * ∑' v : ℕ, (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2 := by
  have hc0 : 0 < s / 2 - 2 * gamma := by linarith only [hs0, hsg]
  have hbase := step3_shell_resummation (m := m) (s := s) (theta := 2 * gamma)
    (Kcs := Kcs) (A := A) (T := T) hs0 hs1 (by linarith only [hgamma0]) hc0 hKcs
    hT0 hsum hcs
  refine hbase.trans ?_
  set G : ℝ := ∑' v : ℕ, (3 : ℝ) ^ (-(s / 2) * (v : ℝ)) * A (m - (v : ℤ)) ^ 2 with hG
  have hG0 : 0 ≤ G := by
    rw [hG]
    exact tsum_nonneg fun v =>
      mul_nonneg (Real.rpow_nonneg (by norm_num) _) (sq_nonneg _)
  have hcube : (s / 2 - 2 * gamma) ^ 3 = (s - 4 * gamma) ^ 3 / 8 := by ring
  have habs := sub_four_gamma_inv_cube_le (s := s) (gamma := gamma) hs0 hsg
  have hd0 : (0 : ℝ) < (s - 4 * gamma) ^ 3 := by
    have : 0 < s - 4 * gamma := by linarith only [hs0, hsg]
    positivity
  have hrw : 72 * Kcs / (s / 2 - 2 * gamma) ^ 3
      = 576 * Kcs * ((s - 4 * gamma) ^ 3)⁻¹ := by
    rw [hcube]
    field_simp
    ring
  rw [hrw]
  have hKcsG : 0 ≤ Kcs * G := mul_nonneg hKcs hG0
  have hstep : 576 * Kcs * ((s - 4 * gamma) ^ 3)⁻¹ * G
      ≤ 576 * Kcs * (8 * (s ^ 3)⁻¹) * G := by
    have hmul : Kcs * ((s - 4 * gamma) ^ 3)⁻¹ ≤ Kcs * (8 * (s ^ 3)⁻¹) :=
      mul_le_mul_of_nonneg_left habs hKcs
    calc 576 * Kcs * ((s - 4 * gamma) ^ 3)⁻¹ * G
        = 576 * (Kcs * ((s - 4 * gamma) ^ 3)⁻¹) * G := by ring
      _ ≤ 576 * (Kcs * (8 * (s ^ 3)⁻¹)) * G := by
          have h0 : (0 : ℝ) ≤ 576 * G := by linarith only [hG0]
          have := mul_le_mul_of_nonneg_left hmul h0
          linarith only [this]
      _ = 576 * Kcs * (8 * (s ^ 3)⁻¹) * G := by ring
  refine hstep.trans (le_of_eq ?_)
  ring

/-! ## Step 3: the `sigma-bar` ratio sum -/

/-- **The `sigma-bar` ratio sum, arithmetic core**.

From the `e.shom.m.vs.shom.n` display in the form
`|sigma_m sigma_{n-2}^{-1} - 1|^2 <= (K1 (m-n) + K0)^2 3^(2 gamma (m-n))`,
the annular double sum is at most `1024 K1^2 s^(-4) + 16 K0^2 s^(-2)`. -/
theorem step3_sigma_ratio_core {m : ℤ} {s gamma K1 K0 : ℝ} {sig : ℤ → ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hgamma0 : 0 ≤ gamma) (hsg : 8 * gamma ≤ s)
    (hsig0 : ∀ n, 0 ≤ sig n)
    (hshom : ∀ n : ℤ, n ≤ m - 1 →
      sig n ≤ (K1 * ((m - n : ℤ) : ℝ) + K0) ^ 2
        * (3 : ℝ) ^ (2 * gamma * ((m - n : ℤ) : ℝ))) :
    annDouble m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)
      ≤ 1024 * K1 ^ 2 / s ^ 4 + 16 * K0 ^ 2 / s ^ 2 := by
  have hc0 : 0 < s - 2 * gamma := by linarith only [hs0, hsg]
  have hc1 : s - 2 * gamma ≤ 1 := by linarith only [hs1, hgamma0]
  have hh0 : ∀ j n : ℤ, 0 ≤ (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n :=
    fun _ n => mul_nonneg (Real.rpow_nonneg (by norm_num) _) (hsig0 n)
  have hle : ∀ j n : ℤ, j ≤ m → n ≤ j - 1 →
      (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n
        ≤ (2 * K1 ^ 2 * ((m - n : ℤ) : ℝ) ^ 2 + 2 * K0 ^ 2)
          * (3 : ℝ) ^ (-((s - 2 * gamma) * ((m - n : ℤ) : ℝ))) := by
    intro j n hj hn
    have hnm : n ≤ m - 1 := by omega
    have hq0 : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by
      have : (0 : ℤ) ≤ m - n := by omega
      exact_mod_cast this
    have hwt0 : (0 : ℝ) ≤ (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    have hmul := mul_le_mul_of_nonneg_left (hshom n hnm) hwt0
    refine hmul.trans ?_
    have hcollapse : (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
        * (3 : ℝ) ^ (2 * gamma * ((m - n : ℤ) : ℝ))
        = (3 : ℝ) ^ (-((s - 2 * gamma) * ((m - n : ℤ) : ℝ))) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
      congr 1
      ring
    have hrw : (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
        * ((K1 * ((m - n : ℤ) : ℝ) + K0) ^ 2
          * (3 : ℝ) ^ (2 * gamma * ((m - n : ℤ) : ℝ)))
        = (K1 * ((m - n : ℤ) : ℝ) + K0) ^ 2
          * ((3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ)))
            * (3 : ℝ) ^ (2 * gamma * ((m - n : ℤ) : ℝ))) := by ring
    rw [hrw, hcollapse]
    have hsq : (K1 * ((m - n : ℤ) : ℝ) + K0) ^ 2
        ≤ 2 * K1 ^ 2 * ((m - n : ℤ) : ℝ) ^ 2 + 2 * K0 ^ 2 := by
      have hd : (0 : ℝ) ≤ (K1 * ((m - n : ℤ) : ℝ) - K0) ^ 2 := sq_nonneg _
      have hexp : (K1 * ((m - n : ℤ) : ℝ) + K0) ^ 2
          + (K1 * ((m - n : ℤ) : ℝ) - K0) ^ 2
          = 2 * K1 ^ 2 * ((m - n : ℤ) : ℝ) ^ 2 + 2 * K0 ^ 2 := by ring
      linarith only [hd, hexp]
    exact mul_le_mul_of_nonneg_right hsq (Real.rpow_nonneg (by norm_num) _)
  have hcore := annDouble_le_of_quadratic_geom (m := m)
    (h := fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)
    (K2 := 2 * K1 ^ 2) (K0 := 2 * K0 ^ 2) (c := s - 2 * gamma)
    hc0 hc1 (by positivity) (by positivity) hh0 hle
  refine hcore.trans ?_
  -- absorb `(s - 2 gamma)^(-k)` into `s^(-k)` using `s >= 8 gamma`
  have hlow : 3 * s / 4 ≤ s - 2 * gamma := by linarith only [hsg]
  have h34 : (0 : ℝ) < 3 * s / 4 := by linarith only [hs0]
  have hp4 : (3 * s / 4) ^ 4 ≤ (s - 2 * gamma) ^ 4 :=
    pow_le_pow_left₀ h34.le hlow 4
  have hp2 : (3 * s / 4) ^ 2 ≤ (s - 2 * gamma) ^ 2 :=
    pow_le_pow_left₀ h34.le hlow 2
  have hs4 : (0 : ℝ) < s ^ 4 := by positivity
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hq4 : (0 : ℝ) < (3 * s / 4) ^ 4 := by positivity
  have hq2 : (0 : ℝ) < (3 * s / 4) ^ 2 := by positivity
  have hd4 : (0 : ℝ) < (s - 2 * gamma) ^ 4 := by positivity
  have hd2 : (0 : ℝ) < (s - 2 * gamma) ^ 2 := by positivity
  have hne4 : (s : ℝ) ^ 4 ≠ 0 := ne_of_gt hs4
  have hne2 : (s : ℝ) ^ 2 ≠ 0 := ne_of_gt hs2
  have hT1 : 128 * (2 * K1 ^ 2) / (s - 2 * gamma) ^ 4 ≤ 1024 * K1 ^ 2 / s ^ 4 := by
    rw [div_le_iff₀ hd4]
    have hval4 : (3 * s / 4) ^ 4 = 81 / 256 * s ^ 4 := by ring
    have hlow4 : 81 / 256 * s ^ 4 ≤ (s - 2 * gamma) ^ 4 := by
      linarith only [hp4, hval4]
    have hpos : (0 : ℝ) ≤ 1024 * K1 ^ 2 / s ^ 4 := by positivity
    have hstep := mul_le_mul_of_nonneg_left hlow4 hpos
    have hval : 1024 * K1 ^ 2 / s ^ 4 * (81 / 256 * s ^ 4) = 324 * K1 ^ 2 := by
      field_simp
      ring
    rw [hval] at hstep
    linarith only [hstep, sq_nonneg K1]
  have hT2 : 4 * (2 * K0 ^ 2) / (s - 2 * gamma) ^ 2 ≤ 16 * K0 ^ 2 / s ^ 2 := by
    rw [div_le_iff₀ hd2]
    have hval2 : (3 * s / 4) ^ 2 = 9 / 16 * s ^ 2 := by ring
    have hlow2 : 9 / 16 * s ^ 2 ≤ (s - 2 * gamma) ^ 2 := by
      linarith only [hp2, hval2]
    have hpos : (0 : ℝ) ≤ 16 * K0 ^ 2 / s ^ 2 := by positivity
    have hstep := mul_le_mul_of_nonneg_left hlow2 hpos
    have hval : 16 * K0 ^ 2 / s ^ 2 * (9 / 16 * s ^ 2) = 9 * K0 ^ 2 := by
      field_simp
    rw [hval] at hstep
    linarith only [hstep, sq_nonneg K0]
  linarith only [hT1, hT2]

/-- **The `sigma-bar` ratio sum, in the `hsig` slot shape of the Step-3
regrouping**.

The caller supplies `e.shom.m.vs.shom.n` in the manuscript's own shape, at the
`sigma-bar` index pair `(m, n-2)` (whose two-scale shift is the `2 gamma`
summand) and at the parameter choice `E ≍ cstar^(-1)`:

```
|sigma_m sigma_{n-2}^{-1} - 1|^2
  <= ( Cshom gamma (m-n) + Cshom (2 gamma + cstar^(-2) gamma |log gamma|^2) )^2
     3^(2 gamma (m-n)) .
```

The output is the `hsig` slot at the free constant `Csig = 7000 Cshom^2
s^(-1)`.

The two side conditions are honest and discharged in-repo at the caller: `|log
gamma| >= 1` holds for `gamma <= 1/8` (indeed for `gamma <= e^(-1)`), and
`cstar^4 <= 6` follows from the proved `cstar <= 3/2`. -/
theorem step3_sigma_ratio_slot {m : ℤ} {s gamma cstar Cshom : ℝ} {sig : ℤ → ℝ}
    (hs0 : 0 < s) (hs1 : s ≤ 1) (hgamma0 : 0 ≤ gamma) (hsg : 8 * gamma ≤ s)
    (hcstar0 : 0 < cstar) (hcstar4 : cstar ^ 4 ≤ 6)
    (hlog : 1 ≤ |Real.log gamma|)
    (hsig0 : ∀ n, 0 ≤ sig n)
    (hshom : ∀ n : ℤ, n ≤ m - 1 →
      sig n ≤ (Cshom * gamma * ((m - n : ℤ) : ℝ)
          + Cshom * (2 * gamma
            + (cstar ^ 2)⁻¹ * (gamma * |Real.log gamma| ^ 2))) ^ 2
        * (3 : ℝ) ^ (2 * gamma * ((m - n : ℤ) : ℝ))) :
    annDouble m (fun _ n => (3 : ℝ) ^ (-(s * ((m - n : ℤ) : ℝ))) * sig n)
      ≤ 7000 * Cshom ^ 2 * s⁻¹ * (s ^ 3)⁻¹ * (cstar ^ 4)⁻¹
          * (gamma ^ 2 * |Real.log gamma| ^ 4) := by
  set L : ℝ := |Real.log gamma| with hLdef
  have hL0 : (0 : ℝ) ≤ L := by rw [hLdef]; exact abs_nonneg _
  have hcs4 : (0 : ℝ) < cstar ^ 4 := by positivity
  have hcs2 : (0 : ℝ) < cstar ^ 2 := by positivity
  set q : ℝ := (cstar ^ 2)⁻¹ * (gamma * L ^ 2) with hqdef
  have hq0 : (0 : ℝ) ≤ q := by
    rw [hqdef]
    exact mul_nonneg (inv_nonneg.2 hcs2.le) (mul_nonneg hgamma0 (by positivity))
  have hcore := step3_sigma_ratio_core (m := m) (s := s) (gamma := gamma)
    (K1 := Cshom * gamma) (K0 := Cshom * (2 * gamma + q)) (sig := sig)
    hs0 hs1 hgamma0 hsg hsig0 hshom
  refine hcore.trans ?_
  -- the two atoms
  set X : ℝ := Cshom ^ 2 * gamma ^ 2 with hXdef
  have hX0 : (0 : ℝ) ≤ X := by rw [hXdef]; positivity
  set P : ℝ := (cstar ^ 4)⁻¹ * L ^ 4 with hPdef
  have hL4 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hlog
  have hP6 : (1 : ℝ) / 6 ≤ P := by
    have hinv : (6 : ℝ)⁻¹ ≤ (cstar ^ 4)⁻¹ := inv_anti₀ hcs4 hcstar4
    have hstep : (cstar ^ 4)⁻¹ ≤ (cstar ^ 4)⁻¹ * L ^ 4 := by
      have hm := mul_le_mul_of_nonneg_left hL4 (inv_nonneg.2 hcs4.le)
      rwa [mul_one] at hm
    rw [hPdef]
    linarith only [hinv, hstep]
  have hP0 : (0 : ℝ) ≤ P := by linarith only [hP6]
  -- the numerator bounds
  have hnum1 : 1024 * (Cshom * gamma) ^ 2 = 1024 * X := by
    rw [hXdef]; ring
  have hnum2 : 16 * (Cshom * (2 * gamma + q)) ^ 2 ≤ 128 * X + 32 * (X * P) := by
    have hexp : (2 * gamma + q) ^ 2 + (2 * gamma - q) ^ 2 = 8 * gamma ^ 2 + 2 * q ^ 2 := by
      ring
    have hsq : (2 * gamma + q) ^ 2 ≤ 8 * gamma ^ 2 + 2 * q ^ 2 := by
      linarith only [sq_nonneg (2 * gamma - q), hexp]
    have hXP : Cshom ^ 2 * q ^ 2 = X * P := by
      rw [hXdef, hPdef, hqdef]
      field_simp
    have hmul : Cshom ^ 2 * (2 * gamma + q) ^ 2
        ≤ Cshom ^ 2 * (8 * gamma ^ 2 + 2 * q ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    have hrw : Cshom ^ 2 * (8 * gamma ^ 2 + 2 * q ^ 2)
        = 8 * X + 2 * (Cshom ^ 2 * q ^ 2) := by rw [hXdef]; ring
    rw [hrw, hXP] at hmul
    have hlhs : 16 * (Cshom * (2 * gamma + q)) ^ 2
        = 16 * (Cshom ^ 2 * (2 * gamma + q) ^ 2) := by ring
    rw [hlhs]
    linarith only [hmul]
  -- the two weights
  have hs4 : (0 : ℝ) < s ^ 4 := by positivity
  have hs2 : (0 : ℝ) < s ^ 2 := by positivity
  have hpow : s ^ 4 ≤ s ^ 2 := by
    have hid : s ^ 4 = s ^ 2 * s ^ 2 := by ring
    rw [hid]
    calc s ^ 2 * s ^ 2 ≤ s ^ 2 * 1 :=
          mul_le_mul_of_nonneg_left (by nlinarith only [hs0, hs1]) hs2.le
      _ = s ^ 2 := mul_one _
  have hinvpow : (1 : ℝ) / s ^ 2 ≤ 1 / s ^ 4 := one_div_le_one_div_of_le hs4 hpow
  -- assemble
  have hA : 1024 * (Cshom * gamma) ^ 2 / s ^ 4 = 1024 * X * (1 / s ^ 4) := by
    rw [hnum1]; ring
  have hB : 16 * (Cshom * (2 * gamma + q)) ^ 2 / s ^ 2
      ≤ (128 * X + 32 * (X * P)) * (1 / s ^ 4) := by
    have hstep1 : 16 * (Cshom * (2 * gamma + q)) ^ 2 / s ^ 2
        = 16 * (Cshom * (2 * gamma + q)) ^ 2 * (1 / s ^ 2) := by ring
    have hnn : (0 : ℝ) ≤ 1 / s ^ 2 := by positivity
    have hstep2 : 16 * (Cshom * (2 * gamma + q)) ^ 2 * (1 / s ^ 2)
        ≤ (128 * X + 32 * (X * P)) * (1 / s ^ 2) :=
      mul_le_mul_of_nonneg_right hnum2 hnn
    have hstep3 : (128 * X + 32 * (X * P)) * (1 / s ^ 2)
        ≤ (128 * X + 32 * (X * P)) * (1 / s ^ 4) :=
      mul_le_mul_of_nonneg_left hinvpow
        (by positivity)
    rw [hstep1]
    linarith only [hstep2, hstep3]
  have hXP0 : (0 : ℝ) ≤ X * P := mul_nonneg hX0 hP0
  have habsorb : 1024 * X + (128 * X + 32 * (X * P)) ≤ 7000 * (X * P) := by
    have h6 : X * (1 / 6) ≤ X * P := mul_le_mul_of_nonneg_left hP6 hX0
    have hid : X * (1 / 6) = X / 6 := by ring
    rw [hid] at h6
    linarith only [h6, hXP0]
  have hfin : (1024 * X + (128 * X + 32 * (X * P))) * (1 / s ^ 4)
      ≤ 7000 * (X * P) * (1 / s ^ 4) :=
    mul_le_mul_of_nonneg_right habsorb (by positivity)
  have hgoal : 7000 * (X * P) * (1 / s ^ 4)
      = 7000 * Cshom ^ 2 * s⁻¹ * (s ^ 3)⁻¹ * (cstar ^ 4)⁻¹ * (gamma ^ 2 * L ^ 4) := by
    rw [hXdef, hPdef]
    field_simp
  rw [hA]
  calc 1024 * X * (1 / s ^ 4) + 16 * (Cshom * (2 * gamma + q)) ^ 2 / s ^ 2
      ≤ 1024 * X * (1 / s ^ 4) + (128 * X + 32 * (X * P)) * (1 / s ^ 4) := by
        linarith only [hB]
    _ = (1024 * X + (128 * X + 32 * (X * P))) * (1 / s ^ 4) := by ring
    _ ≤ 7000 * (X * P) * (1 / s ^ 4) := hfin
    _ = 7000 * Cshom ^ 2 * s⁻¹ * (s ^ 3)⁻¹ * (cstar ^ 4)⁻¹ * (gamma ^ 2 * L ^ 4) := hgoal

end

end Algsuperdiff.Section4.Provider.Annular
