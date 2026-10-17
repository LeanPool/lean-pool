/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.IterationCore

/-!
# IterationGoodRun

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Iteration lemma, Step 2 on a run of good scales

ABK26, §4.3, `l.iteration.lemma`, Step 2.  Given the reabsorption of
`IterationCore.lean`, the source runs the discrete Grönwall lemma on `a_l:=
|∇ℓ_{b−l} − ∇ℓ_b|` to obtain `e.grad.bound.good`, substitutes back into
`e.sum.excess.bound` to get the same bound for `E_i`, and arrives at
`e.E.and.grad.bound.good`.  This module proves that chain for abstract
nonnegative sequences:

* `slopeGronwall` --- `e.grad.bound.good`: the pointwise slope bound on the run,
  obtained from `reabsorbSum` + `slopeTelescope` + `discrete_gronwall`;
* `goodRunBound` --- `e.E.and.grad.bound.good` at the bottom of the run:
  `E_a + p_a ≤ goodConst · (E_b + p_b + ∑δ) · exp(goodRate · ∑ε)`,
  **with no dependence on the run length**.

## Source gaps this module has to fill (disclosed, from the graph NOTEs)

* does not write the reindexing `a_l := |∇ℓ_{b−l} − ∇ℓ_b|`, nor the
  identification of Grönwall's `H`, nor the final passage from a bound on
  `|∇ℓ_i − ∇ℓ_b|` to one on `|∇ℓ_i|`.  All three are performed explicitly here;
  `H` is `5 Cstab (iterM · E_b + p_b ∑ε + ∑δ)`.
* performs the split `|∇ℓ_k| ≤ |∇ℓ_b| + |∇ℓ_k − ∇ℓ_b|` silently; it is the step
  `hεp` below, and it is what makes the Grönwall recursion linear in the
  unknown `|∇ℓ_k − ∇ℓ_b|`.
* asserts "Substituting back into `e.sum.excess.bound` gives the same bound for
  `E_i`"; the substitution produces a sum `∑ ε_k |∇ℓ_k|` each of whose summands
  carries its own exponential, and the collapse to a single exponential is not
  shown.  Here the collapse is explicit: every summand is bounded by the
  *uniform* run bound before summation, which is why `slopeGronwall` is proved
  for all `k` in the run and not only at the bottom.
* the `δ`-sum index silently shifts between; the shape proved here uses the
  full run sum `∑_{[a,b]} δ` in both places, which dominates either printed
  range.

## Constants

The `θ^h < 3/5` gate enters only through `reabsorbSum`; `h` enters only through
`iterM`.  `Real.exp` is kept opaque: the only facts used are `x ≤ exp x`,
monotonicity, and `exp(x)exp(y) = exp(x+y)`.

## Scope

`hmono`/`hstab` are binders on the abstract sequences here and are *not*
hypotheses of the source lemma (see `IterationCore.lean`); nothing in this
module may be presented as `l.iteration.lemma` or as any part of it closed.

## References

* ABK26, `l.iteration.lemma` proof Step 2.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Finset

noncomputable section

/-! ### The slope bound on a run (`e.grad.bound.good`) -/

section SlopeGronwall

variable {E p ε δ : ℤ → ℝ} {Cstab M : ℝ} {h : ℕ}

/-- **`e.grad.bound.good`**, uniform on the run `[a,b]`.

The hypothesis `hUb` is the reabsorption `e.sum.excess.bound` at every base point
of the run; the conclusion is the Grönwall output at every point of the run. -/
theorem slopeGronwall (hC : 0 ≤ Cstab) (hM : 0 ≤ M) (hE : ∀ k, 0 ≤ E k)
    (hp : ∀ k, 0 ≤ p k) (hε : ∀ k, 0 ≤ ε k) (hδ : ∀ k, 0 ≤ δ k)
    (hstab : ∀ k, |p k - p (k - 1)| ≤ Cstab * (E k + E (k - 1)))
    (hh : 1 ≤ h) {a b : ℤ} (hab : a ≤ b)
    (hUb : ∀ i, a ≤ i → i ≤ b → ∑ k ∈ Icc i b, E k
      ≤ 5 / 2 * (M * E b + ∑ k ∈ Icc (i + (h : ℤ)) b, (ε k * p k + δ k))) :
    ∀ k, a ≤ k → k ≤ b →
      |p k - p b|
        ≤ 5 * Cstab * (M * E b + p b * (∑ j ∈ Icc a b, ε j) + ∑ j ∈ Icc a b, δ j)
          * Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j) := by
  have hNval : (((b - a).toNat : ℕ) : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  have hW0 : 0 ≤ ∑ j ∈ Icc a b, ε j := Finset.sum_nonneg fun k _ => hε k
  have hD0 : 0 ≤ ∑ j ∈ Icc a b, δ j := Finset.sum_nonneg fun k _ => hδ k
  have hC5 : (0 : ℝ) ≤ 5 * Cstab := by linarith only [hC]
  have hH0 : 0 ≤ 5 * Cstab * (M * E b + p b * (∑ j ∈ Icc a b, ε j)
      + ∑ j ∈ Icc a b, δ j) := by
    refine mul_nonneg hC5 ?_
    have h1 : 0 ≤ M * E b := mul_nonneg hM (hE b)
    have h2 : 0 ≤ p b * ∑ j ∈ Icc a b, ε j := mul_nonneg (hp b) hW0
    linarith only [h1, h2, hD0]
  have hEe0 : ∀ l : ℕ, 0 ≤ 5 * Cstab * ε (b - (l : ℤ)) := fun l =>
    mul_nonneg hC5 (hε _)
  -- The Grönwall recursion.
  have hrec : ∀ l ≤ (b - a).toNat,
      |p (b - (l : ℤ)) - p b|
        ≤ 5 * Cstab * (M * E b + p b * (∑ j ∈ Icc a b, ε j) + ∑ j ∈ Icc a b, δ j)
          + ∑ k ∈ range l, (5 * Cstab * ε (b - (k : ℤ))) * |p (b - (k : ℤ)) - p b| := by
    intro l hlN
    have hlb : (l : ℤ) ≤ b - a := by
      rw [← hNval]
      exact_mod_cast hlN
    have hai : a ≤ b - (l : ℤ) := by omega
    have hib : b - (l : ℤ) ≤ b := by
      have : (0 : ℤ) ≤ (l : ℤ) := Int.natCast_nonneg l
      omega
    have hs := slopeTelescope hC hE hstab b l
    have hr := hUb (b - (l : ℤ)) hai hib
    -- the reflected error sum
    have hconv : ∑ k ∈ range l, ε (b - (k : ℤ)) * |p (b - (k : ℤ)) - p b|
        = ∑ k ∈ Icc (b - (l : ℤ) + 1) b, ε k * |p k - p b| :=
      refl_sum (fun k => ε k * |p k - p b|) b l
    have hAstep : |p (b - (l : ℤ)) - p b|
        ≤ 2 * Cstab * (5 / 2 * (M * E b
            + ∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, (ε k * p k + δ k))) := by
      refine le_trans hs ?_
      exact mul_le_mul_of_nonneg_left hr (by linarith only [hC])
    -- split `ε p` against the run top
    have hεp : ∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, ε k * p k
        ≤ p b * (∑ j ∈ Icc a b, ε j)
          + ∑ k ∈ range l, ε (b - (k : ℤ)) * |p (b - (k : ℤ)) - p b| := by
      have hpk : ∀ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b,
          ε k * p k ≤ ε k * p b + ε k * |p k - p b| := by
        intro k _
        have hpp : p k ≤ p b + |p k - p b| := by
          linarith only [le_abs_self (p k - p b)]
        have hm := mul_le_mul_of_nonneg_left hpp (hε k)
        linarith only [hm]
      have hsub1 : ∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, ε k ≤ ∑ j ∈ Icc a b, ε j := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hε k
        intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        omega
      have hsub2 : ∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, ε k * |p k - p b|
          ≤ ∑ k ∈ Icc (b - (l : ℤ) + 1) b, ε k * |p k - p b| := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_
          fun k _ _ => mul_nonneg (hε k) (abs_nonneg _)
        intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        have : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
        omega
      calc ∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, ε k * p k
          ≤ ∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, (ε k * p b + ε k * |p k - p b|) :=
            Finset.sum_le_sum hpk
        _ = (∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, ε k) * p b
            + ∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, ε k * |p k - p b| := by
            rw [Finset.sum_add_distrib, Finset.sum_mul]
        _ ≤ (∑ j ∈ Icc a b, ε j) * p b
            + ∑ k ∈ Icc (b - (l : ℤ) + 1) b, ε k * |p k - p b| :=
            add_le_add (mul_le_mul_of_nonneg_right hsub1 (hp b)) hsub2
        _ = p b * (∑ j ∈ Icc a b, ε j)
            + ∑ k ∈ range l, ε (b - (k : ℤ)) * |p (b - (k : ℤ)) - p b| := by
            rw [hconv]; ring
    have hδe : ∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, δ k ≤ ∑ j ∈ Icc a b, δ j := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hδ k
      intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    have hsplit : ∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, (ε k * p k + δ k)
        = (∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, ε k * p k)
          + ∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, δ k := Finset.sum_add_distrib
    have hmono2 : 2 * Cstab * (5 / 2 * (M * E b
          + ∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, (ε k * p k + δ k)))
        ≤ 2 * Cstab * (5 / 2 * (M * E b
            + (p b * (∑ j ∈ Icc a b, ε j)
              + ∑ k ∈ range l, ε (b - (k : ℤ)) * |p (b - (k : ℤ)) - p b|
              + ∑ j ∈ Icc a b, δ j))) := by
      refine mul_le_mul_of_nonneg_left ?_ (by linarith only [hC])
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [hsplit]
      linarith only [hεp, hδe]
    have hfinal : 2 * Cstab * (5 / 2 * (M * E b
          + (p b * (∑ j ∈ Icc a b, ε j)
            + ∑ k ∈ range l, ε (b - (k : ℤ)) * |p (b - (k : ℤ)) - p b|
            + ∑ j ∈ Icc a b, δ j)))
        = 5 * Cstab * (M * E b + p b * (∑ j ∈ Icc a b, ε j) + ∑ j ∈ Icc a b, δ j)
          + ∑ k ∈ range l, (5 * Cstab * ε (b - (k : ℤ))) * |p (b - (k : ℤ)) - p b| := by
      have hpull : ∑ k ∈ range l,
            (5 * Cstab * ε (b - (k : ℤ))) * |p (b - (k : ℤ)) - p b|
          = 5 * Cstab * ∑ k ∈ range l,
            ε (b - (k : ℤ)) * |p (b - (k : ℤ)) - p b| := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [hpull]
      ring
    calc |p (b - (l : ℤ)) - p b|
        ≤ 2 * Cstab * (5 / 2 * (M * E b
            + ∑ k ∈ Icc (b - (l : ℤ) + (h : ℤ)) b, (ε k * p k + δ k))) := hAstep
      _ ≤ 2 * Cstab * (5 / 2 * (M * E b
            + (p b * (∑ j ∈ Icc a b, ε j)
              + ∑ k ∈ range l, ε (b - (k : ℤ)) * |p (b - (k : ℤ)) - p b|
              + ∑ j ∈ Icc a b, δ j))) := hmono2
      _ = 5 * Cstab * (M * E b + p b * (∑ j ∈ Icc a b, ε j) + ∑ j ∈ Icc a b, δ j)
          + ∑ k ∈ range l, (5 * Cstab * ε (b - (k : ℤ)))
            * |p (b - (k : ℤ)) - p b| := hfinal
  -- Grönwall, then bound the exponent.
  have hgron := discrete_gronwall (N := (b - a).toNat)
    (H := 5 * Cstab * (M * E b + p b * (∑ j ∈ Icc a b, ε j) + ∑ j ∈ Icc a b, δ j))
    (a := fun l : ℕ => |p (b - (l : ℤ)) - p b|)
    (ε := fun l : ℕ => 5 * Cstab * ε (b - (l : ℤ))) hH0 hEe0 hrec
  have hexpb : ∀ l ≤ (b - a).toNat,
      ∑ k ∈ range l, (5 * Cstab * ε (b - (k : ℤ)))
        ≤ 5 * Cstab * ∑ j ∈ Icc a b, ε j := by
    intro l hlN
    have hlb : (l : ℤ) ≤ b - a := by
      rw [← hNval]
      exact_mod_cast hlN
    have hEeE : ∑ k ∈ range l, (5 * Cstab * ε (b - (k : ℤ)))
        = 5 * Cstab * ∑ k ∈ range l, ε (b - (k : ℤ)) := by
      rw [Finset.mul_sum]
    rw [hEeE, refl_sum ε b l]
    refine mul_le_mul_of_nonneg_left ?_ hC5
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hε k
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  intro k hak hkb
  have hkN : (b - k).toNat ≤ (b - a).toNat := by omega
  have hbk : b - (((b - k).toNat : ℕ) : ℤ) = k := by
    rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ b - k)]
    ring
  have hfin : |p (b - (((b - k).toNat : ℕ) : ℤ)) - p b|
      ≤ 5 * Cstab * (M * E b + p b * (∑ j ∈ Icc a b, ε j) + ∑ j ∈ Icc a b, δ j)
        * Real.exp (∑ j ∈ range (b - k).toNat, (5 * Cstab * ε (b - (j : ℤ)))) :=
    hgron (b - k).toNat hkN
  have hmono3 : Real.exp (∑ j ∈ range (b - k).toNat, (5 * Cstab * ε (b - (j : ℤ))))
      ≤ Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j) :=
    Real.exp_le_exp.mpr (hexpb (b - k).toNat hkN)
  have hchain := le_trans hfin (mul_le_mul_of_nonneg_left hmono3 hH0)
  rwa [hbk] at hchain

end SlopeGronwall

/-! ### The fold into the good-run constant -/

/-- The arithmetic core of `e.E.and.grad.bound.good`, with `Real.exp` replaced by
opaque reals `e5` (`= exp(5 Cstab ∑ε)`) and `Ex` (`= exp(goodRate ∑ε)`) satisfying
the four folding inequalities.  Keeping it exp-free is what allows every step to
be closed by an explicit monotonicity lemma or `linarith only`. -/
private theorem foldCore {Cstab M W Dd Eb pb Ea pa e5 Ex H : ℝ} (hC : 0 ≤ Cstab)
    (hM : 0 ≤ M) (hW : 0 ≤ W) (hD : 0 ≤ Dd) (hEb : 0 ≤ Eb) (hpb : 0 ≤ pb)
    (he5 : 0 ≤ e5) (hEx1 : 1 ≤ Ex) (he5Ex : e5 ≤ Ex) (hWEx : W ≤ Ex)
    (hWe5 : W * e5 ≤ Ex) (hW2e5 : W * W * e5 ≤ Ex)
    (hHdef : H = 5 * Cstab * (M * Eb + pb * W + Dd))
    (hEa : Ea ≤ 5 / 2 * (M * Eb + W * pb + W * (H * e5) + Dd))
    (hpa : pa ≤ pb + H * e5) :
    Ea + pa
      ≤ (5 / 2 * M + 6 + 5 * Cstab * (7 / 2 * M + 7)) * (Eb + pb + Dd) * Ex := by
  have hS0 : 0 ≤ Eb + pb + Dd := by linarith only [hEb, hpb, hD]
  have hSle : Eb + pb + Dd ≤ (Eb + pb + Dd) * Ex := by
    have h := mul_le_mul_of_nonneg_left hEx1 hS0
    linarith only [h]
  have b1 : M * Eb ≤ M * ((Eb + pb + Dd) * Ex) := by
    have h1 : M * Eb ≤ M * (Eb + pb + Dd) :=
      mul_le_mul_of_nonneg_left (by linarith only [hpb, hD]) hM
    have h2 : M * (Eb + pb + Dd) ≤ M * ((Eb + pb + Dd) * Ex) :=
      mul_le_mul_of_nonneg_left hSle hM
    linarith only [h1, h2]
  have b2 : W * pb ≤ (Eb + pb + Dd) * Ex := by
    have h1 : W * pb ≤ W * (Eb + pb + Dd) :=
      mul_le_mul_of_nonneg_left (by linarith only [hEb, hD]) hW
    have h2 : W * (Eb + pb + Dd) ≤ Ex * (Eb + pb + Dd) :=
      mul_le_mul_of_nonneg_right hWEx hS0
    linarith only [h1, h2]
  have b3 : Dd ≤ (Eb + pb + Dd) * Ex := by linarith only [hEb, hpb, hSle]
  have b4 : pb ≤ (Eb + pb + Dd) * Ex := by linarith only [hEb, hD, hSle]
  have hkey : (5 / 2 * W + 1) * ((M + W + 1) * e5) ≤ (7 / 2 * M + 7) * Ex := by
    have e1 : M * (W * e5) ≤ M * Ex := mul_le_mul_of_nonneg_left hWe5 hM
    have e2 : M * e5 ≤ M * Ex := mul_le_mul_of_nonneg_left he5Ex hM
    have hexp : (5 / 2 * W + 1) * ((M + W + 1) * e5)
        = 5 / 2 * (M * (W * e5)) + 5 / 2 * (W * W * e5) + 5 / 2 * (W * e5)
          + M * e5 + W * e5 + e5 := by ring
    have hrhs : (7 / 2 * M + 7) * Ex = 7 / 2 * (M * Ex) + 7 * Ex := by ring
    rw [hexp, hrhs]
    linarith only [e1, e2, hW2e5, hWe5, he5Ex]
  have hHle : H ≤ 5 * Cstab * ((Eb + pb + Dd) * (M + W + 1)) := by
    have h1 : M * Eb ≤ M * (Eb + pb + Dd) :=
      mul_le_mul_of_nonneg_left (by linarith only [hpb, hD]) hM
    have h2 : pb * W ≤ (Eb + pb + Dd) * W :=
      mul_le_mul_of_nonneg_right (by linarith only [hEb, hD]) hW
    have hin : M * Eb + pb * W + Dd ≤ (Eb + pb + Dd) * (M + W + 1) := by
      have hexp : (Eb + pb + Dd) * (M + W + 1)
          = M * (Eb + pb + Dd) + (Eb + pb + Dd) * W + (Eb + pb + Dd) := by ring
      rw [hexp]
      linarith only [h1, h2, hEb, hpb]
    rw [hHdef]
    exact mul_le_mul_of_nonneg_left hin (by linarith only [hC])
  have b5 : (5 / 2 * W + 1) * (H * e5)
      ≤ 5 * Cstab * (7 / 2 * M + 7) * ((Eb + pb + Dd) * Ex) := by
    have s1 : (5 / 2 * W + 1) * (H * e5)
        ≤ (5 / 2 * W + 1) * ((5 * Cstab * ((Eb + pb + Dd) * (M + W + 1))) * e5) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hHle he5)
        (by linarith only [hW])
    have s2 : (5 / 2 * W + 1) * ((5 * Cstab * ((Eb + pb + Dd) * (M + W + 1))) * e5)
        = (5 * Cstab * (Eb + pb + Dd)) * ((5 / 2 * W + 1) * ((M + W + 1) * e5)) := by
      ring
    have s3 : (5 * Cstab * (Eb + pb + Dd)) * ((5 / 2 * W + 1) * ((M + W + 1) * e5))
        ≤ (5 * Cstab * (Eb + pb + Dd)) * ((7 / 2 * M + 7) * Ex) :=
      mul_le_mul_of_nonneg_left hkey (mul_nonneg (by linarith only [hC]) hS0)
    have s4 : (5 * Cstab * (Eb + pb + Dd)) * ((7 / 2 * M + 7) * Ex)
        = 5 * Cstab * (7 / 2 * M + 7) * ((Eb + pb + Dd) * Ex) := by ring
    calc (5 / 2 * W + 1) * (H * e5)
        ≤ (5 / 2 * W + 1) * ((5 * Cstab * ((Eb + pb + Dd) * (M + W + 1))) * e5) := s1
      _ = (5 * Cstab * (Eb + pb + Dd)) * ((5 / 2 * W + 1) * ((M + W + 1) * e5)) := s2
      _ ≤ (5 * Cstab * (Eb + pb + Dd)) * ((7 / 2 * M + 7) * Ex) := s3
      _ = 5 * Cstab * (7 / 2 * M + 7) * ((Eb + pb + Dd) * Ex) := s4
  have hid : (5 / 2 * W + 1) * (H * e5) = 5 / 2 * (W * (H * e5)) + H * e5 := by ring
  have hgoal : (5 / 2 * M + 6 + 5 * Cstab * (7 / 2 * M + 7)) * (Eb + pb + Dd) * Ex
      = 5 / 2 * (M * ((Eb + pb + Dd) * Ex)) + 6 * ((Eb + pb + Dd) * Ex)
        + 5 * Cstab * (7 / 2 * M + 7) * ((Eb + pb + Dd) * Ex) := by ring
  rw [hgoal]
  linarith only [hEa, hpa, hid, b1, b2, b3, b4, b5]

/-! ### The good-run bound (`e.E.and.grad.bound.good`) -/

section GoodRun

variable {E p ε δ : ℤ → ℝ} {θ κ Cstab : ℝ} {h : ℕ}

/-- **`e.E.and.grad.bound.good`** at the bottom of a run of good scales, in the
length-independent form the assembly consumes:

`E_a + p_a ≤ goodConst h κ Cstab · (E_b + p_b + ∑_{[a,b]} δ) · exp(goodRate Cstab ·
∑_{[a,b]} ε)`.

`1 ≤ h` is not assumed: it follows from `θ^h < 3/5`. -/
theorem goodRunBound (hθpos : 0 < θ) (hθh : θ ^ h < 3 / 5) (hE : ∀ k, 0 ≤ E k)
    (hp : ∀ k, 0 ≤ p k) (hε : ∀ k, 0 ≤ ε k) (hδ : ∀ k, 0 ≤ δ k) (hκ : 1 ≤ κ)
    (hC : 0 ≤ Cstab) (hmono : ∀ k, E k ≤ κ * E (k + 1))
    (hstab : ∀ k, |p k - p (k - 1)| ≤ Cstab * (E k + E (k - 1))) {a b : ℤ}
    (hab : a ≤ b)
    (hdecay : ∀ j, a ≤ j → j ≤ b → E (j - h) ≤ θ ^ h * E j + ε j * p j + δ j) :
    E a + p a
      ≤ goodConst h κ Cstab * ((E b + p b) + ∑ k ∈ Icc a b, δ k)
        * Real.exp (goodRate Cstab * ∑ k ∈ Icc a b, ε k) := by
  have hh : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · rw [h0, pow_zero] at hθh
      exact absurd hθh (by norm_num)
    · exact hpos
  have hM : 0 ≤ iterM h κ := iterM_nonneg h hκ
  have hW0 : 0 ≤ ∑ k ∈ Icc a b, ε k := Finset.sum_nonneg fun k _ => hε k
  have hD0 : 0 ≤ ∑ k ∈ Icc a b, δ k := Finset.sum_nonneg fun k _ => hδ k
  -- reabsorption at every base point of the run
  have hUb : ∀ i, a ≤ i → i ≤ b → ∑ k ∈ Icc i b, E k
      ≤ 5 / 2 * (iterM h κ * E b
        + ∑ k ∈ Icc (i + (h : ℤ)) b, (ε k * p k + δ k)) := by
    intro i hai hib
    refine reabsorbSum hθpos hθh hE hε hp hδ hκ hmono ?_
    intro j hj1 hj2
    exact hdecay j (le_trans hai hj1) hj2
  -- the slope bound on the run
  have hslope := slopeGronwall hC hM hE hp hε hδ hstab hh hab hUb
  -- Step 3: the excess at the bottom
  have hEa : E a ≤ 5 / 2 * (iterM h κ * E b
      + (∑ k ∈ Icc a b, ε k) * p b
      + (∑ k ∈ Icc a b, ε k)
        * ((5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
            + ∑ j ∈ Icc a b, δ j))
          * Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j))
      + ∑ k ∈ Icc a b, δ k) := by
    have hsingle : E a ≤ ∑ k ∈ Icc a b, E k := by
      refine Finset.single_le_sum (f := E) (fun k _ => hE k) ?_
      simp only [Finset.mem_Icc]
      exact ⟨le_rfl, hab⟩
    have hbound := hUb a le_rfl hab
    have hpkb : ∀ k ∈ Icc (a + (h : ℤ)) b, ε k * p k
        ≤ ε k * (p b + 5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
            + ∑ j ∈ Icc a b, δ j)
          * Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j)) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk
      have hhz : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
      have hpb' := hslope k (by omega) hk.2
      have hpp : p k ≤ p b + |p k - p b| := by
        linarith only [le_abs_self (p k - p b)]
      exact mul_le_mul_of_nonneg_left (by linarith only [hpp, hpb']) (hε k)
    have hεsub : ∑ k ∈ Icc (a + (h : ℤ)) b, ε k ≤ ∑ k ∈ Icc a b, ε k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hε k
      intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    have hδsub : ∑ k ∈ Icc (a + (h : ℤ)) b, δ k ≤ ∑ k ∈ Icc a b, δ k := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun k _ _ => hδ k
      intro x hx
      simp only [Finset.mem_Icc] at hx ⊢
      omega
    have hq0 : 0 ≤ p b + 5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
        + ∑ j ∈ Icc a b, δ j) * Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j) := by
      have h1 : 0 ≤ iterM h κ * E b := mul_nonneg hM (hE b)
      have h2 : 0 ≤ p b * ∑ j ∈ Icc a b, ε j := mul_nonneg (hp b) hW0
      have h3 : 0 ≤ 5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
          + ∑ j ∈ Icc a b, δ j) := by
        refine mul_nonneg (by linarith only [hC]) ?_
        linarith only [h1, h2, hD0]
      have h4 := mul_nonneg h3 (le_of_lt (Real.exp_pos
        (5 * Cstab * ∑ j ∈ Icc a b, ε j)))
      linarith only [hp b, h4]
    have hεp : ∑ k ∈ Icc (a + (h : ℤ)) b, ε k * p k
        ≤ (∑ k ∈ Icc a b, ε k)
          * (p b + 5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
              + ∑ j ∈ Icc a b, δ j)
            * Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j)) := by
      calc ∑ k ∈ Icc (a + (h : ℤ)) b, ε k * p k
          ≤ ∑ k ∈ Icc (a + (h : ℤ)) b, ε k
              * (p b + 5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
                  + ∑ j ∈ Icc a b, δ j)
                * Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j)) :=
            Finset.sum_le_sum hpkb
        _ = (∑ k ∈ Icc (a + (h : ℤ)) b, ε k)
              * (p b + 5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
                  + ∑ j ∈ Icc a b, δ j)
                * Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j)) := by
            rw [Finset.sum_mul]
        _ ≤ (∑ k ∈ Icc a b, ε k)
              * (p b + 5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
                  + ∑ j ∈ Icc a b, δ j)
                * Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j)) :=
            mul_le_mul_of_nonneg_right hεsub hq0
    have hsum : ∑ k ∈ Icc (a + (h : ℤ)) b, (ε k * p k + δ k)
        = (∑ k ∈ Icc (a + (h : ℤ)) b, ε k * p k)
          + ∑ k ∈ Icc (a + (h : ℤ)) b, δ k := Finset.sum_add_distrib
    have hstep : 5 / 2 * (iterM h κ * E b
          + ∑ k ∈ Icc (a + (h : ℤ)) b, (ε k * p k + δ k))
        ≤ 5 / 2 * (iterM h κ * E b
          + ((∑ k ∈ Icc a b, ε k)
              * (p b + 5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
                  + ∑ j ∈ Icc a b, δ j)
                * Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j))
            + ∑ k ∈ Icc a b, δ k)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      rw [hsum]
      linarith only [hεp, hδsub]
    have hexpand : 5 / 2 * (iterM h κ * E b
          + ((∑ k ∈ Icc a b, ε k)
              * (p b + 5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
                  + ∑ j ∈ Icc a b, δ j)
                * Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j))
            + ∑ k ∈ Icc a b, δ k))
        = 5 / 2 * (iterM h κ * E b
          + (∑ k ∈ Icc a b, ε k) * p b
          + (∑ k ∈ Icc a b, ε k)
            * ((5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
                + ∑ j ∈ Icc a b, δ j))
              * Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j))
          + ∑ k ∈ Icc a b, δ k) := by ring
    calc E a ≤ ∑ k ∈ Icc a b, E k := hsingle
      _ ≤ 5 / 2 * (iterM h κ * E b
          + ∑ k ∈ Icc (a + (h : ℤ)) b, (ε k * p k + δ k)) := hbound
      _ ≤ _ := hstep
      _ = _ := hexpand
  -- Step 4: the slope at the bottom
  have hpa : p a ≤ p b + 5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
      + ∑ j ∈ Icc a b, δ j) * Real.exp (5 * Cstab * ∑ j ∈ Icc a b, ε j) := by
    have h := hslope a le_rfl hab
    linarith only [h, le_abs_self (p a - p b)]
  -- the exponential folding facts
  have hWe : ∑ k ∈ Icc a b, ε k ≤ Real.exp (∑ k ∈ Icc a b, ε k) := by
    linarith only [Real.add_one_le_exp (∑ k ∈ Icc a b, ε k)]
  have hrate : 0 ≤ goodRate Cstab := goodRate_nonneg hC
  have hEx1 : 1 ≤ Real.exp (goodRate Cstab * ∑ k ∈ Icc a b, ε k) := by
    rw [Real.one_le_exp_iff]
    exact mul_nonneg hrate hW0
  have hle1 : 5 * Cstab * ∑ k ∈ Icc a b, ε k
      ≤ goodRate Cstab * ∑ k ∈ Icc a b, ε k := by
    rw [goodRate]
    have := mul_le_mul_of_nonneg_right
      (by linarith only [] : 5 * Cstab ≤ 5 * Cstab + 2) hW0
    linarith only [this]
  have he5Ex : Real.exp (5 * Cstab * ∑ k ∈ Icc a b, ε k)
      ≤ Real.exp (goodRate Cstab * ∑ k ∈ Icc a b, ε k) := Real.exp_le_exp.mpr hle1
  have hWEx : ∑ k ∈ Icc a b, ε k
      ≤ Real.exp (goodRate Cstab * ∑ k ∈ Icc a b, ε k) := by
    refine le_trans hWe (Real.exp_le_exp.mpr ?_)
    rw [goodRate]
    have := mul_le_mul_of_nonneg_right
      (by linarith only [hC] : (1 : ℝ) ≤ 5 * Cstab + 2) hW0
    linarith only [this]
  have hWe5 : (∑ k ∈ Icc a b, ε k) * Real.exp (5 * Cstab * ∑ k ∈ Icc a b, ε k)
      ≤ Real.exp (goodRate Cstab * ∑ k ∈ Icc a b, ε k) := by
    calc (∑ k ∈ Icc a b, ε k) * Real.exp (5 * Cstab * ∑ k ∈ Icc a b, ε k)
        ≤ Real.exp (∑ k ∈ Icc a b, ε k)
            * Real.exp (5 * Cstab * ∑ k ∈ Icc a b, ε k) :=
          mul_le_mul_of_nonneg_right hWe (le_of_lt (Real.exp_pos _))
      _ = Real.exp ((∑ k ∈ Icc a b, ε k) + 5 * Cstab * ∑ k ∈ Icc a b, ε k) := by
          rw [← Real.exp_add]
      _ ≤ Real.exp (goodRate Cstab * ∑ k ∈ Icc a b, ε k) := by
          refine Real.exp_le_exp.mpr ?_
          rw [goodRate]
          have := mul_le_mul_of_nonneg_right
            (by linarith only [] : 1 + 5 * Cstab ≤ 5 * Cstab + 2) hW0
          linarith only [this]
  have hW2e5 : (∑ k ∈ Icc a b, ε k) * (∑ k ∈ Icc a b, ε k)
        * Real.exp (5 * Cstab * ∑ k ∈ Icc a b, ε k)
      ≤ Real.exp (goodRate Cstab * ∑ k ∈ Icc a b, ε k) := by
    have hWW : (∑ k ∈ Icc a b, ε k) * (∑ k ∈ Icc a b, ε k)
        ≤ Real.exp (∑ k ∈ Icc a b, ε k) * Real.exp (∑ k ∈ Icc a b, ε k) :=
      mul_le_mul hWe hWe hW0 (le_of_lt (Real.exp_pos _))
    calc (∑ k ∈ Icc a b, ε k) * (∑ k ∈ Icc a b, ε k)
          * Real.exp (5 * Cstab * ∑ k ∈ Icc a b, ε k)
        ≤ (Real.exp (∑ k ∈ Icc a b, ε k) * Real.exp (∑ k ∈ Icc a b, ε k))
            * Real.exp (5 * Cstab * ∑ k ∈ Icc a b, ε k) :=
          mul_le_mul_of_nonneg_right hWW (le_of_lt (Real.exp_pos _))
      _ = Real.exp ((∑ k ∈ Icc a b, ε k) + (∑ k ∈ Icc a b, ε k)
            + 5 * Cstab * ∑ k ∈ Icc a b, ε k) := by
          rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp (goodRate Cstab * ∑ k ∈ Icc a b, ε k) := by
          refine Real.exp_le_exp.mpr ?_
          rw [goodRate]
          have := mul_le_mul_of_nonneg_right
            (by linarith only [] : 1 + 1 + 5 * Cstab ≤ 5 * Cstab + 2) hW0
          linarith only [this]
  have hfold := foldCore (Cstab := Cstab) (M := iterM h κ) (W := ∑ k ∈ Icc a b, ε k)
    (Dd := ∑ k ∈ Icc a b, δ k) (Eb := E b) (pb := p b) (Ea := E a) (pa := p a)
    (e5 := Real.exp (5 * Cstab * ∑ k ∈ Icc a b, ε k))
    (Ex := Real.exp (goodRate Cstab * ∑ k ∈ Icc a b, ε k))
    (H := 5 * Cstab * (iterM h κ * E b + p b * (∑ j ∈ Icc a b, ε j)
      + ∑ j ∈ Icc a b, δ j))
    hC hM hW0 hD0 (hE b) (hp b) (le_of_lt (Real.exp_pos _)) hEx1 he5Ex hWEx hWe5
    hW2e5 rfl hEa hpa
  rw [goodConst]
  calc E a + p a
      ≤ (5 / 2 * iterM h κ + 6 + 5 * Cstab * (7 / 2 * iterM h κ + 7))
        * (E b + p b + ∑ k ∈ Icc a b, δ k)
        * Real.exp (goodRate Cstab * ∑ k ∈ Icc a b, ε k) := hfold
    _ = (5 / 2 * iterM h κ + 6 + 5 * Cstab * (7 / 2 * iterM h κ + 7))
        * (E b + p b + ∑ k ∈ Icc a b, δ k)
        * Real.exp (goodRate Cstab * ∑ k ∈ Icc a b, ε k) := rfl

end GoodRun

end

end Algsuperdiff.Section4.Provider.ExcessDecay
