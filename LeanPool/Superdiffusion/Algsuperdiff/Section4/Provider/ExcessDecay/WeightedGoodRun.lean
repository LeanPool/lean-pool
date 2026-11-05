/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.IterationCore

/-!
# WeightedGoodRun

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `θ`-weighted good-run iterate and the weighted run assembly

ABK26, §4.3, inside the proof of `l.iteration.lemma`, Step 4 and Step 3, for
**abstract nonnegative sequences** `E δ w : ℤ → ℝ`.

`IterationExcessDecay.goodRunExcessIterate` iterates the `h`-gap decay recurrence and
**discards** every `θ`-weight on the error terms, which is what the source's own display
does.  The decay-carrying half of the lemma needs the opposite bookkeeping: the weights
must be **kept**, because the geometric series

```
∑_{r ≥ 0} (θ^h)^r ≤ 1/(1 − 3/5) = 5/2       (θ^h < 3/5)
```

then bounds the whole accumulated `w`-budget of a run by `(5/2)·(a single bound Mp for
w on the run)`, with **no dependence on the run length**.  That is the only reason a
single power of the error scale survives to the bottom of `[n,m]`; with the weights
discarded one gets a length-dependent `∑_j w_j` instead.

Three results, all abstract:

* `weightedGoodRunIterate` --- the weighted iterate.  The geometric series is
  *internalised*: the induction carries the closed budget `(5/2)·Mp` and the step
  `θ^h·(5/2)Mp + Mp ≤ (5/2)Mp` is exactly the geometric estimate at `θ^h ≤ 3/5`
  (`(3/5)(5/2) + 1 = 5/2`, an equality --- the gate is used at full strength here).
* `weightedRunBound` --- the same bound at the *exact* bottom `a` of a run `[a,b]`.
  The iterate only reaches `b − t h`; the remaining `s = (b−a) mod h` scales are crossed
  with quasi-monotonicity, and the `θ`-power is restored to the geometric `θ^{b−a}` at
  the cost of the division remainder `(κ θ^{-1})^h`.
* `weightedAssemble` --- the downward run assembly across `B`: one factor
  `Λ = 2(κθ^{-1})^{h+2}` per bad scale (plus one for the initial run), the payoff being
  the genuine `θ^{m−k}` on the top excess and a length-independent error budget.

## What the `θ`-powers cost, and why the anchor's prefactor has room for it

Each bad scale is crossed with `E_{k−1} ≤ κ E_k`, which loses one power of `θ`
against the `θ^{m−k}` bookkeeping, and each good run loses at most `θ^{-(h+1)}`
(the division remainder plus the two crossings).  The assembly therefore pays
`θ^{-(h+2)(|B ∩ [k,m]| + 1)}`, which is below the frozen statement's
`θ^{-C(h+1)(|B|+1)}` for any `C ≥ 2`: the `θ`-power prefactor of conclusion
(ii) is the *legitimate division remainder*, and it is `≥ 1` because `θ < 1`,
so it is slack, never a burden.

## References

* ABK26, `l.iteration.lemma` Step 3, Step 4; conclusion (ii)
  `e.excess.decay.lemma`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Finset

noncomputable section

/-! ### `θ`-power bookkeeping -/

section ZpowHelpers

variable {θ : ℝ}

/-- On `(0,1]` the inverse is at least one; this is the only sign fact the `θ`-payback
factors need. -/
theorem one_le_inv_of_le_one (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) : 1 ≤ θ⁻¹ :=
  (one_le_inv₀ hθ0).mpr hθ1

/-- `1 ≤ κ θ^{-1}`: the per-scale payback factor of the assembly. -/
theorem one_le_mul_inv {κ : ℝ} (hκ : 1 ≤ κ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) :
    1 ≤ κ * θ⁻¹ := by
  have hi : 1 ≤ θ⁻¹ := one_le_inv_of_le_one hθ0 hθ1
  have h := mul_le_mul_of_nonneg_left hi (by linarith only [hκ] : (0 : ℝ) ≤ κ)
  linarith only [h, hκ]

end ZpowHelpers

/-! ### The weighted iterate -/

section WeightedIterate

variable {E δ w : ℤ → ℝ} {θ Mp : ℝ} {h : ℕ}

/-- **The `θ`-weighted good-run iterate** (first display, with the weights kept).

On a run `[a,b]` carrying the `h`-gap decay recurrence, with the error scale `w` bounded
by `Mp` on the run,

```
E_{b − t h} ≤ (θ^h)^t E_b + (5/2) Mp + ∑_{(b − t h, b]} δ ,
```

for every `t` with `a ≤ b − t h`.  The constant `5/2` is the closed geometric budget
`∑_r (θ^h)^r ≤ 1/(1 − 3/5)`: the induction step
`θ^h (5/2) Mp + Mp ≤ (3/5)(5/2) Mp + Mp = (5/2) Mp` is that estimate, and it is an
equality at `θ^h = 3/5`, so the gate is used at full strength.  Compare
`goodRunExcessIterate`, which discards the weights and therefore carries the whole sum
`∑_r w_{b−rh}`. -/
theorem weightedGoodRunIterate (hθpos : 0 < θ) (hθh : θ ^ h < 3 / 5)
    (hδ : ∀ k, 0 ≤ δ k) (hMp : 0 ≤ Mp) {a b : ℤ}
    (hwM : ∀ j, a ≤ j → j ≤ b → w j ≤ Mp)
    (hdecay : ∀ j, a ≤ j → j ≤ b → E (j - h) ≤ θ ^ h * E j + w j + δ j) :
    ∀ t : ℕ, a ≤ b - (t : ℤ) * (h : ℤ) →
      E (b - (t : ℤ) * (h : ℤ))
        ≤ (θ ^ h) ^ t * E b + 5 / 2 * Mp
          + ∑ j ∈ Icc (b - (t : ℤ) * (h : ℤ) + 1) b, δ j := by
  have hh : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · rw [h0, pow_zero] at hθh
      exact absurd hθh (by norm_num)
    · exact hpos
  have hhz : (1 : ℤ) ≤ (h : ℤ) := by exact_mod_cast hh
  have hθh0 : (0 : ℝ) ≤ θ ^ h := le_of_lt (pow_pos hθpos h)
  intro t
  induction t with
  | zero =>
      intro _
      simp only [Nat.cast_zero, zero_mul, sub_zero, pow_zero, one_mul]
      have hemp : Icc (b + 1) b = (∅ : Finset ℤ) := Finset.Icc_eq_empty_of_lt (by omega)
      rw [hemp, Finset.sum_empty, add_zero]
      linarith only [hMp]
  | succ t ih =>
      intro hbt
      have hcast : b - ((t + 1 : ℕ) : ℤ) * (h : ℤ)
          = (b - (t : ℤ) * (h : ℤ)) - (h : ℤ) := by
        push_cast
        ring
      have hat : a ≤ b - (t : ℤ) * (h : ℤ) := by
        rw [hcast] at hbt
        omega
      have hbb : b - (t : ℤ) * (h : ℤ) ≤ b := by
        have hnn : (0 : ℤ) ≤ (t : ℤ) * (h : ℤ) :=
          mul_nonneg (Int.natCast_nonneg t) (Int.natCast_nonneg h)
        omega
      have hstep := hdecay (b - (t : ℤ) * (h : ℤ)) hat hbb
      have hwle := hwM (b - (t : ℤ) * (h : ℤ)) hat hbb
      have hih := ih hat
      have hD0 : 0 ≤ ∑ j ∈ Icc (b - (t : ℤ) * (h : ℤ) + 1) b, δ j :=
        Finset.sum_nonneg fun j _ => hδ j
      have hmul : θ ^ h * E (b - (t : ℤ) * (h : ℤ))
          ≤ θ ^ h * ((θ ^ h) ^ t * E b + 5 / 2 * Mp
            + ∑ j ∈ Icc (b - (t : ℤ) * (h : ℤ) + 1) b, δ j) :=
        mul_le_mul_of_nonneg_left hih hθh0
      have hpowid : θ ^ h * ((θ ^ h) ^ t * E b) = (θ ^ h) ^ (t + 1) * E b := by
        rw [pow_succ]
        ring
      have hbudget : θ ^ h * (5 / 2 * Mp) + Mp ≤ 5 / 2 * Mp := by
        have hm := mul_le_mul_of_nonneg_right (le_of_lt hθh) hMp
        linarith only [hm]
      have hdrop : θ ^ h * ∑ j ∈ Icc (b - (t : ℤ) * (h : ℤ) + 1) b, δ j
          ≤ ∑ j ∈ Icc (b - (t : ℤ) * (h : ℤ) + 1) b, δ j := by
        have hle1 : θ ^ h ≤ 1 := by linarith only [hθh]
        have hm := mul_le_mul_of_nonneg_right hle1 hD0
        linarith only [hm]
      have hins : Icc (b - (t : ℤ) * (h : ℤ)) b
          = insert (b - (t : ℤ) * (h : ℤ)) (Icc (b - (t : ℤ) * (h : ℤ) + 1) b) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Icc]
        omega
      have hnot : (b - (t : ℤ) * (h : ℤ)) ∉ Icc (b - (t : ℤ) * (h : ℤ) + 1) b := by
        simp only [Finset.mem_Icc]
        omega
      have hsum : ∑ j ∈ Icc (b - (t : ℤ) * (h : ℤ)) b, δ j
          = δ (b - (t : ℤ) * (h : ℤ))
            + ∑ j ∈ Icc (b - (t : ℤ) * (h : ℤ) + 1) b, δ j := by
        rw [hins, Finset.sum_insert hnot]
      have hgrow : ∑ j ∈ Icc (b - (t : ℤ) * (h : ℤ)) b, δ j
          ≤ ∑ j ∈ Icc (b - ((t + 1 : ℕ) : ℤ) * (h : ℤ) + 1) b, δ j := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hδ j
        intro x hx
        simp only [Finset.mem_Icc] at hx ⊢
        rw [hcast]
        omega
      rw [hcast] at hgrow
      rw [hcast]
      linarith only [hstep, hwle, hmul, hpowid, hbudget, hdrop, hsum, hgrow]

end WeightedIterate

/-! ### The weighted run bound at the exact bottom of a run -/

section WeightedRun

variable {E δ w : ℤ → ℝ} {θ κ Mp : ℝ} {h : ℕ}

/-- **The weighted good-run bound at the bottom of the run.**

The iterate of `weightedGoodRunIterate` proves on `b − t h`, which overshoots
the bottom `a` by the division remainder `s = (b − a) mod h < h`.  Crossing
those `s` scales with quasi-monotonicity and restoring the `θ`-power to the
geometric `θ^{b−a}` costs exactly `(κ θ^{-1})^h`:

```
E_a ≤ (κ θ^{-1})^h · (θ^{b−a} E_b + (5/2) Mp + ∑_{[a,b]} δ) .
```

Both losses are `θ`-powers or `κ`-powers of the *fixed* lag `h`, never of the run length:
that is what makes the assembly length-independent. -/
theorem weightedRunBound (hθpos : 0 < θ) (hθ1 : θ ≤ 1) (hθh : θ ^ h < 3 / 5)
    (hE : ∀ k, 0 ≤ E k) (hδ : ∀ k, 0 ≤ δ k) (hMp : 0 ≤ Mp) (hκ : 1 ≤ κ)
    (hmono : ∀ k, E k ≤ κ * E (k + 1)) {a b : ℤ} (hab : a ≤ b)
    (hwM : ∀ j, a ≤ j → j ≤ b → w j ≤ Mp)
    (hdecay : ∀ j, a ≤ j → j ≤ b → E (j - h) ≤ θ ^ h * E j + w j + δ j) :
    E a ≤ (κ * θ⁻¹) ^ h
      * (θ ^ (b - a) * E b + 5 / 2 * Mp + ∑ j ∈ Icc a b, δ j) := by
  have hh : 1 ≤ h := by
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · rw [h0, pow_zero] at hθh
      exact absurd hθh (by norm_num)
    · exact hpos
  have hκ0 : (0 : ℝ) ≤ κ := by linarith only [hκ]
  have hinv : 1 ≤ θ⁻¹ := one_le_inv_of_le_one hθpos hθ1
  have hinv0 : (0 : ℝ) ≤ θ⁻¹ := by linarith only [hinv]
  have hκθ : 1 ≤ κ * θ⁻¹ := one_le_mul_inv hκ hθpos hθ1
  -- the division of the run length by the lag
  have hNz : (((b - a).toNat : ℕ) : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
  have hts : h * ((b - a).toNat / h) + (b - a).toNat % h = (b - a).toNat :=
    Nat.div_add_mod _ h
  have hsh : (b - a).toNat % h < h := Nat.mod_lt _ hh
  have htsz : (h : ℤ) * (((b - a).toNat / h : ℕ) : ℤ) + (((b - a).toNat % h : ℕ) : ℤ)
      = b - a := by
    have h1 : ((h * ((b - a).toNat / h) + (b - a).toNat % h : ℕ) : ℤ) = b - a := by
      rw [hts]; exact hNz
    rw [Nat.cast_add, Nat.cast_mul] at h1
    exact h1
  have hidx : b - (((b - a).toNat / h : ℕ) : ℤ) * (h : ℤ)
      = a + (((b - a).toNat % h : ℕ) : ℤ) := by
    linarith only [htsz]
  have hsnn : (0 : ℤ) ≤ (((b - a).toNat % h : ℕ) : ℤ) := Int.natCast_nonneg _
  have hat : a ≤ b - (((b - a).toNat / h : ℕ) : ℤ) * (h : ℤ) := by
    rw [hidx]
    omega
  have hiter := weightedGoodRunIterate hθpos hθh hδ hMp hwM hdecay
    ((b - a).toNat / h) hat
  -- the `δ`-block sits inside the run
  have hsub : ∑ j ∈ Icc (b - (((b - a).toNat / h : ℕ) : ℤ) * (h : ℤ) + 1) b, δ j
      ≤ ∑ j ∈ Icc a b, δ j := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hδ j
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    rw [hidx] at hx
    omega
  -- the `θ`-power: the geometric factor plus the division remainder
  have hzp : θ ^ (b - a) = θ ^ ((b - a).toNat : ℕ) := by
    rw [← zpow_natCast θ ((b - a).toNat), hNz]
  have hsplit : (θ : ℝ) ^ ((b - a).toNat : ℕ)
      = θ ^ (h * ((b - a).toNat / h)) * θ ^ ((b - a).toNat % h) := by
    rw [← pow_add, hts]
  have hsne : (θ : ℝ) ^ ((b - a).toNat % h) ≠ 0 :=
    ne_of_gt (pow_pos hθpos _)
  have hpow : (θ ^ h) ^ ((b - a).toNat / h)
      = θ ^ (b - a) * (θ⁻¹) ^ ((b - a).toNat % h) := by
    rw [← pow_mul, hzp, hsplit, inv_pow]
    field_simp
  -- the pieces of the bracket
  have hEb0 : 0 ≤ θ ^ (b - a) * E b :=
    mul_nonneg (le_of_lt (zpow_pos hθpos _)) (hE b)
  have hD0 : 0 ≤ ∑ j ∈ Icc a b, δ j := Finset.sum_nonneg fun j _ => hδ j
  have hbr0 : 0 ≤ θ ^ (b - a) * E b + 5 / 2 * Mp + ∑ j ∈ Icc a b, δ j := by
    linarith only [hEb0, hMp, hD0]
  -- crossing the remainder with quasi-monotonicity
  have hcross := excessIterMono hκ0 hmono ((b - a).toNat % h) a
  have hcross' : E a ≤ κ ^ ((b - a).toNat % h)
      * E (b - (((b - a).toNat / h : ℕ) : ℤ) * (h : ℤ)) := by
    rw [hidx]
    exact hcross
  have hstep1 : E (b - (((b - a).toNat / h : ℕ) : ℤ) * (h : ℤ))
      ≤ (θ⁻¹) ^ ((b - a).toNat % h)
        * (θ ^ (b - a) * E b + 5 / 2 * Mp + ∑ j ∈ Icc a b, δ j) := by
    have hinvpow : 1 ≤ (θ⁻¹) ^ ((b - a).toNat % h) := one_le_pow₀ hinv
    have hmulE : θ ^ (b - a) * (θ⁻¹) ^ ((b - a).toNat % h) * E b
        = (θ⁻¹) ^ ((b - a).toNat % h) * (θ ^ (b - a) * E b) := by ring
    have hrest : 5 / 2 * Mp + ∑ j ∈ Icc a b, δ j
        ≤ (θ⁻¹) ^ ((b - a).toNat % h) * (5 / 2 * Mp + ∑ j ∈ Icc a b, δ j) := by
      have hm := mul_le_mul_of_nonneg_right hinvpow
        (by linarith only [hMp, hD0] : (0 : ℝ) ≤ 5 / 2 * Mp + ∑ j ∈ Icc a b, δ j)
      linarith only [hm]
    have hexp : (θ⁻¹) ^ ((b - a).toNat % h)
        * (θ ^ (b - a) * E b + 5 / 2 * Mp + ∑ j ∈ Icc a b, δ j)
        = (θ⁻¹) ^ ((b - a).toNat % h) * (θ ^ (b - a) * E b)
          + (θ⁻¹) ^ ((b - a).toNat % h) * (5 / 2 * Mp + ∑ j ∈ Icc a b, δ j) := by
      ring
    rw [hexp, ← hmulE, ← hpow]
    linarith only [hiter, hsub, hrest]
  have hκpow0 : (0 : ℝ) ≤ κ ^ ((b - a).toNat % h) := pow_nonneg hκ0 _
  have hstep2 : E a ≤ (κ * θ⁻¹) ^ ((b - a).toNat % h)
      * (θ ^ (b - a) * E b + 5 / 2 * Mp + ∑ j ∈ Icc a b, δ j) := by
    have hm := mul_le_mul_of_nonneg_left hstep1 hκpow0
    have hid : κ ^ ((b - a).toNat % h)
        * ((θ⁻¹) ^ ((b - a).toNat % h)
          * (θ ^ (b - a) * E b + 5 / 2 * Mp + ∑ j ∈ Icc a b, δ j))
        = (κ * θ⁻¹) ^ ((b - a).toNat % h)
          * (θ ^ (b - a) * E b + 5 / 2 * Mp + ∑ j ∈ Icc a b, δ j) := by
      rw [mul_pow]
      ring
    rw [hid] at hm
    exact le_trans hcross' hm
  have hlast : (κ * θ⁻¹) ^ ((b - a).toNat % h) ≤ (κ * θ⁻¹) ^ h :=
    pow_le_pow_right₀ hκθ (le_of_lt hsh)
  exact le_trans hstep2 (mul_le_mul_of_nonneg_right hlast hbr0)

end WeightedRun

end

end Algsuperdiff.Section4.Provider.ExcessDecay
