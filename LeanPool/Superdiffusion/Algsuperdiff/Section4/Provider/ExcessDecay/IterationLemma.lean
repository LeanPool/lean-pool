/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.IterationGoodRun

/-!
# IterationLemma

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Iteration lemma, Step 3: crossing bad scales

ABK26, §4.3, `l.iteration.lemma`, Step 3.  The source concatenates the
good-run bound `e.E.and.grad.bound.good` across the maximal good intervals
of `([n,m] ∩ ℤ) ∖ B`, paying one factor per bad scale, and reaches
`e.combined.bound`; two endpoint comparisons then convert it into conclusion
(i), `e.iteration.slope.lemma`.

Both steps are proved here for abstract nonnegative sequences:

* `assembleRuns` --- the run concatenation, over an abstract nonnegative `q`;
* `combinedBound` --- `e.combined.bound` at `q = E + p`;
* `iterationSlopeBound` --- conclusion (i) in the oscillation form, from
  `combinedBound` plus the two endpoint comparisons supplied as an interface.

## The prefactor: the product form, and how it differs from the printed one

The source prints the prefactor of both `e.combined.bound` and
`e.iteration.slope.lemma` **additively**, as `exp(C h + C|B| + C∑ε)`.  What the
downward induction actually yields is the **product** form

```
(goodConst h κ Cstab · badConst κ Cstab) ^ (3|B ∩ [n,m]| + 3) · exp(goodRate · ∑ε),
```

and since `goodConst` grows like `h κ^h`, the exponent of the product form is
of order `h(|B| + 1)`, i.e. `exp(C h |B|)`, not `exp(C(h + |B|))`.  The two
shapes agree at the fixed `h` the lemma is used with (§4.4 pins `h := k ≥ 3`).

**This module therefore proves the product form and does not claim the printed
additive form.**  Deriving the additive form would need an argument that pays
the `h`-cost once rather than once per good run --- conceivable, because the
factor `iterM h κ` multiplies `E_b` only while `p_b` passes with coefficient
`1`, so an induction keeping the `E`- and `p`-components separate can hope to
hoist it --- but it is not attempted here.

## Reading choices, as implemented

* **The window cap.**  The window nesting/sandwich is demanded only for `j ≤
  m`.  The abstract hypotheses `hmono`/`hstab` are stated for all `k`, which is
  *stronger* than the argument needs and is the honest shape for abstract
  sequences; a consumer must honour the `j ≤ m` cap, and no
  statement in this module reads `E`, `p` at any index `> m`: the conclusions
  and all sums range over `[n,m]`, the decay hypothesis over `([n,m] ∩ ℤ) ∖ B`,
  and the lowest index reached is `n − h`.
* **The sandwich is not instantiated here.**  `κ` and `Cstab` are
  parameters, and `AffineExcess.lean`'s normalizer comparison is stated at the
  printed aspect ratio `3^{-2}`, never at the sharper `1/2`.
* **`h` and `θ` are data, not constants.**  They are explicit binders and appear in
  the conclusion through `iterM h κ` and through the gate `θ^h < 3/5`; no
  declaration hides them in an existential, and no constant here is existential.
* **`C` is quantified outermost, depending on `d`
  alone.**  Implemented literally: `goodConst`, `goodRate`, `badConst` are explicit
  `def`s of `h`, `κ`, `Cstab` only, so a consumer supplying `κ = κ(d)`,
  `Cstab = Cstab(d)` from the window geometry gets a constant uniform in
  `n, m, B, ε, δ, u`.
* **The family is used on `[n−h,m]` while the
  sums range over `[n,m]`.**  Implemented literally above.
* **`θ^{−C(h+|B|)}` versus `exp(C(h+|B|))`.**
  The two shapes are reconciled only through an undisplayed relation between
  `C` and `log(1/θ)`.
* **The `h`-gap is never weakened.**  The `h`-gap and the gate `θ^h < 3/5` are
  never replaced by an adjacent-scale contraction anywhere below.

## Scope

`hmono`, `hstab`, `hlo`, `hhi` are *hypotheses on abstract sequences* here, and
are the source's own Step-1/Step-3 **conclusions**; a consumer presenting these
theorems as `l.iteration.lemma` itself would be turning three proof obligations
into binders.

## References

* ABK26, `l.iteration.lemma`: statement, Step 3.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Finset

noncomputable section

/-! ### Arithmetic helpers -/

/-- Two disjoint blocks of an interval sum to at most the interval. -/
private theorem sum_two_blocks_le {f : ℤ → ℝ} (hf : ∀ k, 0 ≤ f k) {k b m : ℤ}
    (hkb : k ≤ b) (hbm : b ≤ m) :
    (∑ j ∈ Icc k (b - 1), f j) + ∑ j ∈ Icc (b + 1) m, f j ≤ ∑ j ∈ Icc k m, f j := by
  have hdisj : Disjoint (Icc k (b - 1)) (Icc (b + 1) m) := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [Finset.mem_Icc] at hx hx'
    omega
  have hunion : Icc k (b - 1) ∪ Icc (b + 1) m ⊆ Icc k m := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_Icc] at hx ⊢
    omega
  calc (∑ j ∈ Icc k (b - 1), f j) + ∑ j ∈ Icc (b + 1) m, f j
      = ∑ j ∈ Icc k (b - 1) ∪ Icc (b + 1) m, f j := (Finset.sum_union hdisj).symm
    _ ≤ ∑ j ∈ Icc k m, f j :=
        Finset.sum_le_sum_of_subset_of_nonneg hunion fun j _ _ => hf j

/-- The top-scale case of the assembly: the bound is trivial there. -/
private theorem top_case {qm Pk X S : ℝ} (hq0 : 0 ≤ qm) (hPk1 : 1 ≤ Pk)
    (hX1 : 1 ≤ X) (hS0 : 0 ≤ S) : qm ≤ Pk * X * (qm + S) := by
  have hPX : 1 ≤ Pk * X := by
    have hm := mul_le_mul_of_nonneg_left hX1 (by linarith only [hPk1] : (0 : ℝ) ≤ Pk)
    linarith only [hm, hPk1]
  have hs0 : (0 : ℝ) ≤ qm + S := by linarith only [hq0, hS0]
  have hm := mul_le_mul_of_nonneg_right hPX hs0
  linarith only [hm, hS0]

/-- The bookkeeping step of the assembly: a bound of shape `q ≤ G(qn + Sl)Xl`
composed with `qn ≤ Pn(Tm + Sn)` collapses to `q ≤ Pk(Tm + S)` as soon as the
prefactors multiply and the two error blocks fit inside `S`. -/
private theorem assembleStep {q qn G Pn Xl Sl Sn S Tm Pk : ℝ} (hG1 : 1 ≤ G)
    (hPn1 : 1 ≤ Pn) (hXl1 : 1 ≤ Xl) (hSl0 : 0 ≤ Sl) (hSn0 : 0 ≤ Sn)
    (hTm0 : 0 ≤ Tm) (hq : q ≤ G * (qn + Sl) * Xl) (hqn : qn ≤ Pn * (Tm + Sn))
    (hS : Sl + Sn ≤ S) (hpref : G * Pn * Xl ≤ Pk) :
    q ≤ Pk * (Tm + S) := by
  have hG0 : (0 : ℝ) ≤ G := by linarith only [hG1]
  have hPn0 : (0 : ℝ) ≤ Pn := by linarith only [hPn1]
  have hXl0 : (0 : ℝ) ≤ Xl := by linarith only [hXl1]
  have hSlPn : Sl ≤ Pn * Sl := by
    have hm := mul_le_mul_of_nonneg_right hPn1 hSl0
    linarith only [hm]
  have h1 : G * (qn + Sl) * Xl ≤ G * (Pn * (Tm + Sn) + Pn * Sl) * Xl := by
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hG0) hXl0
    linarith only [hqn, hSlPn]
  have h3 : (G * Pn * Xl) * (Tm + (Sl + Sn)) ≤ (G * Pn * Xl) * (Tm + S) := by
    refine mul_le_mul_of_nonneg_left (by linarith only [hS]) ?_
    exact mul_nonneg (mul_nonneg hG0 hPn0) hXl0
  have hTmS0 : (0 : ℝ) ≤ Tm + S := by linarith only [hTm0, hS, hSl0, hSn0]
  have h4 : (G * Pn * Xl) * (Tm + S) ≤ Pk * (Tm + S) :=
    mul_le_mul_of_nonneg_right hpref hTmS0
  calc q ≤ G * (qn + Sl) * Xl := hq
    _ ≤ G * (Pn * (Tm + Sn) + Pn * Sl) * Xl := h1
    _ = (G * Pn * Xl) * (Tm + (Sl + Sn)) := by ring
    _ ≤ (G * Pn * Xl) * (Tm + S) := h3
    _ ≤ Pk * (Tm + S) := h4

/-! ### The run concatenation -/

/-- **The abstract run concatenation** behind `e.combined.bound`.

Given a nonnegative sequence `q` that  grows by at most `Bc` per single scale
and (b) satisfies the length-independent good-run bound with constant `G` on
every all-good subinterval of `[n,m]`, the value at the bottom is controlled by
the value at the top with a prefactor depending on the *number* of bad scales
only.

The exponent `3|B ∩ [k,m]| + 3` is what the induction pays: at most one good-run
factor `G` and two single-scale factors `Bc` per bad scale crossed, plus the initial
run. -/
private theorem assembleRuns {q ε δ : ℤ → ℝ} {G Bc rate : ℝ} {n m : ℤ}
    (B : Finset ℤ) (hq : ∀ k, 0 ≤ q k) (hε : ∀ k, 0 ≤ ε k) (hδ : ∀ k, 0 ≤ δ k)
    (hG : 1 ≤ G) (hBc : 1 ≤ Bc) (hrate : 0 ≤ rate)
    (hbad : ∀ k : ℤ, q (k - 1) ≤ Bc * q k)
    (hgood : ∀ a b : ℤ, n ≤ a → a ≤ b → b ≤ m → (∀ j, a ≤ j → j ≤ b → j ∉ B) →
      q a ≤ G * (q b + ∑ j ∈ Icc a b, δ j) * Real.exp (rate * ∑ j ∈ Icc a b, ε j)) :
    ∀ k, n ≤ k → k ≤ m →
      q k ≤ (G * Bc) ^ (3 * (B ∩ Icc k m).card + 3)
        * Real.exp (rate * ∑ j ∈ Icc k m, ε j) * (q m + ∑ j ∈ Icc k m, δ j) := by
  have hP1 : 1 ≤ G * Bc := by
    have hm := mul_le_mul_of_nonneg_left hBc (by linarith only [hG] : (0 : ℝ) ≤ G)
    linarith only [hm, hG]
  have hP0 : (0 : ℝ) ≤ G * Bc := by linarith only [hP1]
  have hpow : ∀ i : ℕ, 1 ≤ (G * Bc) ^ i := fun i => one_le_pow₀ hP1
  have hpowmono : ∀ i i' : ℕ, i ≤ i' → (G * Bc) ^ i ≤ (G * Bc) ^ i' :=
    fun _ _ hii => pow_le_pow_right₀ hP1 hii
  have hBcG : Bc ≤ G * Bc := by
    have hm := mul_le_mul_of_nonneg_right hG (by linarith only [hBc] : (0 : ℝ) ≤ Bc)
    linarith only [hm]
  have hGP : G ≤ G * Bc := by
    have hm := mul_le_mul_of_nonneg_left hBc (by linarith only [hG] : (0 : ℝ) ≤ G)
    linarith only [hm]
  have hX1 : ∀ i : ℤ, 1 ≤ Real.exp (rate * ∑ j ∈ Icc i m, ε j) := by
    intro i
    rw [Real.one_le_exp_iff]
    exact mul_nonneg hrate (Finset.sum_nonneg fun j _ => hε j)
  have hsumsub : ∀ (f : ℤ → ℝ), (∀ j, 0 ≤ f j) → ∀ i i' : ℤ, i ≤ i' →
      ∑ j ∈ Icc i' m, f j ≤ ∑ j ∈ Icc i m, f j := by
    intro f hf i i' hii
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hf j
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have hblock : ∀ (f : ℤ → ℝ), (∀ j, 0 ≤ f j) → ∀ a b : ℤ, a ≤ b → b ≤ m →
      ∑ j ∈ Icc a b, f j ≤ ∑ j ∈ Icc a m, f j := by
    intro f hf a b _ _
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hf j
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have key : ∀ t : ℕ, ∀ k : ℤ, n ≤ k → k ≤ m → (m - k).toNat ≤ t →
      q k ≤ (G * Bc) ^ (3 * (B ∩ Icc k m).card + 3)
        * Real.exp (rate * ∑ j ∈ Icc k m, ε j) * (q m + ∑ j ∈ Icc k m, δ j) := by
    intro t
    induction t with
    | zero =>
        intro k _ hkm hle
        have hkeq : k = m := by omega
        subst hkeq
        exact top_case (hq k) (hpow _) (hX1 k) (Finset.sum_nonneg fun j _ => hδ j)
    | succ t ih =>
        intro k hnk hkm hle
        rcases eq_or_lt_of_le hkm with hkeq | hklt
        · subst hkeq
          exact top_case (hq k) (hpow _) (hX1 k) (Finset.sum_nonneg fun j _ => hδ j)
        · by_cases hBe : (B ∩ Icc k m).Nonempty
          · obtain ⟨b₀, hb₀mem, hb₀min⟩ :
                ∃ b₀ ∈ B ∩ Icc k m, ∀ j ∈ B ∩ Icc k m, b₀ ≤ j :=
              ⟨(B ∩ Icc k m).min' hBe, Finset.min'_mem _ hBe,
                fun j hj => Finset.min'_le _ j hj⟩
            have hb₀k : k ≤ b₀ := (Finset.mem_Icc.1 (Finset.mem_inter.1 hb₀mem).2).1
            have hb₀m : b₀ ≤ m := (Finset.mem_Icc.1 (Finset.mem_inter.1 hb₀mem).2).2
            rcases eq_or_lt_of_le hb₀k with hbk | hbk
            · -- the bottom scale itself is bad: cross it and recurse
              have hcard : (B ∩ Icc (k + 1) m).card + 1 ≤ (B ∩ Icc k m).card := by
                have hss : B ∩ Icc (k + 1) m ⊂ B ∩ Icc k m := by
                  refine (Finset.ssubset_iff_of_subset ?_).2 ⟨b₀, hb₀mem, ?_⟩
                  · intro x hx
                    simp only [Finset.mem_inter, Finset.mem_Icc] at hx ⊢
                    exact ⟨hx.1, by omega, hx.2.2⟩
                  · intro hc
                    have h2 := (Finset.mem_Icc.1 (Finset.mem_inter.1 hc).2).1
                    omega
                have hlt := Finset.card_lt_card hss
                omega
              have hcross : q k ≤ Bc * q (k + 1) := by
                have hb := hbad (k + 1)
                rwa [add_sub_cancel_right] at hb
              have hih := ih (k + 1) (by omega) (by omega) (by omega)
              refine assembleStep (G := Bc) (Sl := 0) (Xl := 1) hBc ?_ le_rfl le_rfl
                (Finset.sum_nonneg fun j _ => hδ j) (hq m)
                (by linarith only [hcross]) hih ?_ ?_
              · have hm := mul_le_mul_of_nonneg_left (hX1 (k + 1))
                  (by linarith only [hpow (3 * (B ∩ Icc (k + 1) m).card + 3)] :
                    (0 : ℝ) ≤ (G * Bc) ^ (3 * (B ∩ Icc (k + 1) m).card + 3))
                linarith only [hm, hpow (3 * (B ∩ Icc (k + 1) m).card + 3)]
              · have hd := hsumsub δ hδ k (k + 1) (by omega)
                linarith only [hd]
              · have hXX := hsumsub ε hε k (k + 1) (by omega)
                have hXe : Real.exp (rate * ∑ j ∈ Icc (k + 1) m, ε j)
                    ≤ Real.exp (rate * ∑ j ∈ Icc k m, ε j) :=
                  Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hXX hrate)
                have hA : Bc * (G * Bc) ^ (3 * (B ∩ Icc (k + 1) m).card + 3)
                    ≤ (G * Bc) * (G * Bc)
                      ^ (3 * (B ∩ Icc (k + 1) m).card + 3) :=
                  mul_le_mul_of_nonneg_right hBcG (pow_nonneg hP0 _)
                have hmm := mul_le_mul hA hXe (le_of_lt (Real.exp_pos _))
                  (mul_nonneg hP0 (pow_nonneg hP0 _))
                have hstep2 : (G * Bc) * (G * Bc)
                      ^ (3 * (B ∩ Icc (k + 1) m).card + 3)
                    ≤ (G * Bc) ^ (3 * (B ∩ Icc k m).card + 3) := by
                  have hpp := hpowmono (3 * (B ∩ Icc (k + 1) m).card + 3 + 1)
                    (3 * (B ∩ Icc k m).card + 3) (by omega)
                  calc (G * Bc) * (G * Bc)
                        ^ (3 * (B ∩ Icc (k + 1) m).card + 3)
                      = (G * Bc) ^ (3 * (B ∩ Icc (k + 1) m).card + 3 + 1) := by
                        rw [pow_succ]; ring
                    _ ≤ (G * Bc) ^ (3 * (B ∩ Icc k m).card + 3) := hpp
                have hfin := mul_le_mul_of_nonneg_right hstep2
                  (le_of_lt (Real.exp_pos (rate * ∑ j ∈ Icc k m, ε j)))
                calc Bc * ((G * Bc) ^ (3 * (B ∩ Icc (k + 1) m).card + 3)
                      * Real.exp (rate * ∑ j ∈ Icc (k + 1) m, ε j)) * 1
                    = (Bc * (G * Bc) ^ (3 * (B ∩ Icc (k + 1) m).card + 3))
                      * Real.exp (rate * ∑ j ∈ Icc (k + 1) m, ε j) := by ring
                  _ ≤ ((G * Bc) * (G * Bc)
                      ^ (3 * (B ∩ Icc (k + 1) m).card + 3))
                      * Real.exp (rate * ∑ j ∈ Icc k m, ε j) := hmm
                  _ ≤ (G * Bc) ^ (3 * (B ∩ Icc k m).card + 3)
                      * Real.exp (rate * ∑ j ∈ Icc k m, ε j) := hfin
            · -- a genuine good run `[k, b₀-1]`, then the bad scale `b₀`
              have hgd : ∀ j, k ≤ j → j ≤ b₀ - 1 → j ∉ B := by
                intro j hj1 hj2 hjB
                have hle' := hb₀min j (Finset.mem_inter.2 ⟨hjB, by
                  simp only [Finset.mem_Icc]
                  exact ⟨hj1, by omega⟩⟩)
                omega
              have hrun := hgood k (b₀ - 1) hnk (by omega) (by omega) hgd
              have hcross1 : q (b₀ - 1) ≤ Bc * q b₀ := hbad b₀
              have hXl1 : 1 ≤ Real.exp (rate * ∑ j ∈ Icc k (b₀ - 1), ε j) := by
                rw [Real.one_le_exp_iff]
                exact mul_nonneg hrate (Finset.sum_nonneg fun j _ => hε j)
              have hXlle : Real.exp (rate * ∑ j ∈ Icc k (b₀ - 1), ε j)
                  ≤ Real.exp (rate * ∑ j ∈ Icc k m, ε j) := by
                refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hrate)
                exact hblock ε hε k (b₀ - 1) (by omega) (by omega)
              rcases eq_or_lt_of_le hb₀m with hbm | hbm
              · -- the bad scale is the top scale
                rw [hbm] at hrun hcross1 hXl1 hXlle
                refine assembleStep (Pn := Bc) (Sn := 0) hG hBc hXl1
                  (Finset.sum_nonneg fun j _ => hδ j) le_rfl (hq m) hrun
                  (by linarith only [hcross1]) ?_ ?_
                · have hd := hblock δ hδ k (m - 1) (by omega) (by omega)
                  linarith only [hd]
                · have h1 : (G * Bc) ^ 1 ≤ (G * Bc)
                      ^ (3 * (B ∩ Icc k m).card + 3) := hpowmono 1 _ (by omega)
                  rw [pow_one] at h1
                  exact mul_le_mul h1 hXlle (le_of_lt (Real.exp_pos _))
                    (le_trans hP0 h1)
              · -- cross `b₀` and recurse above it
                have hcard : (B ∩ Icc (b₀ + 1) m).card + 1
                    ≤ (B ∩ Icc k m).card := by
                  have hss : B ∩ Icc (b₀ + 1) m ⊂ B ∩ Icc k m := by
                    refine (Finset.ssubset_iff_of_subset ?_).2 ⟨b₀, hb₀mem, ?_⟩
                    · intro x hx
                      simp only [Finset.mem_inter, Finset.mem_Icc] at hx ⊢
                      exact ⟨hx.1, by omega, hx.2.2⟩
                    · intro hc
                      have h2 := (Finset.mem_Icc.1 (Finset.mem_inter.1 hc).2).1
                      omega
                  have hlt := Finset.card_lt_card hss
                  omega
                have hcross2 : q b₀ ≤ Bc * q (b₀ + 1) := by
                  have hb := hbad (b₀ + 1)
                  rwa [add_sub_cancel_right] at hb
                have hih := ih (b₀ + 1) (by omega) (by omega) (by omega)
                have hBc0 : (0 : ℝ) ≤ Bc := by linarith only [hBc]
                have hqn : q (b₀ - 1)
                    ≤ (Bc * Bc * ((G * Bc)
                        ^ (3 * (B ∩ Icc (b₀ + 1) m).card + 3)
                        * Real.exp (rate * ∑ j ∈ Icc (b₀ + 1) m, ε j)))
                      * (q m + ∑ j ∈ Icc (b₀ + 1) m, δ j) := by
                  have h1 : Bc * q b₀ ≤ Bc * (Bc * q (b₀ + 1)) :=
                    mul_le_mul_of_nonneg_left hcross2 hBc0
                  have h2 : Bc * (Bc * q (b₀ + 1))
                      ≤ Bc * (Bc * ((G * Bc)
                        ^ (3 * (B ∩ Icc (b₀ + 1) m).card + 3)
                        * Real.exp (rate * ∑ j ∈ Icc (b₀ + 1) m, ε j)
                        * (q m + ∑ j ∈ Icc (b₀ + 1) m, δ j))) :=
                    mul_le_mul_of_nonneg_left
                      (mul_le_mul_of_nonneg_left hih hBc0) hBc0
                  calc q (b₀ - 1) ≤ Bc * q b₀ := hcross1
                    _ ≤ Bc * (Bc * q (b₀ + 1)) := h1
                    _ ≤ Bc * (Bc * ((G * Bc)
                        ^ (3 * (B ∩ Icc (b₀ + 1) m).card + 3)
                        * Real.exp (rate * ∑ j ∈ Icc (b₀ + 1) m, ε j)
                        * (q m + ∑ j ∈ Icc (b₀ + 1) m, δ j))) := h2
                    _ = (Bc * Bc * ((G * Bc)
                        ^ (3 * (B ∩ Icc (b₀ + 1) m).card + 3)
                        * Real.exp (rate * ∑ j ∈ Icc (b₀ + 1) m, ε j)))
                        * (q m + ∑ j ∈ Icc (b₀ + 1) m, δ j) := by ring
                have hPn1 : (1 : ℝ) ≤ Bc * Bc * ((G * Bc)
                    ^ (3 * (B ∩ Icc (b₀ + 1) m).card + 3)
                    * Real.exp (rate * ∑ j ∈ Icc (b₀ + 1) m, ε j)) := by
                  have hA : (1 : ℝ) ≤ Bc * Bc := by
                    have hm := mul_le_mul_of_nonneg_left hBc hBc0
                    linarith only [hm, hBc]
                  have hB2 : (1 : ℝ) ≤ (G * Bc)
                      ^ (3 * (B ∩ Icc (b₀ + 1) m).card + 3)
                      * Real.exp (rate * ∑ j ∈ Icc (b₀ + 1) m, ε j) := by
                    have hm := mul_le_mul_of_nonneg_left (hX1 (b₀ + 1))
                      (by linarith only
                        [hpow (3 * (B ∩ Icc (b₀ + 1) m).card + 3)] :
                        (0 : ℝ) ≤ (G * Bc)
                          ^ (3 * (B ∩ Icc (b₀ + 1) m).card + 3))
                    linarith only [hm, hpow (3 * (B ∩ Icc (b₀ + 1) m).card + 3)]
                  have hm := mul_le_mul hA hB2 (by norm_num) (by linarith only [hA])
                  linarith only [hm]
                refine assembleStep hG hPn1 hXl1
                  (Finset.sum_nonneg fun j _ => hδ j)
                  (Finset.sum_nonneg fun j _ => hδ j) (hq m) hrun hqn ?_ ?_
                · exact sum_two_blocks_le hδ (le_of_lt hbk) (le_of_lt hbm)
                · have hεblocks := sum_two_blocks_le hε (le_of_lt hbk)
                    (le_of_lt hbm)
                  have hXprod : Real.exp (rate * ∑ j ∈ Icc (b₀ + 1) m, ε j)
                      * Real.exp (rate * ∑ j ∈ Icc k (b₀ - 1), ε j)
                      ≤ Real.exp (rate * ∑ j ∈ Icc k m, ε j) := by
                    rw [← Real.exp_add]
                    refine Real.exp_le_exp.mpr ?_
                    have hm := mul_le_mul_of_nonneg_left hεblocks hrate
                    linarith only [hm]
                  have hcoef : G * (Bc * Bc) ≤ (G * Bc) ^ 2 := by
                    have hm : (G * Bc) * Bc ≤ (G * Bc) * (G * Bc) :=
                      mul_le_mul_of_nonneg_left hBcG hP0
                    calc G * (Bc * Bc) = (G * Bc) * Bc := by ring
                      _ ≤ (G * Bc) * (G * Bc) := hm
                      _ = (G * Bc) ^ 2 := by ring
                  have hpowfin : (G * Bc) ^ 2 * (G * Bc)
                        ^ (3 * (B ∩ Icc (b₀ + 1) m).card + 3)
                      ≤ (G * Bc) ^ (3 * (B ∩ Icc k m).card + 3) := by
                    have hpp := hpowmono
                      (2 + (3 * (B ∩ Icc (b₀ + 1) m).card + 3))
                      (3 * (B ∩ Icc k m).card + 3) (by omega)
                    rwa [pow_add] at hpp
                  have hleft : G * (Bc * Bc) * (G * Bc)
                        ^ (3 * (B ∩ Icc (b₀ + 1) m).card + 3)
                      ≤ (G * Bc) ^ (3 * (B ∩ Icc k m).card + 3) := by
                    have hm := mul_le_mul_of_nonneg_right hcoef
                      (pow_nonneg hP0 (3 * (B ∩ Icc (b₀ + 1) m).card + 3))
                    exact le_trans hm hpowfin
                  have hAle : G * (Bc * Bc * ((G * Bc)
                        ^ (3 * (B ∩ Icc (b₀ + 1) m).card + 3)
                        * Real.exp (rate * ∑ j ∈ Icc (b₀ + 1) m, ε j)))
                      * Real.exp (rate * ∑ j ∈ Icc k (b₀ - 1), ε j)
                      = (G * (Bc * Bc) * (G * Bc)
                        ^ (3 * (B ∩ Icc (b₀ + 1) m).card + 3))
                      * (Real.exp (rate * ∑ j ∈ Icc (b₀ + 1) m, ε j)
                        * Real.exp (rate * ∑ j ∈ Icc k (b₀ - 1), ε j)) := by
                    ring
                  rw [hAle]
                  refine mul_le_mul hleft hXprod ?_ (pow_nonneg hP0 _)
                  exact mul_nonneg (le_of_lt (Real.exp_pos _))
                    (le_of_lt (Real.exp_pos _))
          · -- no bad scale at or above `k`: one good run all the way to `m`
            have hgd : ∀ j, k ≤ j → j ≤ m → j ∉ B := by
              intro j hj1 hj2 hjB
              exact hBe ⟨j, Finset.mem_inter.2 ⟨hjB, by
                simp only [Finset.mem_Icc]
                exact ⟨hj1, hj2⟩⟩⟩
            have hrun := hgood k m hnk hkm le_rfl hgd
            have hpre : G ≤ (G * Bc) ^ (3 * (B ∩ Icc k m).card + 3) := by
              have h1 : (G * Bc) ^ 1 ≤ (G * Bc)
                  ^ (3 * (B ∩ Icc k m).card + 3) := hpowmono 1 _ (by omega)
              rw [pow_one] at h1
              linarith only [hGP, h1]
            have hs0 : (0 : ℝ) ≤ q m + ∑ j ∈ Icc k m, δ j := by
              have hsum := Finset.sum_nonneg (f := δ) (s := Icc k m) fun j _ => hδ j
              linarith only [hsum, hq m]
            calc q k ≤ G * (q m + ∑ j ∈ Icc k m, δ j)
                  * Real.exp (rate * ∑ j ∈ Icc k m, ε j) := hrun
              _ ≤ (G * Bc) ^ (3 * (B ∩ Icc k m).card + 3)
                  * (q m + ∑ j ∈ Icc k m, δ j)
                  * Real.exp (rate * ∑ j ∈ Icc k m, ε j) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right hpre hs0)
                  (le_of_lt (Real.exp_pos _))
              _ = (G * Bc) ^ (3 * (B ∩ Icc k m).card + 3)
                  * Real.exp (rate * ∑ j ∈ Icc k m, ε j)
                  * (q m + ∑ j ∈ Icc k m, δ j) := by ring
  intro k hnk hkm
  exact key (m - n).toNat k hnk hkm (by omega)

/-! ### `e.combined.bound` and conclusion (i) -/

section Conclusions

variable {E p ε δ : ℤ → ℝ} {θ κ Cstab : ℝ} {h : ℕ}

/-- **`e.combined.bound`**, in the product-prefactor form the downward induction
yields (see the module docstring for the/ divergence from the printed additive
form).

For every `k ∈ [n,m]`,
`E_k + p_k ≤ (goodConst · badConst)^(3|B ∩ [k,m]| + 3) · exp(goodRate ∑_{[k,m]} ε) ·
(E_m + p_m + ∑_{[k,m]} δ)`, uniformly in the length `m − n`. -/
theorem combinedBound (hθpos : 0 < θ) (hθh : θ ^ h < 3 / 5) (hE : ∀ k, 0 ≤ E k)
    (hp : ∀ k, 0 ≤ p k) (hε : ∀ k, 0 ≤ ε k) (hδ : ∀ k, 0 ≤ δ k) (hκ : 1 ≤ κ)
    (hC : 0 ≤ Cstab) (hmono : ∀ k, E k ≤ κ * E (k + 1))
    (hstab : ∀ k, |p k - p (k - 1)| ≤ Cstab * (E k + E (k - 1))) {n m : ℤ}
    (B : Finset ℤ)
    (hdecay : ∀ j, n ≤ j → j ≤ m → j ∉ B →
      E (j - h) ≤ θ ^ h * E j + ε j * p j + δ j) :
    ∀ k, n ≤ k → k ≤ m →
      E k + p k
        ≤ (goodConst h κ Cstab * badConst κ Cstab)
            ^ (3 * (B ∩ Icc k m).card + 3)
          * Real.exp (goodRate Cstab * ∑ j ∈ Icc k m, ε j)
          * ((E m + p m) + ∑ j ∈ Icc k m, δ j) := by
  refine assembleRuns (q := fun k => E k + p k) B
    (fun k => by linarith only [hE k, hp k]) hε hδ (one_le_goodConst h hκ hC)
    (one_le_badConst hκ hC) (goodRate_nonneg hC) ?_ ?_
  · intro k
    exact badCrossing hE hκ hC hmono hp hstab k
  · intro a b hna hab hbm hgd
    have hdec : ∀ j, a ≤ j → j ≤ b →
        E (j - h) ≤ θ ^ h * E j + ε j * p j + δ j := by
      intro j hj1 hj2
      exact hdecay j (le_trans hna hj1) (le_trans hj2 hbm) (hgd j hj1 hj2)
    exact goodRunBound hθpos hθh hE hp hε hδ hκ hC hmono hstab hab hdec

/-- **Conclusion (i) of `l.iteration.lemma`** (`e.iteration.slope.lemma`), in the
oscillation form and with the product prefactor.

The two endpoint comparisons --- which per the binding need *opposite* halves
of the affine window geometry and are not bare triangle inequalities --- enter
as the interface hypotheses `hlo`, `hhi`; they are the source's own Step-3
conclusions and must be discharged from the window sandwich at each use site,
never lifted as binders into a source-facing statement. -/
theorem iterationSlopeBound (hθpos : 0 < θ) (hθh : θ ^ h < 3 / 5)
    (hE : ∀ k, 0 ≤ E k) (hp : ∀ k, 0 ≤ p k) (hε : ∀ k, 0 ≤ ε k)
    (hδ : ∀ k, 0 ≤ δ k) (hκ : 1 ≤ κ) (hC : 0 ≤ Cstab)
    (hmono : ∀ k, E k ≤ κ * E (k + 1))
    (hstab : ∀ k, |p k - p (k - 1)| ≤ Cstab * (E k + E (k - 1))) {n m : ℤ}
    (hnm : n ≤ m) (B : Finset ℤ)
    (hdecay : ∀ j, n ≤ j → j ≤ m → j ∉ B →
      E (j - h) ≤ θ ^ h * E j + ε j * p j + δ j) (osc : ℤ → ℝ) {Ci : ℝ}
    (hCi : 1 ≤ Ci) (hlo : osc n ≤ Ci * (E n + p n)) (hhi : E m + p m ≤ Ci * osc m) :
    osc n
      ≤ Ci ^ 2 * (goodConst h κ Cstab * badConst κ Cstab)
          ^ (3 * (B ∩ Icc n m).card + 3)
        * Real.exp (goodRate Cstab * ∑ j ∈ Icc n m, ε j)
        * (osc m + ∑ j ∈ Icc n m, δ j) := by
  have hCi0 : (0 : ℝ) ≤ Ci := by linarith only [hCi]
  have hD0 : (0 : ℝ) ≤ ∑ j ∈ Icc n m, δ j := Finset.sum_nonneg fun j _ => hδ j
  have hcb := combinedBound hθpos hθh hE hp hε hδ hκ hC hmono hstab B hdecay n
    le_rfl hnm
  have hPX0 : (0 : ℝ) ≤ (goodConst h κ Cstab * badConst κ Cstab)
      ^ (3 * (B ∩ Icc n m).card + 3)
      * Real.exp (goodRate Cstab * ∑ j ∈ Icc n m, ε j) := by
    have hP1 : 1 ≤ goodConst h κ Cstab * badConst κ Cstab := by
      have hg := one_le_goodConst h hκ hC
      have hb := one_le_badConst hκ hC
      have hm := mul_le_mul_of_nonneg_left hb (by linarith only [hg] :
        (0 : ℝ) ≤ goodConst h κ Cstab)
      linarith only [hm, hg]
    exact mul_nonneg (pow_nonneg (by linarith only [hP1]) _)
      (le_of_lt (Real.exp_pos _))
  have htop : (E m + p m) + ∑ j ∈ Icc n m, δ j
      ≤ Ci * (osc m + ∑ j ∈ Icc n m, δ j) := by
    have hm := mul_le_mul_of_nonneg_right hCi hD0
    have hexp : Ci * (osc m + ∑ j ∈ Icc n m, δ j)
        = Ci * osc m + Ci * ∑ j ∈ Icc n m, δ j := by ring
    rw [hexp]
    linarith only [hhi, hm]
  calc osc n ≤ Ci * (E n + p n) := hlo
    _ ≤ Ci * ((goodConst h κ Cstab * badConst κ Cstab)
        ^ (3 * (B ∩ Icc n m).card + 3)
        * Real.exp (goodRate Cstab * ∑ j ∈ Icc n m, ε j)
        * ((E m + p m) + ∑ j ∈ Icc n m, δ j)) :=
      mul_le_mul_of_nonneg_left hcb hCi0
    _ ≤ Ci * ((goodConst h κ Cstab * badConst κ Cstab)
        ^ (3 * (B ∩ Icc n m).card + 3)
        * Real.exp (goodRate Cstab * ∑ j ∈ Icc n m, ε j)
        * (Ci * (osc m + ∑ j ∈ Icc n m, δ j))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htop hPX0) hCi0
    _ = Ci ^ 2 * (goodConst h κ Cstab * badConst κ Cstab)
        ^ (3 * (B ∩ Icc n m).card + 3)
        * Real.exp (goodRate Cstab * ∑ j ∈ Icc n m, ε j)
        * (osc m + ∑ j ∈ Icc n m, δ j) := by ring

end Conclusions

end

end Algsuperdiff.Section4.Provider.ExcessDecay
