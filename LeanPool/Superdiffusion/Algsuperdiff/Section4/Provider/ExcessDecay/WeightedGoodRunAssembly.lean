/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.WeightedGoodRun

/-!
# WeightedGoodRunAssembly

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The weighted run assembly across the bad scales (decay-carrying)

ABK26, §4.3, `l.iteration.lemma`, Step 3 in the **decay-carrying**
bookkeeping that conclusion (ii) (`e.excess.decay.lemma`) needs, for
abstract nonnegative sequences.

`IterationLemma.assembleRuns` concatenates the good runs of `([n,m] ∩ ℤ) ∖ B` keeping the
error terms and *discarding* the geometric decay.  `weightedAssemble` does the opposite:
it keeps a genuine `θ^{m−k}` on the top excess, and pays for it with

* one factor `Λ = 2(κθ^{-1})^{h+2}` per bad scale crossed, plus one for the initial run;
* a **single** error budget `(5/2)·Mp + ∑_{[k,m]} δ` --- length-independent, because
  `weightedRunBound` is length-independent and the factor `2` inside `Λ` absorbs the one
  extra copy each crossing produces.

```
E_k ≤ Λ^{|B ∩ [k,m]| + 1} · (θ^{m−k} E_m + (5/2) Mp + ∑_{[k,m]} δ) .
```

The `θ`-payback `θ^{-(h+2)(|B ∩ [k,m]|+1)}` hidden inside `Λ^{|B∩[k,m]|+1}` is
exactly the division remainder plus the crossings, and it is dominated by the
frozen statement's `θ^{-C(h+1)(|B|+1)}` for every `C ≥ 2`; the `κ`-growth is
carried by the `exp` factor.

## References

* ABK26, `l.iteration.lemma` Step 3; conclusion (ii).
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open Finset

noncomputable section

/-! ### Absorption helpers (pure algebra over abstract reals) -/

/-- The top-scale case: the invariant is trivial at `k = m`. -/
private theorem weightedTopCase {q P R S : ℝ} (hq : 0 ≤ q) (hP : 1 ≤ P) (hR : 0 ≤ R)
    (hS : 0 ≤ S) : q ≤ P * (q + R + S) := by
  have h0 : (0 : ℝ) ≤ q + R + S := by linarith only [hq, hR, hS]
  have h1 : q + R + S ≤ P * (q + R + S) := by
    have hm := mul_le_mul_of_nonneg_right hP h0
    linarith only [hm]
  linarith only [h1, hR, hS]

/-- Crossing one scale and composing with the invariant one scale higher. -/
private theorem weightedCrossAbsorb {q qn c W W' ti V V' : ℝ} (hc0 : 0 ≤ c)
    (hW'0 : 0 ≤ W') (hV0 : 0 ≤ V) (hq : q ≤ c * qn) (hqn : qn ≤ W' * V')
    (hV' : V' ≤ ti * V) (hpref : c * ti * W' ≤ W) : q ≤ W * V := by
  have h1 : c * qn ≤ c * (W' * V') := mul_le_mul_of_nonneg_left hqn hc0
  have h2 : W' * V' ≤ W' * (ti * V) := mul_le_mul_of_nonneg_left hV' hW'0
  have h3 : c * (W' * V') ≤ c * (W' * (ti * V)) := mul_le_mul_of_nonneg_left h2 hc0
  have h4 : c * (W' * (ti * V)) = c * ti * W' * V := by ring
  have h5 : c * ti * W' * V ≤ W * V := mul_le_mul_of_nonneg_right hpref hV0
  linarith only [hq, h1, h3, h4, h5]

/-- The good run whose top value is controlled by a multiple of the *top excess*: the case
where the run reaches the top scale `m`. -/
private theorem weightedRunAbsorb {q P r Y X R S V W : ℝ} (hP0 : 0 ≤ P) (hr1 : 1 ≤ r)
    (hR0 : 0 ≤ R) (hS0 : 0 ≤ S) (hV0 : 0 ≤ V) (hq : q ≤ P * (Y + R + S))
    (hY : Y ≤ r * X) (hXRS : X + R + S ≤ V) (hpref : P * r ≤ W) : q ≤ W * V := by
  have h2 : r * X + R + S ≤ r * (X + R + S) := by
    have hm := mul_le_mul_of_nonneg_right hr1 (by linarith only [hR0, hS0] : (0 : ℝ) ≤ R + S)
    linarith only [hm]
  have h3 : r * (X + R + S) ≤ r * V :=
    mul_le_mul_of_nonneg_left hXRS (by linarith only [hr1])
  have h4 : P * (Y + R + S) ≤ P * (r * V) :=
    mul_le_mul_of_nonneg_left (by linarith only [hY, h2, h3]) hP0
  have h5 : P * (r * V) = P * r * V := by ring
  have h6 : P * r * V ≤ W * V := mul_le_mul_of_nonneg_right hpref hV0
  linarith only [hq, h4, h5, h6]

/-- The good run whose top value is controlled by a multiple of the *whole invariant* one
bad scale higher: the generic case.  The factor `2` on the prefactor is what absorbs the
extra copy of the error budget produced by the run. -/
private theorem weightedRunAbsorbInner {q P Z Y R S V W : ℝ} (hP0 : 0 ≤ P) (hZ1 : 1 ≤ Z)
    (hV0 : 0 ≤ V) (hq : q ≤ P * (Y + R + S))
    (hY : Y ≤ Z * V) (hRS : R + S ≤ V) (hpref : P * (2 * Z) ≤ W) : q ≤ W * V := by
  have h2 : V ≤ Z * V := le_mul_of_one_le_left hV0 hZ1
  have h3 : Y + R + S ≤ 2 * Z * V := by linarith only [hY, hRS, h2]
  have h4 : P * (Y + R + S) ≤ P * (2 * Z * V) := mul_le_mul_of_nonneg_left h3 hP0
  have h5 : P * (2 * Z * V) = P * (2 * Z) * V := by ring
  have h6 : P * (2 * Z) * V ≤ W * V := mul_le_mul_of_nonneg_right hpref hV0
  linarith only [hq, h4, h5, h6]

/-! ### The assembly -/

section Assembly

variable {E δ w : ℤ → ℝ} {θ κ Mp : ℝ} {h : ℕ}

private theorem weightedGoodRunAssembly_comparisonBounds1 :
    ∀ {E δ : ℤ → ℝ} {θ κ Mp : ℝ} {h : ℕ} (_ : (0 : ℝ) < θ) (_ : θ ≤ (1 : ℝ))
      (_ : ∀ (k : ℤ), (0 : ℝ) ≤ E k) (_ : ∀ (k : ℤ), (0 : ℝ) ≤ δ k) (_ : (0 : ℝ) ≤ Mp) (_ : (1 : ℝ) ≤ κ) {m : ℤ},
      (0 : ℝ) ≤ κ ∧
        (0 : ℝ) ≤ θ⁻¹ ∧
          (1 : ℝ) ≤ κ * θ⁻¹ ∧
            (0 : ℝ) ≤ κ * θ⁻¹ ∧
              (∀ (i : ℕ), (1 : ℝ) ≤ ((2 : ℝ) * (κ * θ⁻¹) ^ (h + (2 : ℕ))) ^ i) ∧
                (∀ (i i' : ℕ),
                    i ≤ i' → ((2 : ℝ) * (κ * θ⁻¹) ^ (h + (2 : ℕ))) ^ i ≤ ((2 : ℝ) * (κ * θ⁻¹) ^ (h + (2 : ℕ))) ^ i') ∧
                  (∀ (i b : ℤ), b ≤ m → ∑ j ∈ Icc i b, δ j ≤ ∑ j ∈ Icc i m, δ j) ∧
                    (∀ (i : ℤ), (0 : ℝ) ≤ ∑ j ∈ Icc i m, δ j) ∧
                      (∀ (i : ℤ), (0 : ℝ) ≤ θ ^ (m - i) * E m) ∧
                        (∀ (i : ℤ), (0 : ℝ) ≤ θ ^ (m - i) * E m + (5 / 2 : ℝ) * Mp + ∑ j ∈ Icc i m, δ j) ∧
                          ∀ (i i' e : ℤ) (p : ℕ),
                            (0 : ℤ) ≤ e →
                              θ ^ e * θ ^ (m - i') = θ ^ (m - i) * θ⁻¹ ^ p →
                                i ≤ i' →
                                  θ ^ e * (θ ^ (m - i') * E m + (5 / 2 : ℝ) * Mp + ∑ j ∈ Icc i' m, δ j) ≤
                                    θ⁻¹ ^ p * (θ ^ (m - i) * E m + (5 / 2 : ℝ) * Mp + ∑ j ∈ Icc i m, δ j) := by
  intro E δ θ κ Mp h hθpos hθ1 hE hδ hMp hκ m
  have hκ0 : (0 : ℝ) ≤ κ := by linarith only [hκ]
  have hinv : 1 ≤ θ⁻¹ := one_le_inv_of_le_one hθpos hθ1
  have hinv0 : (0 : ℝ) ≤ θ⁻¹ := by linarith only [hinv]
  have hκθ : 1 ≤ κ * θ⁻¹ := one_le_mul_inv hκ hθpos hθ1
  have hκθ0 : (0 : ℝ) ≤ κ * θ⁻¹ := by linarith only [hκθ]
  have hL1 : (1 : ℝ) ≤ 2 * (κ * θ⁻¹) ^ (h + 2) := by
    have hp : (1 : ℝ) ≤ (κ * θ⁻¹) ^ (h + 2) := one_le_pow₀ hκθ
    linarith only [hp]
  have hL0 : (0 : ℝ) ≤ 2 * (κ * θ⁻¹) ^ (h + 2) := by linarith only [hL1]
  have hLpow : ∀ i : ℕ, (1 : ℝ) ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ i := fun _ => one_le_pow₀ hL1
  have hLmono : ∀ i i' : ℕ, i ≤ i' →
      (2 * (κ * θ⁻¹) ^ (h + 2)) ^ i ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ i' :=
    fun _ _ hii => pow_le_pow_right₀ hL1 hii
  have hδsub : ∀ i i' : ℤ, i ≤ i' → ∑ j ∈ Icc i' m, δ j ≤ ∑ j ∈ Icc i m, δ j := by
    intro i i' hii
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hδ j
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have hδblk : ∀ i b : ℤ, b ≤ m → ∑ j ∈ Icc i b, δ j ≤ ∑ j ∈ Icc i m, δ j := by
    intro i b _
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun j _ _ => hδ j
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    omega
  have hδ0 : ∀ i : ℤ, (0 : ℝ) ≤ ∑ j ∈ Icc i m, δ j :=
    fun i => Finset.sum_nonneg fun j _ => hδ j
  have hXnn : ∀ i : ℤ, (0 : ℝ) ≤ θ ^ (m - i) * E m :=
    fun i => mul_nonneg (le_of_lt (zpow_pos hθpos _)) (hE m)
  have hVnn : ∀ i : ℤ,
      (0 : ℝ) ≤ θ ^ (m - i) * E m + 5 / 2 * Mp + ∑ j ∈ Icc i m, δ j :=
    fun i => by linarith only [hXnn i, hMp, hδ0 i]
  -- the `V`-shift: a `θ`-power times the invariant higher up is below `(θ⁻¹)^p` times it
  have hVshift : ∀ (i i' : ℤ) (e : ℤ) (p : ℕ), 0 ≤ e →
      θ ^ e * θ ^ (m - i') = θ ^ (m - i) * (θ⁻¹) ^ p → i ≤ i' →
      θ ^ e * (θ ^ (m - i') * E m + 5 / 2 * Mp + ∑ j ∈ Icc i' m, δ j)
        ≤ (θ⁻¹) ^ p * (θ ^ (m - i) * E m + 5 / 2 * Mp + ∑ j ∈ Icc i m, δ j) := by
    intro i i' e p he hpow hii
    have he1 : θ ^ e ≤ 1 := zpow_le_one₀ hθpos hθ1 he
    have he0 : (0 : ℝ) ≤ θ ^ e := le_of_lt (zpow_pos hθpos e)
    have hip : (1 : ℝ) ≤ (θ⁻¹) ^ p := one_le_pow₀ hinv
    have hid : θ ^ e * (θ ^ (m - i') * E m) = θ ^ (m - i) * (θ⁻¹) ^ p * E m := by
      rw [← hpow]
      ring
    have hR : θ ^ e * (5 / 2 * Mp) ≤ 5 / 2 * Mp := by
      have hm := mul_le_mul_of_nonneg_right he1 (by linarith only [hMp] : (0 : ℝ) ≤ 5 / 2 * Mp)
      linarith only [hm]
    have hS : θ ^ e * ∑ j ∈ Icc i' m, δ j ≤ ∑ j ∈ Icc i m, δ j := by
      have hm := mul_le_mul_of_nonneg_right he1 (hδ0 i')
      have hd := hδsub i i' hii
      linarith only [hm, hd]
    have hgrow : θ ^ (m - i) * (θ⁻¹) ^ p * E m + 5 / 2 * Mp + ∑ j ∈ Icc i m, δ j
        ≤ (θ⁻¹) ^ p * (θ ^ (m - i) * E m + 5 / 2 * Mp + ∑ j ∈ Icc i m, δ j) := by
      have hm := mul_le_mul_of_nonneg_right hip
        (by linarith only [hMp, hδ0 i] : (0 : ℝ) ≤ 5 / 2 * Mp + ∑ j ∈ Icc i m, δ j)
      have hexp : (θ⁻¹) ^ p * (θ ^ (m - i) * E m + 5 / 2 * Mp + ∑ j ∈ Icc i m, δ j)
          = θ ^ (m - i) * (θ⁻¹) ^ p * E m
            + (θ⁻¹) ^ p * (5 / 2 * Mp + ∑ j ∈ Icc i m, δ j) := by ring
      rw [hexp]
      linarith only [hm]
    have hexp2 : θ ^ e * (θ ^ (m - i') * E m + 5 / 2 * Mp + ∑ j ∈ Icc i' m, δ j)
        = θ ^ e * (θ ^ (m - i') * E m) + θ ^ e * (5 / 2 * Mp)
          + θ ^ e * ∑ j ∈ Icc i' m, δ j := by ring
    rw [hexp2, hid]
    linarith only [hR, hS, hgrow]
  exact ⟨hκ0, hinv0, hκθ, hκθ0, hLpow, hLmono, hδblk, hδ0, hXnn, hVnn, hVshift⟩

private theorem weightedGoodRunAssembly_estimate1 :
    ∀ {E : ℤ → ℝ} {θ κ : ℝ} {h : ℕ} (hθpos : (0 : ℝ) < θ)
      (hmono : ∀ (k : ℤ), E k ≤ κ * E (k + (1 : ℤ))) {m : ℤ} (hinv0 : (0 : ℝ) ≤ θ⁻¹) (k b₀ : ℤ) (hbm : b₀ = m),
      θ ^ (b₀ - (1 : ℤ) - k) * E (b₀ - (1 : ℤ)) ≤ κ * θ⁻¹ * (θ ^ (m - k) * E m) := by
  intro E θ κ h hθpos hmono m hinv0 k b₀ hbm
  have hb : E (b₀ - 1) ≤ κ * E b₀ := by
    have h := hmono (b₀ - 1)
    rwa [sub_add_cancel] at h
  have hcross : E (b₀ - 1) ≤ κ * E m := by
    rw [← hbm]
    exact hb
  have hzid : θ ^ (b₀ - 1 - k) = θ ^ (m - k) * θ⁻¹ := by
    rw [← hbm, show b₀ - 1 - k = b₀ - k - 1 from by ring,
      zpow_sub_one₀ (ne_of_gt hθpos)]
  have hm0 : (0 : ℝ) ≤ θ ^ (m - k) * θ⁻¹ :=
    mul_nonneg (le_of_lt (zpow_pos hθpos _)) hinv0
  have hmul := mul_le_mul_of_nonneg_left hcross hm0
  rw [hzid]
  calc θ ^ (m - k) * θ⁻¹ * E (b₀ - 1)
      ≤ θ ^ (m - k) * θ⁻¹ * (κ * E m) := hmul
    _ = κ * θ⁻¹ * (θ ^ (m - k) * E m) := by ring

private theorem weightedGoodRunAssembly_estimate2 :
    ∀ {θ κ : ℝ} {h : ℕ} {n m : ℤ} (B : Finset ℤ) (hκθ : (1 : ℝ) ≤ κ * θ⁻¹)
      (hLmono :
        ∀ (i i' : ℕ), i ≤ i' → ((2 : ℝ) * (κ * θ⁻¹) ^ (h + (2 : ℕ))) ^ i ≤ ((2 : ℝ) * (κ * θ⁻¹) ^ (h + (2 : ℕ))) ^ i')
      (T : ℕ) (k : ℤ) (hcard0 : #(B ∩ Icc k m) = (0 : ℕ)),
      (κ * θ⁻¹) ^ h ≤ ((2 : ℝ) * (κ * θ⁻¹) ^ (h + (2 : ℕ))) ^ (#(B ∩ Icc k m) + (1 : ℕ)) := by
  intro θ κ h n m B hκθ hLmono T k hcard0
  have h1 : (κ * θ⁻¹) ^ h ≤ (κ * θ⁻¹) ^ (h + 2) :=
    pow_le_pow_right₀ hκθ (by omega)
  have h2 : (κ * θ⁻¹) ^ (h + 2) ≤ 2 * (κ * θ⁻¹) ^ (h + 2) := by
    have := one_le_pow₀ (n := h + 2) hκθ
    linarith only [this]
  have h3 : (2 * (κ * θ⁻¹) ^ (h + 2)) ^ 1
      ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc k m).card + 1) :=
    hLmono 1 _ (by omega)
  rw [pow_one] at h3
  linarith only [h1, h2, h3]

private theorem weightedGoodRunAssembly_estimate3 :
    ∀ {n m : ℤ} (B : Finset ℤ) (T : ℕ) (k b₀ : ℤ)
      (hb₀mem : b₀ ∈ B ∩ Icc k m) (hbk : k = b₀), #(B ∩ Icc (k + (1 : ℤ)) m) + (1 : ℕ) ≤ #(B ∩ Icc k m) := by
  intro n m B T k b₀ hb₀mem hbk
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

/-- **The decay-carrying run assembly.**

For abstract nonnegative sequences with the `h`-gap decay recurrence on
`([n,m] ∩ ℤ) ∖ B`, the error scale `w` bounded by `Mp` on `[n,m]`, and per-scale
quasi-monotonicity `E_k ≤ κ E_{k+1}`:

```
E_k ≤ (2 (κ θ^{-1})^{h+2})^{|B ∩ [k,m]| + 1}
        · (θ^{m−k} E_m + (5/2) Mp + ∑_{[k,m]} δ)      for every k ∈ [n,m].
```

Both the geometric factor on `E_m` and the length-independence of the error budget are
essential for conclusion (ii): the first is its `θ^{m−n}` slot, the second is what makes
its middle slot carry a *single* power of `M`. -/
private theorem weightedGoodRunAssembly_estimate4 :
    ∀ {E δ : ℤ → ℝ} {θ κ Mp : ℝ} {h : ℕ} (hθpos : (0 : ℝ) < θ) {m : ℤ}
      (B : Finset ℤ) (hκ0 : (0 : ℝ) ≤ κ) (k b₀ : ℤ)
      (hih :
        E (b₀ + (1 : ℤ)) ≤
          ((2 : ℝ) * (κ * θ⁻¹) ^ (h + (2 : ℕ))) ^ (#(B ∩ Icc (b₀ + (1 : ℤ)) m) + (1 : ℕ)) *
            (θ ^ (m - (b₀ + (1 : ℤ))) * E m + (5 / 2 : ℝ) * Mp + ∑ j ∈ Icc (b₀ + (1 : ℤ)) m, δ j))
      (hVs :
        θ ^ (b₀ - (1 : ℤ) - k) * (θ ^ (m - (b₀ + (1 : ℤ))) * E m + (5 / 2 : ℝ) * Mp + ∑ j ∈ Icc (b₀ + (1 : ℤ)) m, δ j) ≤
          θ⁻¹ ^ (2 : ℕ) * (θ ^ (m - k) * E m + (5 / 2 : ℝ) * Mp + ∑ j ∈ Icc k m, δ j))
      (hW'0 : (0 : ℝ) ≤ ((2 : ℝ) * (κ * θ⁻¹) ^ (h + (2 : ℕ))) ^ (#(B ∩ Icc (b₀ + (1 : ℤ)) m) + (1 : ℕ)))
      (hcross2 : E (b₀ - (1 : ℤ)) ≤ κ * (κ * E (b₀ + (1 : ℤ)))),
      θ ^ (b₀ - (1 : ℤ) - k) * E (b₀ - (1 : ℤ)) ≤
        (κ * θ⁻¹) ^ (2 : ℕ) * ((2 : ℝ) * (κ * θ⁻¹) ^ (h + (2 : ℕ))) ^ (#(B ∩ Icc (b₀ + (1 : ℤ)) m) + (1 : ℕ)) *
          (θ ^ (m - k) * E m + (5 / 2 : ℝ) * Mp + ∑ j ∈ Icc k m, δ j) := by
  intro E δ θ κ Mp h hθpos m B hκ0 k b₀ hih hVs hW'0 hcross2
  have hz0 : (0 : ℝ) ≤ θ ^ (b₀ - 1 - k) := le_of_lt (zpow_pos hθpos _)
  have hc0 : (0 : ℝ) ≤ κ * (κ
      * (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc (b₀ + 1) m).card + 1)) :=
    mul_nonneg hκ0 (mul_nonneg hκ0 hW'0)
  have s1 : θ ^ (b₀ - 1 - k) * E (b₀ - 1)
      ≤ θ ^ (b₀ - 1 - k) * (κ * (κ * E (b₀ + 1))) :=
    mul_le_mul_of_nonneg_left hcross2 hz0
  have s2 : θ ^ (b₀ - 1 - k) * (κ * (κ * E (b₀ + 1)))
      ≤ θ ^ (b₀ - 1 - k) * (κ * (κ
        * ((2 * (κ * θ⁻¹) ^ (h + 2))
            ^ ((B ∩ Icc (b₀ + 1) m).card + 1)
          * (θ ^ (m - (b₀ + 1)) * E m + 5 / 2 * Mp
            + ∑ j ∈ Icc (b₀ + 1) m, δ j)))) :=
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hih hκ0) hκ0) hz0
  have s3 : θ ^ (b₀ - 1 - k) * (κ * (κ
        * ((2 * (κ * θ⁻¹) ^ (h + 2))
            ^ ((B ∩ Icc (b₀ + 1) m).card + 1)
          * (θ ^ (m - (b₀ + 1)) * E m + 5 / 2 * Mp
            + ∑ j ∈ Icc (b₀ + 1) m, δ j))))
      = κ * (κ * (2 * (κ * θ⁻¹) ^ (h + 2))
            ^ ((B ∩ Icc (b₀ + 1) m).card + 1))
        * (θ ^ (b₀ - 1 - k)
          * (θ ^ (m - (b₀ + 1)) * E m + 5 / 2 * Mp
            + ∑ j ∈ Icc (b₀ + 1) m, δ j)) := by ring
  have s4 : κ * (κ * (2 * (κ * θ⁻¹) ^ (h + 2))
          ^ ((B ∩ Icc (b₀ + 1) m).card + 1))
        * (θ ^ (b₀ - 1 - k)
          * (θ ^ (m - (b₀ + 1)) * E m + 5 / 2 * Mp
            + ∑ j ∈ Icc (b₀ + 1) m, δ j))
      ≤ κ * (κ * (2 * (κ * θ⁻¹) ^ (h + 2))
          ^ ((B ∩ Icc (b₀ + 1) m).card + 1))
        * ((θ⁻¹) ^ 2
          * (θ ^ (m - k) * E m + 5 / 2 * Mp + ∑ j ∈ Icc k m, δ j)) :=
    mul_le_mul_of_nonneg_left hVs hc0
  have s5 : κ * (κ * (2 * (κ * θ⁻¹) ^ (h + 2))
          ^ ((B ∩ Icc (b₀ + 1) m).card + 1))
        * ((θ⁻¹) ^ 2
          * (θ ^ (m - k) * E m + 5 / 2 * Mp + ∑ j ∈ Icc k m, δ j))
      = (κ * θ⁻¹) ^ 2
          * (2 * (κ * θ⁻¹) ^ (h + 2))
            ^ ((B ∩ Icc (b₀ + 1) m).card + 1)
        * (θ ^ (m - k) * E m + 5 / 2 * Mp + ∑ j ∈ Icc k m, δ j) := by
    ring
  linarith only [s1, s2, s3, s4, s5]

theorem weightedAssemble (hθpos : 0 < θ) (hθ1 : θ ≤ 1) (hθh : θ ^ h < 3 / 5)
    (hE : ∀ k, 0 ≤ E k) (hδ : ∀ k, 0 ≤ δ k) (hMp : 0 ≤ Mp) (hκ : 1 ≤ κ)
    (hmono : ∀ k, E k ≤ κ * E (k + 1)) {n m : ℤ} (B : Finset ℤ)
    (hwM : ∀ j, n ≤ j → j ≤ m → w j ≤ Mp)
    (hdecay : ∀ j, n ≤ j → j ≤ m → j ∉ B →
      E (j - h) ≤ θ ^ h * E j + w j + δ j) :
    ∀ k : ℤ, n ≤ k → k ≤ m →
      E k ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc k m).card + 1)
        * (θ ^ (m - k) * E m + 5 / 2 * Mp + ∑ j ∈ Icc k m, δ j) := by
  obtain ⟨hκ0, hinv0, hκθ, hκθ0, hLpow, hLmono, hδblk, hδ0, hXnn, hVnn, hVshift⟩ :=
    @weightedGoodRunAssembly_comparisonBounds1 (E) (δ) (θ) (κ) (Mp) (h) (hθpos) (hθ1) (hE) (hδ)
      (hMp) (hκ) (m)
  -- the strong downward induction on the distance to the top
  have key : ∀ T : ℕ, ∀ k : ℤ, n ≤ k → k ≤ m → (m - k).toNat ≤ T →
      E k ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc k m).card + 1)
        * (θ ^ (m - k) * E m + 5 / 2 * Mp + ∑ j ∈ Icc k m, δ j) := by
    intro T
    induction T with
    | zero =>
        intro k _ hkm hle
        have hkeq : k = m := by omega
        subst hkeq
        simp only [sub_self, zpow_zero, one_mul]
        exact weightedTopCase (hE k) (hLpow _) (by linarith only [hMp]) (hδ0 k)
    | succ T ih =>
        intro k hnk hkm hle
        rcases eq_or_lt_of_le hkm with hkeq | hklt
        · subst hkeq
          simp only [sub_self, zpow_zero, one_mul]
          exact weightedTopCase (hE k) (hLpow _) (by linarith only [hMp]) (hδ0 k)
        · by_cases hBe : (B ∩ Icc k m).Nonempty
          · obtain ⟨b₀, hb₀mem, hb₀min⟩ :
                ∃ b₀ ∈ B ∩ Icc k m, ∀ j ∈ B ∩ Icc k m, b₀ ≤ j :=
              ⟨(B ∩ Icc k m).min' hBe, Finset.min'_mem _ hBe,
                fun j hj => Finset.min'_le _ j hj⟩
            have hb₀k : k ≤ b₀ := (Finset.mem_Icc.1 (Finset.mem_inter.1 hb₀mem).2).1
            have hb₀m : b₀ ≤ m := (Finset.mem_Icc.1 (Finset.mem_inter.1 hb₀mem).2).2
            rcases eq_or_lt_of_le hb₀k with hbk | hbk
            · -- the bottom scale is bad: cross it and recurse
              have hcard : (B ∩ Icc (k + 1) m).card + 1 ≤ (B ∩ Icc k m).card  := @weightedGoodRunAssembly_estimate3 (n) (m) (B) (T) (k) (b₀) (hb₀mem) (hbk)
              have hih := ih (k + 1) (by omega) (by omega) (by omega)
              have hVs := hVshift k (k + 1) 0 1 le_rfl (by
                  rw [zpow_zero, one_mul, show m - (k + 1) = m - k - 1 from by ring,
                    zpow_sub_one₀ (ne_of_gt hθpos)]
                  ring) (by omega)
              rw [zpow_zero, one_mul] at hVs
              refine weightedCrossAbsorb (c := κ) hκ0
                (by linarith only [hLpow ((B ∩ Icc (k + 1) m).card + 1)]) (hVnn k)
                (hmono k) hih hVs ?_
              have hstep : κ * (θ⁻¹) ^ 1 * (2 * (κ * θ⁻¹) ^ (h + 2))
                    ^ ((B ∩ Icc (k + 1) m).card + 1)
                  ≤ (2 * (κ * θ⁻¹) ^ (h + 2))
                    * (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc (k + 1) m).card + 1) := by
                refine mul_le_mul_of_nonneg_right ?_
                  (by linarith only [hLpow ((B ∩ Icc (k + 1) m).card + 1)])
                have hp : (κ * θ⁻¹) ^ 1 ≤ (κ * θ⁻¹) ^ (h + 2) :=
                  pow_le_pow_right₀ hκθ (by omega)
                rw [pow_one] at hp
                rw [pow_one]
                linarith only [hp, hκθ]
              have hfold : (2 * (κ * θ⁻¹) ^ (h + 2))
                    * (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc (k + 1) m).card + 1)
                  ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc k m).card + 1) := by
                have hpp := hLmono ((B ∩ Icc (k + 1) m).card + 1 + 1)
                  ((B ∩ Icc k m).card + 1) (by omega)
                calc (2 * (κ * θ⁻¹) ^ (h + 2))
                      * (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc (k + 1) m).card + 1)
                    = (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc (k + 1) m).card + 1 + 1) := by
                      rw [pow_succ]; ring
                  _ ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc k m).card + 1) := hpp
              exact le_trans hstep hfold
            · -- a genuine good run `[k, b₀ − 1]`, then the bad scale `b₀`
              have hgd : ∀ j, k ≤ j → j ≤ b₀ - 1 → j ∉ B := by
                intro j hj1 hj2 hjB
                have hle' := hb₀min j (Finset.mem_inter.2 ⟨hjB, by
                  simp only [Finset.mem_Icc]
                  exact ⟨hj1, by omega⟩⟩)
                omega
              have hrun := weightedRunBound hθpos hθ1 hθh hE hδ hMp hκ hmono
                (a := k) (b := b₀ - 1) (by omega)
                (fun j hj1 hj2 => hwM j (by omega) (by omega))
                (fun j hj1 hj2 => hdecay j (by omega) (by omega) (hgd j hj1 hj2))
              have hP0 : (0 : ℝ) ≤ (κ * θ⁻¹) ^ h := pow_nonneg hκθ0 h
              rcases eq_or_lt_of_le hb₀m with hbm | hbm
              · -- the bad scale is the top scale
                have hY : θ ^ (b₀ - 1 - k) * E (b₀ - 1)
                    ≤ κ * θ⁻¹ * (θ ^ (m - k) * E m)  := @weightedGoodRunAssembly_estimate1 (E) (θ) (κ) (h) (hθpos) (hmono) (m) (hinv0) (k) (b₀) (hbm)
                refine weightedRunAbsorb hP0 hκθ (by linarith only [hMp])
                  (Finset.sum_nonneg fun j _ => hδ j) (hVnn k) hrun hY ?_ ?_
                · have hd := hδblk k (b₀ - 1) (by omega)
                  linarith only [hd]
                · have hp : (κ * θ⁻¹) ^ h * (κ * θ⁻¹) ^ 1
                      ≤ (κ * θ⁻¹) ^ (h + 2) := by
                    rw [← pow_add]
                    exact pow_le_pow_right₀ hκθ (by omega)
                  have hL : (κ * θ⁻¹) ^ (h + 2)
                      ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc k m).card + 1) := by
                    have h1 : (κ * θ⁻¹) ^ (h + 2) ≤ 2 * (κ * θ⁻¹) ^ (h + 2) := by
                      have := one_le_pow₀ (n := h + 2) hκθ
                      linarith only [this]
                    have h2 : (2 * (κ * θ⁻¹) ^ (h + 2)) ^ 1
                        ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc k m).card + 1) :=
                      hLmono 1 _ (by omega)
                    rw [pow_one] at h2
                    linarith only [h1, h2]
                  rw [pow_one] at hp
                  linarith only [hp, hL]
              · -- cross `b₀` and recurse above it
                have hcard : (B ∩ Icc (b₀ + 1) m).card + 1 ≤ (B ∩ Icc k m).card := by
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
                have hih := ih (b₀ + 1) (by omega) (by omega) (by omega)
                have hVs := hVshift k (b₀ + 1) (b₀ - 1 - k) 2 (by omega) (by
                    rw [← zpow_add₀ (ne_of_gt hθpos),
                      show b₀ - 1 - k + (m - (b₀ + 1)) = m - k - 1 - 1 from by ring,
                      zpow_sub_one₀ (ne_of_gt hθpos),
                      zpow_sub_one₀ (ne_of_gt hθpos)]
                    ring) (by omega)
                have hW'1 : (1 : ℝ)
                    ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc (b₀ + 1) m).card + 1) :=
                  hLpow _
                have hW'0 : (0 : ℝ)
                    ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc (b₀ + 1) m).card + 1) := by
                  linarith only [hW'1]
                have hκθsq : (1 : ℝ) ≤ (κ * θ⁻¹) ^ 2 := one_le_pow₀ hκθ
                have hcross2 : E (b₀ - 1) ≤ κ * (κ * E (b₀ + 1)) := by
                  have h1 : E (b₀ - 1) ≤ κ * E b₀ := by
                    have hb := hmono (b₀ - 1)
                    rw [sub_add_cancel] at hb
                    exact hb
                  have h3 : κ * E b₀ ≤ κ * (κ * E (b₀ + 1)) :=
                    mul_le_mul_of_nonneg_left (hmono b₀) hκ0
                  linarith only [h1, h3]
                have hY : θ ^ (b₀ - 1 - k) * E (b₀ - 1)
                    ≤ (κ * θ⁻¹) ^ 2
                        * (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc (b₀ + 1) m).card + 1)
                      * (θ ^ (m - k) * E m + 5 / 2 * Mp + ∑ j ∈ Icc k m, δ j)  := @weightedGoodRunAssembly_estimate4 (E) (δ) (θ) (κ) (Mp) (h) (hθpos) (m) (B) (hκ0) (k) (b₀) (hih) (hVs) (hW'0) (hcross2)
                refine weightedRunAbsorbInner hP0 ?_ (hVnn k) hrun hY ?_ ?_
                · have hm := mul_le_mul_of_nonneg_left hW'1
                    (by linarith only [hκθsq] : (0 : ℝ) ≤ (κ * θ⁻¹) ^ 2)
                  linarith only [hm, hκθsq]
                · have hd := hδblk k (b₀ - 1) (by omega)
                  linarith only [hd, hXnn k]
                · have hid : (κ * θ⁻¹) ^ h * (2 * ((κ * θ⁻¹) ^ 2
                        * (2 * (κ * θ⁻¹) ^ (h + 2))
                          ^ ((B ∩ Icc (b₀ + 1) m).card + 1)))
                      = 2 * (κ * θ⁻¹) ^ (h + 2)
                        * (2 * (κ * θ⁻¹) ^ (h + 2))
                          ^ ((B ∩ Icc (b₀ + 1) m).card + 1) := by
                    rw [pow_add]
                    ring
                  rw [hid]
                  calc 2 * (κ * θ⁻¹) ^ (h + 2)
                        * (2 * (κ * θ⁻¹) ^ (h + 2))
                          ^ ((B ∩ Icc (b₀ + 1) m).card + 1)
                      = (2 * (κ * θ⁻¹) ^ (h + 2))
                          ^ ((B ∩ Icc (b₀ + 1) m).card + 1 + 1) := by
                        rw [pow_succ]; ring
                    _ ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc k m).card + 1) :=
                        hLmono _ _ (by omega)
          · -- no bad scale at or above `k`: one good run to the top
            have hcard0 : (B ∩ Icc k m).card = 0 :=
              Finset.card_eq_zero.2 (Finset.not_nonempty_iff_eq_empty.1 hBe)
            have hrun := weightedRunBound hθpos hθ1 hθh hE hδ hMp hκ hmono
              (a := k) (b := m) hkm
              (fun j hj1 hj2 => hwM j (by omega) hj2)
              (fun j hj1 hj2 => hdecay j (by omega) hj2 (by
                intro hjB
                exact hBe ⟨j, Finset.mem_inter.2 ⟨hjB, by
                  simp only [Finset.mem_Icc]
                  exact ⟨hj1, hj2⟩⟩⟩))
            have hpref : (κ * θ⁻¹) ^ h
                ≤ (2 * (κ * θ⁻¹) ^ (h + 2)) ^ ((B ∩ Icc k m).card + 1)  := @weightedGoodRunAssembly_estimate2 (θ) (κ) (h) (n) (m) (B) (hκθ) (hLmono) (T) (k) (hcard0)
            exact le_trans hrun (mul_le_mul_of_nonneg_right hpref (hVnn k))
  intro k hnk hkm
  exact key (m - n).toNat k hnk hkm (by omega)

end Assembly

end

end Algsuperdiff.Section4.Provider.ExcessDecay
