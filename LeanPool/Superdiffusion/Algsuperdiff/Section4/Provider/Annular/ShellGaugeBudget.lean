/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.ClauseOneHonestEvent
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.Annular.UglyLatticeChain

/-!
# ShellGaugeBudget

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The `𝒢₁` gradient-gauge budget of Step 2, at the honest amplitude

ABK26, Section 4.1, `p.mathcalE.annular.decomp` Step 2.  The manuscript's second
good-event budget reads

```
σ_{n−2}^{-1} 3^{2n} sup_{L ≥ m} ‖∇(k_L − k_{n−2})‖_{W^{1,∞}(z+□_n)} 1_{𝒢}
  ≤ C 3^{s(m−n)/4} ,
```

and is the `hshell` slot of `Ugly.uglyJEstimate_of_sensitivity`,
`UglyChain.exists_responseJ_ugly_estimate` and
`UglyLatticeChain.exists_uglyJEstimate_lattice_cube`.  This module produces the
gauge half of it — everything except the `σ` prefactor — from membership in the
frozen event `Support.eventG1 M m s T`, at an **explicit numeral** constant.

## The decay the proved layer bound throws away

`EventBudgets.three_rpow_mul_shellW1InfGradNorm_translate_le_shellBlockLatticeReal`
bounds the weighted layer term by `9 A(l)` uniformly in `l`.  That is enough
for Step 3's Cauchy--Schwarz-with-multiplicity, but **not** for Step 2: summing
a uniform bound over the `(m−n)+2` layers costs a factor `(m−n)+2`, which no
fixed power of `3^{s(m−n)/4}` absorbs at a constant independent of `s` (the
optimum is `s^{-1/2}`).  The manuscript avoids this — keeps the factor
`3^{(1−γ)(n−k)}` through the cube comparison and only then applies
Cauchy--Schwarz.  `three_rpow_gauge_weight_decay_le` below is that sharper
weight arithmetic; it retains the geometric decay and the layer sum is then
bounded by an absolute constant, with **no `s`-dependence anywhere**.

## What is proved

* `three_rpow_gauge_weight_decay_le` — the sharpened Step-2 weight arithmetic,
  at the constant `3` (both branches are tight at `l = n − 1`).
* `three_rpow_mul_shellW1InfGradNorm_translate_le_decay` — the per-layer bound
  with the decay retained.
* `sum_three_rpow_decay_le` — the layer sum of the decay weights is at most `8`.
* `shellBlockLatticeReal_le_of_eventG1` — the **single-block** reading of `𝒢₁ᵇ`:
  every shell block in the layer range is at most `2 T 3^{s(m−n)/8}`.
* `shellGaugeHead_le_of_eventG1` / `shellGaugeTail_le_of_eventG1` /
  `shellGauge_le_of_eventG1` — the head block `(n−2, m]`, the tail block
  `(m, L]` and their sum.
-/

namespace Algsuperdiff.Section4.Provider.Annular

open HCPolySupport HCPolySupport.Book HCPolySupport.Book.Ch02
open Algsuperdiff.Section3
open Algsuperdiff.Frozen.Assumptions

noncomputable section

variable {d : ℕ}

/-! ## Part A -- the sharpened weight arithmetic, over abstract reals -/

private theorem three_rpow_mono' {x y : ℝ} (h : x ≤ y) : (3 : ℝ) ^ x ≤ (3 : ℝ) ^ y :=
  Real.rpow_le_rpow_of_exponent_le (by norm_num) h

private theorem three_mul_rpow (a : ℝ) : (3 : ℝ) * (3 : ℝ) ^ a = (3 : ℝ) ^ (1 + a) := by
  rw [Real.rpow_add (by norm_num : (0 : ℝ) < 3) 1 a, Real.rpow_one]

private theorem three_rpow_collect (a b : ℝ) :
    (3 : ℝ) * ((3 : ℝ) ^ a * (3 : ℝ) ^ b) = (3 : ℝ) ^ (1 + (a + b)) := by
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3) a b, three_mul_rpow]

/-- **The Step-2 weight arithmetic with the shell decay retained**.  For a layer
index `ll` at or above `nn − 1` — the honest range of the layer sum `(n−2, m]`
— the cube-comparison factor `max(1, 3^{ll−nn})` is paid for by the constant
`3` *and* the geometric factor `3^{(1−gam)(nn−ll)}` is kept:

```
3^{(2−gam) nn} max(1, 3^{ll−nn}) ≤ 3 · 3^{(1−gam)(nn−ll)} · 3^{(2−gam) ll} .
```

The second branch is an identity up to the constant; the first branch is tight
at `ll = nn − 1`.  Neither branch uses a bound on `gam`. -/
theorem three_rpow_gauge_weight_decay_le {gam nn ll : ℝ} (hl : nn - 1 ≤ ll) :
    (3 : ℝ) ^ ((2 - gam) * nn) * max 1 ((3 : ℝ) ^ (ll - nn))
      ≤ 3 * ((3 : ℝ) ^ ((1 - gam) * (nn - ll)) * (3 : ℝ) ^ ((2 - gam) * ll)) := by
  rw [three_rpow_collect]
  rcases max_cases (1 : ℝ) ((3 : ℝ) ^ (ll - nn)) with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he]
  · rw [mul_one]
    refine three_rpow_mono' ?_
    have hid : 1 + ((1 - gam) * (nn - ll) + (2 - gam) * ll) - (2 - gam) * nn
        = 1 - (nn - ll) := by ring
    linarith only [hid, hl]
  · rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    refine three_rpow_mono' ?_
    have hid : 1 + ((1 - gam) * (nn - ll) + (2 - gam) * ll)
        - ((2 - gam) * nn + (ll - nn)) = 1 := by ring
    linarith only [hid]

/-! ## Part B -- the per-layer bound at the pinned lattice family -/

/-- **The per-shell atom bound with the decay retained.**  On the cube
`z + □_n` with `z` a scale-`n` lattice point of `□_m`, the weighted
`W^{1,∞}` gauge of the shell `j_l` is at most `3 · 3^{(1−γ)(n−l)} A(l)`, with
`A = shellBlockLatticeReal` the pinned lattice family of the frozen clause-(i)
fourth term.  This is the sharpening of
`EventBudgets.three_rpow_mul_shellW1InfGradNorm_translate_le_shellBlockLatticeReal`
that Step 2 needs. -/
theorem three_rpow_mul_shellW1InfGradNorm_translate_le_decay
    (M : ABKModel d) {m n l : ℤ} (hnm : n ≤ m) (hln : n - 1 ≤ l) (hlm : l ≤ m)
    (omega : Cutoff.CutoffSample d) {v : Fin d → ℤ}
    (hv : v ∈ Support.latticeCubeSet d n m) :
    (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l))
      ≤ 3 * ((3 : ℝ) ^ ((1 - M.gamma) * ((n : ℝ) - (l : ℝ)))
          * shellBlockLatticeReal M m omega l) := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) := by positivity
  have hL0 : 0 ≤ shellW2InfLatticeMaxOf m l (omega.1 l) :=
    shellW2InfLatticeMaxOf_nonneg m l (omega.1 l)
  have hgauge :=
    shellW1InfGradNorm_translate_le_shellW2InfLatticeMaxOf hnm hlm hv (omega.1 l)
  have hzpow : ((3 : ℝ) ^ (l - n) : ℝ) = (3 : ℝ) ^ ((l : ℝ) - (n : ℝ)) := by
    rw [show ((l : ℝ)) - (n : ℝ) = (((l - n : ℤ)) : ℝ) from by push_cast; ring,
      Real.rpow_intCast]
  rw [hzpow] at hgauge
  have hstep := mul_le_mul_of_nonneg_left hgauge hpos.le
  have hlR : (n : ℝ) - 1 ≤ (l : ℝ) := by
    have hz : ((n - 1 : ℤ) : ℝ) ≤ ((l : ℤ) : ℝ) := by exact_mod_cast hln
    push_cast at hz
    linarith only [hz]
  have hweight := three_rpow_gauge_weight_decay_le (gam := M.gamma) (nn := (n : ℝ))
    (ll := (l : ℝ)) hlR
  have hdef : shellBlockLatticeReal M m omega l
      = (3 : ℝ) ^ ((2 - M.gamma) * (l : ℝ)) * shellW2InfLatticeMaxOf m l (omega.1 l) :=
    rfl
  refine hstep.trans ?_
  rw [hdef]
  calc (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        (max 1 ((3 : ℝ) ^ ((l : ℝ) - (n : ℝ))) * shellW2InfLatticeMaxOf m l (omega.1 l))
      = ((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) * max 1 ((3 : ℝ) ^ ((l : ℝ) - (n : ℝ))))
          * shellW2InfLatticeMaxOf m l (omega.1 l) := by ring
    _ ≤ (3 * ((3 : ℝ) ^ ((1 - M.gamma) * ((n : ℝ) - (l : ℝ)))
          * (3 : ℝ) ^ ((2 - M.gamma) * (l : ℝ))))
          * shellW2InfLatticeMaxOf m l (omega.1 l) :=
        mul_le_mul_of_nonneg_right hweight hL0
    _ = 3 * ((3 : ℝ) ^ ((1 - M.gamma) * ((n : ℝ) - (l : ℝ)))
          * ((3 : ℝ) ^ ((2 - M.gamma) * (l : ℝ))
            * shellW2InfLatticeMaxOf m l (omega.1 l))) := by ring

/-! ## Part C -- the layer sum of the decay weights -/

private theorem five_thirds_le_three_rpow_three_quarters :
    (5 / 3 : ℝ) ≤ (3 : ℝ) ^ ((3 : ℝ) / 4) := by
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((3 : ℝ) / 4) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hfour : ((3 : ℝ) ^ ((3 : ℝ) / 4)) ^ (4 : ℕ) = 27 := by
    rw [← Real.rpow_natCast ((3 : ℝ) ^ ((3 : ℝ) / 4)) 4,
      ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    norm_num
  refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) hpos.le ?_
  rw [hfour]
  norm_num

private theorem three_rpow_neg_three_quarters_le : (3 : ℝ) ^ (-((3 : ℝ) / 4)) ≤ 3 / 5 := by
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3)]
  have h := inv_anti₀ (by norm_num : (0 : ℝ) < 5 / 3)
    five_thirds_le_three_rpow_three_quarters
  calc ((3 : ℝ) ^ ((3 : ℝ) / 4))⁻¹ ≤ ((5 : ℝ) / 3)⁻¹ := h
    _ = 3 / 5 := by norm_num

private theorem sum_geom_three_quarter_le (N : ℕ) :
    ∑ u ∈ Finset.range N, ((3 : ℝ) ^ (-((3 : ℝ) / 4))) ^ u ≤ 5 / 2 := by
  set r : ℝ := (3 : ℝ) ^ (-((3 : ℝ) / 4)) with hr
  have hr0 : (0 : ℝ) ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr35 : r ≤ 3 / 5 := three_rpow_neg_three_quarters_le
  have hr1 : r < 1 := lt_of_le_of_lt hr35 (by norm_num)
  have hsum : Summable fun u : ℕ => r ^ u := summable_geometric_of_lt_one hr0 hr1
  have hpart : ∑ u ∈ Finset.range N, r ^ u ≤ ∑' u : ℕ, r ^ u :=
    Summable.sum_le_tsum _ (fun u _ => pow_nonneg hr0 u) hsum
  have hval : ∑' u : ℕ, r ^ u = (1 - r)⁻¹ := tsum_geometric_of_lt_one hr0 hr1
  rw [hval] at hpart
  refine hpart.trans ?_
  have hden : (2 : ℝ) / 5 ≤ 1 - r := by linarith only [hr35]
  have := inv_anti₀ (by norm_num : (0 : ℝ) < 2 / 5) hden
  calc (1 - r)⁻¹ ≤ ((2 : ℝ) / 5)⁻¹ := this
    _ = 5 / 2 := by norm_num

/-- **The layer sum of the decay weights is bounded by an absolute constant.**
Over the honest layer range `l ∈ [n−1, m]` the geometric factors of
`three_rpow_gauge_weight_decay_le` sum to at most `8`, uniformly in `n`, `m` and
in `γ ≤ 1/4`.  This is the step that keeps the Step-2 budget free of `s`. -/
theorem sum_three_rpow_decay_le (M : ABKModel d) {n m : ℤ} (hnm : n ≤ m) :
    ∑ l ∈ Finset.Icc (n - 1) m,
        (3 : ℝ) ^ ((1 - M.gamma) * ((n : ℝ) - (l : ℝ))) ≤ 8 := by
  classical
  have hg14 : M.gamma ≤ 1 / 4 := M.shellPrefix.gamma_le_quarter
  have hg0 : (0 : ℝ) < M.gamma := M.shellPrefix.gamma_pos
  set N : ℕ := (m - n + 2).toNat with hN
  have himg : Finset.Icc (n - 1) m
      = (Finset.range N).image fun u : ℕ => (n - 1) + (u : ℤ) := by
    ext l
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨(l - (n - 1)).toNat, by omega, by omega⟩
    · rintro ⟨u, hu, rfl⟩
      omega
  have hinj : Set.InjOn (fun u : ℕ => (n - 1) + (u : ℤ))
      (↑(Finset.range N) : Set ℕ) := by
    intro x _hx y _hy hxy
    have hxy' : (n - 1) + (x : ℤ) = (n - 1) + (y : ℤ) := hxy
    omega
  rw [himg, Finset.sum_image hinj]
  have hterm : ∀ u ∈ Finset.range N,
      (3 : ℝ) ^ ((1 - M.gamma) * ((n : ℝ) - (((n - 1) + (u : ℤ) : ℤ) : ℝ)))
        ≤ 3 * ((3 : ℝ) ^ (-((3 : ℝ) / 4))) ^ u := by
    intro u _hu
    have hcast : ((n : ℝ) - (((n - 1) + (u : ℤ) : ℤ) : ℝ)) = 1 - (u : ℝ) := by
      push_cast
      ring
    rw [hcast]
    have hpow : ((3 : ℝ) ^ (-((3 : ℝ) / 4))) ^ u
        = (3 : ℝ) ^ (-((3 : ℝ) / 4) * (u : ℝ)) := by
      rw [← Real.rpow_natCast ((3 : ℝ) ^ (-((3 : ℝ) / 4))) u,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [hpow, three_mul_rpow]
    refine three_rpow_mono' ?_
    have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
    have hprod : (3 : ℝ) / 4 * (u : ℝ) ≤ (1 - M.gamma) * (u : ℝ) :=
      mul_le_mul_of_nonneg_right (by linarith only [hg14]) hu0
    have hid : (1 - M.gamma) * (1 - (u : ℝ))
        = (1 - M.gamma) - (1 - M.gamma) * (u : ℝ) := by ring
    have hid2 : (1 : ℝ) + -((3 : ℝ) / 4) * (u : ℝ) = 1 - (3 : ℝ) / 4 * (u : ℝ) := by
      ring
    rw [hid, hid2]
    linarith only [hprod, hg0]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  have hgeo := sum_geom_three_quarter_le N
  linarith only [hgeo]

/-! ## Part D -- the single-block reading of `𝒢₁ᵇ` -/

private theorem three_rpow_sq (a : ℝ) : ((3 : ℝ) ^ a) ^ (2 : ℕ) = (3 : ℝ) ^ (a * 2) := by
  rw [← Real.rpow_natCast ((3 : ℝ) ^ a) 2, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

/-- **The single-block reading of `𝒢₁ᵇ`.**  On `𝒢₁(m; s, T)` every shell block
in the layer range `[n−1, m]` of the annulus at scale `n` is at most
`2 T 3^{s(m−n)/8}`.  Unlike `EventReading.shellPartialSum_le_of_eventG1` this is
a bound on a *single* block, at the *first* power, which is what the Step-2 layer
sum consumes. -/
theorem shellBlockLatticeReal_le_of_eventG1 (M : ABKModel d) (m : ℤ) {s T : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hT : 0 ≤ T) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG1 M m s T) {n l : ℤ} (hnm : n ≤ m)
    (hln : n - 1 ≤ l) (hlm : l ≤ m) :
    shellBlockLatticeReal M m omega l
      ≤ 2 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) := by
  classical
  have hpart := shellPartialSum_le_of_eventG1 M m hs0 hT homega n hnm
  have hmem : (m - l).toNat ∈ Finset.range ((m - n).toNat + 2) := by
    rw [Finset.mem_range]
    omega
  have hidx : m - (((m - l).toNat : ℕ) : ℤ) = l := by omega
  have hsingle0 : shellBlockLatticeReal M m omega (m - (((m - l).toNat : ℕ) : ℤ)) ^ 2
      ≤ ∑ v ∈ Finset.range ((m - n).toNat + 2),
          shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2 :=
    Finset.single_le_sum
      (f := fun v : ℕ => shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2)
      (fun i _hi => sq_nonneg _) hmem
  rw [hidx] at hsingle0
  have hsingle : shellBlockLatticeReal M m omega l ^ 2
      ≤ ∑ v ∈ Finset.range ((m - n).toNat + 2),
          shellBlockLatticeReal M m omega (m - (v : ℤ)) ^ 2 := hsingle0
  have hq0 : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ m - n := by omega
    exact_mod_cast this
  have h34 : (3 : ℝ) ^ (s / 4) ≤ 4 := by
    calc (3 : ℝ) ^ (s / 4) ≤ (3 : ℝ) ^ (1 : ℝ) := three_rpow_mono' (by linarith only [hs1])
      _ = 3 := Real.rpow_one 3
      _ ≤ 4 := by norm_num
  have hw0 : (0 : ℝ) ≤ (3 : ℝ) ^ (s / 4 * ((m - n : ℤ) : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hT2 : (0 : ℝ) ≤ T ^ 2 := sq_nonneg T
  have hchain : shellBlockLatticeReal M m omega l ^ 2
      ≤ (2 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ))) ^ 2 := by
    have hstep1 : ((3 : ℝ) ^ (s / 4) * T ^ 2) * (3 : ℝ) ^ (s / 4 * ((m - n : ℤ) : ℝ))
        ≤ (4 * T ^ 2) * (3 : ℝ) ^ (s / 4 * ((m - n : ℤ) : ℝ)) := by
      refine mul_le_mul_of_nonneg_right ?_ hw0
      exact mul_le_mul_of_nonneg_right h34 hT2
    have hexp : (2 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ))) ^ 2
        = (4 * T ^ 2) * (3 : ℝ) ^ (s / 4 * ((m - n : ℤ) : ℝ)) := by
      have hsq := three_rpow_sq (s / 8 * ((m - n : ℤ) : ℝ))
      have hval : s / 8 * ((m - n : ℤ) : ℝ) * 2 = s / 4 * ((m - n : ℤ) : ℝ) := by ring
      rw [hval] at hsq
      calc (2 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ))) ^ 2
          = 4 * T ^ 2 * ((3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ))) ^ (2 : ℕ) := by ring
        _ = (4 * T ^ 2) * (3 : ℝ) ^ (s / 4 * ((m - n : ℤ) : ℝ)) := by rw [hsq]
    rw [hexp]
    linarith only [hsingle, hpart, hstep1]
  have hrhs0 : (0 : ℝ) ≤ 2 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) := by
    have : (0 : ℝ) ≤ (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    positivity
  exact le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hrhs0 hchain

/-! ## Part E -- the head block `(n−2, m]` -/

/-- **The head block of the Step-2 gauge budget.**  On `𝒢₁(m; s, T)` the weighted
`W^{1,∞}` gauge of `∇(k_m − k_{n−2})` on the lattice cube `z + □_n` is at most
`48 T 3^{s(m−n)/8}`.  The constant is absolute: `3` from the weight arithmetic,
`8` from the layer sum of the decay weights and `2` from the single-block reading
of `𝒢₁ᵇ`. -/
theorem shellGaugeHead_le_of_eventG1 (M : ABKModel d) (m : ℤ) {s T : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hT : 0 ≤ T) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG1 M m s T) {n : ℤ} (hnm : n ≤ m)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m) :
    (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 (n - 2) m))
      ≤ 48 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) := by
  classical
  have hIoc : Finset.Ioc (n - 2) m = Finset.Icc (n - 1) m := by
    ext l
    simp only [Finset.mem_Ioc, Finset.mem_Icc]
    omega
  have htri := Support.shellW1InfGradNorm_translate_shellIncrement_le n v omega.1 (n - 2) m
  rw [hIoc] at htri
  have hpos : (0 : ℝ) < (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) := by positivity
  have hB0 : (0 : ℝ) ≤ 2 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) := by
    have h1 : (0 : ℝ) ≤ (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) :=
      Real.rpow_nonneg (by norm_num) _
    positivity
  have hterm : ∀ l ∈ Finset.Icc (n - 1) m,
      (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
          Support.shellW1InfGradNorm n
            (ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l))
        ≤ 3 * ((3 : ℝ) ^ ((1 - M.gamma) * ((n : ℝ) - (l : ℝ)))
            * (2 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)))) := by
    intro l hl
    rw [Finset.mem_Icc] at hl
    refine (three_rpow_mul_shellW1InfGradNorm_translate_le_decay M hnm hl.1 hl.2
      omega hv).trans ?_
    have hblock := shellBlockLatticeReal_le_of_eventG1 M m hs0 hs1 hT homega hnm
      hl.1 hl.2
    have hw : (0 : ℝ) ≤ (3 : ℝ) ^ ((1 - M.gamma) * ((n : ℝ) - (l : ℝ))) :=
      Real.rpow_nonneg (by norm_num) _
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hblock hw)
      (by norm_num)
  calc (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 (n - 2) m))
      ≤ (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
          ∑ l ∈ Finset.Icc (n - 1) m,
            Support.shellW1InfGradNorm n
              (ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l)) :=
        mul_le_mul_of_nonneg_left htri hpos.le
    _ = ∑ l ∈ Finset.Icc (n - 1) m,
          (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
            Support.shellW1InfGradNorm n
              (ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l)) :=
        Finset.mul_sum _ _ _
    _ ≤ ∑ l ∈ Finset.Icc (n - 1) m,
          3 * ((3 : ℝ) ^ ((1 - M.gamma) * ((n : ℝ) - (l : ℝ)))
            * (2 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)))) :=
        Finset.sum_le_sum hterm
    _ = (3 * (2 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ))))
          * ∑ l ∈ Finset.Icc (n - 1) m,
              (3 : ℝ) ^ ((1 - M.gamma) * ((n : ℝ) - (l : ℝ))) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
    _ ≤ (3 * (2 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)))) * 8 :=
        mul_le_mul_of_nonneg_left (sum_three_rpow_decay_le M hnm) (by linarith only [hB0])
    _ = 48 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) := by ring

/-! ## Part F -- the tail block `(m, L]` and the raw tail summability -/

/-- The weighted layer sum over `(m, b]` sits below the full `𝒢₁ᵃ` tail sum,
i.e. below `√(gradTailSq)`.  This is the form the fifth (`gradM`) slot of
`e.ugly.estimate.for.J` consumes. -/
theorem sum_gradTailFam_Ioc_le_tsum (M : ABKModel d) (m : ℤ) {s T : ℝ}
    {omega : Cutoff.CutoffSample d} (homega : omega ∈ Support.eventG1 M m s T)
    (b : ℤ) :
    (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ)) *
        ∑ l ∈ Finset.Ioc m b, Support.shellW1InfGradNorm m (omega.1 l)
      ≤ ∑' k : {k : ℤ // m ≤ k},
          (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
            * Support.shellW1InfGradNorm m (omega.1 k.1) := by
  classical
  have hsum := summable_gradTail_of_eventG1 M m homega
  have hW0 : ∀ l : ℤ, (0 : ℝ) ≤ (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
      * Support.shellW1InfGradNorm m (omega.1 l) :=
    fun l => mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (Support.shellW1InfGradNorm_nonneg m _)
  have hle := Summable.sum_le_tsum ((Finset.Ioc m b).subtype fun k : ℤ => m ≤ k)
    (fun i _ => hW0 i.1) hsum
  rw [Finset.sum_subtype_eq_sum_filter
      (f := fun l : ℤ => (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
        * Support.shellW1InfGradNorm m (omega.1 l)),
    Finset.filter_true_of_mem
      (fun l hl => by rw [Finset.mem_Ioc] at hl; omega)] at hle
  rwa [← Finset.mul_sum] at hle

/-- **The tail block of the Step-2 gauge budget.**  The layers above `m` are
transported to scale `m` by the cross-scale comparison and then absorbed by the
first component of `𝒢₁`, with constant `1`.  No relation between `m` and `L` is
needed: for `L < m` the layer range is empty. -/
theorem shellGaugeTail_le_tsum_of_eventG1 (M : ABKModel d) (m : ℤ) {s T : ℝ}
    {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG1 M m s T) {n L : ℤ} (hnm : n ≤ m)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m) :
    (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 m L))
      ≤ ∑' k : {k : ℤ // m ≤ k},
          (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
            * Support.shellW1InfGradNorm m (omega.1 k.1) := by
  classical
  have hg1 : M.gamma ≤ 1 := by
    have := M.shellPrefix.gamma_le_quarter
    linarith only [this]
  have hnmR : ((n : ℝ) ≤ (m : ℝ)) := by exact_mod_cast hnm
  have hW0 : ∀ l : ℤ, (0 : ℝ) ≤ Support.shellW1InfGradNorm m (omega.1 l) :=
    fun l => Support.shellW1InfGradNorm_nonneg m _
  have hpos : (0 : ℝ) ≤ (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have h1 := Support.shellW1InfGradNorm_translate_shellIncrement_le n v omega.1 m L
  have h2 : ∑ l ∈ Finset.Ioc m L,
      Support.shellW1InfGradNorm n
        (ShellField.translate (Support.triadicLatticePoint n v) (omega.1 l)) ≤
      (3 : ℝ) ^ (m - n) * ∑ l ∈ Finset.Ioc m L,
        Support.shellW1InfGradNorm m (omega.1 l) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun l _ =>
      shellW1InfGradNorm_translate_le_zpow_mul hnm hv (omega.1 l)
  have h3 : (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) * ((3 : ℝ) ^ (m - n))
      ≤ (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ)) := by
    have hz : ((3 : ℝ) ^ (m - n) : ℝ) = (3 : ℝ) ^ (((m - n : ℤ)) : ℝ) := by
      rw [Real.rpow_intCast]
    rw [hz, ← Real.rpow_add (by norm_num : (0 : ℝ) < 3)]
    refine three_rpow_mono' ?_
    have hd : (0 : ℝ) ≤ (1 - M.gamma) * ((m : ℝ) - (n : ℝ)) :=
      mul_nonneg (by linarith only [hg1]) (by linarith only [hnmR])
    push_cast
    linarith only [hd]
  calc (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 m L))
      ≤ (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
          ((3 : ℝ) ^ (m - n) * ∑ l ∈ Finset.Ioc m L,
            Support.shellW1InfGradNorm m (omega.1 l)) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) hpos
    _ = ((3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) * (3 : ℝ) ^ (m - n)) *
          ∑ l ∈ Finset.Ioc m L, Support.shellW1InfGradNorm m (omega.1 l) := by ring
    _ ≤ (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ)) *
          ∑ l ∈ Finset.Ioc m L, Support.shellW1InfGradNorm m (omega.1 l) :=
        mul_le_mul_of_nonneg_right h3 (Finset.sum_nonneg fun l _ => hW0 l)
    _ ≤ ∑' k : {k : ℤ // m ≤ k},
          (3 : ℝ) ^ ((2 - M.gamma) * (m : ℝ))
            * Support.shellW1InfGradNorm m (omega.1 k.1) :=
        sum_gradTailFam_Ioc_le_tsum M m homega L

/-- **The tail block of the Step-2 gauge budget**, against the event threshold. -/
theorem shellGaugeTail_le_of_eventG1 (M : ABKModel d) (m : ℤ) {s T : ℝ}
    (hT : 0 ≤ T) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG1 M m s T) {n L : ℤ} (hnm : n ≤ m)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m) :
    (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 m L)) ≤ T :=
  (shellGaugeTail_le_tsum_of_eventG1 M m homega (L := L) hnm hv).trans
    (tsum_gradTail_le_of_eventG1 M m hT homega)

/-! ## Part G -- the full Step-2 gauge bound -/

/-- **The Step-2 gauge budget, gauge half.**  On `𝒢₁(m; s, T)`, for every
`L ≥ m` and every scale-`n` lattice point of `□_m`,

```
3^{(2−γ)n} ‖∇(k_L − k_{n−2})‖_{W^{1,∞}(z+□_n)} ≤ 49 T 3^{s(m−n)/8} .
```

The constant `49 = 48 + 1` is absolute: no `s`, no `γ`, no `c⋆`, no dimension. -/
theorem shellGauge_le_of_eventG1 (M : ABKModel d) (m : ℤ) {s T : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hT : 0 ≤ T) {omega : Cutoff.CutoffSample d}
    (homega : omega ∈ Support.eventG1 M m s T) {n L : ℤ} (hnm : n ≤ m) (hmL : m ≤ L)
    {v : Fin d → ℤ} (hv : v ∈ Support.latticeCubeSet d n m) :
    (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) *
        Support.shellW1InfGradNorm n
          (ShellField.translate (Support.triadicLatticePoint n v)
            (Provider.Stream.shellIncrement omega.1 (n - 2) L))
      ≤ 49 * T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) := by
  have hpos : (0 : ℝ) ≤ (3 : ℝ) ^ ((2 - M.gamma) * (n : ℝ)) :=
    Real.rpow_nonneg (by norm_num) _
  have hq0 : (0 : ℝ) ≤ ((m - n : ℤ) : ℝ) := by
    have : (0 : ℤ) ≤ m - n := by omega
    exact_mod_cast this
  have hone : (1 : ℝ) ≤ (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) := by
    have h0 : (0 : ℝ) ≤ s / 8 * ((m - n : ℤ) : ℝ) :=
      mul_nonneg (by linarith only [hs0]) hq0
    calc (1 : ℝ) = (3 : ℝ) ^ (0 : ℝ) := (Real.rpow_zero 3).symm
      _ ≤ (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) := three_rpow_mono' h0
  have hsplit := shellW1InfGradNorm_translate_shellIncrement_add_le n v omega.1
    (by omega : n - 2 ≤ m) hmL
  have hhead := shellGaugeHead_le_of_eventG1 M m hs0 hs1 hT homega hnm hv
  have htail := shellGaugeTail_le_of_eventG1 M m hT homega (L := L) hnm hv
  have hTle : T ≤ T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) := by
    calc T = T * 1 := (mul_one T).symm
      _ ≤ T * (3 : ℝ) ^ (s / 8 * ((m - n : ℤ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hone hT
  have hstep := mul_le_mul_of_nonneg_left hsplit hpos
  rw [mul_add] at hstep
  linarith only [hstep, hhead, htail, hTle]

end

end Algsuperdiff.Section4.Provider.Annular
