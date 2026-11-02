/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.IndicatorDensity

/-!
# IndicatorDensityTails

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Rate shaping for the indicator-density tails

ABK26, §4.1.  `IndicatorDensity.lean` delivers the Appendix-D output at
concentration's *native* rate `exp(-(s p θ)/(16 r)·(M+1))` and only for windows
of length `M ≥ r`.  Two genuine steps separate that from the shape the downstream
minimal-scale layer consumes, namely

```
∀ n : ℕ, P [ θ < density of bad scales of `Ev` over the window {0,…,n} ]
           ≤ exp(-c₁ n) / Q ,
```

and both are proved here over an abstract probability space.

1. **The rate conversion.**  `exp(-a(n+1)) ≤ exp(-c₁ n)/Q` whenever `a ≥ c₁`
   and `a ≥ log Q`, where `a = s p θ/(16 r)` — the paper's "by taking `K(d)`
   larger, if necessary" at the end of each ratio-lemma proof.  The prefactor
   `Q ≥ 1` is a parameter: `Q = 3` for a lane run once (`𝒢₀`, `𝒢₂`), `Q = 6`
   for one half of the `𝒢₁ = 𝒢₁a ∩ 𝒢₁b` split, whose two halves the paper
   itself treats as two separate applications of `p.concentration.for.scales`.

2. **The short windows `n < r`.**  The paper states each ratio lemma for
   *every* `M ∈ ℕ₀`, but its only tool, Proposition
   `p.concentration.for.scales`, requires `M ≥ r` ("`m ∈ ℕ` with `m ≥ r`").
   The gap is closed here **without any new hypothesis**, from the
   concentration output itself:
   * for a single scale `k ∈ {0,…,r}`, the bad event `(Ev k)ᶜ` already forces the
     bad-scale *density over the longer window* `{0,…,r}` to be `≥ 1/(r+1)`,
     hence `> θ` as soon as `θ(r+1) < 1`, so
     `P[(Ev k)ᶜ] ≤ exp(-a(r+1))` (`measure_compl_le_of_concEvent`);
   * a union bound over the `n+1 ≤ r` scales of the short window then gives
     `P[θ < density over {0,…,n}] ≤ (n+1)·exp(-a(r+1))`,
   and the single rate hypothesis `log(Qr) + c₁ r ≤ a` dominates *both*
   regimes.

## Scope

Provider material: carrier-neutral local helpers over an abstract probability
space.  The concentration output (`hconc`) and the deterministic scale-locality
reduction (`hreduce`) enter as conditional A hypotheses; nothing new is
assumed.  No `sorry`, no custom axioms, no `set_option maxHeartbeats`.
-/

open MeasureTheory
open Algsuperdiff.Section4.Probability.ScalesConcentration
open scoped ENNReal

namespace Algsuperdiff.Section4.Probability.IndicatorDensity

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ### The threshold event of Appendix D, at a fixed level `θ` -/

/-- The Appendix-D count event at window `{0,…,M}` and level `θ`: the proportion of
rows `k ≤ M` whose weighted row sum `Y_k` exceeds the threshold
`9 s⁻¹ C^{1/p} θ^{-1/p}` is more than `θ`.  This is the left-hand side of the
Appendix-D concentration bound. -/
def concEvent (X : ℤ → ℤ → Ω → ℝ) (p s' θ C : ℝ) (M : ℕ) : Set Ω :=
  {ω | θ < (1 / ((M : ℝ) + 1)) *
      ∑ k ∈ Finset.Icc (0 : ℤ) (M : ℤ),
        (if 9 * s'⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < Yk X s' k ω then (1 : ℝ) else 0)}

/-- **Fixed-level form of the bad-scale density bound.**  The density of bad
scales over the window `{0,…,M}` is dominated by the Appendix-D count event, at the
one level `θ` — the form needed when `θ` is pinned by the consumer. -/
theorem measure_badProp_le_of_concEvent (P : Measure Ω) (X : ℤ → ℤ → Ω → ℝ)
    {p s' θ C : ℝ} (Ev : ℤ → Set Ω) (M : ℕ)
    (hreduce : ∀ m : ℤ, 0 ≤ m → m ≤ (M : ℤ) → ∀ ω ∈ (Ev m)ᶜ,
      9 * s'⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < Yk X s' m ω) :
    P {ω | θ < scaleProp (fun m => (Ev m)ᶜ) M ω} ≤ P (concEvent X p s' θ C M) := by
  classical
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_ofPred_eq, scaleProp, concEvent] at hω ⊢
  refine lt_of_lt_of_le hω ?_
  have hnn : (0 : ℝ) ≤ 1 / ((M : ℝ) + 1) := by positivity
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun m hm => ?_)) hnn
  by_cases hmem : ω ∈ (Ev m)ᶜ
  · have hm' := Finset.mem_Icc.1 hm
    simp only [ite_eq_left hmem, ite_eq_left (hreduce m hm'.1 hm'.2 ω hmem), le_refl]
  · rw [ite_eq_right hmem]; split_ifs <;> norm_num

/-- **A single bad scale inside a length-`r` window is already a `θ`-density event.**
If the level satisfies `θ(r+1) < 1` then, for any scale `k ∈ {0,…,r}`, the bad event
`(Ev k)ᶜ` is contained in the Appendix-D count event over the window `{0,…,r}`:
a single exceeding row contributes `1/(r+1) > θ` to the density.

This is the device that closes the paper's short-window gap: it converts the
concentration bound at the *shortest admissible* window `M = r` into a bound on the
probability of a single bad scale, with no extra hypothesis. -/
theorem measure_compl_le_of_concEvent (P : Measure Ω) (X : ℤ → ℤ → Ω → ℝ)
    {p s' θ C : ℝ} {r : ℕ} (Ev : ℤ → Set Ω) (k : ℤ)
    (hk0 : 0 ≤ k) (hkr : k ≤ (r : ℤ)) (_hθ0 : 0 < θ) (hθr : θ * ((r : ℝ) + 1) < 1)
    (hreduce : ∀ m : ℤ, 0 ≤ m → m ≤ (r : ℤ) → ∀ ω ∈ (Ev m)ᶜ,
      9 * s'⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < Yk X s' m ω) :
    P ((Ev k)ᶜ) ≤ P (concEvent X p s' θ C r) := by
  classical
  refine measure_mono ?_
  intro ω hω
  simp only [Set.mem_ofPred_eq, concEvent]
  have hrpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hθlt : θ < 1 / ((r : ℝ) + 1) := by
    rw [lt_div_iff₀ hrpos]; exact hθr
  have hmemk : k ∈ Finset.Icc (0 : ℤ) (r : ℤ) := Finset.mem_Icc.2 ⟨hk0, hkr⟩
  have hexc := hreduce k hk0 hkr ω hω
  have hone : (1 : ℝ) ≤ ∑ j ∈ Finset.Icc (0 : ℤ) (r : ℤ),
      (if 9 * s'⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < Yk X s' j ω then (1 : ℝ) else 0) := by
    have hterm : (if 9 * s'⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < Yk X s' k ω then (1 : ℝ) else 0)
        ≤ ∑ j ∈ Finset.Icc (0 : ℤ) (r : ℤ),
            (if 9 * s'⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < Yk X s' j ω then (1 : ℝ) else 0) :=
      Finset.single_le_sum (f := fun j =>
        (if 9 * s'⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < Yk X s' j ω then (1 : ℝ) else 0))
        (fun j _ => by split_ifs <;> norm_num) hmemk
    rw [ite_eq_left hexc] at hterm
    exact hterm
  calc θ < 1 / ((r : ℝ) + 1) := hθlt
    _ = (1 / ((r : ℝ) + 1)) * 1 := by ring
    _ ≤ (1 / ((r : ℝ) + 1)) *
        ∑ j ∈ Finset.Icc (0 : ℤ) (r : ℤ),
          (if 9 * s'⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < Yk X s' j ω then (1 : ℝ) else 0) :=
        mul_le_mul_of_nonneg_left hone (by positivity)

/-! ### The rate arithmetic -/

/-- **Long windows.**  `exp(-a(n+1)) ≤ exp(-c₁ n)/Q` when `c₁ ≤ a` and `log Q ≤ a`.

The prefactor `Q` is `3` for a lane that is run once (`𝒢₀`, `𝒢₂`) and `6` for a
lane that is split into two halves at level `θ/2` and recombined by a union
bound (`𝒢₁ = 𝒢₁a ∩ 𝒢₁b`, — two separate applications of
`p.concentration.for.scales`). -/
theorem exp_rate_long {a c₁ Q : ℝ} (n : ℕ) (hQ : 0 < Q) (hc₁ : c₁ ≤ a)
    (hlog : Real.log Q ≤ a) :
    Real.exp (-a * ((n : ℝ) + 1)) ≤ Real.exp (-c₁ * (n : ℝ)) / Q := by
  have h3 : Real.exp (-c₁ * (n : ℝ)) / Q
      = Real.exp (-c₁ * (n : ℝ) - Real.log Q) := by
    rw [Real.exp_sub, Real.exp_log hQ]
  rw [h3]
  refine Real.exp_le_exp.2 ?_
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  linarith only [mul_le_mul_of_nonneg_right hc₁ hn0, hlog]

/-- **Short windows.**  `(n+1)·exp(-a(r+1)) ≤ exp(-c₁ n)/Q` when `n + 1 ≤ r`,
`0 ≤ c₁`, and the single rate condition `log(Q r) + c₁ r ≤ a` holds. -/
theorem exp_rate_short {a c₁ Q : ℝ} {n r : ℕ} (hnr : n + 1 ≤ r) (hc₁ : 0 ≤ c₁)
    (hQ : 0 < Q) (ha0 : 0 ≤ a)
    (hrate : Real.log (Q * (r : ℝ)) + c₁ * (r : ℝ) ≤ a) :
    ((n : ℝ) + 1) * Real.exp (-a * ((r : ℝ) + 1)) ≤ Real.exp (-c₁ * (n : ℝ)) / Q := by
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hnr' : (n : ℝ) + 1 ≤ (r : ℝ) := by exact_mod_cast hnr
  have hr0 : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le hn1 hnr'
  have hLHS : ((n : ℝ) + 1) * Real.exp (-a * ((r : ℝ) + 1))
      = Real.exp (Real.log ((n : ℝ) + 1) + -a * ((r : ℝ) + 1)) := by
    rw [Real.exp_add, Real.exp_log hn1]
  have h3 : Real.exp (-c₁ * (n : ℝ)) / Q
      = Real.exp (-c₁ * (n : ℝ) - Real.log Q) := by
    rw [Real.exp_sub, Real.exp_log hQ]
  rw [hLHS, h3]
  refine Real.exp_le_exp.2 ?_
  -- `log(n+1) + log Q = log(Q(n+1)) ≤ log(Qr) ≤ a - c₁ r ≤ a - c₁ n ≤ a(r+1) - c₁ n`
  have hsplit : Real.log (Q * ((n : ℝ) + 1)) = Real.log Q + Real.log ((n : ℝ) + 1) :=
    Real.log_mul (ne_of_gt hQ) (ne_of_gt hn1)
  have hlogle : Real.log (Q * ((n : ℝ) + 1)) ≤ Real.log (Q * (r : ℝ)) := by
    refine Real.log_le_log (by positivity) ?_
    exact mul_le_mul_of_nonneg_left hnr' hQ.le
  have hcn : c₁ * (n : ℝ) ≤ c₁ * (r : ℝ) := by
    have hnr'' : (n : ℝ) ≤ (r : ℝ) := by linarith only [hnr', hn1]
    exact mul_le_mul_of_nonneg_left hnr'' hc₁
  have har : a ≤ a * ((r : ℝ) + 1) := by
    have har0 : 0 ≤ a * (r : ℝ) := mul_nonneg ha0 hr0.le
    linarith only [har0]
  linarith only [hsplit, hlogle, hcn, har, hrate]

/-! ### The produced tail — generic in the event family -/

/-- **The ratio-lemma tail, in the consumer's shape.**

Given, for one event family `Ev`:

* `hconc` — the Appendix-D concentration output at level `θ` for the family's array
  `X` and threshold constant `C`;
* `hreduce` — the deterministic scale-locality reduction
  `(Ev m)ᶜ ⊆ {9 s⁻¹C^{1/p}θ^{-1/p} < Y_m}` for `m ≥ 0`;

together with the level conditions `0 < θ`, `θ(r+1) < 1` and the single rate
condition `log(Qr) + c₁ r ≤ s p θ/(16 r)`, the bad-scale density over **every**
window `{0,…,n}`, `n : ℕ` — including the short windows `n < r` that
`p.concentration.for.scales` does not reach — obeys
  `P[θ < density of bad scales over {0,…,n}] ≤ exp(-c₁ n)/Q`.

The prefactor `Q ≥ 1` is free: `Q = 3` for a lane that is run once, `Q = 6` for
one half of a lane that is split at level `θ/2` and recombined by a union bound
(the `𝒢₁ = 𝒢₁a ∩ 𝒢₁b` treatment/10598). -/
theorem ratioTail_of_concentration (P : Measure Ω) (X : ℤ → ℤ → Ω → ℝ)
    {p s' θ c₁ C Q : ℝ} {r : ℕ} (Ev : ℤ → Set Ω)
    (hr : 1 ≤ r) (hQ : 1 ≤ Q) (hθ0 : 0 < θ) (hθr : θ * ((r : ℝ) + 1) < 1) (hc₁ : 0 ≤ c₁)
    (hrate : Real.log (Q * (r : ℝ)) + c₁ * (r : ℝ) ≤ s' * p * θ / (16 * (r : ℝ)))
    (hconc : ∀ M : ℕ, (r : ℤ) ≤ (M : ℤ) →
      P (concEvent X p s' θ C M)
        ≤ ENNReal.ofReal (Real.exp (-(s' * p * θ) / (16 * (r : ℝ)) * ((M : ℝ) + 1))))
    (hreduce : ∀ m : ℤ, 0 ≤ m → ∀ ω ∈ (Ev m)ᶜ,
      9 * s'⁻¹ * C ^ (1 / p) * θ ^ (-1 / p) < Yk X s' m ω)
    (n : ℕ) :
    P {ω | θ < scaleProp (fun k => (Ev k)ᶜ) n ω}
      ≤ ENNReal.ofReal (Real.exp (-c₁ * (n : ℝ)) / Q) := by
  classical
  set a : ℝ := s' * p * θ / (16 * (r : ℝ)) with ha
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hrR : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hlog3r : Real.log Q ≤ Real.log (Q * (r : ℝ)) := by
    refine Real.log_le_log hQ0 ?_
    exact le_mul_of_one_le_right hQ0.le hrR
  have hlog3 : (0 : ℝ) ≤ Real.log Q := Real.log_nonneg hQ
  have hcr : c₁ ≤ c₁ * (r : ℝ) := le_mul_of_one_le_right hc₁ hrR
  have ha0 : 0 ≤ a := by linarith only [hrate, hlog3r, hlog3, hcr, hc₁]
  have hac : c₁ ≤ a := by linarith only [hrate, hlog3r, hlog3, hcr]
  have halog : Real.log Q ≤ a := by linarith only [hrate, hlog3r, hcr, hc₁]
  have hneg : -(s' * p * θ) / (16 * (r : ℝ)) = -a := by rw [ha]; ring
  rcases le_or_gt (r : ℤ) (n : ℤ) with hcase | hcase
  · -- long window: the concentration bound applies directly
    refine le_trans (measure_badProp_le_of_concEvent P X Ev n
      (fun m hm0 _ ω hω => hreduce m hm0 ω hω)) ?_
    refine le_trans (hconc n hcase) ?_
    rw [hneg]
    exact ENNReal.ofReal_le_ofReal (exp_rate_long n hQ0 hac halog)
  · -- short window `n < r`: union bound over the `n+1 ≤ r` scales
    have hnr : n + 1 ≤ r := by exact_mod_cast hcase
    have hsub : {ω | θ < scaleProp (fun k => (Ev k)ᶜ) n ω}
        ⊆ ⋃ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (Ev k)ᶜ := by
      intro ω hω
      by_contra hc
      simp only [Set.mem_iUnion, not_exists] at hc
      have hzero : scaleProp (fun k => (Ev k)ᶜ) n ω = 0 := by
        simp only [scaleProp]
        exact mul_eq_zero_of_right _ (Finset.sum_eq_zero (fun k hk => ite_eq_right (hc k hk)))
      rw [Set.mem_ofPred_eq, hzero] at hω
      exact absurd hω (not_lt.2 hθ0.le)
    have hcard : (Finset.Icc (0 : ℤ) (n : ℤ)).card = n + 1 := by
      rw [Int.card_Icc]; omega
    have hsingle : ∀ k ∈ Finset.Icc (0 : ℤ) (n : ℤ),
        P ((Ev k)ᶜ) ≤ ENNReal.ofReal (Real.exp (-a * ((r : ℝ) + 1))) := by
      intro k hk
      have hk' := Finset.mem_Icc.1 hk
      have hkr : k ≤ (r : ℤ) := le_trans hk'.2 (by exact_mod_cast hcase.le)
      refine le_trans (measure_compl_le_of_concEvent (r := r) P X Ev k hk'.1 hkr hθ0 hθr
        (fun m hm0 _ ω hω => hreduce m hm0 ω hω)) ?_
      refine le_trans (hconc r le_rfl) ?_
      rw [hneg]
    calc P {ω | θ < scaleProp (fun k => (Ev k)ᶜ) n ω}
        ≤ P (⋃ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), (Ev k)ᶜ) := measure_mono hsub
      _ ≤ ∑ k ∈ Finset.Icc (0 : ℤ) (n : ℤ), P ((Ev k)ᶜ) := measure_biUnion_finset_le _ _
      _ ≤ ∑ _k ∈ Finset.Icc (0 : ℤ) (n : ℤ),
            ENNReal.ofReal (Real.exp (-a * ((r : ℝ) + 1))) := Finset.sum_le_sum hsingle
      _ = ((n : ℕ) + 1 : ℕ) • ENNReal.ofReal (Real.exp (-a * ((r : ℝ) + 1))) := by
            rw [Finset.sum_const, hcard]
      _ = ENNReal.ofReal (((n : ℝ) + 1) * Real.exp (-a * ((r : ℝ) + 1))) := by
            rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast ((n : ℕ) + 1),
              ← ENNReal.ofReal_mul (by positivity)]
            norm_num
      _ ≤ ENNReal.ofReal (Real.exp (-c₁ * (n : ℝ)) / Q) :=
            ENNReal.ofReal_le_ofReal (exp_rate_short hnr hc₁ hQ0 ha0 hrate)

end

end Algsuperdiff.Section4.Probability.IndicatorDensity
