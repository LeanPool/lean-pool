/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import Mathlib.Analysis.Subadditive
public import Mathlib.Topology.Instances.EReal.Lemmas
public import LeanPool.MultiplicativeErgodic.Birkhoff

/-!
# Subadditive families: definitions and block decompositions

The first part of `ProofMet.Kingman` (Section 4 of `proof_met.tex`): `SubadditiveFamily`
itself, the elementary block decompositions of `f n`, and the existence of Fekete's limit for
the means.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Two-sided iteration of an invertible measurable transformation, so that
`zIter σ (-n) ω = σ⁻¹^[n] ω`. Used to state the backward-in-time statements of the paper. -/
noncomputable def zIter (σ : Ω ≃ᵐ Ω) : ℤ → Ω → Ω
  | Int.ofNat n => fun ω => σ^[n] ω
  | Int.negSucc n => fun ω => σ.symm^[n + 1] ω

/-- **Definition.** A subadditive family of measurable functions:
`f_{m+n}(ω) ≤ f_m(σ^n ω) + f_n(ω)`. -/
def SubadditiveFamily (σ : Ω → Ω) (f : ℕ → Ω → ℝ) : Prop :=
  (∀ n, Measurable (f n)) ∧ ∀ m n ω, f (m + n) ω ≤ f m (σ^[n] ω) + f n ω

/-- **Definition.** The stationary subadditive process `f_{a→b} := f_{b-a} ∘ σ^a` generated
by a subadditive family (for `σ` invertible, so `a, b` range over `ℤ`). -/
noncomputable def SubadditiveFamily.toProcess (σ : Ω ≃ᵐ Ω) (f : ℕ → Ω → ℝ) (a b : ℤ) (ω : Ω) : ℝ :=
  f (b - a).toNat (zIter σ a ω)

/-- For `x : ℝ` and `n : ℕ`, the `EReal` quotient `↑x / ↑n` is the coercion of the real
quotient `x / n`.  The two sides are definitionally equal (`EReal.coe_div` and
`EReal.coe_coe_eq_natCast` are both `rfl`), but having it as a rewrite rule lets
`EReal.tendsto_coe` apply *syntactically* to the statements below, where the limit is
`EReal`-valued but the sequence is real-valued. -/
theorem coe_div_natCast (x : ℝ) (n : ℕ) :
    ((x : EReal) / (n : EReal)) = ((x / (n : ℝ) : ℝ) : EReal) := rfl

/-- Subadditivity bounds the whole family by the Birkhoff sums of `f 1`:
`f n ω ≤ Σ_{i<n} f 1 (σⁱ ω)` for `n ≥ 1`.

Stated from `n = 1`, not `n = 0`: subadditivity at `(0,0)` gives `f 0 ≤ f 0 + f 0`, i.e.
`0 ≤ f 0`, which is the *wrong* direction for the `n = 0` case. -/
theorem SubadditiveFamily.le_birkhoffSum {σ : Ω → Ω} {f : ℕ → Ω → ℝ}
    (hf : SubadditiveFamily σ f) : ∀ n, 1 ≤ n → ∀ ω, f n ω ≤ birkhoffSum σ (f 1) n ω := by
  intro n
  induction n with
  | zero => omega
  | succ n ih =>
    intro _ ω
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [birkhoffSum]
    · have h1 := hf.2 1 n ω
      have h2 := ih hn (ω := ω)
      rw [congrFun (birkhoffSum_succ σ (f 1) n) ω]
      simp only [Pi.add_apply, Function.comp_apply]
      have : (1 + n) = (n + 1) := by ring
      rw [this] at h1
      linarith

/-- Chaining subadditivity across `q` consecutive blocks of length `N`:
`f_{qN}(ω) ≤ Σ_{i<q} f_N(σ^{iN} ω)`.

As with `le_birkhoffSum`, this starts at `q = 1`: at `q = 0` the right side is `0` while
subadditivity only gives `0 ≤ f 0`. -/
theorem SubadditiveFamily.le_sum_blocks {σ : Ω → Ω} {f : ℕ → Ω → ℝ}
    (hf : SubadditiveFamily σ f) (N : ℕ) :
    ∀ q, 1 ≤ q → ∀ ω, f (q * N) ω ≤ ∑ i ∈ Finset.range q, f N (σ^[i * N] ω) := by
  intro q
  induction q with
  | zero => omega
  | succ q ih =>
    intro _ ω
    rcases Nat.eq_zero_or_pos q with rfl | hq
    · simp
    · have hstep := hf.2 N (q * N) ω
      have hrec := ih hq ω
      rw [Finset.sum_range_succ]
      have hidx : N + q * N = (q + 1) * N := by ring
      rw [hidx] at hstep
      linarith

/-- The block decomposition used for Kingman's `limsup ≤ C` half: writing `n = q·N + r`,
`f_n(ω) ≤ f_r(σ^{qN} ω) + Σ_{i<q} f_N(σ^{iN} ω)`.

The first term is the boundary remainder (`r < N`, so finitely many possibilities), and the sum
is a Birkhoff sum for `σ^N`. Averaging this over the `N` offsets `j ∈ [0, N)` converts that into
a Birkhoff sum for `σ` itself — which is why only ergodicity of `σ` is needed, not of `σ^N`
(see the note in `ProofMet.Birkhoff`). -/
theorem SubadditiveFamily.le_block_decomp {σ : Ω → Ω} {f : ℕ → Ω → ℝ}
    (hf : SubadditiveFamily σ f) (N q r : ℕ) (hq : 1 ≤ q) (ω : Ω) :
    f (r + q * N) ω ≤ f r (σ^[q * N] ω) + ∑ i ∈ Finset.range q, f N (σ^[i * N] ω) := by
  have hsplit := hf.2 r (q * N) ω
  have hblocks := hf.le_sum_blocks N q hq ω
  linarith

/-- The index identity behind offset averaging: summing a `σ^N`-indexed family over the `N`
offsets recovers a plain `σ`-indexed sum,
`Σ_{i<q} Σ_{j<N} g(iN + j) = Σ_{k<qN} g(k)`. -/
theorem sum_blocks_eq_sum_range (N : ℕ) (g : ℕ → ℝ) :
    ∀ q, ∑ i ∈ Finset.range q, ∑ j ∈ Finset.range N, g (i * N + j)
      = ∑ k ∈ Finset.range (q * N), g k := by
  intro q
  induction q with
  | zero => simp
  | succ q ih =>
    rw [Finset.sum_range_succ, ih, show (q + 1) * N = q * N + N by ring, Finset.sum_range_add]

/-- **The sharp integrability hypothesis is `∫ (f 1)⁺ < ∞`.**

`proof_met.tex` (l.406) and Kingman's own paper ask for `∀ n, Integrable (f n) μ`. That is
doubly too strong, and `kingman` assumes only `Integrable (fun ω => max (f 1 ω) 0) μ` instead.

By `SubadditiveFamily.le_birkhoffSum`, `f n ≤ Σ_{i<n} f 1 ∘ σⁱ`, so

  `(f n)⁺ ≤ (Σ_{i<n} f 1 ∘ σⁱ)⁺ ≤ Σ_{i<n} (f 1)⁺ ∘ σⁱ`,

which is integrable whenever `(f 1)⁺` is, because `σ` preserves `μ`. So integrability of the
*positive part of `f 1` alone* already gives `∫ f n` a well-defined value in `[-∞, ∞)` for every
`n`, and `n ↦ ∫ f n` is still subadditive, so Fekete still produces a limit in `[-∞, ∞)`.

**Why the positive part, not `f 1` itself.** `Integrable (f 1) μ` means `∫ |f 1| < ∞`, i.e. both
parts finite. For a rank-deficient cocycle `f 1 = log ρ_k(𝓛)` is unboundedly negative on a set of
positive measure, so `∫ |f 1| = ∞` and even that hypothesis is undischargeable. What *is*
available there is exactly `∫ (f 1)⁺ < ∞`, since `ρ_k ≤ ‖L‖` gives `log⁺ ρ_k ≤ log⁺ ‖L‖`, which
is the cocycle's own `forwardIntegrable` assumption. So the weakening is not cosmetic: it is the
difference between a theorem the cocycle application can use and one it cannot.

**How `kingman` states the mean clause.** Applying this weakening needs `∫ f n` to make sense
where the value `-∞` is legitimately attained, which the ordinary Bochner integral does not
(Lean's `∫ g` is the junk value `0` off `L¹`). `kingman` therefore uses `lowerIntegral`, and
`lowerIntegral_eq_integral` shows the two agree on `L¹`. Same design decision as at
`Cocycle.chiRaw`. -/
theorem SubadditiveFamily.integrable_posPart {σ : Ω → Ω} {f : ℕ → Ω → ℝ}
    {μ : Measure Ω} (hmp : MeasurePreserving σ μ μ) (hf : SubadditiveFamily σ f)
    (h1 : Integrable (fun ω => max (f 1 ω) 0) μ) (n : ℕ) (hn : 1 ≤ n) :
    Integrable (fun ω => max (f n ω) 0) μ := by
  refine Integrable.mono' (g := fun ω => birkhoffSum σ (fun x => max (f 1 x) 0) n ω) ?_ ?_ ?_
  · -- `Σ (f 1)⁺ ∘ σⁱ` is integrable, by measure preservation.
    change Integrable (fun ω => ∑ i ∈ Finset.range n, max (f 1 (σ^[i] ω)) 0) μ
    exact integrable_finsetSum _
      (fun i _ => (hmp.iterate i).integrable_comp_of_integrable h1)
  · exact ((hf.1 n).max measurable_const).aestronglyMeasurable
  · filter_upwards with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    refine max_le ?_ ?_
    · refine le_trans (hf.le_birkhoffSum n hn ω) ?_
      exact Finset.sum_le_sum (fun i _ => le_max_left _ _)
    · exact Finset.sum_nonneg (fun i _ => le_max_right _ _)

/-- The means `n ↦ ∫ f_n` of an integrable subadditive family are themselves a subadditive
sequence: integrate `f_{m+n} ≤ f_m ∘ σⁿ + f_n` and use measure preservation to drop the `σⁿ`. -/
theorem SubadditiveFamily.subadditive_integral (μ : Measure Ω)
    (σ : Ω → Ω) (hmp : MeasurePreserving σ μ μ) (f : ℕ → Ω → ℝ) (hf : SubadditiveFamily σ f)
    (hL1 : ∀ n, Integrable (f n) μ) :
    Subadditive (fun n => ∫ ω, f n ω ∂μ) := by
  intro m n
  have hcomp : ∫ ω, f m (σ^[n] ω) ∂μ = ∫ ω, f m ω ∂μ := by
    have hmap : Measure.map (σ^[n]) μ = μ := (hmp.iterate n).map_eq
    calc ∫ ω, f m (σ^[n] ω) ∂μ = ∫ ω, f m ω ∂(Measure.map (σ^[n]) μ) :=
          (integral_map (hmp.iterate n).measurable.aemeasurable
            (by rw [hmap]; exact (hL1 m).aestronglyMeasurable)).symm
      _ = ∫ ω, f m ω ∂μ := by rw [hmap]
  calc ∫ ω, f (m + n) ω ∂μ ≤ ∫ ω, (f m (σ^[n] ω) + f n ω) ∂μ :=
        integral_mono (hL1 (m + n))
          (((hmp.iterate n).integrable_comp_of_integrable (hL1 m)).add (hL1 n))
          (fun ω => hf.2 m n ω)
    _ = (∫ ω, f m ω ∂μ) + ∫ ω, f n ω ∂μ := by
        rw [integral_add (f := fun ω => f m (σ^[n] ω)) (g := fun ω => f n ω)
          ((hmp.iterate n).integrable_comp_of_integrable (hL1 m)) (hL1 n), hcomp]

/-- The **mean** half of Kingman's theorem, by Fekete's subadditive lemma.

For an `L¹` subadditive family the sequence `n ↦ ∫ f_n` is subadditive (measure preservation
kills the `σⁿ` in `f_{m+n} ≤ f_m ∘ σⁿ + f_n`), so `(1/n) ∫ f_n` converges in `[-∞, ∞)`.

The `EReal` value is genuinely needed: Fekete gives the limit `inf_{n ≥ 1} (1/n)∫f_n`, which is a
real number exactly when that infimum is bounded below, and `-∞` otherwise. Mathlib's
`Subadditive.tendsto_lim` covers the bounded case; the unbounded case follows from
`Subadditive.eventually_div_lt_of_div_lt`, which turns a single `n` with `u n / n < L` into
`u m / m < L` eventually — i.e. exactly divergence to `-∞`. -/
theorem exists_tendsto_integral_div (μ : Measure Ω) (σ : Ω → Ω)
    (hmp : MeasurePreserving σ μ μ) (f : ℕ → Ω → ℝ) (hf : SubadditiveFamily σ f)
    (hL1 : ∀ n, Integrable (f n) μ) :
    ∃ C : EReal, C < ⊤ ∧
      Tendsto (fun n => ((∫ ω, f n ω ∂μ) / n : EReal)) atTop (nhds C) := by
  set u : ℕ → ℝ := fun n => ∫ ω, f n ω ∂μ with hu
  have hsub : Subadditive u := SubadditiveFamily.subadditive_integral μ σ hmp f hf hL1
  by_cases hbdd : BddBelow (Set.range fun n => u n / n)
  · -- Bounded below: Fekete gives a real limit.
    refine ⟨(hsub.lim : EReal), EReal.coe_lt_top _, ?_⟩
    simp only [coe_div_natCast]
    exact EReal.tendsto_coe.2 (hsub.tendsto_lim hbdd)
  · -- Not bounded below: the averages diverge to `-∞`.
    refine ⟨⊥, bot_lt_top, ?_⟩
    simp only [coe_div_natCast]
    refine EReal.tendsto_coe_nhds_bot_iff.mpr (tendsto_atBot.mpr fun L => ?_)
    -- Some `n` has `u n / n` below `min L 0 - 1 < 0`; that forces `n ≠ 0`, since `u 0 / 0 = 0`.
    obtain ⟨y, hymem, hylt⟩ := not_bddBelow_iff.mp hbdd (min L 0 - 1)
    obtain ⟨m, rfl⟩ := hymem
    have hneg : u m / m < 0 := lt_of_lt_of_le hylt (by simp)
    have hm0 : m ≠ 0 := by
      rintro rfl
      simp only [Nat.cast_zero, div_zero] at hneg
      exact absurd hneg (lt_irrefl 0)
    have hmL : u m / m < L := lt_of_lt_of_le hylt (by
      have : min L 0 ≤ L := min_le_left _ _
      linarith)
    have hpow (k : ℕ) : (Real.exp (u k)) ^ (k : ℝ)⁻¹ = Real.exp (u k / k) := by
      rw [← Real.exp_mul, div_eq_mul_inv]
    have hevent := hsub.submultiplicative_exp.eventually_rpow_lt_of_rpow_lt
      (fun k => (Real.exp_pos (u k)).le) hm0
      (by simpa only [hpow] using Real.exp_lt_exp.mpr hmL)
    filter_upwards [hevent] with p hp
    rw [hpow] at hp
    exact (Real.exp_lt_exp.mp hp).le

end MultiplicativeErgodic
