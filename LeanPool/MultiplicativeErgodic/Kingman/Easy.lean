/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Kingman.Core

/-!
# The easy half, along orbits

`easyking` and its `L¹` sibling: `limsup f_n(σⁿω)/n ≤ C` along the orbit, together with the
offset decompositions and boundary-decay estimates it needs, and the `EReal`/`ℝ` wrappers.
-/

@[expose] public section

namespace MultiplicativeErgodic

open MeasureTheory Filter

open scoped ENNReal

variable {Ω : Type*} [MeasurableSpace Ω]
/-- **Boundary decay.** In the block decomposition `f_n ≤ f_r ∘ σ^{qN} + Σ_{i<q} f_N ∘ σ^{iN}`
the remainder `r` ranges over the finitely many values `< N`, and each boundary term
`f_r(σ^m ω)` is `o(m)` along the orbit. This holds for *all* `r` simultaneously, a.e.,
for any measurable integrable family.

Each `r` is `L1_orbit_decay` applied to `f r`; the countably many `r` are intersected with
`ae_all_iff`. Note this is now a corollary of Birkhoff, not of `kingman` — see the note on
`L1_orbit_decay` above. -/
theorem SubadditiveFamily.boundary_decay (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → Ω)
    (hmp : MeasurePreserving σ μ μ) (f : ℕ → Ω → ℝ) (hfm : ∀ n, Measurable (f n))
    (hint : ∀ n, Integrable (f n) μ) :
    ∀ᵐ ω ∂μ, ∀ r : ℕ, Tendsto (fun m : ℕ => f r (σ^[m] ω) / m) atTop (nhds 0) := by
  refine ae_all_iff.mpr (fun r => ?_)
  exact L1_orbit_decay μ σ hmp (f r) (hfm r) (hint r)

/-- **Pointwise block bound along multiples of `N`.** Dividing `le_sum_blocks` by `qN` gives
`f_{qN}(ω)/(qN) ≤ (1/N) · (1/q) Σ_{i<q} f_N(σ^{iN} ω)`.

This finite inequality needs no invariant measure. Under measure preservation and integrability
of `f_N`, Birkhoff's theorem can later supply almost-everywhere convergence of the right side;
ergodicity of `σ^N` is unnecessary. The general-index bound also needs the offset average and
`boundary_decay`. -/
theorem SubadditiveFamily.blockAverage_le (σ : Ω → Ω)
    (f : ℕ → Ω → ℝ) (hf : SubadditiveFamily σ f)
    (N : ℕ) (hN : 1 ≤ N) (q : ℕ) (hq : 1 ≤ q) (ω : Ω) :
    f (q * N) ω / (q * N : ℝ)
      ≤ (1 / (N : ℝ)) * birkhoffAverage ℝ (σ^[N]) (f N) q ω := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hblocks := hf.le_sum_blocks N q hq ω
  -- the block sum *is* the Birkhoff sum of `f N` for `σ^N`
  have hsum : birkhoffSum (σ^[N]) (f N) q ω = ∑ i ∈ Finset.range q, f N (σ^[i * N] ω) := by
    change ∑ i ∈ Finset.range q, f N ((σ^[N])^[i] ω) = _
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Function.iterate_mul]
    congr 2
    ring
  rw [birkhoffAverage_real, hsum]
  rw [div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * N)]
  have hrhs : (1 / (N : ℝ)) * ((∑ i ∈ Finset.range q, f N (σ^[i * N] ω)) / (q : ℝ))
      * ((q : ℝ) * N) = ∑ i ∈ Finset.range q, f N (σ^[i * N] ω) := by
    field_simp
  rw [hrhs]
  exact hblocks

/-- Single-offset decomposition: starting the block chain at offset `j < N`,
`f_{(p+1)N}(ω) ≤ f_{N-j}(σ^{pN+j} ω) + Σ_{i<p} f_N(σ^{iN+j} ω) + f_j(ω)`.

Written with `q = p + 1` so the `ℕ`-subtraction arithmetic stays linear. -/
theorem SubadditiveFamily.le_offset_decomp {σ : Ω → Ω} {f : ℕ → Ω → ℝ}
    (hf : SubadditiveFamily σ f) (N p j : ℕ) (hp : 1 ≤ p) (hj : j < N) (ω : Ω) :
    f ((p + 1) * N) ω ≤ f (N - j) (σ^[p * N] (σ^[j] ω))
      + (∑ i ∈ Finset.range p, f N (σ^[i * N] (σ^[j] ω))) + f j ω := by
  have hexp : (p + 1) * N = p * N + N := by ring
  have hjle : j ≤ p * N + N := by omega
  have hsplit := hf.2 ((p + 1) * N - j) j ω
  rw [Nat.sub_add_cancel (by omega : j ≤ (p + 1) * N)] at hsplit
  have hdec := hf.le_block_decomp N p (N - j) hp (σ^[j] ω)
  have harith : N - j + p * N = (p + 1) * N - j := by omega
  rw [harith] at hdec
  linarith

/-- **Offset-averaged bound.** Summing `le_offset_decomp` over the `N` offsets collapses the
double sum into a plain `σ`-Birkhoff sum of `f_N`:

`N · f_{(p+1)N}(ω) ≤ Σ_{k<pN} f_N(σ^k ω) + Σ_{j<N} f_{N-j}(σ^{pN+j} ω) + Σ_{j<N} f_j(ω)`.

The first term on the right is a Birkhoff sum for `σ` itself — *not* `σ^N` — which is exactly why
ergodicity of `σ` alone suffices; `σ^N` need not be ergodic (see the note in `ProofMet.Birkhoff`).
The other two terms involve only the `N` boundary values, killed by `boundary_decay` after
dividing by `n`. -/
theorem SubadditiveFamily.nsmul_le_sum_offsets {σ : Ω → Ω} {f : ℕ → Ω → ℝ}
    (hf : SubadditiveFamily σ f) (N p : ℕ) (hp : 1 ≤ p) (ω : Ω) :
    (N : ℝ) * f ((p + 1) * N) ω
      ≤ (∑ k ∈ Finset.range (p * N), f N (σ^[k] ω))
        + (∑ j ∈ Finset.range N, f (N - j) (σ^[p * N] (σ^[j] ω)))
        + ∑ j ∈ Finset.range N, f j ω := by
  -- Sum the `N` single-offset bounds.
  have hsum : (N : ℝ) * f ((p + 1) * N) ω
      = ∑ _j ∈ Finset.range N, f ((p + 1) * N) ω := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum]
  have hstep : ∀ j ∈ Finset.range N, f ((p + 1) * N) ω
      ≤ f (N - j) (σ^[p * N] (σ^[j] ω))
        + (∑ i ∈ Finset.range p, f N (σ^[i * N] (σ^[j] ω))) + f j ω :=
    fun j hj => hf.le_offset_decomp N p j hp (Finset.mem_range.mp hj) ω
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  -- Regroup, and collapse the double block sum via `sum_blocks_eq_sum_range`.
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hdouble : ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range p, f N (σ^[i * N] (σ^[j] ω))
      = ∑ k ∈ Finset.range (p * N), f N (σ^[k] ω) := by
    rw [Finset.sum_comm]
    have hcomp : ∀ i j : ℕ, f N (σ^[i * N] (σ^[j] ω)) = f N (σ^[i * N + j] ω) := by
      intro i j
      rw [← Function.iterate_add_apply]
    simp only [hcomp]
    exact sum_blocks_eq_sum_range N (fun k => f N (σ^[k] ω)) p
  rw [hdouble]
  ring

/-- A boundary term `u(pN+j)/((p+1)N)` vanishes whenever `u(m)/m` does: the denominators differ
by a bounded factor, since `pN + j ≤ (p+1)N` for `j < N`. -/
theorem tendsto_boundary_div (N j : ℕ) (hN : 1 ≤ N) (hj : j < N) (u : ℕ → ℝ)
    (hu : Tendsto (fun m : ℕ => u m / m) atTop (nhds 0)) :
    Tendsto (fun p : ℕ => u (p * N + j) / (((p + 1) * N : ℕ) : ℝ)) atTop (nhds 0) := by
  have hidx : Tendsto (fun p : ℕ => p * N + j) atTop atTop :=
    tendsto_atTop_mono (fun p => le_trans (Nat.le_mul_of_pos_right p hN) (Nat.le_add_right _ _))
      tendsto_id
  have hg : Tendsto (fun p : ℕ => |u (p * N + j) / ((p * N + j : ℕ) : ℝ)|) atTop (nhds 0) := by
    simpa using (hu.comp hidx).abs
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hm1 : 1 ≤ p * N + j :=
    le_trans (le_trans hp (Nat.le_mul_of_pos_right p hN)) (Nat.le_add_right _ _)
  have hm : (0 : ℝ) < ((p * N + j : ℕ) : ℝ) := by exact_mod_cast hm1
  have hle : ((p * N + j : ℕ) : ℝ) ≤ (((p + 1) * N : ℕ) : ℝ) := by
    have hnat : p * N + j ≤ (p + 1) * N := by
      have : (p + 1) * N = p * N + N := by ring
      omega
    exact_mod_cast hnat
  rw [Real.norm_eq_abs, abs_div, abs_div]
  gcongr

/-- **`limsup ≤ ∫ f_N / N` along multiples of `N`.**

Dividing `nsmul_le_sum_offsets` through by `N·(p+1)N` and letting `p → ∞`: the collapsed block
sum is a `σ`-Birkhoff sum of `f_N`, so ergodic Birkhoff sends it to `∫ f_N`, while the `2N`
boundary terms vanish by `boundary_decay` via `tendsto_boundary_div`.

Stated in the `∀ b > bound, eventually < b` form used elsewhere in this development, which avoids
`limsup` boundedness bookkeeping. -/
theorem SubadditiveFamily.eventually_lt_of_integral_div_lt (μ : Measure Ω)
    [IsProbabilityMeasure μ] (σ : Ω → Ω) (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily σ f) (hint : ∀ n, Integrable (f n) μ) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, (∫ x, f N x ∂μ) / N < b →
      ∀ᶠ p in atTop, f ((p + 1) * N) ω / (((p + 1) * N : ℕ) : ℝ) < b := by
  have hmp : MeasurePreserving σ μ μ := hσ.toMeasurePreserving
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  filter_upwards [ae_tendsto_birkhoffAverage_of_ergodic hσ (f N) (hf.1 N) (hint N),
    SubadditiveFamily.boundary_decay μ σ hmp f hf.1 hint] with ω hbirk hbd
  intro b hb
  -- The right-hand side of `nsmul_le_sum_offsets`, divided by `N·(p+1)N`.
  set S : ℕ → ℝ := fun p => (∑ k ∈ Finset.range (p * N), f N (σ^[k] ω)) / (((p + 1) * N : ℕ) : ℝ)
    with hS
  set B1 : ℕ → ℝ := fun p =>
    (∑ j ∈ Finset.range N, f (N - j) (σ^[p * N] (σ^[j] ω))) / (((p + 1) * N : ℕ) : ℝ) with hB1
  set B2 : ℕ → ℝ := fun p =>
    (∑ j ∈ Finset.range N, f j ω) / (((p + 1) * N : ℕ) : ℝ) with hB2
  -- `S p → ∫ f N`.
  have hSlim : Tendsto S atTop (nhds (∫ x, f N x ∂μ)) := by
    have hb1 : Tendsto (fun p : ℕ => birkhoffAverage ℝ σ (f N) (p * N) ω) atTop
        (nhds (∫ x, f N x ∂μ)) := by
      refine hbirk.comp (tendsto_atTop_mono (fun p => Nat.le_mul_of_pos_right p hN) tendsto_id)
    have hratio : Tendsto (fun p : ℕ => ((p * N : ℕ) : ℝ) / (((p + 1) * N : ℕ) : ℝ)) atTop
        (nhds 1) := by
      have : ∀ p : ℕ, ((p * N : ℕ) : ℝ) / (((p + 1) * N : ℕ) : ℝ)
          = (p : ℝ) / ((p : ℝ) + 1) := by
        intro p
        push_cast
        rw [div_eq_div_iff (by positivity) (by positivity)]
        ring
      simp only [this]
      exact tendsto_natCast_div_add_atTop (1 : ℝ)
    have hmul := hb1.mul hratio
    rw [mul_one] at hmul
    refine hmul.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with p hp
    have hpN : (0 : ℝ) < ((p * N : ℕ) : ℝ) := by
      have : 0 < p * N := Nat.mul_pos hp hN
      exact_mod_cast this
    rw [hS, birkhoffAverage_real]
    field_simp
    rfl
  -- Boundary terms vanish.
  have hB1lim : Tendsto B1 atTop (nhds 0) := by
    rw [hB1]
    simp only [Finset.sum_div]
    rw [show (0:ℝ) = ∑ _j ∈ Finset.range N, (0:ℝ) by simp]
    refine tendsto_finsetSum _ (fun j hj => ?_)
    have hjN := Finset.mem_range.mp hj
    have := tendsto_boundary_div N j hN hjN (fun m => f (N - j) (σ^[m] ω)) (hbd (N - j))
    refine this.congr (fun p => ?_)
    rw [← Function.iterate_add_apply]
  have hB2lim : Tendsto B2 atTop (nhds 0) := by
    rw [hB2]
    have hden : Tendsto (fun p : ℕ => (((p + 1) * N : ℕ) : ℝ)) atTop atTop := by
      refine tendsto_natCast_atTop_atTop.comp ?_
      refine tendsto_atTop_mono (fun p => ?_) tendsto_id
      exact le_trans (Nat.le_succ p) (Nat.le_mul_of_pos_right (p + 1) hN)
    exact Tendsto.div_atTop tendsto_const_nhds hden
  -- Assemble: the bound tends to `∫ f N / N < b`.
  have htotal : Tendsto (fun p => (S p + B1 p + B2 p) / N) atTop
      (nhds ((∫ x, f N x ∂μ) / N)) := by
    have := ((hSlim.add hB1lim).add hB2lim).div_const (N : ℝ)
    simpa using this
  filter_upwards [(tendsto_order.mp htotal).2 b hb, eventually_ge_atTop 1] with p hlt hp
  -- and `f_{(p+1)N}/((p+1)N)` is below it, by `nsmul_le_sum_offsets`.
  have hkey := hf.nsmul_le_sum_offsets N p hp ω
  have hpos : (0 : ℝ) < (((p + 1) * N : ℕ) : ℝ) := by
    have : 0 < (p + 1) * N := Nat.mul_pos (Nat.succ_pos p) hN
    exact_mod_cast this
  have hle : f ((p + 1) * N) ω / (((p + 1) * N : ℕ) : ℝ) ≤ (S p + B1 p + B2 p) / N := by
    have hSum : S p + B1 p + B2 p
        = ((∑ k ∈ Finset.range (p * N), f N (σ^[k] ω))
          + (∑ j ∈ Finset.range N, f (N - j) (σ^[p * N] (σ^[j] ω)))
          + (∑ j ∈ Finset.range N, f j ω)) / (((p + 1) * N : ℕ) : ℝ) := by
      rw [hS, hB1, hB2]; ring
    rw [hSum, div_div, div_le_div_iff₀ hpos (by positivity)]
    nlinarith [hkey, hpos, hN0]
  linarith

/-- **Offset average at an arbitrary length.** A variant of `nsmul_le_sum_offsets` whose block
count `q` is *uniform across the offsets* instead of being tied to the length: as long as
`qN + N ≤ n + 1`, every offset `j < N` still admits `q` full blocks, so the double sum tiles
`[0, qN)` exactly and the leftover `f_{n-j-qN}` has length `< 2N`.

This is the shape needed at a *moving* base point, where the length `n` cannot be arranged to be
a multiple of `N`. -/
theorem SubadditiveFamily.nsmul_le_sum_offsets_of_le {σ : Ω → Ω} {f : ℕ → Ω → ℝ}
    (hf : SubadditiveFamily σ f) (N q n : ℕ) (hq : 1 ≤ q) (hn : q * N + N ≤ n + 1) (ω : Ω) :
    (N : ℝ) * f n ω
      ≤ (∑ k ∈ Finset.range (q * N), f N (σ^[k] ω))
        + (∑ j ∈ Finset.range N, f (n - j - q * N) (σ^[q * N + j] ω))
        + ∑ j ∈ Finset.range N, f j ω := by
  have hsum : (N : ℝ) * f n ω = ∑ _j ∈ Finset.range N, f n ω := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsum]
  have hstep : ∀ j ∈ Finset.range N, f n ω
      ≤ (∑ i ∈ Finset.range q, f N (σ^[i * N] (σ^[j] ω)))
        + f (n - j - q * N) (σ^[q * N + j] ω) + f j ω := by
    intro j hj
    have hjN := Finset.mem_range.mp hj
    have hqj : q * N + j ≤ n := by
      have h1 : q * N + j < q * N + N := Nat.add_lt_add_left hjN _
      exact Nat.lt_succ_iff.mp (lt_of_lt_of_le h1 hn)
    have hjn : j ≤ n := le_trans (Nat.le_add_left j (q * N)) hqj
    have hqn : q * N ≤ n - j := Nat.le_sub_of_add_le (by omega)
    have hsplit := hf.2 (n - j) j ω
    rw [Nat.sub_add_cancel hjn] at hsplit
    have hdec := hf.le_block_decomp N q (n - j - q * N) hq (σ^[j] ω)
    rw [Nat.sub_add_cancel hqn] at hdec
    rw [show σ^[q * N] (σ^[j] ω) = σ^[q * N + j] ω from
      (Function.iterate_add_apply σ (q * N) j ω).symm] at hdec
    linarith
  refine le_trans (Finset.sum_le_sum hstep) (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hdouble : ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range q, f N (σ^[i * N] (σ^[j] ω))
      = ∑ k ∈ Finset.range (q * N), f N (σ^[k] ω) := by
    rw [Finset.sum_comm]
    have hcomp : ∀ i j : ℕ, f N (σ^[i * N] (σ^[j] ω)) = f N (σ^[i * N + j] ω) := by
      intro i j
      rw [← Function.iterate_add_apply]
    simp only [hcomp]
    exact sum_blocks_eq_sum_range N (fun k => f N (σ^[k] ω)) q
  rw [hdouble]

/-- Decay survives reindexing: if `u m / m → 0` and the indices `idx n → ∞` with `idx n / n`
convergent, then `u (idx n) / n → 0` as well.

Stated for a plain sequence `u` rather than for `g ∘ σ^{·} ω` on purpose. In the orbit-decay
form the unifier faces `?g (σ^[m] ω) =?= …`, which is *not* a Miller pattern (the argument is a
term containing the bound variable, not the variable itself), and higher-order projection search
blows the heartbeat budget. With `?u m` it is a pattern and unification is immediate. -/
theorem tendsto_orbit_div_of_ratio {u : ℕ → ℝ}
    (hg : Tendsto (fun m : ℕ => u m / m) atTop (nhds 0))
    (idx : ℕ → ℕ) (hidx : Tendsto idx atTop atTop) (L : ℝ)
    (hratio : Tendsto (fun n : ℕ => (idx n : ℝ) / n) atTop (nhds L)) :
    Tendsto (fun n : ℕ => u (idx n) / n) atTop (nhds 0) := by
  have h1 : Tendsto (fun n : ℕ => u (idx n) / ((idx n : ℕ) : ℝ)) atTop (nhds 0) :=
    hg.comp hidx
  have h2 := h1.mul hratio
  rw [zero_mul] at h2
  refine h2.congr' ?_
  filter_upwards [hidx.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hidxn hn
  have hne : ((idx n : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((idx n : ℕ) : ℝ) := by exact_mod_cast hidxn
    exact ne_of_gt this
  have hne' : ((n : ℕ) : ℝ) ≠ 0 := by
    have : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast hn
    exact ne_of_gt this
  field_simp

/-- **`limsup f_n(σⁿω)/n ≤ ∫ f_N / N`** — the upper half of `easyking_of_integrable`.

The block decomposition of `eventually_lt_of_integral_div_lt` is run at the *moving* base point
`σⁿω`, where the length `n` cannot be arranged to be a multiple of `N`; the uniform tiling comes
from `nsmul_le_sum_offsets_of_le` with `q = n/N - 1` blocks per offset. The bulk term is then the
Birkhoff-sum difference `S_{n+qN}f_N(ω) - S_n f_N(ω)`, which over `nN` tends to
`(2∫f_N - ∫f_N)/N` because `qN/n → 1`; the `2N` boundary values are all dominated by the single
integrable observable `G = Σ_{t ≤ 2N} |f_t|` along the orbit, and die by `L1_orbit_decay`. -/
theorem SubadditiveFamily.eventually_shift_lt_of_integral_div_lt (μ : Measure Ω)
    [IsProbabilityMeasure μ] (σ : Ω → Ω) (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily σ f) (hint : ∀ n, Integrable (f n) μ) (N : ℕ) (hN : 1 ≤ N) :
    ∀ᵐ ω ∂μ, ∀ b : ℝ, (∫ x, f N x ∂μ) / N < b →
      ∀ᶠ n in atTop, f n (σ^[n] ω) / (n : ℝ) < b := by
  have hN0 : 0 < N := hN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  -- One integrable observable dominating every boundary value.
  have hGmeas : Measurable (fun y => ∑ t ∈ Finset.range (2 * N + 1), |f t y|) :=
    Finset.measurable_sum _ (fun t _ => (hf.1 t).abs)
  have hGint : Integrable (fun y => ∑ t ∈ Finset.range (2 * N + 1), |f t y|) μ :=
    integrable_finsetSum _ (fun t _ => (hint t).abs)
  have hGle : ∀ s : ℕ, s < 2 * N + 1 → ∀ y : Ω,
      f s y ≤ ∑ t ∈ Finset.range (2 * N + 1), |f t y| := by
    intro s hs y
    refine le_trans (le_abs_self _) ?_
    exact Finset.single_le_sum (f := fun t => |f t y|) (fun t _ => abs_nonneg _)
      (Finset.mem_range.mpr hs)
  -- Index bookkeeping for `q = n/N - 1`.
  have hQ : ∀ n : ℕ, 2 * N ≤ n →
      1 ≤ n / N - 1 ∧ (n / N - 1) * N + N ≤ n + 1 ∧ n ≤ (n / N - 1) * N + 2 * N
        ∧ (n / N - 1) * N ≤ n := by
    intro n hn
    have hd2 : 2 ≤ n / N := (Nat.le_div_iff_mul_le hN0).mpr (by omega)
    have hdN : N ≤ n / N * N :=
      Nat.le_mul_of_pos_left N (lt_of_lt_of_le (by norm_num) hd2)
    have hDeq : (n / N - 1) * N + N = n / N * N := by
      rw [Nat.sub_mul, one_mul, Nat.sub_add_cancel hdN]
    have hle : n / N * N ≤ n := Nat.div_mul_le_self n N
    have hlt : n < n / N * N + N := by
      have h1 : N * (n / N) + n % N = n := Nat.div_add_mod n N
      have h2 : n % N < N := Nat.mod_lt n hN0
      calc n = N * (n / N) + n % N := h1.symm
        _ < N * (n / N) + N := Nat.add_lt_add_left h2 _
        _ = n / N * N + N := by rw [Nat.mul_comm]
    refine ⟨Nat.le_sub_of_add_le (show 1 + 1 ≤ n / N from hd2), ?_, ?_, ?_⟩
    · rw [hDeq]; exact le_trans hle (Nat.le_succ n)
    · have hrw : (n / N - 1) * N + 2 * N = (n / N - 1) * N + N + N := by
        rw [two_mul, Nat.add_assoc]
      rw [hrw, hDeq]
      exact le_of_lt hlt
    · calc (n / N - 1) * N ≤ (n / N - 1) * N + N := Nat.le_add_right _ _
        _ = n / N * N := hDeq
        _ ≤ n := hle
  filter_upwards [ae_tendsto_birkhoffAverage_of_ergodic hσ (f N) (hf.1 N) (hint N),
    L1_orbit_decay μ σ hσ.toMeasurePreserving
      (fun y => ∑ t ∈ Finset.range (2 * N + 1), |f t y|) hGmeas hGint]
    with ω hbirk hGdec
  intro b hb
  -- `qN/n → 1` and `(n + qN)/n → 2`.
  have hQratio : Tendsto (fun n : ℕ => (((n / N - 1) * N : ℕ) : ℝ) / n) atTop (nhds 1) := by
    have hlow : Tendsto (fun n : ℕ => 1 - (2 * N : ℝ) / n) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub (tendsto_const_div_atTop_nhds_zero_nat (2 * N : ℝ))
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
    · filter_upwards [eventually_ge_atTop (2 * N), eventually_gt_atTop 0] with n hn hn0
      obtain ⟨-, -, h3, -⟩ := hQ n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      have h3R : (n : ℝ) ≤ (((n / N - 1) * N : ℕ) : ℝ) + 2 * N := by exact_mod_cast h3
      rw [le_div_iff₀ hnR, show (1 - (2 * N : ℝ) / n) * n = (n : ℝ) - 2 * N from by field_simp]
      linarith
    · filter_upwards [eventually_ge_atTop (2 * N), eventually_gt_atTop 0] with n hn hn0
      obtain ⟨-, -, -, h4⟩ := hQ n hn
      have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
      rw [div_le_one hnR]
      exact_mod_cast h4
  have hAtop : Tendsto (fun n : ℕ => n + (n / N - 1) * N) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n _) tendsto_id
  have hAratio : Tendsto (fun n : ℕ => ((n + (n / N - 1) * N : ℕ) : ℝ) / n) atTop (nhds 2) := by
    have h : Tendsto (fun n : ℕ => (1 : ℝ) + (((n / N - 1) * N : ℕ) : ℝ) / n) atTop
        (nhds ((1 : ℝ) + 1)) := tendsto_const_nhds.add hQratio
    rw [show (1 : ℝ) + 1 = 2 from by norm_num] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hne' : ((n : ℕ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast hn
      exact ne_of_gt this
    push_cast
    field_simp
  -- Bulk term.
  have hSdiv : Tendsto (fun m : ℕ => birkhoffSum σ (f N) m ω / m) atTop
      (nhds (∫ x, f N x ∂μ)) := by simpa only [birkhoffAverage_real] using hbirk
  have hSA : Tendsto (fun n : ℕ => birkhoffSum σ (f N) (n + (n / N - 1) * N) ω / n) atTop
      (nhds (2 * ∫ x, f N x ∂μ)) := by
    have h1 := hSdiv.comp hAtop
    have h2 := h1.mul hAratio
    rw [show (∫ x, f N x ∂μ) * 2 = 2 * ∫ x, f N x ∂μ from by ring] at h2
    refine h2.congr' ?_
    filter_upwards [hAtop.eventually_gt_atTop 0, eventually_gt_atTop 0] with n hAn hn
    have hne : (((n + (n / N - 1) * N : ℕ)) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < (((n + (n / N - 1) * N : ℕ)) : ℝ) := by exact_mod_cast hAn
      exact ne_of_gt this
    have hne' : ((n : ℕ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast hn
      exact ne_of_gt this
    simp only [Function.comp_apply]
    field_simp
  have hbulk : Tendsto (fun n : ℕ =>
      (birkhoffSum σ (f N) (n + (n / N - 1) * N) ω - birkhoffSum σ (f N) n ω)
        / ((n : ℝ) * N)) atTop (nhds ((∫ x, f N x ∂μ) / N)) := by
    have h := (hSA.sub hSdiv).div_const (N : ℝ)
    rw [show (2 * (∫ x, f N x ∂μ) - ∫ x, f N x ∂μ) / N = (∫ x, f N x ∂μ) / N from by ring] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hne' : ((n : ℕ) : ℝ) ≠ 0 := by
      have : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast hn
      exact ne_of_gt this
    field_simp
  -- Boundary terms.
  have hBj : ∀ j : ℕ, Tendsto (fun n : ℕ =>
      (∑ t ∈ Finset.range (2 * N + 1), |f t (σ^[(n + (n / N - 1) * N) + j] ω)|) / n)
      atTop (nhds 0) := by
    intro j
    have hidx : Tendsto (fun n : ℕ => (n + (n / N - 1) * N) + j) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_add_right (n + (n / N - 1) * N) j) hAtop
    have hr : Tendsto (fun n : ℕ => (((n + (n / N - 1) * N) + j : ℕ) : ℝ) / n) atTop
        (nhds 2) := by
      have h : Tendsto (fun n : ℕ =>
          ((n + (n / N - 1) * N : ℕ) : ℝ) / n + (j : ℝ) / n) atTop (nhds (2 + 0)) :=
        hAratio.add (tendsto_const_div_atTop_nhds_zero_nat (j : ℝ))
      rw [add_zero] at h
      refine h.congr' ?_
      filter_upwards [eventually_gt_atTop 0] with n hn
      have hne' : ((n : ℕ) : ℝ) ≠ 0 := by
        have : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast hn
        exact ne_of_gt this
      push_cast
      field_simp
    exact tendsto_orbit_div_of_ratio hGdec (fun n => (n + (n / N - 1) * N) + j) hidx 2 hr
  have hB1 : Tendsto (fun n : ℕ =>
      (∑ j ∈ Finset.range N,
        ∑ t ∈ Finset.range (2 * N + 1), |f t (σ^[(n + (n / N - 1) * N) + j] ω)|)
        / ((n : ℝ) * N)) atTop (nhds 0) := by
    have hsum : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range N,
        (∑ t ∈ Finset.range (2 * N + 1), |f t (σ^[(n + (n / N - 1) * N) + j] ω)|) / n)
        atTop (nhds 0) := by
      rw [show (0 : ℝ) = ∑ _j ∈ Finset.range N, (0 : ℝ) by simp]
      exact tendsto_finsetSum _ (fun j _ => hBj j)
    have h := hsum.div_const (N : ℝ)
    rw [zero_div] at h
    refine h.congr (fun n => ?_)
    rw [← Finset.sum_div, div_div]
  have hB2 : Tendsto (fun n : ℕ =>
      (∑ _j ∈ Finset.range N,
        ∑ t ∈ Finset.range (2 * N + 1), |f t (σ^[n] ω)|) / ((n : ℝ) * N)) atTop (nhds 0) := by
    have hsum : Tendsto (fun n : ℕ => ∑ _j ∈ Finset.range N,
        (∑ t ∈ Finset.range (2 * N + 1), |f t (σ^[n] ω)|) / n) atTop (nhds 0) := by
      rw [show (0 : ℝ) = ∑ _j ∈ Finset.range N, (0 : ℝ) by simp]
      exact tendsto_finsetSum _ (fun _ _ => hGdec)
    have h := hsum.div_const (N : ℝ)
    rw [zero_div] at h
    refine h.congr (fun n => ?_)
    rw [← Finset.sum_div, div_div]
  have hUlim := (hbulk.add hB1).add hB2
  rw [add_zero, add_zero] at hUlim
  filter_upwards [(tendsto_order.mp hUlim).2 b hb, eventually_ge_atTop (2 * N),
    eventually_gt_atTop 0] with n hUn hn2N hn0
  obtain ⟨hq1, hqn, hn3, hn4⟩ := hQ n hn2N
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  refine lt_of_le_of_lt ?_ hUn
  have hkey := hf.nsmul_le_sum_offsets_of_le N (n / N - 1) n hq1 hqn (σ^[n] ω)
  have hblock : ∑ k ∈ Finset.range ((n / N - 1) * N), f N (σ^[k] (σ^[n] ω))
      = birkhoffSum σ (f N) (n + (n / N - 1) * N) ω - birkhoffSum σ (f N) n ω := by
    have h := birkhoffSum_add_right_apply σ (f N) n ((n / N - 1) * N) ω
    have h2 : birkhoffSum σ (f N) ((n / N - 1) * N) (σ^[n] ω)
        = ∑ k ∈ Finset.range ((n / N - 1) * N), f N (σ^[k] (σ^[n] ω)) := rfl
    linarith
  rw [hblock] at hkey
  have hbd1 : ∑ j ∈ Finset.range N, f (n - j - (n / N - 1) * N)
        (σ^[(n / N - 1) * N + j] (σ^[n] ω))
      ≤ ∑ j ∈ Finset.range N,
        ∑ t ∈ Finset.range (2 * N + 1), |f t (σ^[(n + (n / N - 1) * N) + j] ω)| := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    have hidx : (n / N - 1) * N + j + n = n + (n / N - 1) * N + j := by
      rw [Nat.add_right_comm, Nat.add_comm ((n / N - 1) * N) n]
    have hpt : σ^[(n / N - 1) * N + j] (σ^[n] ω) = σ^[(n + (n / N - 1) * N) + j] ω := by
      rw [← Function.iterate_add_apply, hidx]
    rw [hpt]
    refine hGle _ (Nat.lt_succ_of_le ?_) _
    have h1 : n - j - (n / N - 1) * N ≤ n - (n / N - 1) * N := by
      rw [Nat.sub_sub]
      exact Nat.sub_le_sub_left (Nat.le_add_left _ _) n
    have h2 : n - (n / N - 1) * N ≤ 2 * N :=
      Nat.sub_le_iff_le_add.mpr (by rw [Nat.add_comm]; exact hn3)
    exact le_trans h1 h2
  have hbd2 : ∑ j ∈ Finset.range N, f j (σ^[n] ω)
      ≤ ∑ _j ∈ Finset.range N, ∑ t ∈ Finset.range (2 * N + 1), |f t (σ^[n] ω)| := by
    refine Finset.sum_le_sum (fun j hj => ?_)
    have := Finset.mem_range.mp hj
    exact hGle _ (by omega) _
  have hfinal : ∀ x y z w : ℝ, (N : ℝ) * w ≤ x + y + z →
      w / (n : ℝ) ≤ x / ((n : ℝ) * N) + y / ((n : ℝ) * N) + z / ((n : ℝ) * N) := by
    intro x y z w h
    rw [← add_div, ← add_div, div_le_div_iff₀ hnR (by positivity)]
    calc w * ((n : ℝ) * N) = ((N : ℝ) * w) * n := by ring
      _ ≤ (x + y + z) * n := mul_le_mul_of_nonneg_right h hnR.le
  exact hfinal _ _ _ _ (by linarith)

/-- **Lemma \ref{easyking}.** `(1/n) f_{n→2n} → C = lim (1/n) ∫ f_n` for any `L¹`
subadditive family, ergodicity assumed but invertibility of the base not required for
`f_{n → 2n} = f_n ∘ σ^n`. -/
theorem easyking_of_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → Ω)
    (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily σ f) (hL1 : ∀ n, Integrable (f n) μ) (C : EReal)
    (hC : Tendsto (fun n => ((∫ ω, f n ω ∂μ) / n : EReal)) atTop (nhds C)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => (f n (σ^[n] ω) / n : EReal)) atTop (nhds C) := by
  -- **Lower bound.**  This is the paper's "immediately clear" step.  Spelled out, it genuinely
  -- uses the *pointwise* a.e. convergence `f_n(ω)/n → C`, i.e. classical Kingman at the base point:
  -- the subadditive rearrangement `f_n(σ^n ω) ≥ f_{2n}(ω) - f_n(ω)` needs a *lower* bound on
  -- `f_{2n}(ω)/(2n)`, which is exactly the hard (liminf) direction — no bound from Fekete + orbit
  -- decay is sharp enough.  We reduce it to `kingman` (proved in `ProofMet.Kingman.Core`).
  obtain ⟨C', hC'top, hC'ae, -, hC'mean⟩ := kingman μ σ hσ f hf ((hL1 1).sup (integrable_const 0))
  have hC'int := tendsto_mean_of_lowerIntegral hL1 hC'mean
  have hCC' : C' = C := tendsto_nhds_unique hC'int hC
  rw [hCC'] at hC'ae hC'top
  -- `hC'ae : ∀ᵐ ω, Tendsto (fun n => f n ω / n) atTop (nhds C)`.
  --
  -- **Upper bound `limsup f_n(σ^n ω)/n ≤ C`.**
  -- The paper splits `[n, 2n)` into a length-`j` boundary, `⌊n/N⌋` blocks of length `N`, and a
  -- final boundary, applies subadditivity, and averages over the offset `j ∈ [0, N)`.  The boundary
  -- terms are `O(1/n)·(S_N|f_1| ∘ σ^n)` and vanish a.e. by the L¹ orbit-decay fact; the bulk term,
  -- after the `j`-average, telescopes to `(S_{2n} f_N(ω) - S_n f_N(ω))/(nN)` at the base point and
  -- so tends a.e. to `∫ f_N / N ≤ C + ε`.  Both ingredients are Birkhoff's theorem for a single L¹
  -- The observable is handled by `ae_tendsto_birkhoffAverage`
  -- in `ProofMet.Birkhoff`.  The block combinatorics are `eventually_shift_lt_of_integral_div_lt`,
  -- and the whole bound is discharged below.
  have hupper : ∀ᵐ ω ∂μ, ∀ b : ℝ, C < (b : EReal) →
      ∀ᶠ n in atTop, f n (σ^[n] ω) / (n : ℝ) < b := by
    -- `C = inf_N ∫f_N/N` (Fekete), so any real `b > C` is already beaten at some scale `N`;
    -- at that scale `eventually_shift_lt_of_integral_div_lt` supplies the block bound.
    have hall : ∀ᵐ ω ∂μ, ∀ N : ℕ, ∀ b : ℝ, 1 ≤ N → (∫ x, f N x ∂μ) / N < b →
        ∀ᶠ n in atTop, f n (σ^[n] ω) / (n : ℝ) < b := by
      refine ae_all_iff.mpr (fun N => ?_)
      by_cases hN : 1 ≤ N
      · filter_upwards [hf.eventually_shift_lt_of_integral_div_lt μ σ hσ f hL1 N hN] with ω hω
        intro b _ hb
        exact hω b hb
      · filter_upwards with ω b h
        exact absurd h hN
    filter_upwards [hall] with ω hω
    intro b hb
    obtain ⟨N, hN1, hNb⟩ : ∃ N : ℕ, 1 ≤ N ∧ (∫ x, f N x ∂μ) / N < b := by
      have hCm : Tendsto (fun n : ℕ => (((∫ ω, f n ω ∂μ) / n : ℝ) : EReal)) atTop (nhds C) := by
        simpa only [coe_div_natCast] using hC
      obtain ⟨N, h1, h2⟩ := (((tendsto_order.mp hCm).2 (b : EReal) hb).and
        (eventually_ge_atTop 1)).exists
      exact ⟨N, h2, by exact_mod_cast h1⟩
    exact hω N b hN1 hNb
  -- Assemble: `C ≤ liminf` (lower) and `limsup ≤ C` (upper) give convergence to `C`.
  --
  -- With `C : EReal` the assembly can no longer be pure real arithmetic (`EReal` is not a ring:
  -- `2 * C`, `2 * C - C = C` are not available at `⊥`).  Instead we verify the two halves of
  -- `tendsto_order` in `EReal` directly, unwrapping to `ℝ` exactly where the real argument is
  -- needed.  The point is that the *lower* half already forces `C` to be finite: an `a < C`
  -- witnesses `C ≠ ⊥`, and `hC'top` gives `C ≠ ⊤`, so the real Kingman limit is available there.
  -- In the degenerate case `C = ⊥` the lower half is vacuous and only `hupper` is used.
  filter_upwards [hC'ae, hupper] with ω hae hup
  simp only [coe_div_natCast] at hae ⊢
  rw [tendsto_order]
  constructor
  · -- Lower half: `∀ a < C, eventually a < f_n(σⁿω)/n`.
    intro a ha
    -- `a < C` rules out `C = ⊥`, and `hC'top` rules out `C = ⊤`; so `C` is a real number.
    obtain ⟨c, rfl⟩ : ∃ c : ℝ, C = (c : EReal) := by
      cases C with
      | bot => exact absurd ha not_lt_bot
      | top => exact absurd hC'top (lt_irrefl _)
      | coe c => exact ⟨c, rfl⟩
    have haeR : Tendsto (fun n => f n ω / (n : ℝ)) atTop (nhds c) := EReal.tendsto_coe.1 hae
    cases a with
    | bot => exact .of_forall fun n => EReal.bot_lt_coe _
    | top => exact absurd ha (by simp)
    | coe a =>
      have ha : a < c := EReal.coe_lt_coe_iff.1 ha
      -- Lower-bounding sequence `a_n = (f_{2n}(ω) - f_n(ω))/n → 2c - c = c`.
      have h2 : Tendsto (fun n : ℕ => 2 * n) atTop atTop :=
        tendsto_atTop_mono (fun n => by change n ≤ 2 * n; omega) tendsto_id
      have hb2 : Tendsto (fun n => f (2 * n) ω / ((2 * n : ℕ) : ℝ)) atTop (nhds c) :=
        haeR.comp h2
      have hb2' : Tendsto (fun n => f (2 * n) ω / (n : ℝ)) atTop (nhds (2 * c)) := by
        refine (hb2.const_mul (2 : ℝ)).congr' ?_
        filter_upwards [eventually_gt_atTop 0] with n hn
        have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
        push_cast
        field_simp
      have hlim : Tendsto (fun n => (f (2 * n) ω - f n ω) / (n : ℝ)) atTop (nhds c) := by
        have h := hb2'.sub haeR
        rw [show (2 : ℝ) * c - c = c by ring] at h
        exact h.congr (fun n => (sub_div _ _ _).symm)
      filter_upwards [(tendsto_order.mp hlim).1 a ha, eventually_gt_atTop 0] with n hn_lt hn_pos
      rw [EReal.coe_lt_coe_iff]
      have hsub : f (2 * n) ω ≤ f n (σ^[n] ω) + f n ω := by
        have := hf.2 n n ω; rwa [← two_mul] at this
      refine lt_of_lt_of_le hn_lt ?_
      gcongr
      linarith [hsub]
  · -- Upper half: `∀ b > C, eventually f_n(σⁿω)/n < b`.  For `b = ⊤` this is automatic (the
    -- sequence is real-valued); for real `b` it is exactly `hupper`.
    intro b hb
    cases b with
    | bot => exact absurd hb not_lt_bot
    | top => exact .of_forall fun n => EReal.coe_lt_top _
    | coe b =>
      filter_upwards [hup b hb] with n hn
      exact EReal.coe_lt_coe hn

/-!
## Real-valued repackagings

`kingman_of_integrable`, `kingman_backward_of_integrable` and `easyking_of_integrable`
state their limit constant
in `EReal`, since a
subadditive family's mean genuinely may diverge to `-∞`.  Most call sites downstream, however,
already carry a *real* constant `C` together with the real mean-convergence
`(1/n) ∫ f_n → C`, which pins the `EReal` constant to `(C : EReal)` and so rules out the `-∞`
case.  The three wrappers below do that identification once, so those call sites can keep
working with ordinary real-valued `Tendsto`.

The rewrite `coe_div_natCast` is what makes each of them short: it moves the coercion
syntactically outermost, which is what `EReal.tendsto_coe` needs in order to fire.
-/

/-- The `EReal` form of a real mean-convergence hypothesis, as `kingman` and friends want it. -/
theorem tendsto_mean_coe {m : ℕ → ℝ} {C : ℝ}
    (hC : Tendsto (fun n => m n / n) atTop (nhds C)) :
    Tendsto (fun n => ((m n : EReal) / (n : EReal))) atTop (nhds (C : EReal)) := by
  simp only [coe_div_natCast]
  exact EReal.tendsto_coe.2 hC

/-- **Kingman**, real-valued: given the real mean-convergence `(1/n) ∫ f_n → C`, the a.e.
pointwise limit is that same real `C`. -/
theorem kingman_real_of_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → Ω)
    (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily σ f) (hL1 : ∀ n, Integrable (f n) μ) (C : ℝ)
    (hC : Tendsto (fun n => (∫ ω, f n ω ∂μ) / n) atTop (nhds C)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n ω / n) atTop (nhds C) := by
  obtain ⟨C', -, hae, -, hmean⟩ := kingman μ σ hσ f hf ((hL1 1).sup (integrable_const 0))
  have hint := tendsto_mean_of_lowerIntegral hL1 hmean
  have hC' : C' = (C : EReal) := tendsto_nhds_unique hint (tendsto_mean_coe hC)
  filter_upwards [hae] with ω hω
  rw [hC'] at hω
  simp only [coe_div_natCast] at hω
  exact EReal.tendsto_coe.1 hω

/-- **Backward Kingman**, real-valued (see `kingman_real_of_integrable`). -/
theorem kingman_backward_real_of_integrable (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω ≃ᵐ Ω)
    (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ)
    (hf : SubadditiveFamily σ f) (hL1 : ∀ n, Integrable (f n) μ) (C : ℝ)
    (hC : Tendsto (fun n => (∫ ω, f n ω ∂μ) / n) atTop (nhds C)) :
    ∀ᵐ ω ∂μ, Tendsto (fun n => f n (zIter σ (-n) ω) / n) atTop (nhds C) := by
  filter_upwards [kingman_backward_of_integrable μ σ hσ f hf hL1
    (C : EReal) (tendsto_mean_coe hC)] with ω hω
  simp only [coe_div_natCast] at hω
  exact EReal.tendsto_coe.1 hω

/-- **Kingman for the shifted averages `f_n(σⁿω)/n`, under the general hypothesis.**

The `L¹` form is `easyking_of_integrable`. As with `kingman`, the extension is by truncation: the
`L¹` theorem applied to `gᴹ = max(f, -M·)` gives `max (f_n(σⁿω)/n) (-M) → c M` for the *same*
constants `c M` that `exists_truncation_limits` produces, and `ae_tendsto_of_ae_tendsto_max`
takes `M → ∞`. Nothing about the one-sided argument has to be redone. -/
theorem easyking (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω → Ω)
    (hσ : Ergodic σ μ) (f : ℕ → Ω → ℝ) (hf : SubadditiveFamily σ f)
    (h1 : Integrable (fun ω => max (f 1 ω) 0) μ) :
    ∃ C : EReal, C < ⊤ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (f n (σ^[n] ω) / n : EReal)) atTop (nhds C)) ∧
      Tendsto (fun n : ℕ => lowerIntegral μ (fun ω => f n ω / n)) atTop (nhds C) := by
  have hmp : MeasurePreserving σ μ μ := hσ.toMeasurePreserving
  obtain ⟨c, hcanti, hcmean, -, -, hmean⟩ := hf.exists_truncation_limits hσ h1
  have hF : SubadditiveFamily σ (Function.update f 0 0) := hf.update_zero
  have hFeq : ∀ {n : ℕ}, 1 ≤ n → Function.update f 0 0 n = f n :=
    fun {n} hn => SubadditiveFamily.update_zero_apply f hn
  have hstep : ∀ M : ℕ, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => max (f n (σ^[n] ω) / n) (-(M : ℝ))) atTop (nhds (c M)) := by
    intro M
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hint := fun n => hf.truncate_integrable_update hmp h1 (M : ℝ) hM0 n
    have hCM : Tendsto (fun n : ℕ =>
        ((∫ ω, SubadditiveFamily.truncate (Function.update f 0 0) (M : ℝ) n ω ∂μ) / n : EReal))
        atTop (nhds ((c M : ℝ) : EReal)) := by
      simp only [coe_div_natCast]
      exact EReal.tendsto_coe.2 (hcmean M)
    have hres := easyking_of_integrable μ σ hσ
      (SubadditiveFamily.truncate (Function.update f 0 0) (M : ℝ))
      (hF.truncate_subadditive (M : ℝ)) hint ((c M : ℝ) : EReal) hCM
    filter_upwards [hres] with ω hω
    have hω' : Tendsto (fun n : ℕ =>
        SubadditiveFamily.truncate (Function.update f 0 0) (M : ℝ) n (σ^[n] ω) / n) atTop
        (nhds (c M)) := by
      refine EReal.tendsto_coe.1 ?_
      simpa only [coe_div_natCast] using hω
    refine Filter.Tendsto.congr' ?_ hω'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [SubadditiveFamily.truncate_div _ hM0 n (σ^[n] ω), hFeq hn]
  exact ⟨⨅ M : ℕ, (c M : EReal), lt_of_le_of_lt (iInf_le _ 0) (EReal.coe_lt_top _),
    ae_tendsto_of_ae_tendsto_max hcanti hstep, hmean⟩

/-- **Backward Kingman, under the general hypothesis.** The `L¹` form is
`kingman_backward_of_integrable`; the extension is the same truncation argument as `easyking`. -/
theorem kingman_backward (μ : Measure Ω) [IsProbabilityMeasure μ] (σ : Ω ≃ᵐ Ω)
    (hσ : Ergodic (⇑σ) μ) (f : ℕ → Ω → ℝ) (hf : SubadditiveFamily (⇑σ) f)
    (h1 : Integrable (fun ω => max (f 1 ω) 0) μ) :
    ∃ C : EReal, C < ⊤ ∧
      (∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => (f n (zIter σ (-n) ω) / n : EReal)) atTop (nhds C)) ∧
      Tendsto (fun n : ℕ => lowerIntegral μ (fun ω => f n ω / n)) atTop (nhds C) := by
  have hmp : MeasurePreserving (⇑σ) μ μ := hσ.toMeasurePreserving
  obtain ⟨c, hcanti, hcmean, -, -, hmean⟩ := hf.exists_truncation_limits hσ h1
  have hF : SubadditiveFamily (⇑σ) (Function.update f 0 0) := hf.update_zero
  have hFeq : ∀ {n : ℕ}, 1 ≤ n → Function.update f 0 0 n = f n :=
    fun {n} hn => SubadditiveFamily.update_zero_apply f hn
  have hstep : ∀ M : ℕ, ∀ᵐ ω ∂μ,
      Tendsto (fun n : ℕ => max (f n (zIter σ (-n) ω) / n) (-(M : ℝ))) atTop (nhds (c M)) := by
    intro M
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have hint := fun n => hf.truncate_integrable_update hmp h1 (M : ℝ) hM0 n
    have hCM : Tendsto (fun n : ℕ =>
        ((∫ ω, SubadditiveFamily.truncate (Function.update f 0 0) (M : ℝ) n ω ∂μ) / n : EReal))
        atTop (nhds ((c M : ℝ) : EReal)) := by
      simp only [coe_div_natCast]
      exact EReal.tendsto_coe.2 (hcmean M)
    have hres := kingman_backward_of_integrable μ σ hσ
      (SubadditiveFamily.truncate (Function.update f 0 0) (M : ℝ))
      (hF.truncate_subadditive (M : ℝ)) hint ((c M : ℝ) : EReal) hCM
    filter_upwards [hres] with ω hω
    have hω' : Tendsto (fun n : ℕ =>
        SubadditiveFamily.truncate (Function.update f 0 0) (M : ℝ) n (zIter σ (-n) ω) / n) atTop
        (nhds (c M)) := by
      refine EReal.tendsto_coe.1 ?_
      simpa only [coe_div_natCast] using hω
    refine Filter.Tendsto.congr' ?_ hω'
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [SubadditiveFamily.truncate_div _ hM0 n (zIter σ (-n) ω), hFeq hn]
  exact ⟨⨅ M : ℕ, (c M : EReal), lt_of_le_of_lt (iInf_le _ 0) (EReal.coe_lt_top _),
    ae_tendsto_of_ae_tendsto_max hcanti hstep, hmean⟩

end MultiplicativeErgodic
