/-
Copyright (c) 2026 Lukas Niebel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lukas Niebel
-/

module

public import LeanPool.FastDynamo.Local.SeedParameters
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Diffusivity intervals and horizontal scales

This file formalises the arithmetic construction in Section 3.2 of the paper.  The local
data are fixed first.  We then
choose a single ratio `1 < q < √(δ₊/δ₋)`, and only after that choose
the initial integer Fourier index `K0`, so large that `q + K0⁻¹ < √(δ₊/δ₋)`.
The latter choice can be made above any prescribed
natural-number lower bound, as required when later estimates enlarge `K0`; every
such enlargement preserves the rounding bound (the sentence after `eq:ratio-choice`,
`ScaleFamily.rounding_bound_of_le`).

For the rounded recursion

`K (n + 1) = Nat.ceil (q * K n)`

we prove `eq:ratio-choice` in its three-part form

`q ≤ K_{n+1} / K_n ≤ q + 1/K0 < √(δ₊/δ₋)`,

exact axial-wavenumber matching, overlap of adjacent diffusivity intervals, and
the covering identity

`(⋃ n, diffusivityInterval n) = Set.Ioc 0 epsilon0`.

The paper says *horizontal* where the Lean identifiers say `transverse`; the two words mean
the same.
-/

@[expose] public section

noncomputable section

namespace FastDynamo

/-- The single geometric ratio chosen after the local instability data and
before the base Fourier index (§3.1, §3.2). -/
structure ScaleRatios (p : LocalSeedParameters) where
  /-- Lower target for every adjacent integer-frequency ratio. -/
  q : ℝ
  one_lt_q : 1 < q
  /-- `q < √(δ₊/δ₋)`: the ceiling that leaves room for the rounding loss `1/K0`
  and keeps consecutive diffusivity intervals overlapping. -/
  q_lt_scaleRatioCeiling : q < p.scaleRatioCeiling

namespace ScaleRatios

variable {p : LocalSeedParameters} (r : ScaleRatios p)

/-- The lower ratio target `q` is positive, since it exceeds `1`. -/
theorem q_pos : 0 < r.q :=
  zero_lt_one.trans r.one_lt_q

/-- The local diffusivity window always admits a ratio with the strict
inequalities required in Section 3.2. -/
theorem exists_for (p : LocalSeedParameters) : Nonempty (ScaleRatios p) := by
  obtain ⟨q, hq_one, hq_ceiling⟩ := p.exists_scaleRatios
  exact ⟨⟨q, hq_one, hq_ceiling⟩⟩

end ScaleRatios

/-- A final choice of the base integer Fourier index.  The rounding bound
`q + K0⁻¹ < √(δ₊/δ₋)` is the only Section 3.2 condition on `K0`;
later stages may impose additional monotone lower bounds before constructing
this structure, and every such enlargement preserves the bound
(`ScaleFamily.rounding_bound_of_le`). -/
structure ScaleFamily {p : LocalSeedParameters} (r : ScaleRatios p) where
  /-- Initial positive integer Fourier index. -/
  K0 : ℕ
  K0_pos : 0 < K0
  rounding_bound : r.q + (K0 : ℝ)⁻¹ < p.scaleRatioCeiling

namespace ScaleFamily

variable {p : LocalSeedParameters} {r : ScaleRatios p}

/-- `K0` can be chosen above any lower bound while retaining the rounding
estimate.  This is the form needed to preserve the paper's parameter order. -/
theorem exists_ge (r : ScaleRatios p) (M : ℕ) :
    ∃ f : ScaleFamily r, M ≤ f.K0 := by
  let gap : ℝ := p.scaleRatioCeiling - r.q
  have hgap : 0 < gap := by
    dsimp [gap]
    linarith [r.q_lt_scaleRatioCeiling]
  obtain ⟨K0, hK0⟩ := exists_nat_gt (max gap⁻¹ (M : ℝ))
  have hinv_lt_K0 : gap⁻¹ < (K0 : ℝ) :=
    (le_max_left _ _).trans_lt hK0
  have hM_lt_K0 : (M : ℝ) < (K0 : ℝ) :=
    (le_max_right _ _).trans_lt hK0
  have hK0_real_pos : 0 < (K0 : ℝ) := by
    exact (inv_pos.2 hgap).trans hinv_lt_K0
  have hK0_pos : 0 < K0 := by
    exact_mod_cast hK0_real_pos
  have hreciprocal : (K0 : ℝ)⁻¹ < gap := by
    exact (inv_lt_comm₀ hK0_real_pos hgap).2 hinv_lt_K0
  refine ⟨⟨K0, hK0_pos, ?_⟩, ?_⟩
  · dsimp [gap] at hreciprocal
    linarith
  · exact_mod_cast hM_lt_K0.le

/-- "Every subsequent enlargement of `K_0` preserves the inequalities" (§3.2, after
`eq:ratio-choice`):
the rounding bound `q + K⁻¹ < √(δ₊/δ₋)` persists for every `K ≥ K0`, because
`K ↦ K⁻¹` is decreasing.  This is what makes the later monotone lower bounds on
`K0` harmless. -/
theorem rounding_bound_of_le (f : ScaleFamily r) {K : ℕ} (hK : f.K0 ≤ K) :
    r.q + (K : ℝ)⁻¹ < p.scaleRatioCeiling := by
  have hK0 : (0 : ℝ) < (f.K0 : ℝ) := Nat.cast_pos.2 f.K0_pos
  have hKpos : (0 : ℝ) < (K : ℝ) :=
    hK0.trans_le (by exact_mod_cast hK)
  have hinv : (K : ℝ)⁻¹ ≤ (f.K0 : ℝ)⁻¹ :=
    (inv_le_inv₀ hKpos hK0).2 (by exact_mod_cast hK)
  linarith [f.rounding_bound]

/-- The rounded positive integer Fourier indices. -/
def fourierIndex (f : ScaleFamily r) : ℕ → ℕ
  | 0 => f.K0
  | n + 1 => Nat.ceil (r.q * (fourierIndex f n : ℝ))

/-- The recursion starts at the chosen base index: `K_0` is `f.K0`. -/
@[simp]
theorem fourierIndex_zero (f : ScaleFamily r) : f.fourierIndex 0 = f.K0 :=
  rfl

/-- The defining recursion for the integer Fourier indices, `K_{n+1} = ⌈q K_n⌉`
(Section 3.2). -/
@[simp]
theorem fourierIndex_succ (f : ScaleFamily r) (n : ℕ) :
    f.fourierIndex (n + 1) = Nat.ceil (r.q * (f.fourierIndex n : ℝ)) :=
  rfl

/-- Every index in the family is positive, by induction from `0 < K0` and positivity of the
ceiling of a positive real. -/
theorem fourierIndex_pos (f : ScaleFamily r) : ∀ n, 0 < f.fourierIndex n
  | 0 => f.K0_pos
  | n + 1 => by
      rw [fourierIndex_succ]
      exact Nat.ceil_pos.2
        (mul_pos r.q_pos (Nat.cast_pos.2 (fourierIndex_pos f n)))

/-- The index sequence strictly increases at each step, `K_n < K_{n+1}`, because `q > 1` and
rounding up does not decrease the product. -/
theorem fourierIndex_strictMono_step (f : ScaleFamily r) (n : ℕ) :
    f.fourierIndex n < f.fourierIndex (n + 1) := by
  have hKn : 0 < (f.fourierIndex n : ℝ) :=
    Nat.cast_pos.2 (f.fourierIndex_pos n)
  have hqKn : (f.fourierIndex n : ℝ) <
      r.q * (f.fourierIndex n : ℝ) := by
    nlinarith [r.one_lt_q]
  have hceil : r.q * (f.fourierIndex n : ℝ) ≤
      (f.fourierIndex (n + 1) : ℝ) := by
    rw [fourierIndex_succ]
    exact Nat.le_ceil _
  exact_mod_cast hqKn.trans_le hceil

/-- Every index dominates the base index, `K0 ≤ K_n`, by induction from strict monotonicity. -/
theorem K0_le_fourierIndex (f : ScaleFamily r) (n : ℕ) :
    f.K0 ≤ f.fourierIndex n := by
  induction n with
  | zero => simp
  | succ n ih =>
      exact ih.trans (f.fourierIndex_strictMono_step n).le

/-- The index sequence grows at least by one per step: `K0 + n ≤ K_n`. -/
theorem add_le_fourierIndex (f : ScaleFamily r) (n : ℕ) :
    f.K0 + n ≤ f.fourierIndex n := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hstep := f.fourierIndex_strictMono_step n
      omega

/-- Lower half of `eq:ratio-choice`: `q ≤ K_{n+1} / K_n`, because `K_{n+1} = ⌈q K_n⌉` is at
least `q K_n` (Section 3.2).  This is the bound behind `r_m ≥ q` for `m < n` and
`r_m ≤ q⁻¹` for `m > n` in the proof of `prop:background-resolvent`, which separates the axial
shifts of distinct cells. -/
theorem adjacent_ratio_lower (f : ScaleFamily r) (n : ℕ) :
    r.q ≤ (f.fourierIndex (n + 1) : ℝ) / f.fourierIndex n := by
  have hKn : 0 < (f.fourierIndex n : ℝ) :=
    Nat.cast_pos.2 (f.fourierIndex_pos n)
  apply (le_div_iff₀ hKn).2
  rw [fourierIndex_succ]
  exact Nat.le_ceil _

/-- Upper half of `eq:ratio-choice`: `K_{n+1} / K_n ≤ q + 1 / K0`, since the ceiling overshoots
by less than `1` and `K0 ≤ K_n` (Section 3.2).  Together with the family's
rounding bound this is the bound that rules out gaps between consecutive diffusivity intervals.
-/
theorem adjacent_ratio_upper (f : ScaleFamily r) (n : ℕ) :
    (f.fourierIndex (n + 1) : ℝ) / f.fourierIndex n ≤
      r.q + (f.K0 : ℝ)⁻¹ := by
  have hKn : 0 < (f.fourierIndex n : ℝ) :=
    Nat.cast_pos.2 (f.fourierIndex_pos n)
  have hK0 : 0 < (f.K0 : ℝ) := Nat.cast_pos.2 f.K0_pos
  have hceil : (f.fourierIndex (n + 1) : ℝ) <
      r.q * (f.fourierIndex n : ℝ) + 1 := by
    rw [fourierIndex_succ]
    exact Nat.ceil_lt_add_one (mul_nonneg r.q_pos.le hKn.le)
  have hratio : (f.fourierIndex (n + 1) : ℝ) / f.fourierIndex n <
      r.q + (f.fourierIndex n : ℝ)⁻¹ := by
    apply (div_lt_iff₀ hKn).2
    field_simp
    simpa [mul_add] using hceil
  have hinv : (f.fourierIndex n : ℝ)⁻¹ ≤ (f.K0 : ℝ)⁻¹ := by
    exact (inv_le_inv₀ hKn hK0).2 (by exact_mod_cast f.K0_le_fourierIndex n)
  linarith

/-- **`eq:ratio-choice`** in full (Section 3.2):
`q ≤ K_{n+1} / K_n ≤ q + 1/K0 < √(δ₊/δ₋)`.  The first two bounds are
`adjacent_ratio_lower` and `adjacent_ratio_upper`; the last one is the family's rounding
condition.  This is the property that makes every consecutive pair of diffusivity intervals
overlap. -/
theorem adjacent_ratio_bounds (f : ScaleFamily r) (n : ℕ) :
    r.q ≤ (f.fourierIndex (n + 1) : ℝ) / f.fourierIndex n ∧
      (f.fourierIndex (n + 1) : ℝ) / f.fourierIndex n ≤ r.q + (f.K0 : ℝ)⁻¹ ∧
      r.q + (f.K0 : ℝ)⁻¹ < p.scaleRatioCeiling :=
  ⟨f.adjacent_ratio_lower n, f.adjacent_ratio_upper n, f.rounding_bound⟩

/-- The squared form of the rounding bound, `(q + 1/K0)² < δ₊/δ₋`, obtained by squaring
`eq:ratio-choice` against the ceiling `√(δ₊/δ₋)` (as in §3.2).  This is the shape
consumed by the diffusivity-interval overlap. -/
theorem adjacent_ratio_sq_lt (f : ScaleFamily r) :
    (r.q + (f.K0 : ℝ)⁻¹) ^ 2 < p.deltaPlus / p.deltaMinus := by
  have hnonneg : 0 ≤ r.q + (f.K0 : ℝ)⁻¹ :=
    add_nonneg r.q_pos.le (inv_nonneg.2 (Nat.cast_nonneg _))
  have hsq : (r.q + (f.K0 : ℝ)⁻¹) ^ 2 <
      (Real.sqrt (p.deltaPlus / p.deltaMinus)) ^ 2 :=
    (sq_lt_sq₀ hnonneg (Real.sqrt_nonneg _)).2 f.rounding_bound
  rwa [Real.sq_sqrt (zero_le_one.trans p.one_lt_deltaRatio.le)] at hsq

/-- Horizontal (`transverse`) core scale `ell n = kStar / K n` (§3.2). -/
def ell (f : ScaleFamily r) (n : ℕ) : ℝ :=
  (p.kStar : ℝ) / f.fourierIndex n

/-- Every horizontal core scale `ell n = kStar / K_n` is positive. -/
theorem ell_pos (f : ScaleFamily r) (n : ℕ) : 0 < f.ell n := by
  exact div_pos (Nat.cast_pos.2 p.kStar_pos)
    (Nat.cast_pos.2 (f.fourierIndex_pos n))

/-- Unfolding of the core scale: `ell n = kStar / K_n` (Section 3.2, where the
display reads `ell_n = 1/K_n`: the Lean keeps `k_*` as a parameter, the paper takes
`k_* = 1`). -/
theorem ell_formula (f : ScaleFamily r) (n : ℕ) :
    f.ell n = (p.kStar : ℝ) / f.fourierIndex n :=
  rfl

/-- Every scale has exactly the local model's axial wavenumber, `2π K_n ell_n = N`.  The
paper sets `ell_n = 1/K_n` (§3.2), so `K_n ell_n = 1`; with `k_*` kept as a Lean parameter the
identity reads `2π K_n ell_n = 2π k_* = N`, which is the `k_*`-general form of the paper's
`k_* = 1` statement. -/
theorem axial_wavenumber_match (f : ScaleFamily r) (n : ℕ) :
    2 * Real.pi * (f.fourierIndex n : ℝ) * f.ell n = p.wavenumber := by
  unfold ell LocalSeedParameters.wavenumber
  have hKn : (f.fourierIndex n : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.2 (f.fourierIndex_pos n))
  field_simp

/-- Physical diffusivities for which the `n`th rescaled cell lies in the
local admissible window, `eq:diffusivity-intervals`. -/
def diffusivityInterval (f : ScaleFamily r) (n : ℕ) : Set ℝ :=
  Set.Icc (p.deltaMinus * f.ell n ^ 2) (p.deltaPlus * f.ell n ^ 2)

/-- Largest physical diffusivity covered by the scale family. -/
def epsilon0 (f : ScaleFamily r) : ℝ :=
  p.deltaPlus * f.ell 0 ^ 2

/-- The threshold diffusivity in terms of the base index: `epsilon0 = deltaPlus kStar² / K0²`
(§3.2, where it reads `ε₀ = δ₊/K₀²`: the Lean keeps `k_*` as a parameter, the
paper takes `k_* = 1`). -/
theorem epsilon0_formula (f : ScaleFamily r) :
    f.epsilon0 =
      p.deltaPlus * (p.kStar : ℝ) ^ 2 / (f.K0 : ℝ) ^ 2 := by
  simp only [epsilon0, ell, fourierIndex_zero, div_pow]
  ring

/-- The threshold diffusivity is positive, so the covered range `(0, epsilon0]` is nonempty. -/
theorem epsilon0_pos (f : ScaleFamily r) : 0 < f.epsilon0 := by
  exact mul_pos p.deltaPlus_pos (sq_pos_of_pos (f.ell_pos 0))

/-- The core scales are largest at `n = 0`: `ell n ≤ ell 0`, since `K0 ≤ K_n`. -/
theorem ell_le_ell_zero (f : ScaleFamily r) (n : ℕ) :
    f.ell n ≤ f.ell 0 := by
  unfold ell
  have hk : 0 ≤ (p.kStar : ℝ) := (Nat.cast_nonneg _)
  have hK0 : 0 < (f.K0 : ℝ) := Nat.cast_pos.2 f.K0_pos
  simpa using div_le_div_of_nonneg_left hk hK0
    (show (f.K0 : ℝ) ≤ (f.fourierIndex n : ℝ) by
      exact_mod_cast f.K0_le_fourierIndex n)

/-- The upper endpoint of every diffusivity interval lies below the threshold `epsilon0`, so the
whole family of intervals is contained in `(0, epsilon0]`. -/
theorem interval_upper_le_epsilon0 (f : ScaleFamily r) (n : ℕ) :
    p.deltaPlus * f.ell n ^ 2 ≤ f.epsilon0 := by
  have hsquares : f.ell n ^ 2 ≤ f.ell 0 ^ 2 :=
    (sq_le_sq₀ (f.ell_pos n).le (f.ell_pos 0).le).2 (f.ell_le_ell_zero n)
  exact mul_le_mul_of_nonneg_left hsquares p.deltaPlus_pos.le

/-- Adjacent closed diffusivity intervals overlap (in fact, their overlap has positive length
because `eq:ratio-choice` is strict at its last step).  This is the paper's computation after
`eq:diffusivity-intervals`, run with the upper ratio bound `q + 1/K0` of `eq:ratio-choice`. -/
theorem neighboring_intervals_overlap (f : ScaleFamily r) (n : ℕ) :
    p.deltaMinus * f.ell n ^ 2 <
      p.deltaPlus * f.ell (n + 1) ^ 2 := by
  let A : ℝ := f.fourierIndex n
  let B : ℝ := f.fourierIndex (n + 1)
  let Q : ℝ := r.q + (f.K0 : ℝ)⁻¹
  have hA : 0 < A := Nat.cast_pos.2 (f.fourierIndex_pos n)
  have hB : 0 < B := Nat.cast_pos.2 (f.fourierIndex_pos (n + 1))
  have hQ_nonneg : 0 ≤ Q :=
    add_nonneg r.q_pos.le (inv_nonneg.2 (Nat.cast_nonneg _))
  have hB_le : B ≤ Q * A := by
    exact (div_le_iff₀ hA).1 (f.adjacent_ratio_upper n)
  have hqA_nonneg : 0 ≤ Q * A :=
    mul_nonneg hQ_nonneg hA.le
  have hBsq : B ^ 2 ≤ (Q * A) ^ 2 :=
    (sq_le_sq₀ hB.le hqA_nonneg).2 hB_le
  have hdelta : p.deltaMinus * Q ^ 2 < p.deltaPlus := by
    simpa [mul_comm] using
      (lt_div_iff₀ p.deltaMinus_pos).1 f.adjacent_ratio_sq_lt
  have hcross : p.deltaMinus * B ^ 2 < p.deltaPlus * A ^ 2 := by
    calc
      p.deltaMinus * B ^ 2 ≤ p.deltaMinus * (Q * A) ^ 2 :=
        mul_le_mul_of_nonneg_left hBsq p.deltaMinus_pos.le
      _ = (p.deltaMinus * Q ^ 2) * A ^ 2 := by ring
      _ < p.deltaPlus * A ^ 2 :=
        mul_lt_mul_of_pos_right hdelta (sq_pos_of_pos hA)
  unfold ell
  rw [div_pow, div_pow]
  change p.deltaMinus * ((p.kStar : ℝ) ^ 2 / A ^ 2) <
    p.deltaPlus * ((p.kStar : ℝ) ^ 2 / B ^ 2)
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (div_lt_div_iff₀ (sq_pos_of_pos hA) (sq_pos_of_pos hB)).2
  have hkSq : 0 < (p.kStar : ℝ) ^ 2 :=
    sq_pos_of_pos (Nat.cast_pos.2 p.kStar_pos)
  calc
    (p.deltaMinus * (p.kStar : ℝ) ^ 2) * B ^ 2 =
        (p.kStar : ℝ) ^ 2 * (p.deltaMinus * B ^ 2) := by ring
    _ < (p.kStar : ℝ) ^ 2 * (p.deltaPlus * A ^ 2) :=
      mul_lt_mul_of_pos_left hcross hkSq
    _ = (p.deltaPlus * (p.kStar : ℝ) ^ 2) * A ^ 2 := by ring

/-- The lower endpoints eventually fall below every positive diffusivity.
This elementary Archimedean proof avoids assuming a convergence theorem for
the rounded sequence. -/
theorem exists_lower_le (f : ScaleFamily r) {ε : ℝ} (hε : 0 < ε) :
    ∃ n, p.deltaMinus * f.ell n ^ 2 ≤ ε := by
  let c : ℝ := p.deltaMinus * (p.kStar : ℝ) ^ 2
  obtain ⟨n, hn⟩ := exists_nat_gt (c / ε)
  have hc_nonneg : 0 ≤ c := by
    dsimp [c]
    exact mul_nonneg p.deltaMinus_pos.le (sq_nonneg _)
  have hn_real_pos : 0 < (n : ℝ) :=
    (div_nonneg hc_nonneg hε.le).trans_lt hn
  have hn_pos : 0 < n := by exact_mod_cast hn_real_pos
  have hn_le_K : (n : ℝ) ≤ (f.fourierIndex n : ℝ) := by
    exact_mod_cast (show n ≤ f.fourierIndex n from
      (Nat.le_add_left n f.K0).trans (f.add_le_fourierIndex n))
  have hK : 1 ≤ (f.fourierIndex n : ℝ) := by
    exact_mod_cast f.fourierIndex_pos n
  have hn_le_Ksq : (n : ℝ) ≤ (f.fourierIndex n : ℝ) ^ 2 := by
    calc
      (n : ℝ) ≤ (f.fourierIndex n : ℝ) := hn_le_K
      _ ≤ (f.fourierIndex n : ℝ) ^ 2 := by nlinarith
  have hc_lt : c < ε * (n : ℝ) := by
    simpa [mul_comm] using (div_lt_iff₀ hε).1 hn
  have hc_le : c ≤ ε * (f.fourierIndex n : ℝ) ^ 2 :=
    hc_lt.le.trans (mul_le_mul_of_nonneg_left hn_le_Ksq hε.le)
  refine ⟨n, ?_⟩
  unfold ell
  rw [div_pow]
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (sq_pos_of_pos (Nat.cast_pos.2 (f.fourierIndex_pos n)))).2
  simpa [c, mul_assoc] using hc_le

/-- Section 3.2's interval covering `⋃_n I_n = (0, ε₀]`, with the right endpoint included and
zero excluded. -/
theorem iUnion_diffusivityInterval (f : ScaleFamily r) :
    (⋃ n : ℕ, f.diffusivityInterval n) = Set.Ioc 0 f.epsilon0 := by
  apply Set.Subset.antisymm
  · rw [Set.iUnion_subset_iff]
    intro n ε hε
    rcases hε with ⟨hlower, hupper⟩
    refine ⟨?_, hupper.trans (f.interval_upper_le_epsilon0 n)⟩
    exact (mul_pos p.deltaMinus_pos (sq_pos_of_pos (f.ell_pos n))).trans_le hlower
  · intro ε hε
    rcases hε with ⟨hεpos, hεupper⟩
    let hex : ∃ n, p.deltaMinus * f.ell n ^ 2 ≤ ε := f.exists_lower_le hεpos
    let N : ℕ := Nat.find hex
    have hNlower : p.deltaMinus * f.ell N ^ 2 ≤ ε := Nat.find_spec hex
    cases hNval : N with
    | zero =>
        apply Set.mem_iUnion_of_mem 0
        refine ⟨?_, ?_⟩
        · simpa [hNval] using hNlower
        · simpa [epsilon0] using hεupper
    | succ n =>
        have hn_lt_N : n < N := by omega
        have hn_not : ¬ p.deltaMinus * f.ell n ^ 2 ≤ ε :=
          Nat.find_min hex hn_lt_N
        have hε_lt_previous : ε < p.deltaMinus * f.ell n ^ 2 :=
          lt_of_not_ge hn_not
        have hε_upper_next : ε ≤ p.deltaPlus * f.ell (n + 1) ^ 2 :=
          (hε_lt_previous.trans (f.neighboring_intervals_overlap n)).le
        apply Set.mem_iUnion_of_mem (n + 1)
        refine ⟨?_, hε_upper_next⟩
        simpa [hNval] using hNlower

/-- Every positive physical diffusivity below the threshold selects a cell
whose rescaled diffusivity belongs to the local interval.  The scale family
is fixed before `ε`; only `n` is selected afterwards. -/
theorem exists_matching_scale (f : ScaleFamily r) {ε : ℝ}
    (hεpos : 0 < ε) (hεupper : ε ≤ f.epsilon0) :
    ∃ n : ℕ, ε / f.ell n ^ 2 ∈ p.interval := by
  have hmem : ε ∈ ⋃ n : ℕ, f.diffusivityInterval n := by
    rw [f.iUnion_diffusivityInterval]
    exact ⟨hεpos, hεupper⟩
  simp only [Set.mem_iUnion] at hmem
  obtain ⟨n, hlower, hupper⟩ := hmem
  refine ⟨n, ?_, ?_⟩
  · exact (le_div_iff₀ (sq_pos_of_pos (f.ell_pos n))).2 (by
      simpa [mul_comm] using hlower)
  · exact (div_le_iff₀ (sq_pos_of_pos (f.ell_pos n))).2 (by
      simpa [mul_comm] using hupper)

end ScaleFamily

/-- Fully discharged arithmetic choices, in the paper's quantifier order (§3.1):
local data, then the ratio `q`, then an arbitrarily large final base index `K0`.  The
universal quantifier over later lower bounds is inside the choice of the ratio. -/
theorem exists_scale_selection (p : LocalSeedParameters) :
    ∃ r : ScaleRatios p, ∀ M : ℕ, ∃ f : ScaleFamily r, M ≤ f.K0 := by
  let r := (ScaleRatios.exists_for p).some
  exact ⟨r, fun M ↦ ScaleFamily.exists_ge r M⟩

end FastDynamo
