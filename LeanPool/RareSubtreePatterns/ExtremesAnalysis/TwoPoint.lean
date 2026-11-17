/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Statements.Main


/-!
# Two-point sets, integer levels and subsequence splitting

Deterministic bookkeeping behind the two-point and one-point localization statements of
Theorems `thm:max_string`(ii) and `thm:max_lh`(ii) (source lines 486–501, 2860–2897, 545–558,
3363–3383; inventory P20, P24).

* The two-point set `J_n = twoPointSet x` (`{m-1, m}` if `θ ≤ 1/2`, `{m, m+1}` otherwise, with
  `m = ⌊x⌋`, `θ = {x}`) is the integer interval `[a, a+2)` with `a = twoPointLow x = ⌈x - 1/2⌉ - 1`
  (`twoPointSet_eq`, `mem_twoPointSet_iff`). In both cases `a ≤ x - 1/2` and `x + 1/2 ≤ a + 2`
  (`twoPointLow_le`, `add_half_le_twoPointLow_add_two`), so the paper's case split at
  `θ_n = 1/2` can be replaced by one level sequence `a_n` valid for all `n`.
* In the interior phase `δ ≤ min(θ, 1 - θ)`: `⌊x⌋ ≤ x - δ` and `x + δ ≤ ⌊x⌋ + 1`.
* Integer levels versus natural mark indices: for `H : ℕ` and `z : ℤ`,
  `z ≤ H ↔ z.toNat ≤ H` holds for *every* `z` (negative floors included), so the events
  `{H ≤ ⌊y⌋}`, `{H ∈ J}` and `{H = ⌊x⌋}` are expressed through the events `{k ≤ H}` at the
  natural levels `k = (·).toNat`, with no "eventually" needed.
* Subsequence splitting (source lines 2876–2880): a limit along `l ⊓ 𝓟 S` and along
  `l ⊓ 𝓟 Sᶜ` (either possibly trivial) gives the limit along `l`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace PoissonDeclumping

/-- The strengthened localization contract retains the original full-filter refinement. -/
theorem TwoPointLocalization.tendsto_singlePoint {μ : PMF ℕ} {H : PlaneTree → ℕ}
    {x : ℕ → ℝ} (h : TwoPointLocalization μ H x)
    (hphase : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in admissibleSizes μ,
      δ ≤ min (Int.fract (x n)) (1 - Int.fract (x n))) :
    Tendsto (fun n => (PlaneTree.conditioned μ n).real
      {T | ((H T : ℕ) : ℤ) = ⌊x n⌋}) (admissibleSizes μ) (𝓝 1) := by
  rcases (admissibleSizes μ).eq_or_neBot with hbot | hne
  · rw [hbot]
    exact tendsto_bot
  · exact h.2 _ le_rfl hne hphase

/-- Single-point localization along any cofinal admissible subsequence with interior phases. -/
theorem TwoPointLocalization.tendsto_singlePoint_subsequence {μ : PMF ℕ}
    {H : PlaneTree → ℕ} {x : ℕ → ℝ} (h : TwoPointLocalization μ H x)
    {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    (hadm : ∀ᶠ n in atTop, PlaneTree.Admissible μ (s n))
    (hphase : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      δ ≤ min (Int.fract (x (s n))) (1 - Int.fract (x (s n)))) :
    Tendsto (fun n => (PlaneTree.conditioned μ (s n)).real
      {T | ((H T : ℕ) : ℤ) = ⌊x (s n)⌋}) atTop (𝓝 1) := by
  have hl : map s atTop ≤ admissibleSizes μ :=
    tendsto_inf.mpr ⟨hs, tendsto_principal.mpr hadm⟩
  obtain ⟨δ, hδ, hphase⟩ := hphase
  exact (h.2 (map s atTop) hl inferInstance ⟨δ, hδ, hphase⟩).comp
    (show Tendsto s atTop (map s atTop) from le_rfl)

namespace ExtremesAnalysis

/-! ### The two-point set as an integer interval -/

/-- The lower point `a = ⌈x - 1/2⌉ - 1` of the two-point set `J = {a, a + 1}`: it is
`⌊x⌋ - 1` if `{x} ≤ 1/2` and `⌊x⌋` otherwise. -/
noncomputable def twoPointLow (x : ℝ) : ℤ := ⌈x - 1 / 2⌉ - 1

theorem twoPointLow_eq_of_fract_le {x : ℝ} (h : Int.fract x ≤ 1 / 2) :
    twoPointLow x = ⌊x⌋ - 1 := by
  have hf := Int.floor_add_fract x
  have h0 := Int.fract_nonneg x
  have hc : ⌈x - 1 / 2⌉ = ⌊x⌋ := by
    rw [Int.ceil_eq_iff]
    constructor <;> linarith
  rw [twoPointLow, hc]

theorem twoPointLow_eq_of_lt_fract {x : ℝ} (h : 1 / 2 < Int.fract x) :
    twoPointLow x = ⌊x⌋ := by
  have hf := Int.floor_add_fract x
  have h1 := Int.fract_lt_one x
  have hc : ⌈x - 1 / 2⌉ = ⌊x⌋ + 1 := by
    rw [Int.ceil_eq_iff]
    push_cast
    constructor <;> linarith
  rw [twoPointLow, hc, add_sub_cancel_right]

/-- `J = twoPointSet x = {a, a + 1}` with `a = twoPointLow x`. -/
theorem twoPointSet_eq (x : ℝ) : twoPointSet x = {twoPointLow x, twoPointLow x + 1} := by
  unfold twoPointSet
  split_ifs with h
  · rw [twoPointLow_eq_of_fract_le h, sub_add_cancel]
  · rw [twoPointLow_eq_of_lt_fract (not_le.mp h)]

/-- `z ∈ J ↔ a ≤ z < a + 2`. -/
theorem mem_twoPointSet_iff (x : ℝ) (z : ℤ) :
    z ∈ twoPointSet x ↔ twoPointLow x ≤ z ∧ z < twoPointLow x + 2 := by
  rw [twoPointSet_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- `a ≤ x - 1/2`, i.e. the lower level lies at least `1/2` below the centering. -/
theorem twoPointLow_le (x : ℝ) : (twoPointLow x : ℝ) ≤ x - 1 / 2 := by
  have := Int.ceil_lt_add_one (x - 1 / 2)
  simp only [twoPointLow, Int.cast_sub, Int.cast_one]
  linarith

/-- `x - 3/2 ≤ a`. -/
theorem sub_le_twoPointLow (x : ℝ) : x - 3 / 2 ≤ (twoPointLow x : ℝ) := by
  have := Int.le_ceil (x - 1 / 2)
  simp only [twoPointLow, Int.cast_sub, Int.cast_one]
  linarith

/-- `x + 1/2 ≤ a + 2`, i.e. the first excluded level lies at least `1/2` above the centering. -/
theorem add_half_le_twoPointLow_add_two (x : ℝ) :
    x + 1 / 2 ≤ ((twoPointLow x + 2 : ℤ) : ℝ) := by
  have := Int.le_ceil (x - 1 / 2)
  simp only [twoPointLow, Int.cast_add, Int.cast_sub, Int.cast_one, Int.cast_ofNat]
  linarith

/-- `a + 2 ≤ x + 3/2`. -/
theorem twoPointLow_add_two_le (x : ℝ) : ((twoPointLow x + 2 : ℤ) : ℝ) ≤ x + 3 / 2 := by
  have := twoPointLow_le x
  push_cast
  linarith

/-! ### The interior phase -/

/-- Interior phase: if `δ ≤ min({x}, 1 - {x})` then `⌊x⌋ ≤ x - δ`. -/
theorem floor_le_sub_of_le_min {x δ : ℝ} (h : δ ≤ min (Int.fract x) (1 - Int.fract x)) :
    (⌊x⌋ : ℝ) ≤ x - δ := by
  have hf := Int.floor_add_fract x
  have := h.trans (min_le_left _ _)
  linarith

/-- Interior phase: if `δ ≤ min({x}, 1 - {x})` then `x + δ ≤ ⌊x⌋ + 1`. -/
theorem add_le_floor_add_one_of_le_min {x δ : ℝ} (h : δ ≤ min (Int.fract x) (1 - Int.fract x)) :
    x + δ ≤ ((⌊x⌋ + 1 : ℤ) : ℝ) := by
  have hf := Int.floor_add_fract x
  have := h.trans (min_le_right _ _)
  push_cast
  linarith

/-- A lower level shifted away from the centering equals the floor in an interior phase. -/
theorem floor_sub_eq_floor_of_phase {x δ : ℝ} (hδ : 0 < δ)
    (h : δ ≤ min (Int.fract x) (1 - Int.fract x)) : ⌊x - δ⌋ = ⌊x⌋ := by
  apply Int.floor_eq_iff.mpr
  have hf := Int.floor_add_fract x
  have h1 := Int.fract_lt_one x
  have hlow := h.trans (min_le_left _ _)
  constructor <;> linarith only [hf, h1, hlow, hδ]

/-- An upper level shifted away from the centering equals the next integer in an interior phase. -/
theorem ceil_add_eq_floor_add_one_of_phase {x δ : ℝ} (hδ : 0 < δ)
    (h : δ ≤ min (Int.fract x) (1 - Int.fract x)) : ⌈x + δ⌉ = ⌊x⌋ + 1 := by
  apply Int.ceil_eq_iff.mpr
  have hf := Int.floor_add_fract x
  have h0 := Int.fract_nonneg x
  have hup := h.trans (min_le_right _ _)
  push_cast
  constructor <;> linarith only [hf, h0, hup, hδ]

/-! ### Integer levels and natural mark indices -/

/-- For every integer `z` (negative ones included), `z ≤ H ↔ z.toNat ≤ H`. -/
theorem int_le_natCast_iff_toNat_le (z : ℤ) (H : ℕ) : z ≤ (H : ℤ) ↔ z.toNat ≤ H := by
  omega

/-- `{H ≤ m} = {(m+1).toNat ≤ H}ᶜ`, for every integer `m` (used with `m = ⌊x_n + t⌋`). -/
theorem natCast_le_iff_not_toNat_le (H : ℕ) (m : ℤ) :
    (H : ℤ) ≤ m ↔ ¬ (m + 1).toNat ≤ H := by
  omega

/-- `{H ∈ J} = {a.toNat ≤ H} \ {(a+2).toNat ≤ H}` with `a = twoPointLow x`. -/
theorem natCast_mem_twoPointSet_iff (x : ℝ) (H : ℕ) :
    (H : ℤ) ∈ twoPointSet x ↔
      (twoPointLow x).toNat ≤ H ∧ ¬ (twoPointLow x + 2).toNat ≤ H := by
  rw [mem_twoPointSet_iff]
  omega

/-- `{H = m} = {m.toNat ≤ H} \ {(m+1).toNat ≤ H}` for every integer `m` (used with `m = ⌊x_n⌋`). -/
theorem natCast_eq_iff (H : ℕ) (m : ℤ) :
    (H : ℤ) = m ↔ m.toNat ≤ H ∧ ¬ (m + 1).toNat ≤ H := by
  omega

/-- If the level `z` is nonnegative its natural index has the same real value. -/
theorem cast_toNat_of_nonneg {z : ℤ} (hz : 0 ≤ z) : ((z.toNat : ℕ) : ℝ) = (z : ℝ) := by
  rw [← Int.cast_natCast, Int.toNat_of_nonneg hz]

/-- If `x_n → ∞` along `l` and the integer levels `z_n` satisfy `x_n - K ≤ z_n`, then the levels
are eventually nonnegative, so that `(z_n.toNat : ℝ) = z_n` eventually. -/
theorem eventually_cast_toNat_eq {ι : Type*} {l : Filter ι} {x : ι → ℝ} {z : ι → ℤ} {K : ℝ}
    (hx : Tendsto x l atTop) (hz : ∀ᶠ i in l, x i - K ≤ z i) :
    ∀ᶠ i in l, 0 ≤ z i ∧ (((z i).toNat : ℕ) : ℝ) = (z i : ℝ) := by
  filter_upwards [hz, hx.eventually_ge_atTop (K - 1 / 2)] with i hi hxi
  have h0 : (-1 : ℝ) < z i := by linarith
  have h0' : -1 < z i := by exact_mod_cast h0
  have hz0 : 0 ≤ z i := by omega
  exact ⟨hz0, cast_toNat_of_nonneg hz0⟩

/-! ### Subsequence splitting -/

/-- Subsequence splitting: a limit along the indices in `S` and along the indices outside `S`
(either set possibly finite or empty) gives the limit along the whole filter. -/
theorem tendsto_of_tendsto_inf_principal_of_compl {α β : Type*} {l : Filter α} {l' : Filter β}
    {f : α → β} (S : Set α) (h₁ : Tendsto f (l ⊓ 𝓟 S) l') (h₂ : Tendsto f (l ⊓ 𝓟 Sᶜ) l') :
    Tendsto f l l' := by
  classical
  simpa using h₁.piecewise h₂

/-- The split used in the source (lines 2876–2880, 3363–3374) for the two-point localization:
along the indices with `{x_n} ≤ 1/2` and along those with `{x_n} > 1/2`. -/
theorem tendsto_of_fract_le_half_of_half_lt {α β : Type*} {l : Filter α} {l' : Filter β}
    {f : α → β} (x : α → ℝ)
    (h₁ : Tendsto f (l ⊓ 𝓟 {n | Int.fract (x n) ≤ 1 / 2}) l')
    (h₂ : Tendsto f (l ⊓ 𝓟 {n | 1 / 2 < Int.fract (x n)}) l') :
    Tendsto f l l' := by
  refine tendsto_of_tendsto_inf_principal_of_compl {n | Int.fract (x n) ≤ 1 / 2} h₁ ?_
  convert h₂ using 3
  ext n
  simp

end ExtremesAnalysis
end PoissonDeclumping
