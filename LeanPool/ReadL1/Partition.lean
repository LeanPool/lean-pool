/-
Copyright (c) 2026 Zayn Blore. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zayn Blore
-/

-- Modified for Lean Pool.

module

public import Mathlib.Data.Nat.Basic
public import Mathlib.Order.Monotone.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Śliwa's partition of the indices

W. Śliwa (Rocky Mountain J. Math. 40 (2010), p. 628–629) builds Read's operator from a fast
growing integer sequence `d`. Put `aₙ = d₂ₙ₋₁`, `bₙ = d₂ₙ` and `vₙ = (n - 1)(aₙ + bₙ)`. For
`n > r ≥ 1` the positive integers are cut into consecutive blocks

* `Jₙ,ᵣ = ((r - 1)aₙ + vₙ₋ᵣ, r aₙ)` and `Iₙ,ᵣ = [r aₙ, r aₙ + vₙ₋ᵣ₋₁]`, which fill
  `(vₙ₋₁, (n - 1)aₙ]`;
* `Lₙ,ᵣ = ((n - 1)aₙ + (r - 1)bₙ, r(aₙ + bₙ))` and `Kₙ,ᵣ = [r(aₙ + bₙ), (n - 1)aₙ + r bₙ]`,
  which fill `((n - 1)aₙ, vₙ]`.

This file proves that every positive integer lies in exactly one block (`ReadL1.exists_block`,
`ReadL1.block_unique`). Only three growth facts are used, collected in `ReadL1.PartitionHyp`;
Śliwa derives them (and more) on p. 628 from his growth condition.
-/

@[expose] public section

namespace ReadL1

/-- `aₙ = d₂ₙ₋₁`. (At `n = 0`, natural-number subtraction gives `2 * 0 - 1 = 0`, so `a₀ = d₀`;
Śliwa only uses `aₙ` for `n ≥ 1`; the only conditions here that mention `a₀` are
`PartitionHyp.one_le_a` and `PartitionHyp.a_lt_b` at `n = 0`, which the explicit sequence meets
trivially.) -/
def seqA (d : ℕ → ℕ) (n : ℕ) : ℕ := d (2 * n - 1)

/-- `bₙ = d₂ₙ`. -/
def seqB (d : ℕ → ℕ) (n : ℕ) : ℕ := d (2 * n)

/-- `vₙ = (n - 1)(aₙ + bₙ)`, so `v₀ = v₁ = 0`. -/
def seqV (d : ℕ → ℕ) (n : ℕ) : ℕ := (n - 1) * (seqA d n + seqB d n)

/-- The growth facts the partition needs. -/
structure PartitionHyp (d : ℕ → ℕ) : Prop where
  one_le_a : ∀ n, 1 ≤ seqA d n
  /-- Every earlier `vₖ` is below `aₙ` (Śliwa: `8(vₙ₋₁ + 1) < aₙ`). -/
  v_lt_a : ∀ n k, k < n → seqV d k < seqA d n
  /-- `bₙ` beats `(n - 2)aₙ` (Śliwa: `8n aₙ < bₙ`). -/
  a_lt_b : ∀ n, (n - 2) * seqA d n < seqB d n

/-- The four kinds of block. -/
inductive Kind
  | J | I | L | K
  deriving DecidableEq

/-- A block `Jₙ,ᵣ`, `Iₙ,ᵣ`, `Lₙ,ᵣ` or `Kₙ,ᵣ`. -/
@[ext]
structure Block where
  /-- The level `n`. -/
  n : ℕ
  /-- The position `r` within the level, `1 ≤ r < n`. -/
  r : ℕ
  /-- Which of `J`, `I`, `L`, `K` the block is. -/
  kind : Kind

/-- `i` lies in the block `B` (with `n > r ≥ 1`). -/
def Block.Mem (d : ℕ → ℕ) (B : Block) (i : ℕ) : Prop :=
  1 ≤ B.r ∧ B.r < B.n ∧
    match B.kind with
    | .J => (B.r - 1) * seqA d B.n + seqV d (B.n - B.r) < i ∧ i < B.r * seqA d B.n
    | .I => B.r * seqA d B.n ≤ i ∧ i ≤ B.r * seqA d B.n + seqV d (B.n - B.r - 1)
    | .L => (B.n - 1) * seqA d B.n + (B.r - 1) * seqB d B.n < i ∧
        i < B.r * (seqA d B.n + seqB d B.n)
    | .K => B.r * (seqA d B.n + seqB d B.n) ≤ i ∧
        i ≤ (B.n - 1) * seqA d B.n + B.r * seqB d B.n

/-! ### Locating an index in a chain of intervals -/

/-- If `e` is strictly increasing and `e 0 < i ≤ e m`, then `i` lies in some `(e (r - 1), e r]`
with `1 ≤ r ≤ m`. -/
lemma exists_mem_chain {e : ℕ → ℕ} {i m : ℕ} (h0 : e 0 < i) (hm : i ≤ e m) :
    ∃ r, 1 ≤ r ∧ r ≤ m ∧ e (r - 1) < i ∧ i ≤ e r := by
  classical
  have hex : ∃ r, i ≤ e r := ⟨m, hm⟩
  set r := Nat.find hex with hr
  have hri : i ≤ e r := Nat.find_spec hex
  have hr0 : r ≠ 0 := fun h ↦ by rw [h] at hri; omega
  refine ⟨r, Nat.one_le_iff_ne_zero.2 hr0, Nat.find_min' hex hm, ?_, hri⟩
  exact lt_of_not_ge (Nat.find_min hex (by omega))

/-- The interval of a strictly increasing chain containing `i` is unique. -/
lemma chain_index_unique {e : ℕ → ℕ} (he : StrictMono e) {i r s : ℕ} (hr : 1 ≤ r) (hs : 1 ≤ s)
    (hri : e (r - 1) < i ∧ i ≤ e r) (hsi : e (s - 1) < i ∧ i ≤ e s) : r = s := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := he.monotone (show r ≤ s - 1 by omega); omega
  · have := he.monotone (show s ≤ r - 1 by omega); omega

variable {d : ℕ → ℕ}

/-! ### The levels `(vₙ₋₁, vₙ]` -/

lemma seqV_zero : seqV d 0 = 0 := by simp [seqV]

lemma seqV_one : seqV d 1 = 0 := by simp [seqV]

/-- From `n = 1` on, `v` strictly increases: `vₙ < aₙ₊₁ ≤ n aₙ₊₁ ≤ vₙ₊₁`. -/
lemma seqV_lt_succ (h : PartitionHyp d) {n : ℕ} (hn : 1 ≤ n) : seqV d n < seqV d (n + 1) := by
  have h1 := h.v_lt_a (n + 1) n (by omega)
  have h2 : seqA d (n + 1) ≤ n * seqA d (n + 1) := Nat.le_mul_of_pos_left _ hn
  have h3 : n * seqA d (n + 1) ≤ seqV d (n + 1) := by
    unfold seqV; simp only [Nat.add_sub_cancel]; exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- Every `i` is at most `vᵢ₊₁ = i(aᵢ₊₁ + bᵢ₊₁)`. -/
lemma le_seqV_succ (h : PartitionHyp d) (i : ℕ) : i ≤ seqV d (i + 1) := by
  unfold seqV
  simp only [Nat.add_sub_cancel]
  exact Nat.le_mul_of_pos_right _ (by have := h.one_le_a (i + 1); omega)

/-- The shifted sequence `n ↦ vₙ₊₁` is strictly increasing. -/
lemma strictMono_seqV_succ (h : PartitionHyp d) : StrictMono fun n ↦ seqV d (n + 1) :=
  strictMono_nat_of_lt_succ fun n ↦ seqV_lt_succ h (by omega)

/-- Each positive `i` lies in exactly one level `(vₙ₋₁, vₙ]`, and then `n ≥ 2`. -/
lemma exists_level (h : PartitionHyp d) {i : ℕ} (hi : 1 ≤ i) :
    ∃ n, 2 ≤ n ∧ seqV d (n - 1) < i ∧ i ≤ seqV d n := by
  -- Apply the chain lemma to `e k = vₖ₊₁`, which starts at `v₁ = 0`.
  obtain ⟨r, hr1, -, hlo, hhi⟩ :=
    exists_mem_chain (e := fun k ↦ seqV d (k + 1)) (m := i)
      (by simp only [zero_add, seqV_one]; omega) (le_seqV_succ h i)
  refine ⟨r + 1, by omega, ?_, hhi⟩
  simpa [show r - 1 + 1 = r by omega] using hlo

lemma level_unique (h : PartitionHyp d) {i n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m)
    (hni : seqV d (n - 1) < i ∧ i ≤ seqV d n) (hmi : seqV d (m - 1) < i ∧ i ≤ seqV d m) :
    n = m := by
  have := chain_index_unique (e := fun k ↦ seqV d (k + 1)) (strictMono_seqV_succ h)
    (r := n - 1) (s := m - 1) (i := i) (by omega) (by omega)
    (by simpa [show n - 1 - 1 + 1 = n - 1 by omega, show n - 1 + 1 = n by omega] using hni)
    (by simpa [show m - 1 - 1 + 1 = m - 1 by omega, show m - 1 + 1 = m by omega] using hmi)
  omega

/-! ### Inside a level -/

/-- The right ends `r aₙ + vₙ₋ᵣ₋₁` of the blocks `Iₙ,ᵣ` increase with `r`. -/
lemma strictMono_chainX (h : PartitionHyp d) (n : ℕ) :
    StrictMono fun r ↦ r * seqA d n + seqV d (n - r - 1) := by
  refine strictMono_nat_of_lt_succ fun r ↦ ?_
  have hv : seqV d (n - r - 1) < seqA d n ∨ n - r - 1 = 0 := by
    rcases Nat.eq_zero_or_pos (n - r - 1) with h0 | h0
    · exact Or.inr h0
    · exact Or.inl (h.v_lt_a n _ (by omega))
  have hsucc : (r + 1) * seqA d n = r * seqA d n + seqA d n := by ring
  rcases hv with hv | hv
  · rw [hsucc]; omega
  · rw [hsucc, hv, show n - (r + 1) - 1 = 0 by omega, seqV_zero]
    have := h.one_le_a n; omega

/-- The right ends `(n - 1)aₙ + r bₙ` of the blocks `Kₙ,ᵣ` increase with `r`. -/
lemma strictMono_chainY (h : PartitionHyp d) (n : ℕ) :
    StrictMono fun r ↦ (n - 1) * seqA d n + r * seqB d n := by
  have hb : 0 < seqB d n := lt_of_le_of_lt (Nat.zero_le _) (h.a_lt_b n)
  exact strictMono_nat_of_lt_succ fun r ↦ by nlinarith

/-- **Every positive integer lies in a block.** -/
theorem exists_block (h : PartitionHyp d) {i : ℕ} (hi : 1 ≤ i) : ∃ B : Block, B.Mem d i := by
  obtain ⟨n, hn, hlo, hhi⟩ := exists_level h hi
  have hva : seqV d (n - 1) < seqA d n := h.v_lt_a n (n - 1) (by omega)
  by_cases hX : i ≤ (n - 1) * seqA d n
  · -- `i` is in `(vₙ₋₁, (n - 1)aₙ]`: find `r` with `i ∈ Jₙ,ᵣ ∪ Iₙ,ᵣ`.
    obtain ⟨r, hr1, hrm, hrlo, hrhi⟩ :=
      exists_mem_chain (e := fun r ↦ r * seqA d n + seqV d (n - r - 1)) (m := n - 1)
        (by simpa using hlo) (by simpa [show n - (n - 1) - 1 = 0 by omega, seqV_zero] using hX)
    have hlo' : (r - 1) * seqA d n + seqV d (n - r) < i := by
      simpa [show n - (r - 1) - 1 = n - r by omega] using hrlo
    by_cases hJ : i < r * seqA d n
    · exact ⟨⟨n, r, .J⟩, hr1, (show r < n by omega), hlo', hJ⟩
    · exact ⟨⟨n, r, .I⟩, hr1, (show r < n by omega), (show r * seqA d n ≤ i by omega), hrhi⟩
  · -- `i` is in `((n - 1)aₙ, vₙ]`: find `r` with `i ∈ Lₙ,ᵣ ∪ Kₙ,ᵣ`.
    have hvn : seqV d n = (n - 1) * seqA d n + (n - 1) * seqB d n := by unfold seqV; ring
    obtain ⟨r, hr1, hrm, hrlo, hrhi⟩ :=
      exists_mem_chain (e := fun r ↦ (n - 1) * seqA d n + r * seqB d n) (m := n - 1)
        (by simpa using lt_of_not_ge hX) (by simpa [← hvn] using hhi)
    by_cases hL : i < r * (seqA d n + seqB d n)
    · exact ⟨⟨n, r, .L⟩, hr1, (show r < n by omega), hrlo, hL⟩
    · exact ⟨⟨n, r, .K⟩, hr1, (show r < n by omega),
        (show r * (seqA d n + seqB d n) ≤ i by omega), hrhi⟩

/-- A block lies inside its level `(vₙ₋₁, vₙ]`, on the `X` side `(vₙ₋₁, (n - 1)aₙ]` for `J, I`
and the `Y` side `((n - 1)aₙ, vₙ]` for `L, K`. -/
lemma Block.mem_level (h : PartitionHyp d) {B : Block} {i : ℕ} (hB : B.Mem d i) :
    seqV d (B.n - 1) < i ∧ i ≤ seqV d B.n ∧
      (i ≤ (B.n - 1) * seqA d B.n ↔ B.kind = .J ∨ B.kind = .I) := by
  obtain ⟨n, r, k⟩ := B
  obtain ⟨hr1, hrn, hk⟩ := hB
  dsimp only at hr1 hrn hk ⊢
  have hva : seqV d (n - 1) < seqA d n := h.v_lt_a n (n - 1) (by omega)
  have ha := h.one_le_a n
  have hab := h.a_lt_b n
  have hvn : seqV d n = (n - 1) * seqA d n + (n - 1) * seqB d n := by unfold seqV; ring
  have hra : r * seqA d n ≤ (n - 1) * seqA d n := Nat.mul_le_mul_right _ (by omega)
  have hrb : r * seqB d n ≤ (n - 1) * seqB d n := Nat.mul_le_mul_right _ (by omega)
  have hrsucc : (r - 1) * seqA d n + seqA d n = r * seqA d n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
  cases k with
  | J =>
    obtain ⟨h1, h2⟩ := hk
    -- `(r - 1)aₙ + vₙ₋ᵣ ≥ vₙ₋₁`: equality at `r = 1`, and `aₙ > vₙ₋₁` beyond.
    have hge : seqV d (n - 1) ≤ (r - 1) * seqA d n + seqV d (n - r) := by
      rcases Nat.eq_or_lt_of_le hr1 with hr | hr
      · subst hr; simp
      · have : seqA d n ≤ (r - 1) * seqA d n := Nat.le_mul_of_pos_left _ (by omega)
        omega
    refine ⟨by omega, by omega, by simp; omega⟩
  | I =>
    obtain ⟨h1, h2⟩ := hk
    have hra1 : seqA d n ≤ r * seqA d n := Nat.le_mul_of_pos_left _ hr1
    -- `r aₙ + vₙ₋ᵣ₋₁ ≤ (n - 1)aₙ`: at `r = n - 1` because `v₀ = 0`, below because `v < aₙ`.
    have hend : r * seqA d n + seqV d (n - r - 1) ≤ (n - 1) * seqA d n := by
      rcases Nat.eq_or_lt_of_le (show r ≤ n - 1 by omega) with hr | hr
      · rw [hr, show n - (n - 1) - 1 = 0 by omega, seqV_zero]; simp
      · have hv := h.v_lt_a n (n - r - 1) (by omega)
        have : (r + 1) * seqA d n ≤ (n - 1) * seqA d n := Nat.mul_le_mul_right _ (by omega)
        nlinarith
    refine ⟨by omega, by omega, by simp; omega⟩
  | L =>
    obtain ⟨h1, h2⟩ := hk
    have : seqA d n ≤ (n - 1) * seqA d n := Nat.le_mul_of_pos_left _ (by omega)
    have hlt : r * (seqA d n + seqB d n) ≤ seqV d n := by rw [hvn]; nlinarith
    refine ⟨by omega, by omega, by simp; omega⟩
  | K =>
    obtain ⟨h1, h2⟩ := hk
    have : seqA d n ≤ r * seqA d n := Nat.le_mul_of_pos_left _ hr1
    have hb0 : 0 < seqB d n := lt_of_le_of_lt (Nat.zero_le _) hab
    -- `(n - 1)aₙ = aₙ + (n - 2)aₙ < aₙ + bₙ ≤ r(aₙ + bₙ)`.
    have hsplit : (n - 1) * seqA d n = seqA d n + (n - 2) * seqA d n := by
      rw [show n - 1 = 1 + (n - 2) by omega, Nat.add_mul, one_mul]
    have hr' : seqA d n + seqB d n ≤ r * (seqA d n + seqB d n) := Nat.le_mul_of_pos_left _ hr1
    have : (n - 1) * seqA d n < r * (seqA d n + seqB d n) := by omega
    refine ⟨by nlinarith, by omega, by simp; omega⟩

lemma Block.two_le_n {B : Block} {i : ℕ} (hB : B.Mem d i) : 2 ≤ B.n := by
  obtain ⟨h1, h2, -⟩ := hB; omega

/-- A `J` or `I` block sits in the interval `(e (r - 1), e r]` of the chain
`e r = r aₙ + vₙ₋ᵣ₋₁`. -/
lemma Block.chainX (h : PartitionHyp d) {B : Block} {i : ℕ} (hB : B.Mem d i)
    (hk : B.kind = .J ∨ B.kind = .I) :
    (B.r - 1) * seqA d B.n + seqV d (B.n - (B.r - 1) - 1) < i ∧
      i ≤ B.r * seqA d B.n + seqV d (B.n - B.r - 1) := by
  obtain ⟨n, r, k⟩ := B
  obtain ⟨hr1, hrn, hk'⟩ := hB
  dsimp only at *
  rw [show n - (r - 1) - 1 = n - r by omega]
  have hv := h.v_lt_a n (n - r) (by omega)
  have hrsucc : (r - 1) * seqA d n + seqA d n = r * seqA d n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
  rcases hk with rfl | rfl
  · obtain ⟨h1, h2⟩ := hk'; exact ⟨h1, by omega⟩
  · obtain ⟨h1, h2⟩ := hk'; exact ⟨by omega, h2⟩

/-- An `L` or `K` block sits in the interval `(g (r - 1), g r]` of the chain
`g r = (n - 1)aₙ + r bₙ`. -/
lemma Block.chainY (h : PartitionHyp d) {B : Block} {i : ℕ} (hB : B.Mem d i)
    (hk : B.kind = .L ∨ B.kind = .K) :
    (B.n - 1) * seqA d B.n + (B.r - 1) * seqB d B.n < i ∧
      i ≤ (B.n - 1) * seqA d B.n + B.r * seqB d B.n := by
  obtain ⟨n, r, k⟩ := B
  obtain ⟨hr1, hrn, hk'⟩ := hB
  dsimp only at *
  have hab := h.a_lt_b n
  have hrsucc : (r - 1) * seqB d n + seqB d n = r * seqB d n := by
    rw [← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1]
  rcases hk with rfl | rfl
  · obtain ⟨h1, h2⟩ := hk'
    refine ⟨h1, ?_⟩
    have : r * seqA d n ≤ (n - 1) * seqA d n := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · obtain ⟨h1, h2⟩ := hk'
    refine ⟨?_, h2⟩
    -- `(n - 1)aₙ + (r - 1)bₙ < r aₙ + r bₙ`, as `(n - 1 - r)aₙ ≤ (n - 2)aₙ < bₙ`.
    have : (n - 1) * seqA d n ≤ (n - 2) * seqA d n + r * seqA d n := by
      rw [← Nat.add_mul]; exact Nat.mul_le_mul_right _ (by omega)
    nlinarith

/-- **The block containing a positive integer is unique.** -/
theorem block_unique (h : PartitionHyp d) {i : ℕ} {B C : Block} (hB : B.Mem d i)
    (hC : C.Mem d i) : B = C := by
  obtain ⟨hBlo, hBhi, hBX⟩ := B.mem_level h hB
  obtain ⟨hClo, hChi, hCX⟩ := C.mem_level h hC
  have hnm : B.n = C.n :=
    level_unique h (Block.two_le_n hB) (Block.two_le_n hC) ⟨hBlo, hBhi⟩ ⟨hClo, hChi⟩
  have hXB := Block.chainX h hB
  have hXC := Block.chainX h hC
  have hYB := Block.chainY h hB
  have hYC := Block.chainY h hC
  obtain ⟨n, r, k⟩ := B
  obtain ⟨m, s, l⟩ := C
  obtain ⟨hr1, hrn, hk⟩ := hB
  obtain ⟨hs1, hsm, hl⟩ := hC
  dsimp only at *
  subst hnm
  -- The same `r` on the `X` side, and on the `Y` side.
  have hrsX : (k = .J ∨ k = .I) → (l = .J ∨ l = .I) → r = s := fun hk hl ↦
    chain_index_unique (e := fun r ↦ r * seqA d n + seqV d (n - r - 1)) (strictMono_chainX h n)
      hr1 hs1 (hXB hk) (hXC hl)
  have hrsY : (k = .L ∨ k = .K) → (l = .L ∨ l = .K) → r = s := fun hk hl ↦
    chain_index_unique (e := fun r ↦ (n - 1) * seqA d n + r * seqB d n) (strictMono_chainY h n)
      hr1 hs1 (hYB hk) (hYC hl)
  cases k <;> cases l <;> simp only [Block.mk.injEq, true_and, and_true]
  -- Same kind: the chain gives `r = s`. Different kinds on one side: with `r = s` the two blocks'
  -- bounds clash at the split point. Different sides: the side test `i ≤ (n - 1)aₙ` clashes.
  all_goals first
    | exact hrsX (Or.inl rfl) (Or.inl rfl)
    | exact hrsX (Or.inr rfl) (Or.inr rfl)
    | exact hrsY (Or.inl rfl) (Or.inl rfl)
    | exact hrsY (Or.inr rfl) (Or.inr rfl)
    | (obtain rfl := hrsX (Or.inl rfl) (Or.inr rfl); omega)
    | (obtain rfl := hrsX (Or.inr rfl) (Or.inl rfl); omega)
    | (obtain rfl := hrsY (Or.inl rfl) (Or.inr rfl); omega)
    | (obtain rfl := hrsY (Or.inr rfl) (Or.inl rfl); omega)
    | (simp at hBX hCX; omega)

end ReadL1
