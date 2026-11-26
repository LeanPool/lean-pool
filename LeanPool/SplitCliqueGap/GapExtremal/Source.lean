/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Core
public import LeanPool.SplitCliqueGap.GapExtremal.Bridge
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# Counting blocks and the fractional source (ledger L7.4)

* `blocks_eq`, `card_blocks`: the blocks are the lines `line (0, w) c`, `c ∈ C`, `w ∈ W`, all
distinct, so
  `#blocks = |C| · |W|`.
* `ysrc`: mass `1/3` on the nine source pieces of every block; `resPack_ysrc` (capacity 1 on every
pair) and
  `value_ysrc` (`∑ y w ≥ 25/3 · |C| · |W|`).
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]
variable {C : Finset W} {σ : Fin 6 ↪ F}

/-! ### Blocks indexed by direction and colour-0 point -/

omit [Fintype W] in
theorem line_zero (w c : W) : line ((0 : F), w) c = univ.image fun a : F => (a, w + a • c) := by
  unfold line
  congr 1
  funext a
  simp [u]

omit [Fintype W] in
theorem mem_line_zero {w c : W} {p : F × W} : p ∈ line ((0 : F), w) c ↔ p.2 = w + p.1 • c := by
  rw [line_zero]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, rfl⟩; rfl
  · intro h; exact ⟨p.1, by rw [← h]⟩

omit [Fintype W] in
theorem line_eq_line_zero (x : F × W) (c : W) : line x c = line ((0 : F), x.2 - x.1 • c) c := by
  symm
  apply line_eq_of_mem
  exact mem_line.mpr ⟨-x.1, by simp [u, Prod.ext_iff, sub_eq_add_neg]⟩

omit [Fintype W] in
theorem line_zero_inj {w w' c c' : W} (h : line ((0 : F), w) c = line ((0 : F), w') c') :
    w = w' ∧ c = c' := by
  have h0 : ((0 : F), w) ∈ line ((0 : F), w') c' := h ▸ self_mem_line _ _
  rw [mem_line_zero] at h0
  simp only [zero_smul, add_zero] at h0
  subst h0
  have h1 : ((1 : F), w + (1 : F) • c) ∈ line ((0 : F), w) c' := by
    rw [← h, mem_line_zero]
  rw [mem_line_zero] at h1
  simp only [one_smul, add_right_inj] at h1
  exact ⟨rfl, h1⟩

theorem blocks_eq : blocks (F := F) C = (C ×ˢ univ).image fun p : W × W => line ((0 : F), p.2) p.1
  := by
  ext ℓ
  constructor
  · intro hℓ
    obtain ⟨⟨x, c⟩, hp, rfl⟩ := Finset.mem_image.mp hℓ
    have hc : c ∈ C := (Finset.mem_product.mp hp).2
    exact Finset.mem_image.mpr ⟨(c, x.2 - x.1 • c),
      Finset.mem_product.mpr ⟨hc, Finset.mem_univ _⟩, (line_eq_line_zero x c).symm⟩
  · intro hℓ
    obtain ⟨⟨c, w⟩, hp, rfl⟩ := Finset.mem_image.mp hℓ
    exact mem_blocks_of (Finset.mem_product.mp hp).1

theorem card_blocks : (blocks (F := F) C).card = C.card * Fintype.card W := by
  rw [blocks_eq, Finset.card_image_of_injOn, Finset.card_product, Finset.card_univ]
  rintro ⟨c, w⟩ - ⟨c', w'⟩ - h
  obtain ⟨hw, hc⟩ := line_zero_inj h
  exact Prod.ext hc hw

/-! ### The source -/

/-- The nine pieces of the local fractional source (mass `1/3` each). -/
def src : Finset (Finset (Fin 6)) :=
  {{0, 1, 4}, {0, 1, 5}, {1, 2, 4}, {1, 2, 5}, {2, 3, 4}, {2, 3, 5}, {0, 1, 4, 5}, {0, 3, 4, 5},
    {2, 3, 4, 5}}

theorem src_value : ∑ K ∈ src, (2 * (H12.eH K : ℤ) - (K.card.choose 2 : ℕ) - 1) = 25 := by
  decide +kernel

theorem src_card : ∀ K ∈ src, 3 ≤ K.card := by decide +kernel

theorem src_pair : ∀ i j : Fin 6, i ≠ j → (src.filter fun K => i ∈ K ∧ j ∈ K).card ≤ 3 := by
  decide +kernel

/-- The point of colour `σ i` on the line `line (0, w) c`. -/
def ptc (σ : Fin 6 ↪ F) (w c : W) (i : Fin 6) : F × W := (σ i, w + σ i • c)

omit [DecidableEq F] [DecidableEq W] [Fintype F] [Fintype W] in
theorem ptc_injective (w c : W) : Function.Injective (ptc σ w c) := fun _ _ h =>
  σ.injective (congrArg Prod.fst h)

/-- A source piece, indexed by direction, colour-0 point and colour set. -/
def piece (σ : Fin 6 ↪ F) (x : (W × W) × Finset (Fin 6)) : Finset (F × W) :=
  x.2.image (ptc σ x.1.2 x.1.1)

/-- Index set of the pieces. -/
def pidx (C : Finset W) : Finset ((W × W) × Finset (Fin 6)) := (C ×ˢ univ) ×ˢ src

omit [Fintype F] [Fintype W] in
theorem card_piece (x : (W × W) × Finset (Fin 6)) : (piece σ x).card = x.2.card :=
  Finset.card_image_of_injective _ (ptc_injective _ _)

omit [DecidableEq F] [DecidableEq W] [Fintype F] [Fintype W] in
/-- Two points of distinct colours on a line `line (0, w) c` determine `w` and `c`. -/
theorem wc_eq_of_two {w c w' c' : W} {a b : F} (hab : a ≠ b) (ha : w + a • c = w' + a • c')
    (hb : w + b • c = w' + b • c') : w = w' ∧ c = c' := by
  have h1 : (a - b) • (c - c') = 0 := by
    calc (a - b) • (c - c') = (w + a • c - (w' + a • c')) - (w + b • c - (w' + b • c')) := by module
      _ = 0 := by rw [ha, hb, sub_self, sub_self, sub_zero]
  have hc : c = c' := by
    have := congrArg (fun v => (a - b)⁻¹ • v) h1
    simp only [smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr hab), one_smul, smul_zero] at this
    exact sub_eq_zero.mp this
  subst hc
  exact ⟨add_right_cancel ha, rfl⟩

omit [Fintype F] in
theorem piece_injOn : Set.InjOn (piece (W := W) σ) (↑(pidx C)) := by
  rintro ⟨⟨c, w⟩, K⟩ hx ⟨⟨c', w'⟩, K'⟩ hx' h
  rw [Finset.mem_coe, pidx, Finset.mem_product] at hx hx'
  have h3 := src_card K hx.2
  obtain ⟨i1, hi1, i2, hi2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < K.card)
  have m1 : ptc σ w c i1 ∈ piece σ ((c', w'), K') := h ▸ Finset.mem_image_of_mem _ hi1
  have m2 : ptc σ w c i2 ∈ piece σ ((c', w'), K') := h ▸ Finset.mem_image_of_mem _ hi2
  obtain ⟨j1, -, e1⟩ := Finset.mem_image.mp m1
  obtain ⟨j2, -, e2⟩ := Finset.mem_image.mp m2
  simp only [ptc, Prod.mk.injEq] at e1 e2
  have hj1 : j1 = i1 := σ.injective e1.1
  have hj2 : j2 = i2 := σ.injective e2.1
  subst hj1 hj2
  obtain ⟨hw, hc⟩ := wc_eq_of_two (fun h' => hne (σ.injective h')) e1.2.symm e2.2.symm
  subst hw hc
  have : K = K' := Finset.image_injective (ptc_injective w c) h
  rw [this]

/-- All the source pieces. -/
def pieces (C : Finset W) (σ : Fin 6 ↪ F) : Finset (Finset (F × W)) := (pidx C).image (piece σ)

open Classical in
/-- The fractional source: `1/3` on every piece. -/
noncomputable def ysrc (C : Finset W) (σ : Fin 6 ↪ F) (S : Finset (F × W)) : ℝ :=
  if S ∈ pieces C σ then 1 / 3 else 0

omit [DecidableEq F] [DecidableEq W] [Fintype F] [Fintype W] in
theorem ptc_adj {c : W} (hc : c ∈ C) (w : W) {i j : Fin 6} (h : H12.graph.Adj i j) :
    (Bgr C σ).Adj (ptc σ w c i) (ptc σ w c j) := by
  refine ⟨fun h' => h.ne (ptc_injective w c h'), ⟨c, hc, ?_⟩, i, j, rfl, rfl, h⟩
  simp only [ptc, u, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul, mul_one]
  exact ⟨trivial, by module⟩

omit [Fintype F] [Fintype W] in
theorem mem_piece_iff {x : (W × W) × Finset (Fin 6)} {p : F × W} :
    p ∈ piece σ x ↔ ∃ i ∈ x.2, ptc σ x.1.2 x.1.1 i = p := Finset.mem_image

theorem resPack_ysrc : ResPack (ysrc C σ) where
  nonneg S := by unfold ysrc; split_ifs <;> norm_num
  two S h := by
    unfold ysrc at h
    split_ifs at h with hS
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hS
      rw [card_piece]
      have := src_card x.2 (Finset.mem_product.mp hx).2
      omega
    · exact absurd rfl h
  load a b hab := by
    classical
    set T := (pieces C σ).filter (fun S => a ∈ S ∧ b ∈ S) with hT
    have hsum : ∑ S, (if a ∈ S ∧ b ∈ S then ysrc C σ S else 0) = T.card * (1 / 3 : ℝ) := by
      rw [hT, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
      rw [← Finset.sum_subset (Finset.subset_univ (pieces C σ))]
      · refine Finset.sum_congr rfl fun S hS => ?_
        unfold ysrc
        rw [ite_eq_left hS]
        split_ifs <;> simp
      · intro S _ hS
        unfold ysrc
        rw [ite_eq_right hS]
        simp
    rw [hsum]
    have hT3 : T.card ≤ 3 := by
      rcases T.eq_empty_or_nonempty with h0 | ⟨S0, hS0⟩
      · rw [h0]; simp
      obtain ⟨hS0p, ha0, hb0⟩ := Finset.mem_filter.mp hS0
      obtain ⟨⟨⟨c, w⟩, K⟩, hx0, rfl⟩ := Finset.mem_image.mp hS0p
      obtain ⟨i, -, rfl⟩ := mem_piece_iff.mp ha0
      obtain ⟨j, -, rfl⟩ := mem_piece_iff.mp hb0
      have hij : i ≠ j := fun h => hab (by rw [h])
      refine (Finset.card_le_card ?_).trans
        ((Finset.card_image_le (s := src.filter fun K => i ∈ K ∧ j ∈ K)
          (f := fun K => piece σ ((c, w), K))).trans (src_pair i j hij))
      intro S hS
      obtain ⟨hSp, haS, hbS⟩ := Finset.mem_filter.mp hS
      obtain ⟨⟨⟨c', w'⟩, K'⟩, hx', rfl⟩ := Finset.mem_image.mp hSp
      obtain ⟨i', hi', e1⟩ := mem_piece_iff.mp haS
      obtain ⟨j', hj', e2⟩ := mem_piece_iff.mp hbS
      simp only [ptc, Prod.mk.injEq] at e1 e2
      have hii : i' = i := σ.injective e1.1
      have hjj : j' = j := σ.injective e2.1
      subst hii hjj
      obtain ⟨hw, hc⟩ := wc_eq_of_two (fun h => hij (σ.injective h)) e1.2 e2.2
      subst hw hc
      refine Finset.mem_image.mpr ⟨K', Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hx').2, hi',
        hj'⟩, rfl⟩
    have : (T.card : ℝ) ≤ 3 := by exact_mod_cast hT3
    linarith

/-- **L7.4.** The source has value at least `25/3` per block. -/
theorem value_ysrc :
    (25 / 3 : ℝ) * (C.card * Fintype.card W) ≤ ∑ S, ysrc C σ S * (w (Bgr C σ) S : ℝ) := by
  classical
  have h1 : ∑ S, ysrc C σ S * (w (Bgr C σ) S : ℝ) =
      ∑ x ∈ pidx C, (1 / 3 : ℝ) * (w (Bgr C σ) (piece σ x) : ℝ) := by
    rw [← Finset.sum_image (f := fun S => (1 / 3 : ℝ) * (w (Bgr C σ) S : ℝ)) piece_injOn]
    rw [← Finset.sum_subset (Finset.subset_univ (pieces C σ))]
    · refine Finset.sum_congr rfl fun S hS => ?_
      unfold ysrc
      rw [ite_eq_left (show S ∈ pieces C σ from hS)]
    · intro S _ hS
      unfold ysrc
      rw [ite_eq_right (show S ∉ pieces C σ from hS), zero_mul]
  have h2 : ∀ x ∈ pidx C, ((2 * (H12.eH x.2 : ℤ) - (x.2.card.choose 2 : ℕ) - 1 : ℤ) : ℝ) ≤
      (w (Bgr C σ) (piece σ x) : ℝ) := by
    rintro ⟨⟨c, w0⟩, K⟩ hx
    have hc : c ∈ C := (Finset.mem_product.mp (Finset.mem_product.mp hx).1).1
    have he : e H12.graph K ≤ e (Bgr C σ) (piece σ ((c, w0), K)) :=
      e_le_e_image (B := H12.graph) (Bgr C σ) (ptc σ w0 c) (ptc_injective w0 c).injOn
        fun i _ j _ h => ptc_adj hc w0 h
    rw [H12.e_graph_eq] at he
    unfold w
    rw [card_piece]
    have : (H12.eH K : ℝ) ≤ (e (Bgr C σ) (piece σ ((c, w0), K)) : ℝ) := by exact_mod_cast he
    push_cast
    linarith
  rw [h1]
  calc (25 / 3 : ℝ) * (C.card * Fintype.card W)
      = ∑ x ∈ pidx C, (1 / 3 : ℝ) *
          ((2 * (H12.eH x.2 : ℤ) - (x.2.card.choose 2 : ℕ) - 1 : ℤ) : ℝ) := by
        rw [← Finset.mul_sum, pidx, Finset.sum_product]
        simp only
        have hv : ∑ K ∈ src, ((2 * (H12.eH K : ℤ) - (K.card.choose 2 : ℕ) - 1 : ℤ) : ℝ) = 25 := by
          exact_mod_cast src_value
        rw [Finset.sum_congr rfl fun _ _ => hv, Finset.sum_const, Finset.card_product,
          Finset.card_univ, nsmul_eq_mul]
        push_cast
        ring
    _ ≤ _ := Finset.sum_le_sum fun x hx => by
        have := h2 x hx
        linarith

end GapExtremal
