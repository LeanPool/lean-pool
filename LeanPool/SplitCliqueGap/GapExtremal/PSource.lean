/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.PCore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# The fractional source on a positioned core (ledger §16.3, L7.4)

The nine source pieces of every selected line, realised through `D.rl`; none contains both labels
`0` and `2`
(which may share a base). `presPack` (capacity 1) and `pvalue` (`∑ y w ≥ 25/3 · |C| · |W|`).
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]
variable {V P : Type*} [Fintype V] [DecidableEq V] [DecidableEq P]
variable (D : PData F W V P) {C : Finset W}

theorem src_no02 : ∀ K ∈ src, ¬ ((0 : Fin 6) ∈ K ∧ (2 : Fin 6) ∈ K) := by decide +kernel

theorem not_adj02 : ¬ H12.graph.Adj 0 2 ∧ ¬ H12.graph.Adj 2 0 := by decide

/-- The base point of label `i` on `line (0, w) c`. -/
def ppt (w c : W) (i : Fin 6) : F × W := (D.col (D.σ i), w + D.col (D.σ i) • c)

/-- The vertex of label `i` on `line (0, w) c`. -/
def pvx (w c : W) (i : Fin 6) : V := D.rl (ppt D w c i) i

omit [DecidableEq F] [DecidableEq P] [DecidableEq V] [DecidableEq W] [Fintype F] [Fintype V]
    [Fintype W] in
theorem pvx_base (w c : W) (i : Fin 6) : D.base (pvx D w c i) = ppt D w c i :=
  D.rl_base _ _ rfl

omit [DecidableEq F] [DecidableEq P] [DecidableEq V] [DecidableEq W] [Fintype F] [Fintype V]
    [Fintype W] in
theorem pvx_pos (w c : W) (i : Fin 6) : D.pos (pvx D w c i) = D.σ i :=
  D.rl_pos _ _ rfl

omit [DecidableEq F] [DecidableEq P] [DecidableEq V] [DecidableEq W] [Fintype F] [Fintype V]
    [Fintype W] in
theorem pvx_injective (w c : W) : Function.Injective (pvx D w c) := fun i j h =>
  D.σ.injective (by rw [← pvx_pos D w c i, ← pvx_pos D w c j, h])

/-- A piece. -/
def ppiece (x : (W × W) × Finset (Fin 6)) : Finset V := x.2.image (pvx D x.1.2 x.1.1)

omit [DecidableEq F] [DecidableEq P] [DecidableEq W] [Fintype F] [Fintype V] [Fintype W] in
theorem card_ppiece (x : (W × W) × Finset (Fin 6)) : (ppiece D x).card = x.2.card :=
  Finset.card_image_of_injective _ (pvx_injective _ _ _)

omit [DecidableEq F] [DecidableEq P] [DecidableEq W] [Fintype F] [Fintype V] [Fintype W] in
theorem mem_ppiece {x : (W × W) × Finset (Fin 6)} {v : V} :
    v ∈ ppiece D x ↔ ∃ i ∈ x.2, pvx D x.1.2 x.1.1 i = v := Finset.mem_image

omit [DecidableEq F] [DecidableEq P] [DecidableEq V] [DecidableEq W] [Fintype F] [Fintype V]
    [Fintype W] in
/-- Colours of two labels of a source piece are distinct. -/
theorem col_ne_of_src {K : Finset (Fin 6)} (hK : K ∈ src) {i j : Fin 6} (hi : i ∈ K) (hj : j ∈ K)
    (hij : i ≠ j) : D.col (D.σ i) ≠ D.col (D.σ j) := by
  intro h
  rcases D.colσ i j h with h | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hij h
  · exact src_no02 K hK ⟨hi, hj⟩
  · exact src_no02 K hK ⟨hj, hi⟩

omit [DecidableEq F] [DecidableEq P] [DecidableEq W] [Fintype F] [Fintype V] in
theorem ppiece_injOn : Set.InjOn (ppiece D) (↑(pidx C)) := by
  rintro ⟨⟨c, w⟩, K⟩ hx ⟨⟨c', w'⟩, K'⟩ hx' h
  rw [Finset.mem_coe, pidx, Finset.mem_product] at hx hx'
  have h3 := src_card K hx.2
  obtain ⟨i1, hi1, i2, hi2, hne⟩ := Finset.one_lt_card.mp (by omega : 1 < K.card)
  have m1 : pvx D w c i1 ∈ ppiece D ((c', w'), K') := h ▸ Finset.mem_image_of_mem _ hi1
  have m2 : pvx D w c i2 ∈ ppiece D ((c', w'), K') := h ▸ Finset.mem_image_of_mem _ hi2
  obtain ⟨j1, -, e1⟩ := Finset.mem_image.mp m1
  obtain ⟨j2, -, e2⟩ := Finset.mem_image.mp m2
  have hj1 : j1 = i1 := D.σ.injective (by rw [← pvx_pos D w' c' j1, e1, pvx_pos])
  have hj2 : j2 = i2 := D.σ.injective (by rw [← pvx_pos D w' c' j2, e2, pvx_pos])
  subst hj1 hj2
  have b1 := congrArg D.base e1
  have b2 := congrArg D.base e2
  rw [pvx_base, pvx_base] at b1 b2
  simp only [ppt, Prod.mk.injEq] at b1 b2
  obtain ⟨hw, hc⟩ := wc_eq_of_two (col_ne_of_src D hx.2 hi1 hi2 hne) b1.2.symm b2.2.symm
  subst hw hc
  have : K = K' := Finset.image_injective (pvx_injective D w c) h
  rw [this]

/-- All pieces. -/
noncomputable def ppieces (C : Finset W) : Finset (Finset V) := (pidx C).image (ppiece D)

open Classical in
/-- The fractional source. -/
noncomputable def pysrc (C : Finset W) (S : Finset V) : ℝ := if S ∈ ppieces D C then 1 / 3 else 0

omit [DecidableEq F] [DecidableEq P] [DecidableEq W] [Fintype F] in
theorem presPack : ResPack (pysrc D C) where
  nonneg S := by unfold pysrc; split_ifs <;> norm_num
  two S h := by
    unfold pysrc at h
    split_ifs at h with hS
    · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hS
      rw [card_ppiece]
      have := src_card x.2 (Finset.mem_product.mp hx).2
      omega
    · exact absurd rfl h
  load a b hab := by
    classical
    set T := (ppieces D C).filter (fun S => a ∈ S ∧ b ∈ S)
    have hsum : ∑ S, (if a ∈ S ∧ b ∈ S then pysrc D C S else 0) = T.card * (1 / 3 : ℝ) :=
      by simpa only [pysrc, T] using source_pair_weight (ppieces D C) a b
    rw [hsum]
    have hT3 : T.card ≤ 3 := by
      rcases T.eq_empty_or_nonempty with h0 | ⟨S0, hS0⟩
      · rw [h0]; simp
      obtain ⟨hS0p, ha0, hb0⟩ := Finset.mem_filter.mp hS0
      obtain ⟨⟨⟨c, w⟩, K⟩, hx0, rfl⟩ := Finset.mem_image.mp hS0p
      have hK : K ∈ src := (Finset.mem_product.mp hx0).2
      obtain ⟨i, hi, rfl⟩ := (mem_ppiece D).mp ha0
      obtain ⟨j, hj, rfl⟩ := (mem_ppiece D).mp hb0
      have hij : i ≠ j := fun h => hab (by rw [h])
      have hcij := col_ne_of_src D hK hi hj hij
      refine (Finset.card_le_card ?_).trans
        ((Finset.card_image_le (s := src.filter fun K => i ∈ K ∧ j ∈ K)
          (f := fun K => ppiece D ((c, w), K))).trans (src_pair i j hij))
      intro S hS
      obtain ⟨hSp, haS, hbS⟩ := Finset.mem_filter.mp hS
      obtain ⟨⟨⟨c', w'⟩, K'⟩, hx', rfl⟩ := Finset.mem_image.mp hSp
      obtain ⟨i', hi', e1⟩ := (mem_ppiece D).mp haS
      obtain ⟨j', hj', e2⟩ := (mem_ppiece D).mp hbS
      have hii : i' = i := D.σ.injective (by rw [← pvx_pos D w' c' i', e1, pvx_pos])
      have hjj : j' = j := D.σ.injective (by rw [← pvx_pos D w' c' j', e2, pvx_pos])
      subst hii hjj
      have b1 := congrArg D.base e1
      have b2 := congrArg D.base e2
      rw [pvx_base, pvx_base] at b1 b2
      simp only [ppt, Prod.mk.injEq] at b1 b2
      obtain ⟨hw, hc⟩ := wc_eq_of_two hcij b1.2 b2.2
      subst hw hc
      exact Finset.mem_image.mpr ⟨K', Finset.mem_filter.mpr ⟨(Finset.mem_product.mp hx').2, hi',
        hj'⟩, rfl⟩
    have : (T.card : ℝ) ≤ 3 := by exact_mod_cast hT3
    linarith

omit [DecidableEq F] [DecidableEq P] [DecidableEq V] [DecidableEq W] [Fintype F] [Fintype V]
    [Fintype W] in
theorem pvx_adj {c : W} (hc : c ∈ C) (w0 : W) {i j : Fin 6} (h : H12.graph.Adj i j) :
    (PB D C).Adj (pvx D w0 c i) (pvx D w0 c j) := by
  have hcol : D.col (D.σ i) ≠ D.col (D.σ j) := by
    intro hh
    rcases D.colσ i j hh with h' | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.ne h'
    · exact not_adj02.1 h
    · exact not_adj02.2 h
  refine ⟨?_, ⟨c, hc, ?_⟩, i, j, (pvx_pos D w0 c i).symm, (pvx_pos D w0 c j).symm, h⟩
  · rw [pvx_base, pvx_base]
    intro hh
    exact hcol (congrArg Prod.fst hh)
  · rw [pvx_base, pvx_base]
    simp only [ppt, u, Prod.ext_iff, Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul, mul_one]
    exact ⟨trivial, by module⟩

omit [DecidableEq F] [DecidableEq P] [DecidableEq W] [Fintype F] in
/-- **L7.4** on a positioned core. -/
theorem pvalue :
    (25 / 3 : ℝ) * (C.card * Fintype.card W) ≤ ∑ S, pysrc D C S * (w (PB D C) S : ℝ) := by
  classical
  have h2 : ∀ x ∈ pidx C, ((2 * (H12.eH x.2 : ℤ) - (x.2.card.choose 2 : ℕ) - 1 : ℤ) : ℝ) ≤
      (w (PB D C) (ppiece D x) : ℝ) := by
    rintro ⟨⟨c, w0⟩, K⟩ hx
    have hc : c ∈ C := (Finset.mem_product.mp (Finset.mem_product.mp hx).1).1
    have he : e H12.graph K ≤ e (PB D C) (ppiece D ((c, w0), K)) :=
      e_le_e_image (B := H12.graph) (PB D C) (pvx D w0 c) (pvx_injective D w0 c).injOn
        fun i _ j _ h => pvx_adj D hc w0 h
    rw [H12.e_graph_eq] at he
    unfold w
    rw [card_ppiece]
    have : (H12.eH K : ℝ) ≤ (e (PB D C) (ppiece D ((c, w0), K)) : ℝ) := by exact_mod_cast he
    push_cast
    linarith
  have bound := source_score_bound C (ppiece D) (fun S => (w (PB D C) S : ℝ)) (ppiece_injOn D) h2
  refine bound.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro S _
  unfold pysrc ppieces
  by_cases hS : S ∈ (pidx C).image (ppiece D) <;> simp [hS]

end GapExtremal
