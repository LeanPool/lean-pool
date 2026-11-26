/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Geometry
public import LeanPool.SplitCliqueGap.GapExtremal.LocalEmbed
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# The core `F × W`, its blocks and the graph `B` (ledger §4–§5, §7)

* `line x c`: the affine line through `x` with direction `u c = (1, c)`;
* `blocks C`: all lines with direction in `C`;
* `Bgr C σ`: `x ~ y` iff `y - x` has a direction of `C` and the colours `x.1, y.1` are an edge of
`H12`
  (transported by `σ : Fin 6 ↪ F`).

Main results: `blockHyp` (the hypotheses of `global_bound`, from CAP) and `I_le` (`I(B) ≤ 8 ·
#blocks`).
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]

/-- The line through `x` with direction `u c`. -/
def line (x : F × W) (c : W) : Finset (F × W) := univ.image fun t : F => x + t • u c

omit [Fintype W] in
theorem mem_line {x y : F × W} {c : W} : y ∈ line x c ↔ ∃ t : F, y = x + t • u c := by
  simp [line, eq_comm]

omit [Fintype W] in
theorem self_mem_line (x : F × W) (c : W) : x ∈ line x c := mem_line.mpr ⟨0, by simp⟩

omit [Fintype W] in
theorem line_eq_of_mem {x y : F × W} {c : W} (h : y ∈ line x c) : line y c = line x c := by
  obtain ⟨t, rfl⟩ := mem_line.mp h
  ext z
  simp only [mem_line]
  constructor
  · rintro ⟨s, rfl⟩; exact ⟨t + s, by rw [add_smul]; abel⟩
  · rintro ⟨s, rfl⟩; exact ⟨s - t, by rw [sub_smul]; abel⟩

omit [Fintype W] in
/-- Two points of one line differ by a multiple of its direction. -/
theorem sub_of_mem_line {x p q : F × W} {c : W} (hp : p ∈ line x c) (hq : q ∈ line x c) :
    q - p = (q.1 - p.1) • u c := by
  obtain ⟨t, rfl⟩ := mem_line.mp hp
  obtain ⟨s, rfl⟩ := mem_line.mp hq
  ext
  · simp [u]
  · simp [u, sub_smul]

omit [Fintype W] in
theorem fst_injOn_line (x : F × W) (c : W) : Set.InjOn Prod.fst (line x c : Set (F × W)) := by
  intro p hp q hq h
  have := sub_of_mem_line hp hq
  rw [h, sub_self, zero_smul, sub_eq_zero] at this
  exact this.symm

variable (C : Finset W) (σ : Fin 6 ↪ F)

/-- The blocks: lines with direction in `C`. -/
def blocks : Finset (Finset (F × W)) := (univ ×ˢ C).image fun p => line p.1 p.2

/-- The graph `B`. -/
def Bgr : SimpleGraph (F × W) where
  Adj x y := x ≠ y ∧ (∃ c ∈ C, y - x = (y.1 - x.1) • u c) ∧
    ∃ i j, σ i = x.1 ∧ σ j = y.1 ∧ H12.graph.Adj i j
  symm := ⟨fun x y ⟨hne, ⟨c, hc, h⟩, i, j, hi, hj, hij⟩ =>
    ⟨hne.symm, ⟨c, hc, by
      have : x - y = -(y - x) := (neg_sub y x).symm
      rw [this, h, ← neg_smul, neg_sub]⟩, j, i, hj, hi, hij.symm⟩⟩
  loopless := ⟨fun x h => h.1 rfl⟩

open Classical in
noncomputable instance : DecidableRel (Bgr C σ).Adj := Classical.decRel _

variable {C σ}

omit [DecidableEq F] [DecidableEq W] [Fintype F] [Fintype W] in
theorem Bgr_fst_ne {x y : F × W} (h : (Bgr C σ).Adj x y) : x.1 ≠ y.1 := by
  obtain ⟨-, -, i, j, hi, hj, hij⟩ := h
  rw [← hi, ← hj]
  exact fun h' => hij.ne (σ.injective h')

omit [Fintype W] in
/-- Two distinct lines with directions in `C` share at most one point. -/
theorem card_inter_line_le {x x' : F × W} {c c' : W}
    (hne : line x c ≠ line x' c') : (line x c ∩ line x' c').card ≤ 1 := by
  rw [Finset.card_le_one]
  intro p hp q hq
  by_contra hpq
  obtain ⟨hp1, hp2⟩ := Finset.mem_inter.mp hp
  obtain ⟨hq1, hq2⟩ := Finset.mem_inter.mp hq
  have h1 := sub_of_mem_line hp1 hq1
  have h2 := sub_of_mem_line hp2 hq2
  have hne1 : q.1 - p.1 ≠ 0 := by
    intro h0
    rw [h0, zero_smul, sub_eq_zero] at h1
    exact hpq h1.symm
  obtain ⟨-, hcc⟩ := par_eq (h1.symm.trans h2)
  have hcc := hcc hne1
  subst hcc
  apply hne
  rw [← line_eq_of_mem hp1, ← line_eq_of_mem hp2]

theorem mem_blocks_of {x : F × W} {c : W} (hc : c ∈ C) : line x c ∈ blocks C :=
  Finset.mem_image.mpr ⟨(x, c), by simp [hc], rfl⟩

omit [DecidableEq F] [DecidableEq W] [Fintype F] [Fintype W] in
theorem snd_eq_of_sub {x y : F × W} {c : W} (h : y - x = (y.1 - x.1) • u c) :
    y.2 - x.2 = (y.1 - x.1) • c := by
  simpa [u] using congrArg Prod.snd h

omit [Fintype W] in
theorem mem_line_of_sub {x y : F × W} {c : W} (h : y - x = (y.1 - x.1) • u c) : y ∈ line x c :=
  mem_line.mpr ⟨y.1 - x.1, by rw [← h]; abel⟩

variable (hC : IsCap F (C : Set W))
include hC

/-- **L5.1.** Every triangle of `B` lies in a block. -/
theorem blocks_tri (x y z : F × W) (hxy : (Bgr C σ).Adj x y) (hyz : (Bgr C σ).Adj y z)
    (hxz : (Bgr C σ).Adj x z) : ∃ ℓ ∈ blocks C, x ∈ ℓ ∧ y ∈ ℓ ∧ z ∈ ℓ := by
  obtain ⟨a, ha, h1⟩ := hxy.2.1
  obtain ⟨b, hb, h2⟩ := hyz.2.1
  obtain ⟨c, hc, h3⟩ := hxz.2.1
  have hα : y.1 - x.1 ≠ 0 := sub_ne_zero.mpr (Bgr_fst_ne hxy).symm
  by_cases hab : a = b
  · subst hab
    refine ⟨line x a, mem_blocks_of ha, self_mem_line x a, mem_line_of_sub h1, ?_⟩
    refine mem_line.mpr ⟨(y.1 - x.1) + (z.1 - y.1), ?_⟩
    rw [add_smul, ← h1, ← h2]; abel
  by_cases hac : a = c
  · subst hac
    exact ⟨line x a, mem_blocks_of ha, self_mem_line x a, mem_line_of_sub h1, mem_line_of_sub h3⟩
  by_cases hbc : b = c
  · subst hbc
    refine ⟨line z b, mem_blocks_of hb, ?_, ?_, self_mem_line z b⟩
    · refine mem_line.mpr ⟨-(z.1 - x.1), ?_⟩
      rw [neg_smul, ← h3]; abel
    · refine mem_line.mpr ⟨-(z.1 - y.1), ?_⟩
      rw [neg_smul, ← h2]; abel
  exfalso
  have e1 := snd_eq_of_sub h1
  have e2 := snd_eq_of_sub h2
  have e3 := snd_eq_of_sub h3
  have := dep_zero hC ha hb hc hab hac hbc (α := y.1 - x.1) (β := z.1 - y.1) (γ := -(z.1 - x.1))
    (by ring) (by rw [← e1, ← e2, neg_smul, ← e3]; abel)
  exact hα this.1

/-- **L5.2.** A point outside a block has at most one `B`-neighbour in it. -/
theorem blocks_one (ℓ : Finset (F × W)) (hℓ : ℓ ∈ blocks C) (z : F × W) (hz : z ∉ ℓ)
    (y : F × W) (hy : y ∈ ℓ) (y' : F × W) (hy' : y' ∈ ℓ) (h : (Bgr C σ).Adj z y)
    (h' : (Bgr C σ).Adj z y') : y = y' := by
  obtain ⟨⟨x0, c0⟩, hp, rfl⟩ := Finset.mem_image.mp hℓ
  have hc0 : c0 ∈ C := (Finset.mem_product.mp hp).2
  simp only at hy hy' hz
  by_contra hne
  have hyy := sub_of_mem_line hy hy'
  have hγ : y'.1 - y.1 ≠ 0 := fun h0 =>
    hne (fst_injOn_line x0 c0 hy hy' (sub_eq_zero.mp h0).symm)
  obtain ⟨d, hd, hzy⟩ := h.2.1
  obtain ⟨e', he, hzy'⟩ := h'.2.1
  by_cases hdc : d = c0
  · subst hdc
    apply hz
    rw [← line_eq_of_mem hy]
    refine mem_line.mpr ⟨-(y.1 - z.1), ?_⟩
    rw [neg_smul, ← hzy]; abel
  by_cases hec : e' = c0
  · subst hec
    apply hz
    rw [← line_eq_of_mem hy']
    refine mem_line.mpr ⟨-(y'.1 - z.1), ?_⟩
    rw [neg_smul, ← hzy']; abel
  by_cases hde : d = e'
  · subst hde
    have : (y'.1 - y.1) • (u d : F × W) = (y'.1 - y.1) • u c0 := by
      rw [← hyy]
      have : y' - y = (y' - z) - (y - z) := by abel
      rw [this, hzy, hzy', ← sub_smul]
      congr 1; ring
    exact hdc ((par_eq this).2 hγ)
  have e1 := snd_eq_of_sub hzy
  have e2 := snd_eq_of_sub hzy'
  have e3 := snd_eq_of_sub hyy
  have := dep_zero hC he hd hc0 (Ne.symm hde) hec hdc (α := y'.1 - z.1) (β := -(y.1 - z.1))
    (γ := -(y'.1 - y.1)) (by ring) (by rw [← e2, neg_smul, ← e1, neg_smul, ← e3]; abel)
  exact Bgr_fst_ne h' (sub_eq_zero.mp this.1).symm

/-- The block hypotheses hold for the selected lines of a cap. -/
theorem blockHyp : BlockHyp (Bgr C σ) (blocks C) where
  inter := by
    intro ℓ hℓ ℓ' hℓ' hne
    obtain ⟨⟨x, c⟩, -, rfl⟩ := Finset.mem_image.mp hℓ
    obtain ⟨⟨x', c'⟩, -, rfl⟩ := Finset.mem_image.mp hℓ'
    exact card_inter_line_le hne
  edge := by
    intro x y h
    obtain ⟨c, hc, hxy⟩ := h.2.1
    exact ⟨line x c, mem_blocks_of hc, self_mem_line x c, mem_line_of_sub hxy⟩
  tri := blocks_tri hC
  one := blocks_one hC

/-- **`I(B) ≤ 8 τ`** on the concrete core. -/
theorem I_le {T : Finset (Finset (F × W))} (hT : IsPack T) :
    ∑ Q ∈ T, w (Bgr C σ) Q ≤ 8 * (blocks (F := F) C).card := by
  refine global_bound (blockHyp hC) 8 ?_ hT
  intro ℓ hℓ T' hT'sub hT'
  obtain ⟨⟨x, c⟩, -, rfl⟩ := Finset.mem_image.mp hℓ
  have := block_local (B := Bgr C σ) Prod.fst σ (fst_injOn_line x c)
    (fun u _ v _ huv => by
      obtain ⟨-, -, i, j, hi, hj, hij⟩ := huv
      exact ⟨i, j, hi, hj, hij⟩) T' hT'sub hT'
  simpa using this

end GapExtremal
