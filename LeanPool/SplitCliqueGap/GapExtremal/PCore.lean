/-
Copyright (c) 2026 Juan Pablo Traverso Gianini. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juan Pablo Traverso Gianini
-/
/- Modified by Lean Pool contributors for the current Lean and Mathlib toolchain. -/
module

public import LeanPool.SplitCliqueGap.GapExtremal.Global2
public import LeanPool.SplitCliqueGap.GapExtremal.Source
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Positioned cores (ledger §16.3)

A core `V` with a base map `base : V → F × W` and a position map `pos : V → P`; the gadget labels
are placed by
`σ : Fin 6 ↪ P`, and each position has a colour `col : P → F` with `(base v).1 = col (pos v)`.
Several vertices may share a base (twins), at most two, with distinct positions.

`PB`: `v ~ v'` iff the bases differ by a selected direction and the positions carry adjacent `H12`
labels.
Blocks: for each selected line, the vertices on it whose position is a label.

Results: `pblockHyp` (hypotheses of `global_bound2`) and `pI_le` (`I(B) ≤ 8 · #blocks`).
-/

@[expose] public section

namespace GapExtremal

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [AddCommGroup W] [Module F W] [Fintype W] [DecidableEq W]

/-! ### Positioned cores -/

/-- Data of a positioned core. -/
structure PData (F W V P : Type*) where
  /-- The field and vector coordinates of each core vertex. -/
  base : V → F × W
  /-- The position of each vertex within its base fibre. -/
  pos : V → P
  /-- The field coordinate assigned to each position. -/
  col : P → F
  /-- The six distinguished positions used for the core roles. -/
  σ : Fin 6 ↪ P
  base_fst : ∀ v, (base v).1 = col (pos v)
  inj : ∀ v v', base v = base v' → pos v = pos v' → v = v'
  fib : ∀ v v' v'', base v = base v' → base v = base v'' → v = v' ∨ v = v'' ∨ v' = v''
  /-- A distinguished vertex at the given base coordinate and role. -/
  rl : F × W → Fin 6 → V
  rl_base : ∀ y i, y.1 = col (σ i) → base (rl y i) = y
  rl_pos : ∀ y i, y.1 = col (σ i) → pos (rl y i) = σ i
  colσ : ∀ i j, col (σ i) = col (σ j) → i = j ∨ (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0)

variable {V P : Type*} [Fintype V] [DecidableEq V] [DecidableEq P]

/-- The graph `B` of a positioned core. -/
def PB (D : PData F W V P) (C : Finset W) : SimpleGraph V where
  Adj v v' := D.base v ≠ D.base v' ∧
    (∃ c ∈ C, D.base v' - D.base v = ((D.base v').1 - (D.base v).1) • u c) ∧
    ∃ i j, D.σ i = D.pos v ∧ D.σ j = D.pos v' ∧ H12.graph.Adj i j
  symm := ⟨fun v v' ⟨hne, ⟨c, hc, h⟩, i, j, hi, hj, hij⟩ =>
    ⟨hne.symm, ⟨c, hc, by
      have : D.base v - D.base v' = -(D.base v' - D.base v) := (neg_sub _ _).symm
      rw [this, h, ← neg_smul, neg_sub]⟩, j, i, hj, hi, hij.symm⟩⟩
  loopless := ⟨fun v h => h.1 rfl⟩

open Classical in
noncomputable instance (D : PData F W V P) (C : Finset W) : DecidableRel (PB D C).Adj :=
  Classical.decRel _

open Classical in
/-- The block of a selected line. -/
noncomputable def pblock (D : PData F W V P) (x : F × W) (c : W) : Finset V :=
  univ.filter fun v => D.base v ∈ line x c ∧ ∃ i, D.σ i = D.pos v

/-- The blocks. -/
noncomputable def pblocks (D : PData F W V P) (C : Finset W) : Finset (Finset V) :=
  (C ×ˢ univ).image fun p : W × W => pblock D ((0 : F), p.2) p.1

variable (D : PData F W V P) {C : Finset W}

omit [DecidableEq V] [Fintype W] in
theorem mem_pblock {x : F × W} {c : W} {v : V} :
    v ∈ pblock D x c ↔ D.base v ∈ line x c ∧ ∃ i, D.σ i = D.pos v := by
  classical
  unfold pblock
  simp

theorem pblock_mem (hc : c ∈ C) (x : F × W) : pblock D x c ∈ pblocks D C := by
  rw [show pblock D x c = pblock D ((0 : F), x.2 - x.1 • c) c by
    unfold pblock; rw [line_eq_line_zero x c]]
  exact Finset.mem_image.mpr ⟨(c, x.2 - x.1 • c), by simp [hc], rfl⟩

theorem card_pblocks_le : (pblocks D C).card ≤ C.card * Fintype.card W := by
  unfold pblocks
  refine Finset.card_image_le.trans ?_
  simp

omit [DecidableEq F] [DecidableEq P] [DecidableEq V] [DecidableEq W] [Fintype F] [Fintype V]
  [Fintype W] in
theorem PB_adj_pos {v v' : V} (h : (PB D C).Adj v v') : (∃ i, D.σ i = D.pos v) ∧ ∃ j,
  D.σ j = D.pos v' :=
  by obtain ⟨-, -, i, j, hi, hj, -⟩ := h; exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩

section ActiveCap

/-- Active colours of a positioned core. -/
def actCol : Set F := Set.range fun i => D.col (D.σ i)

omit [Field F] [AddCommGroup W] [Module F W]
    [DecidableEq F] [DecidableEq P] [DecidableEq V] [DecidableEq W] [Fintype F] [Fintype V]
    [Fintype W] in
theorem fst_mem_actCol {v : V} (h : ∃ i, D.σ i = D.pos v) : (D.base v).1 ∈ actCol D := by
  obtain ⟨i, hi⟩ := h
  exact ⟨i, by rw [D.base_fst]; exact congrArg D.col hi⟩

variable (hC : IsSCap (actCol D) (C : Set W))
include hC

theorem pblockHyp_s : BlockHyp2 (PB D C) (pblocks D C) where
  edge := by
    intro v v' h
    obtain ⟨hv, hv'⟩ := PB_adj_pos D h
    obtain ⟨-, ⟨c, hc, hdir⟩, -⟩ := h
    refine ⟨pblock D (D.base v) c, pblock_mem D hc _, ?_, ?_⟩
    · exact (mem_pblock D).mpr ⟨self_mem_line _ _, hv⟩
    · exact (mem_pblock D).mpr ⟨mem_line_of_sub hdir, hv'⟩
  tri := by
    intro a b x hab hbx hax
    have pa := (PB_adj_pos D hab).1
    have pb := (PB_adj_pos D hab).2
    have px := (PB_adj_pos D hbx).2
    obtain ⟨hne, ⟨c1, hc1, h1⟩, -⟩ := hab
    obtain ⟨-, ⟨c2, hc2, h2⟩, -⟩ := hbx
    obtain ⟨-, ⟨c3, hc3, h3⟩, -⟩ := hax
    obtain ⟨d, hd, p, ha, hb, hx⟩ := tri_geom_s hC hc1 hc2 hc3 hne (fst_mem_actCol D pa)
      (fst_mem_actCol D pb) (fst_mem_actCol D px) h1 h2 h3
    refine ⟨pblock D p d, pblock_mem D hd p, ?_, ?_, ?_⟩
    · exact (mem_pblock D).mpr ⟨ha, pa⟩
    · exact (mem_pblock D).mpr ⟨hb, pb⟩
    · exact (mem_pblock D).mpr ⟨hx, px⟩
  two := by
    intro ℓ hℓ z hz y hy y' hy' y'' hy'' h1 h2 h3
    obtain ⟨⟨c0, w0⟩, hp, rfl⟩ := Finset.mem_image.mp hℓ
    have hc0 : c0 ∈ C := (Finset.mem_product.mp hp).1
    rw [mem_pblock] at hy hy' hy''
    have pz := (PB_adj_pos D h1).1
    have hzl : D.base z ∉ line ((0 : F), w0) c0 := fun hzl =>
      hz ((mem_pblock D).mpr ⟨hzl, pz⟩)
    obtain ⟨-, ⟨d1, hd1, e1⟩, -⟩ := h1
    obtain ⟨-, ⟨d2, hd2, e2⟩, -⟩ := h2
    obtain ⟨-, ⟨d3, hd3, e3⟩, -⟩ := h3
    have b12 := one_geom_s hC hc0 hzl hy.1 hy'.1 (fst_mem_actCol D pz) (fst_mem_actCol D hy.2)
      (fst_mem_actCol D hy'.2) hd1 hd2 e1 e2
    have b13 := one_geom_s hC hc0 hzl hy.1 hy''.1 (fst_mem_actCol D pz) (fst_mem_actCol D hy.2)
      (fst_mem_actCol D hy''.2) hd1 hd3 e1 e3
    exact D.fib y y' y'' b12 b13
  nonadj := by
    intro ℓ hℓ z hz y hy y' hy' h1 h2 hyy
    obtain ⟨⟨c0, w0⟩, hp, rfl⟩ := Finset.mem_image.mp hℓ
    have hc0 : c0 ∈ C := (Finset.mem_product.mp hp).1
    rw [mem_pblock] at hy hy'
    have pz := (PB_adj_pos D h1).1
    have hzl : D.base z ∉ line ((0 : F), w0) c0 := fun hzl =>
      hz ((mem_pblock D).mpr ⟨hzl, pz⟩)
    obtain ⟨-, ⟨d1, hd1, e1⟩, -⟩ := h1
    obtain ⟨-, ⟨d2, hd2, e2⟩, -⟩ := h2
    exact hyy.1 (one_geom_s hC hc0 hzl hy.1 hy'.1 (fst_mem_actCol D pz) (fst_mem_actCol D hy.2)
      (fst_mem_actCol D hy'.2) hd1 hd2 e1 e2)

/-- **`I(B) ≤ 8 · #blocks`** under an S-cap. -/
theorem pI_le_s {T : Finset (Finset V)} (hT : IsPack T) :
    ∑ Q ∈ T, w (PB D C) Q ≤ 8 * (pblocks D C).card := by
  refine global_bound2 (pblockHyp_s D hC) 8 ?_ hT
  intro ℓ hℓ T' hT'sub hT'
  obtain ⟨⟨c0, w0⟩, -, rfl⟩ := Finset.mem_image.mp hℓ
  have hinj : Set.InjOn D.pos (pblock D ((0 : F), w0) c0 : Set V) := by
    intro v hv v' hv' h
    rw [Finset.mem_coe, mem_pblock] at hv hv'
    apply D.inj v v' _ h
    apply fst_injOn_line _ _ hv.1 hv'.1
    rw [D.base_fst, D.base_fst, h]
  have := block_local (B := PB D C) D.pos D.σ hinj
    (fun v _ v' _ h => by
      obtain ⟨-, -, i, j, hi, hj, hij⟩ := h
      exact ⟨i, j, hi, hj, hij⟩) T' hT'sub hT'
  simpa using this

end ActiveCap

variable (hC : IsCap F (C : Set W))
include hC

theorem pblockHyp : BlockHyp2 (PB D C) (pblocks D C) :=
  pblockHyp_s D hC.isSCap

/-- Bound the integral packing score of a positioned core from an ordinary cap. -/
theorem pI_le {T : Finset (Finset V)} (hT : IsPack T) :
    ∑ Q ∈ T, w (PB D C) Q ≤ 8 * (pblocks D C).card :=
  pI_le_s D hC.isSCap hT

end GapExtremal
