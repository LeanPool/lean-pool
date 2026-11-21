/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Frame

/-!
# The front end of the separator program: conventions

The phases of the separator program (namespace `PlanarSeparator.SepProg`: `BFS.lean`,
`LevelStat.lean`, `FaceRep.lean`, `StArr.lean`, the cycle search `CycleRun.lean`, `RootPath.lean`,
`InMark.lean`) read a plane rotation system with vertex weights from the input and compute the
separator of Lipton and Tarjan. This file fixes their conventions.

## The input

For `n` vertices and `m` darts, numbered so that the darts leaving a vertex `v` are the darts
`ofs v ≤ i < ofs (v + 1)`, the input is the list of `3 + 2 n + 3 m` words

`[n, m, ofs 0, …, ofs n, w 0, …, w (n-1), tl 0, rv 0, ro 0, …, tl (m-1), rv (m-1), ro (m-1)]`

with the weight `w v` of each vertex, and for each dart `i` its initial vertex `tl i`, its
reversal `rv i` and its successor `ro i` in the rotation at `tl i` (`InHolds`). The facts the
program uses about these numbers are collected in `NWf`.

## The registers

Registers `r63 … r99` are scratch. Registers `r100 … r121` hold constants and the bases of the
arrays (`Lay`), and `r122 … r131` the quantities computed along the way (the total weight, the
median level, `⌊√n⌋`, the thin levels, the outcome of the cycle search, the face and the flag of
the side of the cycle). The cycle search of `PlanarSeparator/Machine/CycleRun.lean` keeps every
register from `r63` on; it uses `r0 … r10` for its own constants.

## The memory

The cycle search uses `[0, 11 m)`. Above it: the face representatives at `11 m + i`, the inside
marks at `12 m + i`, and from `13 m` the vertex arrays (levels, parent darts, marks, queue,
separator marks), the weights and counts of the levels (`2 n + 2` cells each), the labels at
`13 m + 9 n + 4 + v`, and the weights and parts of the four pieces.

## A loop rule

`Exec.forN`: a loop `while i < N` whose body advances the counter by one, with a bounded body
cost, from `lo` to `N`.
-/

@[expose] public section

namespace WordRAM.Machine.Exec

variable {P : Input} {W : ℕ}

/-- **Counting loops.** If every iteration from a state `I i` with `i < N` reaches `I (i + 1)`
within `B` steps, the loop `while r_i < r_N` runs from `I lo` to `I N` within
`(B + 2) (N - lo) + 2` steps. -/
theorem forN {ri rN N lo B : ℕ} {body : Stmt} (I : ℕ → Config → Prop)
    (hI : ∀ i c, I i c → WordsBounded W c ∧ c.nreg ri = i ∧ c.nreg rN = N)
    (hbody : ∀ i c, I i c → i < N → ∃ c' k, Exec P W body c c' k ∧ I (i + 1) c' ∧ k ≤ B)
    (hlo : lo ≤ N) {c : Config} (hc : I lo c) :
    ∃ c' k, Exec P W (.whileLtN ri rN body) c c' k ∧ I N c' ∧ k ≤ (B + 2) * (N - lo) + 2 := by
  obtain ⟨c', k, e, ⟨i, hiN, hi⟩, hn, hk⟩ :=
    whileLtN_potential (P := P) (W := W) (a := ri) (b := rN)
    (body := body) (fun c => ∃ i, i ≤ N ∧ I i c) (fun c => (B + 2) * (N - c.nreg ri))
    (fun c ⟨i, _, h⟩ => (hI i c h).1)
    (fun c ⟨i, hiN, h⟩ hlt => by
      obtain ⟨-, h1, h2⟩ := hI i c h
      rw [h1, h2] at hlt
      obtain ⟨c', k, e, h', hk⟩ := hbody i c h hlt
      refine ⟨c', k, e, ⟨i + 1, hlt, h'⟩, ?_⟩
      rw [(hI _ _ h').2.1, h1]
      have : (B + 2) * (N - (i + 1)) + (B + 2) ≤ (B + 2) * (N - i) := by
        rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
      omega) ⟨lo, hlo, hc⟩
  obtain ⟨-, h1, h2⟩ := hI i c' hi
  rw [h1, h2] at hn
  obtain rfl : i = N := by omega
  refine ⟨c', k, e, hi, ?_⟩
  rw [(hI lo c hc).2.1] at hk
  exact hk

end WordRAM.Machine.Exec

namespace PlanarSeparator

namespace SepProg

open WordRAM WordRAM.Machine

/-- The input holds the rotation system. -/
structure InHolds (P : Input) (n m : ℕ) (ofs w tl rv ro : ℕ → ℕ) : Prop where
  n_eq : P.data.getD 0 0 = n
  m_eq : P.data.getD 1 0 = m
  ofs_eq : ∀ v ≤ n, P.data.getD (2 + v) 0 = ofs v
  w_eq : ∀ v < n, P.data.getD (n + 3 + v) 0 = w v
  tl_eq : ∀ i < m, P.data.getD (2 * n + 3 + 3 * i) 0 = tl i
  rv_eq : ∀ i < m, P.data.getD (2 * n + 3 + 3 * i + 1) 0 = rv i
  ro_eq : ∀ i < m, P.data.getD (2 * n + 3 + 3 * i + 2) 0 = ro i

/-- The numeric facts about a rotation system without loops whose darts are numbered vertex by
vertex. -/
structure NWf (n m : ℕ) (ofs tl rv ro : ℕ → ℕ) : Prop where
  tl_lt : ∀ i < m, tl i < n
  rv_lt : ∀ i < m, rv i < m
  rv_rv : ∀ i < m, rv (rv i) = i
  ro_lt : ∀ i < m, ro i < m
  ro_inj : ∀ i < m, ∀ j < m, ro i = ro j → i = j
  tl_ro : ∀ i < m, tl (ro i) = tl i
  tl_rv : ∀ i < m, tl (rv i) ≠ tl i
  ofs_mono : ∀ u v, u ≤ v → v ≤ n → ofs u ≤ ofs v
  ofs_n : ofs n = m
  blk : ∀ i < m, ∀ v < n, (tl i = v ↔ ofs v ≤ i ∧ i < ofs (v + 1))

/-- The face permutation, numerically: `φ i = ro (rv i)`. -/
def ph (rv ro : ℕ → ℕ) (i : ℕ) : ℕ := ro (rv i)

namespace NWf

variable {n m : ℕ} {ofs tl rv ro : ℕ → ℕ} (h : NWf n m ofs tl rv ro)
include h

theorem ph_lt {i : ℕ} (hi : i < m) : ph rv ro i < m := h.ro_lt _ (h.rv_lt i hi)

theorem ph_inj {i j : ℕ} (hi : i < m) (hj : j < m) (e : ph rv ro i = ph rv ro j) : i = j := by
  have := h.ro_inj _ (h.rv_lt i hi) _ (h.rv_lt j hj) e
  rw [← h.rv_rv i hi, ← h.rv_rv j hj, this]

theorem ofs_le_m {v : ℕ} (hv : v ≤ n) : ofs v ≤ m := h.ofs_n ▸ h.ofs_mono v n hv le_rfl

end NWf

/-- The constant registers: `r100 … r103 = 0, 1, 2, 3`, `r104 = n`, `r105 = m`, the bases of
the weights and the darts in the input, and the bases of the arrays in memory. -/
structure Lay (n m : ℕ) (c : Config) : Prop where
  r100 : c.nreg 100 = 0
  r101 : c.nreg 101 = 1
  r102 : c.nreg 102 = 2
  r103 : c.nreg 103 = 3
  r104 : c.nreg 104 = n
  r105 : c.nreg 105 = m
  r106 : c.nreg 106 = n + 3
  r107 : c.nreg 107 = 2 * n + 3
  r108 : c.nreg 108 = 3 * m
  r109 : c.nreg 109 = 6 * m
  r110 : c.nreg 110 = 11 * m
  r111 : c.nreg 111 = 12 * m
  r112 : c.nreg 112 = 13 * m
  r113 : c.nreg 113 = 13 * m + n
  r114 : c.nreg 114 = 13 * m + 2 * n
  r115 : c.nreg 115 = 13 * m + 3 * n
  r116 : c.nreg 116 = 13 * m + 4 * n
  r117 : c.nreg 117 = 13 * m + 5 * n
  r118 : c.nreg 118 = 13 * m + 7 * n + 2
  r119 : c.nreg 119 = 13 * m + 9 * n + 4
  r120 : c.nreg 120 = 13 * m + 10 * n + 4
  r121 : c.nreg 121 = 13 * m + 10 * n + 8

/-- The layout is kept by a state agreeing on `r100 … r121`. -/
theorem Lay.of {n m : ℕ} {c c' : Config} (h : Lay n m c)
    (e : ∀ r, 100 ≤ r → r ≤ 121 → c'.nreg r = c.nreg r) :
    Lay n m c' := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := h
  exact ⟨(e 100 (by omega) (by omega)).trans a0, (e 101 (by omega) (by omega)).trans a1,
    (e 102 (by omega) (by omega)).trans a2, (e 103 (by omega) (by omega)).trans a3,
    (e 104 (by omega) (by omega)).trans a4, (e 105 (by omega) (by omega)).trans a5,
    (e 106 (by omega) (by omega)).trans a6, (e 107 (by omega) (by omega)).trans a7,
    (e 108 (by omega) (by omega)).trans a8, (e 109 (by omega) (by omega)).trans a9,
    (e 110 (by omega) (by omega)).trans a10, (e 111 (by omega) (by omega)).trans a11,
    (e 112 (by omega) (by omega)).trans a12, (e 113 (by omega) (by omega)).trans a13,
    (e 114 (by omega) (by omega)).trans a14, (e 115 (by omega) (by omega)).trans a15,
    (e 116 (by omega) (by omega)).trans a16, (e 117 (by omega) (by omega)).trans a17,
    (e 118 (by omega) (by omega)).trans a18, (e 119 (by omega) (by omega)).trans a19,
    (e 120 (by omega) (by omega)).trans a20, (e 121 (by omega) (by omega)).trans a21⟩

/-- A statement writing only registers below `100` keeps the layout. -/
theorem Lay.exec {n m : ℕ} {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Lay n m c) (e : Exec P W s c c' k) (hs : s.wmax < 100) : Lay n m c' :=
  h.of fun _ hr _ => e.nreg_of_wr (Stmt.wr_of_wmax (by omega))

/-- A statement writing none of `r100 … r121` keeps the layout. -/
theorem Lay.exec' {n m : ℕ} {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Lay n m c) (e : Exec P W s c c' k) (hs : ∀ r, 100 ≤ r → r ≤ 121 → s.wr r = false) :
    Lay n m c' :=
  h.of fun r h1 h2 => e.nreg_of_wr (hs r h1 h2)

/-- The size of the memory used by the program. -/
def memTop (n m : ℕ) : ℕ := 13 * m + 10 * n + 12

end SepProg

end PlanarSeparator
