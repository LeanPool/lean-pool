/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Front

/-!
# The separator program: the root paths of the fundamental cycle

After the cycle search, the dart `a` (in `r129`) of the stellar subdivision and its reversal
`A a` give two root paths of the spanning tree. Their vertices of the input graph are marked at
`13 m + 4 n + v` (`walk`), starting from the vertex of the input graph nearest to the vertex of the
dart (`uOf`: a centre of a face hangs from the initial vertex of the representative of the
face). In mode `1` the corners of the last triangle of the walk, the darts `δ / 3` and its
reversal (`r128`), are marked too.
-/

@[expose] public section

namespace PlanarSeparator

namespace SepProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The programs -/

/-- `r80 :=` the vertex of the input graph of the stellar dart `r81 = y`. -/
def uOf : Stmt :=
  .seq (block [.divN 83 81 103, .modN 84 81 103])
  (.ifLtN 84 101 (block [.addN 70 83 83, .addN 70 70 83, .addN 70 70 107, .readIn 80 70])
    (.ifLtN 84 102 (block [.addN 70 83 83, .addN 70 70 83, .addN 70 70 107, .addN 70 70 101,
        .readIn 85 70, .addN 70 85 85, .addN 70 70 85, .addN 70 70 107, .readIn 80 70])
      (block [.addN 69 110 83, .loadN 85 69, .subN 85 85 101, .addN 70 85 85, .addN 70 70 85,
        .addN 70 70 107, .readIn 80 70])))

/-- One step up from `r80 = u`, marking it. -/
def wStep : Stmt := block [.addN 69 113 80, .loadN 85 69, .addN 70 85 85, .addN 70 70 85,
  .addN 70 70 107, .addN 70 70 101, .readIn 86 70, .addN 70 86 86, .addN 70 70 86, .addN 70 70 107,
  .readIn 87 70, .addN 69 112 87, .loadN 82 69, .addN 69 116 80, .storeN 69 101, .copyN 80 87]

/-- **The root path from `r80 = u`**, marked. -/
def walkUp : Stmt :=
  .seq (block [.addN 69 112 80, .loadN 82 69])
    (.seq (.whileLtN 100 82 wStep) (block [.addN 69 116 80, .storeN 69 101]))

/-- The two corners of the input graph of the triangle `r128 = δ`, in mode `1`. -/
def xMark : Stmt := .ifLtN 100 127 (block [.divN 83 128 103, .addN 70 83 83, .addN 70 70 83,
  .addN 70 70 107, .readIn 80 70, .addN 69 116 80, .storeN 69 101, .addN 70 70 101,
  .readIn 85 70, .addN 70 85 85, .addN 70 70 85, .addN 70 70 107, .readIn 80 70,
  .addN 69 116 80, .storeN 69 101]) .skip

/-- **The separator marks**: the root paths of `a = r129` and of `A a`, and the corners. -/
def rootPaths : Stmt :=
  .seq (.instr (.copyN 81 129)) (.seq uOf (.seq walkUp (.seq (.instr (.loadN 81 129))
    (.seq uOf (.seq walkUp xMark)))))

/-! ### The specifications -/

/-- The vertex of the input graph of the stellar dart `y`, numerically. -/
def uN (tl rv fr : ℕ → ℕ) (y : ℕ) : ℕ :=
  if y % 3 = 0 then tl (y / 3) else if y % 3 = 1 then tl (rv (y / 3)) else tl (fr (y / 3) - 1)

/-- The parent of a vertex, numerically. -/
def parN (tl rv pr : ℕ → ℕ) (v : ℕ) : ℕ := tl (rv (pr v))

/-- The ancestors of `u`. -/
def AncN (tl rv pr L : ℕ → ℕ) (u x : ℕ) : Prop := ∃ k ≤ L u, (parN tl rv pr)^[k] u = x

section proofs

variable {n m : ℕ} {ofs w tl rv ro : ℕ → ℕ} {W : ℕ} {P : Input}
  (hN : NWf n m ofs tl rv ro) (hIn : InHolds P n m ofs w tl rv ro)
  (hW : memTop n m + 2 * n + 3 * m + 10 ≤ W) (hPW : ∀ j, P.data.getD j 0 ≤ W)
include hN hIn hW hPW

omit hPW in
theorem uOf_exec (fr : ℕ → ℕ) (hfr : ∀ q < m, 1 ≤ fr q ∧ fr q ≤ m) (c : Config)
    (hc : WordsBounded W c) (hL : Lay n m c) (hfrm : ∀ q < m, c.nmem (11 * m + q) = fr q)
    (hy : c.nreg 81 < 3 * m) :
    ∃ c' k, Exec P W uOf c c' k ∧ k ≤ 14 ∧ c'.nreg 80 = uN tl rv fr (c.nreg 81) ∧
      uN tl rv fr (c.nreg 81) < n ∧ c'.nmem = c.nmem ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) := by
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  generalize hy' : c.nreg 81 = y at hy
  have hq : y / 3 < m := by omega
  have hrv := hN.rv_lt _ hq
  obtain ⟨hf1, hf2⟩ := hfr _ hq
  have ht1 := hN.tl_lt _ hq
  have ht2 := hN.tl_lt _ hrv
  have ht3 := hN.tl_lt (fr (y / 3) - 1) (by omega)
  obtain ⟨c', k, e, h80, hk⟩ :
      ∃ c' k, Exec P W uOf c c' k ∧ c'.nreg 80 = uN tl rv fr y ∧ k ≤ 14 := by
    unfold uOf
    refine spec_seq ?_
    exec_block
    config_simp
    rw [a3, hy'] at *
    by_cases h0 : y % 3 = 0
    · refine spec_ifLtN_true (by config_simp; rw [a1]; omega) ?_
      have r1 : P.data.getD (y / 3 + y / 3 + y / 3 + c.nreg 107) 0 = tl (y / 3) := by
        rw [a7, show y / 3 + y / 3 + y / 3 + (2 * n + 3) = 2 * n + 3 + 3 * (y / 3) by omega]
        exact hIn.tl_eq _ hq
      exec_block
      all_goals try (config_simp; (try simp only [r1]); omega)
      refine ⟨by config_simp; rw [r1]; simp [uN, h0], by omega⟩
    · refine spec_ifLtN_false (by config_simp; rw [a1]; omega) ?_
      by_cases h1 : y % 3 = 1
      · refine spec_ifLtN_true (by config_simp; rw [a2]; omega) ?_
        have r1 : P.data.getD (y / 3 + y / 3 + y / 3 + c.nreg 107 + c.nreg 101) 0 = rv (y / 3) := by
          rw [a7, a1, show y / 3 + y / 3 + y / 3 + (2 * n + 3) + 1 =
            2 * n + 3 + 3 * (y / 3) + 1 by omega]
          exact hIn.rv_eq _ hq
        have r2 : P.data.getD (rv (y / 3) + rv (y / 3) + rv (y / 3) + c.nreg 107) 0 =
            tl (rv (y / 3)) := by
          rw [a7, show rv (y / 3) + rv (y / 3) + rv (y / 3) + (2 * n + 3) =
            2 * n + 3 + 3 * rv (y / 3) by omega]
          exact hIn.tl_eq _ hrv
        exec_block
        all_goals try (config_simp; (try simp only [r1, r2]); omega)
        refine ⟨by config_simp; rw [r1, r2]; simp [uN, h1], by omega⟩
      · refine spec_ifLtN_false (by config_simp; rw [a2]; omega) ?_
        have r1 : c.nmem (c.nreg 110 + y / 3) = fr (y / 3) := by rw [a10]; exact hfrm _ hq
        have r2 : P.data.getD (fr (y / 3) - c.nreg 101 + (fr (y / 3) - c.nreg 101) +
            (fr (y / 3) - c.nreg 101) + c.nreg 107) 0 = tl (fr (y / 3) - 1) := by
          rw [a7, a1, show fr (y / 3) - 1 + (fr (y / 3) - 1) + (fr (y / 3) - 1) + (2 * n + 3) =
            2 * n + 3 + 3 * (fr (y / 3) - 1) by omega]
          exact hIn.tl_eq _ (by omega)
        exec_block
        all_goals try (config_simp; (try simp only [r1, r2]); omega)
        refine ⟨by config_simp; rw [r1, r2]; simp [uN, h0, h1], by omega⟩
  have hun : uN tl rv fr y < n := by
    unfold uN; split_ifs
    · exact hN.tl_lt _ hq
    · exact hN.tl_lt _ hrv
    · exact hN.tl_lt _ (by omega)
  have hwm : uOf.wmax = 85 := by decide
  exact ⟨c', k, e, hk, h80, hun, e.nmem_of_st (by decide), e.output_of_ou (by decide),
    fun r hr => e.nreg_of_wr (Stmt.wr_of_wmax (by omega))⟩


open Classical in
omit hPW in
/-- **The root path from `r80 = u`.** -/
theorem walkUp_exec (pr L : ℕ → ℕ)
    (hpar : ∀ v < n, v ≠ 0 → pr v < m ∧ tl (pr v) = v ∧ L (parN tl rv pr v) + 1 = L v)
    (hL0 : L 0 = 0) (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (hprm : ∀ v < n, c.nmem (13 * m + n + v) = pr v) (hLm : ∀ v < n, c.nmem (13 * m + v) = L v)
    (hu : c.nreg 80 < n) :
    ∃ c' k, Exec P W walkUp c c' k ∧ k ≤ 18 * L (c.nreg 80) + 6 ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, ¬ (13 * m + 4 * n ≤ a ∧ a < 13 * m + 5 * n) → c'.nmem a = c.nmem a) ∧
      (∀ x < n, c'.nmem (13 * m + 4 * n + x) =
        if AncN tl rv pr L (c.nreg 80) x then 1 else c.nmem (13 * m + 4 * n + x)) := by
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  generalize hu0 : c.nreg 80 = u₀ at hu
  set f := parN tl rv pr
  have hfn : ∀ v < n, v ≠ 0 → f v < n := fun v hv h0 =>
    hN.tl_lt _ (hN.rv_lt _ (hpar v hv h0).1)
  have hit : ∀ k, k ≤ L u₀ → f^[k] u₀ < n ∧ L (f^[k] u₀) + k = L u₀ := by
    intro k hk
    induction k with
    | zero => exact ⟨hu, by simp⟩
    | succ k ih =>
      obtain ⟨h1, h2⟩ := ih (by omega)
      have h0 : f^[k] u₀ ≠ 0 := fun e => by rw [e, hL0] at h2; omega
      obtain ⟨-, -, h3⟩ := hpar _ h1 h0
      rw [Function.iterate_succ_apply']
      exact ⟨hfn _ h1 h0, by omega⟩
  -- the start
  have r0 : c.nmem (c.nreg 112 + c.nreg 80) = L u₀ := by rw [a12, hu0]; exact hLm _ hu
  let I : ℕ → Config → Prop := fun k c' => WordsBounded W c' ∧ c'.output = c.output ∧
    (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧ k ≤ L u₀ ∧ c'.nreg 80 = f^[k] u₀ ∧
    c'.nreg 82 = L (f^[k] u₀) ∧
    (∀ a, ¬ (13 * m + 4 * n ≤ a ∧ a < 13 * m + 5 * n) → c'.nmem a = c.nmem a) ∧
    (∀ x < n, c'.nmem (13 * m + 4 * n + x) =
      if (∃ k' < k, f^[k'] u₀ = x) then 1 else c.nmem (13 * m + 4 * n + x))
  have e₁ : ∃ c₁ k₁, Exec P W (block [.addN 69 112 80, .loadN 82 69]) c c₁ k₁ ∧
      I 0 c₁ ∧ k₁ = 2 := by
    exec_block
    · rw [a12, hu0]; omega
    exact ⟨⟨‹_›, rfl, fun r hr => by
      config_simp; simp only [upd_apply]; split_ifs <;> omega,
      le_refl _ |>.trans (Nat.zero_le _), by config_simp; exact hu0, by config_simp; rw [r0]; rfl,
      fun a _ => rfl, fun x _ => by simp⟩, rfl⟩
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ := e₁
  obtain ⟨k', c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_ghost (P := P) (W := W) (a := 100)
    (b := 82) (body := wStep) I (fun k _ => 18 * (L u₀ - k)) (fun k c' h => h.1)
    (fun k c' h hlt => by
      obtain ⟨hw, ho, hr, hk, h80, h82, hfr, hm⟩ := h
      have g : ∀ r, 100 ≤ r → c'.nreg r = c.nreg r := hr
      rw [g 100 (by omega), a0, h82] at hlt
      obtain ⟨hun, hlu⟩ := hit k hk
      generalize hv : f^[k] u₀ = v at h80 h82 hun hlu hlt
      have hv0 : v ≠ 0 := fun e => by rw [e, hL0] at hlt; omega
      obtain ⟨hpv, htv, hLv⟩ := hpar v hun hv0
      have hrv := hN.rv_lt _ hpv
      have hfv := hfn v hun hv0
      have r1 : c'.nmem (c'.nreg 113 + c'.nreg 80) = pr v := by
        rw [g 113 (by omega), a13, h80, hfr _ (by omega)]; exact hprm v hun
      have r2 : P.data.getD (pr v + pr v + pr v + c'.nreg 107 + c'.nreg 101) 0 = rv (pr v) := by
        rw [g 107 (by omega), a7, g 101 (by omega), a1,
          show pr v + pr v + pr v + (2 * n + 3) + 1 = 2 * n + 3 + 3 * pr v + 1 by omega]
        exact hIn.rv_eq _ hpv
      have r3 : P.data.getD (rv (pr v) + rv (pr v) + rv (pr v) + c'.nreg 107) 0 = f v := by
        rw [g 107 (by omega), a7,
          show rv (pr v) + rv (pr v) + rv (pr v) + (2 * n + 3) = 2 * n + 3 + 3 * rv (pr v) by omega]
        exact hIn.tl_eq _ hrv
      have r4 : c'.nmem (c'.nreg 112 + f v) = L (f v) := by
        rw [g 112 (by omega), a12, hfr _ (by omega)]; exact hLm _ hfv
      have hwm : wStep.wmax = 87 := by decide
      obtain ⟨c'', k'', e, h80', h82', hm', hk''⟩ : ∃ c'' k'', Exec P W wStep c' c'' k'' ∧
          c''.nreg 80 = f v ∧ c''.nreg 82 = L (f v) ∧
          c''.nmem = upd c'.nmem (13 * m + 4 * n + v) 1 ∧ k'' = 16 := by
        have g113 : c'.nreg 113 = 13 * m + n := by rw [g 113 (by omega), a13]
        have g112 : c'.nreg 112 = 13 * m := by rw [g 112 (by omega), a12]
        have g116 : c'.nreg 116 = 13 * m + 4 * n := by rw [g 116 (by omega), a16]
        have g107 : c'.nreg 107 = 2 * n + 3 := by rw [g 107 (by omega), a7]
        have g101 : c'.nreg 101 = 1 := by rw [g 101 (by omega), a1]
        unfold wStep
        exec_block
        all_goals try (config_simp; (try simp only [r1, r2, r3, r4]); omega)
        rw [r1] at *
        rw [r2] at *
        rw [r3] at *
        rw [r4] at *
        refine ⟨by config_simp, by config_simp, by
          config_simp; rw [g 116 (by omega), a16, h80, g 101 (by omega), a1], by omega⟩
      refine ⟨k + 1, c'', k'', e, ⟨e.wb_right, (e.output_of_ou (by decide)).trans ho,
        fun r hr' => (e.nreg_of_wr (Stmt.wr_of_wmax (by omega))).trans (hr r hr'), by omega,
        by rw [h80', Function.iterate_succ_apply', hv],
        by rw [h82', Function.iterate_succ_apply', hv],
        fun a ha => by rw [hm', upd_other _ _ _ (by omega)]; exact hfr a ha,
        fun x hx => ?_⟩, by omega⟩
      rw [hm', upd_apply, hm x hx]
      by_cases hxv : x = v
      · rw [ite_eq_left (by omega), ite_eq_left ⟨k, by omega, by rw [hv, hxv]⟩]
      · rw [ite_eq_right (by omega)]
        congr 1; apply propext
        constructor
        · rintro ⟨k', hk', e'⟩; exact ⟨k', by omega, e'⟩
        · rintro ⟨k', hk', e'⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 hk' with h | rfl
          · exact ⟨k', h, e'⟩
          · exact absurd (e'.symm.trans hv) hxv) hI₁
  obtain ⟨hw₂, ho₂, hr₂, hk₂', h80, h82, hfr₂, hm₂⟩ := hI₂
  rw [hr₂ 100 (by omega), a0, h82] at hn₂
  obtain ⟨hun, hlu⟩ := hit k' hk₂'
  have hk'eq : k' = L u₀ := by omega
  subst hk'eq
  obtain ⟨c₃, k₃, e₃, hfin⟩ : ∃ c₃ k₃, Exec P W (block [.addN 69 116 80, .storeN 69 101]) c₂ c₃ k₃ ∧
      (c₃.output = c₂.output ∧ (∀ r, 100 ≤ r → c₃.nreg r = c₂.nreg r) ∧
        c₃.nmem = upd c₂.nmem (13 * m + 4 * n + f^[L u₀] u₀) 1 ∧ k₃ = 2) := by
    exec_block
    · rw [hr₂ 116 (by omega), a16, h80]; omega
    refine ⟨rfl, fun r hr => by
      config_simp; simp only [upd_apply]; split_ifs <;> omega,
      by config_simp; rw [hr₂ 116 (by omega), a16, h80, hr₂ 101 (by omega), a1], rfl⟩
  obtain ⟨ho₃, hr₃, hm₃, rfl⟩ := hfin
  refine ⟨c₃, 2 + (k₂ + 2), .seq e₁ (.seq e₂ e₃), by omega, ho₃.trans ho₂,
    fun r hr => (hr₃ r hr).trans (hr₂ r hr), fun a ha => by
      rw [hm₃, upd_other _ _ _ (by omega)]; exact hfr₂ a ha, fun x hx => ?_⟩
  rw [hm₃, upd_apply, hm₂ x hx]
  unfold AncN
  by_cases hxv : x = f^[L u₀] u₀
  · rw [ite_eq_left (by omega), ite_eq_left ⟨L u₀, le_rfl, hxv.symm⟩]
  · rw [ite_eq_right (by omega)]
    congr 1; apply propext
    constructor
    · rintro ⟨k', hk', e'⟩; exact ⟨k', by omega, e'⟩
    · rintro ⟨k', hk', e'⟩
      rcases Nat.lt_or_ge k' (L u₀) with h | h
      · exact ⟨k', h, e'⟩
      · exact absurd (by rw [show k' = L u₀ by omega] at e'; exact e'.symm) hxv

omit hPW in
/-- **The corners of the last triangle**, in mode `r127 ≥ 1`. -/
theorem xMark_exec (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (hδ : 0 < c.nreg 127 → c.nreg 128 < 3 * m) :
    ∃ c' k, Exec P W xMark c c' k ∧ k ≤ 16 ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, ¬ (13 * m + 4 * n ≤ a ∧ a < 13 * m + 5 * n) → c'.nmem a = c.nmem a) ∧
      (∀ x < n, c'.nmem (13 * m + 4 * n + x) =
        if 0 < c.nreg 127 ∧ (x = tl (c.nreg 128 / 3) ∨ x = tl (rv (c.nreg 128 / 3))) then 1
        else c.nmem (13 * m + 4 * n + x)) := by
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  unfold xMark
  by_cases h0 : 0 < c.nreg 127
  · refine spec_ifLtN_true (by rw [a0]; exact h0) ?_
    have hq : c.nreg 128 / 3 < m := by have := hδ h0; omega
    have hrv := hN.rv_lt _ hq
    have ht1 := hN.tl_lt _ hq
    have ht2 := hN.tl_lt _ hrv
    have r1 : P.data.getD (c.nreg 128 / 3 + c.nreg 128 / 3 + c.nreg 128 / 3 + (2 * n + 3)) 0 =
        tl (c.nreg 128 / 3) := by
      rw [show c.nreg 128 / 3 + c.nreg 128 / 3 + c.nreg 128 / 3 + (2 * n + 3) =
        2 * n + 3 + 3 * (c.nreg 128 / 3) by omega]
      exact hIn.tl_eq _ hq
    have r2 : P.data.getD (c.nreg 128 / 3 + c.nreg 128 / 3 + c.nreg 128 / 3 + (2 * n + 3) + 1) 0 =
        rv (c.nreg 128 / 3) := by
      rw [show c.nreg 128 / 3 + c.nreg 128 / 3 + c.nreg 128 / 3 + (2 * n + 3) + 1 =
        2 * n + 3 + 3 * (c.nreg 128 / 3) + 1 by omega]
      exact hIn.rv_eq _ hq
    have r3 : P.data.getD (rv (c.nreg 128 / 3) + rv (c.nreg 128 / 3) + rv (c.nreg 128 / 3) +
        (2 * n + 3)) 0 = tl (rv (c.nreg 128 / 3)) := by
      rw [show rv (c.nreg 128 / 3) + rv (c.nreg 128 / 3) + rv (c.nreg 128 / 3) + (2 * n + 3) =
        2 * n + 3 + 3 * rv (c.nreg 128 / 3) by omega]
      exact hIn.tl_eq _ hrv
    exec_block
    all_goals config_simp
    all_goals simp only [a1, a3, a7, a16]
    all_goals try simp only [r1, r2, r3]
    all_goals try omega
    refine ⟨by omega, fun r hr => by
      simp only [upd_apply]; split_ifs <;> omega, fun a ha => ?_,
      fun x hx => ?_⟩
    · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
    · simp only [upd_apply]
      split_ifs <;> first | rfl | omega
  · refine spec_ifLtN_false (by rw [a0]; exact h0) (spec_skip hc ?_)
    exact ⟨by omega, rfl, fun _ _ => rfl, fun _ _ => rfl, fun x _ =>
      (ite_eq_right_iff.2 fun h => absurd h.1 h0).symm⟩

open Classical in
omit hPW in
/-- **The separator marks.** The root paths of the dart `a = r129` of the stellar subdivision
and of its reversal `A a` (at address `a`), and in mode `r127 ≥ 1` the two corners of the input
graph of the triangle `r128`. -/
theorem rootPaths_exec (fr pr L : ℕ → ℕ) (hfr : ∀ q < m, 1 ≤ fr q ∧ fr q ≤ m)
    (hpar : ∀ v < n, v ≠ 0 → pr v < m ∧ tl (pr v) = v ∧ L (parN tl rv pr v) + 1 = L v)
    (hL0 : L 0 = 0) (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (hfrm : ∀ q < m, c.nmem (11 * m + q) = fr q)
    (hprm : ∀ v < n, c.nmem (13 * m + n + v) = pr v) (hLm : ∀ v < n, c.nmem (13 * m + v) = L v)
    (hLn : ∀ v < n, L v < n) (ha : c.nreg 129 < 3 * m) (hAa : c.nmem (c.nreg 129) < 3 * m)
    (hδ : 0 < c.nreg 127 → c.nreg 128 < 3 * m) :
    ∃ c' k, Exec P W rootPaths c c' k ∧ k ≤ 36 * n + 60 ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, ¬ (13 * m + 4 * n ≤ a ∧ a < 13 * m + 5 * n) → c'.nmem a = c.nmem a) ∧
      (∀ x < n, c'.nmem (13 * m + 4 * n + x) =
        if AncN tl rv pr L (uN tl rv fr (c.nreg 129)) x ∨
          AncN tl rv pr L (uN tl rv fr (c.nmem (c.nreg 129))) x ∨
          (0 < c.nreg 127 ∧ (x = tl (c.nreg 128 / 3) ∨ x = tl (rv (c.nreg 128 / 3)))) then 1
        else c.nmem (13 * m + 4 * n + x)) := by
  have hW' := hW; unfold memTop at hW'
  have hfrm' : ∀ (c' : Config), (∀ a, ¬ (13 * m + 4 * n ≤ a ∧ a < 13 * m + 5 * n) →
      c'.nmem a = c.nmem a) → (∀ q < m, c'.nmem (11 * m + q) = fr q) ∧
      (∀ v < n, c'.nmem (13 * m + n + v) = pr v) ∧ (∀ v < n, c'.nmem (13 * m + v) = L v) :=
    fun c' h => ⟨fun q hq => (h _ (by omega)).trans (hfrm q hq),
      fun v hv => (h _ (by omega)).trans (hprm v hv), fun v hv => (h _ (by omega)).trans (hLm v hv)⟩
  -- `r81 := a`
  have e₁ := Exec.copyN (P := P) hc 81 129
  generalize hc₁ : ({ c with nreg := upd c.nreg 81 (c.nreg 129) } : Config) = c₁ at e₁
  have hw₁ := e₁.wb_right
  have hr₁ : ∀ r, 100 ≤ r → c₁.nreg r = c.nreg r := fun r hr => by
    rw [← hc₁]; simp only [upd_apply]; split_ifs <;> omega
  have hm₁ : c₁.nmem = c.nmem := by rw [← hc₁]
  have h81 : c₁.nreg 81 = c.nreg 129 := by rw [← hc₁]; simp
  have hL₁ : Lay n m c₁ := hL.of fun r h1 _ => hr₁ r h1
  obtain ⟨c₂, k₂, e₂, hk₂, h80₂, hu₂, hm₂, ho₂, hr₂⟩ :=
    uOf_exec hN hIn hW fr hfr c₁ hw₁ hL₁ (by rw [hm₁]; exact hfrm) (by rw [h81]; exact ha)
  rw [h81] at h80₂ hu₂
  have hL₂ : Lay n m c₂ := hL₁.of fun r h1 _ => hr₂ r h1
  obtain ⟨c₃, k₃, e₃, hk₃, ho₃, hr₃, hf₃, hmk₃⟩ := walkUp_exec hN hIn hW pr L hpar hL0 c₂
    e₂.wb_right hL₂ (by rw [hm₂, hm₁]; exact hprm) (by rw [hm₂, hm₁]; exact hLm)
    (by rw [h80₂]; exact hu₂)
  rw [h80₂] at hk₃ hmk₃
  have hL₃ : Lay n m c₃ := hL₂.of fun r h1 _ => hr₃ r h1
  have hf₃' : ∀ a, ¬ (13 * m + 4 * n ≤ a ∧ a < 13 * m + 5 * n) → c₃.nmem a = c.nmem a :=
    fun a ha => by rw [hf₃ a ha, hm₂, hm₁]
  have g129 : c₃.nreg 129 = c.nreg 129 := by rw [hr₃ 129 (by omega), hr₂ 129 (by omega),
    hr₁ 129 (by omega)]
  -- `r81 := A a`
  have e₄ := Exec.loadN (P := P) e₃.wb_right 81 129
  generalize hc₄ : ({ c₃ with nreg := upd c₃.nreg 81 (c₃.nmem (c₃.nreg 129)) } : Config) = c₄ at e₄
  have hr₄ : ∀ r, 100 ≤ r → c₄.nreg r = c₃.nreg r := fun r hr => by
    rw [← hc₄]; simp only [upd_apply]; split_ifs <;> omega
  have hm₄ : c₄.nmem = c₃.nmem := by rw [← hc₄]
  have h81₄ : c₄.nreg 81 = c.nmem (c.nreg 129) := by
    rw [← hc₄]; simp only [upd_same, g129]; exact hf₃' _ (by omega)
  have hL₄ : Lay n m c₄ := hL₃.of fun r h1 _ => hr₄ r h1
  obtain ⟨⟨hfr₄, hpr₄, hLm₄⟩⟩ : _ ∧ True := ⟨hfrm' c₄ (fun a ha => by rw [hm₄]; exact hf₃' a ha),
    trivial⟩
  obtain ⟨c₅, k₅, e₅, hk₅, h80₅, hu₅, hm₅, ho₅, hr₅⟩ :=
    uOf_exec hN hIn hW fr hfr c₄ e₄.wb_right hL₄ hfr₄ (by rw [h81₄]; exact hAa)
  rw [h81₄] at h80₅ hu₅
  have hL₅ : Lay n m c₅ := hL₄.of fun r h1 _ => hr₅ r h1
  obtain ⟨c₆, k₆, e₆, hk₆, ho₆, hr₆, hf₆, hmk₆⟩ := walkUp_exec hN hIn hW pr L hpar hL0 c₅
    e₅.wb_right hL₅ (by rw [hm₅]; exact hpr₄) (by rw [hm₅]; exact hLm₄)
    (by rw [h80₅]; exact hu₅)
  rw [h80₅] at hk₆ hmk₆
  have hL₆ : Lay n m c₆ := hL₅.of fun r h1 _ => hr₆ r h1
  have hR6 : ∀ r, 100 ≤ r → c₆.nreg r = c.nreg r := fun r hr => by
    rw [hr₆ r hr, hr₅ r hr, hr₄ r hr, hr₃ r hr, hr₂ r hr, hr₁ r hr]
  obtain ⟨c₇, k₇, e₇, hk₇, ho₇, hr₇, hf₇, hmk₇⟩ := xMark_exec hN hIn hW c₆ e₆.wb_right hL₆
    (by rw [hR6 127 (by omega), hR6 128 (by omega)]; exact hδ)
  rw [hR6 127 (by omega), hR6 128 (by omega)] at hmk₇
  have hLu₂ := hLn _ hu₂
  have hLu₅ := hLn _ hu₅
  refine ⟨c₇, 1 + (k₂ + (k₃ + (1 + (k₅ + (k₆ + k₇))))),
    .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ e₇))))), ?_, ?_,
    fun r hr => (hr₇ r hr).trans (hR6 r hr), fun a ha => ?_, fun x hx => ?_⟩
  · have : 18 * L (uN tl rv fr (c.nreg 129)) ≤ 18 * n := by omega
    have : 18 * L (uN tl rv fr (c.nmem (c.nreg 129))) ≤ 18 * n := by omega
    omega
  · rw [ho₇, ho₆, ho₅, e₄.output_of_ou (by decide), ho₃, ho₂, e₁.output_of_ou (by decide)]
  · rw [hf₇ a ha, hf₆ a ha, hm₅, hm₄, hf₃' a ha]
  · rw [hmk₇ x hx, hmk₆ x hx, hm₅, hm₄, hmk₃ x hx, hm₂, hm₁]
    by_cases h1 : AncN tl rv pr L (uN tl rv fr (c.nreg 129)) x
    · simp only [h1, true_or, ↓reduceIte, ite_self]
    by_cases h2 : AncN tl rv pr L (uN tl rv fr (c.nmem (c.nreg 129))) x
    · simp only [h1, h2, true_or, or_true, ↓reduceIte, ite_self]
    simp only [h1, h2, false_or, ↓reduceIte]

end proofs

end SepProg

end PlanarSeparator
