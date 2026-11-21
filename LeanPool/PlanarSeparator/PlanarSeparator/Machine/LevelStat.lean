/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.BFS

/-!
# The separator program: the weights of the levels, the median level, `⌊√n⌋`, the thin levels

Given the levels `L v` (at `13 m + v`, all `< n`) and the weights `w v` (in the input):

* `lstat`: the weight `LW l` and the number `LC l` of the vertices of each level `l`, at
  `13 m + 5 n + l` and `13 m + 7 n + 2 + l`, and the total weight in `r122`;
* `median`: the smallest level `l₁` (in `r123`) such that the levels up to `l₁` weigh at least
  half: then the levels below `l₁` weigh at most half, and so do those above;
* `sqrtL`: `t = ⌊√n⌋` in `r124`, by counting;
* `findJ`, `findJ'`: the first `j`, `j'` (in `r125`, `r126`) such that the level `l₁ - j`
  (resp. `l₁ + 1 + j'`) has at most `n / (t + 1)` vertices; they are at most `t` since the
  `t + 1` candidate levels are disjoint.
-/

@[expose] public section

namespace PlanarSeparator

namespace SepProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The programs -/

/-- One vertex `r74 = v`: add `w v` to the total and to its level, count it. -/
def lsBody : Stmt := block [.addN 69 112 74, .loadN 75 69, .addN 70 106 74, .readIn 76 70,
  .addN 122 122 76, .addN 69 117 75, .loadN 77 69, .addN 77 77 76, .storeN 69 77,
  .addN 69 118 75, .loadN 77 69, .addN 77 77 101, .storeN 69 77, .addN 74 74 101]

/-- **The weights and sizes of the levels.** -/
def lstat : Stmt := .seq (block [.copyN 74 100, .copyN 122 100]) (.whileLtN 74 104 lsBody)

/-- `r80 := 2 (P + LW l)` for `r78 = l`, `r79 = P`. -/
def mTest : List Instr := [.addN 69 117 78, .loadN 80 69, .addN 80 80 79, .addN 80 80 80]

/-- **The median level** `r123`. -/
def median : Stmt :=
  .seq (block ([.copyN 78 100, .copyN 79 100] ++ mTest))
    (.seq (.whileLtN 80 122 (block ([.addN 69 117 78, .loadN 81 69, .addN 79 79 81,
      .addN 78 78 101] ++ mTest))) (.instr (.copyN 123 78)))

/-- **`⌊√n⌋`** in `r124`. -/
def sqrtL : Stmt :=
  .seq (block [.copyN 124 100, .copyN 81 101, .addN 82 104 101])
    (.whileLtN 81 82 (block [.addN 124 124 101, .addN 83 124 101, .mulN 81 83 83]))

/-- `r84 :=` the size of the level `l₁ - j` (`0` if `j > l₁`), `j = r125`. -/
def cntJ : Stmt := .ifLtN 123 125 (.instr (.copyN 84 100))
  (block [.subN 86 123 125, .addN 69 118 86, .loadN 84 69])

/-- **The thin level below**: `j` in `r125`. -/
def findJ : Stmt :=
  .seq (block [.addN 83 124 101, .divN 85 104 83, .copyN 125 100])
    (.seq cntJ (.whileLtN 85 84 (.seq (.instr (.addN 125 125 101)) cntJ)))

/-- `r84 :=` the size of the level `l₁ + 1 + j'`, `j' = r126`. -/
def cntJ' : Stmt := block [.addN 86 123 101, .addN 86 86 126, .addN 69 118 86, .loadN 84 69]

/-- **The thin level above**: `j'` in `r126`. -/
def findJ' : Stmt :=
  .seq (block [.copyN 126 100])
    (.seq cntJ' (.whileLtN 85 84 (.seq (.instr (.addN 126 126 101)) cntJ')))

/-! ### Level statistics -/

/-- The weight of level `l` among the first `i` vertices. -/
def lwF (L w : ℕ → ℕ) (i l : ℕ) : ℕ := ∑ v ∈ (range i).filter (fun v => L v = l), w v
/-- The number of vertices of level `l` among the first `i`. -/
def lcF (L : ℕ → ℕ) (i l : ℕ) : ℕ := #((range i).filter (fun v => L v = l))

section proofs

variable {n m : ℕ} {ofs w tl rv ro : ℕ → ℕ} {W : ℕ} {P : Input}
  (hN : NWf n m ofs tl rv ro) (hIn : InHolds P n m ofs w tl rv ro)
  (hW : memTop n m + 3 * ∑ v ∈ range n, w v + 2 * n + 3 * m + 10 ≤ W)
  (hPW : ∀ j, P.data.getD j 0 ≤ W)
include hN hIn hW hPW

omit hN hPW in
/-- **The level statistics.** -/
theorem lstat_exec (L : ℕ → ℕ) (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (hLm : ∀ v < n, c.nmem (13 * m + v) = L v) (hLn : ∀ v < n, L v < n)
    (hz : ∀ a, 13 * m + 5 * n ≤ a → a < 13 * m + 9 * n + 4 → c.nmem a = 0) :
    ∃ c' k, Exec P W lstat c c' k ∧ k ≤ 16 * n + 4 ∧ Lay n m c' ∧ c'.output = c.output ∧
      (∀ a, (a < 13 * m + 5 * n ∨ 13 * m + 9 * n + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg 122 = ∑ v ∈ range n, w v ∧
      (∀ l < 2 * n + 2, c'.nmem (13 * m + 5 * n + l) = lwF L w n l) ∧
      (∀ l < 2 * n + 2, c'.nmem (13 * m + 7 * n + 2 + l) = lcF L n l) := by
  have hW' := hW; unfold memTop at hW'
  obtain ⟨c₁, k₁, e₁, hI₁⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 74 100, .copyN 122 100]) c c₁ k₁ ∧
      (WordsBounded W c₁ ∧ Lay n m c₁ ∧ c₁.output = c.output ∧ c₁.nmem = c.nmem ∧
      c₁.nreg 74 = 0 ∧ c₁.nreg 122 = 0 ∧ k₁ = 2) := by
    exec_block
    exact ⟨‹_›, hL.of fun r h1 _ => by
      config_simp; simp only [upd_apply]; split_ifs <;> omega,
      rfl, rfl, by config_simp; exact hL.r100, by config_simp; exact hL.r100, rfl⟩
  obtain ⟨hw₁, hL₁, ho₁, hm₁, h74, h122, rfl⟩ := hI₁
  have hsum_le : ∀ i ≤ n, ∑ v ∈ range i, w v ≤ ∑ v ∈ range n, w v := fun i hi =>
    sum_le_sum_of_subset (range_subset_range.2 hi)
  have hlw_le : ∀ i ≤ n, ∀ l, lwF L w i l ≤ ∑ v ∈ range n, w v := fun i hi l =>
    (sum_le_sum_of_subset (filter_subset _ _)).trans (hsum_le i hi)
  have hlc_le : ∀ i, ∀ l, lcF L i l ≤ i := fun i l => (card_le_card (filter_subset _ _)).trans
    (by simp)
  obtain ⟨c', k', e', ⟨hw', hL', ho', h74', hfr', h122', hlw', hlc'⟩, hk'⟩ :=
    Exec.forN (P := P) (W := W) (ri := 74) (rN := 104) (N := n) (lo := 0) (B := 14) (body := lsBody)
    (fun i c' => WordsBounded W c' ∧ Lay n m c' ∧ c'.output = c.output ∧ c'.nreg 74 = i ∧
      (∀ a, (a < 13 * m + 5 * n ∨ 13 * m + 9 * n + 4 ≤ a) → c'.nmem a = c.nmem a) ∧
      c'.nreg 122 = ∑ v ∈ range i, w v ∧
      (∀ l < 2 * n + 2, c'.nmem (13 * m + 5 * n + l) = lwF L w i l) ∧
      (∀ l < 2 * n + 2, c'.nmem (13 * m + 7 * n + 2 + l) = lcF L i l))
    (fun i c' h => ⟨h.1, h.2.2.2.1, h.2.1.r104⟩)
    (fun i c' h hi => by
      obtain ⟨hc', hL', ho', g74, gfr, g122, glw, glc⟩ := h
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
        a19, a20, a21⟩ := hL'
      have hLi := hLn i hi
      have r1 : c'.nmem (c'.nreg 112 + c'.nreg 74) = L i := by
        rw [a12, g74, gfr _ (Or.inl (by omega))]; exact hLm i hi
      have r2 : P.data.getD (c'.nreg 106 + c'.nreg 74) 0 = w i := by
        rw [a6, g74]; exact hIn.w_eq i hi
      have r3 : c'.nmem (c'.nreg 117 + L i) = lwF L w i (L i) := by
        rw [a17]; exact glw _ (by omega)
      have r4 : ∀ x, upd c'.nmem (c'.nreg 117 + L i) x (c'.nreg 118 + L i) = lcF L i (L i) :=
        fun _ => by rw [upd_other _ _ _ (by rw [a17, a18]; omega), a18]; exact glc _ (by omega)
      have hlwo : ∀ l, l ≠ L i → lwF L w (i + 1) l = lwF L w i l := fun l hl => by
        simp [lwF, range_add_one, filter_insert, Ne.symm hl]
      have hlco : ∀ l, l ≠ L i → lcF L (i + 1) l = lcF L i l := fun l hl => by
        simp [lcF, range_add_one, filter_insert, Ne.symm hl]
      have hlwi := hlw_le (i + 1) hi (L i)
      have hlwi' : lwF L w (i + 1) (L i) = lwF L w i (L i) + w i := by
        simp [lwF, range_add_one, filter_insert, sum_insert, add_comm]
      have hs := hsum_le (i + 1) hi
      rw [sum_range_succ] at hs
      have hlci := hlc_le (i + 1) (L i)
      have hlci' : lcF L (i + 1) (L i) = lcF L i (L i) + 1 := by
        simp [lcF, range_add_one, filter_insert]
      unfold lsBody
      exec_block
      all_goals try (config_simp; (try simp only [r1, r2, r3, r4]); omega)
      refine ⟨⟨‹_›, Lay.of ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15,
        a16, a17, a18, a19, a20, a21⟩ fun r h1 h2 => by
          config_simp; simp only [upd_apply]; split_ifs <;> omega,
        by config_simp; exact ho', by config_simp; omega, fun a ha => ?_, ?_, fun l hl => ?_,
        fun l hl => ?_⟩, by omega⟩
      · config_simp; simp only [r1, upd_apply, a17, a18]
        split_ifs <;> first | omega | exact gfr a ha
      · config_simp; rw [r2, g122, sum_range_succ]
      · config_simp
        simp only [r1, r2, r3, r4]
        simp only [upd_apply, a17, a18]
        split_ifs with h1 h2
        · omega
        · rw [show l = L i by omega, hlwi']
        · rw [hlwo l (by omega)]; exact glw l hl
      · config_simp
        simp only [r1, r4]
        simp only [upd_apply, a17, a18, a1]
        split_ifs with h1 h2
        · rw [show l = L i by omega, hlci']
        · omega
        · rw [hlco l (by omega)]; exact glc l hl)
    (Nat.zero_le n) ⟨hw₁, hL₁, ho₁, h74, fun a _ => by rw [hm₁], by rw [h122]; simp,
      fun l hl => by rw [hm₁, hz _ (by omega) (by omega)]; simp [lwF],
      fun l hl => by rw [hm₁, hz _ (by omega) (by omega)]; simp [lcF]⟩
  exact ⟨c', 2 + k', .seq e₁ e', by omega, hL', ho', hfr', h122', hlw', hlc'⟩

omit hN hIn hPW in
/-- **The median level.** -/
theorem median_exec (hn : 1 ≤ n) (lw : ℕ → ℕ) (Wt : ℕ) (c : Config)
    (hc : WordsBounded W c) (hL : Lay n m c)
    (hlw : ∀ l < 2 * n + 2, c.nmem (13 * m + 5 * n + l) = lw l) (h122 : c.nreg 122 = Wt)
    (hWt : Wt ≤ ∑ v ∈ range n, w v) (htot : ∑ l ∈ range n, lw l = Wt)
    (hlwb : ∀ l < 2 * n + 2, lw l ≤ Wt) :
    ∃ c' k, Exec P W median c c' k ∧ k ≤ 10 * n + 9 ∧ c'.nmem = c.nmem ∧
      c'.output = c.output ∧ (∀ r, 100 ≤ r → r ≠ 123 → c'.nreg r = c.nreg r) ∧
      c'.nreg 123 ≤ n ∧ 2 * ∑ l ∈ range (c'.nreg 123), lw l ≤ Wt ∧
      Wt ≤ 2 * ∑ l ∈ range (c'.nreg 123 + 1), lw l := by
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  have hlw_le : ∀ l ≤ n, ∑ i ∈ range l, lw i ≤ Wt := fun l hl => by
    rw [← htot]; exact sum_le_sum_of_subset (range_subset_range.2 hl)
  have hlwl : ∀ l < n, lw l ≤ Wt := fun l hl => by
    have := hlw_le (l + 1) hl; rw [sum_range_succ] at this; omega
  have hlwn : lw n = 0 ∨ True := Or.inr trivial
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ c'.nmem = c.nmem ∧ c'.output = c.output ∧
    (∀ r, 100 ≤ r → r ≠ 123 → c'.nreg r = c.nreg r) ∧ c'.nreg 78 ≤ n ∧
    c'.nreg 79 = ∑ i ∈ range (c'.nreg 78), lw i ∧ 2 * c'.nreg 79 ≤ Wt ∧
    c'.nreg 80 = 2 * (c'.nreg 79 + lw (c'.nreg 78))
  have hrd : ∀ c' : Config, I c' → ∀ x, x < 2 * n + 2 → c'.nmem (c'.nreg 117 + x) = lw x := by
    intro c' h x hx; rw [h.2.1, h.2.2.2.1 117 (by omega) (by omega), a17]; exact hlw x hx
  -- start
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W
      (block ([.copyN 78 100, .copyN 79 100] ++ mTest))
      c c₁ k₁ ∧ I c₁ ∧ k₁ = 6 := by
    have r1 : c.nmem (c.nreg 117 + c.nreg 100) = lw 0 := by rw [a17, a0]; exact hlw 0 (by omega)
    have h0 := hlwl 0 hn
    simp only [mTest, List.cons_append, List.nil_append]
    exec_block
    all_goals try (config_simp; (try simp only [r1]); omega)
    refine ⟨by dsimp only [I]; exact ⟨‹_›, rfl, rfl,
      fun r h1 h2 => by
        simp only [upd_apply]; split_ifs <;> omega,
      by config_simp; omega, by config_simp; simp [a0], by config_simp; omega,
      by config_simp; rw [r1, a0]; omega⟩, rfl⟩
  obtain ⟨c₂, k₂, e₂, hI₂, hn₂, hk₂⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 80)
    (b := 122) (body := block ([.addN 69 117 78, .loadN 81 69, .addN 79 79 81, .addN 78 78 101] ++
      mTest)) I (fun c' => 10 * (n - c'.nreg 78)) (fun c' h => h.1)
    (fun c' h hlt => by
      obtain ⟨hw, hm, ho, hr, h78, h79, h79', h80⟩ := h
      have g122 : c'.nreg 122 = Wt := by rw [hr 122 (by omega) (by omega), h122]
      have g101 : c'.nreg 101 = 1 := by rw [hr 101 (by omega) (by omega), a1]
      have hl : c'.nreg 78 < n := by
        by_contra hc
        have : c'.nreg 78 = n := by omega
        rw [this, htot] at h79
        omega
      have r1 : c'.nmem (c'.nreg 117 + c'.nreg 78) = lw (c'.nreg 78) :=
        hrd c' ⟨hw, hm, ho, hr, h78, h79, h79', h80⟩ _ (by omega)
      have r2 : c'.nmem (c'.nreg 117 + (c'.nreg 78 + c'.nreg 101)) = lw (c'.nreg 78 + 1) := by
        rw [g101]; exact hrd c' ⟨hw, hm, ho, hr, h78, h79, h79', h80⟩ _ (by omega)
      have b1 := hlwb (c'.nreg 78) (by omega)
      have b2 := hlwb (c'.nreg 78 + 1) (by omega)
      have hs := hlw_le (c'.nreg 78 + 1) hl
      rw [sum_range_succ] at hs
      have hr117 : c'.nreg 117 = 13 * m + 5 * n := by rw [hr 117 (by omega) (by omega), a17]
      simp only [mTest, List.cons_append, List.nil_append]
      exec_block
      all_goals try (config_simp; (try simp only [r1, r2]); omega)
      refine ⟨by dsimp only [I]; exact ⟨‹_›, by exact hm, by exact ho,
        fun r h1 h2 => by
          simp only [upd_apply]; split_ifs <;> first | omega | exact hr r h1 h2,
        by config_simp; omega, by config_simp; rw [r1, h79, g101, sum_range_succ],
        by config_simp; rw [r1]; omega, by config_simp; rw [r1, r2, g101]; omega⟩, ?_⟩
      config_simp; rw [g101]; omega) hI₁
  obtain ⟨hw₂, hm₂, ho₂, hr₂, h78, h79, h79', h80⟩ := hI₂
  have g122 : c₂.nreg 122 = Wt := by rw [hr₂ 122 (by omega) (by omega), h122]
  have e₃ := Exec.copyN (P := P) hw₂ 123 78
  refine ⟨{ c₂ with nreg := upd c₂.nreg 123 (c₂.nreg 78) }, 6 + (k₂ + 1), .seq e₁ (.seq e₂ e₃),
    ?_, hm₂, ho₂, fun r h1 h2 => ?_, ?_, ?_, ?_⟩
  · have := hI₁.2.2.2.2.1; omega
  · change upd c₂.nreg 123 (c₂.nreg 78) r = c.nreg r
    rw [upd_other _ _ _ h2]; exact hr₂ r h1 h2
  · change upd c₂.nreg 123 (c₂.nreg 78) 123 ≤ n
    rw [upd_same]; exact h78
  · change 2 * ∑ l ∈ range (upd c₂.nreg 123 (c₂.nreg 78) 123), lw l ≤ Wt
    rw [upd_same, ← h79]; exact h79'
  · change Wt ≤ 2 * ∑ l ∈ range (upd c₂.nreg 123 (c₂.nreg 78) 123 + 1), lw l
    rw [upd_same, sum_range_succ, ← h79]; omega

omit hN hIn hPW in
/-- **`⌊√n⌋`.** -/
theorem sqrtL_exec (c : Config) (hc : WordsBounded W c) (hL : Lay n m c) :
    ∃ c' k, Exec P W sqrtL c c' k ∧ k ≤ 5 * n + 5 ∧ c'.nmem = c.nmem ∧
      c'.output = c.output ∧ (∀ r, 100 ≤ r → r ≠ 124 → c'.nreg r = c.nreg r) ∧
      c'.nreg 124 = Nat.sqrt n := by
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  let I : Config → Prop := fun c' => WordsBounded W c' ∧ c'.nmem = c.nmem ∧ c'.output = c.output ∧
    (∀ r, 100 ≤ r → r ≠ 124 → c'.nreg r = c.nreg r) ∧ c'.nreg 124 * c'.nreg 124 ≤ n ∧
    c'.nreg 81 = (c'.nreg 124 + 1) * (c'.nreg 124 + 1) ∧ c'.nreg 82 = n + 1
  obtain ⟨c₁, k₁, e₁, hI₁, rfl⟩ : ∃ c₁ k₁, Exec P W (block [.copyN 124 100, .copyN 81 101,
      .addN 82 104 101]) c c₁ k₁ ∧ I c₁ ∧ k₁ = 3 := by
    exec_block
    · config_simp; omega
    refine ⟨by dsimp only [I]; exact ⟨‹_›, rfl, rfl,
      fun r h1 h2 => by simp only [upd_apply]; split_ifs <;> omega,
      by config_simp; rw [a0]; omega, by config_simp; rw [a0, a1], by config_simp; omega⟩, rfl⟩
  obtain ⟨c₂, k₂, e₂, ⟨hw₂, hm₂, ho₂, hr₂, h₂, h81, h82⟩, hn₂, hk₂⟩ := Exec.whileLtN_potential
    (P := P) (W := W) (a := 81) (b := 82)
    (body := block [.addN 124 124 101, .addN 83 124 101, .mulN 81 83 83]) I
    (fun c' => 5 * (n - c'.nreg 124)) (fun c' h => h.1)
    (fun c' h hlt => by
      obtain ⟨hw, hm, ho, hr, h1, h81, h82⟩ := h
      have g101 : c'.nreg 101 = 1 := by rw [hr 101 (by omega) (by omega), a1]
      generalize ht : c'.nreg 124 = t at h1 h81
      have hsq : (t + 1) * (t + 1) ≤ n := by omega
      have hsq' : (t + 1 + 1) * (t + 1 + 1) = (t + 1) * (t + 1) + 2 * (t + 1) + 1 := by
        simp only [Nat.add_mul, Nat.mul_add]; omega
      have htn : t + 1 ≤ n := le_trans (Nat.le_mul_self _) hsq
      exec_block
      · omega
      · config_simp; omega
      · config_simp; rw [g101, ht]; omega
      refine ⟨by dsimp only [I]; exact ⟨‹_›, hm, ho,
        fun r h1 h2 => by
          simp only [upd_apply]; split_ifs <;> first | omega | exact hr r h1 h2,
        by config_simp; rw [g101, ht]; exact hsq, by config_simp; rw [g101, ht],
        by config_simp; exact h82⟩, ?_⟩
      config_simp; rw [g101, ht]; omega) hI₁
  refine ⟨c₂, 3 + k₂, .seq e₁ e₂, ?_, hm₂, ho₂, hr₂, ?_⟩
  · have := hI₁.2.2.2.2.1; omega
  · exact Nat.eq_sqrt.2 ⟨h₂, by rw [← h81]; omega⟩

end proofs

section search

variable {W : ℕ} {P : Input}

/-- The search for a thin level: count the candidate `rj`, and advance while it has more than
`r85` vertices. -/
def thinLoop (cnt : Stmt) (rj : ℕ) : Stmt :=
  .seq cnt (.whileLtN 85 84 (.seq (.instr (.addN rj rj 101)) cnt))

/-- **The search for a thin level.** -/
theorem thinLoop_exec {cnt : Stmt} {rj : ℕ} (f : ℕ → ℕ) (q t : ℕ)
    (Inv : Config → Prop) (hInv : ∀ c, Inv c → WordsBounded W c ∧ c.nreg 85 = q ∧ c.nreg 101 = 1)
    (hInc : ∀ c, Inv c → c.nreg rj < t →
      Inv { c with nreg := upd c.nreg rj (c.nreg rj + c.nreg 101) })
    (hcnt : ∀ c, Inv c → c.nreg rj ≤ t → ∃ c' k, Exec P W cnt c c' k ∧ Inv c' ∧
      c'.nreg 84 = f (c.nreg rj) ∧ c'.nreg rj = c.nreg rj ∧ k ≤ 5)
    (hex : ∃ j, j ≤ t ∧ f j ≤ q) (htW : t + 1 ≤ W) (c : Config) (hc : Inv c) (h0 : c.nreg rj = 0) :
    ∃ c' k, Exec P W (thinLoop cnt rj) c c' k ∧ k ≤ 8 * t + 7 ∧ Inv c' ∧ c'.nreg rj ≤ t ∧
      f (c'.nreg rj) ≤ q := by
  classical
  obtain ⟨c₁, k₁, e₁, hI₁, h84, hj₁, hk₁⟩ := hcnt c hc (by omega)
  have hjm := Nat.find_spec hex
  have hjmin : ∀ j < Nat.find hex, ¬ (j ≤ t ∧ f j ≤ q) := fun j hj => Nat.find_min hex hj
  obtain ⟨c', k', e', ⟨hI', hj', h84'⟩, hn', hk'⟩ := Exec.whileLtN_potential (P := P) (W := W)
    (a := 85) (b := 84) (body := .seq (.instr (.addN rj rj 101)) cnt)
    (fun c => Inv c ∧ c.nreg rj ≤ Nat.find hex ∧ c.nreg 84 = f (c.nreg rj))
    (fun c => 8 * (Nat.find hex - c.nreg rj)) (fun c h => (hInv c h.1).1)
    (fun c h hlt => by
      obtain ⟨hI, hj, h84⟩ := h
      obtain ⟨hw, h85, h101⟩ := hInv c hI
      have hlt' : c.nreg rj < Nat.find hex := by
        rcases Nat.lt_or_ge (c.nreg rj) (Nat.find hex) with h | h
        · exact h
        · exfalso
          have e : c.nreg rj = Nat.find hex := by omega
          rw [h85, h84, e] at hlt
          exact absurd hjm.2 (by omega)
      have hI' := hInc c hI (by omega)
      obtain ⟨c₂, k₂, e₂, hI₂, h84₂, hj₂, hk₂⟩ := hcnt _ hI' (by simp; omega)
      have e₁ := Exec.addN (P := P) hw rj rj 101 (by rw [h101]; omega)
      refine ⟨c₂, 1 + k₂, .seq e₁ e₂, ⟨hI₂, ?_, ?_⟩, ?_⟩
      all_goals simp only [hj₂, h84₂, upd_same, h101]
      all_goals omega) ⟨hI₁, by omega, by rw [h84, hj₁]⟩
  obtain ⟨-, h85, -⟩ := hInv c' hI'
  refine ⟨c', k₁ + k', .seq e₁ e', ?_, hI', by omega, by rw [← h84']; omega⟩
  rw [hj₁, h0] at hk'
  omega

end search

section thin

variable {n m : ℕ} {ofs w tl rv ro : ℕ → ℕ} {W : ℕ} {P : Input}
  (hN : NWf n m ofs tl rv ro) (hIn : InHolds P n m ofs w tl rv ro)
  (hW : memTop n m + 3 * ∑ v ∈ range n, w v + 2 * n + 3 * m + 10 ≤ W)
  (hPW : ∀ j, P.data.getD j 0 ≤ W)
include hN hIn hW hPW

omit hN hIn hPW in
/-- **The thin level below the median.** -/
theorem findJ_exec (lc : ℕ → ℕ) (l₁ : ℕ) (hl₁ : l₁ ≤ n) (c : Config) (hc : WordsBounded W c)
    (hL : Lay n m c) (h123 : c.nreg 123 = l₁) (h124 : c.nreg 124 = Nat.sqrt n)
    (hlc : ∀ l < 2 * n + 2, c.nmem (13 * m + 7 * n + 2 + l) = lc l)
    (hex : ∃ j, j ≤ Nat.sqrt n ∧ (if l₁ < j then 0 else lc (l₁ - j)) ≤ n / (Nat.sqrt n + 1)) :
    ∃ c' k, Exec P W findJ c c' k ∧ k ≤ 8 * n + 10 ∧ c'.nmem = c.nmem ∧
      c'.output = c.output ∧ (∀ r, 100 ≤ r → r ≠ 125 → c'.nreg r = c.nreg r) ∧
      c'.nreg 125 ≤ Nat.sqrt n ∧ c'.nreg 85 = n / (Nat.sqrt n + 1) ∧
      (if l₁ < c'.nreg 125 then 0 else lc (l₁ - c'.nreg 125)) ≤ n / (Nat.sqrt n + 1) := by
  have hW' := hW; unfold memTop at hW'
  have hsq : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  have hq : n / (Nat.sqrt n + 1) ≤ n := Nat.div_le_self _ _
  obtain ⟨c₁, k₁, e₁, hw₁, hm₁, ho₁, hr₁, h85, h125, rfl⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 83 124 101, .divN 85 104 83, .copyN 125 100]) c c₁ k₁ ∧ WordsBounded W c₁ ∧
      c₁.nmem = c.nmem ∧ c₁.output = c.output ∧ (∀ r, 100 ≤ r → r ≠ 125 → c₁.nreg r = c.nreg r) ∧
      c₁.nreg 85 = n / (Nat.sqrt n + 1) ∧ c₁.nreg 125 = 0 ∧ k₁ = 3 := by
    exec_block
    · omega
    exact ⟨‹_›, rfl, rfl, fun r h1 h2 => by
      config_simp; simp only [upd_apply]; split_ifs <;> omega,
      by config_simp; rw [a4, h124, a1], by config_simp; exact a0, rfl⟩
  let Inv : Config → Prop := fun c' => WordsBounded W c' ∧ c'.nmem = c.nmem ∧
    c'.output = c.output ∧ (∀ r, 100 ≤ r → r ≠ 125 → c'.nreg r = c.nreg r) ∧
    c'.nreg 85 = n / (Nat.sqrt n + 1)
  obtain ⟨c', k', e', hk', ⟨hw', hm', ho', hr', h85'⟩, hj', hf'⟩ :=
    thinLoop_exec (P := P) (W := W) (cnt := cntJ) (rj := 125)
    (fun j => if l₁ < j then 0 else lc (l₁ - j)) (n / (Nat.sqrt n + 1)) (Nat.sqrt n) Inv
    (fun c' h => ⟨h.1, h.2.2.2.2, by rw [h.2.2.2.1 101 (by omega) (by omega), a1]⟩)
    (fun c' h hlt => ⟨by
        have := h.1
        refine ⟨fun r => ?_, fun a => ?_⟩
        · simp only [upd_apply]; split_ifs
          · rw [h.2.2.2.1 101 (by omega) (by omega), a1]; omega
          · exact this.1 r
        · exact this.2 a, h.2.1, h.2.2.1,
      fun r h1 h2 => by simp only [upd_apply, h2, ↓reduceIte]; exact h.2.2.2.1 r h1 h2,
      by simp only [upd_apply]; exact h.2.2.2.2⟩)
    (fun c' h hj => by
      obtain ⟨hw, hm, ho, hr, h85⟩ := h
      have g123 : c'.nreg 123 = l₁ := by rw [hr 123 (by omega) (by omega), h123]
      have g118 : c'.nreg 118 = 13 * m + 7 * n + 2 := by rw [hr 118 (by omega) (by omega), a18]
      unfold cntJ
      by_cases hlt : l₁ < c'.nreg 125
      · refine spec_ifLtN_true (by rw [g123]; exact hlt) ?_
        refine spec_instr (Exec.copyN hw 84 100) fun hw' => ?_
        refine ⟨⟨hw', hm, ho,
          fun r h1 h2 => by
            config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r h1 h2,
          by config_simp; exact h85⟩, ?_, by config_simp, by omega⟩
        config_simp; rw [hr 100 (by omega) (by omega), a0, ite_eq_left hlt]
      · refine spec_ifLtN_false (by rw [g123]; exact hlt) ?_
        have r1 : c'.nmem (c'.nreg 118 + (c'.nreg 123 - c'.nreg 125)) = lc (l₁ - c'.nreg 125) := by
          rw [hm, g118, g123]; exact hlc _ (by omega)
        exec_block
        · config_simp; rw [g118]; omega
        refine ⟨⟨‹_›, by config_simp; exact hm, by config_simp; exact ho,
          fun r h1 h2 => by
            config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r h1 h2,
          by config_simp; exact h85⟩, ?_, by config_simp, by omega⟩
        config_simp; rw [r1, ite_eq_right hlt])
    hex (by omega) c₁ ⟨hw₁, hm₁, ho₁, hr₁, h85⟩ h125
  refine ⟨c', 3 + k', .seq e₁ e', by omega, hm', ho', fun r h1 h2 => hr' r h1 h2, hj', h85', hf'⟩

omit hN hIn hPW in
/-- **The thin level above the median.** -/
theorem findJ'_exec (lc : ℕ → ℕ) (l₁ : ℕ) (hl₁ : l₁ ≤ n) (c : Config) (hc : WordsBounded W c)
    (hL : Lay n m c) (h123 : c.nreg 123 = l₁) (h85 : c.nreg 85 = n / (Nat.sqrt n + 1))
    (hlc : ∀ l < 2 * n + 2, c.nmem (13 * m + 7 * n + 2 + l) = lc l)
    (hex : ∃ j, j ≤ Nat.sqrt n ∧ lc (l₁ + 1 + j) ≤ n / (Nat.sqrt n + 1)) :
    ∃ c' k, Exec P W findJ' c c' k ∧ k ≤ 8 * n + 8 ∧ c'.nmem = c.nmem ∧
      c'.output = c.output ∧ (∀ r, 100 ≤ r → r ≠ 126 → c'.nreg r = c.nreg r) ∧
      c'.nreg 126 ≤ Nat.sqrt n ∧ lc (l₁ + 1 + c'.nreg 126) ≤ n / (Nat.sqrt n + 1) := by
  have hW' := hW; unfold memTop at hW'
  have hsq : Nat.sqrt n ≤ n := Nat.sqrt_le_self n
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  have e₁ := Exec.copyN (P := P) hc 126 100
  let Inv : Config → Prop := fun c' => WordsBounded W c' ∧ c'.nmem = c.nmem ∧
    c'.output = c.output ∧ (∀ r, 100 ≤ r → r ≠ 126 → c'.nreg r = c.nreg r) ∧
    c'.nreg 85 = n / (Nat.sqrt n + 1)
  obtain ⟨c', k', e', hk', ⟨hw', hm', ho', hr', h85'⟩, hj', hf'⟩ :=
    thinLoop_exec (P := P) (W := W) (cnt := cntJ') (rj := 126)
    (fun j => lc (l₁ + 1 + j)) (n / (Nat.sqrt n + 1)) (Nat.sqrt n) Inv
    (fun c' h => ⟨h.1, h.2.2.2.2, by rw [h.2.2.2.1 101 (by omega) (by omega), a1]⟩)
    (fun c' h hlt => ⟨by
        have := h.1
        refine ⟨fun r => ?_, fun a => ?_⟩
        · simp only [upd_apply]; split_ifs
          · rw [h.2.2.2.1 101 (by omega) (by omega), a1]; omega
          · exact this.1 r
        · exact this.2 a, h.2.1, h.2.2.1,
      fun r h1 h2 => by simp only [upd_apply, h2, ↓reduceIte]; exact h.2.2.2.1 r h1 h2,
      by simp only [upd_apply]; exact h.2.2.2.2⟩)
    (fun c' h hj => by
      obtain ⟨hw, hm, ho, hr, h85⟩ := h
      have g123 : c'.nreg 123 = l₁ := by rw [hr 123 (by omega) (by omega), h123]
      have g118 : c'.nreg 118 = 13 * m + 7 * n + 2 := by rw [hr 118 (by omega) (by omega), a18]
      have g101 : c'.nreg 101 = 1 := by rw [hr 101 (by omega) (by omega), a1]
      have r1 : c'.nmem (c'.nreg 118 + (c'.nreg 123 + c'.nreg 101 + c'.nreg 126)) =
          lc (l₁ + 1 + c'.nreg 126) := by
        rw [hm, g118, g123, g101]; exact hlc _ (by omega)
      unfold cntJ'
      exec_block
      all_goals try (config_simp; omega)
      refine ⟨⟨‹_›, by config_simp; exact hm, by config_simp; exact ho,
        fun r h1 h2 => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r h1 h2,
        by config_simp; exact h85⟩, ?_, by config_simp, by omega⟩
      config_simp; rw [r1])
    hex (by omega) _ ⟨e₁.wb_right, rfl, rfl, fun r h1 h2 => by
      simp only [upd_apply, h2, ↓reduceIte], by simp only [upd_apply]; exact h85⟩
    (by simp only [upd_apply, ↓reduceIte]; exact a0)
  refine ⟨c', 1 + 0 + k', .seq (.seq e₁ (.skip e₁.wb_right)) e', by omega, hm', ho',
    fun r h1 h2 => by
      rw [hr' r h1 h2], hj', hf'⟩

end thin

end SepProg

end PlanarSeparator
