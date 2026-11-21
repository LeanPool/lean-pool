/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Front

/-!
# The separator program: the faces inside the fundamental cycle

After the cycle search, the order of the search of the dual tree is at `9 m + i` and the dart
`pd G` of every face `G ≠ 0` at `8 m + G` (with `m` faces); its reversal `A (pd G)` lies on the
parent face `A (pd G) / 3`. One pass over the faces in the order of the search (`inLoop`) writes
at `12 m + G` the mark `1` for the face `F = r130` and the mark of the parent for every other
face, `0` for the root face (`inLoop_exec`). By
`PlanarSeparator.Map.SpTree.IsSearch.mem_inside_iff` these are the faces inside `pd F`.
-/

@[expose] public section

namespace PlanarSeparator

namespace SepProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-- The face at position `r74` of the search: copy the mark of its parent, or `1` if it is
`F = r130`. -/
def inBody : Stmt :=
  .seq (block [.addN 69 9 74, .loadN 75 69, .addN 69 8 75, .loadN 76 69, .loadN 77 76,
    .divN 77 77 103, .addN 69 111 77, .loadN 78 69])
  (.seq (.ifLtN 75 130 .skip (.ifLtN 130 75 .skip (.instr (.copyN 78 101))))
    (block [.addN 69 111 75, .storeN 69 78, .addN 74 74 101]))

/-- **The marks of the subtree of `F`.** -/
def inLoop : Stmt := .seq (.instr (.copyN 74 101)) (.whileLtN 74 105 inBody)

section proofs

variable {n m : ℕ} {W : ℕ} {P : Input}

/-- **The marks of the subtree of `F`.** `quF` is the order of the search, `pdF` the darts
towards the parents, `AF` the reversal; every face is found once, the face `0` first, and the
parent of every other face is found before it. -/
theorem inLoop_exec (hm1 : 1 ≤ m) (hW : memTop n m + 10 ≤ W) (quF pdF AF : ℕ → ℕ) (F : ℕ)
    (hq : ∀ i < m, quF i < m) (hqi : ∀ i < m, ∀ j < m, quF i = quF j → i = j)
    (hq0 : quF 0 = 0) (hall : ∀ G < m, ∃ i < m, quF i = G)
    (hpar : ∀ i, 1 ≤ i → i < m → pdF (quF i) < 3 * m ∧ AF (pdF (quF i)) < 3 * m ∧
      ∃ i' < i, quF i' = AF (pdF (quF i)) / 3)
    (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (h8 : c.nreg 8 = 8 * m) (h9 : c.nreg 9 = 9 * m) (h130 : c.nreg 130 = F)
    (hqm : ∀ i < m, c.nmem (9 * m + i) = quF i) (hpm : ∀ G < m, c.nmem (8 * m + G) = pdF G)
    (hAm : ∀ x < 3 * m, c.nmem x = AF x) (hz : ∀ G < m, c.nmem (12 * m + G) = 0) :
    ∃ c' k, Exec P W inLoop c c' k ∧ k ≤ 22 * m + 3 ∧ c'.output = c.output ∧
      (∀ r, r ≠ 69 → r ≠ 74 → r ≠ 75 → r ≠ 76 → r ≠ 77 → r ≠ 78 → c'.nreg r = c.nreg r) ∧
      (∀ a, ¬ (12 * m ≤ a ∧ a < 13 * m) → c'.nmem a = c.nmem a) ∧
      c'.nmem (12 * m) = 0 ∧
      (∀ G < m, G ≠ 0 → c'.nmem (12 * m + G) =
        if G = F then 1 else c'.nmem (12 * m + AF (pdF G) / 3)) := by
  classical
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  have hqne : ∀ i, 1 ≤ i → i < m → quF i ≠ 0 := fun i h1 h2 e =>
    absurd (hqi i h2 0 hm1 (by rw [e, hq0])) (by omega)
  let R : Config → Config → Prop := fun c₀ c' =>
    ∀ r, r ≠ 69 → r ≠ 74 → r ≠ 75 → r ≠ 76 → r ≠ 77 → r ≠ 78 → c'.nreg r = c₀.nreg r
  let I : ℕ → Config → Prop := fun i c' => WordsBounded W c' ∧ c'.output = c.output ∧ R c c' ∧
    1 ≤ i ∧ c'.nreg 74 = i ∧
    (∀ i' < i, 1 ≤ i' → c'.nmem (12 * m + quF i') =
      if quF i' = F then 1 else c'.nmem (12 * m + AF (pdF (quF i')) / 3)) ∧
    (∀ G < m, (∀ i' < i, 1 ≤ i' → quF i' ≠ G) → c'.nmem (12 * m + G) = 0) ∧
    (∀ a, ¬ (12 * m ≤ a ∧ a < 13 * m) → c'.nmem a = c.nmem a)
  have e₁ := Exec.copyN (P := P) hc 74 101
  obtain ⟨c', k', e', ⟨hw', ho', hr', -, h74', hI1, hI2, hfr'⟩, hk'⟩ :=
    Exec.forN (P := P) (W := W) (ri := 74) (rN := 105) (N := m) (lo := 1) (B := 20)
    (body := inBody) I
    (fun i c' h => ⟨h.1, h.2.2.2.2.1, by rw [h.2.2.1 105 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega), a5]⟩)
    (fun i c' h hi => by
      obtain ⟨hw, ho, hr, hi1, h74, hI1, hI2, hfr⟩ := h
      have g : ∀ r, r ≠ 69 → r ≠ 74 → r ≠ 75 → r ≠ 76 → r ≠ 77 → r ≠ 78 → c'.nreg r = c.nreg r := hr
      have g8 : c'.nreg 8 = 8 * m := by
        rw [g 8 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h8]
      have g9 : c'.nreg 9 = 9 * m := by
        rw [g 9 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h9]
      have g101 : c'.nreg 101 = 1 := by
        rw [g 101 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a1]
      have g103 : c'.nreg 103 = 3 := by
        rw [g 103 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a3]
      have g111 : c'.nreg 111 = 12 * m := by
        rw [g 111 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), a11]
      have g130 : c'.nreg 130 = F := by
        rw [g 130 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h130]
      have hG := hq i hi
      obtain ⟨hpd, hA, i'', hi'', hpar'⟩ := hpar i hi1 hi
      have r1 : c'.nmem (c'.nreg 9 + c'.nreg 74) = quF i := by
        rw [g9, h74, hfr _ (by omega)]; exact hqm i hi
      have r2 : c'.nmem (c'.nreg 8 + quF i) = pdF (quF i) := by
        rw [g8, hfr _ (by omega)]; exact hpm _ hG
      have r3 : c'.nmem (pdF (quF i)) = AF (pdF (quF i)) := by
        rw [hfr _ (by omega)]; exact hAm _ hpd
      have hP : AF (pdF (quF i)) / 3 < m := by omega
      obtain ⟨c₁, k₁, e₁, hc₁, h75, h77, h78, hm₁, hr₁, hk₁⟩ : ∃ c₁ k₁, Exec P W
          (block [.addN 69 9 74, .loadN 75 69, .addN 69 8 75, .loadN 76 69, .loadN 77 76,
            .divN 77 77 103, .addN 69 111 77, .loadN 78 69]) c' c₁ k₁ ∧ WordsBounded W c₁ ∧
          c₁.nreg 75 = quF i ∧ c₁.nreg 77 = AF (pdF (quF i)) / 3 ∧
          c₁.nreg 78 = c'.nmem (12 * m + AF (pdF (quF i)) / 3) ∧ c₁.nmem = c'.nmem ∧
          R c' c₁ ∧ k₁ = 8 := by
        exec_block
        all_goals try (config_simp; (try simp only [r1, r2, r3, g103]); omega)
        rw [r1] at *
        rw [r2] at *
        rw [r3] at *
        refine ⟨‹_›, by config_simp, by config_simp; rw [g103], by config_simp; rw [g111, g103],
          rfl, fun r h1 h2 h3 h4 h5 h6 => by
            config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl⟩
      -- the test `G = F`
      obtain ⟨c₂, k₂, e₂, h78₂, hm₂, hr₂, hk₂⟩ : ∃ c₂ k₂, Exec P W
          (.ifLtN 75 130 .skip (.ifLtN 130 75 .skip (.instr (.copyN 78 101)))) c₁ c₂ k₂ ∧
          c₂.nreg 78 = (if quF i = F then 1 else c'.nmem (12 * m + AF (pdF (quF i)) / 3)) ∧
          c₂.nmem = c₁.nmem ∧ (∀ r, r ≠ 78 → c₂.nreg r = c₁.nreg r) ∧ k₂ ≤ 5 := by
        have g130' : c₁.nreg 130 = F := by
          rw [hr₁ 130 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g130]
        have g101' : c₁.nreg 101 = 1 := by
          rw [hr₁ 101 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g101]
        rcases Nat.lt_trichotomy (quF i) F with hl | he | hg
        · refine spec_ifLtN_true (by rw [h75, g130']; exact hl) (spec_skip hc₁
            ⟨by rw [h78, ite_eq_right (by omega)], rfl, fun _ _ => rfl, by omega⟩)
        · refine spec_ifLtN_false (by rw [h75, g130']; omega)
            (spec_ifLtN_false (by rw [h75, g130']; omega) ?_)
          refine spec_instr (Exec.copyN hc₁ 78 101) fun _ => ⟨by
            simp only [upd_apply, ↓reduceIte]; rw [g101', ite_eq_left he], rfl,
            fun r hr' => by simp only [upd_apply, hr', ↓reduceIte], by omega⟩
        · refine spec_ifLtN_false (by rw [h75, g130']; omega)
            (spec_ifLtN_true (by rw [h75, g130']; exact hg) ?_)
          exact spec_skip hc₁ ⟨by rw [h78, ite_eq_right (by omega)], rfl, fun _ _ => rfl, by omega⟩
      have hc₂ := e₂.wb_right
      obtain ⟨c₃, k₃, e₃, hfin⟩ : ∃ c₃ k₃, Exec P W (block [.addN 69 111 75, .storeN 69 78,
        .addN 74 74 101])
          c₂ c₃ k₃ ∧ (c₃.nreg 74 = i + 1 ∧ c₃.nmem = upd c'.nmem (12 * m + quF i) (c₂.nreg 78) ∧
          R c₂ c₃ ∧ c₃.output = c₂.output ∧ k₃ = 3) := by
        have g111' : c₂.nreg 111 = 12 * m := by
          rw [hr₂ 111 (by omega),
            hr₁ 111 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g111]
        have g101' : c₂.nreg 101 = 1 := by
          rw [hr₂ 101 (by omega),
            hr₁ 101 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g101]
        have g74 : c₂.nreg 74 = i := by
          rw [hr₂ 74 (by omega)]; exact (show c₁.nreg 74 = i by
            have := e₁.nreg_of_wr (r := 74) (by decide); rw [this, h74])
        have g75 : c₂.nreg 75 = quF i := by rw [hr₂ 75 (by omega), h75]
        exec_block
        all_goals try (config_simp; omega)
        exact ⟨by config_simp; omega, by config_simp; rw [g111', g75, hm₂, hm₁],
          fun r h1 h2 h3 h4 h5 h6 => by
          config_simp; simp only [upd_apply]; split_ifs <;> omega, rfl, rfl⟩
      obtain ⟨g74, hm₃, hr₃, ho₃, rfl⟩ := hfin
      have ho₁ : c₁.output = c'.output := e₁.output_of_ou (by decide)
      have ho₂ : c₂.output = c₁.output := e₂.output_of_ou (by decide)
      have hparne : ∀ j, 1 ≤ j → j < i → AF (pdF (quF j)) / 3 ≠ quF i := by
        intro j hj1 hj2 e
        obtain ⟨-, -, j', hj', hpj⟩ := hpar j hj1 (by omega)
        rw [← hpj] at e
        have := hqi j' (by omega) i hi e
        omega
      refine ⟨c₃, k₁ + (k₂ + 3), .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right, by rw [ho₃, ho₂, ho₁, ho],
        fun r h1 h2 h3 h4 h5 h6 => by
          rw [hr₃ r h1 h2 h3 h4 h5 h6, hr₂ r h6, hr₁ r h1 h2 h3 h4 h5 h6, hr r h1 h2 h3 h4 h5 h6],
        by omega, g74, fun i' hi' h1 => ?_, fun G hG' hne => ?_, fun a ha => ?_⟩, by omega⟩
      · rw [hm₃]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | hi'
        · have hne : quF i' ≠ quF i := fun e => by have := hqi i' (by omega) i hi e; omega
          rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by have := hparne i' h1 hi'; omega)]
          exact hI1 i' hi' h1
        · rw [hi'] at h1 ⊢
          have hne' : quF i ≠ AF (pdF (quF i)) / 3 := fun e => by
            have := hqi i'' (by omega) i hi (hpar'.trans e.symm); omega
          rw [upd_same, h78₂, upd_other _ _ _ (by omega)]
      · rw [hm₃, upd_other _ _ _ (by have := hne i (by omega) hi1; omega)]
        exact hI2 G hG' fun j hj h1 => hne j (by omega) h1
      · rw [hm₃, upd_other _ _ _ (by omega)]; exact hfr a ha)
    hm1 ⟨e₁.wb_right, rfl, fun r h1 h2 h3 h4 h5 h6 => by simp only [upd_apply, h2, ↓reduceIte],
      le_rfl, by simp only [upd_apply, ↓reduceIte]; exact a1, fun i' h1 h2 => by omega,
      fun G hG _ => hz G hG, fun a _ => rfl⟩
  refine ⟨c', 1 + k', .seq e₁ e', by omega, ho', fun r h1 h2 h3 h4 h5 h6 => ?_, hfr', ?_,
    fun G hG hG0 => ?_⟩
  · rw [hr' r h1 h2 h3 h4 h5 h6]
  · have := hI2 0 hm1 fun i' _ h1 => hqne i' h1 (by omega)
    simpa using this
  · obtain ⟨i, hi, rfl⟩ := hall G hG
    have hi1 : 1 ≤ i := by
      by_contra h; obtain rfl : i = 0 := by omega
      exact hG0 hq0
    exact hI1 i hi hi1

end proofs

end SepProg

end PlanarSeparator
