/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Front
public import LeanPool.PlanarSeparator.PlanarSeparator.LevelSep

/-!
# The separator program: the labels and the output

After the separator marks (`PlanarSeparator/Machine/RootPath.lean`) and the inside marks
(`PlanarSeparator/Machine/InMark.lean`), every vertex `v` gets a label (`labN`): `4` for the
separator (the two thin levels, and the vertices of the middle levels with a separator mark),
otherwise its piece: `0` below the thin level `l₁ - j`, `1` above the thin level `l₁ + 1 + j'`,
and for the middle levels `2` (inside) or `3` (outside). A vertex is inside when the inside mark
of the face of its first dart `ofs v` differs from the flag `r131`: the inside marks describe the
inside of the dart `pd F` of a face `F`, which is the dart `a` of the cycle (flag `0`) or its
reversal (flag `1`, `sideOf`).

* `sideOf`: the face `F` (in `r130`) and the flag (in `r131`) of the dart `a = r129` (for a tree
  dart `a`, whose inside is empty, `F = 0` and the flag `0`, so that no vertex is inside);
* `labLoop`: the labels at `13 m + 9 n + 4 + v` and the weights of the four pieces at
  `13 m + 10 n + 4 + i` (`labLoop_exec`);
* `grpLoop`: the parts `gpart` of the four pieces at `13 m + 10 n + 8 + i` (`grpLoop_exec`);
* `prLoop`: prints, for every vertex, `0` for the separator and the part `1` or `2` of its piece
  otherwise (`prLoop_exec`).
-/

@[expose] public section

namespace PlanarSeparator

namespace SepProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The programs -/

/-- **The side of `a = r129`**: if `a` is a tree dart (tree mark at `3 m + a`), `F = 0` and flag
`0` (nothing is inside); otherwise `F = a / 3` and flag `0` if `a` is the dart `pd` of its face (at
`8 m + a / 3`, a face other than `0`), and `F = A a / 3` and flag `1` if not. -/
def sideOf : Stmt :=
  .seq (block [.divN 83 129 103, .addN 69 8 83, .loadN 84 69, .copyN 131 101, .loadN 85 129,
    .divN 130 85 103, .addN 69 108 129, .loadN 86 69])
  (.ifLtN 100 86 (block [.copyN 131 100, .copyN 130 100])
    (.ifLtN 100 83 (.ifLtN 84 129 .skip (.ifLtN 129 84 .skip (block [.copyN 131 100,
      .copyN 130 83])))
      .skip))

/-- The label of a vertex with level `Lv`, separator mark `sv` and inside mark `iv`, for the
median level `l₁`, the thin levels `l₁ - j`, `l₁ + 1 + j'` and the flag `fl`. -/
def labN (l₁ j j' fl Lv sv iv : ℕ) : ℕ :=
  if Lv + j < l₁ then 0 else if l₁ < Lv + j then
    (if Lv < l₁ + 1 + j' then (if sv < 1 then (if iv < fl then 2 else if fl < iv then 2 else 3)
      else 4)
    else if l₁ + 1 + j' < Lv then 1 else 4) else 4

/-- The label `r81` from `r75 = L v`, `r76 = sv`, `r78 = iv`, `r79 = L v + j`,
`r80 = l₁ + 1 + j'`. -/
def labIf : Stmt :=
  .ifLtN 79 123 (.instr (.copyN 81 100))
    (.ifLtN 123 79
      (.ifLtN 75 80
        (.ifLtN 76 101
          (.ifLtN 78 131 (.instr (.copyN 81 102))
            (.ifLtN 131 78 (.instr (.copyN 81 102)) (.instr (.copyN 81 103))))
          (.instr (.copyN 81 82)))
        (.ifLtN 80 75 (.instr (.copyN 81 101)) (.instr (.copyN 81 82))))
      (.instr (.copyN 81 82)))

/-- The readings for the vertex `r74 = v`: `r75 = L v`, `r76` its separator mark, `r78` the
inside mark of the face of `ofs v`, `r79 = L v + j`, `r80 = l₁ + 1 + j'`, `r82 = 4`,
`r84 = w v`. -/
def labRead : Stmt := block [.addN 69 112 74, .loadN 75 69, .addN 69 116 74, .loadN 76 69,
  .addN 70 102 74, .readIn 77 70, .addN 69 111 77, .loadN 78 69, .addN 79 75 125,
  .addN 80 123 101, .addN 80 80 126, .addN 82 103 101, .addN 70 106 74, .readIn 84 70]

/-- Store the label and add the weight to its piece. -/
def labStore : Stmt := .seq (block [.addN 69 119 74, .storeN 69 81])
  (.ifLtN 81 82 (block [.addN 69 120 81, .loadN 83 69, .addN 83 83 84, .storeN 69 83]) .skip)

/-- One vertex `r74 = v`: its label, stored, and its weight added to its piece. -/
def labBody : Stmt := .seq labRead (.seq labIf (.seq labStore (.instr (.addN 74 74 101))))

/-- **The labels and the weights of the pieces.** -/
def labLoop : Stmt := .seq (.instr (.copyN 74 100)) (.whileLtN 74 104 labBody)

/-- One piece `r74 = i`: its part, with the accepted weight in `r86`. -/
def grpBody : Stmt :=
  .seq (block [.addN 69 120 74, .loadN 83 69, .addN 85 86 83, .addN 87 85 85, .addN 87 87 85,
    .addN 88 122 122])
  (.seq (.ifLtN 88 87 (.instr (.copyN 89 102)) (block [.copyN 89 101, .copyN 86 85]))
    (block [.addN 69 121 74, .storeN 69 89, .addN 74 74 101]))

/-- **The parts of the four pieces.** -/
def grpLoop : Stmt := .seq (block [.copyN 74 100, .copyN 86 100, .addN 82 103 101])
  (.whileLtN 74 82 grpBody)

/-- One vertex `r74 = v`: print `0` for the separator, the part of its piece otherwise. -/
def prBody : Stmt :=
  .seq (block [.addN 69 119 74, .loadN 81 69])
    (.seq (.ifLtN 81 82 (block [.addN 69 121 81, .loadN 83 69, .outN 83]) (.instr (.outN 100)))
      (.instr (.addN 74 74 101)))

/-- **The output.** -/
def prLoop : Stmt := .seq (block [.copyN 74 100, .addN 82 103 101]) (.whileLtN 74 104 prBody)

/-- **The labels, the parts and the output.** -/
def outPhase : Stmt := .seq labLoop (.seq grpLoop prLoop)

/-- The output for the labels `lab` and the weights `w` of the `n` vertices: `0` for label `4`,
the part `gpart` of the piece otherwise. -/
def outList (n Wt : ℕ) (w lab : ℕ → ℕ) : List ℕ :=
  (List.range n).map fun v =>
    if lab v < 4 then gpart Wt (fun i => ∑ u ∈ range n with lab u = i, w u) (lab v) else 0

/-! ### The side of the dart -/

/-- The dart `a` is the dart `pd` of its face, a face other than `0`. -/
def IsPd (mem : ℕ → ℕ) (m a : ℕ) : Prop := 0 < a / 3 ∧ mem (8 * m + a / 3) = a

section proofs

variable {n m : ℕ} {W : ℕ} {P : Input}

open Classical in
/-- **The side of `a`.** -/
theorem sideOf_exec (hW : memTop n m + 10 ≤ W) (c : Config) (hc : WordsBounded W c)
    (hL : Lay n m c) (h8 : c.nreg 8 = 8 * m) (ha : c.nreg 129 < 3 * m) :
    ∃ c' k, Exec P W sideOf c c' k ∧ k ≤ 17 ∧ c'.nmem = c.nmem ∧ c'.output = c.output ∧
      (∀ r, r ≠ 69 → r ≠ 83 → r ≠ 84 → r ≠ 85 → r ≠ 86 → r ≠ 130 → r ≠ 131 →
        c'.nreg r = c.nreg r) ∧
      c'.nreg 130 = (if c.nmem (3 * m + c.nreg 129) ≠ 0 then 0
        else if IsPd c.nmem m (c.nreg 129) then c.nreg 129 / 3 else c.nmem (c.nreg 129) / 3) ∧
      c'.nreg 131 = (if c.nmem (3 * m + c.nreg 129) ≠ 0 then 0
        else if IsPd c.nmem m (c.nreg 129) then 0 else 1) := by
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  unfold sideOf
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h8, a3]; omega
  · config_simp; rw [a8]; omega
  by_cases ht : c.nmem (3 * m + c.nreg 129) ≠ 0
  · refine spec_ifLtN_true (by config_simp; rw [a0, a8]; omega) ?_
    exec_block
    refine ⟨by omega, rfl, rfl, fun r h1 h2 h3 h4 h5 h6 h7 => by
      simp only [upd_apply]; split_ifs <;> omega, ?_, ?_⟩ <;>
      config_simp <;> simp [ht, a0]
  refine spec_ifLtN_false (by config_simp; rw [a0, a8]; omega) ?_
  rw [ite_eq_right ht, ite_eq_right ht]
  by_cases h0 : 0 < c.nreg 129 / 3
  · refine spec_ifLtN_true (by config_simp; rw [a0, a3]; exact h0) ?_
    rcases Nat.lt_trichotomy (c.nmem (8 * m + c.nreg 129 / 3)) (c.nreg 129) with hl | he | hg
    · refine spec_ifLtN_true (by config_simp; rw [a3, h8]; exact hl) (spec_skip ‹_› ?_)
      have : ¬ IsPd c.nmem m (c.nreg 129) := fun h => by unfold IsPd at h; omega
      refine ⟨by omega, rfl, rfl, fun r h1 h2 h3 h4 h5 h6 h7 => by
        simp only [upd_apply]; split_ifs <;> omega, ?_, ?_⟩ <;>
        config_simp <;> simp [this, a3, a1]
    · refine spec_ifLtN_false (by config_simp; rw [a3, h8]; omega)
        (spec_ifLtN_false (by config_simp; rw [a3, h8]; omega) ?_)
      exec_block
      have : IsPd c.nmem m (c.nreg 129) := ⟨h0, he⟩
      refine ⟨by omega, rfl, rfl, fun r h1 h2 h3 h4 h5 h6 h7 => by
        simp only [upd_apply]; split_ifs <;> omega, ?_, ?_⟩ <;>
        config_simp <;> simp [this, a0, a3]
    · refine spec_ifLtN_false (by config_simp; rw [a3, h8]; omega)
        (spec_ifLtN_true (by config_simp; rw [a3, h8]; exact hg) (spec_skip ‹_› ?_))
      have : ¬ IsPd c.nmem m (c.nreg 129) := fun h => by unfold IsPd at h; omega
      refine ⟨by omega, rfl, rfl, fun r h1 h2 h3 h4 h5 h6 h7 => by
        simp only [upd_apply]; split_ifs <;> omega, ?_, ?_⟩ <;>
        config_simp <;> simp [this, a3, a1]
  · refine spec_ifLtN_false (by config_simp; rw [a0, a3]; exact h0) (spec_skip ‹_› ?_)
    have : ¬ IsPd c.nmem m (c.nreg 129) := fun h => h0 h.1
    refine ⟨by omega, rfl, rfl, fun r h1 h2 h3 h4 h5 h6 h7 => by
      simp only [upd_apply]; split_ifs <;> omega, ?_, ?_⟩ <;>
      config_simp <;> simp [this, a3, a1]

/-- **The label.** -/
theorem labIf_exec (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (h79 : c.nreg 79 = c.nreg 75 + c.nreg 125) (h80 : c.nreg 80 = c.nreg 123 + 1 + c.nreg 126)
    (h82 : c.nreg 82 = 4) :
    ∃ c' k, Exec P W labIf c c' k ∧ k ≤ 12 ∧
      c'.nreg 81 = labN (c.nreg 123) (c.nreg 125) (c.nreg 126) (c.nreg 131) (c.nreg 75)
        (c.nreg 76) (c.nreg 78) := by
  obtain ⟨a0, a1, a2, a3, -⟩ := hL
  unfold labIf labN
  rw [← h79, ← h80]
  by_cases c1 : c.nreg 79 < c.nreg 123
  · refine spec_ifLtN_true c1 (spec_instr (Exec.copyN hc 81 100) fun _ => ⟨by omega, ?_⟩)
    simp [c1, a0]
  refine spec_ifLtN_false c1 ?_
  rw [ite_eq_right c1]
  by_cases c2 : c.nreg 123 < c.nreg 79
  · refine spec_ifLtN_true c2 ?_
    rw [ite_eq_left c2]
    by_cases c3 : c.nreg 75 < c.nreg 80
    · refine spec_ifLtN_true c3 ?_
      rw [ite_eq_left c3]
      by_cases c4 : c.nreg 76 < c.nreg 101
      · refine spec_ifLtN_true c4 ?_
        rw [a1] at c4
        rw [ite_eq_left c4]
        by_cases c5 : c.nreg 78 < c.nreg 131
        · refine spec_ifLtN_true c5 (spec_instr (Exec.copyN hc 81 102) fun _ => ⟨by omega, ?_⟩)
          simp [c5, a2]
        refine spec_ifLtN_false c5 ?_
        by_cases c6 : c.nreg 131 < c.nreg 78
        · refine spec_ifLtN_true c6 (spec_instr (Exec.copyN hc 81 102) fun _ => ⟨by omega, ?_⟩)
          simp [c5, c6, a2]
        · refine spec_ifLtN_false c6 (spec_instr (Exec.copyN hc 81 103) fun _ => ⟨by omega, ?_⟩)
          simp [c5, c6, a3]
      · refine spec_ifLtN_false c4 (spec_instr (Exec.copyN hc 81 82) fun _ => ⟨by omega, ?_⟩)
        rw [a1] at c4
        simp [c4, h82]
    · refine spec_ifLtN_false c3 ?_
      rw [ite_eq_right c3]
      by_cases c7 : c.nreg 80 < c.nreg 75
      · refine spec_ifLtN_true c7 (spec_instr (Exec.copyN hc 81 101) fun _ => ⟨by omega, ?_⟩)
        simp [c7, a1]
      · refine spec_ifLtN_false c7 (spec_instr (Exec.copyN hc 81 82) fun _ => ⟨by omega, ?_⟩)
        simp [c7, h82]
  · refine spec_ifLtN_false c2 (spec_instr (Exec.copyN hc 81 82) fun _ => ⟨by omega, ?_⟩)
    simp [c2, h82]

end proofs

theorem sum_filter_succ_le {n : ℕ} (w lab : ℕ → ℕ) {i t : ℕ} (hi : i < n) :
    (∑ v ∈ range i with lab v = t, w v) + w i ≤ ∑ v ∈ range n, w v := by
  have h1 : ∑ v ∈ range i with lab v = t, w v ≤ ∑ v ∈ range i, w v :=
    sum_le_sum_of_subset (filter_subset _ _)
  have h2 : ∑ v ∈ range (i + 1), w v ≤ ∑ v ∈ range n, w v :=
    sum_le_sum_of_subset (range_subset_range.2 hi)
  rw [sum_range_succ] at h2
  omega

theorem sum_filter_range_succ (w lab : ℕ → ℕ) (i t : ℕ) :
    ∑ v ∈ range (i + 1) with lab v = t, w v =
      (∑ v ∈ range i with lab v = t, w v) + if lab i = t then w i else 0 := by
  rw [sum_filter, sum_filter, sum_range_succ]

theorem gacc_le (Wt : ℕ) (p : ℕ → ℕ) (i : ℕ) : gacc Wt p i ≤ ∑ t ∈ range i, p t := by
  induction i with
  | zero => simp [gacc]
  | succ i ih => rw [gacc, sum_range_succ]; split_ifs <;> omega

section loops

variable {n m : ℕ} {ofs w tl rv ro : ℕ → ℕ} {W : ℕ} {P : Input}
  (hN : NWf n m ofs tl rv ro) (hIn : InHolds P n m ofs w tl rv ro)
  (hW : memTop n m + 3 * ∑ v ∈ range n, w v + 2 * n + 3 * m + 10 ≤ W)
  (hPW : ∀ j, P.data.getD j 0 ≤ W)
include hN hIn hW hPW

omit hPW in
/-- **The labels and the weights of the pieces.** With the levels `L`, the separator marks `sm`
and the inside marks `im` of the faces, the label of every vertex `v` is
`labN l₁ j j' fl (L v) (sm v) (im (ofs v))`, and piece `i < 4` weighs the vertices of label
`i`. -/
theorem labLoop_exec (L sm im : ℕ → ℕ) (l₁ j j' fl : ℕ) (c : Config) (hc : WordsBounded W c)
    (hL : Lay n m c) (hLm : ∀ v < n, c.nmem (13 * m + v) = L v) (hLn : ∀ v < n, L v ≤ n)
    (hsm : ∀ v < n, c.nmem (13 * m + 4 * n + v) = sm v)
    (him : ∀ x ≤ m, c.nmem (12 * m + x) = im x) (h123 : c.nreg 123 = l₁)
    (h125 : c.nreg 125 = j) (h126 : c.nreg 126 = j') (h131 : c.nreg 131 = fl) (hl₁ : l₁ ≤ n)
    (hj : j ≤ n) (hj' : j' ≤ n) (hz : ∀ i < 4, c.nmem (13 * m + 10 * n + 4 + i) = 0) :
    ∃ c' k, Exec P W labLoop c c' k ∧ k ≤ 42 * n + 3 ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, ¬ (13 * m + 9 * n + 4 ≤ a ∧ a < 13 * m + 10 * n + 8) → c'.nmem a = c.nmem a) ∧
      (∀ v < n, c'.nmem (13 * m + 9 * n + 4 + v) = labN l₁ j j' fl (L v) (sm v) (im (ofs v))) ∧
      (∀ i < 4, c'.nmem (13 * m + 10 * n + 4 + i) =
        ∑ v ∈ range n with labN l₁ j j' fl (L v) (sm v) (im (ofs v)) = i, w v) := by
  have hW' := hW; unfold memTop at hW'
  have hL0 := hL
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  generalize hlab : (fun v => labN l₁ j j' fl (L v) (sm v) (im (ofs v))) = lab
  have hlab' : ∀ v, labN l₁ j j' fl (L v) (sm v) (im (ofs v)) = lab v := fun v => by rw [← hlab]
  simp only [hlab']
  have hlab4 : ∀ v, lab v ≤ 4 := fun v => by
    rw [← hlab']; unfold labN; split_ifs <;> omega
  have e₀ := Exec.copyN (P := P) hc 74 100
  obtain ⟨c', k', e', ⟨hw', ho', hr', h74', hl', hp', hfr'⟩, hk'⟩ :=
    Exec.forN (P := P) (W := W) (ri := 74) (rN := 104) (N := n) (lo := 0) (B := 40)
    (body := labBody) (fun i c' => WordsBounded W c' ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nreg 74 = i ∧
      (∀ v < i, c'.nmem (13 * m + 9 * n + 4 + v) = lab v) ∧
      (∀ t < 4, c'.nmem (13 * m + 10 * n + 4 + t) = ∑ v ∈ range i with lab v = t, w v) ∧
      (∀ a, ¬ (13 * m + 9 * n + 4 ≤ a ∧ a < 13 * m + 10 * n + 8) → c'.nmem a = c.nmem a))
    (fun i c' h => ⟨h.1, h.2.2.2.1, by rw [h.2.2.1 104 (by omega), a4]⟩)
    (fun i c' h hi => by
      obtain ⟨hw, ho, hr, h74, hl, hp, hfr⟩ := h
      have g : ∀ r, 100 ≤ r → c'.nreg r = c.nreg r := hr
      have hofs : ofs i ≤ m := hN.ofs_le_m (by omega)
      have g101 : c'.nreg 101 = 1 := by rw [g 101 (by omega), a1]
      have g102 : c'.nreg 102 = 2 := by rw [g 102 (by omega), a2]
      have g103 : c'.nreg 103 = 3 := by rw [g 103 (by omega), a3]
      have g106 : c'.nreg 106 = n + 3 := by rw [g 106 (by omega), a6]
      have g111 : c'.nreg 111 = 12 * m := by rw [g 111 (by omega), a11]
      have g112 : c'.nreg 112 = 13 * m := by rw [g 112 (by omega), a12]
      have g116 : c'.nreg 116 = 13 * m + 4 * n := by rw [g 116 (by omega), a16]
      have g123 : c'.nreg 123 = l₁ := by rw [g 123 (by omega), h123]
      have g125 : c'.nreg 125 = j := by rw [g 125 (by omega), h125]
      have g126 : c'.nreg 126 = j' := by rw [g 126 (by omega), h126]
      have r1 : c'.nmem (13 * m + i) = L i := by rw [hfr _ (by omega)]; exact hLm i hi
      have r2 : c'.nmem (13 * m + 4 * n + i) = sm i := by rw [hfr _ (by omega)]; exact hsm i hi
      have r3 : P.data.getD (2 + i) 0 = ofs i := hIn.ofs_eq i (by omega)
      have r4 : c'.nmem (12 * m + ofs i) = im (ofs i) := by rw [hfr _ (by omega)]; exact him _ hofs
      have r5 : P.data.getD (n + 3 + i) 0 = w i := hIn.w_eq i hi
      have hwi : w i ≤ ∑ v ∈ range n,
        w v := single_le_sum (fun _ _ => Nat.zero_le _) (mem_range.2 hi)
      -- the readings
      obtain ⟨c₁, k₁, e₁, h75, h76, h78, h79, h80, h82, h84, hk₁⟩ :
          ∃ c₁ k₁, Exec P W labRead c' c₁ k₁ ∧ c₁.nreg 75 = L i ∧ c₁.nreg 76 = sm i ∧
            c₁.nreg 78 = im (ofs i) ∧ c₁.nreg 79 = c₁.nreg 75 + c₁.nreg 125 ∧
            c₁.nreg 80 = c₁.nreg 123 + 1 + c₁.nreg 126 ∧ c₁.nreg 82 = 4 ∧ c₁.nreg 84 = w i ∧
            k₁ = 14 := by
        have hLi := hLn i hi
        unfold labRead
        exec_block
        all_goals config_simp
        all_goals simp only [h74, g101, g102, g103, g106, g111, g112, g116, g123, g125, g126]
        all_goals try simp only [r1, r2, r3, r4, r5]
        all_goals try omega
        simp only [and_self]
      have hm₁ : c₁.nmem = c'.nmem := e₁.nmem_of_st (by decide)
      have hwm : labRead.wmax = 84 := by decide
      have hr₁ : ∀ r, 100 ≤ r → c₁.nreg r = c.nreg r := fun r hr' =>
        (e₁.nreg_of_wr (Stmt.wr_of_wmax (by omega))).trans (g r hr')
      have h74₁ : c₁.nreg 74 = i := (e₁.nreg_of_wr (by decide)).trans h74
      have hL₁ : Lay n m c₁ := hL0.of fun r h1 _ => hr₁ r h1
      -- the label
      obtain ⟨c₂, k₂, e₂, hk₂, h81⟩ := labIf_exec (P := P) c₁ e₁.wb_right hL₁ h79 h80 h82
      rw [hr₁ 123 (by omega), hr₁ 125 (by omega), hr₁ 126 (by omega), hr₁ 131 (by omega), h123,
        h125, h126, h131, h75, h76, h78, hlab'] at h81
      have hm₂ : c₂.nmem = c₁.nmem := e₂.nmem_of_st (by decide)
      have hwm₂ : labIf.wmax = 81 := by decide
      have hr₂ : ∀ r, 100 ≤ r → c₂.nreg r = c.nreg r := fun r hr' =>
        (e₂.nreg_of_wr (Stmt.wr_of_wmax (by omega))).trans (hr₁ r hr')
      have h74₂ : c₂.nreg 74 = i := (e₂.nreg_of_wr (by decide)).trans h74₁
      have h82₂ : c₂.nreg 82 = 4 := (e₂.nreg_of_wr (by decide)).trans h82
      have h84₂ : c₂.nreg 84 = w i := (e₂.nreg_of_wr (by decide)).trans h84
      -- the store
      have hli := hlab4 i
      have hsb := sum_filter_succ_le w lab (t := lab i) hi
      obtain ⟨c₃, k₃, e₃, hm₃, hk₃⟩ : ∃ c₃ k₃, Exec P W labStore c₂ c₃ k₃ ∧
          c₃.nmem = (if lab i < 4 then upd (upd c'.nmem (13 * m + 9 * n + 4 + i) (lab i))
            (13 * m + 10 * n + 4 + lab i) (c'.nmem (13 * m + 10 * n + 4 + lab i) + w i)
            else upd c'.nmem (13 * m + 9 * n + 4 + i) (lab i)) ∧ k₃ ≤ 9 := by
        have g119 : c₂.nreg 119 = 13 * m + 9 * n + 4 := by rw [hr₂ 119 (by omega), a19]
        have g120 : c₂.nreg 120 = 13 * m + 10 * n + 4 := by rw [hr₂ 120 (by omega), a20]
        have hw₂ := e₂.wb_right
        unfold labStore
        refine spec_seq ?_
        exec_block
        · rw [g119, h74₂]; omega
        by_cases hl4 : lab i < 4
        · refine spec_ifLtN_true (by config_simp; rw [h81, h82₂]; exact hl4) ?_
          exec_block
          · config_simp; rw [g120, h81]; omega
          · config_simp; rw [g120, h81, g119, h74₂, h84₂, hm₂, hm₁,
              upd_other _ _ _ (by omega), hp _ hl4]; omega
          config_simp
          rw [g120, h81, g119, h74₂, h84₂, hm₂, hm₁, ite_eq_left hl4, upd_other _ _ _ (by omega)]
          exact ⟨rfl, by omega⟩
        · refine spec_ifLtN_false (by config_simp; rw [h81, h82₂]; exact hl4) (spec_skip ‹_› ?_)
          config_simp
          rw [g119, h81, h74₂, hm₂, hm₁, ite_eq_right hl4]
          exact ⟨rfl, by omega⟩
      have hwm₃ : labStore.wmax = 83 := by decide
      have hr₃ : ∀ r, 100 ≤ r → c₃.nreg r = c.nreg r := fun r hr' =>
        (e₃.nreg_of_wr (Stmt.wr_of_wmax (by omega))).trans (hr₂ r hr')
      have h74₃ : c₃.nreg 74 = i := (e₃.nreg_of_wr (by decide)).trans h74₂
      have e₄ := Exec.addN (P := P) e₃.wb_right 74 74 101
        (by rw [h74₃, hr₃ 101 (by omega), a1]; omega)
      refine ⟨_, k₁ + (k₂ + (k₃ + 1)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), ⟨e₄.wb_right, ?_, ?_, ?_,
        ?_, ?_, ?_⟩, by omega⟩
      · rw [e₃.output_of_ou (by decide), e₂.output_of_ou (by decide), e₁.output_of_ou (by decide),
          ho]
      · intro r hr'; simp only [upd_apply]; split_ifs <;> first | omega | exact hr₃ r hr'
      · simp only [upd_same]; rw [h74₃, hr₃ 101 (by omega), a1]
      · intro v hv
        simp only [hm₃]
        split_ifs with hl4
        · rw [upd_other _ _ _ (by omega)]
          rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
          · rw [upd_other _ _ _ (by omega)]; exact hl v hv
          · rw [upd_same]
        · rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
          · rw [upd_other _ _ _ (by omega)]; exact hl v hv
          · rw [upd_same]
      · intro t ht
        simp only [hm₃]
        rw [sum_filter_range_succ, ← hp t ht]
        split_ifs with hl4 heq heq
        · subst heq; rw [upd_same]
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; omega
        · omega
        · rw [upd_other _ _ _ (by omega)]; omega
      · intro a ha
        simp only [hm₃]
        split_ifs
        · rw [upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]; exact hfr a ha
        · rw [upd_other _ _ _ (by omega)]; exact hfr a ha)
    (Nat.zero_le n) ⟨e₀.wb_right, rfl, fun r hr => by simp only [upd_apply]; split_ifs <;> omega,
      by simp only [upd_apply, ↓reduceIte]; exact a0, fun v hv => by omega,
      fun t ht => by simp only [range_zero, filter_empty, sum_empty]; exact hz t ht,
      fun a _ => rfl⟩
  exact ⟨c', 1 + k', .seq e₀ e', by omega, ho', hr', hfr', fun v hv => hl' v hv, hp'⟩

omit hN hIn hPW in
/-- **The parts of the four pieces**, greedily (`gpart`), for the piece weights `p` and the total
`Wt = r122`. -/
theorem grpLoop_exec (p : ℕ → ℕ) (Wt : ℕ) (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (hpm : ∀ i < 4, c.nmem (13 * m + 10 * n + 4 + i) = p i) (h122 : c.nreg 122 = Wt)
    (hWt : Wt ≤ ∑ v ∈ range n, w v) (hp : ∑ i ∈ range 4, p i ≤ Wt) :
    ∃ c' k, Exec P W grpLoop c c' k ∧ k ≤ 81 ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, ¬ (13 * m + 10 * n + 8 ≤ a ∧ a < 13 * m + 10 * n + 12) → c'.nmem a = c.nmem a) ∧
      (∀ i < 4, c'.nmem (13 * m + 10 * n + 8 + i) = gpart Wt p i) := by
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  obtain ⟨c₀, k₀, e₀, hw₀, hr₀, h74₀, h86₀, h82₀, hm₀, ho₀, rfl⟩ : ∃ c₀ k₀, Exec P W
      (block [.copyN 74 100, .copyN 86 100, .addN 82 103 101]) c c₀ k₀ ∧ WordsBounded W c₀ ∧
      (∀ r, 100 ≤ r → c₀.nreg r = c.nreg r) ∧ c₀.nreg 74 = 0 ∧ c₀.nreg 86 = 0 ∧
      c₀.nreg 82 = 4 ∧ c₀.nmem = c.nmem ∧ c₀.output = c.output ∧ k₀ = 3 := by
    exec_block
    · config_simp; omega
    exact ⟨‹_›, fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega,
      by config_simp; exact a0, by config_simp; exact a0, by config_simp; rw [a3, a1], rfl, rfl,
      rfl⟩
  obtain ⟨c', k', e', ⟨hw', ho', hr', h74', -, -, hg', hfr'⟩, hk'⟩ :=
    Exec.forN (P := P) (W := W) (ri := 74) (rN := 82) (N := 4) (lo := 0) (B := 13)
    (body := grpBody) (fun i c' => WordsBounded W c' ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nreg 74 = i ∧ c'.nreg 82 = 4 ∧
      c'.nreg 86 = gacc Wt p i ∧
      (∀ t < i, c'.nmem (13 * m + 10 * n + 8 + t) = gpart Wt p t) ∧
      (∀ a, ¬ (13 * m + 10 * n + 8 ≤ a ∧ a < 13 * m + 10 * n + 12) → c'.nmem a = c.nmem a))
    (fun i c' h => ⟨h.1, h.2.2.2.1, h.2.2.2.2.1⟩)
    (fun i c' h hi => by
      obtain ⟨hw, ho, hr, h74, h82, h86, hg, hfr⟩ := h
      have g120 : c'.nreg 120 = 13 * m + 10 * n + 4 := by rw [hr 120 (by omega), a20]
      have g121 : c'.nreg 121 = 13 * m + 10 * n + 8 := by rw [hr 121 (by omega), a21]
      have g122 : c'.nreg 122 = Wt := by rw [hr 122 (by omega), h122]
      have g101 : c'.nreg 101 = 1 := by rw [hr 101 (by omega), a1]
      have g102 : c'.nreg 102 = 2 := by rw [hr 102 (by omega), a2]
      have r1 : c'.nmem (13 * m + 10 * n + 4 + i) = p i := by
        rw [hfr _ (by omega)]; exact hpm i hi
      have hacc := gacc_le Wt p i
      have hsum : ∑ t ∈ range (i + 1), p t ≤ Wt :=
        (sum_le_sum_of_subset (range_subset_range.2 (by omega))).trans hp
      rw [sum_range_succ] at hsum
      obtain ⟨c₁, k₁, e₁, h85, h87, h88, hk₁⟩ : ∃ c₁ k₁, Exec P W (block [.addN 69 120 74,
          .loadN 83 69, .addN 85 86 83, .addN 87 85 85, .addN 87 87 85,
            .addN 88 122 122]) c' c₁ k₁ ∧
          c₁.nreg 85 = gacc Wt p i + p i ∧ c₁.nreg 87 = 3 * (gacc Wt p i + p i) ∧
          c₁.nreg 88 = 2 * Wt ∧ k₁ = 6 := by
        exec_block
        all_goals config_simp
        all_goals simp only [h74, h86, g120, g122, r1]
        all_goals try omega
        exact ⟨trivial, by omega, by omega⟩
      have hw₁ := e₁.wb_right
      have hwm₁ : (block [.addN 69 120 74, .loadN 83 69, .addN 85 86 83, .addN 87 85 85,
        .addN 87 87 85, .addN 88 122 122]).wmax = 88 := by decide
      have hr₁ : ∀ r, 100 ≤ r → c₁.nreg r = c.nreg r := fun r hr' =>
        (e₁.nreg_of_wr (Stmt.wr_of_wmax (by omega))).trans (hr r hr')
      have hm₁ : c₁.nmem = c'.nmem := e₁.nmem_of_st (by decide)
      have h74₁ : c₁.nreg 74 = i := (e₁.nreg_of_wr (by decide)).trans h74
      have h82₁ : c₁.nreg 82 = 4 := (e₁.nreg_of_wr (by decide)).trans h82
      have h86₁ : c₁.nreg 86 = gacc Wt p i := (e₁.nreg_of_wr (by decide)).trans h86
      obtain ⟨c₂, k₂, e₂, h89, h86₂, hr₂, hk₂⟩ : ∃ c₂ k₂, Exec P W
          (.ifLtN 88 87 (.instr (.copyN 89 102)) (block [.copyN 89 101, .copyN 86 85])) c₁ c₂ k₂ ∧
          c₂.nreg 89 = gpart Wt p i ∧ c₂.nreg 86 = gacc Wt p (i + 1) ∧
          (∀ r, r ≠ 86 → r ≠ 89 → c₂.nreg r = c₁.nreg r) ∧ k₂ ≤ 4 := by
        by_cases ht : 3 * (gacc Wt p i + p i) ≤ 2 * Wt
        · refine spec_ifLtN_false (by rw [h87, h88]; omega) ?_
          exec_block
          refine ⟨?_, ?_, fun r h1 h2 => by simp only [upd_apply, h1, h2, ↓reduceIte], by omega⟩
          · config_simp; rw [hr₁ 101 (by omega), a1, gpart, ite_eq_left ht]
          · config_simp; rw [h85, gacc, ite_eq_left ht]
        · refine spec_ifLtN_true (by rw [h87, h88]; omega) ?_
          refine spec_instr (Exec.copyN hw₁ 89 102) fun _ => ⟨?_, ?_, fun r h1 h2 => by
            simp only [upd_apply, h2, ↓reduceIte], by omega⟩
          · simp only [upd_same]; rw [hr₁ 102 (by omega), a2, gpart,
              ite_eq_right ht]
          · simp only [upd_apply]; rw [h86₁, gacc, ite_eq_right ht]; rfl
      have hm₂ : c₂.nmem = c₁.nmem := e₂.nmem_of_st (by decide)
      have hw₂ := e₂.wb_right
      have hr₂' : ∀ r, 100 ≤ r → c₂.nreg r = c.nreg r := fun r hr' =>
        (hr₂ r (by omega) (by omega)).trans (hr₁ r hr')
      have h89' : gpart Wt p i ≤ 2 := by unfold gpart; split_ifs <;> omega
      obtain ⟨c₃, k₃, e₃, h74₃, h86₃, hm₃, hr₃, h82₃, hk₃⟩ : ∃ c₃ k₃, Exec P W
          (block [.addN 69 121 74, .storeN 69 89, .addN 74 74 101]) c₂ c₃ k₃ ∧
          c₃.nreg 74 = i + 1 ∧ c₃.nreg 86 = gacc Wt p (i + 1) ∧
          c₃.nmem = upd c'.nmem (13 * m + 10 * n + 8 + i) (gpart Wt p i) ∧
          (∀ r, 100 ≤ r → c₃.nreg r = c.nreg r) ∧ c₃.nreg 82 = 4 ∧ k₃ = 3 := by
        have g121' : c₂.nreg 121 = 13 * m + 10 * n + 8 := by rw [hr₂' 121 (by omega), a21]
        have g74 : c₂.nreg 74 = i := by rw [hr₂ 74 (by omega) (by omega), h74₁]
        have g101' : c₂.nreg 101 = 1 := by rw [hr₂' 101 (by omega), a1]
        exec_block
        all_goals try (config_simp; simp only [g121', g74, g101']; omega)
        refine ⟨by config_simp; rw [g74, g101'], by config_simp; exact h86₂,
          by config_simp; rw [g121', g74, h89, hm₂, hm₁], fun r hr' => by
          config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr₂' r hr',
          by config_simp; rw [hr₂ 82 (by omega) (by omega), h82₁], rfl⟩
      refine ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), ⟨e₃.wb_right, ?_, hr₃, h74₃, h82₃, h86₃,
        fun t ht => ?_, fun a ha => ?_⟩, by omega⟩
      · rw [e₃.output_of_ou (by decide), e₂.output_of_ou (by decide), e₁.output_of_ou (by decide),
        ho]
      · rw [hm₃, upd_apply]
        split_ifs with h
        · rw [show t = i by omega]
        · exact hg t (by omega)
      · rw [hm₃, upd_other _ _ _ (by omega)]; exact hfr a ha)
    (by omega) ⟨hw₀, ho₀, hr₀, h74₀, h82₀, by rw [h86₀]; rfl, fun t ht => by omega,
      fun a _ => by rw [hm₀]⟩
  exact ⟨c', 3 + k', .seq e₀ e', by omega, ho', hr', hfr', fun i hi => hg' i hi⟩

omit hN hIn hPW in
/-- **The output**: for every vertex `v`, `0` if its label is `4`, and the part of its piece
otherwise. -/
theorem prLoop_exec (lab part : ℕ → ℕ) (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (hlab : ∀ v < n, c.nmem (13 * m + 9 * n + 4 + v) = lab v) (hlab4 : ∀ v < n, lab v ≤ 4)
    (hpart : ∀ i < 4, c.nmem (13 * m + 10 * n + 8 + i) = part i) :
    ∃ c' k, Exec P W prLoop c c' k ∧ k ≤ 12 * n + 4 ∧
      c'.output = c.output ++ (List.range n).map (fun v => if lab v < 4 then part (lab v) else 0) ∧
      c'.nmem = c.nmem ∧ (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) := by
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  obtain ⟨c₀, k₀, e₀, hw₀, hr₀, h74₀, h82₀, hm₀, ho₀, rfl⟩ : ∃ c₀ k₀, Exec P W
      (block [.copyN 74 100, .addN 82 103 101]) c c₀ k₀ ∧ WordsBounded W c₀ ∧
      (∀ r, 100 ≤ r → c₀.nreg r = c.nreg r) ∧ c₀.nreg 74 = 0 ∧
      c₀.nreg 82 = 4 ∧ c₀.nmem = c.nmem ∧ c₀.output = c.output ∧ k₀ = 2 := by
    exec_block
    · config_simp; omega
    exact ⟨‹_›, fun r hr => by config_simp; simp only [upd_apply]; split_ifs <;> omega,
      by config_simp; exact a0, by config_simp; rw [a3, a1], rfl, rfl, rfl⟩
  obtain ⟨c', k', e', ⟨hw', ho', hr', h74', -, hm'⟩, hk'⟩ :=
    Exec.forN (P := P) (W := W) (ri := 74) (rN := 104) (N := n) (lo := 0) (B := 10)
    (body := prBody) (fun i c' => WordsBounded W c' ∧
      c'.output = c.output ++ (List.range i).map (fun v => if lab v < 4 then part (lab v) else 0) ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nreg 74 = i ∧ c'.nreg 82 = 4 ∧ c'.nmem = c.nmem)
    (fun i c' h => ⟨h.1, h.2.2.2.1, by rw [h.2.2.1 104 (by omega), a4]⟩)
    (fun i c' h hi => by
      obtain ⟨hw, ho, hr, h74, h82, hm⟩ := h
      have g119 : c'.nreg 119 = 13 * m + 9 * n + 4 := by rw [hr 119 (by omega), a19]
      have g121 : c'.nreg 121 = 13 * m + 10 * n + 8 := by rw [hr 121 (by omega), a21]
      have g101 : c'.nreg 101 = 1 := by rw [hr 101 (by omega), a1]
      have g100 : c'.nreg 100 = 0 := by rw [hr 100 (by omega), a0]
      have hl4 := hlab4 i hi
      unfold prBody
      refine spec_seq ?_
      exec_block
      · rw [g119, h74]; omega
      refine spec_seq ?_
      have r1 : c'.nmem (c'.nreg 119 + c'.nreg 74) = lab i := by rw [g119, h74, hm]; exact hlab i hi
      by_cases hlt : lab i < 4
      · refine spec_ifLtN_true (by config_simp; rw [r1, h82]; exact hlt) ?_
        exec_block
        · config_simp; rw [r1, g121]; omega
        refine spec_instr (Exec.addN ‹_› 74 74 101 (by config_simp; rw [h74, g101]; omega))
          fun _ => ⟨⟨‹_›, ?_, fun r hr' => ?_, ?_, ?_, ?_⟩, by omega⟩
        · config_simp; rw [r1, g121, ho, List.range_succ, List.map_append, List.append_assoc]
          simp only [List.map_cons, List.map_nil, ite_eq_left hlt, hm, hpart _ hlt]
        · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr'
        · config_simp; rw [h74, g101]
        · config_simp; exact h82
        · config_simp; exact hm
      · refine spec_ifLtN_false (by config_simp; rw [r1, h82]; exact hlt) ?_
        refine spec_instr (Exec.outN ‹_› 100) fun _ => ?_
        refine spec_instr (Exec.addN ‹_› 74 74 101 (by config_simp; rw [h74, g101]; omega))
          fun _ => ⟨⟨‹_›, ?_, fun r hr' => ?_, ?_, ?_, ?_⟩, by omega⟩
        · config_simp; rw [g100, ho, List.range_succ, List.map_append, List.append_assoc]
          simp only [List.map_cons, List.map_nil, ite_eq_right hlt]
        · config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr'
        · config_simp; rw [h74, g101]
        · config_simp; exact h82
        · config_simp; exact hm)
    (Nat.zero_le n) ⟨hw₀, by rw [ho₀]; simp, hr₀, h74₀, h82₀, hm₀⟩
  exact ⟨c', 2 + k', .seq e₀ e', by omega, ho', hm', hr'⟩

omit hN hIn hW hPW in
theorem sum_pieces_le (w lab : ℕ → ℕ) (n : ℕ) (hlab : ∀ v, lab v ≤ 4) :
    ∑ i ∈ range 4, ∑ v ∈ range n with lab v = i, w v ≤ ∑ v ∈ range n, w v := by
  have := sum_fiberwise_of_maps_to (s := range n) (t := range 5) (g := lab) (f := w)
    (fun v _ => mem_range.2 (by have := hlab v; omega))
  rw [← this, sum_range_succ (n := 4)]
  omega

omit hPW in
/-- **The labels, the parts and the output.** -/
theorem outPhase_exec (L sm im : ℕ → ℕ) (l₁ j j' fl : ℕ) (c : Config) (hc : WordsBounded W c)
    (hL : Lay n m c) (hLm : ∀ v < n, c.nmem (13 * m + v) = L v) (hLn : ∀ v < n, L v ≤ n)
    (hsm : ∀ v < n, c.nmem (13 * m + 4 * n + v) = sm v)
    (him : ∀ x ≤ m, c.nmem (12 * m + x) = im x) (h122 : c.nreg 122 = ∑ v ∈ range n, w v)
    (h123 : c.nreg 123 = l₁) (h125 : c.nreg 125 = j) (h126 : c.nreg 126 = j')
    (h131 : c.nreg 131 = fl) (hl₁ : l₁ ≤ n) (hj : j ≤ n) (hj' : j' ≤ n)
    (hz : ∀ i < 4, c.nmem (13 * m + 10 * n + 4 + i) = 0) :
    ∃ c' k, Exec P W outPhase c c' k ∧ k ≤ 54 * n + 88 ∧
      c'.output = c.output ++ outList n (∑ v ∈ range n, w v) w
        (fun v => labN l₁ j j' fl (L v) (sm v) (im (ofs v))) := by
  generalize hlab : (fun v => labN l₁ j j' fl (L v) (sm v) (im (ofs v))) = lab
  have hlab4 : ∀ v, lab v ≤ 4 := fun v => by
    rw [← hlab]; simp only; unfold labN; split_ifs <;> omega
  obtain ⟨c₁, k₁, e₁, hk₁, ho₁, hr₁, hf₁, hl₁', hp₁⟩ := labLoop_exec hN hIn hW L sm im l₁ j j' fl c
    hc hL hLm hLn hsm him h123 h125 h126 h131 hl₁ hj hj' hz
  have hlab' : ∀ v, labN l₁ j j' fl (L v) (sm v) (im (ofs v)) = lab v := fun v => by rw [← hlab]
  simp only [hlab'] at hl₁' hp₁
  have hL₁ : Lay n m c₁ := hL.of fun r h _ => hr₁ r h
  obtain ⟨c₂, k₂, e₂, hk₂, ho₂, hr₂, hf₂, hg₂⟩ := grpLoop_exec hW (w := w)
    (fun i => ∑ v ∈ range n with lab v = i, w v) (∑ v ∈ range n, w v) c₁ e₁.wb_right hL₁ hp₁
    (by rw [hr₁ 122 (by omega), h122]) le_rfl (sum_pieces_le w lab n hlab4)
  have hL₂ : Lay n m c₂ := hL₁.of fun r h _ => hr₂ r h
  obtain ⟨c₃, k₃, e₃, hk₃, ho₃, -, -⟩ := prLoop_exec hW (w := w) lab _ c₂ e₂.wb_right hL₂
    (fun v hv => by rw [hf₂ _ (by omega)]; exact hl₁' v hv) (fun v _ => hlab4 v) hg₂
  exact ⟨c₃, k₁ + (k₂ + k₃), .seq e₁ (.seq e₂ e₃), by omega, by rw [ho₃, ho₂, ho₁]; rfl⟩

end loops

end SepProg

end PlanarSeparator
