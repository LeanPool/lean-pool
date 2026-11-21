/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.FaceRep

/-!
# The separator program: the stellar subdivision in memory

The cycle search (`PlanarSeparator/Machine/CycleRun.lean`) works on a triangulated map whose
darts are numbered face by face. For the stellar subdivision of the input map, the face of the
stellar subdivision with corners `old x → up (φ x) → down x` gets the numbers `3x, 3x + 1,
3x + 2`. This file writes the arrays the search reads:

* `vloop`, over the vertices `v`: the tree marks `T (3 x) = 1` of the parent dart `x` of every
  vertex `v ≠ 0` and of its reversal, and the face weight `Fw (ofs v) = w v` for the vertices
  `v` of the middle levels (the face of the first dart `ofs v` of `v` carries the weight of `v`);
* `dloop`, over the darts `x`: the reversals `A (3x) = 3 rv x`, `A (3x + 1) = 3 φ x + 2`,
  `A (3 φ x + 2) = 3x + 1`, and the tree marks `T (3x + 2) = 1` when `x` represents its face,
  `T (3x + 1) = 1` when `φ x` does.
-/

@[expose] public section

namespace PlanarSeparator

namespace SepProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The programs -/

/-- `[a < b]` by truncated subtraction. -/
def ind (a b : ℕ) : ℕ := 1 - (1 - (b - a))

theorem ind_eq (a b : ℕ) : ind a b = if a < b then 1 else 0 := by
  unfold ind; split_ifs <;> omega

/-- The tree marks of the parent dart of `r93 = v ≥ 1` and of its reversal. -/
def tBodyV : Stmt := block [.addN 69 113 93, .loadN 94 69, .addN 70 94 94, .addN 70 70 94,
  .addN 70 70 108, .storeN 70 101, .addN 70 94 94, .addN 70 70 94, .addN 70 70 107,
  .addN 70 70 101, .readIn 95 70, .addN 70 95 95, .addN 70 70 95, .addN 70 70 108, .storeN 70 101,
  .addN 93 93 101]

/-- **The tree marks of the graph tree.** -/
def tloop : Stmt := .seq (.instr (.copyN 93 101)) (.whileLtN 93 104 tBodyV)

/-- The face weight `w v [l₁ < L v + j] [L v < l₁ + 1 + j']` of the first dart of `r93 = v`. -/
def wBodyV : Stmt := block [.addN 69 112 93, .loadN 96 69, .addN 97 96 125, .subN 97 97 123,
  .subN 97 101 97, .subN 97 101 97, .addN 98 123 101, .addN 98 98 126, .subN 98 98 96,
  .subN 98 101 98, .subN 98 101 98, .addN 70 106 93, .readIn 94 70, .mulN 94 94 97,
  .mulN 94 94 98, .addN 70 102 93, .readIn 99 70, .addN 70 109 99, .storeN 70 94, .addN 93 93 101]

/-- **The face weights.** -/
def wloop : Stmt := .seq (.instr (.copyN 93 100)) (.whileLtN 93 104 wBodyV)

/-- One dart `r93 = x`: the reversals of the three darts of its stellar face and the tree marks
of the two spokes. -/
def dBody : Stmt := block [.addN 70 93 93, .addN 70 70 93, .addN 70 70 107, .addN 70 70 101,
  .readIn 94 70, .addN 70 94 94, .addN 70 70 94, .addN 70 70 107, .addN 70 70 102, .readIn 95 70,
  .addN 69 110 93, .loadN 72 69, .addN 69 110 95, .loadN 73 69,
  .addN 96 93 93, .addN 96 96 93, .addN 97 94 94, .addN 97 97 94, .storeN 96 97,
  .addN 98 95 95, .addN 98 98 95, .addN 98 98 102, .addN 99 96 101, .storeN 99 98, .storeN 98 99,
  .subN 71 72 93, .subN 71 101 71, .subN 71 101 71, .addN 69 108 96, .addN 69 69 102,
  .storeN 69 71, .subN 71 73 95, .subN 71 101 71, .subN 71 101 71, .addN 69 108 96,
  .addN 69 69 101, .storeN 69 71, .addN 93 93 101]

/-- **The reversals and the tree marks of the spokes.** -/
def dloop : Stmt := .seq (.instr (.copyN 93 100)) (.whileLtN 93 105 dBody)

section proofs

variable {n m : ℕ} {ofs w tl rv ro : ℕ → ℕ} {W : ℕ} {P : Input}
  (hN : NWf n m ofs tl rv ro) (hIn : InHolds P n m ofs w tl rv ro)
  (hW : memTop n m + 3 * ∑ v ∈ range n, w v + 2 * n + 3 * m + 10 ≤ W)
include hN hIn hW

/-- **The tree marks of the graph tree.** -/
theorem tloop_exec (pr : ℕ → ℕ) (hpr : ∀ v, 1 ≤ v → v < n → pr v < m) (c : Config)
    (hc : WordsBounded W c) (hL : Lay n m c)
    (hprm : ∀ v, 1 ≤ v → v < n → c.nmem (13 * m + n + v) = pr v) :
    ∃ c' k, Exec P W tloop c c' k ∧ k ≤ 18 * n + 3 ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, ¬ (3 * m ≤ a ∧ a < 6 * m ∧ a % 3 = 0) → c'.nmem a = c.nmem a) ∧
      (∀ v, 1 ≤ v → v < n →
        c'.nmem (3 * m + 3 * pr v) = 1 ∧ c'.nmem (3 * m + 3 * rv (pr v)) = 1) ∧
      (∀ x < m, (∀ v, 1 ≤ v → v < n → x ≠ pr v ∧ x ≠ rv (pr v)) →
        c'.nmem (3 * m + 3 * x) = c.nmem (3 * m + 3 * x)) := by
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  have e₁ := Exec.copyN (P := P) hc 93 101
  rcases Nat.lt_or_ge n 1 with hn | hn
  · -- no vertex
    refine ⟨_, 1 + 2, .seq e₁ (.whileLtN_false (by simp only [upd_apply]; simp; omega) e₁.wb_right),
      by omega, rfl, fun r hr => by simp only [upd_apply]; split_ifs <;> omega,
      fun a _ => rfl, fun v h1 h2 => by omega, fun x _ _ => rfl⟩
  obtain ⟨c', k', e', ⟨-, hw', ho', hr', h93', hT1, hT2, hT3⟩, hk'⟩ :=
    Exec.forN (P := P) (W := W) (ri := 93) (rN := 104) (N := n) (lo := 1) (B := 16)
    (body := tBodyV) (fun i c' => 1 ≤ i ∧ WordsBounded W c' ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nreg 93 = i ∧
      (∀ v, 1 ≤ v → v < i → c'.nmem (3 * m + 3 * pr v) = 1 ∧ c'.nmem (3 * m + 3 * rv (pr v)) = 1) ∧
      (∀ x < m, (∀ v, 1 ≤ v → v < i → x ≠ pr v ∧ x ≠ rv (pr v)) →
        c'.nmem (3 * m + 3 * x) = c.nmem (3 * m + 3 * x)) ∧
      (∀ a, ¬ (3 * m ≤ a ∧ a < 6 * m ∧ a % 3 = 0) → c'.nmem a = c.nmem a))
    (fun i c' h => ⟨h.2.1, h.2.2.2.2.1, by rw [h.2.2.2.1 104 (by omega), a4]⟩)
    (fun i c' h hi => by
      obtain ⟨hi1, hw, ho, hr, h93, hT1, hT2, hT3⟩ := h
      have g108 : c'.nreg 108 = 3 * m := by rw [hr 108 (by omega), a8]
      have g107 : c'.nreg 107 = 2 * n + 3 := by rw [hr 107 (by omega), a7]
      have g113 : c'.nreg 113 = 13 * m + n := by rw [hr 113 (by omega), a13]
      have g101 : c'.nreg 101 = 1 := by rw [hr 101 (by omega), a1]
      have hpi := hpr i hi1 hi
      have hrv := hN.rv_lt _ hpi
      have r1 : c'.nmem (c'.nreg 113 + c'.nreg 93) = pr i := by
        rw [g113, h93, hT3 _ (by omega)]; exact hprm i hi1 hi
      have r2 : P.data.getD (pr i + pr i + pr i + c'.nreg 107 + c'.nreg 101) 0 = rv (pr i) := by
        rw [g107, g101, show pr i + pr i + pr i + (2 * n + 3) + 1 =
          2 * n + 3 + 3 * pr i + 1 by omega]
        exact hIn.rv_eq _ hpi
      unfold tBodyV
      exec_block
      all_goals try (config_simp; (try simp only [r1, r2]); omega)
      rw [r1] at *
      rw [r2] at *
      refine ⟨⟨hi1.trans (Nat.le_succ i), ‹_›, by config_simp; exact ho, fun r hr' => by
        config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
        by config_simp; omega, fun v h1 h2 => ?_, fun x hx hv => ?_, fun a ha => ?_⟩, by omega⟩
      · config_simp; simp only [upd_apply, g108, g101]
        rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
        · obtain ⟨t1, t2⟩ := hT1 v h1 h2
          constructor <;> split_ifs <;> first | rfl | assumption
        · constructor <;> split_ifs <;> first | rfl | omega
      · config_simp; simp only [upd_apply, g108, g101]
        have := hv i hi1 (by omega)
        split_ifs <;> first | omega | exact hT2 x hx fun v h1 h2 => hv v h1 (by omega)
      · config_simp; simp only [upd_apply, g108]
        split_ifs <;> first | omega | exact hT3 a ha)
    hn ⟨le_rfl, e₁.wb_right, rfl, fun r hr => by
      simp only [upd_apply]; split_ifs <;> omega,
      by simp only [upd_apply, ↓reduceIte]; exact a1, fun v h1 h2 => by omega,
      fun x _ _ => rfl, fun a _ => rfl⟩
  refine ⟨c', 1 + k', .seq e₁ e', by omega, ho', hr', hT3, hT1, hT2⟩


/-- **The face weights.** -/
theorem wloop_exec (L : ℕ → ℕ) (l₁ j j' : ℕ) (hofs : ∀ v < n, ofs v < ofs (v + 1)) (c : Config)
    (hc : WordsBounded W c) (hL : Lay n m c) (hLm : ∀ v < n, c.nmem (13 * m + v) = L v)
    (hLn : ∀ v < n, L v ≤ n) (h123 : c.nreg 123 = l₁) (h125 : c.nreg 125 = j)
    (h126 : c.nreg 126 = j') (hl₁ : l₁ ≤ n) (hj : j ≤ n) (hj' : j' ≤ n) :
    ∃ c' k, Exec P W wloop c c' k ∧ k ≤ 22 * n + 3 ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, ¬ (6 * m ≤ a ∧ a < 7 * m) → c'.nmem a = c.nmem a) ∧
      (∀ v < n, c'.nmem (6 * m + ofs v) = w v * ind l₁ (L v + j) * ind (L v) (l₁ + 1 + j')) ∧
      (∀ x < m, (∀ v < n, ofs v ≠ x) → c'.nmem (6 * m + x) = c.nmem (6 * m + x)) := by
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  have hofm : ∀ v < n, ofs v < m := fun v hv => lt_of_lt_of_le (hofs v hv) (hN.ofs_le_m hv)
  have hofi : ∀ u < n, ∀ v < n, ofs u = ofs v → u = v := by
    intro u hu v hv e
    by_contra hne
    rcases Nat.lt_or_gt_of_ne hne with h | h
    · have := hN.ofs_mono (u + 1) v h hv.le; have := hofs u hu; omega
    · have := hN.ofs_mono (v + 1) u h hu.le; have := hofs v hv; omega
  have hwle : ∀ v < n, w v ≤ ∑ i ∈ range n, w i := fun v hv =>
    single_le_sum (f := w) (fun _ _ => Nat.zero_le _) (mem_range.2 hv)
  have hmul1 : ∀ a b : ℕ, b ≤ 1 → a * b ≤ a := fun a b hb => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl <;> simp
  have hmul2 : ∀ a b c : ℕ, b ≤ 1 → c ≤ 1 → a * b * c ≤ a := fun a b c hb hc => by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hb with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hc with rfl | rfl <;> simp
  have e₁ := Exec.copyN (P := P) hc 93 100
  obtain ⟨c', k', e', ⟨hw', ho', hr', h93', hW1, hW2, hW3⟩, hk'⟩ :=
    Exec.forN (P := P) (W := W) (ri := 93) (rN := 104) (N := n) (lo := 0) (B := 20)
    (body := wBodyV) (fun i c' => WordsBounded W c' ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nreg 93 = i ∧
      (∀ v < i, c'.nmem (6 * m + ofs v) = w v * ind l₁ (L v + j) * ind (L v) (l₁ + 1 + j')) ∧
      (∀ x < m, (∀ v < i, ofs v ≠ x) → c'.nmem (6 * m + x) = c.nmem (6 * m + x)) ∧
      (∀ a, ¬ (6 * m ≤ a ∧ a < 7 * m) → c'.nmem a = c.nmem a))
    (fun i c' h => ⟨h.1, h.2.2.2.1, by rw [h.2.2.1 104 (by omega), a4]⟩)
    (fun i c' h hi => by
      obtain ⟨hw, ho, hr, h93, hW1, hW2, hW3⟩ := h
      have g109 : c'.nreg 109 = 6 * m := by rw [hr 109 (by omega), a9]
      have g112 : c'.nreg 112 = 13 * m := by rw [hr 112 (by omega), a12]
      have g101 : c'.nreg 101 = 1 := by rw [hr 101 (by omega), a1]
      have g102 : c'.nreg 102 = 2 := by rw [hr 102 (by omega), a2]
      have g106 : c'.nreg 106 = n + 3 := by rw [hr 106 (by omega), a6]
      have g123 : c'.nreg 123 = l₁ := by rw [hr 123 (by omega), h123]
      have g125 : c'.nreg 125 = j := by rw [hr 125 (by omega), h125]
      have g126 : c'.nreg 126 = j' := by rw [hr 126 (by omega), h126]
      have hLi := hLn i hi
      have r1 : c'.nmem (c'.nreg 112 + c'.nreg 93) = L i := by
        rw [g112, h93, hW3 _ (by omega)]; exact hLm i hi
      have r2 : P.data.getD (c'.nreg 106 + c'.nreg 93) 0 = w i := by
        rw [g106, h93]; exact hIn.w_eq i hi
      have r3 : P.data.getD (c'.nreg 102 + c'.nreg 93) 0 = ofs i := by
        rw [g102, h93]; exact hIn.ofs_eq i hi.le
      have hwi := hwle i hi
      have hofi' := hofm i hi
      unfold wBodyV
      exec_block
      all_goals try (config_simp; (try simp only [r1, r2, r3]); omega)
      · config_simp; rw [r1, r2, g101, g123, g125]
        have := hmul1 (w i) (1 - (1 - (L i + j - l₁))) (by omega); omega
      · config_simp; rw [r1, r2, g101, g123, g125, g126]
        have := hmul2 (w i) (1 - (1 - (L i + j - l₁))) (1 - (1 - (l₁ + 1 + j' - L i)))
          (by omega) (by omega)
        omega
      rw [r1] at *
      rw [r2] at *
      rw [r3] at *
      refine ⟨⟨‹_›, by config_simp; exact ho, fun r hr' => by
        config_simp; simp only [upd_apply]; split_ifs <;> first | omega | exact hr r hr',
        by config_simp; omega, fun v hv => ?_, fun x hx hv => ?_, fun a ha => ?_⟩, by omega⟩
      · config_simp; simp only [upd_apply, g109, g101, g123, g125, g126]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hv with hv | rfl
        · have := hofi v (by omega) i hi
          rw [ite_eq_right (by omega)]; exact hW1 v hv
        · rw [ite_eq_left rfl]; simp only [ind]
      · config_simp; simp only [upd_apply, g109]
        rw [ite_eq_right (by have := hv i (by omega); omega)]
        exact hW2 x hx fun v hv' => hv v (by omega)
      · config_simp; simp only [upd_apply, g109]
        rw [ite_eq_right (by omega)]; exact hW3 a ha)
    (Nat.zero_le n) ⟨e₁.wb_right, rfl, fun r hr => by
      simp only [upd_apply]; split_ifs <;> omega,
      by simp only [upd_apply, ↓reduceIte]; exact a0, fun v hv => by omega,
      fun x _ _ => rfl, fun a _ => rfl⟩
  refine ⟨c', 1 + k', .seq e₁ e', by omega, ho', hr', hW3, hW1, hW2⟩


/-- The facts written by `dloop` for the dart `x`. -/
def DFacts (m : ℕ) (rv ro fr : ℕ → ℕ) (mem : ℕ → ℕ) (x : ℕ) : Prop :=
  mem (3 * x) = 3 * rv x ∧ mem (3 * x + 1) = 3 * ph rv ro x + 2 ∧
    mem (3 * ph rv ro x + 2) = 3 * x + 1 ∧ mem (3 * m + 3 * x + 2) = ind x (fr x) ∧
    mem (3 * m + 3 * x + 1) = ind (ph rv ro x) (fr (ph rv ro x))

/-- The five stores performed by one dart iteration, in program order. -/
private def writeDart (m : ℕ) (rv ro fr mem : ℕ → ℕ) (i : ℕ) : ℕ → ℕ :=
  upd (upd (upd (upd (upd mem
    (3 * i) (3 * rv i)) (3 * i + 1) (3 * ph rv ro i + 2))
    (3 * ph rv ro i + 2) (3 * i + 1)) (3 * m + 3 * i + 2) (ind i (fr i)))
    (3 * m + 3 * i + 1) (ind (ph rv ro i) (fr (ph rv ro i)))

omit hN hIn hW in
private theorem writeDart_current {rv ro fr mem : ℕ → ℕ} {i m : ℕ}
    (hφ : ph rv ro i < m) :
    DFacts m rv ro fr (writeDart m rv ro fr mem i) i := by
  unfold DFacts writeDart
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [upd_apply] <;> split_ifs <;> omega

omit hN hIn hW in
private theorem writeDart_previous {rv ro fr mem : ℕ → ℕ} {x i m : ℕ}
    (hx : x < i) (hi : i < m) (hφx : ph rv ro x < m) (hφi : ph rv ro i < m)
    (hne : ph rv ro x ≠ ph rv ro i) (previous : DFacts m rv ro fr mem x) :
    DFacts m rv ro fr (writeDart m rv ro fr mem i) x := by
  obtain ⟨d₁, d₂, d₃, d₄, d₅⟩ := previous
  unfold DFacts writeDart
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [upd_apply] <;> split_ifs <;> omega

omit hN hIn hW in
private theorem writeDart_frame {rv ro fr mem : ℕ → ℕ} {a i m : ℕ}
    (hi : i < m) (hφ : ph rv ro i < m) (ha : 6 * m ≤ a ∨ (3 * m ≤ a ∧ a % 3 = 0)) :
    writeDart m rv ro fr mem i a = mem a := by
  simp only [writeDart, upd_apply]
  split_ifs <;> omega

private theorem dBody_exec (fr : ℕ → ℕ) (i : ℕ) (hi : i < m) (c : Config)
    (hc : WordsBounded W c) (h93 : c.nreg 93 = i)
    (g101 : c.nreg 101 = 1) (g102 : c.nreg 102 = 2) (g107 : c.nreg 107 = 2 * n + 3)
    (g108 : c.nreg 108 = 3 * m) (g110 : c.nreg 110 = 11 * m)
    (hfrm : ∀ x < m, c.nmem (11 * m + x) = fr x) (hfrb : ∀ x < m, fr x ≤ m) :
    ∃ c' k, Exec P W dBody c c' k ∧ c'.output = c.output ∧ c'.nreg 93 = i + 1 ∧
      c'.nmem = writeDart m rv ro fr c.nmem i ∧ k ≤ 38 := by
  have hW' := hW
  unfold memTop at hW'
  have hrv := hN.rv_lt i hi
  have hph := hN.ph_lt hi
  have r1 : P.data.getD (c.nreg 93 + c.nreg 93 + c.nreg 93 + c.nreg 107 + c.nreg 101) 0 =
      rv i := by
    rw [h93, g107, g101, show i + i + i + (2 * n + 3) + 1 = 2 * n + 3 + 3 * i + 1 by omega]
    exact hIn.rv_eq _ hi
  have r2 : P.data.getD (rv i + rv i + rv i + c.nreg 107 + c.nreg 102) 0 = ph rv ro i := by
    rw [g107, g102, show rv i + rv i + rv i + (2 * n + 3) + 2 =
      2 * n + 3 + 3 * rv i + 2 by omega]
    exact hIn.ro_eq _ hrv
  have r3 : c.nmem (c.nreg 110 + c.nreg 93) = fr i := by
    rw [g110, h93]; exact hfrm i hi
  have r4 : c.nmem (c.nreg 110 + ph rv ro i) = fr (ph rv ro i) := by
    rw [g110]; exact hfrm _ hph
  have hf1 := hfrb i hi
  have hf2 := hfrb _ hph
  unfold dBody
  exec_block
  all_goals try (config_simp; (try simp only [r1, r2, r3, r4]); omega)
  refine ⟨by config_simp, by config_simp; omega, ?_, by omega⟩
  have threeTimes (value : ℕ) : 3 * value = value + value + value := by omega
  config_simp
  simp only [r1, r2, r3, r4]
  simp only [h93, g108, g101, g102, writeDart, ind, threeTimes]

/-- **The reversals and the tree marks of the spokes.** -/
theorem dloop_exec (fr : ℕ → ℕ) (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (hfrm : ∀ x < m, c.nmem (11 * m + x) = fr x) (hfrb : ∀ x < m, fr x ≤ m) :
    ∃ c' k, Exec P W dloop c c' k ∧ k ≤ 40 * m + 3 ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧
      (∀ a, (6 * m ≤ a ∨ (3 * m ≤ a ∧ a % 3 = 0)) → c'.nmem a = c.nmem a) ∧
      (∀ x < m, DFacts m rv ro fr c'.nmem x) := by
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  have e₁ := Exec.copyN (P := P) hc 93 100
  obtain ⟨c', k', e', ⟨hw', ho', hr', h93', hD, hfr'⟩, hk'⟩ :=
    Exec.forN (P := P) (W := W) (ri := 93) (rN := 105) (N := m) (lo := 0) (B := 38)
    (body := dBody) (fun i c' => WordsBounded W c' ∧ c'.output = c.output ∧
      (∀ r, 100 ≤ r → c'.nreg r = c.nreg r) ∧ c'.nreg 93 = i ∧
      (∀ x < i, DFacts m rv ro fr c'.nmem x) ∧
      (∀ a, (6 * m ≤ a ∨ (3 * m ≤ a ∧ a % 3 = 0)) → c'.nmem a = c.nmem a))
    (fun i c' h => ⟨h.1, h.2.2.2.1, by rw [h.2.2.1 105 (by omega), a5]⟩)
    (fun i c' h hi => by
      obtain ⟨hw, ho, hr, h93, hD, hfr⟩ := h
      have g101 : c'.nreg 101 = 1 := by rw [hr 101 (by omega), a1]
      have g102 : c'.nreg 102 = 2 := by rw [hr 102 (by omega), a2]
      have g107 : c'.nreg 107 = 2 * n + 3 := by rw [hr 107 (by omega), a7]
      have g108 : c'.nreg 108 = 3 * m := by rw [hr 108 (by omega), a8]
      have g110 : c'.nreg 110 = 11 * m := by rw [hr 110 (by omega), a10]
      have hfrm' (x : ℕ) (hx : x < m) : c'.nmem (11 * m + x) = fr x := by
        rw [hfr _ (Or.inl (by omega))]
        exact hfrm x hx
      obtain ⟨c'', k, e, ho'', h93'', hmem, hk⟩ :=
        dBody_exec hN hIn hW fr i hi c' hw h93 g101 g102 g107 g108 g110 hfrm' hfrb
      have hwm : dBody.wmax = 99 := by decide
      refine ⟨c'', k, e, ⟨e.wb_right, ho''.trans ho, fun r hr' => by
        rw [e.nreg_of_wr (Stmt.wr_of_wmax (by omega))]; exact hr r hr',
        h93'', ?_, ?_⟩, hk⟩
      · intro x hx
        rw [hmem]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hx with hx | rfl
        · exact writeDart_previous hx hi (hN.ph_lt (hx.trans hi)) (hN.ph_lt hi)
            (fun e => (Nat.ne_of_lt hx) (hN.ph_inj (hx.trans hi) hi e)) (hD x hx)
        · exact writeDart_current (hN.ph_lt hi)
      · intro a ha
        rw [hmem, writeDart_frame hi (hN.ph_lt hi) ha]
        exact hfr a ha)
    (Nat.zero_le m) ⟨e₁.wb_right, rfl, fun r hr => by
      simp only [upd_apply]; split_ifs <;> omega,
      by simp only [upd_apply, ↓reduceIte]; exact a0, fun x hx => by omega, fun a _ => rfl⟩
  refine ⟨c', 1 + k', .seq e₁ e', by omega, ho', hr', hfr', hD⟩

end proofs

end SepProg

end PlanarSeparator
