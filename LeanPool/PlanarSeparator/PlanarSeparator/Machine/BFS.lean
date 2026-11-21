/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Front

/-!
# The separator program: breadth-first search from vertex `0`

The search keeps a queue of vertices at `13 m + 3 n + i`, marks at `13 m + 2 n + v`, levels at
`13 m + v` and parent darts at `13 m + n + v` (the dart from `v` towards its parent; `m` for the
root). The darts leaving a vertex `u` are `ofs u ≤ d < ofs (u + 1)`, read from the input; the
head of `d` is `tl (rv d)`.

At the end (`bfs_exec`) every vertex in the queue has all its neighbours in the queue, the parent
dart of every queued vertex other than `0` leads one level down, and adjacent queued vertices are
at most one level apart, within `(B + 2) m + 18 n + 12` steps, `B = 30`.
-/

@[expose] public section

namespace PlanarSeparator

namespace SepProg

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The program -/

/-- Start: mark `0`, queue it, level `0`, parent dart `m`; `r63 = 0` is the head, `r64 = 1` the
tail of the queue. -/
def bStart : Stmt := block [.addN 69 114 100, .storeN 69 101, .storeN 115 100, .storeN 112 100,
  .storeN 113 105, .copyN 64 101, .copyN 63 100]

/-- Dequeue `r65 = u`; `r71 = lv u + 1`, `r66 = ofs u`, `r67 = ofs (u + 1)`. -/
def bDeq : Stmt := block [.addN 69 115 63, .loadN 65 69, .addN 63 63 101, .addN 69 112 65,
  .loadN 71 69, .addN 71 71 101, .addN 70 102 65, .readIn 66 70, .addN 70 70 101, .readIn 67 70]

/-- A new vertex `r68 = v` reached through the dart `r72 = rv d`. -/
def bNew : Stmt := block [.storeN 69 101, .addN 69 112 68, .storeN 69 71, .addN 69 113 68,
  .storeN 69 72, .addN 69 115 64, .storeN 69 68, .addN 64 64 101]

/-- The dart `r66 = d` of `u`. -/
def bVisit : Stmt :=
  .seq (block [.addN 70 66 66, .addN 70 70 66, .addN 70 70 107, .addN 70 70 101, .readIn 72 70,
    .addN 70 72 72, .addN 70 70 72, .addN 70 70 107, .readIn 68 70, .addN 69 114 68, .loadN 73 69])
  (.seq (.ifLtN 73 101 bNew .skip) (.instr (.addN 66 66 101)))

/-- One vertex of the search. -/
def bBody : Stmt := .seq bDeq (.whileLtN 66 67 bVisit)

/-- **Breadth-first search from vertex `0`.** -/
def bfs : Stmt := .seq bStart (.whileLtN 63 64 bBody)

/-! ### The invariants -/

/-- The level of `v`. -/
def lvA (m : ℕ) (mem : ℕ → ℕ) (v : ℕ) : ℕ := mem (13 * m + v)
/-- The parent dart of `v`. -/
def prA (n m : ℕ) (mem : ℕ → ℕ) (v : ℕ) : ℕ := mem (13 * m + n + v)
/-- The mark of `v`. -/
def mkA (n m : ℕ) (mem : ℕ → ℕ) (v : ℕ) : ℕ := mem (13 * m + 2 * n + v)
/-- The `i`-th vertex of the queue. -/
def qA (n m : ℕ) (mem : ℕ → ℕ) (i : ℕ) : ℕ := mem (13 * m + 3 * n + i)

section inv

variable (n m : ℕ) (ofs tl rv : ℕ → ℕ) (W : ℕ) (o : List ℕ) (c₀ : Config)

/-- All darts of `u` lead to marked vertices at most one level further. -/
def Closed (mem : ℕ → ℕ) (u : ℕ) : Prop :=
  ∀ d, ofs u ≤ d → d < ofs (u + 1) →
    mkA n m mem (tl (rv d)) = 1 ∧ lvA m mem (tl (rv d)) ≤ lvA m mem u + 1

/-- The state of the search. -/
structure BS (c : Config) : Prop where
  wb : WordsBounded W c
  lay : Lay n m c
  out : c.output = o
  frame : ∀ a, (a < 13 * m ∨ 13 * m + 4 * n ≤ a) → c.nmem a = c₀.nmem a
  head_le : c.nreg 63 ≤ c.nreg 64
  tail_le : c.nreg 64 ≤ n
  q_lt : ∀ i < c.nreg 64, qA n m c.nmem i < n
  q_inj : ∀ i < c.nreg 64, ∀ j < c.nreg 64, qA n m c.nmem i = qA n m c.nmem j → i = j
  q0 : 0 < c.nreg 64 ∧ qA n m c.nmem 0 = 0
  mk01 : ∀ v < n, mkA n m c.nmem v = 0 ∨ mkA n m c.nmem v = 1
  mk_iff : ∀ v < n, mkA n m c.nmem v = 1 ↔ ∃ i < c.nreg 64, qA n m c.nmem i = v
  lv0 : lvA m c.nmem 0 = 0
  par : ∀ i, 1 ≤ i → i < c.nreg 64 →
    prA n m c.nmem (qA n m c.nmem i) < m ∧ tl (prA n m c.nmem (qA n m c.nmem i)) = qA n m c.nmem i ∧
      lvA m c.nmem (tl (rv (prA n m c.nmem (qA n m c.nmem i)))) + 1 =
        lvA m c.nmem (qA n m c.nmem i) ∧
      ∃ i' < i, qA n m c.nmem i' = tl (rv (prA n m c.nmem (qA n m c.nmem i)))
  mono : ∀ i i',
    i ≤ i' → i' < c.nreg 64 → lvA m c.nmem (qA n m c.nmem i) ≤ lvA m c.nmem (qA n m c.nmem i')
  span : ∀ i' < c.nreg 64, 1 ≤ c.nreg 63 →
    lvA m c.nmem (qA n m c.nmem i') ≤ lvA m c.nmem (qA n m c.nmem (c.nreg 63 - 1)) + 1
  lv_le : ∀ i < c.nreg 64, lvA m c.nmem (qA n m c.nmem i) ≤ i
  t1 : c.nreg 63 = 0 → c.nreg 64 = 1

/-- Between two vertices. -/
structure IS (c : Config) : Prop extends BS n m tl rv W o c₀ c where
  closed : ∀ i < c.nreg 63, Closed n m ofs tl rv c.nmem (qA n m c.nmem i)

/-- While scanning the darts of `r65 = u`. -/
structure VS (c : Config) : Prop extends BS n m tl rv W o c₀ c where
  head_pos : 1 ≤ c.nreg 63
  cur : c.nreg 65 = qA n m c.nmem (c.nreg 63 - 1)
  r71 : c.nreg 71 = lvA m c.nmem (c.nreg 65) + 1
  r67 : c.nreg 67 = ofs (c.nreg 65 + 1)
  r66_ge : ofs (c.nreg 65) ≤ c.nreg 66
  r66_le : c.nreg 66 ≤ c.nreg 67
  closed : ∀ i, i + 1 < c.nreg 63 → Closed n m ofs tl rv c.nmem (qA n m c.nmem i)
  closed_cur : ∀ d, ofs (c.nreg 65) ≤ d → d < c.nreg 66 →
    mkA n m c.nmem (tl (rv d)) = 1 ∧ lvA m c.nmem (tl (rv d)) ≤ lvA m c.nmem (c.nreg 65) + 1

end inv

section proofs

variable {n m : ℕ} {ofs w tl rv ro : ℕ → ℕ} {W : ℕ} {o : List ℕ} {c₀ : Config} {P : Input}

theorem BS.tail_lt {c : Config} (hI : BS n m tl rv W o c₀ c) {v : ℕ} (hv : v < n)
    (hnot : ∀ i < c.nreg 64, qA n m c.nmem i ≠ v) : c.nreg 64 < n := by
  classical
  have h := Finset.card_le_card_of_injOn (qA n m c.nmem) (s := range (c.nreg 64))
    (t := (range n).erase v)
    (fun i hi => by
      simp only [coe_range, Set.mem_Iio] at hi
      simp only [coe_erase, coe_range, Set.mem_sdiff, Set.mem_Iio, Set.mem_singleton_iff]
      exact ⟨hI.q_lt i hi, hnot i hi⟩)
    (fun i hi j hj e => hI.q_inj i (by simpa using hi) j (by simpa using hj) e)
  rw [card_range, card_erase_of_mem (mem_range.2 hv), card_range] at h
  omega

/-- The frame of a step: the registers of the search and the layout are kept. -/
def KeepR (c c' : Config) (l : List ℕ) : Prop := ∀ r, (r ∈ l ∨ 100 ≤ r) → c'.nreg r = c.nreg r

/-- A dart leading to a vertex already marked: only `r66` advances. -/
theorem VS.next_skip {c c' : Config} (hJ : VS n m ofs tl rv W o c₀ c)
    (hd : c.nreg 66 < c.nreg 67)
    (hv : mkA n m c.nmem (tl (rv (c.nreg 66))) = 1 ∧
      lvA m c.nmem (tl (rv (c.nreg 66))) ≤ lvA m c.nmem (c.nreg 65) + 1)
    (hwb : WordsBounded W c') (hK : KeepR c c' [63, 64, 65, 67, 71])
    (h66 : c'.nreg 66 = c.nreg 66 + 1) (hout : c'.output = c.output) (hmem : c'.nmem = c.nmem) :
    VS n m ofs tl rv W o c₀ c' := by
  have g63 := hK 63 (by simp); have g64 := hK 64 (by simp); have g65 := hK 65 (by simp)
  have g67 := hK 67 (by simp); have g71 := hK 71 (by simp)
  have hl := hJ.lay.of fun r h1 _ => hK r (Or.inr h1)
  obtain ⟨⟨_, _, ho, hfr, hhl, htl, hql, hqi, hq0, hm01, hmi, hl0, hpar, hmono, hspan, hlvle, ht1⟩,
    hhp, hcur, h71, h67, h66ge, h66le, hcl, hclc⟩ := hJ
  refine ⟨⟨hwb, hl, hout.trans ho, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_,
    ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [hmem, g63, g64, g65, g67, g71, h66]
  all_goals try first | assumption | omega
  · intro d h1 h2
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
    · exact hclc d h1 h2
    · exact hv

/-- A dart leading to a new vertex `v`: mark it, record its level and parent dart, queue it. -/
theorem VS.next_new (hN : NWf n m ofs tl rv ro) {c c' : Config} (hJ : VS n m ofs tl rv W o c₀ c)
    (hd : c.nreg 66 < c.nreg 67) (hv : mkA n m c.nmem (tl (rv (c.nreg 66))) = 0)
    (hwb : WordsBounded W c') (hK : KeepR c c' [63, 65, 67, 71])
    (h64 : c'.nreg 64 = c.nreg 64 + 1) (h66 : c'.nreg 66 = c.nreg 66 + 1)
    (hout : c'.output = c.output)
    (hmem : c'.nmem = upd (upd (upd (upd c.nmem (13 * m + 2 * n + tl (rv (c.nreg 66))) 1)
      (13 * m + tl (rv (c.nreg 66))) (lvA m c.nmem (c.nreg 65) + 1))
      (13 * m + n + tl (rv (c.nreg 66))) (rv (c.nreg 66)))
      (13 * m + 3 * n + c.nreg 64) (tl (rv (c.nreg 66)))) :
    VS n m ofs tl rv W o c₀ c' := by
  have g63 := hK 63 (by simp); have g65 := hK 65 (by simp)
  have g67 := hK 67 (by simp); have g71 := hK 71 (by simp)
  have hl := hJ.lay.of fun r h1 _ => hK r (Or.inr h1)
  have hhp := hJ.head_pos; have hhl := hJ.head_le; have htl := hJ.tail_le
  have hu := hJ.q_lt _ (show c.nreg 63 - 1 < c.nreg 64 by omega)
  rw [← hJ.cur] at hu
  have hdm : c.nreg 66 < m := by
    have := hN.ofs_le_m (v := c.nreg 65 + 1) (by omega); rw [hJ.r67] at hd; omega
  have hrv := hN.rv_lt _ hdm
  have htlv := hN.tl_lt _ hrv
  generalize hgv : tl (rv (c.nreg 66)) = v at hv hmem htlv
  have hnot : ∀ i < c.nreg 64, qA n m c.nmem i ≠ v := fun i hi e => by
    have := (hJ.mk_iff v htlv).2 ⟨i, hi, e⟩; omega
  have htl' := hJ.tail_lt htlv hnot
  have huv : c.nreg 65 ≠ v := by
    intro e; apply hnot (c.nreg 63 - 1) (by omega); rw [← hJ.cur, e]
  have hmk : ∀ x < n, mkA n m c'.nmem x = if x = v then 1 else mkA n m c.nmem x := fun x hx => by
    simp only [mkA, hmem, upd_apply]; split_ifs <;> omega
  have hlv : ∀ x < n, lvA m c'.nmem x = if x = v then lvA m c.nmem (c.nreg 65) + 1 else
      lvA m c.nmem x := fun x hx => by
    simp only [lvA, hmem, upd_apply]; split_ifs <;> omega
  have hpr : ∀ x < n, prA n m c'.nmem x = if x = v then rv (c.nreg 66) else prA n m c.nmem x :=
    fun x hx => by simp only [prA, hmem, upd_apply]; split_ifs <;> omega
  have hq : ∀ i < n, qA n m c'.nmem i = if i = c.nreg 64 then v else qA n m c.nmem i :=
    fun i hi => by simp only [qA, hmem, upd_apply]; split_ifs <;> omega
  have hq_lt : ∀ i < c.nreg 64, qA n m c'.nmem i = qA n m c.nmem i := fun i hi => by
    rw [hq i (by omega)]; simp [show i ≠ c.nreg 64 by omega]
  have hlv_q : ∀ i < c.nreg 64, lvA m c'.nmem (qA n m c.nmem i) = lvA m c.nmem (qA n m c.nmem i) :=
    fun i hi => by rw [hlv _ (hJ.q_lt i hi)]; simp [hnot i hi]
  have hlvu : lvA m c'.nmem (c.nreg 65) = lvA m c.nmem (c.nreg 65) := by
    rw [hlv _ hu]; simp [huv]
  have hmk_ge : ∀ x < n, mkA n m c.nmem x = 1 → mkA n m c'.nmem x = 1 := fun x hx h => by
    rw [hmk x hx]; split_ifs <;> simp [h]
  have hlv_m : ∀ x < n, mkA n m c.nmem x = 1 → lvA m c'.nmem x = lvA m c.nmem x := fun x hx h => by
    rw [hlv x hx]; split_ifs with e
    · subst e; rw [hv] at h; exact absurd h (by omega)
    · rfl
  have hvl : lvA m c'.nmem v = lvA m c.nmem (c.nreg 65) + 1 := by rw [hlv v htlv]; simp
  have hspan := hJ.span
  have hcurq : qA n m c.nmem (c.nreg 63 - 1) = c.nreg 65 := hJ.cur.symm
  refine ⟨⟨hwb, hl, hout.trans hJ.out, fun a ha => ?_, by rw [h64, g63]; omega,
    by rw [h64]; omega, fun i hi => ?_, fun i hi j hj e => ?_, ?_, fun x hx => ?_,
    fun x hx => ?_, ?_, fun i hi1 hi2 => ?_, fun i i' hii hi' => ?_, fun i' hi' h1 => ?_,
    fun i hi => ?_, fun h => absurd h (by rw [g63]; omega)⟩, by rw [g63]; exact hhp, ?_, ?_, ?_,
    ?_, ?_, fun i hi => ?_, fun d h1 h2 => ?_⟩
  · rw [hmem, ← hJ.frame a ha]; simp only [upd_apply]; split_ifs <;> omega
  · rw [h64] at hi; rw [hq i (by omega)]; split_ifs
    · exact htlv
    · exact hJ.q_lt i (by omega)
  · rw [h64] at hi hj
    rw [hq i (by omega), hq j (by omega)] at e
    split_ifs at e with e1 e2 e2
    · omega
    · exact absurd e.symm (hnot j (by omega))
    · exact absurd e (hnot i (by omega))
    · exact hJ.q_inj i (by omega) j (by omega) e
  · rw [h64]; refine ⟨by omega, ?_⟩; rw [hq_lt 0 hJ.q0.1]; exact hJ.q0.2
  · rw [hmk x hx]; split_ifs
    · right; rfl
    · exact hJ.mk01 x hx
  · rw [hmk x hx, h64]
    split_ifs with hxv
    · subst hxv; simp only [true_iff]; exact ⟨c.nreg 64, by omega, by rw [hq _ htl']; simp⟩
    · rw [hJ.mk_iff x hx]
      constructor
      · rintro ⟨i, hi, e⟩; exact ⟨i, by omega, by rw [hq_lt i hi]; exact e⟩
      · rintro ⟨i, hi, e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, by rw [← hq_lt i hi]; exact e⟩
        · rw [hq _ htl'] at e; simp at e; exact absurd e.symm hxv
  · have h0 := hJ.q0
    rw [← h0.2, ← hq_lt 0 h0.1, hq_lt 0 h0.1, hlv_q 0 h0.1, h0.2]; exact hJ.lv0
  · rw [h64] at hi2
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi2 with hi2 | rfl
    · rw [hq_lt i hi2, hpr _ (hJ.q_lt i hi2)]
      simp only [hnot i hi2, ↓reduceIte]
      obtain ⟨p1, p2, p3, i', hi', p4⟩ := hJ.par i hi1 hi2
      have hpi : tl (rv (prA n m c.nmem (qA n m c.nmem i))) < n := hN.tl_lt _ (hN.rv_lt _ p1)
      refine ⟨p1, p2, ?_, i', hi', by rw [hq_lt i' (by omega), p4]⟩
      rw [← p4, hlv_q i' (by omega), hlv_q i hi2, p4, p3]
    · simp only [hq _ htl', ↓reduceIte]; rw [hpr _ htlv]; simp only [↓reduceIte]
      have hdu := (hN.blk _ hdm _ hu).2 ⟨hJ.r66_ge, by rw [← hJ.r67]; exact hd⟩
      refine ⟨hrv, ?_, ?_, c.nreg 63 - 1, by omega, ?_⟩
      · exact hgv
      · rw [hN.rv_rv _ hdm, hdu, hvl, hlvu]
      · rw [hq_lt _ (by omega), hcurq, hN.rv_rv _ hdm, hdu]
  · rw [h64] at hi'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
    · rw [hq_lt i (by omega), hq_lt i' hi', hlv_q i (by omega), hlv_q i' hi']
      exact hJ.mono i i' hii hi'
    · rw [hq _ htl', ite_eq_left rfl, hvl]
      rcases Nat.lt_or_ge i (c.nreg 64) with h | h
      · rw [hq_lt i h, hlv_q i h, ← hcurq]
        exact hspan i h hhp
      · rw [show i = c.nreg 64 by omega, hq _ htl', ite_eq_left rfl, hvl]
  · have e1 : qA n m c'.nmem (c'.nreg 63 - 1) = c.nreg 65 := by
      rw [g63, hq_lt _ (by omega), hcurq]
    rw [e1, hlvu]
    rw [h64] at hi'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with hi' | rfl
    · rw [hq_lt i' hi', hlv_q i' hi', ← hcurq]; exact hspan i' hi' hhp
    · rw [hq _ htl', ite_eq_left rfl, hvl]
  · rw [h64] at hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · rw [hq_lt i hi, hlv_q i hi]; exact hJ.lv_le i hi
    · rw [hq _ htl', ite_eq_left rfl, hvl]
      have := hJ.lv_le (c.nreg 63 - 1) (by omega)
      rw [hcurq] at this
      omega
  · rw [g65, g63, hq_lt _ (by omega)]; exact hJ.cur
  · rw [g71, g65, hlvu]; exact hJ.r71
  · rw [g67, g65]; exact hJ.r67
  · rw [h66, g65]; have := hJ.r66_ge; omega
  · rw [h66, g67]; omega
  · rw [g63] at hi
    rw [hq_lt i (by omega)]
    intro d h1 h2
    have hqi := hJ.q_lt i (by omega)
    obtain ⟨e1, e2⟩ := hJ.closed i hi d h1 h2
    have hdm' : d < m := by have := hN.ofs_le_m (v := qA n m c.nmem i + 1) (by omega); omega
    have hx := hN.tl_lt _ (hN.rv_lt _ hdm')
    refine ⟨hmk_ge _ hx e1, ?_⟩
    rw [hlv_m _ hx e1, hlv_q i (by omega)]; exact e2
  · rw [g65] at h1 ⊢
    rw [h66] at h2
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
    · obtain ⟨e1, e2⟩ := hJ.closed_cur d h1 h2
      have hdm' : d < m := by
        have := hN.ofs_le_m (v := c.nreg 65 + 1) (by omega); have := hJ.r66_le; rw [hJ.r67] at this
        omega
      have hx := hN.tl_lt _ (hN.rv_lt _ hdm')
      refine ⟨hmk_ge _ hx e1, ?_⟩
      rw [hlv_m _ hx e1, hlvu]; exact e2
    · rw [hgv, hmk v htlv, ite_eq_left rfl, hvl, hlvu]; exact ⟨rfl, le_rfl⟩

variable (hN : NWf n m ofs tl rv ro) (hIn : InHolds P n m ofs w tl rv ro)
  (hW : memTop n m + 2 * n + 3 * m + 10 ≤ W) (hPW : ∀ j, P.data.getD j 0 ≤ W)
include hN hIn hW hPW

omit hPW in
/-- One dart of the current vertex. -/
theorem visit_exec (c : Config) (hJ : VS n m ofs tl rv W o c₀ c) (hd : c.nreg 66 < c.nreg 67) :
    ∃ c' k, Exec P W bVisit c c' k ∧ VS n m ofs tl rv W o c₀ c' ∧ c'.nreg 66 = c.nreg 66 + 1 ∧
      c'.nreg 63 = c.nreg 63 ∧ c'.nreg 65 = c.nreg 65 ∧ c'.nreg 67 = c.nreg 67 ∧ k ≤ 24 ∧
      c.nreg 64 ≤ c'.nreg 64 ∧ (∀ i < c.nreg 64, qA n m c'.nmem i = qA n m c.nmem i) := by
  have hW' := hW; unfold memTop at hW'
  have hc := hJ.wb
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hJ.lay
  have hhp := hJ.head_pos
  have hhl := hJ.head_le
  have htl := hJ.tail_le
  have hu := hJ.q_lt _ (show c.nreg 63 - 1 < c.nreg 64 by omega)
  rw [← hJ.cur] at hu
  have hdm : c.nreg 66 < m := by
    have := hN.ofs_le_m (v := c.nreg 65 + 1) (by omega); rw [hJ.r67] at hd; omega
  have hrv := hN.rv_lt _ hdm
  have htlv := hN.tl_lt _ hrv
  have hr1 : P.data.getD (c.nreg 66 + c.nreg 66 + c.nreg 66 + c.nreg 107 + c.nreg 101) 0 =
      rv (c.nreg 66) := by
    rw [a7, a1, show c.nreg 66 + c.nreg 66 + c.nreg 66 + (2 * n + 3) + 1 =
      2 * n + 3 + 3 * c.nreg 66 + 1 by omega]
    exact hIn.rv_eq _ hdm
  have hr2 : P.data.getD (rv (c.nreg 66) + rv (c.nreg 66) + rv (c.nreg 66) + c.nreg 107) 0 =
      tl (rv (c.nreg 66)) := by
    rw [a7, show rv (c.nreg 66) + rv (c.nreg 66) + rv (c.nreg 66) + (2 * n + 3) =
      2 * n + 3 + 3 * rv (c.nreg 66) by omega]
    exact hIn.tl_eq _ hrv
  have hmv : c.nmem (c.nreg 114 + tl (rv (c.nreg 66))) = mkA n m c.nmem (tl (rv (c.nreg 66))) := by
    rw [a14]; rfl
  unfold bVisit
  refine spec_seq ?_
  exec_block
  all_goals try (config_simp; (try simp only [hr1, hr2]); omega)
  config_simp
  rw [hr1] at *
  rw [hr2] at *
  rw [hmv] at *
  refine spec_seq ?_
  rcases hJ.mk01 _ htlv with hv | hv
  · -- a new vertex
    refine spec_ifLtN_true (by config_simp; omega) ?_
    unfold bNew
    exec_block
    all_goals try (config_simp; omega)
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; omega)) fun hw => ?_
    refine ⟨hJ.next_new hN hd hv hw (fun r hr => ?_) ?_ ?_ rfl ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals config_simp
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [upd_apply]; split_ifs <;> omega
    · omega
    · omega
    · funext a; simp only [upd_apply, a1, a12, a13, a14, a15, hJ.r71]
    all_goals first | omega |
      (intro i hi; simp only [qA, upd_apply, a12, a13, a14, a15]; split_ifs <;> omega)
  · refine spec_ifLtN_false (by config_simp; omega) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; omega)) fun hw => ?_
    have hm1 := (hJ.mk_iff _ htlv).1 hv
    refine ⟨hJ.next_skip hd ⟨hv, ?_⟩ hw (fun r hr => ?_) ?_ rfl rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals config_simp
    · obtain ⟨i, hi, e⟩ := hm1
      have := hJ.span i hi hhp
      rw [e, ← hJ.cur] at this
      exact this
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      simp only [upd_apply]; split_ifs <;> omega
    all_goals first | omega | (intro i hi; trivial)

theorem deq_exec (c : Config) (hI : IS n m ofs tl rv W o c₀ c) (hlt : c.nreg 63 < c.nreg 64) :
    ∃ c' k, Exec P W bDeq c c' k ∧ VS n m ofs tl rv W o c₀ c' ∧ c'.nreg 66 = ofs (c'.nreg 65) ∧
      c'.nreg 63 = c.nreg 63 + 1 ∧ c'.nreg 64 = c.nreg 64 ∧ c'.nmem = c.nmem ∧
      c'.nreg 65 = qA n m c.nmem (c.nreg 63) ∧ k = 10 := by
  have hW' := hW; unfold memTop at hW'
  have hc := hI.wb
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hI.lay
  have htl := hI.tail_le
  have hu := hI.q_lt _ hlt
  have hq : c.nmem (c.nreg 115 + c.nreg 63) = qA n m c.nmem (c.nreg 63) := by rw [a15]; rfl
  have hl : c.nmem (c.nreg 112 + qA n m c.nmem (c.nreg 63)) =
      lvA m c.nmem (qA n m c.nmem (c.nreg 63)) := by rw [a12]; rfl
  have hlu := hI.lv_le _ hlt
  have ho1 : P.data.getD (c.nreg 102 + qA n m c.nmem (c.nreg 63)) 0 =
      ofs (qA n m c.nmem (c.nreg 63)) := by
    rw [a2]; exact hIn.ofs_eq _ (by omega)
  have ho2 : P.data.getD (c.nreg 102 + qA n m c.nmem (c.nreg 63) + c.nreg 101) 0 =
      ofs (qA n m c.nmem (c.nreg 63) + 1) := by
    rw [a2, a1, Nat.add_assoc]; exact hIn.ofs_eq _ (by omega)
  unfold bDeq
  exec_block
  all_goals try (config_simp; (try simp only [hq, hl]); first | exact hPW _ | omega)
  rw [hq] at *
  rw [hl] at *
  rw [ho1] at *
  rw [ho2] at *
  have hspan' : ∀ i' < c.nreg 64, lvA m c.nmem (qA n m c.nmem i') ≤
      lvA m c.nmem (qA n m c.nmem (c.nreg 63)) + 1 := by
    intro i' hi'
    rcases Nat.eq_zero_or_pos (c.nreg 63) with h0 | h0
    · have := hI.t1 h0
      obtain rfl : i' = 0 := by omega
      rw [h0]; omega
    · have := hI.span i' hi' h0
      have := hI.mono (c.nreg 63 - 1) (c.nreg 63) (by omega) hlt
      omega
  refine ⟨⟨⟨‹_›, hI.lay.of fun r h1 _ => by
      config_simp; simp only [upd_apply]; split_ifs <;> omega,
    hI.out, hI.frame, by config_simp; omega, hI.tail_le, hI.q_lt, hI.q_inj,
    hI.q0, hI.mk01, hI.mk_iff, hI.lv0, hI.par, hI.mono,
    fun i' hi' _ => by
      config_simp; rw [show c.nreg 63 + c.nreg 101 - 1 = c.nreg 63 by omega]
      exact hspan' i' hi',
    hI.lv_le, fun h => by config_simp at h; omega⟩, by config_simp; omega,
    by config_simp; rw [show c.nreg 63 + c.nreg 101 - 1 = c.nreg 63 by omega],
    by config_simp; omega, by config_simp, by config_simp; exact le_rfl,
    by config_simp; exact hN.ofs_mono _ _ (by omega) (by omega),
    fun i hi => hI.closed i (by config_simp at hi; omega),
    fun d h1 h2 => by config_simp at h1; config_simp at h2; omega⟩,
    by config_simp, by config_simp; omega, by config_simp, rfl, by config_simp, rfl⟩

theorem body_exec (c : Config) (hI : IS n m ofs tl rv W o c₀ c) (hlt : c.nreg 63 < c.nreg 64) :
    ∃ c' k, Exec P W bBody c c' k ∧ IS n m ofs tl rv W o c₀ c' ∧ c'.nreg 63 = c.nreg 63 + 1 ∧
      k ≤ 26 * (ofs (qA n m c.nmem (c.nreg 63) + 1) - ofs (qA n m c.nmem (c.nreg 63))) + 12 ∧
      c.nreg 64 ≤ c'.nreg 64 ∧ (∀ i < c.nreg 64, qA n m c'.nmem i = qA n m c.nmem i) := by
  obtain ⟨c₁, k₁, e₁, hJ₁, h66, h63, h64, hm, h65, rfl⟩ := deq_exec hN hIn hW hPW c hI hlt
  generalize hu : qA n m c.nmem (c.nreg 63) = u at h65
  have hun : u < n := hu ▸ hI.q_lt _ hlt
  have hle : ofs u ≤ ofs (u + 1) := hN.ofs_mono _ _ (by omega) (by omega)
  obtain ⟨c₂, k₂, e₂, ⟨hJ₂, h66₂, h67₂, h63₂, h65₂, h64₂, hq₂⟩, hk₂⟩ :=
    Exec.forN (P := P) (W := W) (ri := 66) (rN := 67) (N := ofs (u + 1)) (lo := ofs u) (B := 24)
    (body := bVisit) (fun i c' => VS n m ofs tl rv W o c₀ c' ∧ c'.nreg 66 = i ∧
      c'.nreg 67 = ofs (u + 1) ∧ c'.nreg 63 = c.nreg 63 + 1 ∧ c'.nreg 65 = u ∧
      c₁.nreg 64 ≤ c'.nreg 64 ∧ ∀ i < c₁.nreg 64, qA n m c'.nmem i = qA n m c₁.nmem i)
    (fun i c' h => ⟨h.1.wb, h.2.1, h.2.2.1⟩)
    (fun i c' h hi => by
      obtain ⟨hJ, g66, g67, g63, g65, g64, gq⟩ := h
      obtain ⟨c'', k, e, hJ', f66, f63, f65, f67, hk, f64, fq⟩ :=
        visit_exec hN hIn hW c' hJ (by rw [g66, g67]; exact hi)
      exact ⟨c'', k, e, ⟨hJ', by rw [f66, g66], by rw [f67, g67], by rw [f63, g63],
        by rw [f65, g65], by omega, fun i hi => by rw [fq i (by omega), gq i hi]⟩, hk⟩)
    hle ⟨hJ₁, by rw [h66, h65], by rw [hJ₁.r67, h65], h63, h65, le_rfl, fun _ _ => rfl⟩
  refine ⟨c₂, 10 + k₂, .seq e₁ e₂, ⟨hJ₂.toBS, fun i hi => ?_⟩, h63₂, by omega, by omega,
    fun i hi => by rw [hq₂ i (by omega), hm]⟩
  rw [h63₂] at hi
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
  · exact hJ₂.closed i (by omega)
  · have : qA n m c₂.nmem (c.nreg 63) = u := by rw [hq₂ _ (by omega), hm, hu]
    rw [this]
    intro d h1 h2
    have := hJ₂.closed_cur d (by rw [h65₂]; exact h1) (by rw [h66₂]; exact h2)
    rwa [h65₂] at this

end proofs

/-- The total degree of the first `h` vertices of the queue. -/
def dsum (n m : ℕ) (ofs : ℕ → ℕ) (mem : ℕ → ℕ) (h : ℕ) : ℕ :=
  ∑ i ∈ range h, (ofs (qA n m mem i + 1) - ofs (qA n m mem i))

theorem sum_deg_eq {n m : ℕ} {ofs tl rv ro : ℕ → ℕ} (hN : NWf n m ofs tl rv ro) :
    ∀ k ≤ n, ∑ v ∈ range k, (ofs (v + 1) - ofs v) + ofs 0 = ofs k := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    rw [sum_range_succ]
    have := ih (by omega)
    have := hN.ofs_mono k (k + 1) (by omega) hk
    omega

theorem BS.dsum_le {n m : ℕ} {ofs tl rv ro : ℕ → ℕ} {W : ℕ} {o : List ℕ} {c₀ c : Config}
    (hN : NWf n m ofs tl rv ro) (hI : BS n m tl rv W o c₀ c) {h : ℕ} (hh : h ≤ c.nreg 64) :
    dsum n m ofs c.nmem h ≤ m := by
  classical
  unfold dsum
  rw [← sum_image (g := qA n m c.nmem) (f := fun v => ofs (v + 1) - ofs v)
    (fun i hi j hj e => hI.q_inj i (by simp at hi; omega) j (by simp at hj; omega) e)]
  have h1 : ∑ v ∈ (range h).image (qA n m c.nmem), (ofs (v + 1) - ofs v) ≤
      ∑ v ∈ range n, (ofs (v + 1) - ofs v) :=
    sum_le_sum_of_subset (fun v hv => by
      obtain ⟨i, hi, rfl⟩ := mem_image.1 hv
      exact mem_range.2 (hI.q_lt i (by simp at hi; omega)))
  have h2 := sum_deg_eq hN n le_rfl
  have h3 := hN.ofs_n
  omega

section run

variable {n m : ℕ} {ofs w tl rv ro : ℕ → ℕ} {W : ℕ} {P : Input}
  (hN : NWf n m ofs tl rv ro) (hIn : InHolds P n m ofs w tl rv ro)
  (hW : memTop n m + 2 * n + 3 * m + 10 ≤ W) (hPW : ∀ j, P.data.getD j 0 ≤ W)
include hN hIn hW hPW

omit hN hIn hW hPW in
theorem IS_start {o : List ℕ} {c c' : Config} (hwb : WordsBounded W c') (hL : Lay n m c')
    (ho : c'.output = o)
    (hfr : ∀ a, (a < 13 * m ∨ 13 * m + 4 * n ≤ a) → c'.nmem a = c.nmem a)
    (h63 : c'.nreg 63 = 0) (h64 : c'.nreg 64 = 1) (hn : 1 ≤ n)
    (hmk : ∀ x < n, mkA n m c'.nmem x = if x = 0 then 1 else 0) (hq0 : qA n m c'.nmem 0 = 0)
    (hl0 : lvA m c'.nmem 0 = 0) : IS n m ofs tl rv W o c c' := by
  refine ⟨⟨hwb, hL, ho, hfr, by omega, by omega, fun i hi => ?_, fun i hi j hj _ => by omega,
    ⟨by omega, hq0⟩, fun v hv => ?_, fun v hv => ?_, hl0, fun i h1 h2 => by omega,
    fun i i' h1 h2 => ?_, fun i' _ h => by omega, fun i hi => ?_, fun _ => h64⟩,
    fun i hi => by omega⟩
  · obtain rfl : i = 0 := by omega
    rw [hq0]; omega
  · rw [hmk v hv]; split_ifs <;> simp
  · rw [hmk v hv]
    constructor
    · intro h; split_ifs at h with e; first | omega | exact ⟨0, by omega, by rw [hq0, e]⟩
    · rintro ⟨i, hi, e⟩; obtain rfl : i = 0 := by omega
      rw [hq0] at e; subst e; simp
  · obtain rfl : i' = 0 := by omega
    obtain rfl : i = 0 := by omega
    exact le_rfl
  · obtain rfl : i = 0 := by omega
    rw [hq0, hl0]

omit hN hIn hPW in
theorem bStart_exec (hn : 1 ≤ n) (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (hz : ∀ v < n, mkA n m c.nmem v = 0) :
    ∃ c' k, Exec P W bStart c c' k ∧ IS n m ofs tl rv W c.output c c' ∧ c'.nreg 63 = 0 ∧
      k = 7 := by
  have hW' := hW; unfold memTop at hW'
  obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14, a15, a16, a17, a18,
    a19, a20, a21⟩ := hL
  unfold bStart
  exec_block
  all_goals try (config_simp; omega)
  have hmem : ∀ a, upd (upd (upd (upd c.nmem (c.nreg 114 + c.nreg 100) (c.nreg 101)) (c.nreg 115)
      (c.nreg 100)) (c.nreg 112) (c.nreg 100)) (c.nreg 113) (c.nreg 105) a =
      if a = 13 * m + n then m else if a = 13 * m then 0 else if a = 13 * m + 3 * n then 0 else
        if a = 13 * m + 2 * n then 1 else c.nmem a := by
    intro a; simp only [upd_apply, a0, a1, a5, a12, a13, a14, a15, Nat.add_zero]
  refine ⟨IS_start ‹_› (Lay.of ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14,
    a15, a16, a17, a18, a19, a20, a21⟩ fun r h1 _ => by
      config_simp; simp only [upd_apply]; split_ifs <;> omega)
    rfl (fun a ha => by config_simp; rw [hmem]; split_ifs <;> omega)
    (by config_simp; omega) (by config_simp; omega) hn
    (fun x hx => by config_simp; simp only [mkA, hmem]; split_ifs <;> first | omega | exact hz x hx)
    (by config_simp; simp only [qA, hmem]; split_ifs <;> omega)
    (by config_simp; simp only [lvA, hmem]; split_ifs <;> omega),
    by config_simp; exact a0, rfl⟩

/-- **Breadth-first search from vertex `0`.** -/
theorem bfs_exec (hn : 1 ≤ n) (c : Config) (hc : WordsBounded W c) (hL : Lay n m c)
    (hz : ∀ v < n, mkA n m c.nmem v = 0) :
    ∃ c' k, Exec P W bfs c c' k ∧ k ≤ 26 * m + 14 * n + 9 ∧ Lay n m c' ∧ c'.output = c.output ∧
      (∀ a, (a < 13 * m ∨ 13 * m + 4 * n ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ v < n, mkA n m c'.nmem v = 0 ∨ mkA n m c'.nmem v = 1) ∧
      mkA n m c'.nmem 0 = 1 ∧ lvA m c'.nmem 0 = 0 ∧
      (∀ v < n, mkA n m c'.nmem v = 1 → Closed n m ofs tl rv c'.nmem v) ∧
      (∀ v < n, mkA n m c'.nmem v = 1 → lvA m c'.nmem v < n) ∧
      (∀ v < n, mkA n m c'.nmem v = 1 → v ≠ 0 →
        prA n m c'.nmem v < m ∧ tl (prA n m c'.nmem v) = v ∧
        lvA m c'.nmem (tl (rv (prA n m c'.nmem v))) + 1 = lvA m c'.nmem v ∧
        mkA n m c'.nmem (tl (rv (prA n m c'.nmem v))) = 1) := by
  obtain ⟨c₁, k₁, e₁, hI₁, h63, rfl⟩ := bStart_exec hW hn c hc hL hz
  obtain ⟨c', k', e, hI', hn', hk'⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 63) (b := 64)
    (body := bBody) (IS n m ofs tl rv W c.output c)
    (fun c => 14 * (n - c.nreg 63) + 26 * (m - dsum n m ofs c.nmem (c.nreg 63))) (fun c h => h.wb)
    (fun c₂ hI hlt => by
      obtain ⟨c₃, k₃, e₃, hI₃, g63, hk₃, g64, gq⟩ := body_exec hN hIn hW hPW c₂ hI hlt
      refine ⟨c₃, k₃, e₃, hI₃, ?_⟩
      have hd : dsum n m ofs c₃.nmem (c₃.nreg 63) = dsum n m ofs c₂.nmem (c₂.nreg 63) +
          (ofs (qA n m c₂.nmem (c₂.nreg 63) + 1) - ofs (qA n m c₂.nmem (c₂.nreg 63))) := by
        rw [g63]; unfold dsum; rw [sum_range_succ, gq _ hlt]
        congr 1
        exact sum_congr rfl fun i hi => by rw [gq i (by simp at hi; omega)]
      have hle := hI₃.dsum_le hN (h := c₃.nreg 63) (by have := hI₃.head_le; omega)
      have := hI.tail_le
      omega) hI₁
  have hfin : c'.nreg 63 = c'.nreg 64 := by have := hI'.head_le; omega
  refine ⟨c', 7 + k', .seq e₁ e, by rw [h63] at hk'; simp [dsum] at hk'; omega, hI'.lay, hI'.out,
    hI'.frame, hI'.mk01, ?_, hI'.lv0, fun v hv h1 => ?_, fun v hv h1 => ?_, fun v hv h1 h0 => ?_⟩
  · rw [hI'.mk_iff 0 hn]; exact ⟨0, hI'.q0.1, hI'.q0.2⟩
  · obtain ⟨i, hi, rfl⟩ := (hI'.mk_iff v hv).1 h1
    exact hI'.closed i (by omega)
  · obtain ⟨i, hi, rfl⟩ := (hI'.mk_iff v hv).1 h1
    have := hI'.lv_le i hi; have := hI'.tail_le; omega
  · obtain ⟨i, hi, rfl⟩ := (hI'.mk_iff v hv).1 h1
    have hi1 : 1 ≤ i := by
      by_contra h; obtain rfl : i = 0 := by omega
      exact h0 hI'.q0.2
    obtain ⟨p1, p2, p3, i', hi', p4⟩ := hI'.par i hi1 hi
    refine ⟨p1, p2, p3, ?_⟩
    rw [hI'.mk_iff _ (hN.tl_lt _ (hN.rv_lt _ p1))]
    exact ⟨i', by omega, p4⟩

end run

end SepProg

end PlanarSeparator
