/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.WordRAM
public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Frame

/-!
# The fundamental cycle search on the machine: the search of the dual tree

This file and `PlanarSeparator/Machine/Pass.lean`, `PlanarSeparator/Machine/Walk.lean` give
the machine part of the cycle separator lemma of Lipton and Tarjan for a plane map all of whose
faces are triangles, with a spanning tree. The map is held in memory dart by dart, with the darts
of a face at three consecutive addresses: for `k` faces and `3k` darts,

* `A x` at address `x` (`x < 3k`): the reversal of dart `x` (the face permutation is
  `x ↦ 3 ⌊x/3⌋ + (x + 1) mod 3`, so the face of `x` is `⌊x/3⌋`);
* `T x` at address `3k + x`: `1` for a dart of the spanning tree, `0` otherwise;
* `Fw f` at address `6k + f`: the weight of face `f`.

The work arrays: marks at `7k + f`, the dart `pd f` at `8k + f`, the order of the search at
`9k + i`, the inside weights at `10k + f`. Registers `r0 … r10` hold `0, 1, 2, 3, k, 3k, 6k, 7k,
8k, 9k, 10k`.

This file: a breadth-first search of the faces from the face `0` crossing only darts off the
tree. A face `g` found through the dart `x` of the face `f` records `pd g = A x`, the dart of
`g` leading back to `f`. The search reaches every face reachable this way
(`IS.closed`), each face once, each face after the face of its dart `pd` (`SB.pd_ok`), in
`O(k)` steps.
-/

@[expose] public section

namespace PlanarSeparator

namespace CycleSearch

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The memory -/

/-- The mark of face `f`. -/
def mark (k : ℕ) (m : ℕ → ℕ) (f : ℕ) : ℕ := m (7 * k + f)
/-- The dart of face `f` towards the face from which it was found. -/
def pd (k : ℕ) (m : ℕ → ℕ) (f : ℕ) : ℕ := m (8 * k + f)
/-- The face found `i`-th. -/
def qu (k : ℕ) (m : ℕ → ℕ) (i : ℕ) : ℕ := m (9 * k + i)
/-- The inside weight stored for face `f`. -/
def jv (k : ℕ) (m : ℕ → ℕ) (f : ℕ) : ℕ := m (10 * k + f)

/-- The data of a triangulated map with a spanning tree. -/
structure Tri (k : ℕ) (A T : ℕ → ℕ) : Prop where
  A_lt : ∀ x < 3 * k, A x < 3 * k
  A_A : ∀ x < 3 * k, A (A x) = x
  T_le : ∀ x < 3 * k, T x ≤ 1
  T_A : ∀ x < 3 * k, T (A x) = T x

/-- The memory holds the map, the tree and the face weights. -/
def Holds (k : ℕ) (A T Fw : ℕ → ℕ) (m : ℕ → ℕ) : Prop :=
  (∀ x < 3 * k, m x = A x) ∧ (∀ x < 3 * k, m (3 * k + x) = T x) ∧ (∀ f < k, m (6 * k + f) = Fw f)

theorem Holds.of_eq {k : ℕ} {A T Fw : ℕ → ℕ} {m m' : ℕ → ℕ} (h : Holds k A T Fw m)
    (h' : ∀ a < 7 * k, m' a = m a) : Holds k A T Fw m' :=
  ⟨fun x hx => (h' x (by omega)).trans (h.1 x hx), fun x hx => (h' _ (by omega)).trans (h.2.1 x hx),
    fun f hf => (h' _ (by omega)).trans (h.2.2 f hf)⟩

/-- The constant registers. -/
def CRegs (k : ℕ) (c : Config) : Prop :=
  c.nreg 0 = 0 ∧ c.nreg 1 = 1 ∧ c.nreg 2 = 2 ∧ c.nreg 3 = 3 ∧ c.nreg 4 = k ∧ c.nreg 5 = 3 * k ∧
    c.nreg 6 = 6 * k ∧ c.nreg 7 = 7 * k ∧ c.nreg 8 = 8 * k ∧ c.nreg 9 = 9 * k ∧
    c.nreg 10 = 10 * k

theorem cregs_of {k : ℕ} {c c' : Config} (hR : CRegs k c) (h : ∀ r ≤ 10, c'.nreg r = c.nreg r) :
    CRegs k c' := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hR
  exact ⟨(h 0 (by omega)).trans h0, (h 1 (by omega)).trans h1, (h 2 (by omega)).trans h2,
    (h 3 (by omega)).trans h3, (h 4 (by omega)).trans h4, (h 5 (by omega)).trans h5,
    (h 6 (by omega)).trans h6, (h 7 (by omega)).trans h7, (h 8 (by omega)).trans h8,
    (h 9 (by omega)).trans h9, (h 10 (by omega)).trans h10⟩

/-! ### The program -/

/-- Mark the face `0` and put it in the queue: `r11` is the tail, `r12` the head. -/
def sStart : Stmt := block [.addN 20 7 0, .storeN 20 1, .storeN 9 0, .copyN 11 1, .copyN 12 0]

/-- Dequeue the face `r13`; `r14` is its first dart. -/
def deq : Stmt := block [.addN 20 9 12, .loadN 13 20, .addN 12 12 1, .mulN 14 13 3]

/-- The dart `r14 = x` is off the tree: the face `g = A x / 3` across it is marked and queued if
new, with `pd g = A x`. -/
def visitNT : Stmt :=
  .seq (block [.loadN 22 14, .divN 23 22 3, .addN 20 7 23, .loadN 24 20])
    (.ifLtN 24 1 (block [.storeN 20 1, .addN 20 8 23, .storeN 20 22, .addN 20 9 11,
      .storeN 20 23, .addN 11 11 1]) .skip)

/-- One dart `r14` of the dequeued face. -/
def visit : Stmt :=
  .seq (block [.addN 20 5 14, .loadN 21 20])
    (.seq (.ifLtN 21 1 visitNT .skip) (.instr (.addN 14 14 1)))

/-- One face of the search. -/
def body : Stmt := .seq deq (.seq visit (.seq visit visit))

/-- **The search of the dual tree.** -/
def search : Stmt := .seq sStart (.whileLtN 12 11 body)

/-! ### The invariants -/

section inv

variable (k : ℕ) (A T Fw : ℕ → ℕ) (W : ℕ) (o : List ℕ)

/-- The state of the search. -/
structure SB (c : Config) : Prop where
  wb : WordsBounded W c
  regs : CRegs k c
  hold : Holds k A T Fw c.nmem
  out : c.output = o
  head_le : c.nreg 12 ≤ c.nreg 11
  q_lt : ∀ i < c.nreg 11, qu k c.nmem i < k
  q_inj : ∀ i < c.nreg 11, ∀ j < c.nreg 11, qu k c.nmem i = qu k c.nmem j → i = j
  q0 : 0 < c.nreg 11 ∧ qu k c.nmem 0 = 0
  mk01 : ∀ f < k, mark k c.nmem f = 0 ∨ mark k c.nmem f = 1
  mk_iff : ∀ f < k, mark k c.nmem f = 1 ↔ ∃ i < c.nreg 11, qu k c.nmem i = f
  pd_ok : ∀ i, 1 ≤ i → i < c.nreg 11 →
    pd k c.nmem (qu k c.nmem i) / 3 = qu k c.nmem i ∧ pd k c.nmem (qu k c.nmem i) < 3 * k ∧
      T (pd k c.nmem (qu k c.nmem i)) = 0 ∧
      ∃ i' < i, qu k c.nmem i' = A (pd k c.nmem (qu k c.nmem i)) / 3

/-- A face all of whose darts off the tree lead to marked faces. -/
def Scanned (m : ℕ → ℕ) (f : ℕ) : Prop :=
  ∀ j < 3, T (3 * f + j) = 0 → mark k m (A (3 * f + j) / 3) = 1

/-- Between two faces. -/
structure IS (c : Config) : Prop extends SB k A T Fw W o c where
  closed : ∀ i < c.nreg 12, Scanned k A T c.nmem (qu k c.nmem i)

/-- While scanning the darts of the dequeued face `r13`. -/
structure VS (c : Config) : Prop extends SB k A T Fw W o c where
  head_pos : 0 < c.nreg 12
  cur : c.nreg 13 = qu k c.nmem (c.nreg 12 - 1)
  r14_ge : 3 * c.nreg 13 ≤ c.nreg 14
  r14_le : c.nreg 14 ≤ 3 * c.nreg 13 + 3
  closed : ∀ i, i + 1 < c.nreg 12 → Scanned k A T c.nmem (qu k c.nmem i)
  closed_cur : ∀ x, 3 * c.nreg 13 ≤ x → x < c.nreg 14 → T x = 0 → mark k c.nmem (A x / 3) = 1

end inv

section proofs

variable {k : ℕ} {A T Fw : ℕ → ℕ} {W : ℕ} {o : List ℕ} {P : Input}

theorem SB.tail_lt {c : Config} (hI : SB k A T Fw W o c) {v : ℕ} (hv : v < k)
    (hnot : ∀ i < c.nreg 11, qu k c.nmem i ≠ v) : c.nreg 11 < k := by
  classical
  have h := Finset.card_le_card_of_injOn (qu k c.nmem) (s := range (c.nreg 11))
    (t := (range k).erase v)
    (fun i hi => by
      simp only [coe_range, Set.mem_Iio] at hi
      simp only [coe_erase, coe_range, Set.mem_sdiff, Set.mem_Iio, Set.mem_singleton_iff]
      exact ⟨hI.q_lt i hi, hnot i hi⟩)
    (fun i hi j hj e => hI.q_inj i (by simpa using hi) j (by simpa using hj) e)
  rw [card_range, card_erase_of_mem (mem_range.2 hv), card_range] at h
  omega

theorem SB.tail_le {c : Config} (hI : SB k A T Fw W o c) : c.nreg 11 ≤ k := by
  classical
  have h := Finset.card_le_card_of_injOn (qu k c.nmem) (s := range (c.nreg 11)) (t := range k)
    (fun i hi => by simp only [coe_range, Set.mem_Iio] at hi ⊢; exact hI.q_lt i hi)
    (fun i hi j hj e => hI.q_inj i (by simpa using hi) j (by simpa using hj) e)
  simpa using h

/-- A dart which does not discover a face: only `r14` advances. -/
theorem VS.next_skip {c c' : Config} (hJ : VS k A T Fw W o c) (hi : c.nreg 14 < 3 * c.nreg 13 + 3)
    (hv : T (c.nreg 14) = 0 → mark k c.nmem (A (c.nreg 14) / 3) = 1) (hwb : WordsBounded W c')
    (hK : ∀ r, r ≤ 13 → c'.nreg r = c.nreg r) (h14 : c'.nreg 14 = c.nreg 14 + 1)
    (hout : c'.output = c.output) (hmem : c'.nmem = c.nmem) : VS k A T Fw W o c' := by
  have h11 := hK 11 (by omega); have h12 := hK 12 (by omega); have h13 := hK 13 (by omega)
  refine ⟨⟨hwb, cregs_of hJ.regs fun r hr => hK r (by omega), hmem ▸ hJ.hold, hout.trans hJ.out,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals simp only [hmem, h11, h12, h13, h14]
  · exact hJ.head_le
  · exact hJ.q_lt
  · exact hJ.q_inj
  · exact hJ.q0
  · exact hJ.mk01
  · exact hJ.mk_iff
  · exact hJ.pd_ok
  · exact hJ.head_pos
  · exact hJ.cur
  · have := hJ.r14_ge; omega
  · omega
  · exact hJ.closed
  · intro x h1 h2
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
    · exact hJ.closed_cur x h1 h2
    · exact hv

/-- A dart off the tree to a new face: mark the face, record its dart, queue it. -/
theorem VS.next_enq (ht : Tri k A T) {c c' : Config} (hJ : VS k A T Fw W o c)
    (hi : c.nreg 14 < 3 * c.nreg 13 + 3) (hT : T (c.nreg 14) = 0)
    (hv : mark k c.nmem (A (c.nreg 14) / 3) = 0) (hwb : WordsBounded W c')
    (hK : ∀ r, r ≤ 13 → r ≠ 11 → c'.nreg r = c.nreg r) (h11 : c'.nreg 11 = c.nreg 11 + 1)
    (h14 : c'.nreg 14 = c.nreg 14 + 1) (hout : c'.output = c.output)
    (hmem : c'.nmem = upd (upd (upd c.nmem (7 * k + A (c.nreg 14) / 3) 1)
      (8 * k + A (c.nreg 14) / 3) (A (c.nreg 14))) (9 * k + c.nreg 11) (A (c.nreg 14) / 3)) :
    VS k A T Fw W o c' := by
  have h12 := hK 12 (by omega) (by omega); have h13 := hK 13 (by omega) (by omega)
  have hhp := hJ.head_pos; have hhl := hJ.head_le
  have hu := hJ.q_lt _ (show c.nreg 12 - 1 < c.nreg 11 by omega)
  rw [← hJ.cur] at hu
  have hx : c.nreg 14 < 3 * k := by omega
  generalize hgx : c.nreg 14 = x at hv hmem hT hx
  have hAx := ht.A_lt x hx
  generalize hgv : A x / 3 = v at hv hmem
  have hvn : v < k := by omega
  have hx3 : x / 3 = c.nreg 13 := by have := hJ.r14_ge; omega
  have hnot : ∀ i < c.nreg 11, qu k c.nmem i ≠ v := fun i hi e => by
    have := (hJ.mk_iff v hvn).2 ⟨i, hi, e⟩; omega
  have htl := hJ.tail_lt hvn hnot
  have hmk : ∀ f < k, mark k c'.nmem f = if f = v then 1 else mark k c.nmem f := fun f hf => by
    simp only [mark, hmem, upd_apply]; split_ifs <;> omega
  have hpd : ∀ f < k, pd k c'.nmem f = if f = v then A x else pd k c.nmem f := fun f hf => by
    simp only [pd, hmem, upd_apply]; split_ifs <;> omega
  have hqu : ∀ i < k, qu k c'.nmem i = if i = c.nreg 11 then v else qu k c.nmem i := fun i hi => by
    simp only [qu, hmem, upd_apply]; split_ifs <;> omega
  have hqu_lt : ∀ i < c.nreg 11, qu k c'.nmem i = qu k c.nmem i := fun i hi => by
    rw [hqu i (by omega)]; simp [show i ≠ c.nreg 11 by omega]
  have hmk_ge : ∀ f < k, mark k c.nmem f = 1 → mark k c'.nmem f = 1 := fun f hf h => by
    rw [hmk f hf]; split_ifs <;> simp [h]
  refine ⟨⟨hwb, cregs_of hJ.regs fun r hr => hK r (by omega) (by omega), ?_, hout.trans hJ.out,
    by rw [h11, h12]; omega, fun i hi => ?_, fun i hi j hj e => ?_, ?_, fun f hf => ?_,
    fun f hf => ?_, fun i hi1 hi2 => ?_⟩, by rw [h12]; exact hhp, ?_,
    by rw [h14, h13]; have := hJ.r14_ge; omega, by rw [h14, h13]; omega, fun i hi => ?_,
    fun y h1 h2 => ?_⟩
  · exact hJ.hold.of_eq fun a ha => by
      rw [hmem, upd_other _ _ _ (by omega), upd_other _ _ _ (by omega), upd_other _ _ _ (by omega)]
  · rw [h11] at hi; rw [hqu i (by omega)]; split_ifs
    · exact hvn
    · exact hJ.q_lt i (by omega)
  · rw [h11] at hi hj
    rw [hqu i (by omega), hqu j (by omega)] at e
    split_ifs at e with e1 e2 e2
    · omega
    · exact absurd e.symm (hnot j (by omega))
    · exact absurd e (hnot i (by omega))
    · exact hJ.q_inj i (by omega) j (by omega) e
  · rw [h11]; refine ⟨by omega, ?_⟩; rw [hqu_lt 0 hJ.q0.1]; exact hJ.q0.2
  · rw [hmk f hf]; split_ifs
    · right; rfl
    · exact hJ.mk01 f hf
  · rw [hmk f hf, h11]
    split_ifs with hfv
    · subst hfv; simp only [true_iff]; exact ⟨c.nreg 11, by omega, by rw [hqu _ htl]; simp⟩
    · rw [hJ.mk_iff f hf]
      constructor
      · rintro ⟨i, hi, e⟩; exact ⟨i, by omega, by rw [hqu_lt i hi]; exact e⟩
      · rintro ⟨i, hi, e⟩
        rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
        · exact ⟨i, hi, by rw [← hqu_lt i hi]; exact e⟩
        · rw [hqu _ htl] at e; simp at e; exact absurd e.symm hfv
  · rw [h11] at hi2
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi2 with hi2 | rfl
    · rw [hqu_lt i hi2, hpd _ (hJ.q_lt i hi2)]
      simp only [show qu k c.nmem i ≠ v from hnot i hi2, ↓reduceIte]
      obtain ⟨a, b, e, i', hi', f⟩ := hJ.pd_ok i hi1 hi2
      exact ⟨a, b, e, i', hi', by rw [hqu_lt i' (by omega)]; exact f⟩
    · rw [hqu _ htl]; simp only [↓reduceIte]
      rw [hpd _ hvn]; simp only [↓reduceIte]
      refine ⟨hgv, hAx, by rw [ht.T_A x hx]; exact hT, c.nreg 12 - 1, by omega, ?_⟩
      rw [ht.A_A x hx, hqu_lt _ (by omega), ← hJ.cur, hx3]
  · rw [h13, hJ.cur, h12, hqu_lt _ (by omega)]
  · rw [h12] at hi
    intro j hj hTj
    rw [hqu_lt i (by omega)] at hTj ⊢
    have hq := hJ.q_lt i (by omega)
    exact hmk_ge _ (by have := ht.A_lt (3 * qu k c.nmem i + j) (by omega); omega)
      (hJ.closed i hi j hj hTj)
  · rw [h13] at h1; rw [h14] at h2
    intro hTy
    have hy : y < 3 * k := by omega
    have := ht.A_lt y hy
    rcases Nat.lt_succ_iff_lt_or_eq.1 h2 with h2 | rfl
    · exact hmk_ge _ (by omega) (hJ.closed_cur y h1 h2 hTy)
    · rw [hmk _ (by omega), hgx, hgv]; simp

theorem visit_exec (ht : Tri k A T) (hW : 11 * k + 4 ≤ W) (c : Config) (hJ : VS k A T Fw W o c)
    (hi : c.nreg 14 < 3 * c.nreg 13 + 3) :
    ∃ c' k', Exec P W visit c c' k' ∧ VS k A T Fw W o c' ∧ c'.nreg 14 = c.nreg 14 + 1 ∧
      c'.nreg 12 = c.nreg 12 ∧ c'.nreg 13 = c.nreg 13 ∧ k' ≤ 22 ∧
      (∀ a, 11 * k ≤ a → c'.nmem a = c.nmem a) := by
  have hc := hJ.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hJ.regs
  have hhp := hJ.head_pos; have hhl := hJ.head_le
  have hu := hJ.q_lt _ (show c.nreg 12 - 1 < c.nreg 11 by omega)
  rw [← hJ.cur] at hu
  have hx : c.nreg 14 < 3 * k := by omega
  have htl := hJ.tail_le
  obtain ⟨hA, hTm, -⟩ := hJ.hold
  have hTx := hTm _ hx
  have hTle := ht.T_le _ hx
  have hAx := hA _ hx
  have hAlt := ht.A_lt _ hx
  unfold visit
  refine spec_seq ?_
  exec_block
  · rw [h5]; omega
  config_simp
  rw [h5, hTx] at *
  refine spec_seq ?_
  by_cases hT : T (c.nreg 14) = 0
  · refine spec_ifLtN_true (by config_simp; rw [hT, h1]; omega) ?_
    unfold visitNT
    refine spec_seq ?_
    exec_block
    · config_simp; rw [hAx, h7, h3]; omega
    config_simp
    rw [hAx, h7, h3] at *
    have hmv : c.nmem (7 * k + A (c.nreg 14) / 3) = mark k c.nmem (A (c.nreg 14) / 3) := rfl
    rw [hmv] at *
    rcases hJ.mk01 _ (show A (c.nreg 14) / 3 < k by omega) with hv | hv
    · refine spec_ifLtN_true (by config_simp; rw [hv, h1]; omega) ?_
      exec_block
      · config_simp; rw [h8]; omega
      · config_simp; rw [h9]; omega
      · config_simp; rw [h1]; omega
      refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
      refine ⟨hJ.next_enq ht hi hT hv hw (fun r hr hr11 => ?_) ?_ ?_ ?_ ?_, ?_, ?_, ?_, ?_, ?_⟩
      all_goals config_simp
      · simp only [upd_apply]
        split_ifs <;> omega
      · rw [h1]
      · rw [h1]
      · funext a; simp only [upd_apply, h1, h8, h9]
      · rw [h1]
      · omega
      · intro a ha; simp only [upd_apply, h8, h9]; split_ifs <;> omega
    · refine spec_ifLtN_false (by config_simp; rw [hv, h1]; omega) ?_
      refine spec_skip ‹_› ?_
      refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
      refine ⟨hJ.next_skip hi (fun _ => hv) hw (fun r hr => ?_) ?_ ?_ ?_, ?_, ?_, ?_, ?_,
        fun a _ => rfl⟩
      all_goals config_simp
      · simp only [upd_apply]
        split_ifs <;> omega
      · rw [h1]
      · rw [h1]
      · omega
  · refine spec_ifLtN_false (by config_simp; rw [h1]; omega) ?_
    refine spec_skip ‹_› ?_
    refine spec_instr (Exec.addN ‹_› _ _ _ (by config_simp; rw [h1]; omega)) fun hw => ?_
    refine ⟨hJ.next_skip hi (fun h => absurd h hT) hw (fun r hr => ?_) ?_ ?_ ?_, ?_, ?_, ?_, ?_,
      fun a _ => rfl⟩
    all_goals config_simp
    · simp only [upd_apply]
      split_ifs <;> omega
    · rw [h1]
    · rw [h1]
    · omega

theorem deq_exec (hW : 11 * k + 4 ≤ W) (c : Config) (hI : IS k A T Fw W o c)
    (hlt : c.nreg 12 < c.nreg 11) :
    ∃ c' k', Exec P W deq c c' k' ∧ VS k A T Fw W o c' ∧ c'.nreg 14 = 3 * c'.nreg 13 ∧
      c'.nreg 12 = c.nreg 12 + 1 ∧ k' = 4 := by
  have hc := hI.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hI.regs
  have htl := hI.tail_le
  have hu := hI.q_lt _ hlt
  have hq : c.nmem (c.nreg 9 + c.nreg 12) = qu k c.nmem (c.nreg 12) := by rw [h9]; rfl
  unfold deq
  exec_block
  · rw [h9]; omega
  · config_simp; rw [h1]; omega
  · config_simp; rw [hq, h3]; omega
  config_simp
  rw [hq] at *
  refine ⟨⟨⟨‹_›, cregs_of hI.regs fun r hr => ?_, hI.hold, hI.out, ?_, hI.q_lt, hI.q_inj, hI.q0,
    hI.mk01, hI.mk_iff, hI.pd_ok⟩, ?_, ?_, ?_, ?_, fun i hi => hI.closed i ?_,
    fun x h1' h2' => ?_⟩, ?_, ?_⟩
  all_goals config_simp
  · simp only [upd_apply]
    split_ifs <;> omega
  all_goals try rw [h1]
  all_goals try rw [h3]
  · omega
  · omega
  · simp
  · rw [Nat.mul_comm]
  · omega
  · config_simp at hi; rw [h1] at hi; omega
  · config_simp at h1'; config_simp at h2'; rw [h3] at h2'; omega
  · rw [Nat.mul_comm]

theorem body_exec (ht : Tri k A T) (hW : 11 * k + 4 ≤ W) (c : Config) (hI : IS k A T Fw W o c)
    (hlt : c.nreg 12 < c.nreg 11) :
    ∃ c' k', Exec P W body c c' k' ∧ IS k A T Fw W o c' ∧ c'.nreg 12 = c.nreg 12 + 1 ∧
      k' ≤ 70 ∧ (∀ a, 11 * k ≤ a → c'.nmem a = c.nmem a) := by
  obtain ⟨c₁, k₁, e₁, hJ₁, h14₁, h12₁, rfl⟩ := deq_exec (P := P) hW c hI hlt
  obtain ⟨c₂, k₂, e₂, hJ₂, h14₂, h12₂, h13₂, hk₂, f₂⟩ := visit_exec (P := P) ht hW c₁ hJ₁ (by omega)
  obtain ⟨c₃, k₃, e₃, hJ₃, h14₃, h12₃, h13₃, hk₃, f₃⟩ := visit_exec (P := P) ht hW c₂ hJ₂ (by omega)
  obtain ⟨c₄, k₄, e₄, hJ₄, h14₄, h12₄, h13₄, hk₄, f₄⟩ := visit_exec (P := P) ht hW c₃ hJ₃ (by omega)
  have f₁ : c₁.nmem = c.nmem := Exec.nmem_of_st e₁ (by decide)
  refine ⟨c₄, 4 + (k₂ + (k₃ + k₄)), .seq e₁ (.seq e₂ (.seq e₃ e₄)), ⟨hJ₄.toSB, fun i hi => ?_⟩,
    by omega, by omega, fun a ha => by rw [f₄ a ha, f₃ a ha, f₂ a ha, f₁]⟩
  rcases Nat.lt_or_ge (i + 1) (c₄.nreg 12) with h | h
  · exact hJ₄.closed i h
  · obtain rfl : i = c₄.nreg 12 - 1 := by omega
    rw [← hJ₄.cur]
    intro j hj hTj
    exact hJ₄.closed_cur _ (by omega) (by omega) hTj

theorem sStart_exec (hW : 11 * k + 4 ≤ W) (hk : 0 < k) (c : Config)
    (hc : WordsBounded W c) (hR : CRegs k c) (hH : Holds k A T Fw c.nmem) (ho : c.output = o)
    (hz : ∀ f < k, mark k c.nmem f = 0) :
    ∃ c' k', Exec P W sStart c c' k' ∧ IS k A T Fw W o c' ∧ c'.nreg 12 = 0 ∧ k' = 5 ∧
      (∀ a, a < 7 * k → c'.nmem a = c.nmem a) ∧ (∀ a, 11 * k ≤ a → c'.nmem a = c.nmem a) := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hR
  unfold sStart
  exec_block
  · rw [h7, h0]; omega
  config_simp
  have hm : ∀ a, upd (upd c.nmem (c.nreg 7 + c.nreg 0) (c.nreg 1)) (c.nreg 9) (c.nreg 0) a =
      if a = 9 * k then 0 else if a = 7 * k then 1 else c.nmem a := by
    intro a; simp only [upd_apply, h0, h1, h7, h9, Nat.add_zero]
  have hm' : ∀ a, a < 7 * k →
      upd (upd c.nmem (c.nreg 7 + c.nreg 0) (c.nreg 1)) (c.nreg 9) (c.nreg 0) a = c.nmem a := by
    intro a ha; rw [hm]; split_ifs <;> omega
  refine ⟨⟨⟨‹_›, cregs_of ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ fun r hr => ?_,
    hH.of_eq hm', ho, ?_, fun i hi => ?_, fun i hi j hj _ => ?_, ?_, fun f hf => ?_,
    fun f hf => ?_, fun i hi1 hi2 => ?_⟩, fun i hi => ?_⟩, ?_, hm', fun a ha => ?_⟩
  all_goals config_simp
  · simp only [upd_apply]; split_ifs <;> omega
  · rw [h0]; omega
  · config_simp at hi; rw [h1] at hi
    obtain rfl : i = 0 := by omega
    simpa only [qu, hm, add_zero, ↓reduceIte] using hk
  · config_simp at hi; config_simp at hj; rw [h1] at hi hj; omega
  · exact ⟨by rw [h1]; omega, by simp only [qu, hm]; simp⟩
  · simp only [mark, hm]; split_ifs <;> first | omega | exact Or.inl (hz f hf)
  · constructor
    · intro h
      by_cases e : f = 0
      · exact ⟨0, by rw [h1]; omega, by simp [qu, hm, e]⟩
      · exfalso
        have := hz f hf
        simp only [mark] at this
        have hne : 7 * k + f ≠ 9 * k := by omega
        have hne' : 7 * k + f ≠ 7 * k := by omega
        simp only [mark, hm, hne, hne', ite_false, this, Nat.zero_ne_one] at h
    · rintro ⟨i, hi, e⟩
      rw [h1] at hi
      obtain rfl : i = 0 := by omega
      simp only [qu, hm, add_zero, ↓reduceIte] at e
      subst e
      simp [mark, hm]
      omega
  · config_simp at hi2; rw [h1] at hi2; omega
  · config_simp at hi; rw [h0] at hi; omega
  · rw [h0]
  · rw [hm]; split_ifs <;> omega

/-- **The search.** From a state holding the map, with all marks `0`, the search ends with
every face it reached closed, within `72 k + 7` steps. -/
theorem search_exec (ht : Tri k A T) (hW : 11 * k + 4 ≤ W) (hk : 0 < k) (c : Config)
    (hc : WordsBounded W c) (hR : CRegs k c) (hH : Holds k A T Fw c.nmem) (ho : c.output = o)
    (hz : ∀ f < k, mark k c.nmem f = 0) :
    ∃ c' k', Exec P W search c c' k' ∧ IS k A T Fw W o c' ∧ c'.nreg 12 = c'.nreg 11 ∧
      k' ≤ 72 * k + 7 ∧ (∀ a, 11 * k ≤ a → c'.nmem a = c.nmem a) := by
  obtain ⟨c₁, k₁, e₁, hI₁, h12, rfl, -, f₁⟩ := sStart_exec (P := P) hW hk c hc hR hH ho hz
  obtain ⟨c', k', e, ⟨hI', f'⟩, hn, hk'⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 12)
    (b := 11) (body := body) (fun c' => IS k A T Fw W o c' ∧ ∀ a, 11 * k ≤ a → c'.nmem a = c.nmem a)
    (fun c => 72 * (k - c.nreg 12)) (fun c h => h.1.wb)
    (fun c' hc hlt => by
      obtain ⟨c₂, k₂, e₂, hI₂, h12₂, hk₂, f₂⟩ := body_exec (P := P) ht hW c' hc.1 hlt
      refine ⟨c₂, k₂, e₂, ⟨hI₂, fun a ha => by rw [f₂ a ha, hc.2 a ha]⟩, ?_⟩
      have := hc.1.tail_le
      rw [h12₂]
      omega) ⟨hI₁, f₁⟩
  refine ⟨c', 5 + k', .seq e₁ e, hI', by have := hI'.head_le; omega, by rw [h12] at hk'; omega, f'⟩

end proofs

end CycleSearch

end PlanarSeparator
