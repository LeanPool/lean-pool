/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Search
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# The fundamental cycle search on the machine: the pass over the dual tree

After the search of `PlanarSeparator/Machine/Search.lean`, the faces are processed in the
reverse order of the search; for a face `F ≠ 0` with dart `p = pd F`, the program stores

`J F = Fw F + Σ_{x dart of F, x ≠ p, x off the tree} J (A x / 3)`,

where every face `A x / 3` was found from `F`, hence later, and has been processed already.
The statement is relative to a function `Ival` satisfying the same recurrence (in the
application, the weight of the inside of `pd F`, by `PlanarSeparator.Map.SpTree.sum_inside_eq`):
the pass stores `Ival F` for every face `F ≠ 0` (`pass_exec`). A second loop adds up the face
weights (`tot_exec`).
-/

@[expose] public section

namespace PlanarSeparator

namespace CycleSearch

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The program -/

/-- The dart `r19 = x` contributes `J (A x / 3)` if it is off the tree. -/
def childAdd : Stmt :=
  .seq (block [.addN 20 5 19, .loadN 21 20])
    (.ifLtN 21 1 (block [.loadN 22 19, .divN 23 22 3, .addN 20 10 23, .loadN 24 20,
      .addN 18 18 24]) .skip)

/-- The dart `r19` of the face `r16`, unless it is the dart `r17 = pd F`. -/
def child : Stmt :=
  .seq (.ifLtN 19 17 childAdd (.ifLtN 17 19 childAdd .skip)) (.instr (.addN 19 19 1))

/-- The face at position `r15 - 1` of the search. -/
def dpStep : Stmt :=
  .seq (block [.subN 15 15 1, .addN 20 9 15, .loadN 16 20, .addN 20 8 16, .loadN 17 20,
      .addN 20 6 16, .loadN 18 20, .mulN 19 16 3])
    (.seq child (.seq child (.seq child (block [.addN 20 10 16, .storeN 20 18]))))

/-- **The pass over the dual tree**, from the last face found down to the second. -/
def pass : Stmt := .seq (.instr (.copyN 15 11)) (.whileLtN 1 15 dpStep)

/-- One face `r25` of the total `r26` of the face weights. -/
def totStep : Stmt := block [.addN 20 6 25, .loadN 21 20, .addN 26 26 21, .addN 25 25 1]

/-- **The total weight** `r26`. -/
def totW : Stmt := .seq (block [.copyN 25 0, .copyN 26 0]) (.whileLtN 25 4 totStep)

/-! ### The recurrence -/

/-- The contribution of the dart `x` of a face whose dart `pd` is `p`. -/
def childVal (A T : ℕ → ℕ) (J : ℕ → ℕ) (p x : ℕ) : ℕ :=
  if x ≠ p ∧ T x = 0 then J (A x / 3) else 0

/-- The recurrence of the inside weights of the faces. -/
def RecHolds (k : ℕ) (A T Fw : ℕ → ℕ) (pdf : ℕ → ℕ) (J : ℕ → ℕ) : Prop :=
  ∀ F < k, F ≠ 0 → J F = Fw F + childVal A T J (pdf F) (3 * F) +
    childVal A T J (pdf F) (3 * F + 1) +
    childVal A T J (pdf F) (3 * F + 2)

/-- Every other dart off the tree of a face `F ≠ 0` leads to a face `≠ 0` whose dart `pd` is its
reverse. -/
def ChildOk (k : ℕ) (A T : ℕ → ℕ) (pdf : ℕ → ℕ) : Prop :=
  ∀ F < k, F ≠ 0 → ∀ j < 3, 3 * F + j ≠ pdf F → T (3 * F + j) = 0 →
    A (3 * F + j) / 3 ≠ 0 ∧ pdf (A (3 * F + j) / 3) = A (3 * F + j)

section proofs

variable {k : ℕ} {A T Fw : ℕ → ℕ} {W : ℕ} {o : List ℕ} {P : Input}

/-- After the search: every face is found exactly once. -/
theorem SB.exists_pos {c : Config} (hI : SB k A T Fw W o c) (hall : c.nreg 11 = k) {f : ℕ}
    (hf : f < k) : ∃ i < k, qu k c.nmem i = f := by
  classical
  by_contra hno
  push Not at hno
  have := hI.tail_lt hf (fun i hi => hno i (hall ▸ hi))
  omega

/-- The state of the pass: `r15` is the next position (exclusive), `c₀` the state after the
search. -/
structure DI (c₀ : Config) (Ival : ℕ → ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : CRegs k c
  r11 : c.nreg 11 = k
  mem : ∀ a, a < 10 * k ∨ 11 * k ≤ a → c.nmem a = c₀.nmem a
  out : c.output = o
  r15_pos : 1 ≤ c.nreg 15
  r15_le : c.nreg 15 ≤ k
  done : ∀ i, c.nreg 15 ≤ i → i < k → 1 ≤ i → jv k c.nmem (qu k c₀.nmem i) = Ival (qu k c₀.nmem i)

/-- Within one face at position `pos`: `r16` the face, `r17` its dart, `r18` the sum so far,
`r19` the next dart; the memory is `m`. -/
structure CI (c₀ : Config) (Ival : ℕ → ℕ) (m : ℕ → ℕ) (pos j : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : CRegs k c
  r11 : c.nreg 11 = k
  mem : c.nmem = m
  out : c.output = o
  r15 : c.nreg 15 = pos
  r16 : c.nreg 16 = qu k c₀.nmem pos
  r17 : c.nreg 17 = pd k c₀.nmem (qu k c₀.nmem pos)
  r19 : c.nreg 19 = 3 * qu k c₀.nmem pos + j
  r18 : c.nreg 18 = Fw (qu k c₀.nmem pos) + ∑ i ∈ range j,
    childVal A T Ival (pd k c₀.nmem (qu k c₀.nmem pos)) (3 * qu k c₀.nmem pos + i)

variable {c₀ : Config} {Ival : ℕ → ℕ} {tot pos : ℕ}

theorem childAdd_exec (ht : Tri k A T) (hS : SB k A T Fw W o c₀) (hall : c₀.nreg 11 = k)
    (hco : ChildOk k A T (pd k c₀.nmem)) (hle : ∀ F < k, Ival F ≤ tot)
    (hrec : RecHolds k A T Fw (pd k c₀.nmem) Ival) (hW : 11 * k + 3 * tot + 4 ≤ W)
    {m : ℕ → ℕ} (hm : ∀ a < 10 * k, m a = c₀.nmem a)
    (hdone : ∀ i, pos < i → i < k → 1 ≤ i → jv k m (qu k c₀.nmem i) = Ival (qu k c₀.nmem i))
    (hpos : 1 ≤ pos) (hposk : pos < k) {j : ℕ} (hj : j < 3) (c : Config)
    (hC : CI (k := k) (A := A) (T := T) (Fw := Fw) (W := W) (o := o) c₀ Ival m pos j c)
    (hne : 3 * qu k c₀.nmem pos + j ≠ pd k c₀.nmem (qu k c₀.nmem pos)) :
    ∃ c' k', Exec P W childAdd c c' k' ∧ (∀ r, r < 18 ∨ r = 19 → c'.nreg r = c.nreg r) ∧
      c'.nreg 18 = c.nreg 18 + childVal A T Ival (pd k c₀.nmem (qu k c₀.nmem pos))
        (3 * qu k c₀.nmem pos + j) ∧ c'.nreg 18 ≤ tot ∧
      c'.nmem = c.nmem ∧ c'.output = c.output ∧ k' ≤ 10 := by
  have hc := hC.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hC.regs
  generalize hF : qu k c₀.nmem pos = F at hC hne
  have hFk : F < k := hF ▸ hS.q_lt pos (by omega)
  have hF0 : F ≠ 0 := fun e => by
    have := hS.q_inj pos (by omega) 0 hS.q0.1 (by rw [hF, e, hS.q0.2]); omega
  generalize hx : 3 * F + j = x at hne
  have hxk : x < 3 * k := by omega
  have hTm : m (3 * k + x) = T x := by rw [hm _ (by omega)]; exact hS.hold.2.1 x hxk
  have hAm : m x = A x := by rw [hm _ (by omega)]; exact hS.hold.1 x hxk
  have hAx := ht.A_lt x hxk
  have hTle := ht.T_le x hxk
  have hr19 : c.nreg 19 = x := by rw [hC.r19, hF, hx]
  have hpart : c.nreg 18 + childVal A T Ival (pd k c₀.nmem F) x ≤ tot := by
    rw [hC.r18, hF]
    have hfull := hrec F hFk hF0
    have hsum : Fw F + ∑ i ∈ range 3, childVal A T Ival (pd k c₀.nmem F) (3 * F + i) = Ival F := by
      rw [hfull]; simp [sum_range_succ, add_assoc]
    have hsplit := sum_range_add_sum_Ico (fun i => childVal A T Ival (pd k c₀.nmem F) (3 * F + i))
      (show j + 1 ≤ 3 by omega)
    rw [sum_range_succ, hx] at hsplit
    have := hle F hFk
    omega
  have hmem := hC.mem
  unfold childAdd
  refine spec_seq ?_
  exec_block
  · rw [h5, hr19]; omega
  config_simp
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hTle with hT | hT
  · refine spec_ifLtN_true (by config_simp; simp only [h5, hr19, hmem, hTm, hT, h1]; omega) ?_
    -- the face across `x`
    obtain ⟨hc0, hpd⟩ := hco F hFk hF0 j hj (by rw [hx]; exact hne) (by rw [hx]; exact hT)
    rw [hx] at hc0 hpd
    obtain ⟨ic, hic, hqc⟩ := hS.exists_pos hall (show A x / 3 < k by omega)
    have hic1 : 1 ≤ ic := by
      by_contra h0'
      obtain rfl : ic = 0 := by omega
      rw [hS.q0.2] at hqc; exact hc0 hqc.symm
    obtain ⟨-, -, -, i', hi', hqi'⟩ := hS.pd_ok ic hic1 (by omega)
    rw [hqc, hpd, ht.A_A x hxk, show x / 3 = F by omega, ← hF] at hqi'
    have hpi : i' = pos := hS.q_inj i' (by omega) pos (by omega) hqi'
    have hJc : jv k m (A x / 3) = Ival (A x / 3) := by
      have := hdone ic (by omega) (by omega) hic1; rwa [hqc] at this
    have hcv : childVal A T Ival (pd k c₀.nmem F) x = Ival (A x / 3) := by
      simp [childVal, hne, hT]
    exec_block
    · config_simp; simp only [hr19, hmem, hAm, h3, h10]; omega
    · config_simp; simp only [hr19, hmem, hAm, h3, h10]
      rw [show m (10 * k + A x / 3) = jv k m (A x / 3) from rfl, hJc, ← hcv]
      omega
    refine ⟨fun r hr => ?_, ?_, ?_, rfl, rfl, by omega⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> omega
    · simp only [hr19, hmem, hAm, h3, h10]
      rw [show m (10 * k + A x / 3) = jv k m (A x / 3) from rfl, hJc, hcv]
    · simp only [hr19, hmem, hAm, h3, h10]
      rw [show m (10 * k + A x / 3) = jv k m (A x / 3) from rfl, hJc, ← hcv]
      omega
  · refine spec_ifLtN_false (by config_simp; simp only [h5, hr19, hmem, hTm, hT, h1]; omega) ?_
    refine spec_skip ‹_› ?_
    have hcv : childVal A T Ival (pd k c₀.nmem F) x = 0 := by simp [childVal, hT]
    refine ⟨fun r hr => ?_, ?_, ?_, rfl, rfl, by omega⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> omega
    · rw [hcv, add_zero]
    · have := hcv ▸ hpart; omega

theorem part_le (hrec : RecHolds k A T Fw (pd k c₀.nmem) Ival) (hle : ∀ F < k, Ival F ≤ tot)
    {F j : ℕ} (hFk : F < k) (hF0 : F ≠ 0) (hj : j < 3) :
    Fw F + ∑ i ∈ range j, childVal A T Ival (pd k c₀.nmem F) (3 * F + i) +
      childVal A T Ival (pd k c₀.nmem F) (3 * F + j) ≤ tot := by
  have hsum : Fw F + ∑ i ∈ range 3, childVal A T Ival (pd k c₀.nmem F) (3 * F + i) = Ival F := by
    rw [hrec F hFk hF0]; simp [sum_range_succ, add_assoc]
  have hsplit := sum_range_add_sum_Ico (fun i => childVal A T Ival (pd k c₀.nmem F) (3 * F + i))
    (show j + 1 ≤ 3 by omega)
  rw [sum_range_succ] at hsplit
  have := hle F hFk
  omega

theorem child_exec (ht : Tri k A T) (hS : SB k A T Fw W o c₀) (hall : c₀.nreg 11 = k)
    (hco : ChildOk k A T (pd k c₀.nmem)) (hle : ∀ F < k, Ival F ≤ tot)
    (hrec : RecHolds k A T Fw (pd k c₀.nmem) Ival) (hW : 11 * k + 3 * tot + 4 ≤ W)
    {m : ℕ → ℕ} (hm : ∀ a < 10 * k, m a = c₀.nmem a)
    (hdone : ∀ i, pos < i → i < k → 1 ≤ i → jv k m (qu k c₀.nmem i) = Ival (qu k c₀.nmem i))
    (hpos : 1 ≤ pos) (hposk : pos < k) {j : ℕ} (hj : j < 3) (c : Config)
    (hC : CI (k := k) (A := A) (T := T) (Fw := Fw) (W := W) (o := o) c₀ Ival m pos j c) :
    ∃ c' k', Exec P W child c c' k' ∧
      CI (k := k) (A := A) (T := T) (Fw := Fw) (W := W) (o := o) c₀ Ival m pos (j + 1) c' ∧
      k' ≤ 16 := by
  have hFk : qu k c₀.nmem pos < k := hS.q_lt pos (by omega)
  have hF0 : qu k c₀.nmem pos ≠ 0 := fun e => by
    have := hS.q_inj pos (by omega) 0 hS.q0.1 (by rw [e, hS.q0.2]); omega
  have hpart := part_le hrec hle hFk hF0 hj
  have hmid : ∃ c₁ k₁, Exec P W (.ifLtN 19 17 childAdd (.ifLtN 17 19 childAdd .skip)) c c₁ k₁ ∧
      (∀ r, r < 18 ∨ r = 19 → c₁.nreg r = c.nreg r) ∧
      c₁.nreg 18 = c.nreg 18 + childVal A T Ival (pd k c₀.nmem (qu k c₀.nmem pos))
        (3 * qu k c₀.nmem pos + j) ∧ c₁.nreg 18 ≤ tot ∧
      c₁.nmem = c.nmem ∧ c₁.output = c.output ∧ k₁ ≤ 14 := by
    rcases Nat.lt_trichotomy (c.nreg 19) (c.nreg 17) with h | h | h
    · have hne : 3 * qu k c₀.nmem pos + j ≠ pd k c₀.nmem (qu k c₀.nmem pos) := by
        intro e; have := hC.r19; have := hC.r17; omega
      obtain ⟨c₁, k₁, e₁, a1, a2, a3, a4, a5, a6⟩ := childAdd_exec (P := P) ht hS hall hco hle
        hrec hW hm hdone hpos hposk hj c hC hne
      exact ⟨c₁, k₁ + 1, .ifLtN_true h e₁, a1, a2, a3, a4, a5, by omega⟩
    · have hcv : childVal A T Ival (pd k c₀.nmem (qu k c₀.nmem pos))
        (3 * qu k c₀.nmem pos + j) = 0 := by
        simp [childVal, ← hC.r19, ← hC.r17, h]
      refine ⟨c, 0 + 2 + 2, .ifLtN_false (by omega) (.ifLtN_false (by omega) (.skip hC.wb)),
        fun r _ => rfl, by rw [hcv, add_zero], ?_, rfl, rfl, by omega⟩
      rw [hC.r18]; rw [hcv, add_zero] at hpart; exact hpart
    · have hne : 3 * qu k c₀.nmem pos + j ≠ pd k c₀.nmem (qu k c₀.nmem pos) := by
        intro e; have := hC.r19; have := hC.r17; omega
      obtain ⟨c₁, k₁, e₁, a1, a2, a3, a4, a5, a6⟩ := childAdd_exec (P := P) ht hS hall hco hle
        hrec hW hm hdone hpos hposk hj c hC hne
      exact ⟨c₁, k₁ + 1 + 2, .ifLtN_false (Nat.lt_asymm h) (.ifLtN_true h e₁), a1, a2, a3, a4, a5,
        by omega⟩
  obtain ⟨c₁, k₁, e₁, hr, h18, h18le, hmem, hout, hk₁⟩ := hmid
  have hw₁ := e₁.wb_right
  have h1 : c₁.nreg 1 = 1 := (hr 1 (by omega)).trans hC.regs.2.1
  have h19 : c₁.nreg 19 = 3 * qu k c₀.nmem pos + j := (hr 19 (by omega)).trans hC.r19
  have hb : c₁.nreg 19 + c₁.nreg 1 ≤ W := by rw [h1, h19]; omega
  refine ⟨_, k₁ + 1, .seq e₁ (Exec.addN hw₁ 19 19 1 hb), ⟨?_, cregs_of hC.regs fun r hr' => ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by omega⟩
  all_goals config_simp
  · exact (Exec.addN (P := P) hw₁ 19 19 1 hb).wb_right
  · rw [upd_other _ _ _ (by omega), hr r (by omega)]
  · rw [hr 11 (by omega)]; exact hC.r11
  · rw [hmem]; exact hC.mem
  · rw [hout]; exact hC.out
  · rw [hr 15 (by omega)]; exact hC.r15
  · rw [hr 16 (by omega)]; exact hC.r16
  · rw [hr 17 (by omega)]; exact hC.r17
  · rw [h1, h19]; omega
  · rw [h18, hC.r18, sum_range_succ]; omega

theorem dpStep_exec (ht : Tri k A T) (hS : SB k A T Fw W o c₀) (hall : c₀.nreg 11 = k)
    (hco : ChildOk k A T (pd k c₀.nmem)) (hle : ∀ F < k, Ival F ≤ tot)
    (hrec : RecHolds k A T Fw (pd k c₀.nmem) Ival) (hW : 11 * k + 3 * tot + 4 ≤ W) (c : Config)
    (hD : DI (k := k) (W := W) (o := o) c₀ Ival c) (hlt : 1 < c.nreg 15) :
    ∃ c' k', Exec P W dpStep c c' k' ∧ DI (k := k) (W := W) (o := o) c₀ Ival c' ∧
      c'.nreg 15 = c.nreg 15 - 1 ∧ k' ≤ 60 := by
  have hc := hD.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hD.regs
  have hr15 := hD.r15_le
  generalize hpos : c.nreg 15 - 1 = pos
  have hposk : pos < k := by omega
  have hFk : qu k c₀.nmem pos < k := hS.q_lt pos (by omega)
  have hq : c.nmem (c.nreg 9 + (c.nreg 15 - c.nreg 1)) = qu k c₀.nmem pos := by
    rw [h9, h1, hpos, hD.mem _ (by omega)]; rfl
  have hp : c.nmem (c.nreg 8 + qu k c₀.nmem pos) = pd k c₀.nmem (qu k c₀.nmem pos) := by
    rw [h8, hD.mem _ (by omega)]; rfl
  have hfw : c.nmem (c.nreg 6 + qu k c₀.nmem pos) = Fw (qu k c₀.nmem pos) := by
    rw [h6, hD.mem _ (by omega)]; exact hS.hold.2.2 _ hFk
  have hfwle : Fw (qu k c₀.nmem pos) ≤ tot := by
    have hF0 : qu k c₀.nmem pos ≠ 0 := fun e => by
      have := hS.q_inj pos (by omega) 0 hS.q0.1 (by rw [e, hS.q0.2]); omega
    have := part_le (j := 0) hrec hle hFk hF0 (by omega); simp at this; omega
  have hF0 : qu k c₀.nmem pos ≠ 0 := fun e => by
    have := hS.q_inj pos (by omega) 0 hS.q0.1 (by rw [e, hS.q0.2]); omega
  obtain ⟨c₁, k₁, e₁, hC0, hk₁⟩ : ∃ c₁ k₁, Exec P W (block [.subN 15 15 1, .addN 20 9 15,
      .loadN 16 20, .addN 20 8 16, .loadN 17 20, .addN 20 6 16, .loadN 18 20, .mulN 19 16 3])
      c c₁ k₁ ∧
      CI (k := k) (A := A) (T := T) (Fw := Fw) (W := W) (o := o) c₀ Ival c.nmem pos 0 c₁ ∧
      k₁ = 8 := by
    exec_block
    · config_simp; rw [h9]; omega
    · config_simp; rw [hq, h8]; omega
    · config_simp; rw [hq, h6]; omega
    · config_simp; rw [hq, h3]; omega
    refine ⟨⟨‹_›, cregs_of hD.regs fun r hr => ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> omega
    · exact hD.r11
    · exact hD.out
    · rw [h1, hpos]
    · rw [hq]
    · rw [hq, hp]
    · rw [hq, h3]; omega
    · rw [hq, hfw]; simp
  have hm : ∀ a < 10 * k, c.nmem a = c₀.nmem a := fun a ha => hD.mem a (Or.inl ha)
  have hdone : ∀ i, pos < i → i < k → 1 ≤ i →
      jv k c.nmem (qu k c₀.nmem i) = Ival (qu k c₀.nmem i) :=
    fun i h1' h2' h3' => hD.done i (by omega) h2' h3'
  have hpos1 : 1 ≤ pos := by omega
  obtain ⟨c₂, k₂, e₂, hC₂, hk₂⟩ := child_exec (P := P) ht hS hall hco hle hrec hW hm hdone hpos1
    hposk (by omega) c₁ hC0
  obtain ⟨c₃, k₃, e₃, hC₃, hk₃⟩ := child_exec (P := P) ht hS hall hco hle hrec hW hm hdone hpos1
    hposk (by omega) c₂ hC₂
  obtain ⟨c₄, k₄, e₄, hC₄, hk₄⟩ := child_exec (P := P) ht hS hall hco hle hrec hW hm hdone hpos1
    hposk (by omega) c₃ hC₃
  have hval : c₄.nreg 18 = Ival (qu k c₀.nmem pos) := by
    rw [hC₄.r18, hrec _ hFk hF0]; simp [sum_range_succ, add_assoc]
  have hc₄ := hC₄.wb
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ := hC₄.regs
  obtain ⟨c₅, k₅, e₅, hD₅, h15, hk₅⟩ : ∃ c₅ k₅, Exec P W (block [.addN 20 10 16, .storeN 20 18])
      c₄ c₅ k₅ ∧ DI (k := k) (W := W) (o := o) c₀ Ival c₅ ∧ c₅.nreg 15 = pos ∧ k₅ = 2 := by
    exec_block
    · rw [g10, hC₄.r16]; omega
    refine ⟨⟨‹_›, cregs_of hC₄.regs fun r hr => ?_, ?_, fun a ha => ?_, ?_, ?_, ?_, ?_⟩, ?_, rfl⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> omega
    · exact hC₄.r11
    · rw [upd_other _ _ _ (by rw [g10, hC₄.r16]; omega), hC₄.mem]; exact hD.mem a ha
    · exact hC₄.out
    · rw [hC₄.r15]; omega
    · rw [hC₄.r15]; omega
    · intro i hi1 hi2 hi3
      rw [hC₄.r15] at hi1
      simp only [jv, upd_apply, g10, hC₄.r16]
      split_ifs with e
      · have : qu k c₀.nmem i = qu k c₀.nmem pos := by omega
        rw [this, hval]
      · rw [hC₄.mem]
        exact hD.done i (by
          rcases Nat.lt_or_ge pos i with h | h
          · omega
          · exfalso; apply e; rw [show i = pos by omega]) hi2 hi3
    · exact hC₄.r15
  exact ⟨c₅, k₁ + (k₂ + (k₃ + (k₄ + k₅))), .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ e₅))), hD₅,
    by rw [h15], by omega⟩

/-- **The pass.** After the search has found every face, the pass stores `Ival F` for every
face `F ≠ 0`, within `62 k + 3` steps. -/
theorem pass_exec (ht : Tri k A T) (hS : SB k A T Fw W o c₀) (hall : c₀.nreg 11 = k)
    (hco : ChildOk k A T (pd k c₀.nmem)) (hle : ∀ F < k, Ival F ≤ tot)
    (hrec : RecHolds k A T Fw (pd k c₀.nmem) Ival) (hW : 11 * k + 3 * tot + 4 ≤ W) (hk : 0 < k) :
    ∃ c' k', Exec P W pass c₀ c' k' ∧ WordsBounded W c' ∧ CRegs k c' ∧ c'.nreg 11 = k ∧
      (∀ a, a < 10 * k ∨ 11 * k ≤ a → c'.nmem a = c₀.nmem a) ∧ c'.output = o ∧
      (∀ F < k, F ≠ 0 → jv k c'.nmem F = Ival F) ∧ k' ≤ 62 * k + 3 := by
  have hc := hS.wb
  have hb : c₀.nreg 11 ≤ W := by have := hS.tail_le; omega
  have e₁ := Exec.copyN (P := P) hc 15 11
  have hD : DI (k := k) (W := W) (o := o) c₀ Ival
      { c₀ with nreg := upd c₀.nreg 15 (c₀.nreg 11) } := by
    refine ⟨e₁.wb_right, cregs_of hS.regs fun r hr => ?_, ?_, fun a _ => rfl, hS.out, ?_, ?_, ?_⟩
    all_goals config_simp
    · simp only [upd_apply]; split_ifs <;> omega
    · exact hall
    · omega
    · omega
    · intro i h1 h2; omega
  obtain ⟨c', k', e, hD', hn, hk'⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 1) (b := 15)
    (body := dpStep) (DI (k := k) (W := W) (o := o) c₀ Ival) (fun c => 62 * c.nreg 15)
    (fun c h => h.wb)
    (fun c hc hlt => by
      obtain ⟨c₂, k₂, e₂, hD₂, h15, hk₂⟩ := dpStep_exec (P := P) ht hS hall hco hle hrec hW c hc
        (by rw [hc.regs.2.1] at hlt; exact hlt)
      exact ⟨c₂, k₂, e₂, hD₂, by rw [h15]; have := hc.regs.2.1; omega⟩) hD
  refine ⟨c', 1 + k', .seq e₁ e, hD'.wb, hD'.regs, hD'.r11, hD'.mem, hD'.out, fun F hF hF0 => ?_,
    by config_simp at hk'; rw [hall] at hk'; omega⟩
  obtain ⟨i, hi, rfl⟩ := hS.exists_pos hall hF
  have hi1 : 1 ≤ i := by
    by_contra h; obtain rfl : i = 0 := by omega
    exact hF0 hS.q0.2
  have h15 : c'.nreg 15 ≤ 1 := by rw [hD'.regs.2.1] at hn; omega
  exact hD'.done i (by omega) hi hi1

/-- The state of the total. -/
structure TI (c₀ : Config) (c : Config) : Prop where
  wb : WordsBounded W c
  keep : ∀ r, r ≠ 20 → r ≠ 21 → r ≠ 25 → r ≠ 26 → c.nreg r = c₀.nreg r
  mem : c.nmem = c₀.nmem
  out : c.output = c₀.output
  r25 : c.nreg 25 ≤ k
  r26 : c.nreg 26 = ∑ f ∈ range (c.nreg 25), Fw f

/-- **The total of the face weights**, in `r26`, within `6 k + 4` steps. -/
theorem totW_exec (hW : 11 * k + ∑ f ∈ range k, Fw f + 4 ≤ W) (c₀ : Config) (hc : WordsBounded W c₀)
    (hR : CRegs k c₀) (hH : Holds k A T Fw c₀.nmem) :
    ∃ c' k', Exec P W totW c₀ c' k' ∧ WordsBounded W c' ∧
      (∀ r, r ≠ 20 → r ≠ 21 → r ≠ 25 → r ≠ 26 → c'.nreg r = c₀.nreg r) ∧
      c'.nmem = c₀.nmem ∧ c'.output = c₀.output ∧ c'.nreg 26 = ∑ f ∈ range k, Fw f ∧
      k' ≤ 6 * k + 4 := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hR
  obtain ⟨c₁, k₁, e₁, hT₁, h25₁, hk₁⟩ :
      ∃ c₁ k₁, Exec P W (block [.copyN 25 0, .copyN 26 0]) c₀ c₁ k₁ ∧
      TI (k := k) (Fw := Fw) (W := W) c₀ c₁ ∧ c₁.nreg 25 = 0 ∧ k₁ = 2 := by
    exec_block
    refine ⟨⟨‹_›, fun r a b e f => ?_, rfl, rfl, ?_, ?_⟩, ?_, rfl⟩
    all_goals config_simp
    · simp only [upd_apply, e, f, ↓reduceIte]
    · rw [h0]; omega
    · rw [h0]; simp
    · rw [h0]
  have hsum_le : ∀ n ≤ k, ∑ f ∈ range n, Fw f ≤ ∑ f ∈ range k, Fw f := fun n hn =>
    sum_le_sum_of_subset (range_subset_range.2 hn)
  obtain ⟨c', k', e, hT', hn, hk'⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 25) (b := 4)
    (body := totStep) (TI (k := k) (Fw := Fw) (W := W) c₀) (fun c => 6 * (k - c.nreg 25))
    (fun c h => h.wb)
    (fun c hT hlt => by
      have hc := hT.wb
      have g4 : c.nreg 4 = k := (hT.keep 4 (by omega) (by omega) (by omega) (by omega)).trans h4
      have g6 : c.nreg 6 = 6 * k := (hT.keep 6 (by omega) (by omega) (by omega) (by omega)).trans h6
      have g1 : c.nreg 1 = 1 := (hT.keep 1 (by omega) (by omega) (by omega) (by omega)).trans h1
      rw [g4] at hlt
      have hfw : c.nmem (c.nreg 6 + c.nreg 25) = Fw (c.nreg 25) := by
        rw [g6, hT.mem]; exact hH.2.2 _ hlt
      have hs := hsum_le (c.nreg 25 + 1) (by omega)
      rw [sum_range_succ] at hs
      unfold totStep
      exec_block
      · rw [g6]; omega
      · config_simp; rw [hfw, hT.r26]; omega
      · config_simp; rw [g1]; omega
      refine ⟨⟨‹_›, fun r a b e f => ?_, hT.mem, hT.out, ?_, ?_⟩, ?_⟩
      all_goals config_simp
      · simp only [upd_apply, a, b, e, f, ↓reduceIte]; exact hT.keep r a b e f
      · rw [g1]; omega
      · rw [g1, hfw, hT.r26, sum_range_succ]
      · rw [g1]; omega) hT₁
  have g4 : c'.nreg 4 = k := (hT'.keep 4 (by omega) (by omega) (by omega) (by omega)).trans h4
  have h25 : c'.nreg 25 = k := by have := hT'.r25; rw [g4] at hn; omega
  refine ⟨c', k₁ + k', .seq e₁ e, hT'.wb, hT'.keep, hT'.mem, hT'.out, by rw [hT'.r26, h25], ?_⟩
  rw [h25₁] at hk'
  omega

end proofs

end CycleSearch

end PlanarSeparator
