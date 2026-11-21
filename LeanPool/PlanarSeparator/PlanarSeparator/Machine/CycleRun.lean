/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.CycleBridge

/-!
# The cycle search with its frame

`CycleSearch.cycleSep_run` gives the outcome and the facts a caller needs after the search.
The memory at and above `11 k` and below `7 k` is kept, the search of the
dual tree is left at `8 k … 10 k` (the darts `pd` and the order of the search, `SB`), the
registers above `62` are kept, and the outcome registers describe a balanced fundamental cycle.
-/

@[expose] public section

namespace PlanarSeparator

namespace CycleSearch

open Finset Map Map.SpTree WordRAM WordRAM.Machine Coded

variable {D V : Type*} [Fintype D] [DecidableEq D] [Fintype V] [DecidableEq V] {M : Map D V}
  {T : M.SpTree} {k : ℕ} {cd : D ≃ Fin (3 * k)} {A Tm : ℕ → ℕ}

theorem cycleSep_wmax : cycleSep.wmax = 62 := by decide

theorem cycleSep_wr {r : ℕ} (hr : 63 ≤ r) : cycleSep.wr r = false :=
  Stmt.wr_of_wmax (by rw [cycleSep_wmax]; omega)

theorem walk_st : walk.st = false := by decide

theorem holds_eq {Fw m m' : ℕ → ℕ} (h : Holds k A Tm Fw m) (h' : Holds k A Tm Fw m') (a : ℕ)
    (ha : a < 7 * k) : m a = m' a := by
  rcases Nat.lt_or_ge a (3 * k) with h1 | h1
  · rw [h.1 a h1, h'.1 a h1]
  rcases Nat.lt_or_ge a (6 * k) with h2 | h2
  · have := h.2.1 (a - 3 * k) (by omega); have := h'.2.1 (a - 3 * k) (by omega)
    rw [show a = 3 * k + (a - 3 * k) by omega]; omega
  · have := h.2.2 (a - 6 * k) (by omega); have := h'.2.2 (a - 6 * k) (by omega)
    rw [show a = 6 * k + (a - 6 * k) by omega]; omega

/-- **The cycle search with its frame.** The memory below
`7 k` and from `11 k` on, and the registers from `63` on, are kept, and there is a state `c₁`
(the end of the search of the dual tree) satisfying `SB` with every face found, whose memory at
`8 k … 10 k` is still in place at the end. -/
theorem cycleSep_run {P : Input} {W : ℕ} {Fw : ℕ → ℕ} (hC : Coded M T k cd A Tm)
    (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) (hk2 : 2 ≤ k) (fw : M.Face → ℕ)
    (hFw : ∀ x, Fw ((cd x : ℕ) / 3) = fw (M.face x)) (hW : 11 * k + 3 * ∑ G, fw G + 4 ≤ W)
    (c : Config) (hc : WordsBounded W c) (hR : CRegs k c) (hH : Holds k A Tm Fw c.nmem)
    (hz : ∀ f < k, mark k c.nmem f = 0) :
    ∃ c' k', Exec P W cycleSep c c' k' ∧ k' ≤ 202 * k + 112 ∧ c'.output = c.output ∧
      CycleOut M T fw cd (c'.nreg 61) (c'.nreg 50) (c'.nreg 53) ∧
      (∀ a, (a < 7 * k ∨ 11 * k ≤ a) → c'.nmem a = c.nmem a) ∧
      (∀ r, 63 ≤ r → c'.nreg r = c.nreg r) ∧ CRegs k c' ∧
      ∃ c₁, SB k A Tm Fw W c.output c₁ ∧ c₁.nreg 11 = k ∧
        (∀ a, 8 * k ≤ a → a < 10 * k → c'.nmem a = c₁.nmem a) := by
  have hk : 0 < k := by omega
  have ht := hC.tri
  have hsum := hC.sum_fw fw hFw
  obtain ⟨c₁, k₁, e₁, hI₁, hend, hk₁, f₁⟩ := search_exec (P := P) (o := c.output) ht (by omega)
    hk c hc hR hH rfl hz
  have hall := hC.search_all hM hk hI₁ hend
  have hS₁ := hI₁.toSB
  obtain ⟨c₂, k₂, e₂, hw₂, hR₂, h11₂, hm₂, ho₂, hJ₂, hk₂⟩ := pass_exec (P := P)
    (Ival := Ival (T := T) (cd := cd) (c₀ := c₁) hk fw) (tot := ∑ G, fw G) ht hS₁ hall
    (hC.childOk hk hS₁ hall hM) (fun F _ => Iw_le (T := T) fw _)
    (hC.recHolds hk hS₁ hall fw hM hT3 hFw) hW hk
  have hH₂ : Holds k A Tm Fw c₂.nmem := hS₁.hold.of_eq fun a ha => hm₂ a (Or.inl (by omega))
  obtain ⟨c₃, k₃, e₃, hw₃, hkeep₃, hm₃, ho₃, h26, hk₃⟩ := totW_exec (P := P) (A := A) (T := Tm)
    (by rw [← hsum]; omega) c₂ hw₂ hR₂ hH₂
  rw [← hsum] at h26
  have hR₃ : CRegs k c₃ := cregs_of hR₂ fun r hr =>
    hkeep₃ r (by omega) (by omega) (by omega) (by omega)
  have hWS : WS k A Tm (pd k c₁.nmem) (jv k c₂.nmem) (∑ G, fw G) W c₃ :=
    ⟨hw₃, hR₃, fun x hx => by rw [hm₃]; exact hH₂.1 x hx,
      fun x hx => by rw [hm₃]; exact hH₂.2.1 x hx,
      fun f hf => by rw [hm₃, hm₂ _ (Or.inl (by omega))]; rfl, fun f hf _ => by rw [hm₃]; rfl, h26⟩
  have hq1 : qu k c₁.nmem 1 < k := hS₁.q_lt 1 (by omega)
  have hq10 : qu k c₁.nmem 1 ≠ 0 := fun e => by
    have := hS₁.q_inj 1 (by omega) 0 hS₁.q0.1 (by rw [e, hS₁.q0.2]); omega
  obtain ⟨-, hd0, hT0⟩ := pd_spec hS₁ hall hq1 hq10
  have hmq : c₃.nmem (9 * k + 1) = qu k c₁.nmem 1 := by rw [hm₃, hm₂ _ (Or.inl (by omega))]; rfl
  have hJ : ∀ f < k, f ≠ 0 → jv k c₂.nmem f = Ival (T := T) (cd := cd) (c₀ := c₁) hk fw f :=
    hJ₂
  obtain ⟨c₄, k₄, e₄, hWS₄, ho₄, hgood, hk₄⟩ := walk_exec (P := P) (o := c₃.output)
    (hC.wa hk hS₁ hall fw hM hJ) (hC.wh hk hS₁ hall fw hM hT3 hFw hJ) hW c₃ hWS rfl
    (by rw [hmq]; exact hq1) (by rw [hmq]; exact hd0) (by rw [hmq]; exact hT0)
  have hm₄ : c₄.nmem = c₃.nmem := Exec.nmem_of_st e₄ walk_st
  have he : Exec P W cycleSep c c₄ (k₁ + (k₂ + (k₃ + k₄))) := .seq e₁ (.seq e₂ (.seq e₃ e₄))
  refine ⟨c₄, k₁ + (k₂ + (k₃ + k₄)), he, by omega, by rw [ho₄, ho₃, ho₂], ?_, ?_,
    fun r hr => he.nreg_of_wr (cycleSep_wr hr), hWS₄.regs, c₁, hS₁, hall, ?_⟩
  · rcases hgood with ⟨h61, hlt, hT, h1, h2⟩ | ⟨h61, hlt, hT, ha, h54, h1, h2⟩
    · left
      refine ⟨h61, dartN (cd := cd) hk (c₄.nreg 53), cd_dartN hk hlt,
        (hC.T_cd _).1 (by rw [cd_dartN hk hlt]; exact hT), ?_, ?_⟩
      · have := hC.Inum_eq hk hS₁ hall fw hM hJ hlt hT
        unfold Iw at this; rw [← this]; exact h1
      · have e := hC.Inum_eq hk hS₁ hall fw hM hJ hlt hT
        have hnt : ¬ T.IsTree (dartN (cd := cd) hk (c₄.nreg 53)) :=
          (hC.T_cd _).1 (by rw [cd_dartN hk hlt]; exact hT)
        have hc := sum_inside_α T hM hnt fw
        unfold Iw at e
        omega
    · right
      have h53 : c₄.nreg 53 < 3 * k := by
        rcases ha with h | h <;> rw [h]
        · exact hC.tri.A_lt _ (phi3_lt hlt)
        · exact hC.tri.A_lt _ (phi3_lt (phi3_lt hlt))
      refine ⟨h61, dartN (cd := cd) hk (c₄.nreg 50), dartN (cd := cd) hk (c₄.nreg 53),
        cd_dartN hk hlt, cd_dartN hk h53, (hC.T_cd _).1 (by rw [cd_dartN hk hlt]; exact hT), ?_, ?_,
        ?_⟩
      · rcases ha with h | h
        · left; rw [h, hC.dartN_A hk (phi3_lt hlt), hC.dartN_phi3 hk hlt]
        · right; rw [h, hC.dartN_A hk (phi3_lt (phi3_lt hlt)), hC.dartN_phi3 hk (phi3_lt hlt),
            hC.dartN_phi3 hk hlt]
      · have := hC.cvn_eq hk hS₁ hall fw hM hJ h53
        unfold Iw at this; rw [← this, ← h54]; exact h1
      · have e1 := hC.cvn_eq hk hS₁ hall fw hM hJ h53
        have e2 := hFw (dartN (cd := cd) hk (c₄.nreg 50))
        rw [cd_dartN hk hlt] at e2
        unfold Iw at e1
        rw [← e1, ← h54, ← e2]
        exact h2
  · intro a ha
    rw [hm₄, hm₃]
    rcases ha with ha | ha
    · rw [hm₂ a (Or.inl (by omega))]; exact holds_eq hS₁.hold hH a ha
    · rw [hm₂ a (Or.inr ha), f₁ a ha]
  · intro a h1 h2
    rw [hm₄, hm₃, hm₂ a (Or.inl h2)]
/-- **The cycle separator lemma of Lipton and Tarjan on the machine, in linear time.** Let `M` be
a plane map all of whose `k ≥ 2` faces are triangles, with a spanning tree `T`, coded in memory
(`Coded`, `Holds`) with face weights `fw`. From any state with the constant registers set and
the marks clear, `cycleSep` ends within `202 k + 112` steps in a state whose registers
`r61, r50, r53` describe a balanced fundamental cycle (`CycleOut`). -/
theorem cycleSep_exec {P : Input} {W : ℕ} {Fw : ℕ → ℕ} (hC : Coded M T k cd A Tm)
    (hM : M.IsPlane) (hT3 : ∀ δ, M.IsTriangle δ) (hk2 : 2 ≤ k) (fw : M.Face → ℕ)
    (hFw : ∀ x, Fw ((cd x : ℕ) / 3) = fw (M.face x)) (hW : 11 * k + 3 * ∑ G, fw G + 4 ≤ W)
    (c : Config) (hc : WordsBounded W c) (hR : CRegs k c) (hH : Holds k A Tm Fw c.nmem)
    (hz : ∀ f < k, mark k c.nmem f = 0) :
    ∃ c' k', Exec P W cycleSep c c' k' ∧ k' ≤ 202 * k + 112 ∧ c'.output = c.output ∧
      CycleOut M T fw cd (c'.nreg 61) (c'.nreg 50) (c'.nreg 53) := by
  obtain ⟨c', steps, execution, cost, output, outcome, -⟩ :=
    cycleSep_run (P := P) hC hM hT3 hk2 fw hFw hW c hc hR hH hz
  exact ⟨c', steps, execution, cost, output, outcome⟩

end CycleSearch

end PlanarSeparator
