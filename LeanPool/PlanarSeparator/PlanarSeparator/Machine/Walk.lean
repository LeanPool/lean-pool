/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.PlanarSeparator.Machine.Pass

/-!
# The fundamental cycle search on the machine: the walk

With the inside weights `J F` of the darts `pd F` stored (`PlanarSeparator/Machine/Pass.lean`)
and the total `tot` of the face weights, the inside weight of every dart `y` off the tree is
`Inum y`: `J (y / 3)` if `y` is the dart `pd` of its face, and `tot - J (A y / 3)` otherwise
(then `A y` is the dart `pd` of its face). The walk of Lipton and Tarjan starts from the dart
`δ₀ = pd` of the second face found. If neither side of `δ₀` weighs more than `2/3` of `tot`, it
stops (mode `0`); otherwise it starts from the heavier side and moves from `δ` to the heavier
of `A (φ δ)` and `A (φ² δ)` as long as that is heavier than `2/3`, and stops (mode `1`) at the
first `δ` where it is not. Each step costs `O(1)`, and the insides shrink, so the walk costs
`O(k)`.

The statement (`walk_exec`) is numeric: it assumes the recurrence and the complement rule of
`Inum`, and a size function decreasing along the walk; the bridge to plane maps
(`PlanarSeparator/Machine/CycleBridge.lean`) supplies them.
-/

@[expose] public section

namespace PlanarSeparator

namespace CycleSearch

open WordRAM WordRAM.Machine WordRAM.Machine.Stmt WordRAM.Programs Finset

/-! ### The numeric quantities -/

/-- The next dart of the face, numerically. -/
def phi3 (y : ℕ) : ℕ := if y % 3 < 2 then y + 1 else y - 2

/-- The inside weight of a dart off the tree. -/
def Inum (A pdf J : ℕ → ℕ) (tot y : ℕ) : ℕ :=
  if y / 3 ≠ 0 ∧ pdf (y / 3) = y then J (y / 3) else tot - J (A y / 3)

/-- The inside weight of any dart (`0` for a tree dart). -/
def cvn (A T pdf J : ℕ → ℕ) (tot z : ℕ) : ℕ := if T z = 0 then Inum A pdf J tot z else 0

/-! ### The program -/

/-- `r42 := Inum r41`, for `r41` off the tree. -/
def ivSelf : Stmt := block [.addN 20 10 43, .loadN 42 20]
/-- Subtract the stored inside weight of the reverse dart from the total weight. -/
def ivOther : Stmt :=
  block [.loadN 45 41, .divN 45 45 3, .addN 20 10 45, .loadN 46 20, .subN 42 26 46]
/-- Compute the inside weight from the stored weight of the parent dart in either orientation. -/
def ival : Stmt :=
  .seq (block [.divN 43 41 3, .addN 20 8 43, .loadN 44 20])
    (.ifLtN 0 43 (.ifLtN 44 41 ivOther (.ifLtN 41 44 ivOther ivSelf)) ivOther)

/-- `r42 := cvn r41`. -/
def cv : Stmt :=
  .seq (block [.addN 20 5 41, .loadN 47 20]) (.ifLtN 47 1 ival (.instr (.copyN 42 0)))

/-- `rOut := phi3 rIn`. -/
def phi (rIn rOut : ℕ) : Stmt :=
  .seq (.instr (.modN 48 rIn 3))
    (.ifLtN 48 2 (.instr (.addN rOut rIn 1)) (.instr (.subN rOut rIn 2)))

/-- One step of the walk from `δ = r50` with inside weight `r51`. -/
def wbody : Stmt :=
  .seq (phi 50 55) <| .seq (.instr (.loadN 41 55)) <| .seq cv <|
  .seq (block [.copyN 56 41, .copyN 57 42]) <| .seq (phi 55 58) <| .seq (.instr (.loadN 41 58)) <|
  .seq cv <|
  .seq (.ifLtN 57 42 (block [.copyN 53 41, .copyN 54 42]) (block [.copyN 53 56, .copyN 54 57])) <|
  .seq (.instr (.mulN 59 54 3)) <|
  .ifLtN 27 59 (block [.copyN 50 53, .copyN 51 54]) (.instr (.copyN 52 1))

/-- The start of the walk. -/
def wstart : Stmt :=
  .seq (block [.addN 27 26 26, .addN 20 9 1, .loadN 60 20, .addN 20 8 60, .loadN 40 20,
    .copyN 41 40]) <| .seq ival <| .seq (.instr (.mulN 59 42 3)) <|
  .ifLtN 27 59 (block [.copyN 50 40, .copyN 51 42, .copyN 52 0, .copyN 61 1])
    (.seq (block [.subN 62 26 42, .mulN 59 62 3])
      (.ifLtN 27 59 (block [.loadN 50 40, .copyN 51 62, .copyN 52 0, .copyN 61 1])
        (block [.copyN 53 40, .copyN 52 1, .copyN 61 0])))

/-- **The walk.** -/
def walk : Stmt := .seq wstart (.whileLtN 52 1 wbody)

/-! ### Specifications -/

section proofs

variable {k : ℕ} {A T Fw : ℕ → ℕ} {W : ℕ} {P : Input}

/-- The facts the walk uses about the state: the map, the stored weights, the total. -/
structure WS (k : ℕ) (A T : ℕ → ℕ) (pdf J : ℕ → ℕ) (tot W : ℕ) (c : Config) : Prop where
  wb : WordsBounded W c
  regs : CRegs k c
  A_m : ∀ x < 3 * k, c.nmem x = A x
  T_m : ∀ x < 3 * k, c.nmem (3 * k + x) = T x
  pd_m : ∀ f < k, c.nmem (8 * k + f) = pdf f
  J_m : ∀ f < k, f ≠ 0 → c.nmem (10 * k + f) = J f
  r26 : c.nreg 26 = tot

variable {pdf J : ℕ → ℕ} {tot : ℕ}

/-- The assumptions of the walk. -/
structure WA (k : ℕ) (A T : ℕ → ℕ) (pdf J : ℕ → ℕ) (tot : ℕ) : Prop where
  tri : Tri k A T
  pdor : ∀ y < 3 * k, T y = 0 → (y / 3 ≠ 0 ∧ pdf (y / 3) = y) ∨ (A y / 3 ≠ 0 ∧ pdf (A y / 3) = A y)
  J_le : ∀ f < k, f ≠ 0 → J f ≤ tot

theorem phi3_lt {y : ℕ} {k : ℕ} (hy : y < 3 * k) : phi3 y < 3 * k := by
  unfold phi3; split_ifs <;> omega

theorem WS.keep {c c' : Config} (h : WS k A T pdf J tot W c) (hw : WordsBounded W c')
    (hr : ∀ r, r ≤ 10 ∨ r = 26 → c'.nreg r = c.nreg r) (hm : c'.nmem = c.nmem) :
    WS k A T pdf J tot W c' :=
  ⟨hw, cregs_of h.regs fun r hr' => hr r (Or.inl hr'), fun x hx => hm ▸ h.A_m x hx,
    fun x hx => hm ▸ h.T_m x hx, fun f hf => hm ▸ h.pd_m f hf, fun f hf h0 => hm ▸ h.J_m f hf h0,
    (hr 26 (Or.inr rfl)).trans h.r26⟩

theorem Inum_le (hA : WA k A T pdf J tot) {y : ℕ} (hy : y < 3 * k) :
    Inum A pdf J tot y ≤ tot := by
  unfold Inum
  split_ifs with h
  · exact hA.J_le _ (by omega) h.1
  · omega

/-- The frame of the helpers: registers other than `r20` and `r42 … r47` are kept. -/
def Fr (c c' : Config) : Prop := ∀ r, (r < 42 ∨ 47 < r) → r ≠ 20 → c'.nreg r = c.nreg r

theorem ivOther_exec (hA : WA k A T pdf J tot) (hW : 11 * k + 3 * tot + 4 ≤ W) (c : Config)
    (hS : WS k A T pdf J tot W c) (hy : c.nreg 41 < 3 * k) (hT : T (c.nreg 41) = 0)
    (hno : ¬ (c.nreg 41 / 3 ≠ 0 ∧ pdf (c.nreg 41 / 3) = c.nreg 41)) :
    ∃ c' k', Exec P W ivOther c c' k' ∧ k' ≤ 5 ∧ (WS k A T pdf J tot W c' ∧ Fr c c' ∧
      c'.nreg 42 = Inum A pdf J tot (c.nreg 41) ∧ c'.output = c.output) := by
  have hc := hS.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hS.regs
  have hAy := hA.tri.A_lt _ hy
  have hAm := hS.A_m _ hy
  have hor := hA.pdor _ hy hT
  have hc0 : A (c.nreg 41) / 3 ≠ 0 := by tauto
  have hJm := hS.J_m (A (c.nreg 41) / 3) (by omega) hc0
  unfold ivOther
  exec_block
  · config_simp; rw [hAm, h3, h10]; omega
  refine ⟨by omega, ?_, fun r hr h20 => ?_, ?_, rfl⟩
  · exact hS.keep ‹_› (fun r hr => by
      rcases hr with hr | rfl
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp) rfl
  · config_simp; simp only [upd_apply]; split_ifs <;> omega
  · config_simp; rw [hAm, h3, h10, hJm, hS.r26]; unfold Inum; rw [ite_eq_right hno]

theorem ival_exec (hA : WA k A T pdf J tot) (hW : 11 * k + 3 * tot + 4 ≤ W) (c : Config)
    (hS : WS k A T pdf J tot W c) (hy : c.nreg 41 < 3 * k) (hT : T (c.nreg 41) = 0) :
    ∃ c' k', Exec P W ival c c' k' ∧ k' ≤ 14 ∧ (WS k A T pdf J tot W c' ∧ Fr c c' ∧
      c'.nreg 42 = Inum A pdf J tot (c.nreg 41) ∧ c'.output = c.output) := by
  have hc := hS.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hS.regs
  have hpdm : c.nmem (c.nreg 8 + c.nreg 41 / c.nreg 3) = pdf (c.nreg 41 / 3) := by
    rw [h8, h3]; exact hS.pd_m _ (by omega)
  unfold ival
  refine spec_seq ?_
  exec_block
  · config_simp; rw [h8, h3]; omega
  config_simp
  -- the state after the first block
  generalize hc₁ : (⟨c.pc, _, c.rreg, c.nmem, c.rmem, c.output⟩ : Config) = c₁
  have hS₁ : WS k A T pdf J tot W c₁ := by
    subst hc₁; exact hS.keep ‹_› (fun r hr => by
      rcases hr with hr | rfl
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp) rfl
  have g41 : c₁.nreg 41 = c.nreg 41 := by subst hc₁; config_simp
  have g43 : c₁.nreg 43 = c.nreg 41 / 3 := by subst hc₁; config_simp; rw [h3]
  have g44 : c₁.nreg 44 = pdf (c.nreg 41 / 3) := by subst hc₁; config_simp; rw [hpdm]
  have g0 : c₁.nreg 0 = 0 := by subst hc₁; config_simp; exact h0
  have gfr : Fr c c₁ := fun r hr h20 => by
    subst hc₁; config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hout₁ : c₁.output = c.output := by subst hc₁; rfl
  have fin : ∀ c', Fr c₁ c' → c'.nreg 42 = Inum A pdf J tot (c₁.nreg 41) →
      c'.output = c₁.output → Fr c c' ∧ c'.nreg 42 = Inum A pdf J tot (c.nreg 41) ∧
        c'.output = c.output := fun c' hfr h42 hout =>
    ⟨fun r hr h20 => (hfr r hr h20).trans (gfr r hr h20), by rw [h42, g41], hout.trans hout₁⟩
  have other : ¬ (c.nreg 41 / 3 ≠ 0 ∧ pdf (c.nreg 41 / 3) = c.nreg 41) →
      ∃ c' k', Exec P W ivOther c₁ c' k' ∧ k' ≤ 5 ∧ (WS k A T pdf J tot W c' ∧ Fr c₁ c' ∧
        c'.nreg 42 = Inum A pdf J tot (c₁.nreg 41) ∧ c'.output = c₁.output) := fun hno =>
    ivOther_exec hA hW c₁ hS₁ (by rw [g41]; exact hy) (by rw [g41]; exact hT)
      (by rw [g41]; exact hno)
  by_cases hcond : c.nreg 41 / 3 ≠ 0 ∧ pdf (c.nreg 41 / 3) = c.nreg 41
  · refine spec_ifLtN_true (by rw [g0, g43]; omega) ?_
    refine spec_ifLtN_false (by rw [g44, g41, hcond.2]; omega) ?_
    refine spec_ifLtN_false (by rw [g44, g41, hcond.2]; omega) ?_
    have hc₁w := hS₁.wb
    obtain ⟨i0, i1, i2, i3, i4, i5, i6, i7, i8, i9, i10⟩ := hS₁.regs
    have hJm := hS.J_m (c.nreg 41 / 3) (by omega) hcond.1
    unfold ivSelf
    exec_block
    · rw [i10, g43]; omega
    have hm₁ : c₁.nmem = c.nmem := by subst hc₁; rfl
    refine ⟨by omega, hS₁.keep ‹_› (fun r hr => by
      rcases hr with hr | rfl
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp) rfl, fin _ (fun r hr h20 => by
        config_simp; simp only [upd_apply]; split_ifs <;> omega) (by
        config_simp; rw [i10, g43, g41, hm₁, hJm]; unfold Inum; rw [ite_eq_left hcond]) rfl⟩
  · have hother := other hcond
    by_cases h43 : 0 < c₁.nreg 43
    · refine spec_ifLtN_true (by rw [g0]; exact h43) ?_
      rcases Nat.lt_trichotomy (c₁.nreg 44) (c₁.nreg 41) with h | h | h
      · refine spec_ifLtN_true h ?_
        obtain ⟨c', k', e', hk', a, b, d, f⟩ := hother
        exact ⟨c', k', e', by omega, a, fin c' b d f⟩
      · exfalso; apply hcond; rw [g43] at h43; rw [g44, g41] at h; exact ⟨by omega, h⟩
      · refine spec_ifLtN_false (by omega) ?_
        refine spec_ifLtN_true h ?_
        obtain ⟨c', k', e', hk', a, b, d, f⟩ := hother
        exact ⟨c', k', e', by omega, a, fin c' b d f⟩
    · refine spec_ifLtN_false (by rw [g0]; exact h43) ?_
      obtain ⟨c', k', e', hk', a, b, d, f⟩ := hother
      exact ⟨c', k', e', by omega, a, fin c' b d f⟩

theorem cv_exec (hA : WA k A T pdf J tot) (hW : 11 * k + 3 * tot + 4 ≤ W) (c : Config)
    (hS : WS k A T pdf J tot W c) (hy : c.nreg 41 < 3 * k) :
    ∃ c' k', Exec P W cv c c' k' ∧ k' ≤ 17 ∧ (WS k A T pdf J tot W c' ∧ Fr c c' ∧
      c'.nreg 42 = cvn A T pdf J tot (c.nreg 41) ∧ c'.output = c.output) := by
  have hc := hS.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hS.regs
  have hTm := hS.T_m _ hy
  have hTle := hA.tri.T_le _ hy
  unfold cv
  refine spec_seq ?_
  exec_block
  · rw [h5]; omega
  config_simp
  generalize hc₁ : (⟨c.pc, _, c.rreg, c.nmem, c.rmem, c.output⟩ : Config) = c₁
  have hS₁ : WS k A T pdf J tot W c₁ := by
    subst hc₁; exact hS.keep ‹_› (fun r hr => by
      rcases hr with hr | rfl
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp) rfl
  have g41 : c₁.nreg 41 = c.nreg 41 := by subst hc₁; config_simp
  have g47 : c₁.nreg 47 = T (c.nreg 41) := by subst hc₁; config_simp; rw [h5, hTm]
  have g1 : c₁.nreg 1 = 1 := by subst hc₁; config_simp; exact h1
  have gfr : Fr c c₁ := fun r hr h20 => by
    subst hc₁; config_simp; simp only [upd_apply]; split_ifs <;> omega
  have hout₁ : c₁.output = c.output := by subst hc₁; rfl
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hTle with hT | hT
  · refine spec_ifLtN_true (by rw [g47, g1, hT]; omega) ?_
    obtain ⟨c', k', e', hk', a, b, d, f⟩ := ival_exec (P := P) hA hW c₁ hS₁ (by rw [g41]; exact hy)
      (by rw [g41]; exact hT)
    refine ⟨c', k', e', by omega, a, fun r hr h20 => (b r hr h20).trans (gfr r hr h20), ?_,
      f.trans hout₁⟩
    rw [d, g41]; unfold cvn; rw [ite_eq_left hT]
  · refine spec_ifLtN_false (by rw [g47, g1, hT]; omega) ?_
    have hc₁w := hS₁.wb
    refine spec_instr (Exec.copyN hc₁w 42 0) fun hw => ?_
    refine ⟨by omega, hS₁.keep hw (fun r hr => by
      rcases hr with hr | rfl
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp) rfl, fun r hr h20 => ?_, ?_, hout₁⟩
    · config_simp; simp only [upd_apply]
      split_ifs
      · omega
      · exact gfr r hr h20
    · config_simp; rw [hS₁.regs.1]; unfold cvn; rw [ite_eq_right (by omega)]

theorem phi_exec {rIn rOut : ℕ} (hIn : rIn ≠ 48) (c : Config)
    (hc : WordsBounded W c) (h1 : c.nreg 1 = 1) (h2 : c.nreg 2 = 2) (h3 : c.nreg 3 = 3)
    (hb : c.nreg rIn + 1 ≤ W) :
    ∃ c' k', Exec P W (phi rIn rOut) c c' k' ∧ k' ≤ 4 ∧ c'.nreg rOut = phi3 (c.nreg rIn) ∧
      (∀ r, r ≠ 48 → r ≠ rOut → c'.nreg r = c.nreg r) ∧ c'.nmem = c.nmem ∧
      c'.output = c.output := by
  unfold phi
  refine spec_seq ?_
  refine spec_instr (Exec.modN hc 48 rIn 3) fun hw => ?_
  have hu : ∀ v, upd c.nreg 48 v rIn = c.nreg rIn := fun v => upd_other _ _ _ hIn
  have hu1 : ∀ v, upd c.nreg 48 v 1 = 1 := fun v => by rw [upd_other _ _ _ (by omega), h1]
  by_cases h : c.nreg rIn % 3 < 2
  · refine spec_ifLtN_true (by config_simp; rw [h2, h3]; exact h) ?_
    refine spec_instr (Exec.addN hw rOut rIn 1 (by simp [hu, h1, hb])) fun hw' => ?_
    refine ⟨by omega, ?_, fun r h48 hr => ?_, rfl, rfl⟩
    · simp [hu, h1, phi3, h]
    · config_simp; rw [upd_other _ _ _ hr, upd_other _ _ _ h48]
  · refine spec_ifLtN_false (by config_simp; rw [h2, h3]; exact h) ?_
    refine spec_instr (Exec.subN hw rOut rIn 2) fun hw' => ?_
    refine ⟨by omega, ?_, fun r h48 hr => ?_, rfl, rfl⟩
    · simp [hu, h2, phi3, h]
    · config_simp; rw [upd_other _ _ _ hr, upd_other _ _ _ h48]

/-- The outcome of the walk: mode `r61 = 0` with the dart `r53`, or mode `1` with the last dart
`r50 = δ` and the dart `r53 = a` (one of the two other darts of the triangle of `δ`, reversed)
with inside weight `r54`. -/
def Good (k : ℕ) (A T Fw pdf J : ℕ → ℕ) (tot : ℕ) (c : Config) : Prop :=
  (c.nreg 61 = 0 ∧ c.nreg 53 < 3 * k ∧ T (c.nreg 53) = 0 ∧
      3 * Inum A pdf J tot (c.nreg 53) ≤ 2 * tot ∧
        3 * (tot - Inum A pdf J tot (c.nreg 53)) ≤ 2 * tot) ∨
    (c.nreg 61 = 1 ∧ c.nreg 50 < 3 * k ∧ T (c.nreg 50) = 0 ∧
      (c.nreg 53 = A (phi3 (c.nreg 50)) ∨ c.nreg 53 = A (phi3 (phi3 (c.nreg 50)))) ∧
      c.nreg 54 = cvn A T pdf J tot (c.nreg 53) ∧ 3 * c.nreg 54 ≤ 2 * tot ∧
      3 * (tot - c.nreg 54 - Fw (c.nreg 50 / 3)) ≤ 2 * tot)

/-- The walk is running from `δ = r50`, heavier than `2/3`. -/
def Running (k : ℕ) (A T pdf J : ℕ → ℕ) (tot : ℕ) (c : Config) : Prop :=
  c.nreg 52 = 0 ∧ c.nreg 61 = 1 ∧ c.nreg 50 < 3 * k ∧ T (c.nreg 50) = 0 ∧
    c.nreg 51 = Inum A pdf J tot (c.nreg 50) ∧ 2 * tot < 3 * c.nreg 51

/-- The state of the walk. -/
structure WI (k : ℕ) (A T Fw pdf J : ℕ → ℕ) (tot W : ℕ) (o : List ℕ) (c : Config) : Prop where
  ws : WS k A T pdf J tot W c
  r27 : c.nreg 27 = 2 * tot
  out : c.output = o
  st : Running k A T pdf J tot c ∨ (c.nreg 52 = 1 ∧ Good k A T Fw pdf J tot c)

/-- The facts on the inside weights which the walk uses. -/
structure WH (k : ℕ) (A T Fw pdf J : ℕ → ℕ) (tot : ℕ) (sz : ℕ → ℕ) : Prop where
  recI : ∀ y < 3 * k, T y = 0 → Inum A pdf J tot y =
    Fw (y / 3) + cvn A T pdf J tot (A (phi3 y)) + cvn A T pdf J tot (A (phi3 (phi3 y)))
  dec₁ : ∀ y < 3 * k, T y = 0 → T (A (phi3 y)) = 0 → sz (A (phi3 y)) < sz y
  dec₂ : ∀ y < 3 * k, T y = 0 → T (A (phi3 (phi3 y))) = 0 → sz (A (phi3 (phi3 y))) < sz y
  comp : ∀ y < 3 * k, T y = 0 → Inum A pdf J tot (A y) + Inum A pdf J tot y = tot
  sz_le : ∀ y < 3 * k, sz y ≤ k

theorem cvn_le (hA : WA k A T pdf J tot) {z : ℕ} (hz : z < 3 * k) : cvn A T pdf J tot z ≤ tot := by
  unfold cvn; split_ifs with h
  · exact Inum_le hA hz
  · omega

theorem wbody_exec {o : List ℕ} {sz : ℕ → ℕ} (hA : WA k A T pdf J tot)
    (hH : WH k A T Fw pdf J tot sz)
    (hW : 11 * k + 3 * tot + 4 ≤ W) (c : Config) (hI : WI k A T Fw pdf J tot W o c)
    (hrun : Running k A T pdf J tot c) :
    ∃ c' k', Exec P W wbody c c' k' ∧ WI k A T Fw pdf J tot W o c' ∧
      (if c'.nreg 52 = 0 then 62 * (sz (c'.nreg 50) + 1) else 0) + k' + 2 ≤
        62 * (sz (c.nreg 50) + 1) := by
  obtain ⟨r52, r61, hδ, hTδ, r51, hheavy⟩ := hrun
  have hS := hI.ws
  have hc := hS.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hS.regs
  generalize hgδ : c.nreg 50 = δ at hδ hTδ r51
  have hφ := phi3_lt hδ
  have hφφ := phi3_lt hφ
  have ha₁ := hA.tri.A_lt _ hφ
  have ha₂ := hA.tri.A_lt _ hφφ
  -- step 1
  obtain ⟨c₁, k₁, e₁, hk₁, g55, f₁, m₁, o₁⟩ := phi_exec (P := P) (rIn := 50) (rOut := 55)
    (by omega) c hc h1 h2 h3 (by omega)
  rw [hgδ] at g55
  have hS₁ : WS k A T pdf J tot W c₁ :=
    hS.keep e₁.wb_right (fun r hr => f₁ r (by omega) (by omega)) m₁
  -- step 2
  have e₂ := Exec.loadN (P := P) e₁.wb_right 41 55
  have hS₂ := hS₁.keep e₂.wb_right (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]) rfl
  have g41 : ({ c₁ with nreg := upd c₁.nreg 41 (c₁.nmem (c₁.nreg 55)) } : Config).nreg 41 =
      A (phi3 δ) := by config_simp; rw [g55, hS₁.A_m _ hφ]
  -- step 3
  obtain ⟨c₃, k₃, e₃, hk₃, hS₃, f₃, g42, o₃⟩ := cv_exec (P := P) hA hW _ hS₂
    (by rw [g41]; exact ha₁)
  rw [g41] at g42
  -- step 4
  obtain ⟨c₄, k₄, e₄, hS₄, g56, g57, f₄, o₄, hk₄⟩ : ∃ c₄ k₄, Exec P W (block [.copyN 56 41,
      .copyN 57 42]) c₃ c₄ k₄ ∧ WS k A T pdf J tot W c₄ ∧ c₄.nreg 56 = c₃.nreg 41 ∧
      c₄.nreg 57 = c₃.nreg 42 ∧ (∀ r, r ≠ 56 → r ≠ 57 → c₄.nreg r = c₃.nreg r) ∧
      c₄.output = c₃.output ∧ k₄ = 2 := by
    have hc₃ := hS₃.wb
    exec_block
    refine ⟨hS₃.keep ‹_› (fun r hr => by
      config_simp; simp only [upd_apply]; split_ifs <;> omega) rfl,
      by config_simp, by config_simp,
      fun r a b => by config_simp; simp only [upd_apply, a, b, ↓reduceIte],
      rfl, rfl⟩
  -- step 5
  have g55' : c₄.nreg 55 = phi3 δ := by
    rw [f₄ 55 (by omega) (by omega), f₃ 55 (by omega) (by omega)]; config_simp; exact g55
  obtain ⟨c₅, k₅, e₅, hk₅, g58, f₅, m₅, o₅⟩ := phi_exec (P := P) (rIn := 55) (rOut := 58)
    (by omega) c₄ hS₄.wb hS₄.regs.2.1 hS₄.regs.2.2.1 hS₄.regs.2.2.2.1
    (by rw [g55']; omega)
  rw [g55'] at g58
  have hS₅ : WS k A T pdf J tot W c₅ :=
    hS₄.keep e₅.wb_right (fun r hr => f₅ r (by omega) (by omega)) m₅
  -- step 6
  have e₆ := Exec.loadN (P := P) e₅.wb_right 41 58
  have hS₆ := hS₅.keep e₆.wb_right (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]) rfl
  have g41' : ({ c₅ with nreg := upd c₅.nreg 41 (c₅.nmem (c₅.nreg 58)) } : Config).nreg 41 =
      A (phi3 (phi3 δ)) := by config_simp; rw [g58, hS₅.A_m _ hφφ]
  -- step 7
  obtain ⟨c₇, k₇, e₇, hk₇, hS₇, f₇, g42', o₇⟩ := cv_exec (P := P) hA hW _ hS₆
    (by rw [g41']; exact ha₂)
  rw [g41'] at g42'
  -- the values
  have v41 : c₇.nreg 41 = A (phi3 (phi3 δ)) := by
    rw [f₇ 41 (by omega) (by omega)]; exact g41'
  have v56 : c₇.nreg 56 = A (phi3 δ) := by
    rw [f₇ 56 (by omega) (by omega)]; config_simp; rw [f₅ 56 (by omega) (by omega), g56,
      f₃ 41 (by omega) (by omega), g41]
  have v57 : c₇.nreg 57 = cvn A T pdf J tot (A (phi3 δ)) := by
    rw [f₇ 57 (by omega) (by omega)]; config_simp; rw [f₅ 57 (by omega) (by omega), g57, g42]
  have keep₇ : ∀ r, r ≤ 10 ∨ r = 26 ∨ r = 27 ∨ r = 50 ∨ r = 52 ∨ r = 61 → c₇.nreg r = c.nreg r := by
    intro r hr
    rw [f₇ r (by omega) (by omega)]; config_simp
    rw [upd_other _ _ _ (by omega), f₅ r (by omega) (by omega), f₄ r (by omega) (by omega),
      f₃ r (by omega) (by omega)]; config_simp
    rw [upd_other _ _ _ (by omega), f₁ r (by omega) (by omega)]
  have hout₇ : c₇.output = c.output := by
    rw [o₇]; config_simp; rw [o₅, o₄, o₃]; config_simp; rw [o₁]
  have hc₇ := hS₇.wb
  have hI₁ := cvn_le hA ha₁
  have hI₂ := cvn_le hA ha₂
  have hrec := hH.recI δ hδ hTδ
  -- step 8: the heavier
  obtain ⟨c₈, k₈, e₈, hS₈, g53, g54, f₈, o₈, hk₈⟩ : ∃ c₈ k₈, Exec P W (.ifLtN 57 42
      (block [.copyN 53 41, .copyN 54 42]) (block [.copyN 53 56, .copyN 54 57])) c₇ c₈ k₈ ∧
      WS k A T pdf J tot W c₈ ∧
      ((c₈.nreg 53 = A (phi3 (phi3 δ)) ∧ c₈.nreg 54 = cvn A T pdf J tot (A (phi3 (phi3 δ))) ∧
          cvn A T pdf J tot (A (phi3 δ)) < cvn A T pdf J tot (A (phi3 (phi3 δ)))) ∨
        (c₈.nreg 53 = A (phi3 δ) ∧ c₈.nreg 54 = cvn A T pdf J tot (A (phi3 δ)) ∧
          cvn A T pdf J tot (A (phi3 (phi3 δ))) ≤ cvn A T pdf J tot (A (phi3 δ)))) ∧
      True ∧ (∀ r, r ≠ 53 → r ≠ 54 → c₈.nreg r = c₇.nreg r) ∧ c₈.output = c₇.output ∧ k₈ ≤ 4 := by
    by_cases hlt : c₇.nreg 57 < c₇.nreg 42
    · refine spec_ifLtN_true hlt ?_
      exec_block
      refine ⟨hS₇.keep ‹_› (fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> omega) rfl,
        Or.inl ⟨by config_simp; exact v41, by config_simp; exact g42',
        by rw [← v57, ← g42']; exact hlt⟩,
        trivial, fun r a b => by config_simp; simp only [upd_apply, a, b, ↓reduceIte],
      rfl, by omega⟩
    · refine spec_ifLtN_false hlt ?_
      exec_block
      refine ⟨hS₇.keep ‹_› (fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> omega) rfl,
        Or.inr ⟨by config_simp; exact v56, by config_simp; exact v57, by rw [← v57, ← g42']; omega⟩,
        trivial, fun r a b => by config_simp; simp only [upd_apply, a, b, ↓reduceIte],
      rfl, by omega⟩
  have hIa : c₈.nreg 54 ≤ tot := by rcases g53 with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> rw [h] <;> assumption
  have k₈r : ∀ r, r ≤ 10 ∨ r = 26 ∨ r = 27 ∨ r = 50 ∨ r = 52 ∨ r = 61 → c₈.nreg r = c.nreg r :=
    fun r hr => (f₈ r (by omega) (by omega)).trans (keep₇ r hr)
  have hc₈ := hS₈.wb
  have g3 : c₈.nreg 3 = 3 := (k₈r 3 (by omega)).trans h3
  -- step 9
  have e₉ := Exec.mulN (P := P) hc₈ 59 54 3 (by rw [g3]; omega)
  -- step 10
  have g27 : c₈.nreg 27 = 2 * tot := (k₈r 27 (by omega)).trans hI.r27
  have gδ : c₈.nreg 50 = δ := (k₈r 50 (by omega)).trans hgδ
  have g52 : c₈.nreg 52 = 0 := (k₈r 52 (by omega)).trans r52
  have g61 : c₈.nreg 61 = 1 := (k₈r 61 (by omega)).trans r61
  have g1 : c₈.nreg 1 = 1 := (k₈r 1 (by omega)).trans h1
  have hS₉ := hS₈.keep e₉.wb_right (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]) rfl
  have hw₉ := e₉.wb_right
  have hpre : ∀ (c₁₀ : Config) (k₁₀ : ℕ), Exec P W
      (.ifLtN 27 59 (block [.copyN 50 53, .copyN 51 54])
      (.instr (.copyN 52 1))) { c₈ with nreg := upd c₈.nreg 59 (c₈.nreg 54 * c₈.nreg 3) } c₁₀ k₁₀ →
      Exec P W wbody c c₁₀ (k₁ + (1 + (k₃ + (k₄ + (k₅ + (1 + (k₇ + (k₈ + (1 + k₁₀))))))))) :=
    fun c₁₀ k₁₀ e₁₀ => .seq e₁ (.seq e₂ (.seq e₃ (.seq e₄ (.seq e₅ (.seq e₆ (.seq e₇ (.seq e₈
      (.seq e₉ e₁₀))))))))
  by_cases hcont : 2 * tot < 3 * c₈.nreg 54
  · -- continue from `a`
    have hT : T (c₈.nreg 53) = 0 := by
      by_contra hT
      rcases g53 with ⟨a, b, -⟩ | ⟨a, b, -⟩ <;>
      · rw [a] at hT; rw [b] at hcont; unfold cvn at hcont; rw [ite_eq_right hT] at hcont; omega
    have ha : c₈.nreg 53 < 3 * k := by rcases g53 with ⟨a, -⟩ | ⟨a, -⟩ <;> rw [a] <;> assumption
    have hval : c₈.nreg 54 = Inum A pdf J tot (c₈.nreg 53) := by
      rcases g53 with ⟨a, b, -⟩ | ⟨a, b, -⟩ <;> rw [b, ← a] <;> unfold cvn <;> rw [ite_eq_left hT]
    have hsz : sz (c₈.nreg 53) < sz δ := by
      rcases g53 with ⟨a, -⟩ | ⟨a, -⟩
      · rw [a] at hT ⊢; exact hH.dec₂ δ hδ hTδ hT
      · rw [a] at hT ⊢; exact hH.dec₁ δ hδ hTδ hT
    obtain ⟨c₁₀, k₁₀, e₁₀, hS₁₀, q50, q51, q52, q61, q27, o₁₀, hk₁₀⟩ : ∃ c₁₀ k₁₀, Exec P W
        (.ifLtN 27 59 (block [.copyN 50 53, .copyN 51 54]) (.instr (.copyN 52 1)))
        { c₈ with nreg := upd c₈.nreg 59 (c₈.nreg 54 * c₈.nreg 3) } c₁₀ k₁₀ ∧
        WS k A T pdf J tot W c₁₀ ∧ c₁₀.nreg 50 = c₈.nreg 53 ∧ c₁₀.nreg 51 = c₈.nreg 54 ∧
        c₁₀.nreg 52 = 0 ∧ c₁₀.nreg 61 = 1 ∧ c₁₀.nreg 27 = 2 * tot ∧ c₁₀.output = c₈.output ∧
        k₁₀ = 3 := by
      refine spec_ifLtN_true (by config_simp; rw [g27, g3]; omega) ?_
      exec_block
      exact ⟨hS₉.keep ‹_› (fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> omega) rfl,
        by config_simp, by config_simp, by config_simp; exact g52, by config_simp; exact g61,
        by config_simp; exact g27, rfl, rfl⟩
    refine ⟨c₁₀, _, hpre c₁₀ k₁₀ e₁₀, ⟨hS₁₀, q27, by rw [o₁₀, o₈, hout₇]; exact hI.out,
      Or.inl ⟨q52, q61, by rw [q50]; exact ha, by rw [q50]; exact hT, by rw [q51, q50]; exact hval,
        by rw [q51]; exact hcont⟩⟩, ?_⟩
    rw [q52, ite_eq_left rfl, q50]
    omega
  · -- stop
    obtain ⟨c₁₀, k₁₀, e₁₀, hS₁₀, q50, q52, q53, q54, q61, q27, o₁₀, hk₁₀⟩ : ∃ c₁₀ k₁₀, Exec P W
        (.ifLtN 27 59 (block [.copyN 50 53, .copyN 51 54]) (.instr (.copyN 52 1)))
        { c₈ with nreg := upd c₈.nreg 59 (c₈.nreg 54 * c₈.nreg 3) } c₁₀ k₁₀ ∧
        WS k A T pdf J tot W c₁₀ ∧ c₁₀.nreg 50 = δ ∧ c₁₀.nreg 52 = 1 ∧
        c₁₀.nreg 53 = c₈.nreg 53 ∧ c₁₀.nreg 54 = c₈.nreg 54 ∧ c₁₀.nreg 61 = 1 ∧
        c₁₀.nreg 27 = 2 * tot ∧ c₁₀.output = c₈.output ∧ k₁₀ = 3 := by
      refine spec_ifLtN_false (by config_simp; rw [g27, g3]; omega) ?_
      refine spec_instr (Exec.copyN hw₉ 52 1) fun hw => ?_
      exact ⟨hS₉.keep hw (fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> omega) rfl,
        by config_simp; exact gδ, by config_simp; exact g1, by config_simp, by config_simp,
        by config_simp; exact g61, by config_simp; exact g27, rfl, rfl⟩
    have hrδ := r51 ▸ hheavy
    refine ⟨c₁₀, _, hpre c₁₀ k₁₀ e₁₀, ⟨hS₁₀, q27, by rw [o₁₀, o₈, hout₇]; exact hI.out,
      Or.inr ⟨q52, Or.inr ⟨q61, by rw [q50]; exact hδ, by rw [q50]; exact hTδ,
        ?_, ?_, ?_, ?_⟩⟩⟩, ?_⟩
    · rw [q53, q50]; rcases g53 with ⟨a, -⟩ | ⟨a, -⟩
      · exact Or.inr a
      · exact Or.inl a
    · rw [q54, q53]; rcases g53 with ⟨a, b, -⟩ | ⟨a, b, -⟩ <;> rw [a, b]
    · rw [q54]; omega
    · rw [q54, q50]
      rcases g53 with ⟨-, b, c'⟩ | ⟨-, b, c'⟩ <;> omega
    · rw [q52]; simp only [show (1 : ℕ) ≠ 0 by omega, ite_false]
      omega

theorem wstart_exec {o : List ℕ} {sz : ℕ → ℕ} (hA : WA k A T pdf J tot)
    (hH : WH k A T Fw pdf J tot sz) (hW : 11 * k + 3 * tot + 4 ≤ W) (c : Config)
    (hS : WS k A T pdf J tot W c) (ho : c.output = o) (hq1 : c.nmem (9 * k + 1) < k)
    (hd0 : pdf (c.nmem (9 * k + 1)) < 3 * k) (hT0 : T (pdf (c.nmem (9 * k + 1))) = 0) :
    ∃ c' k', Exec P W wstart c c' k' ∧ WI k A T Fw pdf J tot W o c' ∧ k' ≤ 34 := by
  have hc := hS.wb
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := hS.regs
  generalize hgq : c.nmem (9 * k + 1) = q at hq1 hd0 hT0
  have hpdm := hS.pd_m q hq1
  have hI0 := Inum_le hA hd0
  obtain ⟨c₁, k₁, e₁, hS₁, g27, g40, g41, g1, g3, g26, o₁, hk₁⟩ : ∃ c₁ k₁, Exec P W
      (block [.addN 27 26 26, .addN 20 9 1, .loadN 60 20, .addN 20 8 60, .loadN 40 20,
        .copyN 41 40])
      c c₁ k₁ ∧ WS k A T pdf J tot W c₁ ∧ c₁.nreg 27 = 2 * tot ∧ c₁.nreg 40 = pdf q ∧
      c₁.nreg 41 = pdf q ∧ c₁.nreg 1 = 1 ∧ c₁.nreg 3 = 3 ∧ c₁.nreg 26 = tot ∧
      c₁.output = c.output ∧ k₁ = 6 := by
    exec_block
    · rw [hS.r26]; omega
    · config_simp; rw [h9, h1]; omega
    · config_simp; rw [h9, h1, h8, hgq]; omega
    refine ⟨hS.keep ‹_› (fun r hr => by
      rcases hr with hr | rfl
      · config_simp; simp only [upd_apply]; split_ifs <;> omega
      · config_simp) rfl, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl⟩
    all_goals config_simp
    · rw [hS.r26]; omega
    · rw [h9, h1, hgq, h8, hpdm]
    · rw [h9, h1, hgq, h8, hpdm]
    · exact h1
    · exact h3
    · exact hS.r26
  obtain ⟨c₂, k₂, e₂, hk₂, hS₂, f₂, g42, o₂⟩ := ival_exec (P := P) hA hW c₁ hS₁
    (by rw [g41]; exact hd0) (by rw [g41]; exact hT0)
  rw [g41] at g42
  have hc₂ := hS₂.wb
  have q27 : c₂.nreg 27 = 2 * tot := (f₂ 27 (by omega) (by omega)).trans g27
  have q40 : c₂.nreg 40 = pdf q := (f₂ 40 (by omega) (by omega)).trans g40
  have q3 : c₂.nreg 3 = 3 := (f₂ 3 (by omega) (by omega)).trans g3
  have q1 : c₂.nreg 1 = 1 := (f₂ 1 (by omega) (by omega)).trans g1
  have q0 : c₂.nreg 0 = 0 := hS₂.regs.1
  have q26 : c₂.nreg 26 = tot := hS₂.r26
  have e₃ := Exec.mulN (P := P) hc₂ 59 42 3 (by rw [g42, q3]; omega)
  have hS₃ := hS₂.keep e₃.wb_right (fun r hr => by config_simp; rw [upd_other _ _ _ (by omega)]) rfl
  have hw₃ := e₃.wb_right
  have hout : c₂.output = o := by rw [o₂, o₁, ho]
  have hpre : ∀ (c₄ : Config) (k₄ : ℕ), Exec P W (.ifLtN 27 59
      (block [.copyN 50 40, .copyN 51 42, .copyN 52 0, .copyN 61 1])
      (.seq (block [.subN 62 26 42, .mulN 59 62 3])
        (.ifLtN 27 59 (block [.loadN 50 40, .copyN 51 62, .copyN 52 0, .copyN 61 1])
          (block [.copyN 53 40, .copyN 52 1, .copyN 61 0]))))
      { c₂ with nreg := upd c₂.nreg 59 (c₂.nreg 42 * c₂.nreg 3) } c₄ k₄ →
      Exec P W wstart c c₄ (k₁ + (k₂ + (1 + k₄))) :=
    fun c₄ k₄ e₄ => .seq e₁ (.seq e₂ (.seq e₃ e₄))
  have hδ₀A := hA.tri.A_lt _ hd0
  have hTA : T (A (pdf q)) = 0 := by rw [hA.tri.T_A _ hd0]; exact hT0
  have hcomp := hH.comp _ hd0 hT0
  have hδ₀m : c₂.nmem (pdf q) = A (pdf q) := hS₂.A_m _ hd0
  have keepw : ∀ c' : Config, WordsBounded W c' →
      (∀ r, r ≤ 10 ∨ r = 26 → c'.nreg r =
        ({ c₂ with nreg := upd c₂.nreg 59 (c₂.nreg 42 * c₂.nreg 3) } : Config).nreg r) →
      c'.nmem = c₂.nmem → WS k A T pdf J tot W c' := fun c' hw hr hm => hS₃.keep hw hr hm
  obtain ⟨c₄, k₄, e₄, hWI, hk₄⟩ : ∃ c₄ k₄, Exec P W (.ifLtN 27 59
      (block [.copyN 50 40, .copyN 51 42, .copyN 52 0, .copyN 61 1])
      (.seq (block [.subN 62 26 42, .mulN 59 62 3])
        (.ifLtN 27 59 (block [.loadN 50 40, .copyN 51 62, .copyN 52 0, .copyN 61 1])
          (block [.copyN 53 40, .copyN 52 1, .copyN 61 0]))))
      { c₂ with nreg := upd c₂.nreg 59 (c₂.nreg 42 * c₂.nreg 3) } c₄ k₄ ∧
      WI k A T Fw pdf J tot W o c₄ ∧ k₄ ≤ 12 := by
    by_cases hh : 2 * tot < 3 * Inum A pdf J tot (pdf q)
    · refine spec_ifLtN_true (by config_simp; rw [q27, g42, q3]; omega) ?_
      exec_block
      refine ⟨⟨keepw _ ‹_› (fun r hr => by
        config_simp; simp only [upd_apply]; split_ifs <;> omega) rfl,
        ?_, hout, Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, by omega⟩
      all_goals config_simp
      · exact q27
      · exact q0
      · exact q1
      · rw [q40]; exact hd0
      · rw [q40]; exact hT0
      · rw [g42, q40]
      · rw [g42]; exact hh
    · refine spec_ifLtN_false (by config_simp; rw [q27, g42, q3]; omega) ?_
      refine spec_seq ?_
      exec_block
      · config_simp; rw [q26, g42, q3]; omega
      by_cases hh2 : 2 * tot < 3 * (tot - Inum A pdf J tot (pdf q))
      · refine spec_ifLtN_true (by config_simp; rw [q27, q26, g42, q3]; omega) ?_
        exec_block
        refine ⟨⟨keepw _ ‹_› (fun r hr => by
          config_simp; simp only [upd_apply]; split_ifs <;> omega) rfl,
          ?_, hout, Or.inl ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩, by omega⟩
        all_goals config_simp
        · exact q27
        · exact q0
        · exact q1
        · rw [q40, hδ₀m]; exact hδ₀A
        · rw [q40, hδ₀m]; exact hTA
        · rw [q40, hδ₀m, q26, g42]; omega
        · rw [q26, g42]; exact hh2
      · refine spec_ifLtN_false (by config_simp; rw [q27, q26, g42, q3]; omega) ?_
        exec_block
        refine ⟨⟨keepw _ ‹_› (fun r hr => by
          config_simp; simp only [upd_apply]; split_ifs <;> omega) rfl,
          ?_, hout, Or.inr ⟨?_, Or.inl ⟨?_, ?_, ?_, ?_, ?_⟩⟩⟩, by omega⟩
        all_goals config_simp
        · exact q27
        · exact q1
        · exact q0
        · rw [q40]; exact hd0
        · rw [q40]; exact hT0
        · rw [q40]; omega
        · rw [q40]; omega
  exact ⟨c₄, _, hpre c₄ k₄ e₄, hWI, by omega⟩

/-- **The walk.** From a state holding the map, the stored inside weights and the total, with
the dart `pd` of the second face found off the tree, the walk ends in the outcome `Good`, within
`62 k + 98` steps. -/
theorem walk_exec {o : List ℕ} {sz : ℕ → ℕ} (hA : WA k A T pdf J tot)
    (hH : WH k A T Fw pdf J tot sz) (hW : 11 * k + 3 * tot + 4 ≤ W) (c : Config)
    (hS : WS k A T pdf J tot W c) (ho : c.output = o) (hq1 : c.nmem (9 * k + 1) < k)
    (hd0 : pdf (c.nmem (9 * k + 1)) < 3 * k) (hT0 : T (pdf (c.nmem (9 * k + 1))) = 0) :
    ∃ c' k', Exec P W walk c c' k' ∧ WS k A T pdf J tot W c' ∧ c'.output = o ∧
      Good k A T Fw pdf J tot c' ∧ k' ≤ 62 * k + 98 := by
  obtain ⟨c₁, k₁, e₁, hI₁, hk₁⟩ := wstart_exec (P := P) hA hH hW c hS ho hq1 hd0 hT0
  obtain ⟨c', k', e, hI', hn, hk'⟩ := Exec.whileLtN_potential (P := P) (W := W) (a := 52) (b := 1)
    (body := wbody) (WI k A T Fw pdf J tot W o)
    (fun c => if c.nreg 52 = 0 then 62 * (sz (c.nreg 50) + 1) else 0) (fun c h => h.ws.wb)
    (fun c hc hlt => by
      have hrun : Running k A T pdf J tot c := by
        rcases hc.st with h | ⟨h, -⟩
        · exact h
        · rw [h, hc.ws.regs.2.1] at hlt; omega
      obtain ⟨c₂, k₂, e₂, hI₂, hΦ⟩ := wbody_exec (P := P) hA hH hW c hc hrun
      exact ⟨c₂, k₂, e₂, hI₂, by rw [ite_eq_left hrun.1]; exact hΦ⟩) hI₁
  have hgood : Good k A T Fw pdf J tot c' := by
    rcases hI'.st with h | ⟨-, h⟩
    · rw [h.1, hI'.ws.regs.2.1] at hn; omega
    · exact h
  refine ⟨c', k₁ + k', .seq e₁ e, hI'.ws, hI'.out, hgood, ?_⟩
  have : (if c₁.nreg 52 = 0 then 62 * (sz (c₁.nreg 50) + 1) else 0) ≤ 62 * (k + 1) := by
    split_ifs with h
    · rcases hI₁.st with h' | ⟨h', -⟩
      · have := hH.sz_le _ h'.2.2.1; omega
      · omega
    · omega
  omega

end proofs

end CycleSearch

end PlanarSeparator
