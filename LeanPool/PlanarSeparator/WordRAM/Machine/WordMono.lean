/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.WordRAM.Machine.Structured

/-!
# Word-bound monotonicity and embedding of structured runs

* `Exec.mono_W`: an execution with word bound `W` is one with any `W' ≥ W` (the word bound is
  a side condition on the visited configurations, `WordsBounded`, never a fault of the machine).
* **Embedding** (`Exec.embed`, `Exec.lift`, `Exec.lift_trunc`). A statement `s` whose
  instructions name only registers `< R` and use neither `inputSize` nor `rand`
  (`Stmt.regsOK R s`) and that runs `Exec P W s c c' k` can be run inside a larger
  configuration `d`: it suffices that `d` agrees with `c` on the registers `< R` and on the
  memory cells at addresses `≤ W` (`Agree R W c d`). Every address the run touches is a natural
  register value of a configuration bounded by `W`, hence `≤ W`; so the cells above `W` and the
  registers `≥ R` of `d` are never read and are kept (`Keep`), the run of `d` ends in a
  configuration agreeing with `c'` in the same sense, and the word bound becomes any
  `W' ≥ W` bounding `d`. The input `P'` of the outer run is arbitrary.
* **Input in memory** (`Stmt.toMem rb tmp`): every `readIn r a` replaced by
  `tmp := a + rb; r := nmem tmp`. If the input words `P.data.getD i 0`, `i ≤ W`, sit in memory at
  `β + i` with `W < β` and the base `β` in the register `rb` (`InData`), the transformed
  statement runs from `d` as `s` runs from `c` on the input `P`, within at most twice the steps
  (exactly the same number when `s` has no `readIn`, in which case `s.toMem rb tmp = s`). Only
  the register `tmp` (`≥ R`) is clobbered in addition.
* `trunc R W d`: the configuration `d` cut to its registers `< R` and its memory `≤ W` (the rest
  zero); `Agree R W (trunc R W d) d`, so a realization proved from any configuration holding
  its input can be applied to `trunc R W d` and lifted to `d` (`Exec.lift_trunc`).
-/

namespace WordRAM

namespace Instr

@[expose] public section

/-- The register indices (natural or real) named by an instruction. -/
def regs : Instr → List ℕ
  | .halt => []
  | .inputSize r => [r]
  | .constN r _ => [r]
  | .copyN r a => [r, a]
  | .addN r a b => [r, a, b]
  | .subN r a b => [r, a, b]
  | .mulN r a b => [r, a, b]
  | .divN r a b => [r, a, b]
  | .modN r a b => [r, a, b]
  | .loadN r a => [r, a]
  | .storeN a r => [a, r]
  | .constR r _ => [r]
  | .copyR r a => [r, a]
  | .addR r a b => [r, a, b]
  | .subR r a b => [r, a, b]
  | .mulR r a b => [r, a, b]
  | .divR r a b => [r, a, b]
  | .loadR r a => [r, a]
  | .storeR a r => [a, r]
  | .readIn r a => [r, a]
  | .rand r a => [r, a]
  | .jump _ => []
  | .brLtN a b _ => [a, b]
  | .brLtR a b _ => [a, b]
  | .outN a => [a]

/-- The instruction reads no input word and not the input size (`readIn`, `inputSize`). -/
def notInp : Instr → Bool
  | .readIn _ _ => false
  | .inputSize _ => false
  | _ => true

/-- The instruction is not `rand`. -/
def noRand : Instr → Bool
  | .rand _ _ => false
  | _ => true

/-- Every register named by the instruction satisfies `U`. -/
def regsOK (U : ℕ → Bool) (i : Instr) : Bool := i.regs.all U

end

end Instr

namespace Machine

namespace Stmt

@[expose] public section

/-- Every register named by the statement (instructions and tests) satisfies `U`. -/
def regsOK (U : ℕ → Bool) : Stmt → Bool
  | .skip => true
  | .instr i => i.regsOK U
  | .seq s t => regsOK U s && regsOK U t
  | .ifLtN a b t e => U a && U b && regsOK U t && regsOK U e
  | .ifLtR a b t e => U a && U b && regsOK U t && regsOK U e
  | .whileLtN a b body => U a && U b && regsOK U body
  | .whileLtR a b body => U a && U b && regsOK U body

/-- No `readIn` and no `inputSize` in the statement. -/
def noInp : Stmt → Bool
  | .skip => true
  | .instr i => i.notInp
  | .seq s t => noInp s && noInp t
  | .ifLtN _ _ t e => noInp t && noInp e
  | .ifLtR _ _ t e => noInp t && noInp e
  | .whileLtN _ _ body => noInp body
  | .whileLtR _ _ body => noInp body

/-- No `rand` in the statement. -/
def noRand : Stmt → Bool
  | .skip => true
  | .instr i => i.noRand
  | .seq s t => noRand s && noRand t
  | .ifLtN _ _ t e => noRand t && noRand e
  | .ifLtR _ _ t e => noRand t && noRand e
  | .whileLtN _ _ body => noRand body
  | .whileLtR _ _ body => noRand body

/-- One instruction with the input read from memory: `readIn r a` becomes
`tmp := β; tmp := tmp + a; r := nmem tmp`, and `inputSize r` becomes `r := len`. -/
def instrToMem (tmp β len : ℕ) : Instr → Stmt
  | .readIn r a =>
    .seq (.instr (.constN tmp β)) (.seq (.instr (.addN tmp tmp a)) (.instr (.loadN r tmp)))
  | .inputSize r => .instr (.constN r len)
  | i => .instr i

/-- The statement with the input read from memory at base `β` (through the scratch register
`tmp`) and the input size `len` (`instrToMem`). -/
def toMem (tmp β len : ℕ) : Stmt → Stmt
  | .skip => .skip
  | .instr i => instrToMem tmp β len i
  | .seq s t => .seq (toMem tmp β len s) (toMem tmp β len t)
  | .ifLtN a b t e => .ifLtN a b (toMem tmp β len t) (toMem tmp β len e)
  | .ifLtR a b t e => .ifLtR a b (toMem tmp β len t) (toMem tmp β len e)
  | .whileLtN a b body => .whileLtN a b (toMem tmp β len body)
  | .whileLtR a b body => .whileLtR a b (toMem tmp β len body)

/-- With the trivial predicate the register condition holds. -/
theorem regsOK_true (s : Stmt) : s.regsOK (fun _ => true) = true := by
  induction s with
  | skip => rfl
  | instr i => exact List.all_eq_true.2 fun _ _ => rfl
  | seq s t ihs iht => simp only [regsOK, ihs, iht, Bool.and_self]
  | ifLtN a b t e iht ihe => simp only [regsOK, iht, ihe, Bool.and_self]
  | ifLtR a b t e iht ihe => simp only [regsOK, iht, ihe, Bool.and_self]
  | whileLtN a b body ih => simp only [regsOK, ih, Bool.and_self]
  | whileLtR a b body ih => simp only [regsOK, ih, Bool.and_self]

@[simp] theorem regsOK_block (U : ℕ → Bool) (l : List Instr) :
    regsOK U (block l) = l.all (Instr.regsOK U) := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [block, regsOK, ih, List.all_cons]

@[simp] theorem noInp_block (l : List Instr) : noInp (block l) = l.all Instr.notInp := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [block, noInp, ih, List.all_cons]

@[simp] theorem noRand_block (l : List Instr) : noRand (block l) = l.all Instr.noRand := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [block, noRand, ih, List.all_cons]

theorem instrToMem_of_notInp {tmp β len : ℕ} {i : Instr} (h : i.notInp = true) :
    instrToMem tmp β len i = .instr i := by
  cases i <;> first | rfl | simp [Instr.notInp] at h

/-- Without `readIn` and `inputSize` the transformation does nothing. -/
theorem toMem_of_noInp {tmp β len : ℕ} {s : Stmt} (h : s.noInp = true) :
    s.toMem tmp β len = s := by
  induction s with
  | skip => rfl
  | instr i => exact instrToMem_of_notInp h
  | seq s t ihs iht =>
    simp only [noInp, Bool.and_eq_true] at h; simp only [toMem, ihs h.1, iht h.2]
  | ifLtN a b t e iht ihe =>
    simp only [noInp, Bool.and_eq_true] at h; simp only [toMem, iht h.1, ihe h.2]
  | ifLtR a b t e iht ihe =>
    simp only [noInp, Bool.and_eq_true] at h; simp only [toMem, iht h.1, ihe h.2]
  | whileLtN a b body ih => simp only [noInp] at h; simp only [toMem, ih h]
  | whileLtR a b body ih => simp only [noInp] at h; simp only [toMem, ih h]

end

end Stmt

open Stmt

@[expose] public section

/-! ### Monotonicity in the word bound -/

namespace Exec

variable {P : Input} {W : ℕ}

/-- **Word-bound monotonicity.** -/
theorem mono_W {s : Stmt} {c c' : Config} {k W' : ℕ} (h : Exec P W s c c' k) (hW : W ≤ W') :
    Exec P W' s c c' k := by
  induction h with
  | skip hw => exact .skip (WordsBounded.mono hw hW)
  | instr hs he hw hw' => exact .instr hs he (WordsBounded.mono hw hW) (WordsBounded.mono hw' hW)
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true ht _ ih => exact .ifLtN_true ht ih
  | ifLtN_false ht _ ih => exact .ifLtN_false ht ih
  | ifLtR_true ht _ ih => exact .ifLtR_true ht ih
  | ifLtR_false ht _ ih => exact .ifLtR_false ht ih
  | whileLtN_false ht hw => exact .whileLtN_false ht (WordsBounded.mono hw hW)
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ht ih₁ ih₂
  | whileLtR_false ht hw => exact .whileLtR_false ht (WordsBounded.mono hw hW)
  | whileLtR_true ht _ _ ih₁ ih₂ => exact .whileLtR_true ht ih₁ ih₂

end Exec

/-! ### Agreement, frames, truncation -/

/-- `d` agrees with `c` on the registers satisfying `U` and on the memory cells at addresses
`≤ W`. -/
structure Agree (U : ℕ → Bool) (W : ℕ) (c d : Config) : Prop where
  nreg : ∀ r, U r = true → d.nreg r = c.nreg r
  rreg : ∀ r, U r = true → d.rreg r = c.rreg r
  nmem : ∀ a ≤ W, d.nmem a = c.nmem a
  rmem : ∀ a ≤ W, d.rmem a = c.rmem a

/-- The frame of an embedded run: the registers outside `U` and the memory cells above `W` are
unchanged. -/
structure Keep (U : ℕ → Bool) (W : ℕ) (d d' : Config) : Prop where
  nreg : ∀ r, U r = false → d'.nreg r = d.nreg r
  rreg : ∀ r, U r = false → d'.rreg r = d.rreg r
  nmem : ∀ a, W < a → d'.nmem a = d.nmem a
  rmem : ∀ a, W < a → d'.rmem a = d.rmem a

theorem Keep.refl (U : ℕ → Bool) (W : ℕ) (d : Config) : Keep U W d d :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

theorem Keep.trans {U : ℕ → Bool} {W : ℕ} {d d₁ d₂ : Config} (h : Keep U W d d₁)
    (h' : Keep U W d₁ d₂) : Keep U W d d₂ :=
  ⟨fun r hr => by rw [h'.nreg r hr, h.nreg r hr], fun r hr => by rw [h'.rreg r hr, h.rreg r hr],
    fun a ha => by rw [h'.nmem a ha, h.nmem a ha], fun a ha => by rw [h'.rmem a ha, h.rmem a ha]⟩

/-- The frame of an embedded run with a scratch register `tmp`: the registers outside `U`
(and `tmp` too when `ro`) and the memory cells above `W` are unchanged. -/
structure KeepT (U : ℕ → Bool) (W tmp : ℕ) (ro : Bool) (d d' : Config) : Prop where
  nreg : ∀ r, U r = false → (r = tmp → ro = true) → d'.nreg r = d.nreg r
  rreg : ∀ r, U r = false → d'.rreg r = d.rreg r
  nmem : ∀ a, W < a → d'.nmem a = d.nmem a
  rmem : ∀ a, W < a → d'.rmem a = d.rmem a

theorem Keep.toT {U : ℕ → Bool} {W : ℕ} {d d' : Config} (h : Keep U W d d') (tmp : ℕ)
    (ro : Bool) : KeepT U W tmp ro d d' :=
  ⟨fun r hr _ => h.nreg r hr, h.rreg, h.nmem, h.rmem⟩

theorem KeepT.trans {U : ℕ → Bool} {W tmp : ℕ} {ro ro' : Bool} {d d₁ d₂ : Config}
    (h : KeepT U W tmp ro d d₁) (h' : KeepT U W tmp ro' d₁ d₂) : KeepT U W tmp (ro && ro') d d₂ :=
  ⟨fun r hr ht => by
      simp only [Bool.and_eq_true] at ht
      rw [h'.nreg r hr (fun e => (ht e).2), h.nreg r hr (fun e => (ht e).1)],
    fun r hr => by rw [h'.rreg r hr, h.rreg r hr],
    fun a ha => by rw [h'.nmem a ha, h.nmem a ha], fun a ha => by rw [h'.rmem a ha, h.rmem a ha]⟩

theorem KeepT.weaken {U : ℕ → Bool} {W tmp : ℕ} {ro ro' : Bool} {d d' : Config}
    (h : KeepT U W tmp ro d d') (hro : ro' = true → ro = true) : KeepT U W tmp ro' d d' :=
  ⟨fun r hr ht => h.nreg r hr (fun e => hro (ht e)), h.rreg, h.nmem, h.rmem⟩

/-- The input words `P.data.getD i 0`, `i ≤ W`, at `β + i`, with `W < β`, `β + W ≤ W'`, and
`len` the number of input words. -/
structure InData (P : Input) (W β len W' : ℕ) (d : Config) : Prop where
  lt : W < β
  le : β + W ≤ W'
  len : len = P.data.length
  mem : ∀ i ≤ W, d.nmem (β + i) = P.data.getD i 0

/-- The configuration `d` cut to its registers satisfying `U` and its memory at addresses
`≤ W`, the rest zero. -/
def trunc (U : ℕ → Bool) (W : ℕ) (d : Config) : Config where
  pc := d.pc
  nreg := fun r => if U r = true then d.nreg r else 0
  rreg := fun r => if U r = true then d.rreg r else 0
  nmem := fun a => if a ≤ W then d.nmem a else 0
  rmem := fun a => if a ≤ W then d.rmem a else 0
  output := d.output

theorem agree_trunc (U : ℕ → Bool) (W : ℕ) (d : Config) : Agree U W (trunc U W d) d :=
  ⟨fun r hr => by simp [trunc, hr], fun r hr => by simp [trunc, hr],
    fun a ha => by simp [trunc, ha], fun a ha => by simp [trunc, ha]⟩

/-- The truncation is bounded by `W` when the registers in `U` and the memory at addresses
`≤ W` of `d` are. -/
theorem wordsBounded_trunc {U : ℕ → Bool} {W : ℕ} {d : Config}
    (hr : ∀ r, U r = true → d.nreg r ≤ W) (hm : ∀ a ≤ W, d.nmem a ≤ W) :
    WordsBounded W (trunc U W d) :=
  ⟨fun r => by
      simp only [trunc]; split
      · exact hr r ‹_›
      · exact Nat.zero_le _,
    fun a => by
      simp only [trunc]; split
      · exact hm a ‹_›
      · exact Nat.zero_le _⟩

/-- The bound of a configuration agreeing with a bounded one, from its other cells. -/
theorem wordsBounded_of_agree {U : ℕ → Bool} {W W' : ℕ} {c d : Config} (hA : Agree U W c d)
    (hc : WordsBounded W c) (hW : W ≤ W') (hr : ∀ r, U r = false → d.nreg r ≤ W')
    (hm : ∀ a, W < a → d.nmem a ≤ W') : WordsBounded W' d :=
  ⟨fun r => by
      cases h : U r
      · exact hr r h
      · rw [hA.nreg r h]; exact (WordsBounded.nreg hc r).trans hW,
    fun a => by
      by_cases h : a ≤ W
      · rw [hA.nmem a h]; exact (WordsBounded.nmem hc a).trans hW
      · exact hm a (by omega)⟩

/-! ### One instruction -/

section instr

variable {P P' : Input} {U : ℕ → Bool} {W : ℕ}

/-- **One straight-line instruction other than `readIn` and `inputSize`, embedded** (for
`rand`, the outer input has the same random tape). -/
theorem effect_embed {ins : Instr} {c c' d : Config} (hok : ins.regsOK U = true)
    (hnr : ins.notInp = true) (hrd : ins.noRand = true ∨ P'.tape = P.tape)
    (he : ins.effect P c = some c') (hc : WordsBounded W c) (hA : Agree U W c d) :
    ∃ d', ins.effect P' d = some d' ∧ Agree U W c' d' ∧ Keep U W d d' ∧
      ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
  have hl : ∀ r ∈ ins.regs, U r = true := fun r hr => List.all_eq_true.1 hok r hr
  have aw : ∀ a, c.nreg a ≤ W := WordsBounded.nreg hc
  have kN : ∀ (f : ℕ → ℕ) (i : ℕ) (v : ℕ), U i = true → ∀ r, U r = false → upd f i v r = f r :=
    fun f i v hi r hr => upd_other _ _ _ (fun e => by rw [e, hi] at hr; cases hr)
  have kR : ∀ (f : ℕ → ℝ) (i : ℕ) (v : ℝ), U i = true → ∀ r, U r = false → upd f i v r = f r :=
    fun f i v hi r hr => upd_other _ _ _ (fun e => by rw [e, hi] at hr; cases hr)
  have aN : ∀ (i : ℕ) (v : ℕ), U i = true → ∀ r, U r = true →
      upd d.nreg i v r = upd c.nreg i v r :=
    fun i v _ r hr => by simp only [upd_apply]; split <;> [rfl; exact hA.nreg r hr]
  have aR : ∀ (i : ℕ) (v : ℝ), U i = true → ∀ r, U r = true →
      upd d.rreg i v r = upd c.rreg i v r :=
    fun i v _ r hr => by simp only [upd_apply]; split <;> [rfl; exact hA.rreg r hr]
  have nil : ∀ x : List ℕ, x = x ++ [] := fun x => (List.append_nil x).symm
  cases ins with
  | halt => simp at he
  | jump l => simp at he
  | brLtN a b l => simp at he
  | brLtR a b l => simp at he
  | inputSize r => simp [Instr.notInp] at hnr
  | readIn r a => simp [Instr.notInp] at hnr
  | rand r a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    have ht : P'.tape = P.tape := by
      rcases hrd with h | h
      · simp [Instr.noRand] at h
      · exact h
    exact ⟨_, rfl, ⟨fun x hx => by
      dsimp only; rw [hA.nreg a ha, ht]; exact aN r _ this x hx, hA.rreg, hA.nmem,
      hA.rmem⟩, ⟨fun x hx => kN _ _ _ this x hx, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩, [], nil _, nil _⟩
  | constN r k =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨fun x hx => aN r k this x hx, hA.rreg, hA.nmem, hA.rmem⟩,
      ⟨fun x hx => kN _ _ _ this x hx, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩,
      [], nil _, nil _⟩
  | copyN r a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨fun x hx => by
      dsimp only; rw [hA.nreg a ha]; exact aN r _ this x hx, hA.rreg, hA.nmem,
      hA.rmem⟩, ⟨fun x hx => kN _ _ _ this x hx, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩, [], nil _, nil _⟩
  | addN r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    have hb := hl b (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨fun x hx => by
      dsimp only; rw [hA.nreg a ha, hA.nreg b hb]; exact aN r _ this x hx, hA.rreg,
      hA.nmem, hA.rmem⟩, ⟨fun x hx => kN _ _ _ this x hx, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩, [], nil _, nil _⟩
  | subN r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    have hb := hl b (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨fun x hx => by
      dsimp only; rw [hA.nreg a ha, hA.nreg b hb]; exact aN r _ this x hx, hA.rreg,
      hA.nmem, hA.rmem⟩, ⟨fun x hx => kN _ _ _ this x hx, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩, [], nil _, nil _⟩
  | mulN r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    have hb := hl b (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨fun x hx => by
      dsimp only; rw [hA.nreg a ha, hA.nreg b hb]; exact aN r _ this x hx, hA.rreg,
      hA.nmem, hA.rmem⟩, ⟨fun x hx => kN _ _ _ this x hx, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩, [], nil _, nil _⟩
  | divN r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    have hb := hl b (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨fun x hx => by
      dsimp only; rw [hA.nreg a ha, hA.nreg b hb]; exact aN r _ this x hx, hA.rreg,
      hA.nmem, hA.rmem⟩, ⟨fun x hx => kN _ _ _ this x hx, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩, [], nil _, nil _⟩
  | modN r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    have hb := hl b (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨fun x hx => by
      dsimp only; rw [hA.nreg a ha, hA.nreg b hb]; exact aN r _ this x hx, hA.rreg,
      hA.nmem, hA.rmem⟩, ⟨fun x hx => kN _ _ _ this x hx, fun _ _ => rfl, fun _ _ => rfl,
      fun _ _ => rfl⟩, [], nil _, nil _⟩
  | loadN r a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨fun x hx => by
      dsimp only; rw [hA.nreg a ha, hA.nmem _ (aw a)]; exact aN r _ this x hx,
      hA.rreg, hA.nmem, hA.rmem⟩, ⟨fun x hx => kN _ _ _ this x hx, fun _ _ => rfl,
      fun _ _ => rfl, fun _ _ => rfl⟩, [], nil _, nil _⟩
  | storeN a r =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    refine ⟨_, rfl, ⟨hA.nreg, hA.rreg, fun x hx => ?_, hA.rmem⟩,
      ⟨fun _ _ => rfl, fun _ _ => rfl, fun x hx => ?_, fun _ _ => rfl⟩, [], nil _, nil _⟩
    · simp only [hA.nreg a ha, hA.nreg r this, upd_apply]
      split <;> [rfl; exact hA.nmem x hx]
    · simp only [hA.nreg a ha]; exact upd_other _ _ _ (by have := aw a; omega)
  | constR r z =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨hA.nreg, fun x hx => aR r _ this x hx, hA.nmem, hA.rmem⟩,
      ⟨fun _ _ => rfl, fun x hx => kR _ _ _ this x hx, fun _ _ => rfl, fun _ _ => rfl⟩,
      [], nil _, nil _⟩
  | copyR r a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨hA.nreg, fun x hx => by
      dsimp only; rw [hA.rreg a ha]; exact aR r _ this x hx, hA.nmem,
      hA.rmem⟩, ⟨fun _ _ => rfl, fun x hx => kR _ _ _ this x hx, fun _ _ => rfl,
      fun _ _ => rfl⟩, [], nil _, nil _⟩
  | addR r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    have hb := hl b (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨hA.nreg, fun x hx => by
      dsimp only; rw [hA.rreg a ha, hA.rreg b hb]; exact aR r _ this x hx,
      hA.nmem, hA.rmem⟩, ⟨fun _ _ => rfl, fun x hx => kR _ _ _ this x hx, fun _ _ => rfl,
      fun _ _ => rfl⟩, [], nil _, nil _⟩
  | subR r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    have hb := hl b (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨hA.nreg, fun x hx => by
      dsimp only; rw [hA.rreg a ha, hA.rreg b hb]; exact aR r _ this x hx,
      hA.nmem, hA.rmem⟩, ⟨fun _ _ => rfl, fun x hx => kR _ _ _ this x hx, fun _ _ => rfl,
      fun _ _ => rfl⟩, [], nil _, nil _⟩
  | mulR r a b =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    have hb := hl b (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨hA.nreg, fun x hx => by
      dsimp only; rw [hA.rreg a ha, hA.rreg b hb]; exact aR r _ this x hx,
      hA.nmem, hA.rmem⟩, ⟨fun _ _ => rfl, fun x hx => kR _ _ _ this x hx, fun _ _ => rfl,
      fun _ _ => rfl⟩, [], nil _, nil _⟩
  | divR r a b =>
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    have hb := hl b (by simp [Instr.regs])
    by_cases h0 : c.rreg b = 0
    · rw [Instr.effect_divR_zero _ _ _ h0] at he; cases he
    · rw [Instr.effect_divR _ _ _ h0, Option.some.injEq] at he; subst he
      have h0' : d.rreg b ≠ 0 := by rw [hA.rreg b hb]; exact h0
      refine ⟨_, Instr.effect_divR _ _ _ h0', ⟨hA.nreg, fun x hx => by
        dsimp only; rw [hA.rreg a ha, hA.rreg b hb]; exact aR r _ this x hx, hA.nmem, hA.rmem⟩,
        ⟨fun _ _ => rfl, fun x hx => kR _ _ _ this x hx, fun _ _ => rfl, fun _ _ => rfl⟩,
        [], nil _, nil _⟩
  | loadR r a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨hA.nreg, fun x hx => by
      dsimp only; rw [hA.nreg a ha, hA.rmem _ (aw a)]; exact aR r _ this x hx, hA.nmem, hA.rmem⟩,
      ⟨fun _ _ => rfl, fun x hx => kR _ _ _ this x hx,
      fun _ _ => rfl, fun _ _ => rfl⟩, [], nil _, nil _⟩
  | storeR a r =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have := hl r (by simp [Instr.regs])
    have ha := hl a (by simp [Instr.regs])
    refine ⟨_, rfl, ⟨hA.nreg, hA.rreg, hA.nmem, fun x hx => ?_⟩,
      ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun x hx => ?_⟩, [], nil _, nil _⟩
    · simp only [hA.nreg a ha, hA.rreg r this, upd_apply]
      split <;> [rfl; exact hA.rmem x hx]
    · simp only [hA.nreg a ha]; exact upd_other _ _ _ (by have := aw a; omega)
  | outN a =>
    simp only [Instr.effect, Option.some.injEq] at he; subst he
    have ha := hl a (by simp [Instr.regs])
    exact ⟨_, rfl, ⟨hA.nreg, hA.rreg, hA.nmem, hA.rmem⟩,
      ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, [c.nreg a], rfl,
      by rw [hA.nreg a ha]⟩

end instr

/-! ### The embedding theorem -/

namespace Exec

variable {P P' : Input} {W : ℕ}

private lemma or_and {x y : Bool} {Q : Prop} (h : (x && y) = true ∨ Q) :
    (x = true ∨ Q) ∧ (y = true ∨ Q) := by
  rcases h with h | h
  · simp only [Bool.and_eq_true] at h; exact ⟨Or.inl h.1, Or.inl h.2⟩
  · exact ⟨Or.inr h, Or.inr h⟩

/-- **Embedding of a structured run.** Let `s` name only registers satisfying `U` and run from
`c` to `c'` in `k` steps with word bound `W` on input `P`. From any configuration `d` bounded by
`W' ≥ W`, agreeing with `c` on the registers in `U` and on the memory at addresses `≤ W`, and
holding the input words of `P` at `β` (`InData`, with `len` the number of words) unless `s` has
neither `readIn` nor `inputSize`, the statement `s.toMem tmp β len` (`tmp` a register outside
`U`) runs on any input `P'` with the random tape of `P` (any input at all if `s` has no `rand`)
in `k'` steps, `k ≤ k' ≤ 3k` (`k' = k` without `readIn` and `inputSize`), to a configuration
agreeing with `c'`, keeping the registers outside `U` but `tmp` (and `tmp` too without
`readIn`, `inputSize`) and the memory above `W`, and appending to the output what `s`
appends. -/
theorem embed {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k) {U : ℕ → Bool}
    {W' tmp β len : ℕ} (hs : s.regsOK U = true) (hW : W ≤ W')
    (hrd : s.noRand = true ∨ P'.tape = P.tape) :
    ∀ d, Agree U W c d → WordsBounded W' d →
      (s.noInp = true ∨ (InData P W β len W' d ∧ U tmp = false)) →
      ∃ d' k', Exec P' W' (s.toMem tmp β len) d d' k' ∧ k ≤ k' ∧ k' ≤ 3 * k ∧
        (s.noInp = true → k' = k) ∧ Agree U W c' d' ∧ KeepT U W tmp s.noInp d d' ∧
        ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
  -- the data region survives a frame
  have hID : ∀ {ro : Bool} {d d' : Config}, KeepT U W tmp ro d d' →
      InData P W β len W' d ∧ U tmp = false → InData P W β len W' d' ∧ U tmp = false :=
    fun hK ⟨hI, ht⟩ => ⟨⟨hI.lt, hI.le, hI.len, fun i hi => by
      rw [hK.nmem _ (by have := hI.lt; omega)]; exact hI.mem i hi⟩, ht⟩
  induction h with
  | skip hw =>
    intro d hA hd _
    exact ⟨d, 0, .skip hd, le_rfl, by omega, fun _ => rfl, hA, (Keep.refl _ _ _).toT _ _, [],
      by simp, by simp⟩
  | @instr ins c c' hst he hw hw' =>
    intro d hA hd hD
    have hl : ∀ r ∈ ins.regs, U r = true := fun r hr => List.all_eq_true.1 hs r hr
    by_cases hri : ins.notInp = true
    · obtain ⟨d', hed, hA', hK, L, hL⟩ := effect_embed (P' := P') hs hri hrd he hw hA
      have hd' : WordsBounded W' d' := wordsBounded_of_agree hA' hw' hW
        (fun r hr => by rw [hK.nreg r hr]; exact WordsBounded.nreg hd r)
        (fun a ha => by rw [hK.nmem a ha]; exact WordsBounded.nmem hd a)
      refine ⟨d', 1, ?_, le_rfl, by omega, fun _ => rfl, hA', hK.toT _ _, L, hL⟩
      rw [show (Stmt.instr ins).toMem tmp β len = .instr ins from instrToMem_of_notInp hri]
      exact .instr hst hed hd hd'
    · have hnr : (Stmt.instr ins).noInp = false := by
        simp only [Bool.not_eq_true] at hri; exact hri
      obtain ⟨hI, htmp⟩ : InData P W β len W' d ∧ U tmp = false := by
        rcases hD with hD | hI
        · rw [hnr] at hD; cases hD
        · exact hI
      have hβ := hI.lt; have hβ' := hI.le
      cases ins with
      | readIn r a =>
        have hr := hl r (by simp [Instr.regs])
        have ha := hl a (by simp [Instr.regs])
        have hrt : r ≠ tmp := fun e => by rw [e, htmp] at hr; cases hr
        have hat : a ≠ tmp := fun e => by rw [e, htmp] at ha; cases ha
        simp only [Instr.effect, Option.some.injEq] at he; subst he
        have hca := WordsBounded.nreg hw a
        set d₁ : Config := { d with nreg := upd d.nreg tmp β } with hd₁
        have hw₁ : WordsBounded W' d₁ := ⟨upd_le hd.1 (by omega), hd.2⟩
        have e₁a : d₁.nreg a = c.nreg a := by
          rw [hd₁]; simp only [upd_other _ _ _ hat]; exact hA.nreg a ha
        set d₂ : Config := { d₁ with nreg := upd d₁.nreg tmp (d₁.nreg tmp + d₁.nreg a) }
          with hd₂
        have e₂ : d₂.nreg tmp = β + c.nreg a := by
          rw [hd₂]; simp only [upd_apply, ite_true]; rw [e₁a, hd₁]; simp
        have hw₂ : WordsBounded W' d₂ := ⟨upd_le hw₁.1 (by
          rw [e₁a, hd₁]; simp only [upd_apply, ite_true]; omega), hw₁.2⟩
        set d₃ : Config := { d₂ with nreg := upd d₂.nreg r (d₂.nmem (d₂.nreg tmp)) } with hd₃
        have hval : d₂.nmem (d₂.nreg tmp) = P.data.getD (c.nreg a) 0 := by
          rw [e₂]; exact hI.mem _ hca
        have hA₃ : Agree U W { c with nreg := upd c.nreg r (P.data.getD (c.nreg a) 0) } d₃ := by
          refine ⟨fun x hx => ?_, hA.rreg, hA.nmem, hA.rmem⟩
          have hxt : x ≠ tmp := fun e => by rw [e, htmp] at hx; cases hx
          rw [hd₃]; simp only [hval, upd_apply]
          split
          · rfl
          · rw [hd₂]; simp only [upd_apply, hxt, ite_false]
            rw [hd₁]; simp only [upd_apply, hxt, ite_false]; exact hA.nreg x hx
        have hK₃ : KeepT U W tmp false d d₃ := by
          refine ⟨fun x hx ht => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩
          have hxt : x ≠ tmp := fun e => by simpa using ht e
          have hxr : x ≠ r := fun e => by rw [e, hr] at hx; cases hx
          rw [hd₃]; simp only [upd_other _ _ _ hxr]
          rw [hd₂]; simp only [upd_other _ _ _ hxt]
          rw [hd₁]; simp only [upd_other _ _ _ hxt]
        have hw₃ : WordsBounded W' d₃ := ⟨upd_le hw₂.1 (by
          rw [hval]; have := WordsBounded.nreg hw' r; simp only [upd_apply, ite_true] at this
          omega), hw₂.2⟩
        refine ⟨d₃, 1 + (1 + 1), ?_, by omega, by omega, (fun h => by rw [hnr] at h; cases h),
          hA₃, (by rw [hnr]; exact hK₃), [], by simp, by simp [hd₃, hd₂, hd₁]⟩
        exact .seq (.instr rfl rfl hd hw₁) (.seq (.instr rfl rfl hw₁ hw₂) (.instr rfl rfl hw₂ hw₃))
      | inputSize r =>
        have hr := hl r (by simp [Instr.regs])
        simp only [Instr.effect, Option.some.injEq] at he; subst he
        have hlen : len ≤ W' := by
          have := WordsBounded.nreg hw' r; simp only [upd_apply, ite_true] at this
          rw [hI.len]; omega
        have hw₁ : WordsBounded W' { d with nreg := upd d.nreg r len } :=
          ⟨upd_le hd.1 hlen, hd.2⟩
        refine ⟨_, 1, .instr rfl rfl hd hw₁, le_rfl, by omega, (fun _ => rfl),
          ⟨fun x hx => ?_, hA.rreg, hA.nmem, hA.rmem⟩,
          ⟨fun x hx _ => ?_, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩, [],
          (List.append_nil _).symm, (List.append_nil _).symm⟩
        · simp only [upd_apply, hI.len]; split
          · rfl
          · exact hA.nreg x hx
        · exact upd_other _ _ _ (fun e => by rw [e, hr] at hx; cases hx)
      | _ => simp [Instr.notInp] at hri
  | @seq s t c c₁ c₂ k₁ k₂ _ _ ih₁ ih₂ =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨hrd₁, hrd₂⟩ := or_and hrd
    obtain ⟨hD₁, hD₂'⟩ := or_and hD
    obtain ⟨d₁, k₁', e₁, a₁, b₁, c₁', hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hs.1 hrd₁ d hA hd hD₁
    have hD₂ : t.noInp = true ∨ (InData P W β len W' d₁ ∧ U tmp = false) := by
      rcases hD₂' with h | h
      · exact Or.inl h
      · exact Or.inr (hID hK₁ h)
    obtain ⟨d₂, k₂', e₂, a₂, b₂, c₂', hA₂, hK₂, L₂, o₂, o₂'⟩ :=
      ih₂ hs.2 hrd₂ d₁ hA₁ e₁.wb_right hD₂
    refine ⟨d₂, k₁' + k₂', .seq e₁ e₂, by omega, by omega, fun h => ?_, hA₂, hK₁.trans hK₂,
      L₁ ++ L₂, by rw [o₂, o₁, List.append_assoc], by rw [o₂', o₁', List.append_assoc]⟩
    simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c₁' h.1, c₂' h.2]
  | @ifLtN_true a b t e c c' k ht _ ih =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', a', b', c'', hA', hK', L, o⟩ :=
      ih hst (or_and hrd).1 d hA hd (or_and hD).1
    refine ⟨d', k' + 1, .ifLtN_true (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e',
      by omega, by omega, fun h => ?_, hA', hK'.weaken fun h' => ?_, L, o⟩
    · simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c'' h.1]
    · simp only [Stmt.noInp, Bool.and_eq_true] at h'; exact h'.1
  | @ifLtN_false a b t e c c' k ht _ ih =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', a', b', c'', hA', hK', L, o⟩ :=
      ih hse (or_and hrd).2 d hA hd (or_and hD).2
    refine ⟨d', k' + 2, .ifLtN_false (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e',
      by omega, by omega, fun h => ?_, hA', hK'.weaken fun h' => ?_, L, o⟩
    · simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c'' h.2]
    · simp only [Stmt.noInp, Bool.and_eq_true] at h'; exact h'.2
  | @ifLtR_true a b t e c c' k ht _ ih =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', a', b', c'', hA', hK', L, o⟩ :=
      ih hst (or_and hrd).1 d hA hd (or_and hD).1
    refine ⟨d', k' + 1, .ifLtR_true (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e',
      by omega, by omega, fun h => ?_, hA', hK'.weaken fun h' => ?_, L, o⟩
    · simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c'' h.1]
    · simp only [Stmt.noInp, Bool.and_eq_true] at h'; exact h'.1
  | @ifLtR_false a b t e c c' k ht _ ih =>
    intro d hA hd hD
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨⟨ha, hb⟩, hst⟩, hse⟩ := hs
    obtain ⟨d', k', e', a', b', c'', hA', hK', L, o⟩ :=
      ih hse (or_and hrd).2 d hA hd (or_and hD).2
    refine ⟨d', k' + 2, .ifLtR_false (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e',
      by omega, by omega, fun h => ?_, hA', hK'.weaken fun h' => ?_, L, o⟩
    · simp only [Stmt.noInp, Bool.and_eq_true] at h; rw [c'' h.2]
    · simp only [Stmt.noInp, Bool.and_eq_true] at h'; exact h'.2
  | @whileLtN_false a b body c ht hw =>
    intro d hA hd _
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨ha, hb⟩, _⟩ := hs
    exact ⟨d, 2, .whileLtN_false (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) hd, le_rfl,
      by omega, fun _ => rfl, hA, (Keep.refl _ _ _).toT _ _, [], by simp, by simp⟩
  | @whileLtN_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    intro d hA hd hD
    have hs' := hs
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs'
    obtain ⟨⟨ha, hb⟩, hsb⟩ := hs'
    obtain ⟨d₁, k₁', e₁, a₁, b₁, c₁', hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hsb hrd d hA hd hD
    have hD₂ : (Stmt.whileLtN a b body).noInp = true ∨
        (InData P W β len W' d₁ ∧ U tmp = false) := by
      rcases hD with h | h
      · exact Or.inl h
      · exact Or.inr (hID hK₁ h)
    obtain ⟨d₂, k₂', e₂, a₂, b₂, c₂', hA₂, hK₂, L₂, o₂, o₂'⟩ := ih₂ hs hrd d₁ hA₁ e₁.wb_right hD₂
    refine ⟨d₂, k₁' + 2 + k₂',
      .whileLtN_true (by rw [hA.nreg a ha, hA.nreg b hb]; exact ht) e₁ e₂, by omega, by omega,
      fun h => ?_, hA₂, (hK₁.trans hK₂).weaken fun h => ?_, L₁ ++ L₂,
      by rw [o₂, o₁, List.append_assoc], by rw [o₂', o₁', List.append_assoc]⟩
    · have h' : body.noInp = true := h
      rw [c₁' h', c₂' h]
    · simp only [Bool.and_eq_true]; exact ⟨h, h⟩
  | @whileLtR_false a b body c ht hw =>
    intro d hA hd _
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs
    obtain ⟨⟨ha, hb⟩, _⟩ := hs
    exact ⟨d, 2, .whileLtR_false (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) hd, le_rfl,
      by omega, fun _ => rfl, hA, (Keep.refl _ _ _).toT _ _, [], by simp, by simp⟩
  | @whileLtR_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    intro d hA hd hD
    have hs' := hs
    simp only [Stmt.regsOK, Bool.and_eq_true] at hs'
    obtain ⟨⟨ha, hb⟩, hsb⟩ := hs'
    obtain ⟨d₁, k₁', e₁, a₁, b₁, c₁', hA₁, hK₁, L₁, o₁, o₁'⟩ := ih₁ hsb hrd d hA hd hD
    have hD₂ : (Stmt.whileLtR a b body).noInp = true ∨
        (InData P W β len W' d₁ ∧ U tmp = false) := by
      rcases hD with h | h
      · exact Or.inl h
      · exact Or.inr (hID hK₁ h)
    obtain ⟨d₂, k₂', e₂, a₂, b₂, c₂', hA₂, hK₂, L₂, o₂, o₂'⟩ := ih₂ hs hrd d₁ hA₁ e₁.wb_right hD₂
    refine ⟨d₂, k₁' + 2 + k₂',
      .whileLtR_true (by rw [hA.rreg a ha, hA.rreg b hb]; exact ht) e₁ e₂, by omega, by omega,
      fun h => ?_, hA₂, (hK₁.trans hK₂).weaken fun h => ?_, L₁ ++ L₂,
      by rw [o₂, o₁, List.append_assoc], by rw [o₂', o₁', List.append_assoc]⟩
    · have h' : body.noInp = true := h
      rw [c₁' h', c₂' h]
    · simp only [Bool.and_eq_true]; exact ⟨h, h⟩

/-- **Lifting a run that reads no input.** If `s` names only registers satisfying `U` and has
no `readIn`, `inputSize` or `rand`, and runs from `c` to `c'` with word bound `W`, then from
any `d` bounded by `W' ≥ W` agreeing with `c` on the registers in `U` and the memory `≤ W`,
`s` itself runs on any input in the same number of steps to a `d'` agreeing with `c'`, with
the registers outside `U` and the memory above `W` of `d` kept. -/
theorem lift {s : Stmt} {c c' : Config} {k W' : ℕ} {U : ℕ → Bool} (h : Exec P W s c c' k)
    (hs : s.regsOK U = true) (hn : s.noInp = true) (hr : s.noRand = true) (hW : W ≤ W')
    {d : Config} (hA : Agree U W c d) (hd : WordsBounded W' d) :
    ∃ d', Exec P' W' s d d' k ∧ Agree U W c' d' ∧ Keep U W d d' ∧
      ∃ L, c'.output = c.output ++ L ∧ d'.output = d.output ++ L := by
  obtain ⟨d', k', e, -, -, hk, hA', hK, L, o⟩ :=
    embed (P' := P') (tmp := 0) (β := 0) (len := 0) h hs hW (Or.inl hr) d hA hd (Or.inl hn)
  rw [toMem_of_noInp hn, hk hn] at e
  rw [hn] at hK
  exact ⟨d', e, hA', ⟨fun r h => hK.nreg r h (fun _ => rfl), hK.rreg, hK.nmem, hK.rmem⟩, L, o⟩

/-- **Lifting a run from the truncation.** A run of `s` (registers in `U`, no input, no `rand`)
from `trunc U W d` lifts to a run from `d`. -/
theorem lift_trunc {s : Stmt} {c' : Config} {k W' : ℕ} {U : ℕ → Bool} {d : Config}
    (h : Exec P W s (trunc U W d) c' k) (hs : s.regsOK U = true) (hn : s.noInp = true)
    (hr : s.noRand = true) (hW : W ≤ W') (hd : WordsBounded W' d) :
    ∃ d', Exec P' W' s d d' k ∧ Agree U W c' d' ∧ Keep U W d d' ∧ d'.output = c'.output := by
  obtain ⟨d', e, hA', hK, L, o, o'⟩ := lift (P' := P') h hs hn hr hW (agree_trunc U W d) hd
  refine ⟨d', e, hA', hK, ?_⟩
  rw [o', o]; rfl

end Exec

end

end Machine

end WordRAM
