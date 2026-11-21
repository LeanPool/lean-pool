/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.WordRAM.Machine.Relocate

/-!
# A structured language and a cost-exact compiler

* `Instr.effect P ins c`: the effect of a straight-line instruction on the state, leaving the
  program counter unchanged (`none` on a division by zero or on a control instruction).
  `step_eq_effect` relates it to `step`.
* `Stmt`: skip, straight-line instruction, sequence, `if a < b`, `while a < b` (on natural
  or on real registers).
* `compile s base : Program`, `codeSize s`, with `(compile s base).length = codeSize s`.

  **Layout and exact costs** (all costs count executed machine instructions):

  * `skip` emits no code and costs zero. `instr i` emits `[i]` and costs one.
  * `seq s t` emits `compile s base ++ compile t (base + codeSize s)`. Its size and its cost are
    the sums of the two constituent sizes and costs.
  * `ifLtN a b t e` puts the branch at `base`, compiles `e` at `base + 1`, and jumps past
    `t` afterwards. The branch target and start of `t` are `base + 2 + codeSize e`. The size
    is `codeSize t + codeSize e + 2`. The true branch costs `k_t + 1` and the false branch
    costs `k_e + 2`. The real-register variant uses the same layout with `brLtR`.
  * `whileLtN a b body` branches to `base + 2` on a true test and jumps to the exit otherwise.
    The body ends with a jump back to `base`. The size is `codeSize body + 3`. The exit costs
    two steps and each iteration costs `k_body + 2`. The real-register variant uses `brLtR`.

  A loop that iterates `m` times with body costs `k₁, …, kₘ` costs exactly
  `(k₁ + 2) + ⋯ + (kₘ + 2) + 2`.
* `Exec P W s c c' k`: big-step cost semantics counting exactly the machine instructions the
  compiled code executes.  Every configuration at which an instruction runs, plus the final
  one, is required to be `WordsBounded W`, and `divR` is never executed with a zero divisor.
  `Exec` never changes the program counter (`Exec.pc_eq`) and is insensitive to it
  (`Exec.setPc`).
* Simulation (`Exec.runsTo`): if `compile s base` sits at `base` inside `q`, then running `q`
  for exactly `k` steps from `c` with `pc := base` ends at `c'` with
  `pc := base + codeSize s`, every visited configuration `WordsBounded W`.
* Top level (`runsWithin_of_exec`): `Exec P W s initConfig c' k` gives
  `RunsWithin (compile s 0 ++ [halt]) P W (k + 1) c'.output`.
* Per-instruction rules `Exec.constN`, …, and loop rules with a potential
  (`Exec.whileLtN_potential`, `Exec.whileLtR_potential`, and the `_bounded` variants).
-/

namespace WordRAM

namespace Instr

@[expose] public section

/-- The effect of a straight-line instruction on the state; the program counter is left
unchanged.  `none` for a division by zero and for control instructions. -/
noncomputable def effect (P : Input) : Instr → Config → Option Config
  | .inputSize r, c => some { c with nreg := upd c.nreg r P.data.length }
  | .constN r k, c => some { c with nreg := upd c.nreg r k }
  | .copyN r a, c => some { c with nreg := upd c.nreg r (c.nreg a) }
  | .addN r a b, c => some { c with nreg := upd c.nreg r (c.nreg a + c.nreg b) }
  | .subN r a b, c => some { c with nreg := upd c.nreg r (c.nreg a - c.nreg b) }
  | .mulN r a b, c => some { c with nreg := upd c.nreg r (c.nreg a * c.nreg b) }
  | .divN r a b, c => some { c with nreg := upd c.nreg r (c.nreg a / c.nreg b) }
  | .modN r a b, c => some { c with nreg := upd c.nreg r (c.nreg a % c.nreg b) }
  | .loadN r a, c => some { c with nreg := upd c.nreg r (c.nmem (c.nreg a)) }
  | .storeN a r, c => some { c with nmem := upd c.nmem (c.nreg a) (c.nreg r) }
  | .constR r z, c => some { c with rreg := upd c.rreg r (z : ℝ) }
  | .copyR r a, c => some { c with rreg := upd c.rreg r (c.rreg a) }
  | .addR r a b, c => some { c with rreg := upd c.rreg r (c.rreg a + c.rreg b) }
  | .subR r a b, c => some { c with rreg := upd c.rreg r (c.rreg a - c.rreg b) }
  | .mulR r a b, c => some { c with rreg := upd c.rreg r (c.rreg a * c.rreg b) }
  | .divR r a b, c =>
      if c.rreg b = 0 then none else some { c with rreg := upd c.rreg r (c.rreg a / c.rreg b) }
  | .loadR r a, c => some { c with rreg := upd c.rreg r (c.rmem (c.nreg a)) }
  | .storeR a r, c => some { c with rmem := upd c.rmem (c.nreg a) (c.rreg r) }
  | .readIn r a, c => some { c with nreg := upd c.nreg r (P.data.getD (c.nreg a) 0) }
  | .rand r a, c => some { c with nreg := upd c.nreg r (P.tape (c.nreg a)) }
  | .outN a, c => some { c with output := c.output ++ [c.nreg a] }
  | .halt, _ => none
  | .jump _, _ => none
  | .brLtN _ _ _, _ => none
  | .brLtR _ _ _, _ => none

variable {P : Input} {c : Config}

@[simp] theorem effect_inputSize (r : ℕ) :
    (Instr.inputSize r).effect P c = some { c with nreg := upd c.nreg r P.data.length } := rfl
@[simp] theorem effect_constN (r k : ℕ) :
    (Instr.constN r k).effect P c = some { c with nreg := upd c.nreg r k } := rfl
@[simp] theorem effect_copyN (r a : ℕ) :
    (Instr.copyN r a).effect P c = some { c with nreg := upd c.nreg r (c.nreg a) } := rfl
@[simp] theorem effect_addN (r a b : ℕ) :
    (Instr.addN r a b).effect P c =
      some { c with nreg := upd c.nreg r (c.nreg a + c.nreg b) } := rfl
@[simp] theorem effect_subN (r a b : ℕ) :
    (Instr.subN r a b).effect P c =
      some { c with nreg := upd c.nreg r (c.nreg a - c.nreg b) } := rfl
@[simp] theorem effect_loadN (r a : ℕ) :
    (Instr.loadN r a).effect P c =
      some { c with nreg := upd c.nreg r (c.nmem (c.nreg a)) } := rfl
@[simp] theorem effect_storeN (a r : ℕ) :
    (Instr.storeN a r).effect P c =
      some { c with nmem := upd c.nmem (c.nreg a) (c.nreg r) } := rfl
@[simp] theorem effect_constR (r : ℕ) (z : ℤ) :
    (Instr.constR r z).effect P c = some { c with rreg := upd c.rreg r (z : ℝ) } := rfl
@[simp] theorem effect_copyR (r a : ℕ) :
    (Instr.copyR r a).effect P c = some { c with rreg := upd c.rreg r (c.rreg a) } := rfl
@[simp] theorem effect_addR (r a b : ℕ) :
    (Instr.addR r a b).effect P c =
      some { c with rreg := upd c.rreg r (c.rreg a + c.rreg b) } := rfl
@[simp] theorem effect_subR (r a b : ℕ) :
    (Instr.subR r a b).effect P c =
      some { c with rreg := upd c.rreg r (c.rreg a - c.rreg b) } := rfl
@[simp] theorem effect_mulR (r a b : ℕ) :
    (Instr.mulR r a b).effect P c =
      some { c with rreg := upd c.rreg r (c.rreg a * c.rreg b) } := rfl
theorem effect_divR (r a b : ℕ) (hb : c.rreg b ≠ 0) :
    (Instr.divR r a b).effect P c =
      some { c with rreg := upd c.rreg r (c.rreg a / c.rreg b) } := by
  simp [effect, hb]
theorem effect_divR_zero (r a b : ℕ) (hb : c.rreg b = 0) :
    (Instr.divR r a b).effect P c = none := by
  simp [effect, hb]
@[simp] theorem effect_loadR (r a : ℕ) :
    (Instr.loadR r a).effect P c =
      some { c with rreg := upd c.rreg r (c.rmem (c.nreg a)) } := rfl
@[simp] theorem effect_storeR (a r : ℕ) :
    (Instr.storeR a r).effect P c =
      some { c with rmem := upd c.rmem (c.nreg a) (c.rreg r) } := rfl
@[simp] theorem effect_mulN (r a b : ℕ) :
    (Instr.mulN r a b).effect P c =
      some { c with nreg := upd c.nreg r (c.nreg a * c.nreg b) } := rfl
@[simp] theorem effect_divN (r a b : ℕ) :
    (Instr.divN r a b).effect P c =
      some { c with nreg := upd c.nreg r (c.nreg a / c.nreg b) } := rfl
@[simp] theorem effect_modN (r a b : ℕ) :
    (Instr.modN r a b).effect P c =
      some { c with nreg := upd c.nreg r (c.nreg a % c.nreg b) } := rfl
@[simp] theorem effect_readIn (r a : ℕ) :
    (Instr.readIn r a).effect P c =
      some { c with nreg := upd c.nreg r (P.data.getD (c.nreg a) 0) } := rfl
@[simp] theorem effect_rand (r a : ℕ) :
    (Instr.rand r a).effect P c =
      some { c with nreg := upd c.nreg r (P.tape (c.nreg a)) } := rfl
@[simp] theorem effect_outN (a : ℕ) :
    (Instr.outN a).effect P c =
      some { c with output := c.output ++ [c.nreg a] } := rfl
@[simp] theorem effect_halt : (Instr.halt).effect P c = none := rfl
@[simp] theorem effect_jump (l : ℕ) : (Instr.jump l).effect P c = none := rfl
@[simp] theorem effect_brLtN (a b l : ℕ) : (Instr.brLtN a b l).effect P c = none := rfl
@[simp] theorem effect_brLtR (a b l : ℕ) : (Instr.brLtR a b l).effect P c = none := rfl

/-- The effect never changes the program counter. -/
theorem effect_pc {ins : Instr} {c' : Config} (h : ins.effect P c = some c') : c'.pc = c.pc := by
  cases ins <;> simp only [effect, Option.some.injEq, reduceCtorEq] at h
  all_goals
    first
    | exact (congrArg Config.pc h).symm
    | (split at h <;> simp only [Option.some.injEq, reduceCtorEq] at h
       exact (congrArg Config.pc h).symm)

/-- The effect is insensitive to the program counter. -/
theorem effect_setPc (ins : Instr) (p : ℕ) :
    ins.effect P { c with pc := p } = (ins.effect P c).map (fun c' => { c' with pc := p }) := by
  cases ins <;> simp only [effect, Option.map_some, Option.map_none]
  split <;> simp_all

/-- `step` on a straight-line instruction is `effect` followed by `pc + 1`. -/
theorem step_eq_effect {prog : Program} {ins : Instr} (h : prog[c.pc]? = some ins)
    (hs : ins.IsStraight) :
    step prog P c = (ins.effect P c).map (fun c' => { c' with pc := c.pc + 1 }) := by
  cases ins <;> simp only [step, effect, h, Option.map_some, Option.map_none] <;>
    first
    | (split <;> rfl)
    | simp at hs

/-- `step` on a straight-line instruction whose effect is `c'`. -/
theorem step_of_effect {prog : Program} {ins : Instr} {c' : Config} (h : prog[c.pc]? = some ins)
    (hs : ins.IsStraight) (he : ins.effect P c = some c') :
    step prog P c = some { c' with pc := c.pc + 1 } := by
  rw [step_eq_effect h hs, he]; rfl

end

end Instr

namespace Machine

@[expose] public section

/-! ### The structured language -/

/-- Structured statements over straight-line instructions. -/
inductive Stmt : Type
  /-- No code. -/
  | skip
  /-- One straight-line instruction (`Instr.IsStraight` is required by the semantics). -/
  | instr (i : Instr)
  /-- Sequencing. -/
  | seq (s t : Stmt)
  /-- `if nreg a < nreg b then thenS else elseS`. -/
  | ifLtN (a b : ℕ) (thenS elseS : Stmt)
  /-- `if rreg a < rreg b then thenS else elseS`. -/
  | ifLtR (a b : ℕ) (thenS elseS : Stmt)
  /-- `while nreg a < nreg b do body`. -/
  | whileLtN (a b : ℕ) (body : Stmt)
  /-- `while rreg a < rreg b do body`. -/
  | whileLtR (a b : ℕ) (body : Stmt)

namespace Stmt

/-- Number of machine instructions in the compiled code. -/
def codeSize : Stmt → ℕ
  | .skip => 0
  | .instr _ => 1
  | .seq s t => codeSize s + codeSize t
  | .ifLtN _ _ t e => codeSize t + codeSize e + 2
  | .ifLtR _ _ t e => codeSize t + codeSize e + 2
  | .whileLtN _ _ body => codeSize body + 3
  | .whileLtR _ _ body => codeSize body + 3

/-- Compile a statement to machine code placed at address `base`. -/
def compile : Stmt → ℕ → Program
  | .skip, _ => []
  | .instr i, _ => [i]
  | .seq s t, base => compile s base ++ compile t (base + codeSize s)
  | .ifLtN a b t e, base =>
      .brLtN a b (base + 2 + codeSize e) :: compile e (base + 1) ++
        .jump (base + 2 + codeSize e + codeSize t) :: compile t (base + 2 + codeSize e)
  | .ifLtR a b t e, base =>
      .brLtR a b (base + 2 + codeSize e) :: compile e (base + 1) ++
        .jump (base + 2 + codeSize e + codeSize t) :: compile t (base + 2 + codeSize e)
  | .whileLtN a b body, base =>
      .brLtN a b (base + 2) :: .jump (base + 3 + codeSize body) ::
        compile body (base + 2) ++ [.jump base]
  | .whileLtR a b body, base =>
      .brLtR a b (base + 2) :: .jump (base + 3 + codeSize body) ::
        compile body (base + 2) ++ [.jump base]

@[simp] theorem codeSize_skip : codeSize .skip = 0 := rfl
@[simp] theorem codeSize_instr (i : Instr) : codeSize (.instr i) = 1 := rfl
@[simp] theorem codeSize_seq (s t : Stmt) : codeSize (.seq s t) = codeSize s + codeSize t := rfl
@[simp] theorem codeSize_ifLtN (a b : ℕ) (t e : Stmt) :
    codeSize (.ifLtN a b t e) = codeSize t + codeSize e + 2 := rfl
@[simp] theorem codeSize_ifLtR (a b : ℕ) (t e : Stmt) :
    codeSize (.ifLtR a b t e) = codeSize t + codeSize e + 2 := rfl
@[simp] theorem codeSize_whileLtN (a b : ℕ) (body : Stmt) :
    codeSize (.whileLtN a b body) = codeSize body + 3 := rfl
@[simp] theorem codeSize_whileLtR (a b : ℕ) (body : Stmt) :
    codeSize (.whileLtR a b body) = codeSize body + 3 := rfl

/-- The compiled code has exactly `codeSize` instructions. -/
@[simp] theorem length_compile (s : Stmt) (base : ℕ) : (compile s base).length = codeSize s := by
  induction s generalizing base with
  | skip => rfl
  | instr i => rfl
  | seq s t ihs iht => simp [compile, ihs, iht]
  | ifLtN a b t e iht ihe => simp [compile, iht, ihe]; omega
  | ifLtR a b t e iht ihe => simp [compile, iht, ihe]; omega
  | whileLtN a b body ih => simp [compile, ih]
  | whileLtR a b body ih => simp [compile, ih]

/-- A block of straight-line instructions, as nested sequences ending in `skip`. -/
def block : List Instr → Stmt
  | [] => .skip
  | i :: l => .seq (.instr i) (block l)

@[simp] theorem block_nil : block [] = .skip := rfl
@[simp] theorem block_cons (i : Instr) (l : List Instr) :
    block (i :: l) = .seq (.instr i) (block l) := rfl

@[simp] theorem codeSize_block (l : List Instr) : codeSize (block l) = l.length := by
  induction l with
  | nil => rfl
  | cons i l ih => simp [block, ih, Nat.add_comm]

/-- A block compiles to exactly its list of instructions, at any base address. -/
@[simp] theorem compile_block (l : List Instr) (base : ℕ) : compile (block l) base = l := by
  induction l generalizing base with
  | nil => rfl
  | cons i l ih => simp [block, compile, ih]

end Stmt

open Stmt

/-! ### Big-step cost semantics -/

/-- `Exec P W s c c' k`: from state `c`, the statement `s` runs to completion in state `c'`
executing exactly `k` machine instructions of its compiled code.  Every configuration at
which an instruction runs, and the final configuration, is `WordsBounded W`; `divR` is never
executed with a zero divisor (the effect must be `some`).  The program counter is carried
along unchanged. -/
inductive Exec (P : Input) (W : ℕ) : Stmt → Config → Config → ℕ → Prop
  | skip {c : Config} : WordsBounded W c → Exec P W .skip c c 0
  | instr {ins : Instr} {c c' : Config} : ins.IsStraight → ins.effect P c = some c' →
      WordsBounded W c → WordsBounded W c' → Exec P W (.instr ins) c c' 1
  | seq {s t : Stmt} {c c₁ c₂ : Config} {k₁ k₂ : ℕ} :
      Exec P W s c c₁ k₁ → Exec P W t c₁ c₂ k₂ → Exec P W (.seq s t) c c₂ (k₁ + k₂)
  | ifLtN_true {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : c.nreg a < c.nreg b →
      Exec P W t c c' k → Exec P W (.ifLtN a b t e) c c' (k + 1)
  | ifLtN_false {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : ¬ c.nreg a < c.nreg b →
      Exec P W e c c' k → Exec P W (.ifLtN a b t e) c c' (k + 2)
  | ifLtR_true {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : c.rreg a < c.rreg b →
      Exec P W t c c' k → Exec P W (.ifLtR a b t e) c c' (k + 1)
  | ifLtR_false {a b : ℕ} {t e : Stmt} {c c' : Config} {k : ℕ} : ¬ c.rreg a < c.rreg b →
      Exec P W e c c' k → Exec P W (.ifLtR a b t e) c c' (k + 2)
  | whileLtN_false {a b : ℕ} {body : Stmt} {c : Config} : ¬ c.nreg a < c.nreg b →
      WordsBounded W c → Exec P W (.whileLtN a b body) c c 2
  | whileLtN_true {a b : ℕ} {body : Stmt} {c c₁ c' : Config} {k₁ k₂ : ℕ} : c.nreg a < c.nreg b →
      Exec P W body c c₁ k₁ → Exec P W (.whileLtN a b body) c₁ c' k₂ →
      Exec P W (.whileLtN a b body) c c' (k₁ + 2 + k₂)
  | whileLtR_false {a b : ℕ} {body : Stmt} {c : Config} : ¬ c.rreg a < c.rreg b →
      WordsBounded W c → Exec P W (.whileLtR a b body) c c 2
  | whileLtR_true {a b : ℕ} {body : Stmt} {c c₁ c' : Config} {k₁ k₂ : ℕ} : c.rreg a < c.rreg b →
      Exec P W body c c₁ k₁ → Exec P W (.whileLtR a b body) c₁ c' k₂ →
      Exec P W (.whileLtR a b body) c c' (k₁ + 2 + k₂)

namespace Exec

variable {P : Input} {W : ℕ}

/-- The starting configuration of an execution is word-bounded. -/
theorem wb_left {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k) :
    WordsBounded W c := by
  induction h with
  | skip hw => exact hw
  | instr _ _ hw _ => exact hw
  | seq _ _ ih₁ _ => exact ih₁
  | ifLtN_true _ _ ih => exact ih
  | ifLtN_false _ _ ih => exact ih
  | ifLtR_true _ _ ih => exact ih
  | ifLtR_false _ _ ih => exact ih
  | whileLtN_false _ hw => exact hw
  | whileLtN_true _ _ _ ih _ => exact ih
  | whileLtR_false _ hw => exact hw
  | whileLtR_true _ _ _ ih _ => exact ih

/-- The final configuration of an execution is word-bounded. -/
theorem wb_right {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k) :
    WordsBounded W c' := by
  induction h with
  | skip hw => exact hw
  | instr _ _ _ hw => exact hw
  | seq _ _ _ ih₂ => exact ih₂
  | ifLtN_true _ _ ih => exact ih
  | ifLtN_false _ _ ih => exact ih
  | ifLtR_true _ _ ih => exact ih
  | ifLtR_false _ _ ih => exact ih
  | whileLtN_false _ hw => exact hw
  | whileLtN_true _ _ _ _ ih => exact ih
  | whileLtR_false _ hw => exact hw
  | whileLtR_true _ _ _ _ ih => exact ih

/-- An execution never changes the program counter. -/
theorem pc_eq {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k) : c'.pc = c.pc := by
  induction h with
  | skip _ => rfl
  | instr _ he _ _ => exact Instr.effect_pc he
  | seq _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | ifLtN_true _ _ ih => exact ih
  | ifLtN_false _ _ ih => exact ih
  | ifLtR_true _ _ ih => exact ih
  | ifLtR_false _ _ ih => exact ih
  | whileLtN_false _ _ => rfl
  | whileLtN_true _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁
  | whileLtR_false _ _ => rfl
  | whileLtR_true _ _ _ ih₁ ih₂ => exact ih₂.trans ih₁

/-- An execution is insensitive to the program counter. -/
theorem setPc {s : Stmt} {c c' : Config} {k : ℕ} (h : Exec P W s c c' k) (p : ℕ) :
    Exec P W s { c with pc := p } { c' with pc := p } k := by
  induction h with
  | skip hw => exact .skip hw
  | instr hs he hw hw' =>
    refine .instr hs ?_ hw hw'
    rw [Instr.effect_setPc, he]; rfl
  | seq _ _ ih₁ ih₂ => exact .seq ih₁ ih₂
  | ifLtN_true ht _ ih => exact .ifLtN_true ht ih
  | ifLtN_false ht _ ih => exact .ifLtN_false ht ih
  | ifLtR_true ht _ ih => exact .ifLtR_true ht ih
  | ifLtR_false ht _ ih => exact .ifLtR_false ht ih
  | whileLtN_false ht hw => exact .whileLtN_false ht hw
  | whileLtN_true ht _ _ ih₁ ih₂ => exact .whileLtN_true ht ih₁ ih₂
  | whileLtR_false ht hw => exact .whileLtR_false ht hw
  | whileLtR_true ht _ _ ih₁ ih₂ => exact .whileLtR_true ht ih₁ ih₂

/-- Replace the cost by an equal one. -/
theorem cast {s : Stmt} {c c' : Config} {k k' : ℕ} (h : Exec P W s c c' k) (hk : k = k') :
    Exec P W s c c' k' := hk ▸ h

/-- Replace the final configuration by an equal one. -/
theorem cast_end {s : Stmt} {c c' c'' : Config} {k : ℕ} (h : Exec P W s c c' k) (hc : c' = c'') :
    Exec P W s c c'' k := hc ▸ h

/-! #### Per-instruction rules

Each rule gives the exact next state, cost `1`, and the side conditions: the written natural
value must be `≤ W` (for `inputSize`, `constN`, `addN`, `mulN`, `readIn`, `rand`), and `divR`
needs a nonzero divisor. -/

section instrRules
variable {c : Config} (hw : WordsBounded W c)
include hw

theorem inputSize (r : ℕ) (hn : P.data.length ≤ W) :
    Exec P W (.instr (.inputSize r)) c { c with nreg := upd c.nreg r P.data.length } 1 :=
  .instr rfl rfl hw (WordsBounded.upd_nreg hw hn c.pc)

theorem constN (r k : ℕ) (hk : k ≤ W) :
    Exec P W (.instr (.constN r k)) c { c with nreg := upd c.nreg r k } 1 :=
  .instr rfl rfl hw (WordsBounded.upd_nreg hw hk c.pc)

theorem copyN (r a : ℕ) :
    Exec P W (.instr (.copyN r a)) c { c with nreg := upd c.nreg r (c.nreg a) } 1 :=
  .instr rfl rfl hw (WordsBounded.upd_nreg hw (hw.1 a) c.pc)

theorem addN (r a b : ℕ) (hab : c.nreg a + c.nreg b ≤ W) :
    Exec P W (.instr (.addN r a b)) c { c with nreg := upd c.nreg r (c.nreg a + c.nreg b) } 1 :=
  .instr rfl rfl hw (WordsBounded.upd_nreg hw hab c.pc)

theorem subN (r a b : ℕ) :
    Exec P W (.instr (.subN r a b)) c { c with nreg := upd c.nreg r (c.nreg a - c.nreg b) } 1 :=
  .instr rfl rfl hw (WordsBounded.upd_nreg hw ((Nat.sub_le _ _).trans (hw.1 a)) c.pc)

theorem loadN (r a : ℕ) :
    Exec P W (.instr (.loadN r a)) c { c with nreg := upd c.nreg r (c.nmem (c.nreg a)) } 1 :=
  .instr rfl rfl hw (WordsBounded.upd_nreg hw (hw.2 _) c.pc)

theorem storeN (a r : ℕ) :
    Exec P W (.instr (.storeN a r)) c { c with nmem := upd c.nmem (c.nreg a) (c.nreg r) } 1 :=
  .instr rfl rfl hw (WordsBounded.upd_nmem hw (hw.1 r) c.pc)

theorem constR (r : ℕ) (z : ℤ) :
    Exec P W (.instr (.constR r z)) c { c with rreg := upd c.rreg r (z : ℝ) } 1 :=
  .instr rfl rfl hw hw

theorem copyR (r a : ℕ) :
    Exec P W (.instr (.copyR r a)) c { c with rreg := upd c.rreg r (c.rreg a) } 1 :=
  .instr rfl rfl hw hw

theorem addR (r a b : ℕ) :
    Exec P W (.instr (.addR r a b)) c { c with rreg := upd c.rreg r (c.rreg a + c.rreg b) } 1 :=
  .instr rfl rfl hw hw

theorem subR (r a b : ℕ) :
    Exec P W (.instr (.subR r a b)) c { c with rreg := upd c.rreg r (c.rreg a - c.rreg b) } 1 :=
  .instr rfl rfl hw hw

theorem mulR (r a b : ℕ) :
    Exec P W (.instr (.mulR r a b)) c { c with rreg := upd c.rreg r (c.rreg a * c.rreg b) } 1 :=
  .instr rfl rfl hw hw

theorem divR (r a b : ℕ) (hb : c.rreg b ≠ 0) :
    Exec P W (.instr (.divR r a b)) c { c with rreg := upd c.rreg r (c.rreg a / c.rreg b) } 1 :=
  .instr rfl (Instr.effect_divR r a b hb) hw hw

theorem loadR (r a : ℕ) :
    Exec P W (.instr (.loadR r a)) c { c with rreg := upd c.rreg r (c.rmem (c.nreg a)) } 1 :=
  .instr rfl rfl hw hw

theorem storeR (a r : ℕ) :
    Exec P W (.instr (.storeR a r)) c { c with rmem := upd c.rmem (c.nreg a) (c.rreg r) } 1 :=
  .instr rfl rfl hw hw

theorem mulN (r a b : ℕ) (hab : c.nreg a * c.nreg b ≤ W) :
    Exec P W (.instr (.mulN r a b)) c { c with nreg := upd c.nreg r (c.nreg a * c.nreg b) } 1 :=
  .instr rfl rfl hw (WordsBounded.upd_nreg hw hab c.pc)

theorem divN (r a b : ℕ) :
    Exec P W (.instr (.divN r a b)) c { c with nreg := upd c.nreg r (c.nreg a / c.nreg b) } 1 :=
  .instr rfl rfl hw (WordsBounded.upd_nreg hw ((Nat.div_le_self _ _).trans (hw.1 a)) c.pc)

theorem modN (r a b : ℕ) :
    Exec P W (.instr (.modN r a b)) c { c with nreg := upd c.nreg r (c.nreg a % c.nreg b) } 1 :=
  .instr rfl rfl hw (WordsBounded.upd_nreg hw ((Nat.mod_le _ _).trans (hw.1 a)) c.pc)

theorem readIn (r a : ℕ) (hv : P.data.getD (c.nreg a) 0 ≤ W) :
    Exec P W (.instr (.readIn r a)) c
      { c with nreg := upd c.nreg r (P.data.getD (c.nreg a) 0) } 1 :=
  .instr rfl rfl hw (WordsBounded.upd_nreg hw hv c.pc)

theorem rand (r a : ℕ) (hv : P.tape (c.nreg a) ≤ W) :
    Exec P W (.instr (.rand r a)) c { c with nreg := upd c.nreg r (P.tape (c.nreg a)) } 1 :=
  .instr rfl rfl hw (WordsBounded.upd_nreg hw hv c.pc)

theorem outN (a : ℕ) :
    Exec P W (.instr (.outN a)) c { c with output := c.output ++ [c.nreg a] } 1 :=
  .instr rfl rfl hw hw

end instrRules

/-! #### Blocks -/

theorem block_nil {c : Config} (hw : WordsBounded W c) : Exec P W (block []) c c 0 :=
  .skip hw

/-- Prepend one instruction to a block: cost `k + 1`. -/
theorem block_cons {i : Instr} {l : List Instr} {c c₁ c' : Config} {k : ℕ}
    (h₁ : Exec P W (.instr i) c c₁ 1) (h₂ : Exec P W (block l) c₁ c' k) :
    Exec P W (block (i :: l)) c c' (k + 1) :=
  (Exec.seq h₁ h₂).cast (Nat.add_comm _ _)

/-! #### Loops with a potential -/

/-- Generic loop rule.  `test` is the loop test, `loop` the loop statement, with the two
loop rules as hypotheses.  Given an invariant `I` (implying the word bound) and a potential
`Φ` such that from any `I`-state with the test true one iteration of the body executes with
cost `k`, re-establishes `I`, and satisfies `Φ c' + k + 2 ≤ Φ c`, the whole loop executes from
any `I`-state with total cost `≤ Φ c + 2` and ends in an `I`-state with the test false. -/
theorem loop_potential (test : Config → Prop) (body loop : Stmt)
    (hfalse : ∀ c, ¬ test c → WordsBounded W c → Exec P W loop c c 2)
    (htrue : ∀ c c₁ c' k₁ k₂, test c → Exec P W body c c₁ k₁ → Exec P W loop c₁ c' k₂ →
      Exec P W loop c c' (k₁ + 2 + k₂))
    (I : Config → Prop) (Φ : Config → ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → test c → ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W loop c c' k ∧ I c' ∧ ¬ test c' ∧ k ≤ Φ c + 2 := by
  induction hn : Φ c using Nat.strong_induction_on generalizing c with
  | _ n ih =>
    by_cases ht : test c
    · obtain ⟨c₁, k₁, hb, hI₁, hΦ⟩ := hbody c hc ht
      obtain ⟨c', k₂, hl, hI', ht', hk₂⟩ := ih (Φ c₁) (by omega) hI₁ rfl
      exact ⟨c', k₁ + 2 + k₂, htrue c c₁ c' k₁ k₂ ht hb hl, hI', ht', by omega⟩
    · exact ⟨c, 2, hfalse c ht (hI c hc), hc, ht, by omega⟩

/-- Loop rule with a potential for `whileLtN a b body`: total cost `≤ Φ c + 2`. -/
theorem whileLtN_potential {a b : ℕ} {body : Stmt} (I : Config → Prop) (Φ : Config → ℕ)
    (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ c + 2 :=
  loop_potential (fun c => c.nreg a < c.nreg b) body (.whileLtN a b body)
    (fun _ ht hw => .whileLtN_false ht hw)
    (fun _ _ _ _ _ ht hb hl => .whileLtN_true ht hb hl) I Φ hI hbody hc

/-- Loop rule with a potential for `whileLtR a b body`: total cost `≤ Φ c + 2`. -/
theorem whileLtR_potential {a b : ℕ} {body : Stmt} (I : Config → Prop) (Φ : Config → ℕ)
    (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.rreg a < c.rreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ Φ c' + k + 2 ≤ Φ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtR a b body) c c' k ∧ I c' ∧ ¬ c'.rreg a < c'.rreg b ∧
      k ≤ Φ c + 2 :=
  loop_potential (fun c => c.rreg a < c.rreg b) body (.whileLtR a b body)
    (fun _ ht hw => .whileLtR_false ht hw)
    (fun _ _ _ _ _ ht hb hl => .whileLtR_true ht hb hl) I Φ hI hbody hc

/-- Loop rule with a bounded body cost `B` and a strictly decreasing measure `μ`: total cost
`≤ (B + 2) * μ c + 2`. -/
theorem loop_bounded (test : Config → Prop) (body loop : Stmt)
    (hfalse : ∀ c, ¬ test c → WordsBounded W c → Exec P W loop c c 2)
    (htrue : ∀ c c₁ c' k₁ k₂, test c → Exec P W body c c₁ k₁ → Exec P W loop c₁ c' k₂ →
      Exec P W loop c c' (k₁ + 2 + k₂))
    (I : Config → Prop) (μ : Config → ℕ) (B : ℕ) (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → test c → ∃ c' k, Exec P W body c c' k ∧ I c' ∧ k ≤ B ∧ μ c' < μ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W loop c c' k ∧ I c' ∧ ¬ test c' ∧ k ≤ (B + 2) * μ c + 2 :=
  loop_potential test body loop hfalse htrue I (fun c => (B + 2) * μ c) hI
    (fun c hc ht => by
      obtain ⟨c', k, he, hI', hk, hμ⟩ := hbody c hc ht
      refine ⟨c', k, he, hI', ?_⟩
      have : (B + 2) * (μ c' + 1) ≤ (B + 2) * μ c := Nat.mul_le_mul_left _ hμ
      rw [Nat.mul_add, Nat.mul_one] at this
      omega) hc

/-- `whileLtN` with a bounded body cost `B` and a strictly decreasing measure `μ`. -/
theorem whileLtN_bounded {a b : ℕ} {body : Stmt} (I : Config → Prop) (μ : Config → ℕ) (B : ℕ)
    (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.nreg a < c.nreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ k ≤ B ∧ μ c' < μ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtN a b body) c c' k ∧ I c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ (B + 2) * μ c + 2 :=
  loop_bounded (fun c => c.nreg a < c.nreg b) body (.whileLtN a b body)
    (fun _ ht hw => .whileLtN_false ht hw)
    (fun _ _ _ _ _ ht hb hl => .whileLtN_true ht hb hl) I μ B hI hbody hc

/-- `whileLtR` with a bounded body cost `B` and a strictly decreasing measure `μ`. -/
theorem whileLtR_bounded {a b : ℕ} {body : Stmt} (I : Config → Prop) (μ : Config → ℕ) (B : ℕ)
    (hI : ∀ c, I c → WordsBounded W c)
    (hbody : ∀ c, I c → c.rreg a < c.rreg b →
      ∃ c' k, Exec P W body c c' k ∧ I c' ∧ k ≤ B ∧ μ c' < μ c)
    {c : Config} (hc : I c) :
    ∃ c' k, Exec P W (.whileLtR a b body) c c' k ∧ I c' ∧ ¬ c'.rreg a < c'.rreg b ∧
      k ≤ (B + 2) * μ c + 2 :=
  loop_bounded (fun c => c.rreg a < c.rreg b) body (.whileLtR a b body)
    (fun _ ht hw => .whileLtR_false ht hw)
    (fun _ _ _ _ _ ht hb hl => .whileLtR_true ht hb hl) I μ B hI hbody hc

/-- Loop rule with a ghost state: the invariant `I a` and the potential `Φ a` may depend on a
value `a : α` that the configuration does not store (for example the set of vertices processed
so far); each iteration may change it. Total cost `≤ Φ a c + 2`. -/
theorem whileLtN_ghost {α : Type} {a b : ℕ} {body : Stmt} (I : α → Config → Prop)
    (Φ : α → Config → ℕ) (hI : ∀ x c, I x c → WordsBounded W c)
    (hbody : ∀ x c, I x c → c.nreg a < c.nreg b →
      ∃ x' c' k, Exec P W body c c' k ∧ I x' c' ∧ Φ x' c' + k + 2 ≤ Φ x c)
    {x : α} {c : Config} (hc : I x c) :
    ∃ x' c' k, Exec P W (.whileLtN a b body) c c' k ∧ I x' c' ∧ ¬ c'.nreg a < c'.nreg b ∧
      k ≤ Φ x c + 2 := by
  induction hn : Φ x c using Nat.strong_induction_on generalizing x c with
  | _ n ih =>
    by_cases ht : c.nreg a < c.nreg b
    · obtain ⟨x₁, c₁, k₁, hb, hI₁, hΦ⟩ := hbody x c hc ht
      obtain ⟨x', c', k₂, hl, hI', ht', hk₂⟩ := ih (Φ x₁ c₁) (by omega) hI₁ rfl
      exact ⟨x', c', k₁ + 2 + k₂, .whileLtN_true ht hb hl, hI', ht', by omega⟩
    · exact ⟨x, c, 2, .whileLtN_false ht (hI x c hc), hc, ht, by omega⟩

end Exec

/-! ### Simulation -/

/-- Placement casts. -/
theorem SubAt.cast {p q : Program} {b b' : ℕ} (h : SubAt p q b) (hb : b = b') : SubAt p q b' :=
  hb ▸ h

/-- Two configurations differing only in an equal program counter are equal. -/
theorem setPc_congr {c : Config} {p p' : ℕ} (h : p = p') :
    ({ c with pc := p } : Config) = { c with pc := p' } := by rw [h]

/-- Replace the final configuration of a bounded run by an equal one. -/
theorem RunsTo.cast_end {prog : Program} {P : Input} {W k : ℕ} {c c' c'' : Config}
    (h : RunsTo prog P W k c c') (hc : c' = c'') : RunsTo prog P W k c c'' := hc ▸ h

/-- **Simulation.**  If `compile s base` sits at `base` inside `q`, an execution
`Exec P W s c c' k` is realised by running `q` for exactly `k` steps from `c` with
`pc := base`, ending at `c'` with `pc := base + codeSize s`, every visited configuration
`WordsBounded W`. -/
theorem Exec.runsTo {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) {q : Program} {base : ℕ} (hq : SubAt (compile s base) q base) :
    RunsTo q P W k { c with pc := base } { c' with pc := base + codeSize s } := by
  induction h generalizing q base with
  | @skip c hw =>
    exact (RunsTo.zero (wordsBounded_setPc.mpr hw)).cast_end (setPc_congr (by simp))
  | @instr ins c c' hs he hw hw' =>
    have hq0 : q[base]? = some ins := SubAt.singleton_iff.mp hq
    have hst : step q P { c with pc := base } = some { c' with pc := base + 1 } := by
      have := Instr.step_of_effect (P := P) (c := { c with pc := base }) hq0 hs
        (by rw [Instr.effect_setPc, he]; rfl)
      exact this
    exact RunsTo.single hw hw' hst
  | @seq s t c c₁ c₂ k₁ k₂ _ _ ih₁ ih₂ =>
    simp only [compile] at hq
    have h₁ := ih₁ hq.of_append_left
    have h₂ := ih₂ (hq.of_append_right.cast (by rw [length_compile]))
    exact (h₁.trans h₂).cast_end (setPc_congr (by rw [codeSize_seq]; omega))
  | @ifLtN_true a b t e c c' k ht _ ih =>
    simp only [compile] at hq
    have h0 : q[base]? = some (.brLtN a b (base + 2 + codeSize e)) := hq.head
    have hqt : SubAt (compile t (base + 2 + codeSize e)) q (base + 2 + codeSize e) :=
      hq.tail.of_append_right.tail.cast (by rw [length_compile]; omega)
    have hst : step q P { c with pc := base } = some { c with pc := base + 2 + codeSize e } :=
      step_brLtN_true h0 ht
    have hrun := ih hqt
    have hw : WordsBounded W { c with pc := base } := hrun.wb_start
    exact (RunsTo.cons hw hst hrun).cast_end
      (setPc_congr (by rw [codeSize_ifLtN]; omega))
  | @ifLtN_false a b t e c c' k ht _ ih =>
    simp only [compile] at hq
    have h0 : q[base]? = some (.brLtN a b (base + 2 + codeSize e)) := hq.head
    have hqe : SubAt (compile e (base + 1)) q (base + 1) := hq.tail.of_append_left
    have hj : q[base + 1 + codeSize e]? = some (.jump (base + 2 + codeSize e + codeSize t)) :=
      hq.tail.of_append_right.cast (by rw [length_compile]) |>.head
    have hst : step q P { c with pc := base } = some { c with pc := base + 1 } :=
      step_brLtN_false h0 ht
    have hrun := ih hqe
    have hstj : step q P { c' with pc := base + 1 + codeSize e } =
        some { c' with pc := base + 2 + codeSize e + codeSize t } :=
      step_jump hj
    have hw : WordsBounded W { c with pc := base } := hrun.wb_start
    exact ((RunsTo.cons hw hst hrun).snoc hstj hrun.wb_end).cast_end
      (setPc_congr (by rw [codeSize_ifLtN]; omega))
  | @ifLtR_true a b t e c c' k ht _ ih =>
    simp only [compile] at hq
    have h0 : q[base]? = some (.brLtR a b (base + 2 + codeSize e)) := hq.head
    have hqt : SubAt (compile t (base + 2 + codeSize e)) q (base + 2 + codeSize e) :=
      hq.tail.of_append_right.tail.cast (by rw [length_compile]; omega)
    have hst : step q P { c with pc := base } = some { c with pc := base + 2 + codeSize e } :=
      step_brLtR_true h0 ht
    have hrun := ih hqt
    have hw : WordsBounded W { c with pc := base } := hrun.wb_start
    exact (RunsTo.cons hw hst hrun).cast_end
      (setPc_congr (by rw [codeSize_ifLtR]; omega))
  | @ifLtR_false a b t e c c' k ht _ ih =>
    simp only [compile] at hq
    have h0 : q[base]? = some (.brLtR a b (base + 2 + codeSize e)) := hq.head
    have hqe : SubAt (compile e (base + 1)) q (base + 1) := hq.tail.of_append_left
    have hj : q[base + 1 + codeSize e]? = some (.jump (base + 2 + codeSize e + codeSize t)) :=
      hq.tail.of_append_right.cast (by rw [length_compile]) |>.head
    have hst : step q P { c with pc := base } = some { c with pc := base + 1 } :=
      step_brLtR_false h0 ht
    have hrun := ih hqe
    have hstj : step q P { c' with pc := base + 1 + codeSize e } =
        some { c' with pc := base + 2 + codeSize e + codeSize t } :=
      step_jump hj
    have hw : WordsBounded W { c with pc := base } := hrun.wb_start
    exact ((RunsTo.cons hw hst hrun).snoc hstj hrun.wb_end).cast_end
      (setPc_congr (by rw [codeSize_ifLtR]; omega))
  | @whileLtN_false a b body c ht hw =>
    simp only [compile] at hq
    have h0 : q[base]? = some (.brLtN a b (base + 2)) := hq.head
    have h1 : q[base + 1]? = some (.jump (base + 3 + codeSize body)) := hq.tail.head
    have hst : step q P { c with pc := base } = some { c with pc := base + 1 } :=
      step_brLtN_false h0 ht
    have hstj : step q P { c with pc := base + 1 } =
        some { c with pc := base + 3 + codeSize body } := step_jump h1
    have hw' : WordsBounded W { c with pc := base } := hw
    have hw1 : WordsBounded W { c with pc := base + 1 } := hw
    have hw3 : WordsBounded W { c with pc := base + 3 + codeSize body } := hw
    exact (RunsTo.cons hw' hst (RunsTo.single hw1 hw3 hstj)).cast_end
      (setPc_congr (by rw [codeSize_whileLtN]; omega))
  | @whileLtN_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    have hq' := hq
    simp only [compile] at hq
    have h0 : q[base]? = some (.brLtN a b (base + 2)) := hq.head
    have hqb : SubAt (compile body (base + 2)) q (base + 2) :=
      hq.tail.tail.of_append_left.cast (by omega)
    have hj : q[base + 2 + codeSize body]? = some (.jump base) :=
      hq.tail.tail.of_append_right.cast (by rw [length_compile]) |>.head
    have hst : step q P { c with pc := base } = some { c with pc := base + 2 } :=
      step_brLtN_true h0 ht
    have hrun := ih₁ hqb
    have hstj : step q P { c₁ with pc := base + 2 + codeSize body } =
        some { c₁ with pc := base } := step_jump hj
    have hrest := ih₂ hq'
    have hw : WordsBounded W { c with pc := base } := hrun.wb_start
    exact (((RunsTo.cons hw hst hrun).snoc hstj hrun.wb_end).trans hrest).cast (by omega)
  | @whileLtR_false a b body c ht hw =>
    simp only [compile] at hq
    have h0 : q[base]? = some (.brLtR a b (base + 2)) := hq.head
    have h1 : q[base + 1]? = some (.jump (base + 3 + codeSize body)) := hq.tail.head
    have hst : step q P { c with pc := base } = some { c with pc := base + 1 } :=
      step_brLtR_false h0 ht
    have hstj : step q P { c with pc := base + 1 } =
        some { c with pc := base + 3 + codeSize body } := step_jump h1
    have hw' : WordsBounded W { c with pc := base } := hw
    have hw1 : WordsBounded W { c with pc := base + 1 } := hw
    have hw3 : WordsBounded W { c with pc := base + 3 + codeSize body } := hw
    exact (RunsTo.cons hw' hst (RunsTo.single hw1 hw3 hstj)).cast_end
      (setPc_congr (by rw [codeSize_whileLtR]; omega))
  | @whileLtR_true a b body c c₁ c' k₁ k₂ ht _ _ ih₁ ih₂ =>
    have hq' := hq
    simp only [compile] at hq
    have h0 : q[base]? = some (.brLtR a b (base + 2)) := hq.head
    have hqb : SubAt (compile body (base + 2)) q (base + 2) :=
      hq.tail.tail.of_append_left.cast (by omega)
    have hj : q[base + 2 + codeSize body]? = some (.jump base) :=
      hq.tail.tail.of_append_right.cast (by rw [length_compile]) |>.head
    have hst : step q P { c with pc := base } = some { c with pc := base + 2 } :=
      step_brLtR_true h0 ht
    have hrun := ih₁ hqb
    have hstj : step q P { c₁ with pc := base + 2 + codeSize body } =
        some { c₁ with pc := base } := step_jump hj
    have hrest := ih₂ hq'
    have hw : WordsBounded W { c with pc := base } := hrun.wb_start
    exact (((RunsTo.cons hw hst hrun).snoc hstj hrun.wb_end).trans hrest).cast (by omega)

/-- Simulation for the compiled program itself (placed at `0`). -/
theorem Exec.runsTo_compile {P : Input} {W : ℕ} {s : Stmt} {c c' : Config} {k : ℕ}
    (h : Exec P W s c c' k) :
    RunsTo (compile s 0) P W k { c with pc := 0 } { c' with pc := codeSize s } := by
  have := h.runsTo (SubAt.refl (compile s 0))
  rwa [Nat.zero_add] at this

/-- **Top level.**  An execution of `s` from the initial configuration gives a
`RunsWithin` for the program `compile s 0 ++ [halt]` with `k + 1` steps. -/
theorem runsWithin_of_exec {P : Input} {W : ℕ} {s : Stmt} {c' : Config} {k : ℕ}
    (h : Exec P W s initConfig c' k) :
    RunsWithin (compile s 0 ++ [Instr.halt]) P W (k + 1) c'.output := by
  have hsub : SubAt (compile s 0) (compile s 0 ++ [Instr.halt]) 0 := SubAt.append_left _ _
  have hrun := h.runsTo hsub
  rw [Nat.zero_add] at hrun
  have hinit : ({ initConfig with pc := 0 } : Config) = initConfig := rfl
  rw [hinit] at hrun
  have hh : AtHalt (compile s 0 ++ [Instr.halt]) { c' with pc := codeSize s } := by
    unfold AtHalt
    have : codeSize s = (compile s 0).length := (length_compile s 0).symm
    change (compile s 0 ++ [Instr.halt])[codeSize s]? = some Instr.halt
    rw [this]
    exact List.getElem?_concat_length
  have := runsWithin_of_runsTo hrun hh
  exact this

/-- Top level, with the output named. -/
theorem runsWithin_of_exec_output {P : Input} {W : ℕ} {s : Stmt} {c' : Config} {k : ℕ}
    {out : List ℕ} (h : Exec P W s initConfig c' k) (ho : c'.output = out) :
    RunsWithin (compile s 0 ++ [Instr.halt]) P W (k + 1) out :=
  ho ▸ runsWithin_of_exec h

end

end Machine

end WordRAM
