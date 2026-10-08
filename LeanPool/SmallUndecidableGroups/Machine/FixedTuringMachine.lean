/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import Mathlib.Computability.TuringMachine.ToPartrec
public import Mathlib.Computability.Reduce
public import Mathlib.Computability.Halting

/-! The already verified Mathlib compilers turn the preceding four-stack
machine into a deterministic one-tape Post machine. -/

@[expose] public section

namespace Undecidability

open Turing
open Encodable Denumerable

/-- The unary universal partial function used for the fixed machine.  Its input
is the natural-number code of a partial-recursive program, and that program is
run on the fixed input `0`. -/
def fixedUniversalEval (n : ℕ) : Part ℕ :=
  Nat.Partrec.Code.eval (ofNat Nat.Partrec.Code n) 0

theorem fixedUniversalEval_partrec : Partrec fixedUniversalEval :=
  Nat.Partrec.Code.eval_part.comp
    ((Computable.ofNat Nat.Partrec.Code).comp Computable.id)
    (Computable.const 0)

/-- A code in Mathlib's list-oriented partial-recursive basis which computes
the unary universal partial function.  This is the fixed program subsequently
compiled to a Turing machine. -/
theorem exists_fixed_universal_code :
    ∃ c : ToPartrec.Code, ∀ n,
      (c.eval [n]).Dom ↔ (fixedUniversalEval n).Dom := by
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code
    (Nat.Partrec'.part_iff₁.mpr fixedUniversalEval_partrec)
  refine ⟨c, fun n => ?_⟩
  have h := hc (n ::ᵥ List.Vector.nil)
  have hv : (n ::ᵥ List.Vector.nil).1 = [n] := by rfl
  rw [hv] at h
  simpa using congrArg Part.Dom h

namespace FixedMachine

/-- The state type of the universal multi-tape machine compiling partial recursive codes. -/
abbrev State := PartrecToTM2.Λ'
/-- The symbol type of the universal multi-tape machine. -/
abbrev Symbol := PartrecToTM2.Γ'
/-- The tape-index type of the universal multi-tape machine. -/
abbrev Stack := PartrecToTM2.K'

instance stackFintype : Fintype PartrecToTM2.K' where
  elems := {.main, .rev, .aux, .stack}
  complete k := by cases k <;> simp

noncomputable instance symbolPrimcodable : Primcodable Symbol :=
  Primcodable.ofEquiv (Fin (Fintype.card Symbol)) (Fintype.equivFin Symbol)

/-- With the initial-state instance specialized to the program `c`, Mathlib's
standard `TM2.init` is definitionally the configuration used by the verified
partial-recursive-to-machine compiler. -/
theorem tm2_eval_dom_iff (c : ToPartrec.Code) (n : ℕ) :
    letI : Inhabited State :=
      ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
    (TM2.eval PartrecToTM2.tr PartrecToTM2.K'.main
      (PartrecToTM2.trList [n])).Dom ↔
      (c.eval [n]).Dom := by
  let : Inhabited State :=
    ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩
  have hinit :
      TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList [n]) =
        PartrecToTM2.init c [n] := by
    unfold TM2.init PartrecToTM2.init
    congr 1
    funext k
    cases k <;> rfl
  unfold TM2.eval
  rw [hinit, PartrecToTM2.tr_eval]
  rfl

/-- The alphabet of the one-tape simulation of the universal multi-tape machine. -/
abbrev TapeSymbol :=
  TM2to1.Γ' Stack (fun _ : Stack => Symbol)

/-- A column recording the optional symbol on each tape of the multi-tape machine. -/
abbrev StackColumn := Stack → Option Symbol

noncomputable instance stackColumnPrimcodable : Primcodable StackColumn :=
  Primcodable.ofEquiv (Fin (Fintype.card StackColumn)) (Fintype.equivFin StackColumn)

noncomputable instance tapeSymbolPrimcodable : Primcodable TapeSymbol := by
  change Primcodable (Bool × StackColumn)
  infer_instance

/-- The state type of the one-tape simulation of the universal multi-tape machine. -/
abbrev OneTapeState :=
  TM2to1.Λ' Stack (fun _ : Stack => Symbol) State (Option Symbol)

/-- The transition program of the one-tape simulation of the universal multi-tape machine. -/
def oneTapeProgram :
    OneTapeState → TM1.Stmt TapeSymbol OneTapeState (Option Symbol) :=
  TM2to1.tr PartrecToTM2.tr

/-- The state type obtained by compiling the one-tape machine to a Post machine. -/
abbrev PostState := TM1to0.Λ' oneTapeProgram

/-- The initial state furnishing an inhabited instance for a specified partial recursive code. -/
@[reducible] def stateInhabited (c : ToPartrec.Code) : Inhabited State :=
  ⟨PartrecToTM2.trNormal c PartrecToTM2.Cont'.halt⟩

/-- The initial state furnishing an inhabited instance for the one-tape simulation. -/
@[reducible] def oneTapeStateInhabited (c : ToPartrec.Code) : Inhabited OneTapeState :=
  @TM2to1.Λ'.inhabited Stack (fun _ : Stack => Symbol) State
    (Option Symbol) (stateInhabited c)

/-- The initial state furnishing an inhabited instance for the compiled Post machine. -/
@[reducible] def postStateInhabited (c : ToPartrec.Code) : Inhabited PostState :=
  @TM1to0.instInhabitedΛ' TapeSymbol OneTapeState
    (oneTapeStateInhabited c) (Option Symbol) inferInstance oneTapeProgram

/-- The Post machine compiling a specified partial recursive code. -/
def postMachine (c : ToPartrec.Code) :
    @TM0.Machine TapeSymbol PostState (postStateInhabited c) :=
  @TM1to0.tr TapeSymbol OneTapeState (oneTapeStateInhabited c)
    (Option Symbol) inferInstance oneTapeProgram

/-- The one-tape input encoding of a natural-number input to the universal machine. -/
def postInput (n : ℕ) : List TapeSymbol :=
  TM2to1.trInit PartrecToTM2.K'.main (PartrecToTM2.trList [n])

private theorem trNum_bit (b : Bool) (n : Num)
    (h : b = true ∨ n ≠ 0) :
    PartrecToTM2.trNum (Num.bit b n) =
      (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0) ::
        PartrecToTM2.trNum n := by
  cases b
  · simp only [Bool.false_eq_true, false_or] at h
    cases n with
    | zero => exact (h rfl).elim
    | pos p => rfl
  · cases n <;> rfl

private theorem trNat_bit (b : Bool) (n : ℕ)
    (h : b = true ∨ n ≠ 0) :
    PartrecToTM2.trNat (Nat.bit b n) =
      (if b then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0) ::
        PartrecToTM2.trNat n := by
  unfold PartrecToTM2.trNat
  change PartrecToTM2.trNum (Num.ofNat' (Nat.bit b n)) =
    _ :: PartrecToTM2.trNum (Num.ofNat' n)
  rw [Num.ofNat'_bit]
  exact trNum_bit b n <| h.imp_right fun hn hcast => hn <| by
    simpa using congrArg (fun x : Num => (x : ℕ)) hcast

theorem trNat_computable : Computable PartrecToTM2.trNat := by
  let g : Unit → List (List Symbol) → Option (List Symbol) := fun _ ih =>
    ih.length.casesOn (some []) fun k =>
      some ((if (k + 1).bodd then PartrecToTM2.Γ'.bit1
        else PartrecToTM2.Γ'.bit0) :: ih.getI (k + 1).div2)
  have hsym : Computable₂ fun (_ : Unit × List (List Symbol)) (k : ℕ) =>
      if (k + 1).bodd then PartrecToTM2.Γ'.bit1 else PartrecToTM2.Γ'.bit0 := by
    unfold Computable₂
    exact (Computable.cond
      (Computable.nat_bodd.comp (Computable.succ.comp
        (Computable.snd : Computable (fun p :
          (Unit × List (List Symbol)) × ℕ => p.2))))
      (Computable.const PartrecToTM2.Γ'.bit1)
      (Computable.const PartrecToTM2.Γ'.bit0)).of_eq fun p => by
        simp only [Nat.add_one, Nat.bodd_succ]
        cases p.2.bodd <;> rfl
  have hget : Computable₂ fun (p : Unit × List (List Symbol)) (k : ℕ) =>
      p.2.getI (k + 1).div2 :=
    (Primrec.list_getI.to_comp.comp
      (Computable.snd.comp Computable.fst)
      (Computable.nat_div2.comp (Computable.succ.comp Computable.snd))).to₂
  have htail : Computable₂ fun (p : Unit × List (List Symbol)) (k : ℕ) =>
      some ((if (k + 1).bodd then PartrecToTM2.Γ'.bit1
        else PartrecToTM2.Γ'.bit0) ::
          p.2.getI (k + 1).div2) :=
    Computable.option_some.comp₂ (Computable.list_cons.comp₂ hsym hget)
  have hg : Computable₂ g := by
    unfold Computable₂
    dsimp only [g]
    apply Computable.nat_casesOn
    · exact Computable.list_length.comp Computable.snd
    · exact Computable.const (some [])
    · exact htail
  have hrec := Computable.nat_strong_rec
    (fun _ n => PartrecToTM2.trNat n) hg
  have hspec : ∀ (_ : Unit) n,
      g Unit.unit ((List.range n).map PartrecToTM2.trNat) =
        some (PartrecToTM2.trNat n) := by
    intro _ n
    cases n with
    | zero => simp [g, PartrecToTM2.trNat_zero]
    | succ n =>
      have hlt : (n + 1).div2 < n + 1 :=
        Nat.div_lt_self (by omega) (by decide)
      have hb : (n + 1).bodd = true ∨ (n + 1).div2 ≠ 0 := by
        by_cases hzero : (n + 1).div2 = 0
        · left
          have hn : n = 0 := by
            rw [Nat.div2_val] at hzero
            omega
          subst n
          rfl
        · exact Or.inr hzero
      simp only [g, List.length_map, List.length_range]
      rw [List.getI_eq_getElem?_getD, List.getElem?_map,
        List.getElem?_range hlt]
      simp only [Option.map_some, Option.getD_some]
      rw [← trNat_bit (n + 1).bodd (n + 1).div2 hb,
        Nat.bit_bodd_div2]
  exact (hrec hspec).comp (Computable.const Unit.unit) Computable.id

theorem trSingleton_computable :
    Computable fun n => PartrecToTM2.trList [n] :=
  (Computable.list_append.comp trNat_computable
    (Computable.const [PartrecToTM2.Γ'.cons])).of_eq fun n => by
      simp

theorem trInit_main_computable :
    Computable (fun L : List Symbol =>
      @TM2to1.trInit Stack (fun _ : Stack => Symbol)
        inferInstance PartrecToTM2.K'.main L) := by
  let putMain : Symbol → TapeSymbol := fun a =>
    (false, Function.update (fun _ : Stack => none)
      PartrecToTM2.K'.main (some a))
  have hputMain : Computable putMain :=
    (Primrec.dom_finite putMain).to_comp
  have hencoded : Computable fun L : List Symbol =>
      L.reverse.map putMain :=
    (Primrec.list_map Primrec.id
      ((Primrec.dom_finite putMain).comp₂ Primrec₂.right)).to_comp.comp
        Computable.list_reverse
  have hhead : Computable fun L : List Symbol =>
      (L.reverse.map putMain).headI.2 :=
    Computable.snd.comp (Primrec.list_headI.to_comp.comp hencoded)
  have hfirst : Computable fun L : List Symbol =>
      (true, (L.reverse.map putMain).headI.2) :=
    (Computable.const true).pair hhead
  have htail : Computable fun L : List Symbol =>
      (L.reverse.map putMain).tail :=
    Primrec.list_tail.to_comp.comp hencoded
  exact (Computable.list_cons.comp hfirst htail).of_eq fun L => by
    rfl

/-- The variable input word for the fixed Post machine is computably obtained
from the natural-number program code. -/
theorem postInput_computable : Computable postInput :=
  trInit_main_computable.comp trSingleton_computable

theorem postInput_encode_computable :
    Computable fun p : Nat.Partrec.Code => postInput (Encodable.encode p) :=
  postInput_computable.comp Computable.encode

theorem post_eval_dom_iff (c : ToPartrec.Code) (n : ℕ) :
    @Part.Dom (ListBlank TapeSymbol)
      (@TM0.eval TapeSymbol PostState (postStateInhabited c) inferInstance
        (postMachine c) (postInput n)) ↔ (c.eval [n]).Dom := by
  let : Inhabited State := stateInhabited c
  let : Inhabited OneTapeState := oneTapeStateInhabited c
  let : Inhabited PostState := postStateInhabited c
  rw [postMachine, TM1to0.tr_eval]
  exact (TM2to1.tr_eval_dom PartrecToTM2.tr
    PartrecToTM2.K'.main (PartrecToTM2.trList [n])).trans
      (tm2_eval_dom_iff c n)

/-- The explicit finite support of the intermediate deterministic one-tape
machine.  This is exposed for bridges that operate at the `TM1` level. -/
noncomputable def oneTapeSupport (c : ToPartrec.Code) : Finset OneTapeState :=
  letI : Inhabited State := stateInhabited c
  TM2to1.trSupp PartrecToTM2.tr <|
    PartrecToTM2.codeSupp c PartrecToTM2.Cont'.halt

theorem oneTapeProgram_supports (c : ToPartrec.Code) :
    @TM1.Supports TapeSymbol OneTapeState (Option Symbol)
      (oneTapeStateInhabited c) oneTapeProgram (oneTapeSupport c) := by
  let : Inhabited State := stateInhabited c
  let : Inhabited OneTapeState := oneTapeStateInhabited c
  apply TM2to1.tr_supports
  exact PartrecToTM2.tr_supports c PartrecToTM2.Cont'.halt

theorem post_halting_not_computable (c : ToPartrec.Code)
    (hc : ∀ n, (c.eval [n]).Dom ↔ (fixedUniversalEval n).Dom) :
    ¬ ComputablePred fun input : List TapeSymbol =>
      (@TM0.eval TapeSymbol PostState (postStateInhabited c) inferInstance
        (postMachine c) input).Dom := by
  intro hhalting
  have hencoded : ComputablePred fun p : Nat.Partrec.Code =>
      (@TM0.eval TapeSymbol PostState (postStateInhabited c) inferInstance
        (postMachine c) (postInput (Encodable.encode p))).Dom :=
    ComputablePred.computable_of_manyOneReducible
      ⟨fun p => postInput (Encodable.encode p), postInput_encode_computable,
        fun _ => Iff.rfl⟩ hhalting
  apply ComputablePred.halting_problem 0
  exact hencoded.of_eq fun p => by
    rw [post_eval_dom_iff, hc]
    simp [fixedUniversalEval]

/-- Undecidability already holds for the intermediate deterministic one-tape
machine, before compiling it to a Post machine. -/
theorem oneTape_halting_not_computable (c : ToPartrec.Code)
    (hc : ∀ n, (c.eval [n]).Dom ↔ (fixedUniversalEval n).Dom) :
    ¬ ComputablePred fun input : List TapeSymbol =>
      (@TM1.eval TapeSymbol OneTapeState (Option Symbol)
        (oneTapeStateInhabited c) inferInstance inferInstance
        oneTapeProgram input).Dom := by
  intro hhalting
  apply post_halting_not_computable c hc
  exact hhalting.of_eq fun input => by
    let : Inhabited OneTapeState := oneTapeStateInhabited c
    let : Inhabited PostState := postStateInhabited c
    rw [postMachine, TM1to0.tr_eval]

end FixedMachine

end Undecidability
