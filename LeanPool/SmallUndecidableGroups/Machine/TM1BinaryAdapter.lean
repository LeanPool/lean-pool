/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import Mathlib.Computability.TuringMachine.PostTuringMachine
public import Mathlib.Computability.Partrec

/-!
# TM1BinaryAdapter

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability

open Turing

namespace TM0FiniteRestriction

variable {Gamma Q : Type*} [Inhabited Gamma] [Inhabited Q]

/-- The initial state belongs to every certified support. -/
@[reducible] def supportedInhabited (M : TM0.Machine Gamma Q) (S : Finset Q)
    (hS : TM0.Supports M (S : Set Q)) : Inhabited S :=
  ⟨⟨default, hS.1⟩⟩

/-- Restrict a finitely supported `TM0` to the finite subtype of states in its
support. -/
noncomputable def liftState (M : TM0.Machine Gamma Q) (S : Finset Q)
    (hS : TM0.Supports M (S : Set Q)) (q : Q) : S := by
  classical
  letI : Inhabited S := supportedInhabited M S hS
  exact if hq : q ∈ S then ⟨q, hq⟩ else default

omit [Inhabited Gamma] in
@[simp]
theorem liftState_coe (M : TM0.Machine Gamma Q) (S : Finset Q)
    (hS : TM0.Supports M (S : Set Q)) {q : Q} (hq : q ∈ S) :
    (liftState M S hS q : Q) = q := by
  classical
  simp [liftState, hq]

/-- The Post machine obtained by restricting the compiled machine to its finite state support. -/
noncomputable def machine (M : TM0.Machine Gamma Q) (S : Finset Q)
    (hS : TM0.Supports M (S : Set Q)) :
    @TM0.Machine Gamma S (supportedInhabited M S hS) :=
  fun q a => (M q.1 a).map fun (q', stmt) =>
    (liftState M S hS q', stmt)

/-- The configuration map including supported states into the original state type. -/
def includeCfg (S : Finset Q) : TM0.Cfg Gamma S → TM0.Cfg Gamma Q
  | ⟨q, tape⟩ => ⟨q.1, tape⟩

theorem step_map (M : TM0.Machine Gamma Q) (S : Finset Q)
    (hS : TM0.Supports M (S : Set Q)) (c : TM0.Cfg Gamma S) :
    Option.map (includeCfg S)
        (@TM0.step Gamma S (supportedInhabited M S hS) inferInstance
          (machine M S hS) c) =
      TM0.step M (includeCfg S c) := by
  classical
  rcases c with ⟨q, tape⟩
  simp only [TM0.step, includeCfg]
  cases h : M q.1 tape.head with
  | none => simp [machine, h]
  | some cmd =>
      rcases cmd with ⟨q', stmt⟩
      have hq' : q' ∈ S := hS.2 h q.2
      cases stmt <;>
        simp [machine, h, includeCfg, liftState_coe M S hS hq']

theorem respects (M : TM0.Machine Gamma Q) (S : Finset Q)
    (hS : TM0.Supports M (S : Set Q)) :
    StateTransition.Respects
      (@TM0.step Gamma S (supportedInhabited M S hS) inferInstance
        (machine M S hS))
      (TM0.step M)
      (fun c d => includeCfg S c = d) := by
  rw [StateTransition.fun_respects]
  intro c
  cases h : @TM0.step Gamma S (supportedInhabited M S hS) inferInstance
      (machine M S hS) c with
  | none =>
      have hm := step_map M S hS c
      simp [h] at hm
      exact hm.symm
  | some d =>
      have hm := step_map M S hS c
      rw [h] at hm
      exact Relation.TransGen.single (by simpa using hm.symm)

theorem init_include (M : TM0.Machine Gamma Q) (S : Finset Q)
    (hS : TM0.Supports M (S : Set Q)) (input : List Gamma) :
    includeCfg S
        (@TM0.init Gamma S (supportedInhabited M S hS) inferInstance input) =
      TM0.init input := rfl

/-- Restricting to a certified finite support preserves the halting domain. -/
theorem eval_dom_iff (M : TM0.Machine Gamma Q) (S : Finset Q)
    (hS : TM0.Supports M (S : Set Q)) (input : List Gamma) :
    (@TM0.eval Gamma S (supportedInhabited M S hS) inferInstance
        (machine M S hS) input).Dom ↔
      (TM0.eval M input).Dom := by
  unfold TM0.eval
  simpa using (StateTransition.tr_eval_dom (respects M S hS)
    (init_include M S hS input)).symm

end TM0FiniteRestriction

end Undecidability

namespace Undecidability

open Turing

namespace TM1BinaryAdapter

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]

/-- A fixed-length binary encoding of a finite tape alphabet, with the blank
symbol represented by an all-zero block. -/
structure Code (Γ : Type*) [Inhabited Γ] where
  /-- The fixed length of each binary code word. -/
  width : ℕ
  /-- The fixed-width binary encoding of an alphabet symbol. -/
  enc : Γ → List.Vector Bool width
  /-- The decoder from a fixed-width binary word to an alphabet symbol. -/
  dec : List.Vector Bool width → Γ
  enc_blank : enc default = List.Vector.replicate width false
  dec_enc : ∀ a, dec (enc a) = a

/-- Every inhabited finite alphabet admits a fixed-length binary code. -/
theorem exists_code (Γ : Type*) [Inhabited Γ] [Finite Γ] : Nonempty (Code Γ) := by
  obtain ⟨n, enc, dec, hblank, hinv⟩ := TM1to1.exists_enc_dec (Γ := Γ)
  exact ⟨⟨n, enc, dec, hblank, hinv⟩⟩

/-- A canonical (noncomputably chosen) binary code for a finite alphabet. -/
noncomputable def canonicalCode (Γ : Type*) [Inhabited Γ] [Finite Γ] : Code Γ :=
  Classical.choice (exists_code Γ)

/-- The binary `TM1` program produced by Mathlib's block-code compiler. -/
def program (B : Code Γ) (M : Λ → TM1.Stmt Γ Λ σ) :
    TM1to1.Λ' Γ Λ σ → TM1.Stmt Bool (TM1to1.Λ' Γ Λ σ) σ :=
  TM1to1.tr B.enc B.dec M

/-- Compile a finite-alphabet `TM1` program all the way to a binary `TM0`. -/
def machine (B : Code Γ) (M : Λ → TM1.Stmt Γ Λ σ) :
    TM0.Machine Bool (TM1to0.Λ' (program B M)) :=
  TM1to0.tr (program B M)

/-- Encode a finite input word by concatenating its fixed-width codewords. -/
def encodeInput (B : Code Γ) (input : List Γ) : List Bool :=
  input.flatMap fun a => (B.enc a).toList

/-- Fixed-width block encoding of words over a finite computably coded
alphabet is computable.  No effectiveness hypothesis on the particular code
table is needed: every function on a finite domain is primitive recursive. -/
theorem encodeInput_computable [Primcodable Γ] [Finite Γ] (B : Code Γ) :
    Computable (encodeInput B) :=
  (Primrec.list_flatMap Primrec.id
    ((Primrec.dom_finite (fun a : Γ => (B.enc a).toList)).comp₂
      Primrec₂.right)).to_comp

private theorem trCfg_init (B : Code Γ) (input : List Γ) :
    TM1to1.trCfg B.enc B.enc_blank (TM1.init input : TM1.Cfg Γ Λ σ) =
      TM1.init (encodeInput B input) := by
  simp [TM1to1.trCfg, TM1.init, TM1to1.trTape, TM1to1.trTape',
    Turing.Tape.mk₁, Turing.Tape.mk₂, encodeInput]
  rfl

/-- Mathlib's binary block compiler preserves the halting domain. -/
theorem program_eval_dom_iff (B : Code Γ) (M : Λ → TM1.Stmt Γ Λ σ)
    (input : List Γ) :
    (TM1.eval (program B M) (encodeInput B input)).Dom ↔
      (TM1.eval M input).Dom := by
  unfold TM1.eval
  simpa [program, trCfg_init (Λ := Λ) (σ := σ) B input] using
    StateTransition.tr_eval_dom
      (TM1to1.tr_respects (enc := B.enc) B.dec M
        (enc0 := B.enc_blank) B.dec_enc)
      (show TM1to1.trCfg B.enc B.enc_blank
          (TM1.init input : TM1.Cfg Γ Λ σ) =
          TM1.init (encodeInput B input) from
            trCfg_init (Λ := Λ) (σ := σ) B input)

/-- Compiling further from `TM1` to `TM0` preserves the halting domain. -/
theorem eval_dom_iff (B : Code Γ) (M : Λ → TM1.Stmt Γ Λ σ)
    (input : List Γ) :
    (TM0.eval (machine B M) (encodeInput B input)).Dom ↔
      (TM1.eval M input).Dom := by
  rw [machine, TM1to0.tr_eval]
  exact program_eval_dom_iff B M input

/-- A finite support for the compiled binary `TM0`, obtained by composing
Mathlib's two support transformations. -/
noncomputable def support [Fintype Γ] [Fintype σ]
    (B : Code Γ) (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) :
    Finset (TM1to0.Λ' (program B M)) :=
  TM1to0.trStmts (program B M) (TM1to1.trSupp M S)

/-- A support certificate for the source program induces one for the binary
`TM0`. -/
theorem machine_supports [Fintype Γ] [Fintype σ]
    (B : Code Γ) (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (hS : TM1.Supports M S) :
    TM0.Supports (machine B M) (support B M S : Set _) := by
  apply TM1to0.tr_supports
  exact TM1to1.tr_supports B.enc B.dec M hS

/-- The inhabited finite subtype of the compiled machine's certified support. -/
@[reducible]
noncomputable def finiteStateInhabited [Fintype Γ] [Fintype σ]
    (B : Code Γ) (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (hS : TM1.Supports M S) : Inhabited (support B M S) :=
  TM0FiniteRestriction.supportedInhabited (machine B M) (support B M S)
    (machine_supports B M S hS)

/-- Restrict the binary compiler output to its certified finite state set. -/
noncomputable def finiteMachine [Fintype Γ] [Fintype σ]
    (B : Code Γ) (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (hS : TM1.Supports M S) :
    @TM0.Machine Bool (support B M S) (finiteStateInhabited B M S hS) :=
  TM0FiniteRestriction.machine (machine B M) (support B M S)
    (machine_supports B M S hS)

/-- The finite-state binary machine has exactly the source program's halting
domain on encoded inputs. -/
theorem finite_eval_dom_iff [Fintype Γ] [Fintype σ]
    (B : Code Γ) (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ)
    (hS : TM1.Supports M S) (input : List Γ) :
    (@TM0.eval Bool (support B M S) (finiteStateInhabited B M S hS)
        inferInstance (finiteMachine B M S hS) (encodeInput B input)).Dom ↔
      (TM1.eval M input).Dom :=
  (TM0FiniteRestriction.eval_dom_iff
    (machine B M) (support B M S) (machine_supports B M S hS)
    (encodeInput B input)).trans (eval_dom_iff B M input)

end TM1BinaryAdapter

end Undecidability
