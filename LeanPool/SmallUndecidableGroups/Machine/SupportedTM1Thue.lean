/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Machine.TM1BinaryAdapter
public import LeanPool.SmallUndecidableGroups.Machine.TM0PostAdapter

/-!
# SupportedTM1Thue

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability

open Turing

namespace SupportedTM1Thue

variable {Γ Λ σ : Type*} [Inhabited Γ] [Inhabited Λ] [Inhabited σ]
variable [Fintype Γ] [Fintype σ]

/-- The finite supported state type used in the one-tape-to-Thue reduction. -/
noncomputable abbrev State (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) :=
  TM1BinaryAdapter.support B M S

/-- The alphabet of the Thue system simulating the supported one-tape machine. -/
noncomputable abbrev Alphabet (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) :=
  PostMachine.Symbol (TM0PostAdapter.Phase (State B M S))

/-- The combined write-and-move machine obtained from a supported source
`TM1`, after binary compilation and restriction to finite state. -/
noncomputable def postMachine (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S) :
    PostMachine.Machine (TM0PostAdapter.Phase (State B M S)) :=
  @TM0PostAdapter.machine (State B M S)
    (TM1BinaryAdapter.finiteStateInhabited B M S hS)
    (TM1BinaryAdapter.finiteMachine B M S hS)

/-- The Thue word encoding the initial configuration on a source input. -/
noncomputable def start (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S)
    (input : List Γ) : List (Alphabet B M S) :=
  PostMachine.encode <|
    @TM0PostAdapter.init (State B M S)
      (TM1BinaryAdapter.finiteStateInhabited B M S hS)
      (TM1BinaryAdapter.encodeInput B input)

/-- The binary initial configuration of the one-tape simulation. -/
def binaryStart {Q : Type*} [Inhabited Q] (input : List Bool) :
    List (PostMachine.Symbol (TM0PostAdapter.Phase Q)) :=
  PostMachine.encode (TM0PostAdapter.init input :
    PostMachine.Config (TM0PostAdapter.Phase Q))

private theorem binaryStart_computable {Q : Type*} [Inhabited Q]
    [Primcodable (PostMachine.Symbol (TM0PostAdapter.Phase Q))] :
    Computable (@binaryStart Q inferInstance) := by
  let tape : Bool → PostMachine.Symbol (TM0PostAdapter.Phase Q) :=
    PostMachine.Symbol.tape
  have htape : Computable tape :=
    (Primrec.dom_finite tape).to_comp
  have hhead : Computable fun input : List Bool => tape input.headI :=
    htape.comp Primrec.list_headI.to_comp
  have htail : Computable fun input : List Bool =>
      input.tail.map tape :=
    (Primrec.list_map Primrec.list_tail
      ((Primrec.dom_finite tape).comp₂ Primrec₂.right)).to_comp
  have hprefix : Computable fun input : List Bool =>
      [PostMachine.Symbol.leftMarker, tape input.headI,
        PostMachine.Symbol.state (TM0PostAdapter.Phase.normal (default : Q))] :=
    Computable.list_cons.comp
      (Computable.const PostMachine.Symbol.leftMarker)
      (Computable.list_cons.comp hhead
        (Computable.const
          [PostMachine.Symbol.state
            (TM0PostAdapter.Phase.normal (default : Q))]))
  have hsuffix : Computable fun input : List Bool =>
      input.tail.map tape ++ [PostMachine.Symbol.rightMarker] :=
    Computable.list_append.comp htail
      (Computable.const [PostMachine.Symbol.rightMarker])
  exact (Computable.list_append.comp hprefix hsuffix).of_eq fun input => by
    cases input <;>
      simp [binaryStart, TM0PostAdapter.init, PostMachine.encode,
        PostMachine.encodeTape, tape]

/-- The reduction from source input words to initial Thue words is
computable. -/
theorem start_computable (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S)
    [Primcodable Γ] [Primcodable (Alphabet B M S)] :
    Computable (start B M S hS) := by
  let : Inhabited (State B M S) :=
    TM1BinaryAdapter.finiteStateInhabited B M S hS
  exact (binaryStart_computable (Q := State B M S)).comp
    (TM1BinaryAdapter.encodeInput_computable B)

/-- The resulting finite fixed-target Thue system recognizes precisely the
halting inputs of the supported source program. -/
theorem thue_iff_eval_dom (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S)
    (input : List Γ) :
    ThueEq (PostMachine.system (postMachine B M S hS))
        (start B M S hS input)
        (PostMachine.target : List (Alphabet B M S)) ↔
      (TM1.eval M input).Dom := by
  let : Inhabited (State B M S) :=
    TM1BinaryAdapter.finiteStateInhabited B M S hS
  exact (TM0PostAdapter.thue_iff_tm0_eval_dom
    (TM1BinaryAdapter.finiteMachine B M S hS)
    (TM1BinaryAdapter.encodeInput B input)).trans
      (TM1BinaryAdapter.finite_eval_dom_iff B M S hS input)

/-- The Thue presentation used above has finitely many rules. -/
theorem system_finite (B : TM1BinaryAdapter.Code Γ)
    (M : Λ → TM1.Stmt Γ Λ σ) (S : Finset Λ) (hS : TM1.Supports M S) :
    Set.Finite (PostMachine.system (postMachine B M S hS)) := by
  let : Inhabited (State B M S) :=
    TM1BinaryAdapter.finiteStateInhabited B M S hS
  exact TM0PostAdapter.thue_system_finite
    (TM1BinaryAdapter.finiteMachine B M S hS)

end SupportedTM1Thue

end Undecidability
