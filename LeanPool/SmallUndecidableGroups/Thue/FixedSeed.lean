/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Machine.FixedTuringMachine
public import LeanPool.SmallUndecidableGroups.Machine.SupportedTM1Thue
public import LeanPool.SmallUndecidableGroups.Thue.FiniteReindex

/-!
# FixedSeed

Part of the dependency closure of the small undecidable group constructions.
-/

@[expose] public section

namespace Undecidability
namespace FixedMachine

open Turing

/-- The canonical binary block code used to feed the finite Post bridge. -/
noncomputable def thueBinaryCode : TM1BinaryAdapter.Code TapeSymbol :=
  TM1BinaryAdapter.canonicalCode TapeSymbol

/-- The finite alphabet of the Thue system simulating a specified partial recursive code. -/
noncomputable abbrev ThueAlphabet (c : ToPartrec.Code) :=
  SupportedTM1Thue.Alphabet thueBinaryCode oneTapeProgram (oneTapeSupport c)

/-- The finitely supported Post machine simulating a specified partial recursive code. -/
noncomputable def thuePostMachine (c : ToPartrec.Code) :
    PostMachine.Machine
      (TM0PostAdapter.Phase
        (SupportedTM1Thue.State thueBinaryCode oneTapeProgram
          (oneTapeSupport c))) := by
  letI : Inhabited OneTapeState := oneTapeStateInhabited c
  exact SupportedTM1Thue.postMachine thueBinaryCode oneTapeProgram
    (oneTapeSupport c) (oneTapeProgram_supports c)

/-- The Thue system simulating a specified partial recursive code. -/
noncomputable def thueSystem (c : ToPartrec.Code) :
    ThueSystem (ThueAlphabet c) :=
  PostMachine.system (thuePostMachine c)

/-- The encoded initial configuration for a specified code and tape input. -/
noncomputable def thueStart (c : ToPartrec.Code) (input : List TapeSymbol) :
    List (ThueAlphabet c) := by
  letI : Inhabited OneTapeState := oneTapeStateInhabited c
  exact SupportedTM1Thue.start thueBinaryCode oneTapeProgram
    (oneTapeSupport c) (oneTapeProgram_supports c) input

theorem thue_iff_oneTape_eval_dom (c : ToPartrec.Code)
    (input : List TapeSymbol) :
    ThueEq (thueSystem c) (thueStart c input)
        (PostMachine.target : List (ThueAlphabet c)) ↔
      letI : Inhabited OneTapeState := oneTapeStateInhabited c
      (TM1.eval oneTapeProgram input).Dom := by
  let : Inhabited OneTapeState := oneTapeStateInhabited c
  exact SupportedTM1Thue.thue_iff_eval_dom thueBinaryCode oneTapeProgram
    (oneTapeSupport c) (oneTapeProgram_supports c) input

theorem thueSystem_finite (c : ToPartrec.Code) : (thueSystem c).Finite := by
  let : Inhabited OneTapeState := oneTapeStateInhabited c
  exact SupportedTM1Thue.system_finite thueBinaryCode oneTapeProgram
    (oneTapeSupport c) (oneTapeProgram_supports c)

noncomputable instance thueAlphabetFintype (c : ToPartrec.Code) :
    Fintype (ThueAlphabet c) := Fintype.ofFinite _

instance thueAlphabetNonempty (c : ToPartrec.Code) :
    Nonempty (ThueAlphabet c) := ⟨PostMachine.Symbol.leftMarker⟩

noncomputable instance thueAlphabetPrimcodable (c : ToPartrec.Code) :
    Primcodable (ThueAlphabet c) :=
  Primcodable.ofEquiv (Fin (Fintype.card (ThueAlphabet c)))
    (Fintype.equivFin (ThueAlphabet c))

theorem thueStart_computable (c : ToPartrec.Code) :
    Computable (thueStart c) := by
  let : Inhabited OneTapeState := oneTapeStateInhabited c
  exact SupportedTM1Thue.start_computable thueBinaryCode oneTapeProgram
    (oneTapeSupport c) (oneTapeProgram_supports c)

theorem thue_target_not_computable (c : ToPartrec.Code)
    (hc : ∀ n, (c.eval [n]).Dom ↔ (fixedUniversalEval n).Dom) :
    ¬ ComputablePred fun Q : List (ThueAlphabet c) =>
      ThueEq (thueSystem c) Q
        (PostMachine.target : List (ThueAlphabet c)) := by
  apply not_computablePred_of_manyOneReducible
    (oneTape_halting_not_computable c hc)
  exact ⟨thueStart c, thueStart_computable c,
    fun input => (thue_iff_oneTape_eval_dom c input).symm⟩

/-- A finite fixed-target Thue seed obtained from
Mathlib's universal partial-recursive evaluator and the explicit Post
simulation. -/
theorem exists_finiteFixedTargetSeed :
    Nonempty Thue.Matiyasevich1993.FiniteFixedTargetSeed := by
  obtain ⟨c, hc⟩ := exists_fixed_universal_code
  obtain ⟨seed, _, _⟩ :=
    Thue.Matiyasevich1993.FiniteReindex.seed_of_finite_system
      (thueSystem c) (thueSystem_finite c)
      (PostMachine.target : List (ThueAlphabet c))
      (thue_target_not_computable c hc)
  exact ⟨seed⟩

end FixedMachine
end Undecidability
