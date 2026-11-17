/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenEffectiveGeneric.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenWordCodeGraph
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenFilters
public import LeanPool.TuringConeRigidity.SetModels.ModelArithmeticComprehension
public import LeanPool.TuringConeRigidity.Computability.ArithmeticOracles
public import LeanPool.TuringConeRigidity.Effective.EffectiveCohen

/-!
# Cohen Effective Generic
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory Encodable OracleJump
open UniformArithmetic CohenBorelForcing CountableForcing
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

def WordDecision (Y : Oracle) (e : ℕ) (p : List Bool) : Prop :=
  Halts Y e (encode p) ∨ ∀ q : List Bool, p <+: q → ¬ Halts Y e (encode q)

theorem wordDecision_arith (e : ℕ) :
    Arith (fun O n => WordDecision (O 0) e (EncodedForcing.word n)) := by
  let w := EncodedForcing.word
  have hw : Primrec w := EncodedForcing.word_primrec
  have hp : Arith (fun (_ : Oracles) v => w (left v) <+: w (right v)) := by
    have h := Arith.pure _ (Primrec.eq.comp (hw.comp left_primrec)
      (Primrec.list_take.comp (Primrec.list_length.comp (hw.comp left_primrec))
        (hw.comp right_primrec)))
    exact h.congr (fun _ _ => List.prefix_iff_eq_take.symm)
  have hhalt := halts_arith (parameter_arith 0) (Primrec.const 0)
    (Primrec.const e) (Primrec.encode.comp hw)
  have hno := (hp.imp (hhalt.comp _ right_primrec).neg).all
  apply (hhalt.or hno).congr
  intro O n
  simp only [left,right,Nat.unpair_pair]
  constructor
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (fun q hq => by
        have hq' : w n <+: w (encode q) := by simpa [w,EncodedForcing.word] using hq
        simpa [w,EncodedForcing.word] using h (encode q) hq')
  · rintro (h|h)
    · exact Or.inl h
    · exact Or.inr (fun k hk => h (w k) hk)

noncomputable def decisionCodes (Y : Oracle) (e : ℕ) : Oracle :=
  arithmeticReal (fun O n => WordDecision (O 0) e (EncodedForcing.word n)) (fun _ => Y)

theorem decisionCodes_true (Y : Oracle) (e n : ℕ) :
    decisionCodes Y e n = true ↔ WordDecision Y e (EncodedForcing.word n) :=
  arithmeticReal_true _ _ n

theorem decisionCodes_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (Y : Oracle) (hY : realCode Y ∈ M) (e : ℕ) : realCode (decisionCodes Y e) ∈ M :=
  sourceT_arithmetic_comprehension M hM hT (wordDecision_arith e) (fun _ => Y) (fun _ => hY)

noncomputable def decisionSet (Y : Oracle) (e : ℕ) : ZFSet.{0} :=
  ZFSet.sep (fun q => ∃ n ∈ realCode (decisionCodes Y e),
    ZFSet.pair n q ∈ wordCodeGraph) conditions

theorem decisionSet_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (Y : Oracle) (hY : realCode Y ∈ M) (e : ℕ) : decisionSet Y e ∈ M := by
  let d := cons (realCode (decisionCodes Y e)) (fun _ => wordCodeGraph)
  have hd : ∀ i, d i ∈ M := by
    intro i
    cases i with
    | zero => exact decisionCodes_mem M hM hT Y hY e
    | succ i => exact wordCodeGraph_mem M hM hT
  have hs := sep_mem M hM hT.separation.finitePrefix.bounded
    (.existsMem 1 (.pairMem 0 1 3)) d hd (conditions_mem M hM hT)
  simpa only [Formula.Eval,Formula.eval_pairMem,cons_zero,cons_succ,d,decisionSet] using hs

theorem wordCode_mem_decisionSet (Y : Oracle) (e : ℕ) (p : List Bool) :
    wordCode p ∈ decisionSet Y e ↔ WordDecision Y e p := by
  rw [decisionSet,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,x,hx,hq⟩
    obtain ⟨n,rfl⟩ := (mem_omega x).mp (realCode_subset _ hx)
    have hp := wordCode_injective ((pair_mem_wordCodeGraph _ _).mp hq)
    rw [hp]
    exact (decisionCodes_true Y e n).mp ((natSet_mem_realCode _ _).mp hx)
  · intro h
    refine ⟨(mem_conditions _).mpr ⟨_,wordCode_function _⟩,natSet (encode p),?_,
      (canonical_wordCodeGraph p _).mpr rfl⟩
    apply (natSet_mem_realCode _ _).mpr
    apply (decisionCodes_true Y e (encode p)).mpr
    simpa [EncodedForcing.word] using h

theorem decisionSet_dense (Y : Oracle) (e : ℕ) :
    Dense {p : Condition | wordCode p.word ∈ decisionSet Y e} := by
  classical
  intro p
  by_cases h : ∃ q : List Bool, p.word <+: q ∧ Halts Y e (encode q)
  · obtain ⟨q,hpq,hq⟩ := h
    exact ⟨⟨q⟩,hpq,(wordCode_mem_decisionSet _ _ _).mpr (Or.inl hq)⟩
  · exact ⟨p,le_refl p,(wordCode_mem_decisionSet _ _ _).mpr
      (Or.inr (fun q hpq hq => h ⟨q,hpq,hq⟩))⟩

theorem groundGeneric_oneGeneric (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (A Y : Oracle) (hY : realCode Y ∈ M)
    (hA : AtomicForcing.GroundGeneric M (pushFilter (realFilter A))) :
    EffectiveCohen.OneGeneric Y A := by
  intro e
  obtain ⟨p,hp,hd⟩ := (groundGeneric_iff M _).mp hA (decisionSet Y e)
    (decisionSet_mem M hM hT Y hY e) (decisionSet_dense Y e)
  rw [pull_push] at hp
  exact ⟨p.word,fun n hn => (hp n hn).symm,(wordCode_mem_decisionSet Y e p.word).mp hd⟩

end TuringRigidity.InternalCohen

end OAI
