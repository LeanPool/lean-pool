/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/OrdinalCodes/NumericalCohenProductSets.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.TaggedProductConditions
public import LeanPool.TuringConeRigidity.CohenForcing.CohenWordCodeGraph

/-!
# Numerical Cohen Product Sets
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.NumericalCohenProductSets
open TransitiveNameModel BoundedSetTheory SetModelFunctions SetModelArithmetic
open InternalCohen Encodable UniformArithmetic
open EncodedForcing (word)
open TaggedProductConditions (code)

/-- The set-coded tagged word pairs whose natural-number codes are selected by `B`. -/
noncomputable def image (c : ZFSet.{0}) (B : Oracle) : ZFSet.{0} :=
  c.sep (fun z => ∃ n : ℕ, B n = true ∧
    z = code (wordCode (word (left n))) (wordCode (word (right n))))

theorem image_mem (M c : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (hc : c ∈ M) (B : Oracle) (hB : realCode B ∈ M) : image c B ∈ M := by
  let C : Context M := ⟨hM,hT.pairing,hT.union,hT.powerSet,
    hT.separation.finitePrefix.bounded,hT.infinity⟩
  obtain ⟨gl,hgl,hl⟩ := primrec_graph C left_primrec
  obtain ⟨gr,hgr,hr⟩ := primrec_graph C right_primrec
  let e := cons (realCode B) (cons ZFSet.omega (cons conditions
    (cons gl (cons gr (cons wordCodeGraph (cons (natSet 0) (fun _ => natSet 1)))))))
  have he : ∀ i, e i ∈ M := by
    intro i
    rcases i with _|_|_|_|_|_|_|i
    · exact hB
    · exact C.omega_mem
    · exact conditions_mem M hM hT
    · exact hgl
    · exact hgr
    · exact wordCodeGraph_mem M hM hT
    all_goals exact hM _ C.omega_mem _ ((mem_omega _).mpr ⟨_,rfl⟩)
  let φ : Formula := .existsMem 1 (.existsMem 3 (.existsMem 4
    (.existsMem 6 (.existsMem 7
      (.conj (.pairMem 4 3 9) (.conj (.pairMem 4 2 10)
        (.conj (.pairMem 3 1 11) (.conj (.pairMem 2 0 11)
          (TaggedProductConditions.codeFormula 1 0 5 12 13)))))))))
  have hspec (z : ZFSet.{0}) : φ.Eval (cons z e) ↔
      ∃ n : ℕ, B n = true ∧
        z = code (wordCode (word (left n))) (wordCode (word (right n))) := by
    have hcode (leftCondition rightCondition leftIndex rightIndex index : ZFSet.{0}) :
        (TaggedProductConditions.codeFormula 1 0 5 12 13).Eval
          (cons rightCondition (cons leftCondition (cons rightIndex
            (cons leftIndex (cons index (cons z e)))))) ↔
              z = code leftCondition rightCondition :=
      TaggedProductConditions.codeFormula_spec 1 0 5 12 13 _ rfl rfl
    simp only [φ,Formula.Eval,Formula.eval_pairMem,hcode,
      cons_zero,cons_succ,e]
    constructor
    · rintro ⟨k,hk,i,hi,j,hj,u,_,v,_,hli,hrj,hu,hv,hz⟩
      obtain ⟨n,rfl⟩ := (mem_omega k).mp (realCode_subset B hk)
      obtain ⟨a,rfl⟩ := (mem_omega i).mp hi
      obtain ⟨b,rfl⟩ := (mem_omega j).mp hj
      have ha := (hl n a).mp hli
      have hb := (hr n b).mp hrj
      subst a
      subst b
      rw [(pair_mem_wordCodeGraph _ _).mp hu,(pair_mem_wordCodeGraph _ _).mp hv] at hz
      exact ⟨n,(natSet_mem_realCode B n).mp hk,hz⟩
    · rintro ⟨n,hn,hz⟩
      exact ⟨natSet n,(natSet_mem_realCode B n).mpr hn,
        natSet (left n),(mem_omega _).mpr ⟨_,rfl⟩,
        natSet (right n),(mem_omega _).mpr ⟨_,rfl⟩,
        wordCode (word (left n)),(mem_conditions _).mpr ⟨_,wordCode_function _⟩,
        wordCode (word (right n)),(mem_conditions _).mpr ⟨_,wordCode_function _⟩,
        (hl _ _).mpr rfl,(hr _ _).mpr rfl,
        (pair_mem_wordCodeGraph _ _).mpr rfl,(pair_mem_wordCodeGraph _ _).mpr rfl,hz⟩
  have hs := sep_mem M hM C.separation φ e he hc
  have heq : c.sep (fun z => φ.Eval (cons z e)) = image c B := by
    apply ZFSet.ext
    intro z
    simp only [image,ZFSet.mem_sep,hspec]
  exact heq ▸ hs

theorem image_spec (c : ZFSet.{0})
    (hcs : ∀ z, z ∈ c ↔ ∃ p ∈ conditions, ∃ s ∈ conditions, z = code p s)
    (P : List Bool → List Bool → Prop) (B : Oracle)
    (hB : ∀ n, B n = true ↔ P (word (left n)) (word (right n)))
    (s t : List Bool) : code (wordCode s) (wordCode t) ∈ image c B ↔ P s t := by
  rw [image,ZFSet.mem_sep]
  constructor
  · rintro ⟨_,n,hn,he⟩
    obtain ⟨hs,ht⟩ := (TaggedProductConditions.code_injective _ _ _ _).mp he
    rw [wordCode_injective hs,wordCode_injective ht]
    exact (hB n).mp hn
  · intro h
    refine ⟨(hcs _).mpr ⟨_,(mem_conditions _).mpr ⟨_,wordCode_function _⟩,
      _,(mem_conditions _).mpr ⟨_,wordCode_function _⟩,rfl⟩,
      Nat.pair (encode s) (encode t),?_,?_⟩
    · apply (hB _).mpr
      simpa [left,right,word] using h
    · simp [left,right,word]

end TuringRigidity.NumericalCohenProductSets

end OAI
