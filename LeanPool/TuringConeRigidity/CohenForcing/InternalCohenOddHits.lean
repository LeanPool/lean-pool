/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/InternalCohenOddHits.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.OrdinalCodes.NumericalCohenSets
public import LeanPool.TuringConeRigidity.CohenForcing.InternalCohenFilters
public import LeanPool.TuringConeRigidity.SetModels.ModelArithmeticComprehension

/-!
# Internal Cohen Odd Hits
-/


@[expose] public section

namespace OAI


namespace TuringRigidity.InternalCohen
open TransitiveNameModel BoundedSetTheory UniformArithmetic Encodable
open ShuffleRequirements CohenBorelForcing CountableForcing
open EncodedForcing (word word_primrec)
attribute [local instance] InternalCollapse.order InternalCollapse.collapsePreorder

theorem oddHit_arith (N : ℕ) : Arith (fun (_ : Oracles) v => OddHit N (word v)) := by
  have hi := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) right_primrec)
    (Primrec.const 1)
  have hn := Arith.pure (fun v => N ≤ right v) (Primrec.nat_le.comp (Primrec.const N) right_primrec)
  have hlen := less hi (Primrec.list_length.comp (word_primrec.comp left_primrec))
  have hb := Arith.pure _ (Primrec.eq.comp
    ((Primrec.list_getD false).comp (word_primrec.comp left_primrec) hi) (Primrec.const true))
  exact (hn.and (hlen.and hb)).ex.congr (fun _ _ => by
    simp only [OddHit,left,right,Nat.unpair_pair])

/-- An arithmetic oracle coding words satisfying the odd-coordinate hitting requirement. -/
noncomputable def oddHitCodes (N : ℕ) : Oracle :=
  arithmeticReal (fun (_ : Oracles) v => OddHit N (word v)) (fun _ => decodeReal (∅ : ZFSet.{0}))

theorem oddHitCodes_true (N n : ℕ) : oddHitCodes N n = true ↔ OddHit N (word n) :=
  arithmeticReal_true _ _ _

theorem oddHitCodes_mem (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M) (N : ℕ) :
    realCode (oddHitCodes N) ∈ M := by
  apply sourceT_arithmetic_comprehension M hM hT (oddHit_arith N)
  intro _
  change realCode (decodeReal (∅ : ZFSet.{0})) ∈ M
  rw [realCode_decodeReal (fun x h => False.elim (ZFSet.notMem_empty x h))]
  exact hM _ (sourceT_omega_mem M hM hT) _ ((mem_omega _).mpr ⟨0,rfl⟩)

theorem groundGeneric_infiniteOdd (M : ZFSet.{0}) (hM : Transitive M) (hT : SourceT M)
    (G : Oracle) (hG : AtomicForcing.GroundGeneric M (pushFilter (realFilter G))) :
    GenericCoding.InfiniteOdd G := by
  apply infiniteOdd_of_hits
  intro N
  have hspec (s : List Bool) := wordImage_spec (OddHit N) (oddHitCodes N) (oddHitCodes_true N) s
  have hd : Dense {p : Condition | wordCode p.word ∈ wordImage (oddHitCodes N)} := by
    intro p
    obtain ⟨s,hps,hs⟩ := (oddHit_denseOpen N).1 p.word
    exact ⟨⟨s⟩,hps,(hspec s).mpr hs⟩
  obtain ⟨p,hp,hpD⟩ := (groundGeneric_iff M _).mp hG (wordImage (oddHitCodes N))
    (wordImage_mem M hM hT _ (oddHitCodes_mem M hM hT N)) hd
  rw [pull_push] at hp
  exact ⟨p.word,(hspec p.word).mp hpD,hp⟩

end TuringRigidity.InternalCohen

end OAI
