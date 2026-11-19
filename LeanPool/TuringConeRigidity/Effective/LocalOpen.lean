/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalOpen.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalColumnCertificates
public import LeanPool.TuringConeRigidity.CohenForcing.EffectiveForcing

/-!
# Local Open
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalOpen
open Encodable UniformOracle ArithmeticHierarchy OracleJump EffectiveWitness EncodedForcing
  CodingForcing
open LocalColumnCertificates

theorem uniform_open_decision (B : Oracle) :
    ∃ step : ℕ → ℕ,
      Nat.RecursiveIn {oracleFunction (jump B)} (fun x => Part.some (step x)) ∧
      ∀ (F : ℕ → Oracle) codes e p, Presents B F codes (active p) →
        Extends F (condition p) (condition (step (encode [codes,e,p]))) ∧
        (Halts B e (step (encode [codes,e,p])) ∨
          (step (encode [codes,e,p]) = p ∧
            ∀ q, Extends F (condition p) (condition q) → ¬ Halts B e q)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let req (i : ℕ) := item_primrec.comp f (Primrec.const i)
  let P : ℕ → Prop := fun v =>
    Extension B (encode [item (Nat.unpair v).1 0,item (Nat.unpair v).1 2,(Nat.unpair v).2]) ∧
      Halts B (item (Nat.unpair v).1 1) (Nat.unpair v).2
  have hext := (extension_sigma B).comp (Primrec.encode.comp
    (Primrec.list_cons.comp (req 0) (Primrec.list_cons.comp (req 2)
      (Primrec.list_cons.comp r (Primrec.const [])))))
  have hhalt := (halts_sigma B).comp (Primrec₂.natPair.comp (req 1) r)
  have hP : Sigma B 1 P := by
    simpa only [P,Nat.unpair_pair] using hext.and hhalt
  obtain ⟨g,hg,hs⟩ := sigma1_choice hP
  let step : ℕ → ℕ := fun x => EffectiveForcing.answer (Nat.pair (item x 2) (g x))
  have hstep := total_comp (total_primrec (O := {oracleFunction (jump B)})
    EffectiveForcing.answer_primrec)
    (total_pair (total_primrec (item_primrec.comp Primrec.id (Primrec.const 2))) hg)
  refine ⟨step,hstep,fun F codes e p h => ?_⟩
  rcases hs (encode [codes,e,p]) with ⟨hz,hn⟩ | ⟨hp,hw⟩
  · have he : step (encode [codes, e, p]) = p := by
      simp only [step, EffectiveForcing.answer, Nat.unpair_pair, ite_eq_left hz, item, encodek,
        Option.getD_some, List.getD_cons_zero, List.getD_cons_succ]
    rw [he]
    refine ⟨extends_refl _ _,Or.inr ⟨rfl,fun q hq hhalt => ?_⟩⟩
    apply hn
    refine ⟨q,?_⟩
    simpa only
      [P,Nat.unpair_pair,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
      using
      And.intro ((extension_condition_iff h).2 hq) hhalt
  · have hz : g (encode [codes,e,p]) ≠ 0 := by omega
    have he : step (encode [codes, e, p]) = g (encode [codes, e, p]) - 1 := by
      simp only [step, EffectiveForcing.answer, Nat.unpair_pair, ite_eq_right hz]
    rw [he]
    have hh : Extension B (encode [codes,p,g (encode [codes,e,p])-1]) ∧ Halts B e (g (encode
      [codes,e,p])-1) := by
      simpa only
        [P,Nat.unpair_pair,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
        using hw
    exact ⟨(extension_condition_iff h).1 hh.1,Or.inl hh.2⟩

end TuringRigidity.LocalOpen

end OAI
