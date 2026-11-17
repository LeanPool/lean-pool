/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalAgreement.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalColumnCertificates

/-!
# Local Agreement
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalAgreement
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness
  IndexMatrix
open CodingForcing UniformProgram LocalColumnCertificates

def NoDisagreement (B : Oracle) (F : ℕ → Oracle) (x : ℕ) (p : Condition) : Prop :=
  ∀ q, Extends F p q → ¬ UniformAgreement.Disagreement B x q

def Cert (B : Oracle) (v : ℕ) : Prop :=
  let req := (Nat.unpair v).1
  let x := item req 1
  let p := item req 2
  let w := (Nat.unpair v).2
  Extension B (encode [item req 0,p,item w 0]) ∧ item w 2 ≠ item w 3 ∧
    item w 2 ∈ UniformRun.run B (machine (item x 0)) (machine (item x 1)) (left (item w 0)) (item
      w 1) ∧
    item w 3 ∈ UniformRun.run B (machine (item x 0)) (machine (item x 2)) (right (item w 0)) (item
      w 1)

theorem cert_sigma (B : Oracle) : Sigma B 1 (Cert B) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let req (i : ℕ) := item_primrec.comp f (Primrec.const i)
  let x (i : ℕ) := item_primrec.comp (req 1) (Primrec.const i)
  let w (i : ℕ) := item_primrec.comp r (Primrec.const i)
  have he := (extension_sigma B).comp (Primrec.encode.comp
    (Primrec.list_cons.comp (req 0) (Primrec.list_cons.comp (req 2)
      (Primrec.list_cons.comp (w 0) (Primrec.const [])))))
  have hn := recursive_primrecPred B ((Primrec.eq.comp (w 2) (w 3)).not)
  have hl := UniformRun.graph_sigma_of B (x 0) (x 1) (Primrec.encode.comp (left_primrec.comp (w
    0))) (w 1) (w 2)
  have hr := UniformRun.graph_sigma_of B (x 0) (x 2) (Primrec.encode.comp (right_primrec.comp (w
    0))) (w 1) (w 3)
  unfold Cert
  simpa only [Nat.unpair_pair,word,encodek,Option.getD_some] using
    he.and ((Form.raise (n := 0) (s := true) hn).and (hl.and hr))

theorem cert_iff {B : Oracle} {F : ℕ → Oracle} {codes p : ℕ}
    (h : Presents B F codes (active p)) (x w : ℕ) :
    Cert B (Nat.pair (encode [codes,x,p]) w) ↔
      Extends F (condition p) (condition (item w 0)) ∧ item w 2 ≠ item w 3 ∧
      item w 2 ∈ UniformRun.run B (machine (item x 0)) (machine (item x 1)) (left (item w 0))
        (item w 1) ∧
      item w 3 ∈ UniformRun.run B (machine (item x 0)) (machine (item x 2)) (right (item w 0))
        (item w 1) := by
  simp only
    [Cert,Nat.unpair_pair,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
  exact and_congr (extension_condition_iff h) Iff.rfl

theorem decide_exists (B : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump B)} (fun v => Part.some (f v)) ∧
    ∀ (F : ℕ → Oracle) codes x p, Presents B F codes (active p) →
      Extends F (condition p) (condition (f (encode [codes,x,p]))) ∧
      (UniformAgreement.Disagreement B x (condition (f (encode [codes,x,p]))) ∨
        (f (encode [codes,x,p]) = p ∧ NoDisagreement B F x (condition p))) := by
  obtain ⟨search,hs,hsearch⟩ := sigma1_choice (cert_sigma B)
  let out : ℕ → ℕ := fun req => if search req = 0 then item req 2 else item (search req-1) 0
  have hmap : Primrec (fun v : ℕ => if (Nat.unpair v).2 = 0 then item (Nat.unpair v).1 2
      else item ((Nat.unpair v).2-1) 0) := by
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    exact Primrec.ite (Primrec.eq.comp r (Primrec.const 0)) (item_primrec.comp f (Primrec.const 2))
      (item_primrec.comp (Primrec.nat_sub.comp r (Primrec.const 1)) (Primrec.const 0))
  refine ⟨out,?_,fun F codes x p h => ?_⟩
  · exact (total_comp (total_primrec hmap) (total_pair (total_primrec Primrec.id) hs)).of_eq
      (fun v => by simp only [Nat.unpair_pair]; rfl)
  · rcases hsearch (encode [codes,x,p]) with ⟨hz,hn⟩ | ⟨hp,hc⟩
    · have hout : out (encode [codes, x, p]) = p := by
        simp only [out, ite_eq_left hz, item, encodek, Option.getD_some, List.getD_cons_zero,
          List.getD_cons_succ]
      rw [hout]
      refine ⟨extends_refl _ _,Or.inr ⟨rfl,fun q hpq hd => ?_⟩⟩
      obtain ⟨n,a,b,hab,ha,hb⟩ := hd
      apply hn
      refine ⟨encode [code q,n,a,b],(cert_iff h x _).2 ?_⟩
      simpa [item,← show left (code q) = q.left from congrArg Condition.left (condition_code q),
        ← show right (code q) = q.right from congrArg Condition.right (condition_code
          q),condition_code] using
        And.intro hpq (And.intro hab (And.intro ha hb))
    · have hz : search (encode [codes,x,p]) ≠ 0 := by omega
      simp only [out,ite_eq_right hz]
      have hc' := (cert_iff h x _).1 hc
      exact ⟨hc'.1,Or.inl ⟨_,_,_,hc'.2⟩⟩

end TuringRigidity.LocalAgreement

end OAI
