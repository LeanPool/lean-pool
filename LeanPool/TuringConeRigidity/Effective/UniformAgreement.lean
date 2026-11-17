/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformAgreement.lean.
Also incorporates the stronger decision proof from the upstream
OAI/Computability/DegreeRigidity/Effective/StablePair.lean
under the same Apache-2.0 terms.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformRun
public import LeanPool.TuringConeRigidity.Effective.EffectiveWitness
public import Mathlib.Algebra.Order.Ring.Star

/-!
# Uniform Agreement
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformAgreement
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness
  IndexMatrix
open CodingForcing UniformProgram

/-- The two designated uniform computations disagree on some input at this condition. -/
def Disagreement (A : Oracle) (x : ℕ) (p : Condition) : Prop :=
  ∃ n a b, a ≠ b ∧
    a ∈ UniformRun.run A (machine (item x 0)) (machine (item x 1)) p.left n ∧
    b ∈ UniformRun.run A (machine (item x 0)) (machine (item x 2)) p.right n

/-- No permitted extension of the condition produces the designated uniform disagreement. -/
def NoDisagreement (A : Oracle) (x : ℕ) (p : Condition) : Prop :=
  ∀ q, Extends (columns A) p q → ¬ Disagreement A x q

/-- A finite certificate of a permitted extension and disagreeing uniform computation outputs. -/
def Cert (A : Oracle) (v : ℕ) : Prop :=
  let x := (Nat.unpair (Nat.unpair v).1).1
  let p := (Nat.unpair (Nat.unpair v).1).2
  let w := (Nat.unpair v).2
  Extends (columns A) (condition p) (condition (item w 0)) ∧ item w 2 ≠ item w 3 ∧
    item w 2 ∈ UniformRun.run A (machine (item x 0)) (machine (item x 1)) (left (item w 0)) (item
      w 1) ∧
    item w 3 ∈ UniformRun.run A (machine (item x 0)) (machine (item x 2)) (right (item w 0)) (item
      w 1)

theorem cert_sigma (A : Oracle) : Sigma A 1 (Cert A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let x (i : ℕ) := item_primrec.comp (f.comp f) (Primrec.const i)
  let w (i : ℕ) := item_primrec.comp r (Primrec.const i)
  have he := recursive_comp (extends_recursive A) (Primrec₂.natPair.comp (r.comp f) (w 0))
  have hn := recursive_primrecPred A ((Primrec.eq.comp (w 2) (w 3)).not)
  have hl := UniformRun.graph_sigma_of A (x 0) (x 1) (Primrec.encode.comp (left_primrec.comp (w
    0))) (w 1) (w 2)
  have hr := UniformRun.graph_sigma_of A (x 0) (x 2) (Primrec.encode.comp (right_primrec.comp (w
    0))) (w 1) (w 3)
  unfold Cert
  simpa only [Nat.unpair_pair,word,encodek,Option.getD_some] using
    (Form.raise (n := 0) (s := true) he).and ((Form.raise (n := 0) (s := true) hn).and (hl.and hr))

/-- A uniform decision procedure either witnesses disagreement or leaves the
condition code unchanged and certifies permanent agreement. -/
theorem decide_exists_with_unchanged_code (A : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (f v)) ∧
    ∀ x p, Extends (columns A) (condition p) (condition (f (Nat.pair x p))) ∧
      (Disagreement A x (condition (f (Nat.pair x p))) ∨ (f (Nat.pair x p) = p ∧ NoDisagreement A
        x (condition p))) := by
  obtain ⟨search,hs,hsearch⟩ := sigma1_choice (cert_sigma A)
  let out : ℕ → ℕ := fun v => if search v = 0 then (Nat.unpair v).2 else item (search v-1) 0
  have hmap : Primrec (fun v : ℕ => if (Nat.unpair v).2 = 0 then (Nat.unpair (Nat.unpair v).1).2
      else item ((Nat.unpair v).2-1) 0) := by
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    exact Primrec.ite (Primrec.eq.comp r (Primrec.const 0)) (r.comp f)
      (item_primrec.comp (Primrec.nat_sub.comp r (Primrec.const 1)) (Primrec.const 0))
  refine ⟨out,?_,fun x p => ?_⟩
  · exact (total_comp (total_primrec hmap) (total_pair (total_primrec Primrec.id) hs)).of_eq
      (fun v => by simp only [Nat.unpair_pair]; rfl)
  · rcases hsearch (Nat.pair x p) with ⟨hz,hn⟩ | ⟨hp,hc⟩
    · simp only [out,hz,↓reduceIte,Nat.unpair_pair]
      refine ⟨extends_refl _ _,Or.inr ⟨trivial,fun q hpq hd => ?_⟩⟩
      obtain ⟨n,a,b,hab,ha,hb⟩ := hd
      apply hn
      refine ⟨encode [code q,n,a,b],?_⟩
      simpa [Cert,item,word,← show left (code q) = q.left from congrArg Condition.left
        (condition_code q),
        ← show right (code q) = q.right from congrArg Condition.right (condition_code
          q),condition_code] using
        And.intro hpq (And.intro hab (And.intro ha hb))
    · have hz : search (Nat.pair x p) ≠ 0 := by omega
      simp only [out,ite_eq_right hz]
      simp only [Cert,Nat.unpair_pair] at hc
      exact ⟨hc.1,Or.inl ⟨_,_,_,hc.2⟩⟩

theorem decide_exists (A : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (f v)) ∧
    ∀ x p, Extends (columns A) (condition p) (condition (f (Nat.pair x p))) ∧
      (Disagreement A x (condition (f (Nat.pair x p))) ∨ NoDisagreement A x (condition (f
        (Nat.pair x p)))) := by
  obtain ⟨f,hf,hs⟩ := decide_exists_with_unchanged_code A
  refine ⟨f,hf,fun x p => ?_⟩
  obtain ⟨he,hdec⟩ := hs x p
  refine ⟨he,?_⟩
  rcases hdec with hd | ⟨hcode,hn⟩
  · exact Or.inl hd
  · rw [hcode]
    exact Or.inr hn

end TuringRigidity.UniformAgreement

end OAI
