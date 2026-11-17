/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/StablePair.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformPair
public import LeanPool.TuringConeRigidity.Effective.CodingRequirements

/-!
# Stable Pair
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.StablePair
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness
  IndexMatrix
open CodingForcing UniformProgram UniformAgreement UniformPair

theorem decide_stable_exists (A : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (f v)) ∧
    ∀ x p, Extends (columns A) (condition p) (condition (f (Nat.pair x p))) ∧
      (Disagreement A x (condition (f (Nat.pair x p))) ∨ (f (Nat.pair x p) = p ∧ NoDisagreement A
        x (condition p))) := by
  exact UniformAgreement.decide_exists_with_unchanged_code A

theorem pair_stable_exists (A : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (f v)) ∧
    ∀ x p, Extends (columns A) (condition p) (condition (f (Nat.pair x p))) ∧
      (Disagreement A x (condition (f (Nat.pair x p))) ∨
        (NoDisagreement A x (condition p) ∧ f (Nat.pair x p) = next A (Nat.pair x p))) := by
  obtain ⟨d,hd,hds⟩ := decide_stable_exists A
  let f := fun v => next A (Nat.pair (Nat.unpair v).1 (d v))
  refine ⟨f,?_,fun x p => ?_⟩
  · have hh := total_comp (next_recursive A) (total_pair
      (total_primrec (Primrec.fst.comp Primrec.unpair)) hd)
    exact hh.of_eq (fun v => rfl)
  · obtain ⟨hp,hm⟩ := hds x p
    have hq := (next_extends A (Nat.pair x (d (Nat.pair x p)))).1
    simp only [Nat.unpair_pair] at hq
    refine ⟨?_,?_⟩
    · simpa only [f,Nat.unpair_pair] using extends_trans hp hq
    · rcases hm with hm | ⟨he,hm⟩
      · exact Or.inl (by simpa only [f,Nat.unpair_pair] using disagreement_mono hq hm)
      · exact Or.inr ⟨hm,by simp only [f,Nat.unpair_pair,he]⟩

theorem next_precise (A : Oracle) (x p : ℕ)
    (hn : UniformAgreement.NoDisagreement A x (condition p)) :
    Extends (columns A) (condition p) (condition (next A (Nat.pair x p))) ∧
    (condition (next A (Nat.pair x p))).active = (condition p).active ∧
    ((condition (next A (Nat.pair x p)) = condition p ∧
      ((¬ ∃ z, UniformSplit.SplitCert A (Nat.pair (request (Nat.pair x p)) z)) ∨
      (∃ w, UniformSplit.PointCert A (Nat.pair (request (Nat.pair x p)) w) ∧
        CodingLocation (columns A) (condition p) (item w 2)))) ∨
      ∃ i n, (i = 1 ∨ i = 2) ∧ ∀ q, Extends (columns A) (condition (next A (Nat.pair x p))) q →
        ∀ a, a ∉ UniformRun.run A (machine (item x 0)) (machine (item x i))
          (if i = 1 then q.left else q.right) n) := by
  exact UniformPair.next_spec_with_unchanged_condition A x p hn

/-- A stable pair requirement is settled by disagreement or permanent divergence of one side. -/
def Decisive (A : Oracle) (x : ℕ) (p : Condition) : Prop :=
  Disagreement A x p ∨ ∃ i n, (i = 1 ∨ i = 2) ∧ ∀ q, Extends (columns A) p q →
    ∀ a, a ∉ UniformRun.run A (machine (item x 0)) (machine (item x i))
      (if i = 1 then q.left else q.right) n

/-- Select the pair procedure supplied by the stable-pair existence theorem. -/
noncomputable def procedure (A : Oracle) : ℕ → ℕ := Classical.choose (pair_stable_exists A)

theorem procedure_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (procedure A v)) :=
  (Classical.choose_spec (pair_stable_exists A)).1

theorem changed_decisive (A : Oracle) (x p : ℕ)
    (hchange : (condition (procedure A (Nat.pair x p))).left ≠ (condition p).left ∨
      (condition (procedure A (Nat.pair x p))).right ≠ (condition p).right) :
    Decisive A x (condition (procedure A (Nat.pair x p))) := by
  obtain ⟨_,hd | ⟨hn,he⟩⟩ := (Classical.choose_spec (pair_stable_exists A)).2 x p
  · exact Or.inl hd
  · change procedure A (Nat.pair x p) = _ at he
    rw [he] at hchange ⊢
    rcases (next_precise A x p hn).2.2 with ⟨hunchanged,_⟩ | hdiv
    · rw [hunchanged] at hchange
      exact False.elim (hchange.elim (fun h => h rfl) (fun h => h rfl))
    · exact Or.inr hdiv

theorem decisive_excludes_common {A Y G₀ G₁ Z : Oracle} {x : ℕ} {p : Condition}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item x 0))) = oracleFunction Y)
    (h₀ : CommonIdeal.Extends G₀ p.left) (h₁ : CommonIdeal.Extends G₁ p.right)
    (he₀ : OracleCode.eval (oracleFunction (join Y G₀)) (meaning (machine (item x 1))) =
      oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y G₁)) (meaning (machine (item x 2))) =
      oracleFunction Z)
    (hd : Decisive A x p) : False := by
  have hr (i : ℕ) (s : List Bool) (n : ℕ) :
      UniformRun.run A (machine (item x 0)) (machine (item x i)) s n =
        CommonIdeal.run Y (meaning (machine (item x i))) s n := by
    simp only [UniformRun.run,hbase,CommonIdeal.run]
  rcases hd with ⟨n,a,b,hab,ha,hb⟩ | ⟨i,n,hi,hdiv⟩
  · rw [hr] at ha hb
    have ha' := CommonIdeal.run_total h₀ n a ha
    have hb' := CommonIdeal.run_total h₁ n b hb
    rw [he₀] at ha'
    rw [he₁] at hb'
    exact hab (Part.mem_unique ha' hb')
  · rcases hi with rfl | rfl
    · obtain ⟨s,hs,hv⟩ := CommonIdeal.run_finite_extension h₀ n (CommonIdeal.bit (Z n)) (by
        rw [he₀]; exact Part.mem_some _)
      obtain ⟨q,hpq,hq⟩ := CodingForcing.arbitrary_left_extension (columns A) p s hs
      have hh := hdiv q hpq (CommonIdeal.bit (Z n))
      simp only [↓reduceIte,hr,hq] at hh
      exact hh hv
    · obtain ⟨s,hs,hv⟩ := CommonIdeal.run_finite_extension h₁ n (CommonIdeal.bit (Z n)) (by
        rw [he₁]; exact Part.mem_some _)
      obtain ⟨q,hpq,hq⟩ := CodingRequirements.arbitrary_right_extension (columns A) p s hs
      have hh := hdiv q hpq (CommonIdeal.bit (Z n))
      simp only [show (2 : ℕ) ≠ 1 by decide,↓reduceIte,hr,hq] at hh
      exact hh hv

end TuringRigidity.StablePair

end OAI
