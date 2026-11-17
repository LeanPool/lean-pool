/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/GuardedPair.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.StablePair

/-!
# Guarded Pair
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GuardedPair
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness
  IndexMatrix
open CodingForcing UniformProgram UniformPair
noncomputable section
attribute [local instance] Classical.propDecidable

def BadCert (A : Oracle) (v : ℕ) : Prop :=
  UniformSplit.PointCert A (Nat.pair (request (Nat.unpair v).1) (Nat.unpair v).2) ∧
    ¬ IsCoding A (Nat.pair (Nat.unpair (Nat.unpair v).1).2 (Nat.pair 1 (Nat.unpair v).2))

def NoBad (A : Oracle) (x : ℕ) (p : Condition) : Prop :=
  ¬ ∃ w, BadCert A (Nat.pair (Nat.pair x (code p)) w)

theorem badCert_sigma (A : Oracle) : Sigma A 1 (BadCert A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := (UniformSplit.pointCert_sigma A).comp
    (Primrec₂.natPair.comp (request_primrec.comp f) r)
  have hc := recursive_comp (recursive_not (coding_recursive A))
    (Primrec₂.natPair.comp (r.comp f) (Primrec₂.natPair.comp (Primrec.const 1) r))
  exact hp.and (Form.raise (n := 0) (s := true) hc)

theorem bad_decisive (A : Oracle) (x p w : ℕ)
    (hn : UniformAgreement.NoDisagreement A x (condition p))
    (hb : BadCert A (Nat.pair (Nat.pair x p) w)) :
    StablePair.Decisive A x (condition (EffectiveSplitConditions.update p (Nat.pair 2 w))) := by
  obtain ⟨hp,hnc⟩ := hb
  have hpq : left p <+: word (item w 1) := by
    simpa [UniformSplit.PointCert,UniformSplit.start,request,item,word] using hp.1
  let q := append (condition p) ((word (item w 1)).drop (left p).length)
  have hl : q.left = word (item w 1) := by
    change left p ++ (word (item w 1)).drop (left p).length = _
    rw [List.prefix_iff_eq_take] at hpq
    conv_lhs => lhs; rw [hpq]
    exact List.take_append_drop _ _
  have hpoint : (left p).length ≤ item w 2 ∧ item w 2 < (word (item w 1)).length ∧
      item w 4 ≠ item w 5 ∧
      item w 4 ∈ UniformRun.run A (machine (item x 0)) (machine (item x 1)) (word (item w 1))
        (item w 0) ∧
      item w 5 ∈ UniformRun.run A (machine (item x 0)) (machine (item x 1))
        ((word (item w 1)).set (item w 2) (item w 3).bodd) (item w 0) := by
    simpa [UniformSplit.PointCert,UniformSplit.start,UniformSplit.base,UniformSplit.program,
      request,item,word] using hp.2
  have hd := split_coding_or_divergence (r := q) hn (append_extends (columns A) (condition p)
    ((word (item w 1)).drop (left p).length)) (item w 2) hpoint.1
    (by simpa [hl] using hpoint.2.1) (item w 3).bodd (item w 0) (item w 4) (item w 5)
    hpoint.2.2.1 (by simpa [hl] using hpoint.2.2.2.1) (by simpa [hl] using hpoint.2.2.2.2)
  have hnc' : ¬ CodingLocation (columns A) (condition p) (item w 2) := by
    simpa only [IsCoding,Nat.unpair_pair] using hnc
  have he : condition (EffectiveSplitConditions.update p (Nat.pair 2 w)) = q := by
    simp [EffectiveSplitConditions.update,Nat.unpair_pair,condition_code,q]
  rw [he]
  exact Or.inr ⟨2,item w 0,Or.inr rfl,by simpa using hd.resolve_left hnc'⟩

def Outcome (A : Oracle) (x p : ℕ) : Prop :=
  (¬ ∃ z, UniformSplit.SplitCert A (Nat.pair (request (Nat.pair x p)) z)) ∨
    ∃ w, UniformSplit.PointCert A (Nat.pair (request (Nat.pair x p)) w) ∧
      CodingLocation (columns A) (condition p) (item w 2)

theorem next_exists (A : Oracle) : ∃ g : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (g v)) ∧
    (∀ x p, Extends (columns A) (condition p) (condition (g (Nat.pair x p))) ∧
      (condition (g (Nat.pair x p))).active = (condition p).active) ∧
    ∀ x p, UniformAgreement.NoDisagreement A x (condition p) →
      StablePair.Decisive A x (condition (g (Nat.pair x p))) ∨
      (condition (g (Nat.pair x p)) = condition p ∧
        (¬ ∃ w, BadCert A (Nat.pair (Nat.pair x p) w)) ∧ Outcome A x p) := by
  obtain ⟨search,hs,hsearch⟩ := sigma1_choice (badCert_sigma A)
  let g := fun v => if search v = 0 then next A v else
    EffectiveSplitConditions.update (Nat.unpair v).2 (Nat.pair 2 (search v-1))
  have hrec : Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (g v)) := by
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    have hu := total_comp (total_primrec (EffectiveSplitConditions.update_primrec.comp f r))
      (total_pair (total_primrec r) (total_comp (total_primrec
        (Primrec₂.natPair.comp (Primrec.const 2) (Primrec.nat_sub.comp Primrec.id (Primrec.const
          1)))) hs))
    have hi := Primrec.ite (Primrec.eq.comp f (Primrec.const 0)) (f.comp r) (r.comp r)
    exact (total_comp (total_primrec hi) (total_pair hs (total_pair (next_recursive A) hu))).of_eq
      (fun v => by simp only [Nat.unpair_pair]; rfl)
  refine ⟨g,hrec,fun x p => ?_,fun x p hn => ?_⟩
  · by_cases hz : search (Nat.pair x p) = 0
    · simpa only [g,ite_eq_left hz,Nat.unpair_pair] using next_extends A (Nat.pair x p)
    · simp only [g,ite_eq_right
      hz,Nat.unpair_pair,EffectiveSplitConditions.update,↓reduceIte,condition_code]
      exact ⟨append_extends _ _ _,rfl⟩
  · rcases hsearch (Nat.pair x p) with ⟨hz,hno⟩ | ⟨hpos,hbad⟩
    · simp only [g,ite_eq_left hz]
      rcases (StablePair.next_precise A x p hn).2.2 with ⟨he,ho⟩ | hd
      · exact Or.inr ⟨he,hno,ho⟩
      · exact Or.inl (Or.inr hd)
    · have hz : search (Nat.pair x p) ≠ 0 := by omega
      simp only [g,ite_eq_right hz,Nat.unpair_pair]
      exact Or.inl (bad_decisive A x p _ hn hbad)

theorem pair_exists (A : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (f v)) ∧
    ∀ x p, Extends (columns A) (condition p) (condition (f (Nat.pair x p))) ∧
      (UniformAgreement.Disagreement A x (condition (f (Nat.pair x p))) ∨
        ((condition (f (Nat.pair x p))).active = (condition p).active ∧
          UniformAgreement.NoDisagreement A x (condition p) ∧
          (StablePair.Decisive A x (condition (f (Nat.pair x p))) ∨
            (condition (f (Nat.pair x p)) = condition p ∧
              (¬ ∃ w, BadCert A (Nat.pair (Nat.pair x p) w)) ∧ Outcome A x p)))) := by
  obtain ⟨d,hd,hds⟩ := StablePair.decide_stable_exists A
  obtain ⟨g,hg,hge,hgs⟩ := next_exists A
  let f := fun v => g (Nat.pair (Nat.unpair v).1 (d v))
  refine ⟨f,?_,fun x p => ?_⟩
  · exact (total_comp hg (total_pair (total_primrec (Primrec.fst.comp Primrec.unpair)) hd)).of_eq
      (fun v => rfl)
  · obtain ⟨hp,hm⟩ := hds x p
    have hq := hge x (d (Nat.pair x p))
    refine ⟨by simpa only [f,Nat.unpair_pair] using extends_trans hp hq.1,?_⟩
    rcases hm with hm | ⟨he,hn⟩
    · exact Or.inl (by simpa only [f,Nat.unpair_pair] using disagreement_mono hq.1 hm)
    · simpa only [f,Nat.unpair_pair,he] using Or.inr ⟨(hge x p).2,hn,hgs x p hn⟩

noncomputable def procedure (A : Oracle) : ℕ → ℕ := Classical.choose (pair_exists A)

theorem procedure_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (procedure A v)) :=
  (Classical.choose_spec (pair_exists A)).1

end
end TuringRigidity.GuardedPair

end OAI
