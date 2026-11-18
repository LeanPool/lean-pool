/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/SetModels/FiniteSupport.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.GuardedPair

/-!
# Finite Support
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.FiniteSupport
open ArithmeticHierarchy Encodable EncodedForcing CodingForcing UniformProgram IndexMatrix

theorem codingLocation_iff {F H : ℕ → Oracle} {p : Condition}
    (h : ∀ k, k < p.active → F k = H k) (m : ℕ) :
    CodingLocation F p m ↔ CodingLocation H p m := by
  constructor
  · rintro ⟨hl,hk,ha⟩
    exact ⟨hl,hk,by rwa [← h _ hk]⟩
  · rintro ⟨hl,hk,ha⟩
    exact ⟨hl,hk,by rwa [h _ hk]⟩

theorem extends_iff {F H : ℕ → Oracle} {p : Condition}
    (h : ∀ k, k < p.active → F k = H k) (q : Condition) :
    Extends F p q ↔ Extends H p q := by
  constructor
  · rintro ⟨hl,hr,hk,hc⟩
    exact ⟨hl,hr,hk,fun m hm hn => hc m ((codingLocation_iff h m).mpr hm) hn⟩
  · rintro ⟨hl,hr,hk,hc⟩
    exact ⟨hl,hr,hk,fun m hm hn => hc m ((codingLocation_iff h m).mp hm) hn⟩

theorem run_eq {A B : Oracle} {x : ℕ}
    (hb : OracleCode.eval (oracleFunction A) (meaning (machine (item x 0))) =
      OracleCode.eval (oracleFunction B) (meaning (machine (item x 0))))
    (i : ℕ) (s : List Bool) (n : ℕ) :
    UniformRun.run A (machine (item x 0)) (machine (item x i)) s n =
      UniformRun.run B (machine (item x 0)) (machine (item x i)) s n := by
  simp only [UniformRun.run,hb]

theorem noDisagreement_iff {A B : Oracle} {x : ℕ} {p : Condition}
    (hb : OracleCode.eval (oracleFunction A) (meaning (machine (item x 0))) =
      OracleCode.eval (oracleFunction B) (meaning (machine (item x 0))))
    (hc : ∀ k, k < p.active → columns A k = columns B k) :
    UniformAgreement.NoDisagreement A x p ↔ UniformAgreement.NoDisagreement B x p := by
  have hd (q : Condition) : UniformAgreement.Disagreement A x q ↔ UniformAgreement.Disagreement B
    x q := by
    simp only [UniformAgreement.Disagreement,run_eq hb]
  simp only [UniformAgreement.NoDisagreement,extends_iff hc,hd]

theorem badCert_iff {A B : Oracle} {x : ℕ} {p : Condition}
    (hb : OracleCode.eval (oracleFunction A) (meaning (machine (item x 0))) =
      OracleCode.eval (oracleFunction B) (meaning (machine (item x 0))))
    (hc : ∀ k, k < p.active → columns A k = columns B k) (w : ℕ) :
    GuardedPair.BadCert A (Nat.pair (Nat.pair x (code p)) w) ↔
      GuardedPair.BadCert B (Nat.pair (Nat.pair x (code p)) w) := by
  have hp : UniformSplit.PointCert A (Nat.pair (UniformPair.request (Nat.pair x (code p))) w) ↔
      UniformSplit.PointCert B (Nat.pair (UniformPair.request (Nat.pair x (code p))) w) := by
    simp only [item] at hb
    simp only [UniformSplit.PointCert,UniformSplit.start,UniformSplit.base,UniformSplit.program,
      UniformPair.request,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ,
      Nat.unpair_pair,UniformRun.run,hb]
  simp only [GuardedPair.BadCert,Nat.unpair_pair,UniformPair.IsCoding,condition_code,hp,
    codingLocation_iff hc]

theorem noBad_iff {A B : Oracle} {x : ℕ} {p : Condition}
    (hb : OracleCode.eval (oracleFunction A) (meaning (machine (item x 0))) =
      OracleCode.eval (oracleFunction B) (meaning (machine (item x 0))))
    (hc : ∀ k, k < p.active → columns A k = columns B k) :
    GuardedPair.NoBad A x p ↔ GuardedPair.NoBad B x p := by
  simp only [GuardedPair.NoBad,badCert_iff hb hc]

end TuringRigidity.FiniteSupport

end OAI
