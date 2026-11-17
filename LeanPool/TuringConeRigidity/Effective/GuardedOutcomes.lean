/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/GuardedOutcomes.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.GuardedLimits

/-!
# Guarded Outcomes
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.GuardedOutcomes
open ArithmeticHierarchy
open Encodable EncodedForcing CodingForcing FiniteInjury GuardedStage
open UniformProgram IndexMatrix
noncomputable section

theorem candidate_decisive (A : Oracle) (t : ℕ) (p : Condition)
    (hc : Changes A t p) : StablePair.Decisive A t (candidate A t p) := by
  let p' := atLevel p t
  let q := condition (pairProcedure A (Nat.pair t (code p')))
  obtain ⟨_,hdis | ⟨ha,hn,hd | ⟨he,hrest⟩⟩⟩ :=
    (Classical.choose_spec (GuardedPair.pair_exists A)).2 t (code p')
  · exact Or.inl hdis
  · have haq : q.active = t := by
      change q.active = (condition (code p')).active at ha
      simpa only [condition_code,p',atLevel] using ha
    have heq : atLevel q t = q := by rw [← haq]; cases q; rfl
    change StablePair.Decisive A t (atLevel q t)
    rw [heq]
    exact hd
  · have heq : q = p' := by
      change q = condition (code p') at he
      simpa only [condition_code] using he
    change (atLevel q t).left ≠ p.left ∨ (atLevel q t).right ≠ p.right at hc
    rw [heq] at hc
    exact False.elim (hc.elim (fun h => h rfl) (fun h => h rfl))

theorem limits_extend_action {A : Oracle} {s t : ℕ}
    (ha : stageAction A s (construction A s) = some t) :
    CommonIdeal.Extends (GuardedLimits.G₀ A) (candidate A t (generic A (construction A s))).left ∧
    CommonIdeal.Extends (GuardedLimits.G₁ A) (candidate A t (generic A (construction A s))).right :=
  StageEngineLimits.limits_extend_action GuardedStage.stateInterface (GuardedStage.procedures A)
    (GuardedStage.candidate_extends A) (GuardedStage.open_extends A) ha

theorem action_excludes_common {A Y Z : Oracle} {s t : ℕ}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    stageAction A s (construction A s) ≠ some t := by
  intro ha
  have hc := (scan_spec ha).2.2.2
  obtain ⟨h₀,h₁⟩ := limits_extend_action ha
  exact StablePair.decisive_excludes_common hbase h₀ h₁ he₀ he₁ (candidate_decisive A t _ hc)

theorem done_witness (A : Oracle) {s t : ℕ} (ht : t ∈ (construction A s).done) :
    ∃ u, u < s ∧ stageAction A u (construction A u) = some t :=
  StageEngine.done_witness GuardedStage.stateInterface (GuardedStage.procedures A) ht

theorem common_not_done {A Y Z : Oracle} {s t : ℕ}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    t ∉ (construction A s).done := by
  intro ht
  obtain ⟨u,_,hu⟩ := done_witness A ht
  exact action_excludes_common hbase he₀ he₁ hu

theorem scan_hits {A : Oracle} {p : Condition} {d : Finset ℕ} {start n t : ℕ}
    (hlo : start ≤ t) (hhi : t < start + n) (hd : t ∉ d) (hc : Changes A t p) :
    ∃ i, i ≤ t ∧ scan A p d start n = some i :=
  StageEngine.scan_hits hlo hhi hd hc

theorem common_eventually_unchanged {A Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    ∃ S, ∀ s, S ≤ s → ¬ Changes A t (generic A (construction A s)) := by
  obtain ⟨S,hS⟩ := finite_injury (proposal A) (t+1)
  refine ⟨max S (t+1),fun s hs hc => ?_⟩
  obtain ⟨i,hi,he⟩ := scan_hits (start := 0) (n := s) (Nat.zero_le t)
    (by omega) (common_not_done (s := s) hbase he₀ he₁) hc
  apply hS s ((le_max_left _ _).trans hs) i (by omega)
  rw [action_eq]
  exact he

theorem nonchanging_outcome {A Y Z : Oracle} {s t : ℕ}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A)))
      (meaning (machine (item t 2))) = oracleFunction Z)
    (hchange : ¬ Changes A t (generic A (construction A s))) :
    let p := atLevel (generic A (construction A s)) t
    UniformAgreement.NoDisagreement A t p ∧ GuardedPair.NoBad A t p ∧
      ((¬ ∃ z, UniformSplit.SplitCert A (Nat.pair (UniformPair.request (Nat.pair t (code p))) z)) ∨
        ∃ w, UniformSplit.PointCert A (Nat.pair (UniformPair.request (Nat.pair t (code p))) w) ∧
          CodingLocation (columns A) p (item w 2)) := by
  let p := atLevel (generic A (construction A s)) t
  let q := condition (pairProcedure A (Nat.pair t (code p)))
  have hwords : q.left = p.left ∧ q.right = p.right := by
    change ¬ (q.left ≠ p.left ∨ q.right ≠ p.right) at hchange
    exact ⟨Classical.not_not.mp (fun hn => hchange (Or.inl hn)),
      Classical.not_not.mp (fun hn => hchange (Or.inr hn))⟩
  have hq₀ : CommonIdeal.Extends (GuardedLimits.G₀ A) q.left := by
    rw [hwords.1]; exact (GuardedLimits.limits_extend_generic A s).1
  have hq₁ : CommonIdeal.Extends (GuardedLimits.G₁ A) q.right := by
    rw [hwords.2]; exact (GuardedLimits.limits_extend_generic A s).2
  obtain ⟨_,hd | ⟨ha,hn,hd | ⟨he,hbad,hout⟩⟩⟩ :=
    (Classical.choose_spec (GuardedPair.pair_exists A)).2 t (code p)
  · exact False.elim (StablePair.decisive_excludes_common hbase hq₀ hq₁ he₀ he₁ (Or.inl hd))
  · exact False.elim (StablePair.decisive_excludes_common hbase hq₀ hq₁ he₀ he₁ hd)
  · refine ⟨by simpa only [condition_code] using hn,hbad,?_⟩
    simpa only [GuardedPair.Outcome,condition_code] using hout

theorem common_eventually_outcome {A Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₀ A)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (GuardedLimits.G₁ A)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    ∃ S, ∀ s, S ≤ s →
      let p := atLevel (generic A (construction A s)) t
      UniformAgreement.NoDisagreement A t p ∧ GuardedPair.NoBad A t p ∧
        ((¬ ∃ z, UniformSplit.SplitCert A (Nat.pair (UniformPair.request (Nat.pair t (code p)))
          z)) ∨
          ∃ w, UniformSplit.PointCert A (Nat.pair (UniformPair.request (Nat.pair t (code p))) w) ∧
            CodingLocation (columns A) p (item w 2)) := by
  obtain ⟨S,hS⟩ := common_eventually_unchanged hbase he₀ he₁
  exact ⟨S,fun s hs => nonchanging_outcome hbase he₀ he₁ (hS s hs)⟩

end
end TuringRigidity.GuardedOutcomes

end OAI
