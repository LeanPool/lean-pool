/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalOutcomes.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalLimits
public import LeanPool.TuringConeRigidity.Effective.LocalDecisive

/-!
# Local Outcomes
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalOutcomes
open ArithmeticHierarchy
open Encodable EncodedForcing CodingForcing FiniteInjury LocalStage
open UniformProgram IndexMatrix
noncomputable section

theorem candidate_decisive (D : LocalInputs.Data) (t : ℕ) (p : Condition)
    (hc : Changes D t p) : LocalPair.Decisive D.B D.F t (candidate D t p) := by
  let p' := atLevel p t
  let q := condition (pairProcedure D (Nat.pair t (code p')))
  obtain ⟨_,hdis | ⟨ha,hn,hd | ⟨he,hrest⟩⟩⟩ :=
    D.pair_spec t (code p')
  · exact Or.inl hdis
  · have haq : q.active = t := by
      change q.active = (condition (code p')).active at ha
      simpa only [condition_code,p',atLevel] using ha
    have heq : atLevel q t = q := by rw [← haq]; cases q; rfl
    change LocalPair.Decisive D.B D.F t (atLevel q t)
    rw [heq]
    exact hd
  · have heq : q = p' := by
      change q = condition (code p') at he
      simpa only [condition_code] using he
    change (atLevel q t).left ≠ p.left ∨ (atLevel q t).right ≠ p.right at hc
    rw [heq] at hc
    exact False.elim (hc.elim (fun h => h rfl) (fun h => h rfl))

theorem limits_extend_action {D : LocalInputs.Data} {s t : ℕ}
    (ha : stageAction D s (construction D s) = some t) :
    CommonIdeal.Extends (LocalLimits.G₀ D) (candidate D t (generic D (construction D s))).left ∧
    CommonIdeal.Extends (LocalLimits.G₁ D) (candidate D t (generic D (construction D s))).right :=
  StageEngineLimits.limits_extend_action LocalStage.stateInterface (LocalStage.procedures D)
    (LocalStage.candidate_extends D) (LocalStage.open_extends D) ha

theorem action_excludes_common {D : LocalInputs.Data} {Y Z : Oracle} {s t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    stageAction D s (construction D s) ≠ some t := by
  intro ha
  have hc := (scan_spec ha).2.2.2
  obtain ⟨h₀,h₁⟩ := limits_extend_action ha
  exact LocalPair.decisive_excludes_common (F := D.F) hbase h₀ h₁ he₀ he₁ (candidate_decisive D t
    _ hc)

theorem done_witness (D : LocalInputs.Data) {s t : ℕ} (ht : t ∈ (construction D s).done) :
    ∃ u, u < s ∧ stageAction D u (construction D u) = some t :=
  StageEngine.done_witness LocalStage.stateInterface (LocalStage.procedures D) ht

theorem common_not_done {D : LocalInputs.Data} {Y Z : Oracle} {s t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    t ∉ (construction D s).done := by
  intro ht
  obtain ⟨u,_,hu⟩ := done_witness D ht
  exact action_excludes_common hbase he₀ he₁ hu

theorem scan_hits {D : LocalInputs.Data} {p : Condition} {d : Finset ℕ} {start n t : ℕ}
    (hlo : start ≤ t) (hhi : t < start + n) (hd : t ∉ d) (hc : Changes D t p) :
    ∃ i, i ≤ t ∧ scan D p d start n = some i :=
  StageEngine.scan_hits hlo hhi hd hc

theorem common_eventually_unchanged {D : LocalInputs.Data} {Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    ∃ S, ∀ s, S ≤ s → ¬ Changes D t (generic D (construction D s)) := by
  obtain ⟨S,hS⟩ := finite_injury (proposal D) (t+1)
  refine ⟨max S (t+1),fun s hs hc => ?_⟩
  obtain ⟨i,hi,he⟩ := scan_hits (start := 0) (n := s) (Nat.zero_le t)
    (by omega) (common_not_done (s := s) hbase he₀ he₁) hc
  apply hS s ((le_max_left _ _).trans hs) i (by omega)
  rw [action_eq]
  exact he

theorem nonchanging_outcome {D : LocalInputs.Data} {Y Z : Oracle} {s t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z)
    (hchange : ¬ Changes D t (generic D (construction D s))) :
    let p := atLevel (generic D (construction D s)) t
    LocalAgreement.NoDisagreement D.B D.F t p ∧ LocalPair.NoBad D.B D.F t (code p) ∧
      ((¬ ∃ z, UniformSplit.SplitCert D.B (Nat.pair (UniformPair.request (Nat.pair t (code p)))
        z)) ∨
        ∃ w, UniformSplit.PointCert D.B (Nat.pair (UniformPair.request (Nat.pair t (code p))) w) ∧
          CodingLocation D.F p (item w 2)) := by
  let p := atLevel (generic D (construction D s)) t
  let q := condition (pairProcedure D (Nat.pair t (code p)))
  have hwords : q.left = p.left ∧ q.right = p.right := by
    change ¬ (q.left ≠ p.left ∨ q.right ≠ p.right) at hchange
    exact ⟨Classical.not_not.mp (fun hn => hchange (Or.inl hn)),
      Classical.not_not.mp (fun hn => hchange (Or.inr hn))⟩
  have hq₀ : CommonIdeal.Extends (LocalLimits.G₀ D) q.left := by
    rw [hwords.1]; exact (LocalLimits.limits_extend_generic D s).1
  have hq₁ : CommonIdeal.Extends (LocalLimits.G₁ D) q.right := by
    rw [hwords.2]; exact (LocalLimits.limits_extend_generic D s).2
  obtain ⟨_,hd | ⟨ha,hn,hd | ⟨he,hbad,hout⟩⟩⟩ :=
    D.pair_spec t (code p)
  · exact False.elim (LocalPair.decisive_excludes_common (F := D.F) hbase hq₀ hq₁ he₀ he₁ (Or.inl
    hd))
  · exact False.elim (LocalPair.decisive_excludes_common (F := D.F) hbase hq₀ hq₁ he₀ he₁ hd)
  · refine ⟨by simpa only [condition_code] using hn,hbad,?_⟩
    simpa only [LocalPair.Outcome,condition_code] using hout

theorem common_eventually_outcome {D : LocalInputs.Data} {Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z) :
    ∃ S, ∀ s, S ≤ s →
      let p := atLevel (generic D (construction D s)) t
      LocalAgreement.NoDisagreement D.B D.F t p ∧ LocalPair.NoBad D.B D.F t (code p) ∧
        ((¬ ∃ z, UniformSplit.SplitCert D.B (Nat.pair (UniformPair.request (Nat.pair t (code p)))
          z)) ∨
          ∃ w, UniformSplit.PointCert D.B (Nat.pair (UniformPair.request (Nat.pair t (code p))) w) ∧
            CodingLocation D.F p (item w 2)) := by
  obtain ⟨S,hS⟩ := common_eventually_unchanged hbase he₀ he₁
  exact ⟨S,fun s hs => nonchanging_outcome hbase he₀ he₁ (hS s hs)⟩

end
end TuringRigidity.LocalOutcomes

end OAI
