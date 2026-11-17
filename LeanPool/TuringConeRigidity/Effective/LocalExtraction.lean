/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalExtraction.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalOutcomes

/-!
# Local Extraction
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalExtraction
open ArithmeticHierarchy
open Encodable CodingForcing EncodedForcing UniformProgram IndexMatrix FiniteInjury LocalStage
noncomputable section

theorem noSplit_reduces {A Y G Z : Oracle} {t : ℕ} {p : Condition}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (hG : CommonIdeal.Extends G p.left)
    (he : OracleCode.eval (oracleFunction (join Y G)) (meaning (machine (item t 1))) =
      oracleFunction Z)
    (hno : ¬ ∃ z, UniformSplit.SplitCert A (Nat.pair (UniformPair.request (Nat.pair t (code p)))
      z)) :
    Reduces Z Y := by
  have hrun (w : List Bool) (n : ℕ) :
      UniformRun.run A (machine (item t 0)) (machine (item t 1)) w n =
        CommonIdeal.run Y (meaning (machine (item t 1))) w n := by
    simp only [UniformRun.run,hbase,CommonIdeal.run]
  apply CodingAgreement.case1_reduces (A := columns A) (p := p) ?_ hG he
  intro q r hpq hpr n a b ha hb
  by_contra hab
  rw [← hrun] at ha hb
  apply hno
  refine ⟨encode [n,encode q.left,encode r.left,a,b],?_⟩
  simpa [UniformSplit.SplitCert,UniformSplit.start,UniformSplit.base,UniformSplit.program,
    UniformPair.request,item,word,
    show left (code p) = p.left from congrArg Condition.left (condition_code p)] using
    And.intro hpq.1 (And.intro hpr.1 (And.intro hab (And.intro ha hb)))

theorem point_splittingLocation {A Y : Oracle} {t w : ℕ} {p : Condition}
    (hbase : OracleCode.eval (oracleFunction A) (meaning (machine (item t 0))) = oracleFunction Y)
    (hw : UniformSplit.PointCert A (Nat.pair (UniformPair.request (Nat.pair t (code p))) w)) :
    CodingLocations.SplittingLocation Y (meaning (machine (item t 1))) p.left (item w 2) := by
  have hrun (v : List Bool) (n : ℕ) :
      UniformRun.run A (machine (item t 0)) (machine (item t 1)) v n =
        CommonIdeal.run Y (meaning (machine (item t 1))) v n := by
    simp only [UniformRun.run,hbase,CommonIdeal.run]
  have hh : p.left <+: word (item w 1) ∧ p.left.length ≤ item w 2 ∧
      item w 2 < (word (item w 1)).length ∧ item w 4 ≠ item w 5 ∧
      item w 4 ∈ CommonIdeal.run Y (meaning (machine (item t 1))) (word (item w 1)) (item w 0) ∧
      item w 5 ∈ CommonIdeal.run Y (meaning (machine (item t 1)))
        ((word (item w 1)).set (item w 2) (item w 3).bodd) (item w 0) := by
    rw [← hrun,← hrun]
    simpa [UniformSplit.PointCert,UniformSplit.start,UniformSplit.base,UniformSplit.program,
      UniformPair.request,item,word,
      show left (code p) = p.left from congrArg Condition.left (condition_code p)] using hw
  exact ⟨word (item w 1),(item w 3).bodd,item w 0,item w 4,item w 5,hh⟩

theorem common_unbounded_points {D : LocalInputs.Data} {Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z)
    (hn : ¬ Reduces Z Y) :
    ∀ N, ∃ m, N ≤ m ∧ (Nat.unpair m).1 < t ∧ D.F (Nat.unpair m).1 (Nat.unpair m).2 = true ∧
      CodingLocations.SplittingLocation Y (meaning (machine (item t 1))) [] m := by
  obtain ⟨S,hS⟩ := LocalOutcomes.common_eventually_outcome hbase he₀ he₁
  intro N
  let s := max S N
  let p := atLevel (generic D (construction D s)) t
  obtain ⟨_,_,hno | ⟨w,hw,hcoding⟩⟩ := hS s (le_max_left _ _)
  · exact False.elim (hn (noSplit_reduces (p := p) (t := t) hbase
    (LocalLimits.limits_extend_generic D s).1 he₀ hno))
  · have hs : N ≤ p.left.length := by
      have hp := (open_extends D (FiniteInjurySchedule.visit (construction D s).seen)
        (construction D s).condition).1.length_le
      exact (le_max_right S N).trans ((length_bound D s).trans hp)
    have hpoint := point_splittingLocation (p := p) (t := t) (w := w) hbase hw
    obtain ⟨v,b,n,a,c,hpv,hpm,hmv,hac,ha,hc⟩ := hpoint
    exact ⟨item w 2,hs.trans hcoding.1,hcoding.2.1,hcoding.2.2,
      v,b,n,a,c,List.nil_prefix,Nat.zero_le _,hmv,hac,ha,hc⟩

theorem common_lower_unbounded_points {D : LocalInputs.Data} {Y Z : Oracle}
    (hY : Reduces Y D.B)
    (h₀ : Reduces Z (join Y (LocalLimits.G₀ D)))
    (h₁ : Reduces Z (join Y (LocalLimits.G₁ D)))
    (hn : ¬ Reduces Z Y) :
    ∃ t, ∀ N, ∃ m, N ≤ m ∧ (Nat.unpair m).1 < t ∧
      D.F (Nat.unpair m).1 (Nat.unpair m).2 = true ∧
      CodingLocations.SplittingLocation Y (meaning (machine (item t 1))) [] m := by
  obtain ⟨b,hb⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp hY
  obtain ⟨e,he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h₀
  obtain ⟨f,hf⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h₁
  let t := encode [encode (represent b),encode (represent e),encode (represent f)]
  have hb' : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction
    Y := by
    simpa [t,item,machine,represent_correct] using hb
  have he' : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z := by
    simpa [t,item,machine,represent_correct] using he
  have hf' : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z := by
    simpa [t,item,machine,represent_correct] using hf
  exact ⟨t,common_unbounded_points hb' he' hf' hn⟩

theorem noBad_sound {D : LocalInputs.Data} {Y : Oracle} {t : ℕ} {p : Condition}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (hbad : LocalPair.NoBad D.B D.F t (code p)) {m : ℕ}
    (hm : CodingLocations.SplittingLocation Y (meaning (machine (item t 1))) p.left m) :
    CodingLocation D.F p m := by
  obtain ⟨v,b,n,a,c,hpv,hpm,hmv,hac,ha,hc⟩ := hm
  have hrun (w : List Bool) (n : ℕ) :
      UniformRun.run D.B (machine (item t 0)) (machine (item t 1)) w n =
        CommonIdeal.run Y (meaning (machine (item t 1))) w n := by
    simp only [UniformRun.run,hbase,CommonIdeal.run]
  have hw : UniformSplit.PointCert D.B
      (Nat.pair (UniformPair.request (Nat.pair t (code p))) (encode [n,encode v,m,CommonIdeal.bit
        b,a,c])) := by
    have hbit : (CommonIdeal.bit b).bodd = b := by cases b <;> rfl
    have hh := And.intro hpv (And.intro hpm (And.intro hmv (And.intro hac
      (And.intro ((hrun v n).symm ▸ ha) ((hrun (v.set m b) n).symm ▸ hc)))))
    simpa [UniformSplit.PointCert,UniformSplit.start,UniformSplit.base,UniformSplit.program,
      UniformPair.request,item,word,hbit,
      show left (code p) = p.left from congrArg Condition.left (condition_code p)] using hh
  have hh := hbad _ hw
  simpa only
    [condition_code,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ] using
    hh

theorem common_recursive_locations {D : LocalInputs.Data} {Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z)
    (hn : ¬ Reduces Z Y) :
    ∃ p : Condition, p.active = t ∧ ∃ C : Oracle, Reduces C Y ∧
      {m | C m = true}.Infinite ∧ ∀ m, C m = true → CodingLocation D.F p m := by
  obtain ⟨S,hS⟩ := LocalOutcomes.common_eventually_outcome hbase he₀ he₁
  let p := atLevel (generic D (construction D S)) t
  have hbad : LocalPair.NoBad D.B D.F t (code p) := (hS S le_rfl).2.1
  obtain ⟨E,hE,hEq⟩ := CodingSplitSearch.splittingLocations_enumerable Y (meaning (machine (item t
    1))) p.left
  have hu : RecursiveInfiniteSubset.Unbounded E := by
    intro N
    let s := max (S+1) N
    let q := atLevel (generic D (construction D s)) t
    have hpq : p.left <+: q.left := by
      exact (LocalLimits.generic_prefix_next D S).1.trans
        ((word_prefix (word_growth D) (le_max_left (S+1) N)).1.trans
          (open_extends D _ _).1)
    obtain ⟨_,_,hno | ⟨w,hw,hcoding⟩⟩ := hS s (by dsimp [s]; omega)
    · exact False.elim (hn (noSplit_reduces (p := q) (t := t) hbase
        (LocalLimits.limits_extend_generic D s).1 he₀ hno))
    · have hN : N ≤ q.left.length := by
        exact (le_max_right (S+1) N).trans ((length_bound D s).trans (open_extends D _
          _).1.length_le)
      obtain ⟨v,b,n,a,c,hqv,hqm,hmv,hac,ha,hc⟩ := point_splittingLocation hbase hw
      have hpoint : CodingLocations.SplittingLocation Y (meaning (machine (item t 1))) p.left
        (item w 2) :=
        ⟨v,b,n,a,c,hpq.trans hqv,hpq.length_le.trans hqm,hmv,hac,ha,hc⟩
      obtain ⟨z,hz⟩ := (hEq (item w 2)).mp hpoint
      exact ⟨z,item w 2,hN.trans hqm,hz⟩
  obtain ⟨C,hCY,hCi,hC⟩ := RecursiveInfiniteSubset.infinite_recursive_subset Y E hu hE
  exact ⟨p,rfl,C,hCY,hCi,fun m hm => noBad_sound hbase hbad ((hEq m).mpr (hC m hm))⟩

theorem common_infinite_column {D : LocalInputs.Data} {Y Z : Oracle} {t : ℕ}
    (hbase : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction Y)
    (he₀ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D)))
      (meaning (machine (item t 1))) = oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D)))
      (meaning (machine (item t 2))) = oracleFunction Z)
    (hn : ¬ Reduces Z Y) :
    ∃ k, k < t ∧ ∃ C : Oracle, Reduces C Y ∧ {a | C a = true}.Infinite ∧
      ∀ a, C a = true → D.F k a = true := by
  obtain ⟨p,hp,C,hCY,hCi,hC⟩ := common_recursive_locations hbase he₀ he₁ hn
  simpa only [hp] using CodingExtraction.infinite_column hCY hCi hC

theorem common_lower_computes_column {D : LocalInputs.Data} {Y Z : Oracle}
    (hIntro : ∀ k C, (∀ a, C a = true → D.F k a = true) →
      {a | C a = true}.Infinite → Reduces (D.F k) C)
    (hY : Reduces Y D.B)
    (h₀ : Reduces Z (join Y (LocalLimits.G₀ D)))
    (h₁ : Reduces Z (join Y (LocalLimits.G₁ D)))
    (hn : ¬ Reduces Z Y) : ∃ k, Reduces (D.F k) Y := by
  obtain ⟨b,hb⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp hY
  obtain ⟨e,he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h₀
  obtain ⟨f,hf⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h₁
  let t := encode [encode (represent b),encode (represent e),encode (represent f)]
  have hb' : OracleCode.eval (oracleFunction D.B) (meaning (machine (item t 0))) = oracleFunction
    Y := by
    simpa [t,item,machine,represent_correct] using hb
  have he' : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₀ D))) (meaning (machine (item
    t 1))) = oracleFunction Z := by
    simpa [t,item,machine,represent_correct] using he
  have hf' : OracleCode.eval (oracleFunction (join Y (LocalLimits.G₁ D))) (meaning (machine (item
    t 2))) = oracleFunction Z := by
    simpa [t,item,machine,represent_correct] using hf
  obtain ⟨k,_,C,hCY,hCi,hC⟩ := common_infinite_column hb' he' hf' hn
  exact ⟨k,reduces_trans (hIntro k C hC hCi) hCY⟩

end
end TuringRigidity.LocalExtraction

end OAI
