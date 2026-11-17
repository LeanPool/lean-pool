/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformPair.lean.
Also incorporates the precise step proof from the upstream
OAI/Computability/DegreeRigidity/Effective/StablePair.lean
under the same Apache-2.0 terms. Also incorporates the construction-independent
certificate-conversion proofs from Effective/GuardedExtraction.lean and
Effective/LocalExtraction.lean under the same terms.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformSplit
public import LeanPool.TuringConeRigidity.Effective.UniformAgreement
public import LeanPool.TuringConeRigidity.Effective.EffectiveSplitConditions

/-!
# Uniform Pair
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformPair
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness
  IndexMatrix
open CodingForcing UniformProgram

/-- Encode the base program, target program, and current left word into a splitting request. -/
def request (v : ℕ) : ℕ := encode [item (Nat.unpair v).1 0,item (Nat.unpair v).1 1,encode (left
  (Nat.unpair v).2)]

theorem request_primrec : Primrec request := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  exact Primrec.encode.comp (Primrec.list_cons.comp (item_primrec.comp f (Primrec.const 0))
    (Primrec.list_cons.comp (item_primrec.comp f (Primrec.const 1))
      (Primrec.list_cons.comp (Primrec.encode.comp (left_primrec.comp r)) (Primrec.const []))))

/-- The splitting certificate's selected position is protected by the active coding
requirement. -/
def IsCoding (A : Oracle) (v : ℕ) : Prop :=
  CodingLocation (columns A) (condition (Nat.unpair v).1) (item (Nat.unpair (Nat.unpair v).2).2 2)

theorem coding_recursive (A : Oracle) : RecursivePred A (IsCoding A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let m := item_primrec.comp (r.comp r) (Primrec.const 2)
  have hl := recursive_primrecPred A (Primrec.nat_le.comp (Primrec.list_length.comp
    (left_primrec.comp f)) m)
  have hk := recursive_primrecPred A (Primrec.nat_lt.comp (f.comp m) (active_primrec.comp f))
  have hq : Nat.RecursiveIn {oracleFunction A} (oracleFunction A) := .oracle _ (Set.mem_singleton _)
  have ha : RecursivePred A (fun v => A (item (Nat.unpair (Nat.unpair v).2).2 2) = true) := by
    exact (Nat.RecursiveIn.comp hq (total_primrec m)).of_eq (fun v => by
      change (Part.some (item (Nat.unpair (Nat.unpair v).2).2 2)).bind (fun input =>
        oracleFunction A input) = _
      rw [Part.bind_some]
      cases h : A (item (Nat.unpair (Nat.unpair v).2).2 2) <;> simp [oracleFunction,h])
  unfold IsCoding
  simpa only [CodingLocation,columns,condition,Nat.pair_unpair] using recursive_and hl
    (recursive_and hk ha)

/-- Select a uniform splitting outcome, assigning a separate tag to an unprotected one-point
split. -/
noncomputable def outcome (A : Oracle) (v : ℕ) : ℕ := by
  classical
  let w := UniformSplit.step A (request v)
  exact if (Nat.unpair w).1 = 1 ∧ ¬ IsCoding A (Nat.pair (Nat.unpair v).2 w)
    then Nat.pair 3 (Nat.unpair w).2 else w

theorem outcome_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (outcome A v)) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hs := total_comp (UniformSplit.step_recursive A) (total_primrec request_primrec)
  have hcode := total_pair (total_primrec r) hs
  have hc := total_comp (recursive_lift (coding_recursive A)) hcode
  have hmap : Primrec (fun v : ℕ => if (Nat.unpair (Nat.unpair v).1).1 = 1 ∧ (Nat.unpair v).2 = 0
      then Nat.pair 3 (Nat.unpair (Nat.unpair v).1).2 else (Nat.unpair v).1) :=
    Primrec.ite ((Primrec.eq.comp (f.comp f) (Primrec.const 1)).and
      (Primrec.eq.comp r (Primrec.const 0))) (Primrec₂.natPair.comp (Primrec.const 3) (r.comp f)) f
  exact (total_comp (total_primrec hmap) (total_pair hs hc)).of_eq (fun v => by
    simp only [Nat.unpair_pair,outcome]
    by_cases h : IsCoding A (Nat.pair (Nat.unpair v).2 (UniformSplit.step A (request v))) <;> simp
      [h])

/-- Retag the unprotected-split outcome as the extension-update case. -/
def retag (w : ℕ) : ℕ :=
  if (Nat.unpair w).1 = 3 then Nat.pair 2 (Nat.unpair w).2 else w

theorem retag_primrec : Primrec retag := Primrec.ite
  (Primrec.eq.comp (Primrec.fst.comp Primrec.unpair) (Primrec.const 3))
  (Primrec₂.natPair.comp (Primrec.const 2) (Primrec.snd.comp Primrec.unpair)) Primrec.id

/-- Update a condition using the retagged uniform splitting outcome. -/
def update (p w : ℕ) : ℕ := EffectiveSplitConditions.update p (retag w)

/-- The next coded condition obtained from the selected uniform pair outcome. -/
noncomputable def next (A : Oracle) (v : ℕ) : ℕ := update (Nat.unpair v).2 (outcome A v)

theorem next_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (next A v)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hu := EffectiveSplitConditions.update_primrec.comp f (retag_primrec.comp r)
  exact (total_comp (total_primrec hu)
    (total_pair (total_primrec r) (outcome_recursive A))).of_eq
      (fun v => by simp only [Nat.unpair_pair]; rfl)

theorem next_extends (A : Oracle) (v : ℕ) :
    Extends (columns A) (condition (Nat.unpair v).2) (condition (next A v)) ∧
    (condition (next A v)).active = (condition (Nat.unpair v).2).active := by
  unfold next update EffectiveSplitConditions.update
  split <;> rw [condition_code]
  · exact ⟨append_extends _ _ _,rfl⟩
  · exact ⟨extends_refl _ _,rfl⟩

theorem split_coding_or_divergence {A : Oracle} {x : ℕ} {p r : Condition}
    (hn : UniformAgreement.NoDisagreement A x p) (hpr : Extends (columns A) p r)
    (m : ℕ) (hm : p.left.length ≤ m) (hmr : m < r.left.length) (b : Bool)
    (n v w : ℕ) (hvw : v ≠ w)
    (hv : v ∈ UniformRun.run A (machine (item x 0)) (machine (item x 1)) r.left n)
    (hw : w ∈ UniformRun.run A (machine (item x 0)) (machine (item x 1)) (r.left.set m b) n) :
    CodingLocation (columns A) p m ∨
      ∀ q, Extends (columns A) r q → ∀ c,
        c ∉ UniformRun.run A (machine (item x 0)) (machine (item x 2)) q.right n := by
  by_cases hc : CodingLocation (columns A) p m
  · exact Or.inl hc
  · right
    intro q hrq c hvc
    have hpq := extends_trans hpr hrq
    have hpc := CodingOnePoint.changeLeft_extends hpq m hm hc b
    have hvq := UniformRun.run_mono hrq.1 n v hv
    have hwq := UniformRun.run_mono (CodingOnePoint.set_prefix_set hrq.1 m hmr b) n w hw
    have hveq : v = c := by
      by_contra hne
      exact hn q hpq ⟨n,v,c,hne,hvq,hvc⟩
    have hweq : w = c := by
      by_contra hne
      exact hn (CodingOnePoint.changeLeft q m b) hpc ⟨n,w,c,hne,hwq,hvc⟩
    exact hvw (hveq.trans hweq.symm)

/-- A uniform pair step leaves the condition unchanged in the no-split or
protected-point cases, or establishes permanent divergence of one side. -/
theorem next_spec_with_unchanged_condition (A : Oracle) (x p : ℕ)
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
  classical
  let v := Nat.pair x p
  let raw := UniformSplit.step A (request v)
  have hs := UniformSplit.step_spec A (request v)
  change UniformSplit.Accept A (Nat.pair (request v) raw) at hs
  simp only [UniformSplit.Accept,Nat.unpair_pair] at hs
  rcases hs with ⟨ht,hno⟩ | ⟨ht,hpoint⟩ | ⟨ht,hdiv⟩
  · have he : condition (next A v) = condition p := by
      simp [next,outcome,update,retag,EffectiveSplitConditions.update,← show raw =
        UniformSplit.step A (request v) from rfl,ht,v,condition_code]
    change Extends _ _ (condition (next A v)) ∧ _
    rw [he]
    exact ⟨extends_refl _ _,rfl,Or.inl ⟨rfl,Or.inl hno⟩⟩
  · let w := (Nat.unpair raw).2
    have hp := hpoint
    simp only [UniformSplit.PointCert,Nat.unpair_pair,UniformSplit.start,UniformSplit.base,
UniformSplit.program, request, v, item, encodek, Option.getD_some, List.getD_cons_zero,
  List.getD_cons_succ,
      word] at hp
    have hpq : left p <+: word (item w 1) := hp.1
    let r := append (condition p) ((word (item w 1)).drop (left p).length)
    have hl : r.left = word (item w 1) := by
      change left p ++ (word (item w 1)).drop (left p).length = _
      rw [List.prefix_iff_eq_take] at hpq
      conv_lhs => lhs; rw [hpq]
      exact List.take_append_drop _ _
    by_cases hcoding : IsCoding A (Nat.pair p raw)
    · have he : condition (next A v) = condition p := by
        simp [next,outcome,update,retag,EffectiveSplitConditions.update,
          ← show raw = UniformSplit.step A (request v) from rfl,ht,v,hcoding,condition_code]
      change Extends _ _ (condition (next A v)) ∧ _
      rw [he]
      exact ⟨extends_refl _ _, rfl, Or.inl ⟨rfl, Or.inr ⟨w, hpoint, by simpa only [IsCoding,
        Nat.unpair_pair] using hcoding⟩⟩⟩
    · have he : condition (next A v) = r := by
        simp [next,outcome,update,retag,EffectiveSplitConditions.update,
          ← show raw = UniformSplit.step A (request v) from rfl,ht,v,hcoding,condition_code]
        rfl
      have hnc : ¬ CodingLocation (columns A) (condition p) (item w 2) := by
        simpa only [IsCoding, Nat.unpair_pair] using hcoding
      have hpr : Extends (columns A) (condition p) r := append_extends _ _ _
      have hd := split_coding_or_divergence (r := r) hn hpr
        (item w 2) hp.2.1 (by simpa [hl,item,word,w] using hp.2.2.1) (item w 3).bodd
        (item w 0) (item w 4) (item w 5) hp.2.2.2.1
        (by simpa [hl, item, word, w] using hp.2.2.2.2.1) (by simpa [hl, item, word, w] using
          hp.2.2.2.2.2)
      change Extends _ _ (condition (next A v)) ∧ _
      rw [he]
      refine ⟨append_extends _ _ _,rfl,Or.inr ⟨2,item w 0,Or.inr rfl,?_⟩⟩
      simpa using hd.resolve_left hnc
  · let w := (Nat.unpair raw).2
    have hpq : left p <+: word (item w 1) := by
      simpa [UniformSplit.DivCert,UniformSplit.start,request,v,item,word] using hdiv.1
    let r := append (condition p) ((word (item w 1)).drop (left p).length)
    have hl : r.left = word (item w 1) := by
      change left p ++ (word (item w 1)).drop (left p).length = _
      rw [List.prefix_iff_eq_take] at hpq
      conv_lhs => lhs; rw [hpq]
      exact List.take_append_drop _ _
    have he : condition (next A v) = r := by
      simp [next,outcome,update,retag,EffectiveSplitConditions.update,
        ← show raw = UniformSplit.step A (request v) from rfl,ht,v,condition_code]
      rfl
    change Extends _ _ (condition (next A v)) ∧ _
    rw [he]
    refine ⟨append_extends _ _ _,rfl,Or.inr ⟨1,item w 0,Or.inl rfl,?_⟩⟩
    intro q hrq a ha
    apply hdiv.2
    refine ⟨encode q.left,a,?_,?_⟩
    · simpa [word,w,hl] using hrq.1
    · simpa [UniformSplit.base,UniformSplit.program,request,v,item,word] using ha

theorem next_spec (A : Oracle) (x p : ℕ)
    (hn : UniformAgreement.NoDisagreement A x (condition p)) :
    Extends (columns A) (condition p) (condition (next A (Nat.pair x p))) ∧
    (condition (next A (Nat.pair x p))).active = (condition p).active ∧
    ((¬ ∃ z, UniformSplit.SplitCert A (Nat.pair (request (Nat.pair x p)) z)) ∨
      (∃ w, UniformSplit.PointCert A (Nat.pair (request (Nat.pair x p)) w) ∧
        CodingLocation (columns A) (condition p) (item w 2)) ∨
      ∃ i n, (i = 1 ∨ i = 2) ∧ ∀ q, Extends (columns A) (condition (next A (Nat.pair x p))) q →
        ∀ a, a ∉ UniformRun.run A (machine (item x 0)) (machine (item x i))
          (if i = 1 then q.left else q.right) n) := by
  obtain ⟨hext,hactive,hrest⟩ := next_spec_with_unchanged_condition A x p hn
  refine ⟨hext,hactive,?_⟩
  rcases hrest with ⟨_,hno | hpoint⟩ | hdiv
  · exact Or.inl hno
  · exact Or.inr (Or.inl hpoint)
  · exact Or.inr (Or.inr hdiv)

theorem disagreement_mono {A : Oracle} {x : ℕ} {p q : Condition}
    (hpq : Extends (columns A) p q) (h : UniformAgreement.Disagreement A x p) :
    UniformAgreement.Disagreement A x q := by
  obtain ⟨n,a,b,hab,ha,hb⟩ := h
  exact ⟨n,a,b,hab,UniformRun.run_mono hpq.1 n a ha,UniformRun.run_mono hpq.2.1 n b hb⟩

theorem pair_exists (A : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump A)} (fun v => Part.some (f v)) ∧
    ∀ x p, Extends (columns A) (condition p) (condition (f (Nat.pair x p))) ∧
      (UniformAgreement.Disagreement A x (condition (f (Nat.pair x p))) ∨
        ∃ q, Extends (columns A) (condition p) (condition q) ∧
          UniformAgreement.NoDisagreement A x (condition q) ∧
          f (Nat.pair x p) = next A (Nat.pair x q)) := by
  obtain ⟨d,hd,hds⟩ := UniformAgreement.decide_exists A
  let f := fun v => next A (Nat.pair (Nat.unpair v).1 (d v))
  refine ⟨f,?_,fun x p => ?_⟩
  · have hp := total_pair (total_primrec (O := {oracleFunction (jump A)})
      (Primrec.fst.comp Primrec.unpair)) hd
    have hr := total_comp (next_recursive A) hp
    exact hr.of_eq (fun v => rfl)
  · obtain ⟨hp,hm⟩ := hds x p
    have hq := (next_extends A (Nat.pair x (d (Nat.pair x p)))).1
    simp only [Nat.unpair_pair] at hq
    refine ⟨?_,?_⟩
    · simpa only [f,Nat.unpair_pair] using extends_trans hp hq
    · rcases hm with hm | hm
      · exact Or.inl (by simpa only [f,Nat.unpair_pair] using disagreement_mono hq hm)
      · exact Or.inr ⟨d (Nat.pair x p),hp,hm,by simp only [f,Nat.unpair_pair]⟩

/-- Convert the absence of a coded split into a reduction, independently of a stage construction. -/
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

/-- Decode a point certificate into its splitting location without a stage-specific hypothesis. -/
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

end TuringRigidity.UniformPair

end OAI
