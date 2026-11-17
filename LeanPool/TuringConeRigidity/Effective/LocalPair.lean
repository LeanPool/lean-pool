/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalPair.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalAgreement

/-!
# Local Pair
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalPair
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness
  IndexMatrix
open CodingForcing UniformProgram UniformPair LocalColumnCertificates
noncomputable section
attribute [local instance] Classical.propDecidable

def Decisive (B : Oracle) (F : ℕ → Oracle) (x : ℕ) (p : Condition) : Prop :=
  UniformAgreement.Disagreement B x p ∨ ∃ i n, (i = 1 ∨ i = 2) ∧ ∀ q, Extends F p q →
    ∀ a, a ∉ UniformRun.run B (machine (item x 0)) (machine (item x i))
      (if i = 1 then q.left else q.right) n

def NoBad (B : Oracle) (F : ℕ → Oracle) (x p : ℕ) : Prop :=
  ∀ w, UniformSplit.PointCert B (Nat.pair (request (Nat.pair x p)) w) →
    CodingLocation F (condition p) (item w 2)

theorem split_coding_or_divergence {B : Oracle} {F : ℕ → Oracle} {x : ℕ} {p r : Condition}
    (hn : LocalAgreement.NoDisagreement B F x p) (hpr : Extends F p r)
    (m : ℕ) (hm : p.left.length ≤ m) (hmr : m < r.left.length) (b : Bool)
    (n v w : ℕ) (hvw : v ≠ w)
    (hv : v ∈ UniformRun.run B (machine (item x 0)) (machine (item x 1)) r.left n)
    (hw : w ∈ UniformRun.run B (machine (item x 0)) (machine (item x 1)) (r.left.set m b) n) :
    CodingLocation F p m ∨
      ∀ q, Extends F r q → ∀ c,
        c ∉ UniformRun.run B (machine (item x 0)) (machine (item x 2)) q.right n := by
  by_cases hc : CodingLocation F p m
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

theorem bad_decisive (B : Oracle) (F : ℕ → Oracle) (x p w : ℕ)
    (hn : LocalAgreement.NoDisagreement B F x (condition p))
    (hb : UniformSplit.PointCert B (Nat.pair (request (Nat.pair x p)) w) ∧
      ¬ CodingLocation F (condition p) (item w 2)) :
    Decisive B F x (condition (EffectiveSplitConditions.update p (Nat.pair 2 w))) := by
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
      item w 4 ∈ UniformRun.run B (machine (item x 0)) (machine (item x 1)) (word (item w 1))
        (item w 0) ∧
      item w 5 ∈ UniformRun.run B (machine (item x 0)) (machine (item x 1))
        ((word (item w 1)).set (item w 2) (item w 3).bodd) (item w 0) := by
    simpa [UniformSplit.PointCert,UniformSplit.start,UniformSplit.base,UniformSplit.program,
      request,item,word] using hp.2
  have hd := split_coding_or_divergence (r := q) hn (append_extends F (condition p)
    ((word (item w 1)).drop (left p).length)) (item w 2) hpoint.1
    (by simpa [hl] using hpoint.2.1) (item w 3).bodd (item w 0) (item w 4) (item w 5)
    hpoint.2.2.1 (by simpa [hl] using hpoint.2.2.2.1) (by simpa [hl] using hpoint.2.2.2.2)
  have hnc' : ¬ CodingLocation F (condition p) (item w 2) := hnc
  have he : condition (EffectiveSplitConditions.update p (Nat.pair 2 w)) = q := by
    simp [EffectiveSplitConditions.update,Nat.unpair_pair,condition_code,q]
  rw [he]
  exact Or.inr ⟨2,item w 0,Or.inr rfl,by simpa using hd.resolve_left hnc'⟩

def Outcome (B : Oracle) (F : ℕ → Oracle) (x p : ℕ) : Prop :=
  (¬ ∃ z, UniformSplit.SplitCert B (Nat.pair (request (Nat.pair x p)) z)) ∨
    ∃ w, UniformSplit.PointCert B (Nat.pair (request (Nat.pair x p)) w) ∧
      CodingLocation F (condition p) (item w 2)

theorem raw_spec (B : Oracle) (F : ℕ → Oracle) (x p : ℕ)
    (hnb : NoBad B F x p) :
    let q := condition (EffectiveSplitConditions.update p (UniformSplit.step B (request (Nat.pair
      x p))))
    Decisive B F x q ∨ (q = condition p ∧ Outcome B F x p) := by
  let raw := UniformSplit.step B (request (Nat.pair x p))
  have hs := UniformSplit.step_spec B (request (Nat.pair x p))
  change UniformSplit.Accept B (Nat.pair (request (Nat.pair x p)) raw) at hs
  simp only [UniformSplit.Accept,Nat.unpair_pair] at hs
  change Decisive B F x (condition (EffectiveSplitConditions.update p raw)) ∨ _
  rcases hs with ⟨ht,hno⟩ | ⟨ht,hpoint⟩ | ⟨ht,hdiv⟩
  · have he : condition (EffectiveSplitConditions.update p raw) = condition p := by
      simp [EffectiveSplitConditions.update,ht,condition_code]
    exact Or.inr ⟨he,Or.inl hno⟩
  · have he : condition (EffectiveSplitConditions.update p raw) = condition p := by
      simp [EffectiveSplitConditions.update,ht,condition_code]
    exact Or.inr ⟨he,Or.inr ⟨_,hpoint,hnb _ hpoint⟩⟩
  · let w := (Nat.unpair raw).2
    have hpq : left p <+: word (item w 1) := by
      simpa [UniformSplit.DivCert,UniformSplit.start,request,item,word] using hdiv.1
    let r := append (condition p) ((word (item w 1)).drop (left p).length)
    have hl : r.left = word (item w 1) := by
      change left p ++ (word (item w 1)).drop (left p).length = _
      rw [List.prefix_iff_eq_take] at hpq
      conv_lhs => lhs; rw [hpq]
      exact List.take_append_drop _ _
    have he : condition (EffectiveSplitConditions.update p raw) = r := by
      simp only [EffectiveSplitConditions.update,ite_eq_left ht,condition_code]
      rfl
    rw [he]
    refine Or.inl (Or.inr ⟨1,item w 0,Or.inl rfl,?_⟩)
    intro q hrq a ha
    simp only [↓reduceIte] at ha
    apply hdiv.2
    refine ⟨encode q.left,a,?_,?_⟩
    · simpa [word,w,hl] using hrq.1
    · simpa [UniformSplit.base,UniformSplit.program,request,item,word] using ha

theorem next_exists (B : Oracle) : ∃ g : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump B)} (fun v => Part.some (g v)) ∧
    (∀ (F : ℕ → Oracle) req, Extends F (condition (item req 2)) (condition (g req)) ∧
      (condition (g req)).active = active (item req 2)) ∧
    ∀ (F : ℕ → Oracle) codes x p, Presents B F codes (active p) →
      LocalAgreement.NoDisagreement B F x (condition p) →
      Decisive B F x (condition (g (encode [codes,x,p]))) ∨
        (condition (g (encode [codes,x,p])) = condition p ∧ NoBad B F x p ∧ Outcome B F x p) := by
  obtain ⟨search,hs,hsearch⟩ := guarded_search B
  let raw := fun req => UniformSplit.step B (request (Nat.pair (item req 1) (item req 2)))
  let tag := fun req => if search req = 0 then raw req else Nat.pair 2 (search req-1)
  let g := fun req => EffectiveSplitConditions.update (item req 2) (tag req)
  have hrec : Nat.RecursiveIn {oracleFunction (jump B)} (fun v => Part.some (g v)) := by
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    let req (i : ℕ) := item_primrec.comp Primrec.id (Primrec.const i)
    have hr := total_comp (UniformSplit.step_recursive B) (total_primrec
      (request_primrec.comp (Primrec₂.natPair.comp (req 1) (req 2))))
    have hm := Primrec.ite (Primrec.eq.comp f (Primrec.const 0)) r
      (Primrec₂.natPair.comp (Primrec.const 2) (Primrec.nat_sub.comp f (Primrec.const 1)))
    have ht := total_comp (total_primrec hm) (total_pair hs hr)
    exact (total_comp (total_primrec (EffectiveSplitConditions.update_primrec.comp f r))
      (total_pair (total_primrec (req 2)) ht)).of_eq (fun req => by
        simp only [Nat.unpair_pair]; rfl)
  refine ⟨g,hrec,fun F req => ?_,fun F codes x p hp hn => ?_⟩
  · unfold g EffectiveSplitConditions.update
    split <;> rw [condition_code]
    · exact ⟨append_extends _ _ _,rfl⟩
    · exact ⟨extends_refl _ _,rfl⟩
  · rcases hsearch (encode [codes,x,p]) with ⟨hz,hno⟩ | ⟨hpos,hbad⟩
    · have hnb : NoBad B F x p := by
        intro w hw
        by_contra hnc
        exact hno ⟨w,(bad_condition_iff hp x w).2 ⟨hw,hnc⟩⟩
      have he : g (encode [codes,x,p]) = EffectiveSplitConditions.update p
          (UniformSplit.step B (request (Nat.pair x p))) := by
            simp only [g, tag, ite_eq_left hz, raw, item, encodek, Option.getD_some,
              List.getD_cons_zero, List.getD_cons_succ]
      rw [he]
      rcases raw_spec B F x p hnb with hd | ⟨he,ho⟩
      · exact Or.inl hd
      · exact Or.inr ⟨he,hnb,ho⟩
    · have hz : search (encode [codes,x,p]) ≠ 0 := by omega
      have he : g (encode [codes,x,p]) = EffectiveSplitConditions.update p
          (Nat.pair 2 (search (encode [codes, x, p])-1)) := by
            simp only [g, tag, ite_eq_right hz, item, encodek, Option.getD_some,
              List.getD_cons_zero, List.getD_cons_succ]
      rw [he]
      exact Or.inl (bad_decisive B F x p _ hn ((bad_condition_iff hp x _).1 hbad))

theorem disagreement_mono {B : Oracle} {F : ℕ → Oracle} {x : ℕ} {p q : Condition}
    (hpq : Extends F p q) (h : UniformAgreement.Disagreement B x p) :
    UniformAgreement.Disagreement B x q := by
  obtain ⟨n,a,b,hab,ha,hb⟩ := h
  exact ⟨n,a,b,hab,UniformRun.run_mono hpq.1 n a ha,UniformRun.run_mono hpq.2.1 n b hb⟩

theorem pair_exists (B : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (jump B)} (fun v => Part.some (f v)) ∧
    ∀ (F : ℕ → Oracle) codes x p, Presents B F codes (active p) →
      Extends F (condition p) (condition (f (encode [codes,x,p]))) ∧
      (UniformAgreement.Disagreement B x (condition (f (encode [codes,x,p]))) ∨
        ((condition (f (encode [codes,x,p]))).active = active p ∧
          LocalAgreement.NoDisagreement B F x (condition p) ∧
          (Decisive B F x (condition (f (encode [codes,x,p]))) ∨
            (condition (f (encode [codes,x,p])) = condition p ∧
              NoBad B F x p ∧ Outcome B F x p)))) := by
  obtain ⟨d,hd,hds⟩ := LocalAgreement.decide_exists B
  obtain ⟨g,hg,hge,hgs⟩ := next_exists B
  let out := fun req => if d req = item req 2 then g req else d req
  have hr : Nat.RecursiveIn {oracleFunction (jump B)} (fun req => Part.some (out req)) := by
    let f := Primrec.fst.comp Primrec.unpair
    let r := Primrec.snd.comp Primrec.unpair
    have hm := Primrec.ite (Primrec.eq.comp f (f.comp r)) (r.comp r) f
    exact (total_comp (total_primrec hm) (total_pair hd
      (total_pair (total_primrec (item_primrec.comp Primrec.id (Primrec.const 2))) hg))).of_eq
        (fun req => by simp only [Nat.unpair_pair]; rfl)
  refine ⟨out,hr,fun F codes x p hp => ?_⟩
  have hdsp := hds F codes x p hp
  have hgep := hge F (encode [codes,x,p])
  have hpitem : item (encode [codes,x,p]) 2 = p := by simp [item]
  rw [hpitem] at hgep
  by_cases he : d (encode [codes,x,p]) = p
  · have hout : out (encode [codes,x,p]) = g (encode [codes,x,p]) := by
      simp only [out,hpitem,he,↓reduceIte]
    rw [hout]
    refine ⟨hgep.1,?_⟩
    rcases hdsp.2 with hdis | ⟨_,hn⟩
    · rw [he] at hdis
      exact Or.inl (disagreement_mono hgep.1 hdis)
    · exact Or.inr ⟨hgep.2,hn,hgs F codes x p hp hn⟩
  · have hout : out (encode [codes,x,p]) = d (encode [codes,x,p]) := by
      simp only [out,hpitem,ite_eq_right he]
    rw [hout]
    exact ⟨hdsp.1,Or.inl (hdsp.2.resolve_right (fun h => he h.1))⟩

end
end TuringRigidity.LocalPair

end OAI
