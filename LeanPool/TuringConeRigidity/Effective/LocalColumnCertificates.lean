/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalColumnCertificates.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformPair

/-!
# Local Column Certificates
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalColumnCertificates
open Encodable UniformOracle ArithmeticHierarchy EncodedForcing CodingForcing

/-- The indexed machine has a finite computation returning the coded output on the coded
input. -/
def Output (B : Oracle) (v : ℕ) : Prop :=
  ∃ z, (Nat.unpair (Nat.unpair v).2).2 ∈ TableIndices.run B
    (IndexMatrix.machine (Nat.unpair v).1) (Nat.unpair (Nat.unpair v).2).1 z

theorem output_sigma (B : Oracle) : Sigma B 1 (Output B) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hr := total_comp (IndexMatrix.run_uniform_recursive B) (total_primrec
    (Primrec₂.natPair.comp (f.comp f) (Primrec₂.natPair.comp (f.comp (r.comp f)) r)))
  have heq := Primrec.ite (Primrec.eq.comp
    (Primrec.option_getD.comp (Primrec.decode.comp f) (Primrec.const none))
    (Primrec.option_some.comp r)) (Primrec.const 1) (Primrec.const 0)
  have hh : RecursivePred B (fun v => (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).2 ∈
      TableIndices.run B (IndexMatrix.machine (Nat.unpair (Nat.unpair v).1).1)
        (Nat.unpair (Nat.unpair (Nat.unpair v).1).2).1 (Nat.unpair v).2) := by
    exact (total_comp (total_primrec heq) (total_pair hr (total_primrec (r.comp (r.comp f))))).of_eq
      (fun v => by simp [Option.mem_def])
  apply (exists_form (n := 0) hh).congr
  intro v
  simp only [Output,Nat.unpair_pair]

/-- The first `count` program codes compute the corresponding columns of `F` relative to `B`. -/
def Presents (B : Oracle) (F : ℕ → Oracle) (codes count : ℕ) : Prop :=
  ∀ k, k < count → TableIndices.Represents B (IndexMatrix.machine (item codes k)) (F k)

theorem output_iff {B : Oracle} {F : ℕ → Oracle} {codes count k : ℕ}
    (h : Presents B F codes count) (hk : k < count) (a v : ℕ) :
    Output B (Nat.pair (item codes k) (Nat.pair a v)) ↔ v = CommonIdeal.bit (F k a) := by
  constructor
  · rintro ⟨z,hz⟩
    exact (h k hk).1 a z v (by simpa only [Nat.unpair_pair] using hz)
  · intro hv
    obtain ⟨z,b,hb⟩ := (h k hk).2 a
    have he := (h k hk).1 a z b hb
    exact ⟨z,by simpa only [Nat.unpair_pair,hv,he] using hb⟩

/-- A position is already assigned, inactive, or certified to be outside the true coding
positions. -/
def Noncoding (B : Oracle) (v : ℕ) : Prop :=
  let codes := (Nat.unpair v).1
  let p := (Nat.unpair (Nat.unpair v).2).1
  let m := (Nat.unpair (Nat.unpair v).2).2
  m < (left p).length ∨ active p ≤ (Nat.unpair m).1 ∨
    Output B (Nat.pair (item codes (Nat.unpair m).1) (Nat.pair (Nat.unpair m).2 0))

theorem noncoding_sigma (B : Oracle) : Sigma B 1 (Noncoding B) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let p := f.comp r
  let m := r.comp r
  have hl := recursive_primrecPred B (Primrec.nat_lt.comp m (Primrec.list_length.comp
    (left_primrec.comp p)))
  have hk := recursive_primrecPred B (Primrec.nat_le.comp (active_primrec.comp p) (f.comp m))
  have ho := (output_sigma B).comp (Primrec₂.natPair.comp (item_primrec.comp f (f.comp m))
    (Primrec₂.natPair.comp (r.comp m) (Primrec.const 0)))
  exact (Form.raise (n := 0) (s := true) hl).or ((Form.raise (n := 0) (s := true) hk).or ho)

theorem noncoding_condition_iff {B : Oracle} {F : ℕ → Oracle} {codes : ℕ} {p : ℕ}
    (h : Presents B F codes (active p)) (m : ℕ) :
    Noncoding B (Nat.pair codes (Nat.pair p m)) ↔ ¬ CodingLocation F (condition p) m := by
  simp only [Noncoding,Nat.unpair_pair,CodingLocation,condition]
  by_cases hk : (Nat.unpair m).1 < active p
  · rw [output_iff h hk]
    cases F (Nat.unpair m).1 (Nat.unpair m).2 <;> simp [CommonIdeal.bit,hk]
  · simp [hk,show active p ≤ (Nat.unpair m).1 from Nat.le_of_not_gt hk]

theorem noncoding_iff {B : Oracle} {F : ℕ → Oracle} {codes : ℕ} {p : Condition}
    (h : Presents B F codes p.active) (m : ℕ) :
    Noncoding B (Nat.pair codes (Nat.pair (code p) m)) ↔ ¬ CodingLocation F p m := by
  have hh : Presents B F codes (active (code p)) := by
    change Presents B F codes (condition (code p)).active
    simpa only [condition_code] using h
  simpa only [condition_code] using noncoding_condition_iff hh m

/-- The two assigned bits agree unless the position is certified noncoding. -/
def Allowed (B : Oracle) (v : ℕ) : Prop :=
  let req := (Nat.unpair v).1
  let m := (Nat.unpair v).2
  (left (item req 2)).getD m false = (right (item req 2)).getD m false ∨
    Noncoding B (Nat.pair (item req 0) (Nat.pair (item req 1) m))

theorem allowed_sigma (B : Oracle) : Sigma B 1 (Allowed B) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let req (i : ℕ) := item_primrec.comp f (Primrec.const i)
  have he := recursive_primrecPred B (Primrec.eq.comp
    ((Primrec.list_getD false).comp (left_primrec.comp (req 2)) r)
    ((Primrec.list_getD false).comp (right_primrec.comp (req 2)) r))
  have hn := (noncoding_sigma B).comp (Primrec₂.natPair.comp (req 0) (Primrec₂.natPair.comp (req
    1) r))
  exact (Form.raise (n := 0) (s := true) he).or hn

/-- Extend both words and the active level while respecting all coded position permissions. -/
def Extension (B : Oracle) (req : ℕ) : Prop :=
  left (item req 1) <+: left (item req 2) ∧ right (item req 1) <+: right (item req 2) ∧
    active (item req 1) ≤ active (item req 2) ∧
    ∀ m < (left (item req 2)).length, Allowed B (Nat.pair req m)

theorem extension_sigma (B : Oracle) : Sigma B 1 (Extension B) := by
  let req (i : ℕ) := item_primrec.comp Primrec.id (Primrec.const i)
  have hl := prefix_recursive B (left_primrec.comp (req 1)) (left_primrec.comp (req 2))
  have hr := prefix_recursive B (right_primrec.comp (req 1)) (right_primrec.comp (req 2))
  have ha := recursive_primrecPred B (Primrec.nat_le.comp (active_primrec.comp (req 1))
    (active_primrec.comp (req 2)))
  have hc := (allowed_sigma B).bounded_all (Primrec.list_length.comp (left_primrec.comp (req 2)))
  exact (Form.raise (n := 0) (s := true) hl).and ((Form.raise (n := 0) (s := true) hr).and
    ((Form.raise (n := 0) (s := true) ha).and hc))

theorem extension_condition_iff {B : Oracle} {F : ℕ → Oracle} {codes p q : ℕ}
    (h : Presents B F codes (active p)) :
    Extension B (encode [codes,p,q]) ↔ Extends F (condition p) (condition q) := by
  have hm (m : ℕ) : Allowed B (Nat.pair (encode [codes,p,q]) m) ↔
      (left q).getD m false = (right q).getD m false ∨ ¬ CodingLocation F (condition p) m := by
    simp only
      [Allowed, Nat.unpair_pair, item, encodek, Option.getD_some, List.getD_cons_zero,
        List.getD_cons_succ]
    exact or_congr Iff.rfl (noncoding_condition_iff h m)
  change (_ ∧ _ ∧ _ ∧ ∀ m < (left (item (encode [codes,p,q]) 2)).length,
    Allowed B (Nat.pair (encode [codes,p,q]) m)) ↔ _
  simp only [hm,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
  constructor
  · rintro ⟨hl,hr,ha,hc⟩
    exact ⟨hl,hr,ha,fun m hm hlen => (hc m hlen).resolve_right (not_not.mpr hm)⟩
  · rintro ⟨hl,hr,ha,hc⟩
    refine ⟨hl,hr,ha,fun m hlen => ?_⟩
    by_cases hm : CodingLocation F (condition p) m
    · exact Or.inl (hc m hm hlen)
    · exact Or.inr hm

theorem extension_iff {B : Oracle} {F : ℕ → Oracle} {codes : ℕ} {p q : Condition}
    (h : Presents B F codes p.active) :
    Extension B (encode [codes,code p,code q]) ↔ Extends F p q := by
  have hh : Presents B F codes (active (code p)) := by
    change Presents B F codes (condition (code p)).active
    simpa only [condition_code] using h
  simpa only [condition_code] using extension_condition_iff (q := code q) hh

/-- A one-point splitting certificate is located at a certified noncoding position. -/
def Bad (B : Oracle) (v : ℕ) : Prop :=
  let req := (Nat.unpair v).1
  let w := (Nat.unpair v).2
  UniformSplit.PointCert B (Nat.pair (UniformPair.request (Nat.pair (item req 1) (item req 2))) w) ∧
    Noncoding B (Nat.pair (item req 0) (Nat.pair (item req 2) (item w 2)))

theorem bad_sigma (B : Oracle) : Sigma B 1 (Bad B) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let req (i : ℕ) := item_primrec.comp f (Primrec.const i)
  have hp := (UniformSplit.pointCert_sigma B).comp (Primrec₂.natPair.comp
    (UniformPair.request_primrec.comp (Primrec₂.natPair.comp (req 1) (req 2))) r)
  have hn := (noncoding_sigma B).comp (Primrec₂.natPair.comp (req 0)
    (Primrec₂.natPair.comp (req 2) (item_primrec.comp r (Primrec.const 2))))
  exact hp.and hn

theorem guarded_search (B : Oracle) : ∃ f : ℕ → ℕ,
    Nat.RecursiveIn {oracleFunction (OracleJump.jump B)} (fun req => Part.some (f req)) ∧
    ∀ req, (f req = 0 ∧ ¬ ∃ w, Bad B (Nat.pair req w)) ∨
      (0 < f req ∧ Bad B (Nat.pair req (f req-1))) :=
  EffectiveWitness.sigma1_choice (bad_sigma B)

theorem bad_condition_iff {B : Oracle} {F : ℕ → Oracle} {codes p : ℕ}
    (h : Presents B F codes (active p)) (x w : ℕ) :
    Bad B (Nat.pair (encode [codes,x,p]) w) ↔
      UniformSplit.PointCert B (Nat.pair (UniformPair.request (Nat.pair x p)) w) ∧
        ¬ CodingLocation F (condition p) (item w 2) := by
  simp only
    [Bad,Nat.unpair_pair,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
  exact and_congr Iff.rfl (noncoding_condition_iff h _)

theorem bad_iff {B : Oracle} {F : ℕ → Oracle} {codes : ℕ} {p : Condition}
    (h : Presents B F codes p.active) (x w : ℕ) :
    Bad B (Nat.pair (encode [codes,x,code p]) w) ↔
      UniformSplit.PointCert B (Nat.pair (UniformPair.request (Nat.pair x (code p))) w) ∧
        ¬ CodingLocation F p (item w 2) := by
  simp only
    [Bad,Nat.unpair_pair,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ]
  exact and_congr Iff.rfl (noncoding_iff h _)

end TuringRigidity.LocalColumnCertificates

end OAI
