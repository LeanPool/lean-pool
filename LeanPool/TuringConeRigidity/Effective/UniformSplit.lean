/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformSplit.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformRun
public import LeanPool.TuringConeRigidity.Effective.CodingSplitting
public import LeanPool.TuringConeRigidity.Effective.EffectiveWitness

/-!
# Uniform Split
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformSplit
open Encodable UniformOracle ArithmeticHierarchy OracleJump EncodedForcing EffectiveWitness
  IndexMatrix
open UniformProgram

/-- The background program extracted from a uniform splitting request. -/
def base (x : ℕ) := machine (item x 0)
/-- The target program extracted from a uniform splitting request. -/
def program (x : ℕ) := machine (item x 1)
/-- The starting finite word extracted from a uniform splitting request. -/
def start (x : ℕ) := word (item x 2)

/-- Two extensions of the starting word give different outputs for one uniform program input. -/
def SplitCert (A : Oracle) (v : ℕ) : Prop :=
  let x := (Nat.unpair v).1
  let w := (Nat.unpair v).2
  start x <+: word (item w 1) ∧ start x <+: word (item w 2) ∧ item w 3 ≠ item w 4 ∧
    item w 3 ∈ UniformRun.run A (base x) (program x) (word (item w 1)) (item w 0) ∧
    item w 4 ∈ UniformRun.run A (base x) (program x) (word (item w 2)) (item w 0)

theorem splitCert_sigma (A : Oracle) : Sigma A 1 (SplitCert A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let x (i : ℕ) := item_primrec.comp f (Primrec.const i)
  let w (i : ℕ) := item_primrec.comp r (Primrec.const i)
  have hp := EncodedForcing.prefix_recursive A (word_primrec.comp (x 2)) (word_primrec.comp (w 1))
  have hq := EncodedForcing.prefix_recursive A (word_primrec.comp (x 2)) (word_primrec.comp (w 2))
  have hn := recursive_primrecPred A ((Primrec.eq.comp (w 3) (w 4)).not)
  have hl := UniformRun.graph_sigma_of A (x 0) (x 1) (w 1) (w 0) (w 3)
  have hr := UniformRun.graph_sigma_of A (x 0) (x 1) (w 2) (w 0) (w 4)
  exact (Form.raise (n := 0) (s := true) hp).and
    ((Form.raise (n := 0) (s := true) hq).and ((Form.raise (n := 0) (s := true) hn).and (hl.and
      hr)))

/-- Changing one new bit in an extension changes the uniform program's output. -/
def PointCert (A : Oracle) (v : ℕ) : Prop :=
  let x := (Nat.unpair v).1
  let w := (Nat.unpair v).2
  let q := word (item w 1)
  start x <+: q ∧ (start x).length ≤ item w 2 ∧ item w 2 < q.length ∧ item w 4 ≠ item w 5 ∧
    item w 4 ∈ UniformRun.run A (base x) (program x) q (item w 0) ∧
    item w 5 ∈ UniformRun.run A (base x) (program x) (q.set (item w 2) (item w 3).bodd) (item w 0)

theorem pointCert_sigma (A : Oracle) : Sigma A 1 (PointCert A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let x (i : ℕ) := item_primrec.comp f (Primrec.const i)
  let w (i : ℕ) := item_primrec.comp r (Primrec.const i)
  let p := word_primrec.comp (x 2)
  let q := word_primrec.comp (w 1)
  have hp := EncodedForcing.prefix_recursive A p q
  have hlo := recursive_primrecPred A (Primrec.nat_le.comp (Primrec.list_length.comp p) (w 2))
  have hhi := recursive_primrecPred A (Primrec.nat_lt.comp (w 2) (Primrec.list_length.comp q))
  have hn := recursive_primrecPred A ((Primrec.eq.comp (w 4) (w 5)).not)
  have hl := UniformRun.graph_sigma_of A (x 0) (x 1) (w 1) (w 0) (w 4)
  have hr := UniformRun.graph_sigma_of A (x 0) (x 1)
    (Primrec.encode.comp (Primrec.list_set.comp q ((w 2).pair (Primrec.nat_bodd.comp (w 3)))))
    (w 0) (w 5)
  unfold PointCert
  simpa only [base,program,start,word,encodek,Option.getD_some] using
    (Form.raise (n := 0) (s := true) hp).and ((Form.raise (n := 0) (s := true) hlo).and
      ((Form.raise (n := 0) (s := true) hhi).and ((Form.raise (n := 0) (s := true) hn).and (hl.and
        hr))))

/-- Some extension of the coded word makes the uniform program converge on the specified
input. -/
def ConvergesAbove (A : Oracle) (v : ℕ) : Prop :=
  let x := (Nat.unpair v).1
  let w := (Nat.unpair v).2
  ∃ q a, word (item w 1) <+: word q ∧
    a ∈ UniformRun.run A (base x) (program x) (word q) (item w 0)

theorem convergesAbove_sigma (A : Oracle) : Sigma A 1 (ConvergesAbove A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let x (i : ℕ) := item_primrec.comp (f.comp (f.comp f)) (Primrec.const i)
  let w (i : ℕ) := item_primrec.comp (r.comp (f.comp f)) (Primrec.const i)
  have hp := EncodedForcing.prefix_recursive A (word_primrec.comp (w 1)) (word_primrec.comp
    (r.comp f))
  have hh := UniformRun.graph_sigma_of A (x 0) (x 1) (r.comp f) (w 0) r
  have h := ((Form.raise (n := 0) (s := true) hp).and hh).ex.ex
  unfold ConvergesAbove
  simpa only [base,program,Nat.unpair_pair] using h

/-- A starting-word extension has no further extension on which the uniform computation
converges. -/
def DivCert (A : Oracle) (v : ℕ) : Prop :=
  start (Nat.unpair v).1 <+: word (item (Nat.unpair v).2 1) ∧ ¬ ConvergesAbove A v

theorem divCert_recursive (A : Oracle) : RecursivePred (jump A) (DivCert A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := EncodedForcing.prefix_recursive (jump A)
    (word_primrec.comp (item_primrec.comp f (Primrec.const 2)))
    (word_primrec.comp (item_primrec.comp r (Primrec.const 1)))
  exact recursive_and hp (recursive_not (form_recursive (convergesAbove_sigma A)))

/-- A tagged uniform splitting certificate for no split, a one-point split, or divergence. -/
def Accept (A : Oracle) (v : ℕ) : Prop :=
  let x := (Nat.unpair v).1
  let tag := (Nat.unpair (Nat.unpair v).2).1
  let w := (Nat.unpair (Nat.unpair v).2).2
  (tag = 0 ∧ ¬ ∃ z, SplitCert A (Nat.pair x z)) ∨
    (tag = 1 ∧ PointCert A (Nat.pair x w)) ∨
    (tag = 2 ∧ DivCert A (Nat.pair x w))

theorem accept_recursive (A : Oracle) : RecursivePred (jump A) (Accept A) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have ht (i : ℕ) := recursive_primrecPred (jump A) (Primrec.eq.comp (f.comp r) (Primrec.const i))
  have hn := recursive_comp (recursive_not (form_recursive (splitCert_sigma A).ex)) f
  have hp := recursive_comp (form_recursive (pointCert_sigma A)) (Primrec₂.natPair.comp f (r.comp
    r))
  have hd := recursive_comp (divCert_recursive A) (Primrec₂.natPair.comp f (r.comp r))
  unfold Accept
  apply Form.congr (n := 0) (s := true) (Form.or (n := 0) (s := true) (recursive_and (ht 0) hn)
    (Form.or (n := 0) (s := true) (recursive_and (ht 1) hp) (recursive_and (ht 2) hd)))
  intro v
  rfl

theorem accept_total (A : Oracle) : ∀ x, ∃ w, Accept A (Nat.pair x w) := by
  intro x
  by_cases hs : ∃ z, SplitCert A (Nat.pair x z)
  · obtain ⟨z,hp,hq,hab,ha,hb⟩ := hs
    simp only [Nat.unpair_pair] at hp hq hab ha hb
    let f := fun w => UniformRun.run A (base x) (program x) w (item z 0)
    have hs : CodingSplitting.OnePoint (start x) f ∨
        ∃ w, start x <+: w ∧ ∀ u v, v ∉ f (w ++ u) := by
      by_cases hd : ∀ w, start x <+: w → ∃ u v, v ∈ f (w ++ u)
      · exact Or.inl (CodingSplitting.onePoint_of_dense
          (fun h v hv => UniformRun.run_mono h (item z 0) v hv) hd hp hq _ _ ha hb hab)
      · right; push Not at hd; exact hd
    rcases hs with hs | hd
    · obtain ⟨q,m,b,a,c,hpq,hlo,hhi,hac,ha,hc⟩ := hs
      refine ⟨Nat.pair 1 (encode [item z 0,encode q,m,CommonIdeal.bit b,a,c]),Or.inr (Or.inl ⟨by
        simp,?_⟩)⟩
      have hbit : (CommonIdeal.bit b).bodd = b := by cases b <;> rfl
      simpa [PointCert,item,word,hbit,f] using
        And.intro hpq (And.intro hlo (And.intro hhi (And.intro hac (And.intro ha hc))))
    · obtain ⟨q,hpq,hd⟩ := hd
      refine ⟨Nat.pair 2 (encode [item z 0,encode q]),Or.inr (Or.inr ⟨by simp,?_,?_⟩)⟩
      · simpa [item,word] using hpq
      · simp only [ConvergesAbove,Nat.unpair_pair,item,encodek,Option.getD_some,
          List.getD_cons_zero,List.getD_cons_succ,word]
        rintro ⟨r,a,hr,ha⟩
        obtain ⟨u,hu⟩ := hr
        exact hd u a (hu ▸ ha)
  · exact ⟨Nat.pair 0 0,Or.inl ⟨by simp,by simpa using hs⟩⟩

/-- Select the least accepted uniform splitting certificate for each request. -/
noncomputable def step (A : Oracle) : ℕ → ℕ := least (Accept A) (accept_total A)

theorem step_recursive (A : Oracle) :
    Nat.RecursiveIn {oracleFunction (jump A)} (fun x => Part.some (step A x)) :=
  least_recursive (accept_recursive A) (accept_total A)

theorem step_spec (A : Oracle) (x : ℕ) : Accept A (Nat.pair x (step A x)) :=
  least_spec (Accept A) (accept_total A) x

end TuringRigidity.UniformSplit

end OAI
