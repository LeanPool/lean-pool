/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/EffectiveSplit.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenRun
public import LeanPool.TuringConeRigidity.Effective.CodingSplitting
public import LeanPool.TuringConeRigidity.Effective.EffectiveWitness

/-!
# Effective Split
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EffectiveSplit
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing
open CohenRun EffectiveWitness CodingSplitting

/-- A finite certificate that two extensions yield different outputs for the same oracle
program and input. -/
def SplitCert (Y : Oracle) (e : OracleCode) (v : ℕ) : Prop :=
  let p := word (Nat.unpair v).1
  let w := (Nat.unpair v).2
  p <+: word (item w 1) ∧ p <+: word (item w 2) ∧ item w 3 ≠ item w 4 ∧
    item w 3 ∈ CommonIdeal.run Y e (word (item w 1)) (item w 0) ∧
    item w 4 ∈ CommonIdeal.run Y e (word (item w 2)) (item w 0)

theorem splitCert_sigma (Y : Oracle) (e : OracleCode) : Sigma Y 1 (SplitCert Y e) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let a (i : ℕ) := item_primrec.comp r (Primrec.const i)
  have hp := EncodedForcing.prefix_recursive Y (word_primrec.comp f) (word_primrec.comp (a 1))
  have hq := EncodedForcing.prefix_recursive Y (word_primrec.comp f) (word_primrec.comp (a 2))
  have hn := recursive_primrecPred Y ((Primrec.eq.comp (a 3) (a 4)).not)
  have hl := (run_mem_sigma Y e).comp
    (Primrec₂.natPair.comp (a 1) (Primrec₂.natPair.comp (a 0) (a 3)))
  have hr := (run_mem_sigma Y e).comp
    (Primrec₂.natPair.comp (a 2) (Primrec₂.natPair.comp (a 0) (a 4)))
  unfold SplitCert
  simpa only [Nat.unpair_pair] using (Form.raise (n := 0) (s := true) hp).and
    ((Form.raise (n := 0) (s := true) hq).and ((Form.raise (n := 0) (s := true) hn).and (hl.and
      hr)))

/-- A certificate that changing one bit of an extended word changes a computed output. -/
def PointCert (Y : Oracle) (e : OracleCode) (v : ℕ) : Prop :=
  let p := word (Nat.unpair v).1
  let w := (Nat.unpair v).2
  let q := word (item w 1)
  p <+: q ∧ p.length ≤ item w 2 ∧ item w 2 < q.length ∧ item w 4 ≠ item w 5 ∧
    item w 4 ∈ CommonIdeal.run Y e q (item w 0) ∧
    item w 5 ∈ CommonIdeal.run Y e (q.set (item w 2) (item w 3).bodd) (item w 0)

theorem pointCert_sigma (Y : Oracle) (e : OracleCode) : Sigma Y 1 (PointCert Y e) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let a (i : ℕ) := item_primrec.comp r (Primrec.const i)
  let p := word_primrec.comp f
  let q := word_primrec.comp (a 1)
  have hp := EncodedForcing.prefix_recursive Y p q
  have hlo := recursive_primrecPred Y (Primrec.nat_le.comp (Primrec.list_length.comp p) (a 2))
  have hhi := recursive_primrecPred Y (Primrec.nat_lt.comp (a 2) (Primrec.list_length.comp q))
  have hn := recursive_primrecPred Y ((Primrec.eq.comp (a 4) (a 5)).not)
  have hl := (run_mem_sigma Y e).comp
    (Primrec₂.natPair.comp (a 1) (Primrec₂.natPair.comp (a 0) (a 4)))
  have hr := (run_mem_sigma Y e).comp
    (Primrec₂.natPair.comp (Primrec.encode.comp
      (Primrec.list_set.comp q ((a 2).pair (Primrec.nat_bodd.comp (a 3)))))
      (Primrec₂.natPair.comp (a 0) (a 5)))
  unfold PointCert
  simpa only [Nat.unpair_pair,word,encodek,Option.getD_some] using
    (Form.raise (n := 0) (s := true) hp).and ((Form.raise (n := 0) (s := true) hlo).and
      ((Form.raise (n := 0) (s := true) hhi).and ((Form.raise (n := 0) (s := true) hn).and (hl.and
        hr))))

/-- Some extension of the coded word makes the specified computation converge. -/
def ConvergesAbove (Y : Oracle) (e : OracleCode) (v : ℕ) : Prop :=
  ∃ q, word (item v 1) <+: word q ∧ (CommonIdeal.run Y e (word q) (item v 0)).Dom

theorem convergesAbove_sigma (Y : Oracle) (e : OracleCode) : Sigma Y 1 (ConvergesAbove Y e) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := EncodedForcing.prefix_recursive Y (word_primrec.comp (item_primrec.comp f
    (Primrec.const 1))) (word_primrec.comp r)
  have hh := (run_dom_sigma Y e).comp
    (Primrec₂.natPair.comp r (item_primrec.comp f (Primrec.const 0)))
  unfold ConvergesAbove
  simpa only [Nat.unpair_pair] using ((Form.raise (n := 0) (s := true) hp).and hh).ex

/-- A coded extension above which the specified input has no convergent extension. -/
def DivCert (Y : Oracle) (e : OracleCode) (v : ℕ) : Prop :=
  word (Nat.unpair v).1 <+: word (item (Nat.unpair v).2 1) ∧
    ¬ ConvergesAbove Y e (Nat.unpair v).2

theorem divCert_recursive (Y : Oracle) (e : OracleCode) : RecursivePred (jump Y) (DivCert Y e) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hp := EncodedForcing.prefix_recursive (jump Y) (word_primrec.comp f)
    (word_primrec.comp (item_primrec.comp r (Primrec.const 1)))
  exact recursive_and hp (recursive_comp (recursive_not (form_recursive (convergesAbove_sigma Y
    e))) r)

/-- A tagged certificate settling a splitting requirement by no split, a one-point split, or
divergence. -/
def Accept (Y : Oracle) (e : OracleCode) (v : ℕ) : Prop :=
  let p := (Nat.unpair v).1
  let tag := (Nat.unpair (Nat.unpair v).2).1
  let w := (Nat.unpair (Nat.unpair v).2).2
  (tag = 0 ∧ ¬ ∃ z, SplitCert Y e (Nat.pair p z)) ∨
    (tag = 1 ∧ PointCert Y e (Nat.pair p w)) ∨
    (tag = 2 ∧ DivCert Y e (Nat.pair p w))

theorem accept_recursive (Y : Oracle) (e : OracleCode) : RecursivePred (jump Y) (Accept Y e) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have ht (i : ℕ) := recursive_primrecPred (jump Y) (Primrec.eq.comp (f.comp r) (Primrec.const i))
  have hn := recursive_comp (recursive_not (form_recursive (splitCert_sigma Y e).ex)) f
  have hp := recursive_comp (form_recursive (pointCert_sigma Y e)) (Primrec₂.natPair.comp f
    (r.comp r))
  have hd := recursive_comp (divCert_recursive Y e) (Primrec₂.natPair.comp f (r.comp r))
  unfold Accept
  apply Form.congr (n := 0) (s := true) (Form.or (n := 0) (s := true) (recursive_and (ht 0) hn)
    (Form.or (n := 0) (s := true) (recursive_and (ht 1) hp) (recursive_and (ht 2) hd)))
  intro v
  rfl

theorem accept_total (Y : Oracle) (e : OracleCode) : ∀ p, ∃ w, Accept Y e (Nat.pair p w) := by
  intro p
  by_cases hs : ∃ z, SplitCert Y e (Nat.pair p z)
  · obtain ⟨z,hp,hq,hab,ha,hb⟩ := hs
    simp only [Nat.unpair_pair] at hp hq hab ha hb
    rcases split_or_divergent_word hp hq (item z 0) (item z 3) (item z 4) ha hb hab with hs | hd
    · obtain ⟨q,m,b,a,c,hpq,hlo,hhi,hac,ha,hc⟩ := hs
      refine ⟨Nat.pair 1 (encode [item z 0,encode q,m,bit b,a,c]),Or.inr (Or.inl ⟨by simp,?_⟩)⟩
      have hbit : (bit b).bodd = b := by cases b <;> rfl
      simpa [PointCert,item,word,hbit] using
        And.intro hpq (And.intro hlo (And.intro hhi (And.intro hac (And.intro ha hc))))
    · obtain ⟨q,hpq,hd⟩ := hd
      refine ⟨Nat.pair 2 (encode [item z 0,encode q]),Or.inr (Or.inr ⟨by simp,?_,?_⟩)⟩
      · simpa [item,word] using hpq
      · simp only [Nat.unpair_pair,item]
        rintro ⟨r,hr,hh⟩
        simp only [item, encodek, Option.getD_some, List.getD_cons_zero,
          List.getD_cons_succ, word] at hr hh
        obtain ⟨u,hu⟩ := hr
        obtain ⟨a,ha⟩ := Part.dom_iff_mem.mp hh
        exact hd u a (hu ▸ ha)
  · exact ⟨Nat.pair 0 0,Or.inl ⟨by simp,by simpa using hs⟩⟩

/-- Choose the least accepted certificate for the given splitting requirement. -/
noncomputable def step (Y : Oracle) (e : OracleCode) : ℕ → ℕ :=
  least (Accept Y e) (accept_total Y e)

theorem step_recursive (Y : Oracle) (e : OracleCode) :
    Nat.RecursiveIn {oracleFunction (jump Y)} (fun p => Part.some (step Y e p)) :=
  least_recursive (accept_recursive Y e) (accept_total Y e)

theorem step_spec (Y : Oracle) (e : OracleCode) (p : ℕ) : Accept Y e (Nat.pair p (step Y e p)) :=
  least_spec (Accept Y e) (accept_total Y e) p

end TuringRigidity.EffectiveSplit

end OAI
