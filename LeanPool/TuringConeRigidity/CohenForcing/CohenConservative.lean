/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/CohenConservative.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.CohenRun
public import LeanPool.TuringConeRigidity.SetModels.ConservativeExtension
public import LeanPool.TuringConeRigidity.CohenForcing.CohenLowness

/-!
# Cohen Conservative
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.CohenConservative
open Encodable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing
open CohenHalting CohenRun EffectiveCohen CohenLowness

theorem value_ne_recursive (X : Oracle) : RecursivePred X (fun v =>
    (Nat.unpair v).2 ≠ bit (X (Nat.unpair v).1)) := by
  classical
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hquery : Nat.RecursiveIn {oracleFunction X} (fun v => Part.some (bit (X (Nat.unpair v).1)))
    := by
    have hq : Nat.RecursiveIn {oracleFunction X} (oracleFunction X) := .oracle _
      (Set.mem_singleton _)
    exact total_comp (f := fun input => bit (X input)) hq (total_primrec f)
  have he : Primrec (fun v : ℕ => if (Nat.unpair v).1 ≠ (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite ((Primrec.eq.comp f r).not) (Primrec.const 1) (Primrec.const 0)
  exact (total_comp (total_primrec he) (total_pair (total_primrec r) hquery)).of_eq
    (fun v => by simp only [Nat.unpair_pair]; split <;> rfl)

theorem disagreement_sigma {A X B : Oracle} (hA : Reduces A B) (hX : Reduces X B)
    (e : OracleCode) : Sigma B 1 (fun p => ∃ n a,
      a ∈ CommonIdeal.run A e (word p) n ∧ a ≠ bit (X n)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  have hr := form_transfer (run_mem_sigma A e) hA
  have hn := recursive_comp (recursive_transfer (value_ne_recursive X) hX) r
  have hh := (hr.and (Form.raise (n := 0) (s := true) hn)).comp
    (Primrec₂.natPair.comp (f.comp f) (Primrec₂.natPair.comp (r.comp f) r))
  simpa only [Nat.unpair_pair] using hh.ex.ex

theorem oneGeneric_conservative {B G : Oracle} (hG : OneGeneric B G)
    (A X : Oracle) (hA : Reduces A B) (hX : Reduces X B)
    (h : Reduces X (join A G)) : Reduces X A := by
  obtain ⟨e,he⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp h
  obtain ⟨p,hp,hd⟩ := hG.decides (disagreement_sigma hA hX e)
  apply ConservativeExtension.removes_oracle hp (e := e) (s := p) ?_ he
  rcases hd with hd | hd
  · exact Or.inl (by simpa [word] using hd)
  · refine Or.inr (fun q hpq n a ha => ?_)
    by_contra hn
    exact hd q hpq ⟨n,a,by simpa [word] using ha,hn⟩

theorem oneGeneric_not_reduces {B G : Oracle} (hG : OneGeneric B G) : ¬ Reduces G B := by
  intro h
  have hp := recursive_not (recursive_transfer (CohenLowness.prefix_recursive G) h)
  obtain ⟨p,hp',hd⟩ := hG.decides (Form.raise (n := 0) (s := true) hp)
  rcases hd with hd | hd
  · exact hd (by simpa [word,Prefix] using hp')
  · let q := p ++ [!(G p.length)]
    have he := hd q (List.prefix_append _ _)
    apply he
    intro hq
    have hh := hq p.length (by simp [word,q])
    have hh' : G p.length = !(G p.length) := by
      simp [word,q,List.getD_eq_getElem?_getD] at hh
    cases hb : G p.length <;> simp [hb] at hh'

theorem relative_low_conservative (B : Oracle) : ∃ G : Oracle,
    Reduces G (jump B) ∧ OneGeneric B G ∧ ¬ Reduces G B ∧
    degree (jump (join B G)) = degree (jump B) ∧
    ∀ A X : Oracle, Reduces A B → Reduces X B → Reduces X (join A G) → Reduces X A := by
  obtain ⟨G,hr,hg,hl⟩ := relative_low_generic B
  exact ⟨G,hr,hg,oneGeneric_not_reduces hg,hl,oneGeneric_conservative hg⟩

end TuringRigidity.CohenConservative

end OAI
