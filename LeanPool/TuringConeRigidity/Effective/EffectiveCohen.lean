/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/EffectiveCohen.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.EncodedForcing
public import LeanPool.TuringConeRigidity.Effective.EffectiveWitness

/-!
# Effective Cohen
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EffectiveCohen
open Encodable UniformOracle ArithmeticHierarchy OracleJump EffectiveWitness EncodedForcing

theorem word_decision (Y : Oracle) :
    ∃ step : ℕ → ℕ, Nat.RecursiveIn {oracleFunction (jump Y)} (fun x => Part.some (step x)) ∧
      ∀ e p, word p <+: word (step (Nat.pair e p)) ∧
        (Halts Y e (encode (word (step (Nat.pair e p)))) ∨
          ∀ q : List Bool, word (step (Nat.pair e p)) <+: q → ¬ Halts Y e (encode q)) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let P : ℕ → Prop := fun v =>
    word (Nat.unpair (Nat.unpair v).1).2 <+: word (Nat.unpair v).2 ∧
      Halts Y (Nat.unpair (Nat.unpair v).1).1 (encode (word (Nat.unpair v).2))
  have hp := EncodedForcing.prefix_recursive Y (word_primrec.comp (r.comp f)) (word_primrec.comp r)
  have hh := (halts_sigma Y).comp (Primrec₂.natPair.comp (f.comp f)
    (Primrec.encode.comp (word_primrec.comp r)))
  have hP : Sigma Y 1 P := by
    simpa only [P,Nat.unpair_pair] using (Form.raise (n := 0) (s := true) hp).and hh
  obtain ⟨g,hg,hs⟩ := sigma1_choice hP
  let a : ℕ → ℕ := fun v => if (Nat.unpair v).2 = 0 then (Nat.unpair v).1 else (Nat.unpair v).2-1
  have ha : Primrec a := Primrec.ite
    (Primrec.eq.comp r (Primrec.const 0)) f (Primrec.nat_sub.comp r (Primrec.const 1))
  let step : ℕ → ℕ := fun x => a (Nat.pair (Nat.unpair x).2 (g x))
  have hstep := total_comp (total_primrec (O := {oracleFunction (jump Y)}) ha)
    (total_pair (total_primrec r) hg)
  refine ⟨step,hstep,fun e p => ?_⟩
  rcases hs (Nat.pair e p) with ⟨hz,hn⟩ | ⟨hp,hw⟩
  · have he : step (Nat.pair e p) = p := by simp [step,a,hz]
    rw [he]
    refine ⟨List.prefix_rfl,Or.inr (fun q hq hhalt => ?_)⟩
    exact hn ⟨encode q,by simpa [P,word] using And.intro hq hhalt⟩
  · have hz : g (Nat.pair e p) ≠ 0 := by omega
    have he : step (Nat.pair e p) = g (Nat.pair e p)-1 := by simp [step,a,hz]
    rw [he]
    have hh : word p <+: word (g (Nat.pair e p)-1) ∧
        Halts Y e (encode (word (g (Nat.pair e p)-1))) := by simpa [P] using hw
    exact ⟨hh.1,Or.inl hh.2⟩

noncomputable def decider (Y : Oracle) : ℕ → ℕ := Classical.choose (word_decision Y)

theorem decider_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction (jump Y)} (fun x => Part.some (decider Y x)) :=
  (Classical.choose_spec (word_decision Y)).1

theorem decider_spec (Y : Oracle) (e p : ℕ) :
    word p <+: word (decider Y (Nat.pair e p)) ∧
      (Halts Y e (encode (word (decider Y (Nat.pair e p)))) ∨
        ∀ q : List Bool, word (decider Y (Nat.pair e p)) <+: q → ¬ Halts Y e (encode q)) :=
  (Classical.choose_spec (word_decision Y)).2 e p

def grow (p : ℕ) : ℕ := encode (word p ++ [false])

theorem grow_primrec : Primrec grow := Primrec.encode.comp
  (Primrec.list_append.comp word_primrec (Primrec.const [false]))

noncomputable def stage (Y : Oracle) : ℕ → ℕ
  | 0 => encode ([] : List Bool)
  | s+1 => grow (decider Y (Nat.pair s (stage Y s)))

theorem stage_recursive (Y : Oracle) :
    Nat.RecursiveIn {oracleFunction (jump Y)} (fun s => Part.some (stage Y s)) := by
  let r := Primrec.snd.comp Primrec.unpair
  have hstep := total_comp (total_primrec grow_primrec)
    (total_comp (decider_recursive Y) (total_primrec r))
  have hr := Nat.RecursiveIn.prec (total_primrec (O := {oracleFunction (jump Y)}) (Primrec.const
    (encode ([] : List Bool)))) hstep
  have h := Nat.RecursiveIn.comp hr
    (total_pair (total_primrec (Primrec.const 0)) (total_primrec Primrec.id))
  apply h.of_eq
  intro n
  change (Part.some (Nat.pair 0 n)).bind _ = _
  rw [Part.bind_some]
  simp only [Nat.unpair_pair]
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ih]
    change (Part.some (stage Y n)).bind _ = _
    rw [Part.bind_some]
    rfl

theorem stage_prefix (Y : Oracle) (s : ℕ) : word (stage Y s) <+: word (stage Y (s+1)) := by
  have h := (decider_spec Y s (stage Y s)).1
  simpa only [stage,grow,word,encodek,Option.getD_some] using
    h.trans (List.prefix_append _ [false])

theorem stage_length (Y : Oracle) (s : ℕ) : s ≤ (word (stage Y s)).length := by
  induction s with
  | zero => exact Nat.zero_le _
  | succ s ih =>
    have hh := (decider_spec Y s (stage Y s)).1.length_le
    simp only
      [stage,grow,word,encodek,Option.getD_some,List.length_append,List.length_cons,List.length_nil]
    simp only [word] at hh ih
    omega

theorem stage_prefix_of_le (Y : Oracle) {s t : ℕ} (h : s ≤ t) : word (stage Y s) <+: word (stage Y
  t) := by
  induction t,h using Nat.le_induction with
  | base => exact List.prefix_rfl
  | succ t ht ih => exact ih.trans (stage_prefix Y t)

noncomputable def generic (Y : Oracle) : Oracle := fun n => (word (stage Y (n+1))).getD n false

theorem generic_extends (Y : Oracle) (s : ℕ) :
    ∀ n < (word (stage Y s)).length, generic Y n = (word (stage Y s)).getD n false := by
  intro n hn
  let t := max s (n+1)
  have h0 := stage_prefix_of_le Y (show s ≤ t from le_max_left _ _)
  have h1 := stage_prefix_of_le Y (show n+1 ≤ t from le_max_right _ _)
  have hn1 : n < (word (stage Y (n+1))).length := (Nat.lt_succ_self n).trans_le (stage_length Y _)
  exact (CodingForcing.getD_of_prefix h1 hn1).symm.trans (CodingForcing.getD_of_prefix h0 hn)

theorem generic_reduces (Y : Oracle) : Reduces (generic Y) (jump Y) := by
  have hs := total_comp (stage_recursive Y) (total_primrec Primrec.succ)
  have hv := total_comp (total_primrec (CommonIdeal.bit_primrec.comp
    ((Primrec.list_getD false).comp (word_primrec.comp (Primrec.fst.comp Primrec.unpair))
      (Primrec.snd.comp Primrec.unpair)))) (total_pair hs (total_primrec Primrec.id))
  apply RecursiveIn.iff_nat.mpr
  exact hv.of_eq (fun n => by simp [oracleFunction,generic,CommonIdeal.bit])

def OneGeneric (Y G : Oracle) : Prop := ∀ e, ∃ p : List Bool,
  (∀ n < p.length, G n = p.getD n false) ∧
    (Halts Y e (encode p) ∨ ∀ q : List Bool, p <+: q → ¬ Halts Y e (encode q))

theorem generic_oneGeneric (Y : Oracle) : OneGeneric Y (generic Y) := by
  intro e
  let w := word (decider Y (Nat.pair e (stage Y e)))
  refine ⟨w,?_,(decider_spec Y e (stage Y e)).2⟩
  intro n hn
  have hw : w <+: word (stage Y (e+1)) := by
    simpa only [w,stage,grow,word,encodek,Option.getD_some] using List.prefix_append w [false]
  exact (generic_extends Y (e+1) n (hn.trans_le hw.length_le)).trans (CodingForcing.getD_of_prefix
    hw hn)

theorem relative_generic (Y : Oracle) : ∃ G : Oracle, Reduces G (jump Y) ∧ OneGeneric Y G :=
  ⟨generic Y,generic_reduces Y,generic_oneGeneric Y⟩

end TuringRigidity.EffectiveCohen

end OAI
