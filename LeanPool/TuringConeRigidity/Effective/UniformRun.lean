/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/UniformRun.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformProgram
public import LeanPool.TuringConeRigidity.CohenForcing.CohenRun

/-!
# Uniform Run
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.UniformRun
open Encodable Computable UniformOracle CommonIdeal ArithmeticHierarchy OracleJump EncodedForcing
  IndexMatrix
open UniformProgram

def run (A : Oracle) (b e : Code) (p : List Bool) (n : ℕ) : Part ℕ :=
  OracleCode.eval (partialJoin (OracleCode.eval (oracleFunction A) (meaning b)) (table p))
    (meaning e) n

def finiteRun (z : List ℕ × Code × Code × List Bool × ℕ) : Part ℕ :=
  OracleCode.eval (partialJoin (OracleCode.eval (BranchMachine.lookup z.1) (meaning z.2.1))
    (table z.2.2.2.1)) (meaning z.2.2.1) z.2.2.2.2

private theorem eval_partialJoin_partrec {α : Type*} [Primcodable α]
    {L : α → List ℕ} {b e : α → Code} {p : α → List Bool} {n : α → ℕ}
    (hL : Computable L) (hb : Computable b) (he : Computable e)
    (hp : Computable p) (hn : Computable n) :
    Partrec (fun z => OracleCode.eval
      (partialJoin (OracleCode.eval (BranchMachine.lookup (L z)) (meaning (b z))) (table (p z)))
      (meaning (e z)) (n z)) := by
  have hbase : Partrec₂ (fun z : α => OracleCode.eval (BranchMachine.lookup (L z)) (meaning (b
    z))) :=
    (UniformProgram.eval_partrec BranchMachine.lookup BranchMachine.lookup_partrec).comp
      ((hb.comp fst).pair ((hL.comp fst).pair snd))
  have htable : Partrec₂ (fun z : α => table (p z)) := table_partrec.comp (hp.comp fst) snd
  exact (UniformProgram.eval_partrec _ (BranchMachine.partialJoin_partrec hbase htable)).comp
    (he.pair (Computable.id.pair hn))

theorem finiteRun_partrec : Partrec finiteRun := by
  exact eval_partialJoin_partrec
    (L := fun z : List ℕ × Code × Code × List Bool × ℕ => z.1)
    (b := fun z => z.2.1) (e := fun z => z.2.2.1)
    (p := fun z => z.2.2.2.1) (n := fun z => z.2.2.2.2)
    fst (fst.comp snd) (fst.comp (snd.comp snd))
    (fst.comp (snd.comp (snd.comp snd))) (snd.comp (snd.comp (snd.comp snd)))

theorem finiteRun_approximates (A : Oracle) (b e : Code) (p : List Bool) (n : ℕ) :
    Approximates (run A b e p n) (fun m => finiteRun
      (oraclePrefix (fun k => bit (A k)) m,b,e,p,n)) := by
  apply OracleCode.eval_approximates
  intro k
  apply BranchMachine.partialJoin_approximates
  · exact OracleCode.eval_approximates (prefix_approximates (fun k => bit (A k))) (meaning b)
  · intro k; exact Approximates.const _

theorem run_represents (A : Oracle) (b e : OracleCode) (p : List Bool) (n : ℕ) :
    run A (represent b) (represent e) p n =
      OracleCode.eval (partialJoin (OracleCode.eval (oracleFunction A) b) (table p)) e n := by
  simp only [run,represent_correct]
  exact congrFun (represent_correct _ e) n

theorem run_total_base {A Y : Oracle} {b e : OracleCode}
    (hb : OracleCode.eval (oracleFunction A) b = oracleFunction Y) (p : List Bool) (n : ℕ) :
    run A (represent b) (represent e) p n = CommonIdeal.run Y e p n := by
  rw [run_represents,hb]
  rfl

theorem run_mono {A : Oracle} {b e : Code} {s t : List Bool}
    (h : s <+: t) (n a : ℕ) (ha : a ∈ run A b e s n) : a ∈ run A b e t n := by
  apply OracleCode.eval_mono (c := meaning e) (n := n) (a := a) ?_ ha
  intro k v hv
  cases hk : k.bodd with
  | false => simpa [partialJoin,hk] using hv
  | true =>
    exact table_mono h _ _ (by simpa [partialJoin,hk] using hv) |>
      (fun hh => by simpa [partialJoin,hk] using hh)

theorem run_table (A : Oracle) : ∃ d : Nat.Partrec.Code,
    ∀ b e p n a, a ∈ run A b e (word p) n ↔
      ∃ z, a ∈ TableIndices.run A d (encode (b,e,word p,n)) z := by
  obtain ⟨d,hd⟩ := partrec_code finiteRun_partrec
  have hd' (L : List ℕ) (b e : Code) (p : List Bool) (n : ℕ) :
      d.eval (Nat.pair (encode L) (encode (b,e,p,n))) = finiteRun (L,b,e,p,n) := hd (L,b,e,p,n)
  refine ⟨d,fun b e p n a => ?_⟩
  have ha := finiteRun_approximates A b e (word p) n
  constructor
  · intro h
    obtain ⟨m,hm⟩ := ha.2 a h
    have hh := hm m le_rfl
    dsimp only at hh
    rw [← hd'] at hh
    obtain ⟨t,ht⟩ := Nat.Partrec.Code.evaln_complete.mp hh
    exact ⟨Nat.pair m t,by simpa only [TableIndices.run,trial,Nat.unpair_pair] using ht⟩
  · rintro ⟨z,hz⟩
    have hh := Nat.Partrec.Code.evaln_sound hz
    rw [hd'] at hh
    exact ha.1 (Nat.unpair z).1 a hh

def Graph (A : Oracle) (v : ℕ) : Prop :=
  item v 4 ∈ run A (machine (item v 0)) (machine (item v 1)) (word (item v 2)) (item v 3)

theorem graph_sigma (A : Oracle) : Sigma A 1 (Graph A) := by
  obtain ⟨d,hd⟩ := run_table A
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let a (i : ℕ) := item_primrec.comp f (Primrec.const i)
  have hinput := Primrec.encode.comp ((machine_primrec.comp (a 0)).pair
    ((machine_primrec.comp (a 1)).pair ((word_primrec.comp (a 2)).pair (a 3))))
  have hr := total_comp (run_uniform_recursive A) (total_primrec
    (Primrec₂.natPair.comp (Primrec.const (encode d)) (Primrec₂.natPair.comp hinput r)))
  have heq : Primrec (fun v : ℕ => if (decode (α := Option ℕ) (Nat.unpair v).1).getD none =
      some (Nat.unpair v).2 then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp (Primrec.option_getD.comp (Primrec.decode.comp f) (Primrec.const
      none))
      (Primrec.option_some.comp r)) (Primrec.const 1) (Primrec.const 0)
  have hcert : RecursivePred A (fun v => item (Nat.unpair v).1 4 ∈
      TableIndices.run A d (encode (machine (item (Nat.unpair v).1 0),
        machine (item (Nat.unpair v).1 1),word (item (Nat.unpair v).1 2),
        item (Nat.unpair v).1 3)) (Nat.unpair v).2) := by
    exact (total_comp (total_primrec heq) (total_pair hr (total_primrec (a 4)))).of_eq
      (fun v => by simp [Option.mem_def])
  apply Form.congr (exists_form (n := 0) hcert)
  intro v
  simp only [Graph,Nat.unpair_pair]
  exact (hd _ _ _ _ _).symm

theorem graph_sigma_of (A : Oracle) {b e p n a : ℕ → ℕ}
    (hb : Primrec b) (he : Primrec e) (hp : Primrec p) (hn : Primrec n) (ha : Primrec a) :
    Sigma A 1 (fun v => a v ∈ run A (machine (b v)) (machine (e v)) (word (p v)) (n v)) := by
  have h := (graph_sigma A).comp (Primrec.encode.comp
    (Primrec.list_cons.comp hb (Primrec.list_cons.comp he (Primrec.list_cons.comp hp
      (Primrec.list_cons.comp hn (Primrec.list_cons.comp ha (Primrec.const [])))))))
  simpa only [Graph,item,encodek,Option.getD_some,List.getD_cons_zero,List.getD_cons_succ] using h

theorem pair_coverage {A Y : Oracle} (hY : Reduces Y A) (e f : OracleCode) :
    ∃ b i j : ℕ, ∀ p n,
      run A (machine b) (machine i) p n = CommonIdeal.run Y e p n ∧
      run A (machine b) (machine j) p n = CommonIdeal.run Y f p n := by
  obtain ⟨b,hb⟩ := (OracleCode.turingReducible_iff_exists_code _ _).mp hY
  refine ⟨encode (represent b),encode (represent e),encode (represent f),fun p n => ?_⟩
  simp only [machine,encodek,Option.getD_some]
  exact ⟨run_total_base hb p n,run_total_base hb p n⟩

end TuringRigidity.UniformRun

end OAI
