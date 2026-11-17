/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Computability/BranchRecovery.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.UniformOracle
public import LeanPool.TuringConeRigidity.Computability.RecoverySetup
public import LeanPool.TuringConeRigidity.Representation.Assembly

/-!
# Branch Recovery
-/


@[expose] public section

namespace OAI

namespace TuringRigidity

@[simp] theorem partialJoin_oracle (A B : Oracle) :
    partialJoin (oracleFunction A) (oracleFunction B) = oracleFunction (join A B) := by
  funext k
  cases hk : k.bodd <;> simp [partialJoin, oracleFunction, join, hk]

namespace RecoveryData
variable {F : ℝ → Oracle} {t u v : ℝ}

def highBit (d : RecoveryData F t u v) : ℕ := if F (u+d.hi) d.bit then 1 else 0

def branchOracle (d : RecoveryData F t u v) : Oracle :=
  fun n => d.test (state d.test (d.delta : ℝ) t n)

private theorem tuple_initial (d : RecoveryData F t u v) :
    BranchMachine.initial (oracleFunction (fourTuple F t u v d.delta)) = oracleFunction (F u) := by
  funext k
  change oracleFunction (fourTuple F t u v d.delta) (8*k) = _
  rw [show 8*k = 2*(2*(2*k)) by omega]
  simp [oracleFunction, fourTuple]

private theorem tuple_anchor (d : RecoveryData F t u v) :
    BranchMachine.anchor (oracleFunction (fourTuple F t u v d.delta)) = oracleFunction (F (u-v))
      := by
  funext k
  change oracleFunction (fourTuple F t u v d.delta) (8*k+4) = _
  rw [show 8*k+4 = 2*(2*(2*k+1)) by omega]
  simp [oracleFunction, fourTuple]

private theorem tuple_increment (d : RecoveryData F t u v) (s : ℝ) :
    BranchMachine.increment (oracleFunction (fourTuple F t u v d.delta)) d.highBit
      (if F (u+s) d.bit then 1 else 0) =
    oracleFunction (F (v-u+(d.delta : ℝ)*(t-choiceBit d.test s))) := by
  funext k
  have h3 : oracleFunction (fourTuple F t u v d.delta) (4*k+2) =
      oracleFunction (F (v-u+(d.delta : ℝ)*t)) k := by
    rw [show 4*k+2 = 2*(2*k+1) by omega]
    simp [oracleFunction, fourTuple]
  have h4 : oracleFunction (fourTuple F t u v d.delta) (2*k+1) =
      oracleFunction (F (v-u+(d.delta : ℝ)*(t-1))) k := by
    simp [oracleFunction, fourTuple]
  cases hb : F (u+s) d.bit <;> cases hh : F (u+d.hi) d.bit <;>
    simp [BranchMachine.increment, highBit, choiceBit, test, hb, hh, h3, h4]

private theorem increment_span (d : RecoveryData F t u v) (s : ℝ) :
    (d.delta : ℝ)*(t-choiceBit d.test s) ∈ rationalSpan t := by
  cases hb : d.test s
  · exact ⟨0,d.delta,by simp [choiceBit,hb]⟩
  · refine ⟨-d.delta,d.delta,?_⟩
    simp only [choiceBit,hb,↓reduceIte,Rat.cast_neg]
    ring

private theorem increment_abs (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1)
    (s : ℝ) : |(d.delta : ℝ)*(t-choiceBit d.test s)| < d.radius := by
  have hd : (0 : ℝ) < d.delta := by exact_mod_cast d.delta_pos
  have hδ := d.delta_lt
  apply abs_lt.mpr
  cases hb : d.test s <;> simp only [choiceBit,hb,Bool.false_eq_true,↓reduceIte,sub_zero] <;>
    constructor <;> nlinarith

theorem stage_correct (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) :
    ∀ n, BranchMachine.stage (codeEnumeration d.forward) (codeEnumeration d.backward)
      d.bit d.highBit (oracleFunction (fourTuple F t u v d.delta)) n =
        oracleFunction (F (u+state d.test (d.delta : ℝ) t n)) := by
  intro n
  induction n with
  | zero =>
    funext input
    simpa [BranchMachine.stage,state] using congrFun (tuple_initial d) input
  | succ n ih =>
    let s := state d.test (d.delta : ℝ) t n
    let a := (d.delta : ℝ)*(t-choiceBit d.test s)
    have hsa : s+a = state d.test (d.delta : ℝ) t (n+1) := rfl
    have hp := d.forward_correct s (state_mem_rationalSpan d.test d.delta t n)
      a (increment_span d s) (d.abs_state_lt ht0 ht1 n) (increment_abs d ht0 ht1 s)
    have hq := d.backward_correct (s+a) (by rw [hsa]; exact state_mem_rationalSpan _ _ _ _)
      (by rw [hsa]; exact d.abs_state_lt ht0 ht1 (n+1))
    funext k
    simp only [BranchMachine.stage,BranchMachine.step,ih,oracleFunction]
    change (Part.some _).bind _ = _
    rw [Part.bind_some]
    change OracleCode.eval
      (partialJoin (OracleCode.eval
        (partialJoin (oracleFunction (F (u+s)))
          (BranchMachine.increment (oracleFunction (fourTuple F t u v d.delta)) d.highBit
            (if F (u+s) d.bit then 1 else 0))) (codeEnumeration d.forward))
        (BranchMachine.anchor (oracleFunction (fourTuple F t u v d.delta))))
      (codeEnumeration d.backward) k = _
    rw [tuple_increment,tuple_anchor,partialJoin_oracle,hp]
    rw [show v+s+a = v+(s+a) by ring,partialJoin_oracle,hq]
    rfl

theorem stage_single_program (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ c : OracleCode, ∀ n k,
      OracleCode.eval (oracleFunction (fourTuple F t u v d.delta)) c (Nat.pair n k) =
        oracleFunction (F (u+state d.test (d.delta : ℝ) t n)) k := by
  let T := fourTuple F t u v d.delta
  let g : ℕ → ℕ := fun k => if T k then 1 else 0
  let f : ℕ → ℕ := fun z => if F (u+state d.test (d.delta : ℝ) t (Nat.unpair z).1)
      (Nat.unpair z).2 then 1 else 0
  have hg : (fun x => Part.some (g x)) = oracleFunction (fourTuple F t u v d.delta) := rfl
  have hf := UniformOracle.stage_recursive (codeEnumeration d.forward) (codeEnumeration d.backward)
    d.bit d.highBit g f (by
      intro n k
      rw [hg]
      have hs := congrFun (d.stage_correct ht0 ht1 n) k
      apply hs.trans
      simp only [f,Nat.unpair_pair]
      rfl)
  obtain ⟨c,hc⟩ := OracleCode.exists_code hf
  rw [hg] at hc
  refine ⟨c,fun n k => (congrFun hc (Nat.pair n k)).trans ?_⟩
  simp only [f,Nat.unpair_pair]
  rfl

theorem branch_reduces (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) :
    Reduces d.branchOracle (fourTuple F t u v d.delta) := by
  obtain ⟨c,hc⟩ := d.stage_single_program ht0 ht1
  have he := OracleCode.eval_recursiveIn (oracleFunction (fourTuple F t u v d.delta)) c
  have hp := UniformOracle.total_primrec (O := {oracleFunction (fourTuple F t u v d.delta)})
    (Primrec₂.natPair.comp Primrec.id (Primrec.const d.bit))
  have hbits : Nat.RecursiveIn {oracleFunction (fourTuple F t u v d.delta)}
      (fun input => oracleFunction (F (u+state d.test (d.delta : ℝ) t input)) d.bit) :=
    (Nat.RecursiveIn.comp he hp).of_eq (fun n => by
    change (Part.some (Nat.pair n d.bit)).bind
      (fun input => OracleCode.eval (oracleFunction (fourTuple F t u v d.delta)) c input) = _
    rw [Part.bind_some,hc])
  have hcmp : Primrec (fun b : ℕ => if b = d.highBit then 1 else 0) :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const d.highBit))
      (Primrec.const 1) (Primrec.const 0)
  apply RecursiveIn.iff_nat.mpr
  apply (Nat.RecursiveIn.comp (UniformOracle.total_primrec hcmp) hbits).of_eq
  intro n
  simp only [oracleFunction]
  change (Part.some _).bind _ = _
  rw [Part.bind_some]
  cases hb : F (u+state d.test (d.delta : ℝ) t n) d.bit <;>
    cases hh : F (u+d.hi) d.bit <;>
    simp [branchOracle,test,highBit,hb,hh]

theorem branch_single_program (d : RecoveryData F t u v) (ht0 : 0 < t) (ht1 : t < 1) :
    ∃ c : OracleCode,
      OracleCode.eval (oracleFunction (fourTuple F t u v d.delta)) c =
        oracleFunction d.branchOracle :=
  (OracleCode.turingReducible_iff_exists_code _ _).mp (d.branch_reduces ht0 ht1)

end RecoveryData
end TuringRigidity

end OAI
