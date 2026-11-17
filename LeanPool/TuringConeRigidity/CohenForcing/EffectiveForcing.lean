/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/CohenForcing/EffectiveForcing.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.CohenForcing.EncodedForcing
public import LeanPool.TuringConeRigidity.Effective.EffectiveWitness

/-!
# Effective Forcing
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.EffectiveForcing
open UniformOracle ArithmeticHierarchy OracleJump EffectiveWitness EncodedForcing CodingForcing

/-- Decode the answer component, using the first component when the second is zero. -/
def answer (v : ℕ) : ℕ := if (Nat.unpair v).2 = 0 then (Nat.unpair v).1 else (Nat.unpair v).2 - 1

theorem answer_primrec : Primrec answer := Primrec.ite
  (Primrec.eq.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 0))
  (Primrec.fst.comp Primrec.unpair)
  (Primrec.nat_sub.comp (Primrec.snd.comp Primrec.unpair) (Primrec.const 1))

theorem uniform_open_decision (Y B : Oracle) (hB : Reduces B Y) :
    ∃ step : ℕ → ℕ,
      Nat.RecursiveIn {oracleFunction (jump Y)} (fun x => Part.some (step x)) ∧
      ∀ e p, Extends (columns B) (condition p) (condition (step (Nat.pair e p))) ∧
        (Halts Y e (step (Nat.pair e p)) ∨
          ∀ q, Extends (columns B) (condition (step (Nat.pair e p))) (condition q) → ¬ Halts Y e
            q) := by
  let f := Primrec.fst.comp Primrec.unpair
  let r := Primrec.snd.comp Primrec.unpair
  let P : ℕ → Prop := fun v =>
    Extends (columns B) (condition (Nat.unpair (Nat.unpair v).1).2) (condition (Nat.unpair v).2) ∧
      Halts Y (Nat.unpair (Nat.unpair v).1).1 (Nat.unpair v).2
  have hext := recursive_transfer
    (recursive_comp (extends_recursive B) (Primrec₂.natPair.comp (r.comp f) r)) hB
  have hhalt := (halts_sigma Y).comp (Primrec₂.natPair.comp (f.comp f) r)
  have hP : Sigma Y 1 P := by
    simpa only [P,Nat.unpair_pair] using (Form.raise (n := 0) (s := true) hext).and hhalt
  obtain ⟨g,hg,hs⟩ := sigma1_choice hP
  let step : ℕ → ℕ := fun x => answer (Nat.pair (Nat.unpair x).2 (g x))
  have hstep := total_comp (total_primrec (O := {oracleFunction (jump Y)}) answer_primrec)
    (total_pair (total_primrec r) hg)
  refine ⟨step,hstep,fun e p => ?_⟩
  rcases hs (Nat.pair e p) with ⟨hz,hn⟩ | ⟨hp,hw⟩
  · have he : step (Nat.pair e p) = p := by simp [step,answer,hz]
    rw [he]
    refine ⟨extends_refl _ _,Or.inr (fun q hq hhalt => ?_)⟩
    exact hn ⟨q,by simpa [P] using And.intro hq hhalt⟩
  · have hz : g (Nat.pair e p) ≠ 0 := by omega
    have he : step (Nat.pair e p) = g (Nat.pair e p) - 1 := by simp [step,answer,hz]
    rw [he]
    have hh : Extends (columns B) (condition p) (condition (g (Nat.pair e p)-1)) ∧
        Halts Y e (g (Nat.pair e p)-1) := by simpa [P] using hw
    exact ⟨hh.1,Or.inl hh.2⟩

end TuringRigidity.EffectiveForcing

end OAI
