/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Effective/LocalDecisive.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Effective.LocalPair
public import LeanPool.TuringConeRigidity.Effective.CodingRequirements

/-!
# Local Decisive
-/


@[expose] public section

namespace OAI

namespace TuringRigidity.LocalPair
open Encodable EncodedForcing CodingForcing UniformProgram IndexMatrix ArithmeticHierarchy

theorem decisive_excludes_common {B Y G₀ G₁ Z : Oracle} {F : ℕ → Oracle} {x : ℕ} {p : Condition}
    (hbase : OracleCode.eval (oracleFunction B) (meaning (machine (item x 0))) = oracleFunction Y)
    (h₀ : CommonIdeal.Extends G₀ p.left) (h₁ : CommonIdeal.Extends G₁ p.right)
    (he₀ : OracleCode.eval (oracleFunction (join Y G₀)) (meaning (machine (item x 1))) =
      oracleFunction Z)
    (he₁ : OracleCode.eval (oracleFunction (join Y G₁)) (meaning (machine (item x 2))) =
      oracleFunction Z)
    (hd : Decisive B F x p) : False := by
  have hr (i : ℕ) (s : List Bool) (n : ℕ) :
      UniformRun.run B (machine (item x 0)) (machine (item x i)) s n =
        CommonIdeal.run Y (meaning (machine (item x i))) s n := by
    simp only [UniformRun.run,hbase,CommonIdeal.run]
  rcases hd with ⟨n,a,b,hab,ha,hb⟩ | ⟨i,n,hi,hdiv⟩
  · rw [hr] at ha hb
    have ha' := CommonIdeal.run_total h₀ n a ha
    have hb' := CommonIdeal.run_total h₁ n b hb
    rw [he₀] at ha'
    rw [he₁] at hb'
    exact hab (Part.mem_unique ha' hb')
  · rcases hi with rfl | rfl
    · obtain ⟨s,hs,hv⟩ := CommonIdeal.run_finite_extension h₀ n (CommonIdeal.bit (Z n)) (by
        rw [he₀]; exact Part.mem_some _)
      obtain ⟨q,hpq,hq⟩ := CodingForcing.arbitrary_left_extension F p s hs
      have hh := hdiv q hpq (CommonIdeal.bit (Z n))
      simp only [↓reduceIte,hr,hq] at hh
      exact hh hv
    · obtain ⟨s,hs,hv⟩ := CommonIdeal.run_finite_extension h₁ n (CommonIdeal.bit (Z n)) (by
        rw [he₁]; exact Part.mem_some _)
      obtain ⟨q,hpq,hq⟩ := CodingRequirements.arbitrary_right_extension F p s hs
      have hh := hdiv q hpq (CommonIdeal.bit (Z n))
      simp only [show (2 : ℕ) ≠ 1 by decide,↓reduceIte,hr,hq] at hh
      exact hh hv

end TuringRigidity.LocalPair

end OAI
