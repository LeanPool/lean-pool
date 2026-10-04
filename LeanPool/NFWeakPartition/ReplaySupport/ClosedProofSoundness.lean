/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.BoundedNominalLoweringBridgeDev004

/-! Soundness of closed nominal proofs in models of the literal theory. -/


public section

namespace NFChoice.ReplaySupport

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal.BoundedNominalLoweringBridgeDev004

/-- Every closed nominal proof is valid in every literal Hailperin model. -/
theorem valid_closed_of_nominal_proof (p : Wff) (closed : p.fv = ∅)
    (proof : Nominal.NPrf p) {S : Fol.Structure LNF}
    (hH : Fol.allRealizeSentence S LiteralHailperinNF) : Wff.Valid S p :=
  by
  intro v
  let a : S := v 0
  let rho : Var → Fin 1 := fun _ => 0
  let xs : DVec S 1 := DVec.cons a DVec.nil
  let v0 : Var → S := fun _ => a
  have hprf : Fol.prf LiteralHailperinNF.fst (Nominal.lowerWff (finValRho rho) p) :=
    proof (finValRho rho)
  have hs : Fol.realizeFormula v0 (Nominal.lowerWff (finValRho rho) p) DVec.nil :=
    by
    apply Fol.formula_soundness hprf S v0
    intro f hf
    rcases hf with ⟨g, hg, rfl⟩
    exact (Fol.realize_sentence_iff v0 g).mp (hH hg)
  rw [lowerWff_toFlypitch rho p] at hs
  have hv : ∀ k (hk : k < 1), xs.nth k hk = v0 k :=
    by
    intro k hk
    have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ hk)
    subst k
    simp [xs, v0, a]
  have hb :
    Fol.realizeBoundedFormula xs (Formula.toFlypitch (Lowering.lowerWff rho p))
      DVec.nil :=
    (Fol.realize_bounded_formula_iff hv _ DVec.nil).2 hs
  have hconst : Wff.Holds S v0 p :=
    (Lowering.lowerWff_realize_iff rho xs v0 (by intro x; simp [rho, xs, v0, a]) p).2 hb
  have hagree : AgreesOn p.fv v0 v := by
    intro x hx
    simp only [closed, Finset.notMem_empty] at hx
  exact (Wff.holds_congr_fv p v0 v hagree).mp hconst

end NFChoice.ReplaySupport
