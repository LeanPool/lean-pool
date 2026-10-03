/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalSubstitutionLemmas
public import LeanPool.NFWeakPartition.WPPCompactSourceSyntax

/-! NF weak partition development: NominalDfEu. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! The source axiom `df-eu` chooses an arbitrary dummy which is fresh for its
displayed body.  `syn_weu` chooses a deterministic dummy.  Both choices lower
to the same de-Bruijn formula, so their biconditional is just reflexivity in
the exact literal Flypitch theory.
-/


/-- The displayed right-hand side of `df-eu`, with its source dummy exposed. -/
@[expose]
def euPrimitive (y x : Var) (p : Wff) : Wff :=
  syn_wex y (.all x (syn_wb p (.objEq x y)))

/-- Two fresh outer dummies induce the same environment on the free variables
of the body below the dummy and object-variable binders. -/
theorem lowerWff_doubleBind_fresh (rho : Var → Nat) (dummy y x : Var) (p : Wff)
    (hdummy_p : dummy ∉ p.fv) (hy_p : y ∉ p.fv) :
    lowerWff (bindRho (bindRho rho dummy) x) p = lowerWff (bindRho (bindRho rho y) x) p :=
  by
  apply lowerWff_congr_fv
  intro z hz
  have hzd : z ≠ dummy := fun h => hdummy_p (h ▸ hz)
  have hzy : z ≠ y := fun h => hy_p (h ▸ hz)
  by_cases hzx : z = x
  · subst z
    simp [bindRho]
  · simp [bindRho, hzx, hzd, hzy]

/-- Alpha-renaming the fresh source dummy is definitional after lowering. -/
theorem lowerEuPrimitive_eq (rho : Var → Nat) (dummy y x : Var) (p : Wff)
    (hdummy_x : dummy ≠ x) (hy_x : y ≠ x) (hdummy_p : dummy ∉ p.fv) (hy_p : y ∉ p.fv) :
    lowerWff rho (euPrimitive dummy x p) = lowerWff rho (euPrimitive y x p) :=
  by
  have hp := lowerWff_doubleBind_fresh rho dummy y x p hdummy_p hy_p
  simp only [euPrimitive, syn_wex, syn_wb, Wff.neg, lowerWff]
  rw [hp]
  simp [bindRho, hdummy_x, hy_x]

/-- Direct proof-algebra implementation of the Metamath `df-eu` axiom.
The hypotheses are exactly its two source `$d` obligations. -/
@[expose]
noncomputable def dfEu (x y : Var) (p : Wff) (hxy : x ≠ y) (hy_p : y ∉ p.fv) :
    NPrf (syn_wb (syn_weu x p) (euPrimitive y x p)) := fun rho =>
  by
  let support : Finset Var := ({ x } : Finset Var) ∪ p.fv
  let dummy : Var := freshVar support 0
  have hdummy : dummy ∉ support := freshVar_not_mem support 0
  have hdummy_x : dummy ≠ x := by
    intro h
    apply hdummy
    simp [support, h]
  have hdummy_p : dummy ∉ p.fv := by
    intro h
    exact hdummy (by simp [support, h])
  have hLower : lowerWff rho (euPrimitive dummy x p) = lowerWff rho (euPrimitive y x p) :=
    lowerEuPrimitive_eq rho dummy y x p hdummy_x (Ne.symm hxy) hdummy_p hy_p
  change
    Fol.prf _
      (biimp (lowerWff rho (euPrimitive dummy x p)) (lowerWff rho (euPrimitive y x p)))
  rw [← hLower]
  simpa [Wff.biimp, Wff.conj, Wff.neg, lowerWff, biimp, conj, neg] using
    (biimpRefl (euPrimitive dummy x p) rho)


end NFChoice.DirectNominalPrf.Nominal
