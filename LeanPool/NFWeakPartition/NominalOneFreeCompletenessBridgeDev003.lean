/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.BoundedNominalLoweringBridgeDev004
public import LeanPool.NFWeakPartition.NominalSubstitutionLemmas

/-! NF weak partition development: NominalOneFreeCompletenessBridgeDev003. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.OneFreeCompletenessBridgeDev003

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.DirectNominalPrf.Nominal
open NFChoice.DirectNominalPrf.Nominal.BoundedNominalLoweringBridgeDev004

abbrev NFTheory : Fol.SentTheory LNF :=
  NFChoice.Foundation.ExactLiteralTrial.LiteralHailperinNF

theorem oneFreeLoweringAsSubst (x : Var) (p : Wff) (hfv : p.fv ⊆ ({ x } : Finset Var))
    (rho : Var → Nat) :
    lowerWff rho p =
      ((NFChoice.SemanticCore.Lowering.lowerWff (fun _ : Var => (0 : Fin 1))
              p).toFlypitch).fst [(&(rho x)) //
        0]f :=
  by
  let boundedRho : Var → Fin 1 := fun _ => 0
  have hRaw :
    lowerWff (finValRho boundedRho) p =
      ((NFChoice.SemanticCore.Lowering.lowerWff boundedRho p).toFlypitch).fst :=
    lowerWff_toFlypitch boundedRho p
  let sigma : Nat → Nat := fun index => substIndexAt index (rho x) 0
  have hEnv : ∀ y, y ∈ p.fv → rho y = renameRho sigma (finValRho boundedRho) y :=
    by
    intro y hy
    have hyx : y = x := Finset.mem_singleton.mp (hfv hy)
    subst y
    simp [renameRho, sigma, substIndexAt, finValRho, boundedRho]
  calc
    lowerWff rho p = lowerWff (renameRho sigma (finValRho boundedRho)) p :=
      lowerWff_congr_fv rho (renameRho sigma (finValRho boundedRho)) p hEnv
    _ = renameFormula sigma (lowerWff (finValRho boundedRho) p) :=
      (lowerWff_rename sigma (finValRho boundedRho) p)
    _ =
        renameFormula sigma
          ((NFChoice.SemanticCore.Lowering.lowerWff boundedRho p).toFlypitch).fst :=
      by rw [hRaw]
    _ =
        ((NFChoice.SemanticCore.Lowering.lowerWff boundedRho p).toFlypitch).fst [(&(rho x)) //
          0]f :=
      by exact renameFormula_substIndexAt (rho x) 0 _
    _ =
        ((NFChoice.SemanticCore.Lowering.lowerWff (fun _ : Var => (0 : Fin 1))
                p).toFlypitch).fst [(&(rho x)) //
          0]f :=
      rfl

@[expose]
noncomputable def oneFreeNPrfOfValidity (x : Var) (p : Wff)
    (hfv : p.fv ⊆ ({ x } : Finset Var))
    (hvalid : ∀ (S : Fol.Structure LNF),
        Nonempty S → Fol.all_realize_sentence S NFTheory → Wff.Valid S p) :
    NPrf p := by
  intro rho
  let f : Formula 1 :=
    NFChoice.SemanticCore.Lowering.lowerWff (fun _ : Var => (0 : Fin 1)) p
  have hProv : NFTheory ⊢ₛ' Fol.bd_alls 1 f.toFlypitch :=
    by
    apply (Fol.completeness NFTheory (Fol.bd_alls 1 f.toFlypitch)).2
    intro S hNonempty hNF
    rw [Fol.realize_sentence_bd_alls]
    intro xs
    let v : Var → S := fun _ => NFChoice.SemanticCore.Lowering.lookup xs 0
    apply
      (NFChoice.SemanticCore.Lowering.lowerWff_realize_iff (fun _ : Var => (0 : Fin 1)) xs
          v (by intro y; simp [v]) p).mp
    exact hvalid S hNonempty hNF v
  have hAll : Fol.prf NFTheory.fst (Fol.preformula.all f.toFlypitch.fst) := by
    exact Classical.choice hProv
  have hInst : Fol.prf NFTheory.fst (f.toFlypitch.fst [(&(rho x)) // 0]f) :=
    Fol.prf.allE₂ f.toFlypitch.fst (&(rho x)) hAll
  rw [oneFreeLoweringAsSubst x p hfv rho]
  simpa [f, NFTheory] using hInst


end NFChoice.DirectNominalPrf.Nominal.OneFreeCompletenessBridgeDev003
