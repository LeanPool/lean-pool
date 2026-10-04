/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaTransport
public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart010
public import LeanPool.NFWeakPartition.FocusedFVPaths

/-! NF weak partition development: NominalAlphaRepairedBase001022Iota. -/


public section


namespace NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit
open NFChoice.Compiler.WPPCompactSyntaxFVExplicit
open NFChoice.Compiler.CoreFVSimp
open NFChoice.DefinitionLeaves.AlphaFocusedSupport
open NFChoice.DefinitionLeaves.AlphaFocusedFV
open NFChoice.DirectNominalPrf
open NFChoice.DirectNominalPrf.Nominal

/-- Checked nominal proof certificate identified upstream as `nominal_df_iota`. -/
@[expose]
noncomputable def nominalDfIota (ph : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCio x ph) (synCuni (.cab y (.classEq (.cab x ph) (synCsn (.cv y)))))) :=
  by
  let alphaDummy000 : Var := (freshVar (({ x } : Finset Var) ∪ (ph).fv) 0)
  let alphaDummy001 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (Wff.classEq (Class.cab x ph) (synCsn (Class.cv alphaDummy000))))).fv) 0)
  let alphaDummy002 : Var :=
    (freshVar (((Class.cab alphaDummy000
          (Wff.classEq (Class.cab x ph) (synCsn (Class.cv alphaDummy000))))).fv) 1)
  let alphaDummy003 : Var :=
    (freshVar (((Class.cab y (Wff.classEq (Class.cab x ph) (synCsn (Class.cv y))))).fv) 0)
  let alphaDummy004 : Var :=
    (freshVar (((Class.cab y (Wff.classEq (Class.cab x ph) (synCsn (Class.cv y))))).fv) 1)
  let alphaDummy005 : Var := (freshVar (((Class.cv alphaDummy000)).fv) 0)
  let alphaDummy006 : Var := (freshVar (((Class.cv y)).fv) 0)
  have fresh_000 :
    alphaDummy001 ∉
      (((Class.cab alphaDummy000
          (Wff.classEq (Class.cab x ph) (synCsn (Class.cv alphaDummy000))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy000
            (Wff.classEq (Class.cab x ph) (synCsn (Class.cv alphaDummy000))))).fv)
        0
  have fresh_001 :
    alphaDummy002 ∉
      (((Class.cab alphaDummy000
          (Wff.classEq (Class.cab x ph) (synCsn (Class.cv alphaDummy000))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab alphaDummy000
            (Wff.classEq (Class.cab x ph) (synCsn (Class.cv alphaDummy000))))).fv)
        1
  have fresh_003 :
    alphaDummy003 ∉
      (((Class.cab y (Wff.classEq (Class.cab x ph) (synCsn (Class.cv y))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab y (Wff.classEq (Class.cab x ph) (synCsn (Class.cv y))))).fv) 0
  have fresh_004 :
    alphaDummy004 ∉
      (((Class.cab y (Wff.classEq (Class.cab x ph) (synCsn (Class.cv y))))).fv) :=
    by
    exact
      freshVar_not_mem
        (((Class.cab y (Wff.classEq (Class.cab x ph) (synCsn (Class.cv y))))).fv) 1
  have fresh_008 : alphaDummy000 ∉ (({ x } : Finset Var) ∪ (ph).fv) := by
    exact freshVar_not_mem (({ x } : Finset Var) ∪ (ph).fv) 0
  have support_part_0000 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0000 : alphaDummy000 ∈ (((Class.cv alphaDummy000)).fv) := by
    exact support_part_0000
  have support_part_0001 : y ∈ (((Class.cv y)).fv) := by
    simp only [Finset.mem_singleton, fv_class_cv, eq_self]
  have support_mem_0001 : y ∈ (((Class.cv y)).fv) := by exact support_part_0001
  exact
    Nominal.alphaClassEq
      (TAlphaClass.cab (TAlphaWff.ex (TAlphaWff.conj (TAlphaWff.objMem (TAlphaVar.there
                (freshVar_injective (((Class.cab alphaDummy000 (Wff.classEq (Class.cab x ph)
                        (synCsn (Class.cv alphaDummy000))))).fv) (by decide))
                (freshVar_injective (((Class.cab y
                      (Wff.classEq (Class.cab x ph) (synCsn (Class.cv y))))).fv) (by decide))
                (TAlphaVar.here _ _ _)) (TAlphaVar.here _ _ _))
            (TAlphaWff.classMem (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cab
                (TAlphaWff.classEq (TAlphaClass.cab (TAlphaWff.reflOfFvFresh _ _ (by
                        intro a b h hne;
                        simp only [List.mem_cons, List.not_mem_nil, or_false,
                          Prod.mk.injEq] at h;
                        repeat'
                          (first
                            | (rcases h with ⟨rfl, rfl⟩));
                          all_goals aesop))) (TAlphaClass.cab
                    (TAlphaWff.classEq (TAlphaClass.cv (TAlphaVar.here _ _ _)) (TAlphaClass.cv
                        (TAlphaVar.there (Nat.ne_of_lt (mem_lt_freshVar support_mem_0000 0))
                          (Nat.ne_of_lt (mem_lt_freshVar support_mem_0001 0))
                          (TAlphaVar.here _ _ _)))))))))))

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired
