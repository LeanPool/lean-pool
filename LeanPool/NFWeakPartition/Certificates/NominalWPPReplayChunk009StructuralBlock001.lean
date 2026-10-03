/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001013Xpk
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001014Cnvk
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001015Ins2k
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001016Ins3k
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001017Imak
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001018P6
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001019Sik
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001020Ssetk
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001021Idk
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001022Iota
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001023Addc
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001024Nnc
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001025Lefin
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001026Ltfin
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001027Ncfin
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001028Tfin
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001029Evenfin
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001030Oddfin
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001031Sfin
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001032Spfin
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001033Phi
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001034OpReflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001035Proj1Reflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001036Proj2Reflected001
public import LeanPool.NFWeakPartition.NominalAlphaRepairedBase001037OpabOpaqueHoisted004
public import LeanPool.NFWeakPartition.NominalNFLiteralXpViaCompletenessDev003
public import LeanPool.NFWeakPartition.NominalNFLiteralRemainingViaCompletenessDev001
public import LeanPool.NFWeakPartition.NominalWPPReplayChunk008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart001`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_elpw1101c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
        (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                          (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have freeVariableCertificate0 :
    y ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have p0000 :=
    @g_elpw1 y A
      (syn_cpw1 (syn_cpw1 (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate0
  have p0001 :=
    (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
        (.classEq A (syn_csn (.cv y)))))
  have freeVariableCertificate1 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0002 := @g_elpw191c x (.cv y) freeVariableCertificate1
  have p0003 :=
    @g_anbi1i
      (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
      (.classEq A (syn_csn (.cv y))) p0002
  have freeVariableCertificate2 : x ∉ ((Wff.classEq A (syn_csn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      dv_A_x, fresh_x_ne_y, or_false, not_false_eq_true]
  have p0004 :=
    @g_n_19_41v
      (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
      (.classEq A (syn_csn (.cv y))) x freeVariableCertificate2
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
          (.classEq A (syn_csn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
          (.classEq A (syn_csn (.cv y)))))
      y p0005
  have p0007 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
          (.classEq A (syn_csn (.cv y)))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
            (.classEq A (syn_csn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                  (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
        (.classEq A (syn_csn (.cv y))))
      y x
  have p0009 :=
    @g_snex
      (syn_csn (syn_csn
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))
  have p0010 :=
    @g_sneq (.cv y)
      (syn_csn (syn_csn (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
  have p0011 :=
    @g_eqeq2d
      (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
      (syn_csn (.cv y))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
      A p0010
  have freeVariableCertificate3 :
    y ∉
      ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                  (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉
      ((Wff.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                        (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y)))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
      y
      (syn_csn (syn_csn (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
      freeVariableCertificate3 freeVariableCertificate4 p0009 p0011
  have p0013 :=
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
          (.classEq A (syn_csn (.cv y)))))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
      x p0012
  have p0014 :=
    @g_bitri
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))
      p0008 p0013
  have p0015 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))
      p0007 p0014
  have p0016 :=
    @g_bitri
      (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))
      p0000 p0015
  exact p0016

@[expose]
noncomputable def g_elpw1111c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))) (syn_wex x
          (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                            (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have freeVariableCertificate0 :
    y ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have p0000 :=
    @g_elpw1 y A
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate0
  have p0001 :=
    (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
        (.classEq A (syn_csn (.cv y)))))
  have freeVariableCertificate1 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0002 := @g_elpw1101c x (.cv y) freeVariableCertificate1
  have p0003 :=
    @g_anbi1i
      (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))
      (.classEq A (syn_csn (.cv y))) p0002
  have freeVariableCertificate2 : x ∉ ((Wff.classEq A (syn_csn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      dv_A_x, fresh_x_ne_y, or_false, not_false_eq_true]
  have p0004 :=
    @g_n_19_41v
      (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
      (.classEq A (syn_csn (.cv y))) x freeVariableCertificate2
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
          (.classEq A (syn_csn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
          (.classEq A (syn_csn (.cv y)))))
      y p0005
  have p0007 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
          (.classEq A (syn_csn (.cv y)))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn
                          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
            (.classEq A (syn_csn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
        (.classEq A (syn_csn (.cv y))))
      y x
  have p0009 :=
    @g_snex
      (syn_csn (syn_csn (syn_csn (syn_csn
              (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))
  have p0010 :=
    @g_sneq (.cv y)
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
  have p0011 :=
    @g_eqeq2d
      (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
      (syn_csn (.cv y))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
      A p0010
  have freeVariableCertificate3 :
    y ∉
      ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉
      ((Wff.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                          (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0012 :=
    @g_ceqsexv (.classEq A (syn_csn (.cv y)))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))
      y
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))
      freeVariableCertificate3 freeVariableCertificate4 p0009 p0011
  have p0013 :=
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
          (.classEq A (syn_csn (.cv y)))))
      (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))))))))
      x p0012
  have p0014 :=
    @g_bitri
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn
                          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn
                          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))))
      p0008 p0013
  have p0015 :=
    @g_bitri
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (syn_csn
                      (syn_csn (syn_csn
                          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))
            (.classEq A (syn_csn (.cv y))))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))))
      p0007 p0014
  have p0016 :=
    @g_bitri
      (.classMem A (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
        (.classEq A (syn_csn (.cv y))))
      (syn_wex x (.classEq A (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn
                        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))))))))
      p0000 p0015
  exact p0016

@[expose]
noncomputable def g_pw1ss1c (A : Class) : Nominal.NPrf (syn_wss (syn_cpw1 A) (syn_c1c)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cpw1 A))
  have p0001 := @g_inss2 (syn_cpw A) (syn_c1c)
  have p0002 :=
    @g_eqsstri (syn_cpw1 A) (syn_cin (syn_cpw A) (syn_c1c)) (syn_c1c) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_n_0nel1c : Nominal.NPrf (.neg (.classMem (syn_c0) (syn_c1c))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := @g_vex x
  have p0001 := @g_snprc (.cv x)
  have p0002 := @g_eqcom (syn_csn (.cv x)) (syn_c0)
  have p0003 :=
    @g_bitri (.neg (.classMem (.cv x) (syn_cvv))) (.classEq (syn_csn (.cv x)) (syn_c0))
      (.classEq (syn_c0) (syn_csn (.cv x))) p0001 p0002
  have p0004 :=
    @g_con1bii (.classMem (.cv x) (syn_cvv)) (.classEq (syn_c0) (syn_csn (.cv x))) p0003
  have p0005 :=
    @g_mpbir (.neg (.classEq (syn_c0) (syn_csn (.cv x)))) (.classMem (.cv x) (syn_cvv))
      p0000 p0004
  have p0006 := @g_nex (.classEq (syn_c0) (syn_csn (.cv x))) x p0005
  have p0007 :=
    @g_el1c x (syn_c0)
      (by
        exact
          (show x ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0008 :=
    @g_mtbir (.classMem (syn_c0) (syn_c1c))
      (syn_wex x (.classEq (syn_c0) (syn_csn (.cv x)))) p0006 p0007
  exact p0008

@[expose]
noncomputable def g_pw0 : Nominal.NPrf (.classEq (syn_cpw (syn_c0)) (syn_csn (syn_c0))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := @g_ss0b (.cv x)
  have p0001 := @g_abbii (syn_wss (.cv x) (syn_c0)) (.classEq (.cv x) (syn_c0)) x p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw x (syn_c0)
      (by
        exact
          (show x ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x (syn_c0)
      (by
        exact
          (show x ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0004 :=
    @g_n_3eqtr4i (.cab x (syn_wss (.cv x) (syn_c0))) (.cab x (.classEq (.cv x) (syn_c0)))
      (syn_cpw (syn_c0)) (syn_csn (syn_c0)) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_pw10 : Nominal.NPrf (.classEq (syn_cpw1 (syn_c0)) (syn_c0)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := (Nominal.classEqRefl (syn_cpw1 (syn_c0)))
  have p0001 := @g_pw0
  have p0002 := @g_ineq1i (syn_cpw (syn_c0)) (syn_csn (syn_c0)) (syn_c1c) p0001
  have freeVariableCertificate0 : x ∉ ((syn_csn (syn_c0))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.notMem_empty,
      not_false_eq_true]
  have p0003 :=
    @g_disj x (syn_csn (syn_c0)) (syn_c1c) freeVariableCertificate0
      (by
        exact
          (show x ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0004 := @g_n_0nel1c
  have p0005 :=
    @g_elsn x (syn_c0)
      (by
        exact
          (show x ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0006 := @g_eleq1 (.cv x) (syn_c0) (syn_c1c)
  have p0007 :=
    @g_sylbi (.classMem (.cv x) (syn_csn (syn_c0))) (.classEq (.cv x) (syn_c0))
      (syn_wb (.classMem (.cv x) (syn_c1c)) (.classMem (syn_c0) (syn_c1c))) p0005 p0006
  have p0008 :=
    @g_mtbiri (.classMem (.cv x) (syn_csn (syn_c0))) (.classMem (.cv x) (syn_c1c))
      (.classMem (syn_c0) (syn_c1c)) p0004 p0007
  have p0009 :=
    @g_mprgbir (.classEq (syn_cin (syn_csn (syn_c0)) (syn_c1c)) (syn_c0))
      (.neg (.classMem (.cv x) (syn_c1c))) x (syn_csn (syn_c0)) p0003 p0008
  have p0010 :=
    @g_n_3eqtri (syn_cpw1 (syn_c0)) (syn_cin (syn_cpw (syn_c0)) (syn_c1c))
      (syn_cin (syn_csn (syn_c0)) (syn_c1c)) (syn_c0) p0000 p0002 p0009
  exact p0010

@[expose]
noncomputable def g_eqpw1 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (syn_wb (.classEq A (syn_cpw1 B)) (syn_wa (syn_wss A (syn_c1c))
          (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have p0000 := @g_pw1ss1c B
  have p0001 := @g_sseq1 A (syn_cpw1 B) (syn_c1c)
  have p0002 :=
    @g_mpbiri (.classEq A (syn_cpw1 B)) (syn_wss A (syn_c1c))
      (syn_wss (syn_cpw1 B) (syn_c1c)) p0000 p0001
  have p0003 :=
    @g_ssofeq y A (syn_cpw1 B) (syn_c1c)
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by
        exact
          (show y ∉ ((syn_cpw1 B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
              exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))))
      (by
        exact
          (show y ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0004 :=
    @g_mpan2 (syn_wss A (syn_c1c)) (syn_wss (syn_cpw1 B) (syn_c1c))
      (syn_wb (.classEq A (syn_cpw1 B)) (syn_wral y (syn_c1c)
          (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))))
      p0000 p0003
  have p0005 :=
    (Nominal.biimpRefl (syn_wral y (syn_c1c)
        (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))))
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0006 := @g_el1c x (.cv y) freeVariableCertificate0
  have p0007 :=
    @g_imbi1i (.classMem (.cv y) (syn_c1c))
      (syn_wex x (.classEq (.cv y) (syn_csn (.cv x))))
      (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))) p0006
  have freeVariableCertificate1 :
    x ∉ ((syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_y, dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have p0008 :=
    @g_n_19_23v (.classEq (.cv y) (syn_csn (.cv x)))
      (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))) x
      freeVariableCertificate1
  have p0009 :=
    @g_bitr4i
      (.imp (.classMem (.cv y) (syn_c1c))
        (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))
      (.imp (syn_wex x (.classEq (.cv y) (syn_csn (.cv x))))
        (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))
      (.all x (.imp (.classEq (.cv y) (syn_csn (.cv x)))
          (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))))
      p0007 p0008
  have p0010 :=
    @g_albii
      (.imp (.classMem (.cv y) (syn_c1c))
        (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))
      (.all x (.imp (.classEq (.cv y) (syn_csn (.cv x)))
          (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))))
      y p0009
  have p0011 :=
    @g_alcom
      (.imp (.classEq (.cv y) (syn_csn (.cv x)))
        (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))
      x y
  have p0012 :=
    @g_bitr4i
      (.all y (.imp (.classMem (.cv y) (syn_c1c))
          (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))))
      (.all y (.all x (.imp (.classEq (.cv y) (syn_csn (.cv x)))
            (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))))
      (.all x (.all y (.imp (.classEq (.cv y) (syn_csn (.cv x)))
            (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))))
      p0010 p0011
  have p0013 :=
    @g_bitri
      (syn_wral y (syn_c1c) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))
      (.all y (.imp (.classMem (.cv y) (syn_c1c))
          (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))))
      (.all x (.all y (.imp (.classEq (.cv y) (syn_csn (.cv x)))
            (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))))
      p0005 p0012
  have p0014 := @g_snex (.cv x)
  have p0015 := @g_eleq1 (.cv y) (syn_csn (.cv x)) A
  have p0016 := @g_eleq1 (.cv y) (syn_csn (.cv x)) (syn_cpw1 B)
  have p0017 :=
    @g_bibi12d (.classEq (.cv y) (syn_csn (.cv x))) (.classMem (.cv y) A)
      (.classMem (syn_csn (.cv x)) A) (.classMem (.cv y) (syn_cpw1 B))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 B)) p0015 p0016
  have freeVariableCertificate2 : y ∉ ((syn_csn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate3 :
    y ∉
      ((syn_wb (.classMem (syn_csn (.cv x)) A)
          (.classMem (syn_csn (.cv x)) (syn_cpw1 B)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, fresh_y_not_B, or_false,
      not_false_eq_true]
  have p0018 :=
    @g_ceqsalv (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))
      (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (syn_csn (.cv x)) (syn_cpw1 B)))
      y (syn_csn (.cv x)) freeVariableCertificate2 freeVariableCertificate3 p0014 p0017
  have p0019 := @g_snelpw1 (.cv x) B
  have p0020 :=
    @g_bibi2i (.classMem (syn_csn (.cv x)) (syn_cpw1 B)) (.classMem (.cv x) B)
      (.classMem (syn_csn (.cv x)) A) p0019
  have p0021 :=
    @g_bitri
      (.all y (.imp (.classEq (.cv y) (syn_csn (.cv x)))
          (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))))
      (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (syn_csn (.cv x)) (syn_cpw1 B)))
      (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)) p0018 p0020
  have p0022 :=
    @g_albii
      (.all y (.imp (.classEq (.cv y) (syn_csn (.cv x)))
          (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B)))))
      (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B)) x p0021
  have p0023 :=
    @g_bitri
      (syn_wral y (syn_c1c) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))
      (.all x (.all y (.imp (.classEq (.cv y) (syn_csn (.cv x)))
            (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))))
      (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) p0013 p0022
  have p0024 :=
    @g_syl6bb (syn_wss A (syn_c1c)) (.classEq A (syn_cpw1 B))
      (syn_wral y (syn_c1c) (syn_wb (.classMem (.cv y) A) (.classMem (.cv y) (syn_cpw1 B))))
      (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) p0004 p0023
  have p0025 :=
    @g_biadan2 (.classEq A (syn_cpw1 B)) (syn_wss A (syn_c1c))
      (.all x (syn_wb (.classMem (syn_csn (.cv x)) A) (.classMem (.cv x) B))) p0002 p0024
  exact p0025

@[expose]
noncomputable def g_pw1un (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_cpw1 (syn_cun A B)) (syn_cun (syn_cpw1 A) (syn_cpw1 B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 := @g_rexun (.classEq (.cv x) (syn_csn (.cv y))) y A B
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((syn_cun A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0001 :=
    @g_elpw1 y (.cv x) (syn_cun A B) freeVariableCertificate0 freeVariableCertificate1
  have p0002 := @g_elun (.cv x) (syn_cpw1 A) (syn_cpw1 B)
  have p0003 :=
    @g_elpw1 y (.cv x) A freeVariableCertificate0
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0004 :=
    @g_elpw1 y (.cv x) B freeVariableCertificate0
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0005 :=
    @g_orbi12i (.classMem (.cv x) (syn_cpw1 A))
      (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))) (.classMem (.cv x) (syn_cpw1 B))
      (syn_wrex y B (.classEq (.cv x) (syn_csn (.cv y)))) p0003 p0004
  have p0006 :=
    @g_bitri (.classMem (.cv x) (syn_cun (syn_cpw1 A) (syn_cpw1 B)))
      (syn_wo (.classMem (.cv x) (syn_cpw1 A)) (.classMem (.cv x) (syn_cpw1 B)))
      (syn_wo (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y))))
        (syn_wrex y B (.classEq (.cv x) (syn_csn (.cv y)))))
      p0002 p0005
  have p0007 :=
    @g_n_3bitr4i (syn_wrex y (syn_cun A B) (.classEq (.cv x) (syn_csn (.cv y))))
      (syn_wo (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y))))
        (syn_wrex y B (.classEq (.cv x) (syn_csn (.cv y)))))
      (.classMem (.cv x) (syn_cpw1 (syn_cun A B)))
      (.classMem (.cv x) (syn_cun (syn_cpw1 A) (syn_cpw1 B))) p0000 p0001 p0006
  have freeVariableCertificate2 : x ∉ ((syn_cpw1 (syn_cun A B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate3 : x ∉ ((syn_cun (syn_cpw1 A) (syn_cpw1 B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0008 :=
    @g_eqriv x (syn_cpw1 (syn_cun A B)) (syn_cun (syn_cpw1 A) (syn_cpw1 B))
      freeVariableCertificate2 freeVariableCertificate3 p0007
  exact p0008

@[expose]
noncomputable def g_pw1in (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_cpw1 (syn_cin A B)) (syn_cin (syn_cpw1 A) (syn_cpw1 B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 :=
    @g_ancom (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) (syn_cpw1 B)))
      (.classEq (.cv x) (syn_csn (.cv y)))
  have p0001 := @g_eleq1 (.cv x) (syn_csn (.cv y)) (syn_cpw1 B)
  have p0002 := @g_snelpw1 (.cv y) B
  have p0003 :=
    @g_syl6bb (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B))
      (.classMem (syn_csn (.cv y)) (syn_cpw1 B)) (.classMem (.cv y) B) p0001 p0002
  have p0004 :=
    @g_anbi2d (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B))
      (.classMem (.cv y) B) (.classMem (.cv y) A) p0003
  have p0005 := @g_elin (.cv y) A B
  have p0006 :=
    @g_syl6bbr (.classEq (.cv x) (syn_csn (.cv y)))
      (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) (syn_cpw1 B)))
      (syn_wa (.classMem (.cv y) A) (.classMem (.cv y) B))
      (.classMem (.cv y) (syn_cin A B)) p0004 p0005
  have p0007 :=
    @g_pm5_32ri (.classEq (.cv x) (syn_csn (.cv y)))
      (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) (syn_cpw1 B)))
      (.classMem (.cv y) (syn_cin A B)) p0006
  have p0008 :=
    @g_an12 (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)
      (.classMem (.cv x) (syn_cpw1 B))
  have p0009 :=
    @g_n_3bitr3i
      (syn_wa (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) (syn_cpw1 B)))
        (.classEq (.cv x) (syn_csn (.cv y))))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv y)))
        (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) (syn_cpw1 B))))
      (syn_wa (.classMem (.cv y) (syn_cin A B)) (.classEq (.cv x) (syn_csn (.cv y))))
      (syn_wa (.classMem (.cv y) A)
        (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B))))
      p0000 p0007 p0008
  have p0010 :=
    @g_rexbii2 (.classEq (.cv x) (syn_csn (.cv y)))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B))) y
      (syn_cin A B) A p0009
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((syn_cin A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0011 :=
    @g_elpw1 y (.cv x) (syn_cin A B) freeVariableCertificate0 freeVariableCertificate1
  have p0012 :=
    @g_elpw1 y (.cv x) A freeVariableCertificate0
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0013 :=
    @g_anbi1i (.classMem (.cv x) (syn_cpw1 A))
      (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))) (.classMem (.cv x) (syn_cpw1 B))
      p0012
  have p0014 := @g_elin (.cv x) (syn_cpw1 A) (syn_cpw1 B)
  have freeVariableCertificate2 : y ∉ ((Wff.classMem (.cv x) (syn_cpw1 B))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, or_false, not_false_eq_true]
  have p0015 :=
    @g_r19_41v (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B)) y A
      freeVariableCertificate2
  have p0016 :=
    @g_n_3bitr4i
      (syn_wa (.classMem (.cv x) (syn_cpw1 A)) (.classMem (.cv x) (syn_cpw1 B)))
      (syn_wa (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y))))
        (.classMem (.cv x) (syn_cpw1 B)))
      (.classMem (.cv x) (syn_cin (syn_cpw1 A) (syn_cpw1 B)))
      (syn_wrex y A
        (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B))))
      p0013 p0014 p0015
  have p0017 :=
    @g_n_3bitr4i (syn_wrex y (syn_cin A B) (.classEq (.cv x) (syn_csn (.cv y))))
      (syn_wrex y A
        (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) (syn_cpw1 B))))
      (.classMem (.cv x) (syn_cpw1 (syn_cin A B)))
      (.classMem (.cv x) (syn_cin (syn_cpw1 A) (syn_cpw1 B))) p0010 p0011 p0016
  have freeVariableCertificate3 : x ∉ ((syn_cpw1 (syn_cin A B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate4 : x ∉ ((syn_cin (syn_cpw1 A) (syn_cpw1 B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0018 :=
    @g_eqriv x (syn_cpw1 (syn_cin A B)) (syn_cin (syn_cpw1 A) (syn_cpw1 B))
      freeVariableCertificate3 freeVariableCertificate4 p0017
  exact p0018

@[expose]
noncomputable def g_pw1sn (A : Class)
    (hyp_pw1sn_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cpw1 (syn_csn A)) (syn_csn (syn_csn A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 := @g_sneq (.cv y) A
  have p0001 := @g_eqeq2d (.classEq (.cv y) A) (syn_csn (.cv y)) (syn_csn A) (.cv x) p0000
  have freeVariableCertificate0 : y ∉ ((Wff.classEq (.cv x) (syn_csn A))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true]
  have p0002 :=
    @g_rexsn (.classEq (.cv x) (syn_csn (.cv y))) (.classEq (.cv x) (syn_csn A)) y A
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate0
      hyp_pw1sn_1 p0001
  have freeVariableCertificate1 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0003 :=
    @g_elpw1 y (.cv x) (syn_csn A) freeVariableCertificate1
      (by
        exact
          (show y ∉ ((syn_csn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
  have p0004 :=
    @g_elsn x (syn_csn A)
      (by
        exact
          (show x ∉ ((syn_csn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
  have p0005 :=
    @g_n_3bitr4i (syn_wrex y (syn_csn A) (.classEq (.cv x) (syn_csn (.cv y))))
      (.classEq (.cv x) (syn_csn A)) (.classMem (.cv x) (syn_cpw1 (syn_csn A)))
      (.classMem (.cv x) (syn_csn (syn_csn A))) p0002 p0003 p0004
  have freeVariableCertificate2 : x ∉ ((syn_cpw1 (syn_csn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_A,
      not_false_eq_true]
  have freeVariableCertificate3 : x ∉ ((syn_csn (syn_csn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_A,
      not_false_eq_true]
  have p0006 :=
    @g_eqriv x (syn_cpw1 (syn_csn A)) (syn_csn (syn_csn A)) freeVariableCertificate2
      freeVariableCertificate3 p0005
  exact p0006

@[expose]
noncomputable def g_pw10b (A : Class) :
    Nominal.NPrf (syn_wb (.classEq (syn_cpw1 A) (syn_c0)) (.classEq A (syn_c0))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have p0000 := @g_n0 x A (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0001 := @g_snelpw1 (.cv x) A
  have p0002 := @g_ne0i (syn_cpw1 A) (syn_csn (.cv x))
  have p0003 :=
    @g_sylbir (.classMem (.cv x) A) (.classMem (syn_csn (.cv x)) (syn_cpw1 A))
      (syn_wne (syn_cpw1 A) (syn_c0)) p0001 p0002
  have freeVariableCertificate0 : x ∉ ((syn_wne (syn_cpw1 A) (syn_c0))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0004 :=
    @g_exlimiv (.classMem (.cv x) A) (syn_wne (syn_cpw1 A) (syn_c0)) x
      freeVariableCertificate0 p0003
  have p0005 :=
    @g_sylbi (syn_wne A (syn_c0)) (syn_wex x (.classMem (.cv x) A))
      (syn_wne (syn_cpw1 A) (syn_c0)) p0000 p0004
  have p0006 := @g_necon4i A (syn_c0) (syn_cpw1 A) (syn_c0) p0005
  have p0007 := @g_pw1eq A (syn_c0)
  have p0008 := @g_pw10
  have p0009 :=
    @g_syl6eq (.classEq A (syn_c0)) (syn_cpw1 A) (syn_cpw1 (syn_c0)) (syn_c0) p0007 p0008
  have p0010 :=
    @g_impbii (.classEq (syn_cpw1 A) (syn_c0)) (.classEq A (syn_c0)) p0006 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart002`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_df1c2 : Nominal.NPrf (.classEq (syn_c1c) (syn_cpw1 (syn_cvv))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 := @g_rexv (.classEq (.cv x) (syn_csn (.cv y))) y
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0001 :=
    @g_elpw1 y (.cv x) (syn_cvv) freeVariableCertificate0
      (by
        exact
          (show y ∉ ((syn_cvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0002 := @g_el1c y (.cv x) freeVariableCertificate0
  have p0003 :=
    @g_n_3bitr4ri (syn_wrex y (syn_cvv) (.classEq (.cv x) (syn_csn (.cv y))))
      (syn_wex y (.classEq (.cv x) (syn_csn (.cv y))))
      (.classMem (.cv x) (syn_cpw1 (syn_cvv))) (.classMem (.cv x) (syn_c1c)) p0000 p0001
      p0002
  have freeVariableCertificate1 : x ∉ ((syn_cpw1 (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.notMem_empty,
      not_false_eq_true]
  have p0004 :=
    @g_eqriv x (syn_c1c) (syn_cpw1 (syn_cvv))
      (by
        exact
          (show x ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0003
  exact p0004

@[expose]
noncomputable def g_pw1ss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wss (syn_cpw1 A) (syn_cpw1 B))) :=
  by
  have p0000 := @g_sspwb A B
  have p0001 := @g_ssrin (syn_cpw A) (syn_cpw B) (syn_c1c)
  have p0002 :=
    @g_sylbi (syn_wss A B) (syn_wss (syn_cpw A) (syn_cpw B))
      (syn_wss (syn_cin (syn_cpw A) (syn_c1c)) (syn_cin (syn_cpw B) (syn_c1c))) p0000
      p0001
  have p0003 := (Nominal.classEqRefl (syn_cpw1 A))
  have p0004 := (Nominal.classEqRefl (syn_cpw1 B))
  have p0005 :=
    @g_n_3sstr4g (syn_wss A B) (syn_cin (syn_cpw A) (syn_c1c))
      (syn_cin (syn_cpw B) (syn_c1c)) (syn_cpw1 A) (syn_cpw1 B) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_pw111 (A : Class) (B : Class) :
    Nominal.NPrf (syn_wb (.classEq (syn_cpw1 A) (syn_cpw1 B)) (.classEq A B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let t : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_t_ne_x : t ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have p0000 := @g_snex (.cv x)
  have p0001 := @g_eleq1 (.cv t) (syn_csn (.cv x)) (syn_cpw1 A)
  have p0002 := @g_eleq1 (.cv t) (syn_csn (.cv x)) (syn_cpw1 B)
  have p0003 :=
    @g_bibi12d (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (.cv t) (syn_cpw1 A))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 B)) p0001 p0002
  have freeVariableCertificate0 : t ∉ ((syn_csn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate1 :
    t ∉
      ((syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 A))
          (.classMem (syn_csn (.cv x)) (syn_cpw1 B)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, fresh_t_not_B, or_false,
      not_false_eq_true]
  have p0004 :=
    @g_ceqsalv (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))
      (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 A))
        (.classMem (syn_csn (.cv x)) (syn_cpw1 B)))
      t (syn_csn (.cv x)) freeVariableCertificate0 freeVariableCertificate1 p0000 p0003
  have p0005 := @g_snelpw1 (.cv x) A
  have p0006 := @g_snelpw1 (.cv x) B
  have p0007 :=
    @g_bibi12i (.classMem (syn_csn (.cv x)) (syn_cpw1 A)) (.classMem (.cv x) A)
      (.classMem (syn_csn (.cv x)) (syn_cpw1 B)) (.classMem (.cv x) B) p0005 p0006
  have p0008 :=
    @g_bitri
      (.all t (.imp (.classEq (.cv t) (syn_csn (.cv x)))
          (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))
      (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 A))
        (.classMem (syn_csn (.cv x)) (syn_cpw1 B)))
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) p0004 p0007
  have p0009 :=
    @g_albii
      (.all t (.imp (.classEq (.cv t) (syn_csn (.cv x)))
          (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0008
  have p0010 := @g_pw1ss1c A
  have p0011 := @g_pw1ss1c B
  have p0012 :=
    @g_ssofeq t (syn_cpw1 A) (syn_cpw1 B) (syn_c1c)
      (by
        exact
          (show t ∉ ((syn_cpw1 A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
              exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))))
      (by
        exact
          (show t ∉ ((syn_cpw1 B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
              exact (show t ∉ (B).fv from (by exact fresh_t_not_B)))))
      (by
        exact
          (show t ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0013 :=
    @g_mp2an (syn_wss (syn_cpw1 A) (syn_c1c)) (syn_wss (syn_cpw1 B) (syn_c1c))
      (syn_wb (.classEq (syn_cpw1 A) (syn_cpw1 B)) (syn_wral t (syn_c1c)
          (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))
      p0010 p0011 p0012
  have p0014 :=
    (Nominal.biimpRefl (syn_wral t (syn_c1c)
        (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))
  have freeVariableCertificate2 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0015 := @g_el1c x (.cv t) freeVariableCertificate2
  have p0016 :=
    @g_imbi1i (.classMem (.cv t) (syn_c1c))
      (syn_wex x (.classEq (.cv t) (syn_csn (.cv x))))
      (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))) p0015
  have freeVariableCertificate3 :
    x ∉ ((syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_t, fresh_x_not_A, fresh_x_not_B, or_false,
      not_false_eq_true]
  have p0017 :=
    @g_n_19_23v (.classEq (.cv t) (syn_csn (.cv x)))
      (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))) x
      freeVariableCertificate3
  have p0018 :=
    @g_bitr4i
      (.imp (.classMem (.cv t) (syn_c1c))
        (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))
      (.imp (syn_wex x (.classEq (.cv t) (syn_csn (.cv x))))
        (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))
      (.all x (.imp (.classEq (.cv t) (syn_csn (.cv x)))
          (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))
      p0016 p0017
  have p0019 :=
    @g_albii
      (.imp (.classMem (.cv t) (syn_c1c))
        (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))
      (.all x (.imp (.classEq (.cv t) (syn_csn (.cv x)))
          (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))
      t p0018
  have p0020 :=
    @g_alcom
      (.imp (.classEq (.cv t) (syn_csn (.cv x)))
        (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))
      t x
  have p0021 :=
    @g_bitri
      (.all t (.imp (.classMem (.cv t) (syn_c1c))
          (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))
      (.all t (.all x (.imp (.classEq (.cv t) (syn_csn (.cv x)))
            (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))))
      (.all x (.all t (.imp (.classEq (.cv t) (syn_csn (.cv x)))
            (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))))
      p0019 p0020
  have p0022 :=
    @g_bitri
      (syn_wral t (syn_c1c)
        (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))
      (.all t (.imp (.classMem (.cv t) (syn_c1c))
          (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B)))))
      (.all x (.all t (.imp (.classEq (.cv t) (syn_csn (.cv x)))
            (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))))
      p0014 p0021
  have p0023 :=
    @g_bitri (.classEq (syn_cpw1 A) (syn_cpw1 B))
      (syn_wral t (syn_c1c)
        (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))
      (.all x (.all t (.imp (.classEq (.cv t) (syn_csn (.cv x)))
            (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))))
      p0013 p0022
  have p0024 :=
    @g_dfcleq x A B (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0025 :=
    @g_n_3bitr4i
      (.all x (.all t (.imp (.classEq (.cv t) (syn_csn (.cv x)))
            (syn_wb (.classMem (.cv t) (syn_cpw1 A)) (.classMem (.cv t) (syn_cpw1 B))))))
      (.all x (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.classEq (syn_cpw1 A) (syn_cpw1 B)) (.classEq A B) p0009 p0023 p0024
  exact p0025

@[expose]
noncomputable def g_eluni1g (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (.classMem A (syn_cuni1 B)) (.classMem (syn_csn A) B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 := (Nominal.classEqRefl (syn_cuni1 B))
  have p0001 := @g_eleq2i (syn_cuni1 B) (syn_cuni (syn_cin B (syn_c1c))) A p0000
  have freeVariableCertificate0 : x ∉ ((syn_cin B (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_B, or_false, not_false_eq_true]
  have p0002 :=
    @g_eluni x A (syn_cin B (syn_c1c))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate0
  have p0003 := @g_elin (.cv x) B (syn_c1c)
  have p0004 := @g_ancom (.classMem (.cv x) B) (.classMem (.cv x) (syn_c1c))
  have freeVariableCertificate1 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0005 := @g_el1c y (.cv x) freeVariableCertificate1
  have p0006 :=
    @g_anbi1i (.classMem (.cv x) (syn_c1c))
      (syn_wex y (.classEq (.cv x) (syn_csn (.cv y)))) (.classMem (.cv x) B) p0005
  have freeVariableCertificate2 : y ∉ ((Wff.classMem (.cv x) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_x, fresh_y_not_B, or_false, not_false_eq_true]
  have p0007 :=
    @g_n_19_41v (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B) y
      freeVariableCertificate2
  have p0008 :=
    @g_bitr4i (syn_wa (.classMem (.cv x) (syn_c1c)) (.classMem (.cv x) B))
      (syn_wa (syn_wex y (.classEq (.cv x) (syn_csn (.cv y)))) (.classMem (.cv x) B))
      (syn_wex y (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)))
      p0006 p0007
  have p0009 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cin B (syn_c1c)))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv x) (syn_c1c)))
      (syn_wa (.classMem (.cv x) (syn_c1c)) (.classMem (.cv x) B))
      (syn_wex y (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)))
      p0003 p0004 p0008
  have p0010 :=
    @g_anbi2i (.classMem (.cv x) (syn_cin B (syn_c1c)))
      (syn_wex y (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)))
      (.classMem A (.cv x)) p0009
  have freeVariableCertificate3 : y ∉ ((Wff.classMem A (.cv x))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0011 :=
    @g_n_19_42v (.classMem A (.cv x))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)) y
      freeVariableCertificate3
  have p0012 :=
    @g_bitr4i (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) (syn_cin B (syn_c1c))))
      (syn_wa (.classMem A (.cv x))
        (syn_wex y (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B))))
      (syn_wex y (syn_wa (.classMem A (.cv x))
          (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B))))
      p0010 p0011
  have p0013 :=
    @g_exbii (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) (syn_cin B (syn_c1c))))
      (syn_wex y (syn_wa (.classMem A (.cv x))
          (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B))))
      x p0012
  have p0014 :=
    @g_excom
      (syn_wa (.classMem A (.cv x))
        (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)))
      x y
  have p0015 :=
    @g_an12 (.classMem A (.cv x)) (.classEq (.cv x) (syn_csn (.cv y)))
      (.classMem (.cv x) B)
  have p0016 :=
    @g_exbii
      (syn_wa (.classMem A (.cv x))
        (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv y)))
        (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B)))
      x p0015
  have p0017 := @g_snex (.cv y)
  have p0018 := @g_eleq2 (.cv x) (syn_csn (.cv y)) A
  have p0019 := @g_vex y
  have p0020 := @g_elsnc2 A (.cv y) p0019
  have p0021 :=
    @g_syl6bb (.classEq (.cv x) (syn_csn (.cv y))) (.classMem A (.cv x))
      (.classMem A (syn_csn (.cv y))) (.classEq A (.cv y)) p0018 p0020
  have p0022 := @g_eleq1 (.cv x) (syn_csn (.cv y)) B
  have p0023 :=
    @g_anbi12d (.classEq (.cv x) (syn_csn (.cv y))) (.classMem A (.cv x))
      (.classEq A (.cv y)) (.classMem (.cv x) B) (.classMem (syn_csn (.cv y)) B) p0021
      p0022
  have freeVariableCertificate4 : x ∉ ((syn_csn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_y,
      not_false_eq_true]
  have freeVariableCertificate5 :
    x ∉ ((syn_wa (.classEq A (.cv y)) (.classMem (syn_csn (.cv y)) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, fresh_x_not_B, or_false,
      not_false_eq_true]
  have p0024 :=
    @g_ceqsexv (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B))
      (syn_wa (.classEq A (.cv y)) (.classMem (syn_csn (.cv y)) B)) x (syn_csn (.cv y))
      freeVariableCertificate4 freeVariableCertificate5 p0017 p0023
  have p0025 := @g_eqcom A (.cv y)
  have p0026 :=
    @g_anbi1i (.classEq A (.cv y)) (.classEq (.cv y) A) (.classMem (syn_csn (.cv y)) B)
      p0025
  have p0027 :=
    @g_n_3bitri
      (syn_wex x (syn_wa (.classMem A (.cv x))
          (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_csn (.cv y)))
          (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) B))))
      (syn_wa (.classEq A (.cv y)) (.classMem (syn_csn (.cv y)) B))
      (syn_wa (.classEq (.cv y) A) (.classMem (syn_csn (.cv y)) B)) p0016 p0024 p0026
  have p0028 :=
    @g_exbii
      (syn_wex x (syn_wa (.classMem A (.cv x))
          (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B))))
      (syn_wa (.classEq (.cv y) A) (.classMem (syn_csn (.cv y)) B)) y p0027
  have p0029 :=
    @g_n_3bitri
      (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) (syn_cin B (syn_c1c)))))
      (syn_wex x (syn_wex y (syn_wa (.classMem A (.cv x))
            (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)))))
      (syn_wex y (syn_wex x (syn_wa (.classMem A (.cv x))
            (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) B)))))
      (syn_wex y (syn_wa (.classEq (.cv y) A) (.classMem (syn_csn (.cv y)) B))) p0013
      p0014 p0028
  have p0030 :=
    @g_n_3bitri (.classMem A (syn_cuni1 B)) (.classMem A (syn_cuni (syn_cin B (syn_c1c))))
      (syn_wex x (syn_wa (.classMem A (.cv x)) (.classMem (.cv x) (syn_cin B (syn_c1c)))))
      (syn_wex y (syn_wa (.classEq (.cv y) A) (.classMem (syn_csn (.cv y)) B))) p0001
      p0002 p0029
  have p0031 := @g_sneq (.cv y) A
  have p0032 := @g_eleq1d (.classEq (.cv y) A) (syn_csn (.cv y)) (syn_csn A) B p0031
  have freeVariableCertificate6 : y ∉ ((Wff.classMem (syn_csn A) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0033 :=
    @g_ceqsexgv (.classMem (syn_csn (.cv y)) B) (.classMem (syn_csn A) B) y A V
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate6
      p0032
  have p0034 :=
    @g_syl5bb (.classMem A (syn_cuni1 B))
      (syn_wex y (syn_wa (.classEq (.cv y) A) (.classMem (syn_csn (.cv y)) B)))
      (.classMem A V) (.classMem (syn_csn A) B) p0030 p0033
  exact p0034

@[expose]
noncomputable def g_eluni1 (A : Class) (B : Class)
    (hyp_eluni1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem A (syn_cuni1 B)) (.classMem (syn_csn A) B)) :=
  by
  have p0000 := @g_eluni1g A B (syn_cvv)
  have p0001 := Nominal.mp hyp_eluni1_1 p0000
  exact p0001

@[expose]
noncomputable def g_elxpk (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cxpk B C)) (syn_wex x (syn_wex y
            (syn_wa (.classEq A (syn_copk (.cv x) (.cv y)))
              (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv
  let w : Var := freshVar proofSupport 0
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have p0000 := @g_elex A (syn_cxpk B C)
  have p0001 := @g_opkex (.cv x) (.cv y)
  have p0002 := @g_eleq1 A (syn_copk (.cv x) (.cv y)) (syn_cvv)
  have p0003 :=
    @g_mpbiri (.classEq A (syn_copk (.cv x) (.cv y))) (.classMem A (syn_cvv))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_adantr (.classEq A (syn_copk (.cv x) (.cv y))) (.classMem A (syn_cvv))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)) p0003
  have freeVariableCertificate0 : x ∉ ((Wff.classMem A (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((Wff.classMem A (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_y, or_false, not_false_eq_true]
  have p0005 :=
    @g_exlimivv
      (syn_wa (.classEq A (syn_copk (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      (.classMem A (syn_cvv)) x y freeVariableCertificate0 freeVariableCertificate1 p0004
  have p0006 := @g_eqeq1 (.cv w) A (syn_copk (.cv x) (.cv y))
  have p0007 :=
    @g_anbi1d (.classEq (.cv w) A) (.classEq (.cv w) (syn_copk (.cv x) (.cv y)))
      (.classEq A (syn_copk (.cv x) (.cv y)))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)) p0006
  have freeVariableCertificate2 : x ∉ ((Wff.classEq (.cv w) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_w, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((Wff.classEq (.cv w) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_w, dv_A_y, or_false, not_false_eq_true]
  have p0008 :=
    @g_n_2exbidv (.classEq (.cv w) A)
      (syn_wa (.classEq (.cv w) (syn_copk (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      (syn_wa (.classEq A (syn_copk (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      x y freeVariableCertificate2 freeVariableCertificate3 p0007
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xpk w x y B C
      (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B)))
      (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
      (by exact (show y ∉ (B).fv from (by exact dv_B_y)))
      (by exact (show w ∉ (C).fv from (by exact fresh_w_not_C)))
      (by exact (show x ∉ (C).fv from (by exact dv_C_x)))
      (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
      (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y))
      (show x ≠ y from (by exact dv_x_y))
  have freeVariableCertificate4 :
    w ∉
      ((syn_wex x (syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y)))
              (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_B,
      fresh_w_not_C, or_false, and_false, not_false_eq_true]
  have p0010 :=
    @g_elab2g
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_copk (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))))
      w A (syn_cxpk B C) (syn_cvv)
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) freeVariableCertificate4
      p0008 p0009
  have p0011 :=
    @g_pm5_21nii (.classMem A (syn_cxpk B C)) (.classMem A (syn_cvv))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))))
      p0000 p0005 p0010
  exact p0011

@[expose]
noncomputable def g_elxpk2 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cxpk B C))
        (syn_wrex x B (syn_wrex y C (.classEq A (syn_copk (.cv x) (.cv y)))))) :=
  by
  have p0000 :=
    @g_ancom (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))
      (.classEq A (syn_copk (.cv x) (.cv y)))
  have p0001 :=
    @g_n_2exbii
      (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))
        (.classEq A (syn_copk (.cv x) (.cv y))))
      (syn_wa (.classEq A (syn_copk (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      x y p0000
  have p0002 :=
    @g_r2ex (.classEq A (syn_copk (.cv x) (.cv y))) x y B C
      (by exact (show y ∉ (B).fv from (by exact dv_B_y)))
      (show x ≠ y from (by exact dv_x_y))
  have p0003 :=
    @g_elxpk x y A B C (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
      (by exact (show y ∉ (B).fv from (by exact dv_B_y)))
      (by exact (show x ∉ (C).fv from (by exact dv_C_x)))
      (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
      (show x ≠ y from (by exact dv_x_y))
  have p0004 :=
    @g_n_3bitr4ri
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C))
            (.classEq A (syn_copk (.cv x) (.cv y))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) C)))))
      (syn_wrex x B (syn_wrex y C (.classEq A (syn_copk (.cv x) (.cv y)))))
      (.classMem A (syn_cxpk B C)) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_xpkeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cxpk A C) (syn_cxpk B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have p0000 :=
    @g_rexeq (syn_wrex z C (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))) y A B
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have freeVariableCertificate1 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have p0001 :=
    @g_elxpk2 y z (.cv x) A C freeVariableCertificate0 freeVariableCertificate1
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0002 :=
    @g_elxpk2 y z (.cv x) B C freeVariableCertificate0 freeVariableCertificate1
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0003 :=
    @g_n_3bitr4g (.classEq A B)
      (syn_wrex y A (syn_wrex z C (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))))
      (syn_wrex y B (syn_wrex z C (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))))
      (.classMem (.cv x) (syn_cxpk A C)) (.classMem (.cv x) (syn_cxpk B C)) p0000 p0001
      p0002
  have freeVariableCertificate2 : x ∉ ((syn_cxpk A C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate3 : x ∉ ((syn_cxpk B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate4 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0004 :=
    @g_eqrdv (.classEq A B) x (syn_cxpk A C) (syn_cxpk B C) freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4 p0003
  exact p0004

@[expose]
noncomputable def g_xpkeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cxpk C A) (syn_cxpk C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have p0000 :=
    @g_rexeq (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) z A B
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
  have freeVariableCertificate0 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0001 :=
    @g_rexbidv (.classEq A B) (syn_wrex z A (.classEq (.cv x) (syn_copk (.cv y) (.cv z))))
      (syn_wrex z B (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))) y C
      freeVariableCertificate0 p0000
  have freeVariableCertificate1 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have p0002 :=
    @g_elxpk2 y z (.cv x) C A freeVariableCertificate1 freeVariableCertificate2
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0003 :=
    @g_elxpk2 y z (.cv x) C B freeVariableCertificate1 freeVariableCertificate2
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0004 :=
    @g_n_3bitr4g (.classEq A B)
      (syn_wrex y C (syn_wrex z A (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))))
      (syn_wrex y C (syn_wrex z B (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))))
      (.classMem (.cv x) (syn_cxpk C A)) (.classMem (.cv x) (syn_cxpk C B)) p0001 p0002
      p0003
  have freeVariableCertificate3 : x ∉ ((syn_cxpk C A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_C, fresh_x_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate4 : x ∉ ((syn_cxpk C B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_C, fresh_x_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate5 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0005 :=
    @g_eqrdv (.classEq A B) x (syn_cxpk C A) (syn_cxpk C B) freeVariableCertificate3
      freeVariableCertificate4 freeVariableCertificate5 p0004
  exact p0005

@[expose]
noncomputable def g_xpkeq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A B) (.classEq C D)) (.classEq (syn_cxpk A C) (syn_cxpk B D))) :=
  by
  have p0000 := @g_xpkeq1 A B C
  have p0001 := @g_xpkeq2 C D B
  have p0002 :=
    @g_sylan9eq (.classEq A B) (.classEq C D) (syn_cxpk A C) (syn_cxpk B C) (syn_cxpk B D)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_xpkeq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_xpkeq12i_1 : Nominal.NPrf (.classEq A B))
    (hyp_xpkeq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (syn_cxpk A C) (syn_cxpk B D)) :=
  by
  have p0000 := @g_xpkeq12 A B C D
  have p0001 :=
    @g_mp2an (.classEq A B) (.classEq C D) (.classEq (syn_cxpk A C) (syn_cxpk B D))
      hyp_xpkeq12i_1 hyp_xpkeq12i_2 p0000
  exact p0001

@[expose]
noncomputable def g_xpkeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_xpkeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cxpk C A) (syn_cxpk C B))) :=
  by
  have p0000 := @g_xpkeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cxpk C A) (syn_cxpk C B)) hyp_xpkeq1d_1 p0000
  exact p0001

@[expose]
noncomputable def g_elvvk (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cxpk (syn_cvv) (syn_cvv)))
        (syn_wex x (syn_wex y (.classEq A (syn_copk (.cv x) (.cv y)))))) :=
  by
  have p0000 :=
    @g_elxpk x y A (syn_cvv) (syn_cvv) (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by
        exact
          (show x ∉ ((syn_cvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((syn_cvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((syn_cvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((syn_cvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show x ≠ y from (by exact dv_x_y))
  have p0001 := @g_vex x
  have p0002 := @g_vex y
  have p0003 :=
    @g_pm3_2i (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_biantru (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
      (.classEq A (syn_copk (.cv x) (.cv y))) p0003
  have p0005 :=
    @g_n_2exbii (.classEq A (syn_copk (.cv x) (.cv y)))
      (syn_wa (.classEq A (syn_copk (.cv x) (.cv y)))
        (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))
      x y p0004
  have p0006 :=
    @g_bitr4i (.classMem A (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_copk (.cv x) (.cv y)))
            (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))))))
      (syn_wex x (syn_wex y (.classEq A (syn_copk (.cv x) (.cv y))))) p0000 p0005
  exact p0006


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart003`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_opkabssvvk (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (syn_wss (.cab x (syn_wex y
            (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph))))
        (syn_cxpk (syn_cvv) (syn_cvv))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var)
  let w : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have p0000 := @g_eqid (syn_copk (.cv y) (.cv z))
  have p0001 := @g_vex y
  have p0002 := @g_vex z
  have p0003 := @g_opkeq12 (.cv w) (.cv t) (.cv y) (.cv z)
  have p0004_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq w y) (.objEq t z))
        (.classEq (syn_copk (.cv w) (.cv t)) (syn_copk (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0004 :=
    @g_eqeq2d (syn_wa (.objEq w y) (.objEq t z)) (syn_copk (.cv w) (.cv t))
      (syn_copk (.cv y) (.cv z)) (syn_copk (.cv y) (.cv z)) p0004_e00_recanon
  have p0005_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv w) (.cv y)) (.classEq (.cv t) (.cv z)))
        (syn_wb (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv w) (.cv t)))
          (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv y) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have freeVariableCertificate0 : w ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_y, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_y, not_false_eq_true]
  have freeVariableCertificate2 : w ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_z, not_false_eq_true]
  have freeVariableCertificate3 : t ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_z, not_false_eq_true]
  have freeVariableCertificate4 :
    w ∉ ((Wff.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv y) (.cv z)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true]
  have freeVariableCertificate5 :
    t ∉ ((Wff.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv y) (.cv z)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_y, fresh_t_ne_z, or_false, not_false_eq_true]
  have p0005 :=
    @g_spc2ev (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv w) (.cv t)))
      (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv y) (.cv z))) w t (.cv y) (.cv z)
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      (show w ≠ t from (by exact fresh_w_ne_t)) p0001 p0002 p0005_e02_recanon
  have p0006 := Nominal.mp p0000 p0005
  have freeVariableCertificate6 : w ∉ ((syn_copk (.cv y) (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true]
  have freeVariableCertificate7 : t ∉ ((syn_copk (.cv y) (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_y, fresh_t_ne_z, or_false, not_false_eq_true]
  have p0007 :=
    @g_elvvk w t (syn_copk (.cv y) (.cv z)) freeVariableCertificate6
      freeVariableCertificate7 (show w ≠ t from (by exact fresh_w_ne_t))
  have p0008 :=
    @g_mpbir (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wex w (syn_wex t (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk (.cv w) (.cv t)))))
      p0006 p0007
  have p0009 := @g_eleq1 (.cv x) (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cvv) (syn_cvv))
  have p0010 :=
    @g_mpbiri (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
      (.classMem (.cv x) (syn_cxpk (syn_cvv) (syn_cvv)))
      (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cvv) (syn_cvv))) p0008 p0009
  have p0011 :=
    @g_adantr (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
      (.classMem (.cv x) (syn_cxpk (syn_cvv) (syn_cvv))) ph p0010
  have freeVariableCertificate8 :
    y ∉ ((Wff.classMem (.cv x) (syn_cxpk (syn_cvv) (syn_cvv)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, (Ne.symm dv_x_y), or_false,
      not_false_eq_true]
  have freeVariableCertificate9 :
    z ∉ ((Wff.classMem (.cv x) (syn_cxpk (syn_cvv) (syn_cvv)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, (Ne.symm dv_x_z), or_false,
      not_false_eq_true]
  have p0012 :=
    @g_exlimivv (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph)
      (.classMem (.cv x) (syn_cxpk (syn_cvv) (syn_cvv))) y z freeVariableCertificate8
      freeVariableCertificate9 p0011
  have freeVariableCertificate10 : x ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0013 :=
    @g_abssi
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph))) x
      (syn_cxpk (syn_cvv) (syn_cvv)) freeVariableCertificate10 p0012
  exact p0013

@[expose]
noncomputable def g_opkabssvvki (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (hyp_opkabssvvki_1 : Nominal.NPrf (.classEq A (.cab x (syn_wex y
              (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph)))))) :
    Nominal.NPrf (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv))) :=
  by
  have p0000 :=
    @g_opkabssvvk ph x y z (show x ≠ y from (by exact dv_x_y))
      (show x ≠ z from (by exact dv_x_z))
  have p0001 :=
    @g_eqsstri A
      (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph))))
      (syn_cxpk (syn_cvv) (syn_cvv)) hyp_opkabssvvki_1 p0000
  exact p0001

@[expose]
noncomputable def g_xpkssvvk (A : Class) (B : Class) :
    Nominal.NPrf (syn_wss (syn_cxpk A B) (syn_cxpk (syn_cvv) (syn_cvv))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xpk x y z A B
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @g_opkabssvvki (syn_wa (.classMem (.cv y) A) (.classMem (.cv z) B)) x y z
      (syn_cxpk A B) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) p0000
  exact p0001

@[expose]
noncomputable def g_ssrelk (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wb (syn_wss A B) (.all x (.all y
              (.imp (.classMem (syn_copk (.cv x) (.cv y)) A)
                (.classMem (syn_copk (.cv x) (.cv y)) B)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have freeVariableCertificate0 : z ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0000 :=
    @g_ssofss z A B (syn_cxpk (syn_cvv) (syn_cvv))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) freeVariableCertificate0
  have p0001 :=
    (Nominal.biimpRefl (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))
  have freeVariableCertificate1 : x ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_z, not_false_eq_true]
  have freeVariableCertificate2 : y ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_z, not_false_eq_true]
  have p0002 :=
    @g_elvvk x y (.cv z) freeVariableCertificate1 freeVariableCertificate2
      (show x ≠ y from (by exact dv_x_y))
  have p0003 :=
    @g_imbi1i (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))))
      (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)) p0002
  have freeVariableCertificate3 :
    x ∉ ((Wff.imp (.classMem (.cv z) A) (.classMem (.cv z) B))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_z, dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉ ((Wff.imp (.classMem (.cv z) A) (.classMem (.cv z) B))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_z, dv_A_y, dv_B_y, or_false, not_false_eq_true]
  have p0004 :=
    @g_n_19_23vv (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
      (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)) x y freeVariableCertificate3
      freeVariableCertificate4
  have p0005 :=
    @g_bitr4i
      (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv)))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.imp (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
            (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))))
      p0003 p0004
  have p0006 :=
    @g_albii
      (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv)))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
            (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))))
      z p0005
  have p0007 :=
    @g_alrot3
      (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      z x y
  have p0008 :=
    @g_bitri
      (.all z (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv)))
          (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.all z (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
              (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      (.all x (.all y (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
              (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      p0006 p0007
  have p0009 :=
    @g_bitri
      (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all z (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv)))
          (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.all x (.all y (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
              (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      p0001 p0008
  have p0010 := @g_opkex (.cv x) (.cv y)
  have p0011 := @g_eleq1 (.cv z) (syn_copk (.cv x) (.cv y)) A
  have p0012 := @g_eleq1 (.cv z) (syn_copk (.cv x) (.cv y)) B
  have p0013 :=
    @g_imbi12d (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.classMem (.cv z) A)
      (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (.cv z) B)
      (.classMem (syn_copk (.cv x) (.cv y)) B) p0011 p0012
  have freeVariableCertificate5 : z ∉ ((syn_copk (.cv x) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate6 :
    z ∉
      ((Wff.imp (.classMem (syn_copk (.cv x) (.cv y)) A)
          (.classMem (syn_copk (.cv x) (.cv y)) B))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_B, or_false,
      not_false_eq_true]
  have p0014 :=
    @g_ceqsalv (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))
      (.imp (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B))
      z (syn_copk (.cv x) (.cv y)) freeVariableCertificate5 freeVariableCertificate6 p0010
      p0013
  have p0015 :=
    @g_n_2albii
      (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
          (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.imp (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B))
      x y p0014
  have p0016 :=
    @g_bitri
      (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
              (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      (.all x (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y)) A)
            (.classMem (syn_copk (.cv x) (.cv y)) B))))
      p0009 p0015
  have p0017 :=
    @g_syl6bb (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv))) (syn_wss A B)
      (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y)) A)
            (.classMem (syn_copk (.cv x) (.cv y)) B))))
      p0000 p0016
  exact p0017

@[expose]
noncomputable def g_eqrelk (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv)))
          (syn_wss B (syn_cxpk (syn_cvv) (syn_cvv)))) (syn_wb (.classEq A B) (.all x (.all y
              (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A)
                (.classMem (syn_copk (.cv x) (.cv y)) B)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have freeVariableCertificate0 : z ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0000 :=
    @g_ssofeq z A B (syn_cxpk (syn_cvv) (syn_cvv))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) freeVariableCertificate0
  have p0001 :=
    (Nominal.biimpRefl (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))
  have freeVariableCertificate1 : x ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_z, not_false_eq_true]
  have freeVariableCertificate2 : y ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_z, not_false_eq_true]
  have p0002 :=
    @g_elvvk x y (.cv z) freeVariableCertificate1 freeVariableCertificate2
      (show x ≠ y from (by exact dv_x_y))
  have p0003 :=
    @g_imbi1i (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))))
      (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)) p0002
  have freeVariableCertificate3 :
    x ∉ ((syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_z, dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉ ((syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_z, dv_A_y, dv_B_y, or_false, not_false_eq_true]
  have p0004 :=
    @g_n_19_23vv (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
      (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)) x y freeVariableCertificate3
      freeVariableCertificate4
  have p0005 :=
    @g_bitr4i
      (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv)))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.imp (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
            (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))))
      p0003 p0004
  have p0006 :=
    @g_albii
      (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv)))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
            (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))))
      z p0005
  have p0007 :=
    @g_alrot3
      (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      z x y
  have p0008 :=
    @g_bitri
      (.all z (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv)))
          (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.all z (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
              (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      (.all x (.all y (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
              (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      p0006 p0007
  have p0009 := @g_opkex (.cv x) (.cv y)
  have p0010 := @g_eleq1 (.cv z) (syn_copk (.cv x) (.cv y)) A
  have p0011 := @g_eleq1 (.cv z) (syn_copk (.cv x) (.cv y)) B
  have p0012 :=
    @g_bibi12d (.classEq (.cv z) (syn_copk (.cv x) (.cv y))) (.classMem (.cv z) A)
      (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (.cv z) B)
      (.classMem (syn_copk (.cv x) (.cv y)) B) p0010 p0011
  have freeVariableCertificate5 : z ∉ ((syn_copk (.cv x) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate6 :
    z ∉
      ((syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A)
          (.classMem (syn_copk (.cv x) (.cv y)) B))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_B, or_false,
      not_false_eq_true]
  have p0013 :=
    @g_ceqsalv (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))
      (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B))
      z (syn_copk (.cv x) (.cv y)) freeVariableCertificate5 freeVariableCertificate6 p0009
      p0012
  have p0014 :=
    @g_n_2albii
      (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
          (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B))
      x y p0013
  have p0015 :=
    @g_n_3bitri
      (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all z (.imp (.classMem (.cv z) (syn_cxpk (syn_cvv) (syn_cvv)))
          (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.all x (.all y (.all z (.imp (.classEq (.cv z) (syn_copk (.cv x) (.cv y)))
              (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      (.all x (.all y (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A)
            (.classMem (syn_copk (.cv x) (.cv y)) B))))
      p0001 p0008 p0014
  have p0016 :=
    @g_syl6bb
      (syn_wa (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv)))
        (syn_wss B (syn_cxpk (syn_cvv) (syn_cvv))))
      (.classEq A B)
      (syn_wral z (syn_cxpk (syn_cvv) (syn_cvv))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A)
            (.classMem (syn_copk (.cv x) (.cv y)) B))))
      p0000 p0015
  exact p0016

@[expose]
noncomputable def g_eqrelkriiv (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y)
    (hyp_eqrelkriiv_1 : Nominal.NPrf (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv))))
    (hyp_eqrelkriiv_2 : Nominal.NPrf (syn_wss B (syn_cxpk (syn_cvv) (syn_cvv))))
    (hyp_eqrelkriiv_3 : Nominal.NPrf (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A)
          (.classMem (syn_copk (.cv x) (.cv y)) B))) :
    Nominal.NPrf (.classEq A B) :=
  by
  have p0000 :=
    @g_gen2
      (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A) (.classMem (syn_copk (.cv x) (.cv y)) B))
      x y hyp_eqrelkriiv_3
  have p0001 :=
    @g_eqrelk x y A B (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
      (by exact (show y ∉ (B).fv from (by exact dv_B_y)))
      (show x ≠ y from (by exact dv_x_y))
  have p0002 :=
    @g_mp2an (syn_wss A (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wss B (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wb (.classEq A B) (.all x (.all y (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A)
              (.classMem (syn_copk (.cv x) (.cv y)) B)))))
      hyp_eqrelkriiv_1 hyp_eqrelkriiv_2 p0001
  have p0003 :=
    @g_mpbir (.classEq A B)
      (.all x (.all y (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) A)
            (.classMem (syn_copk (.cv x) (.cv y)) B))))
      p0000 p0002
  exact p0003

@[expose]
noncomputable def g_cnvkeq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_ccnvk A) (syn_ccnvk B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have p0000 := @g_eleq2 A B (syn_copk (.cv z) (.cv y))
  have p0001 :=
    @g_anbi2d (.classEq A B) (.classMem (syn_copk (.cv z) (.cv y)) A)
      (.classMem (syn_copk (.cv z) (.cv y)) B)
      (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) p0000
  have freeVariableCertificate0 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : z ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have p0002 :=
    @g_n_2exbidv (.classEq A B)
      (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk (.cv z) (.cv y)) A))
      (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk (.cv z) (.cv y)) B))
      y z freeVariableCertificate0 freeVariableCertificate1 p0001
  have freeVariableCertificate2 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0003 :=
    @g_abbidv (.classEq A B)
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk (.cv z) (.cv y)) A))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk (.cv z) (.cv y)) B))))
      x freeVariableCertificate2 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnvk x y z A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnvk x y z B
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0006 :=
    @g_n_3eqtr4g (.classEq A B)
      (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv z) (.cv y)) A)))))
      (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv z) (.cv y)) B)))))
      (syn_ccnvk A) (syn_ccnvk B) p0003 p0004 p0005
  exact p0006


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart004`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ins2keq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cins2k A) (syn_cins2k B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  let u : Var := freshVar proofSupport 5
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_w_ne_u : w ≠ u :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have p0000 := @g_eleq2 A B (syn_copk (.cv w) (.cv u))
  have p0001 :=
    @g_n_3anbi3d (.classEq A B) (.classMem (syn_copk (.cv w) (.cv u)) A)
      (.classMem (syn_copk (.cv w) (.cv u)) B)
      (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
      (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) p0000
  have freeVariableCertificate0 : w ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_w_not_A, fresh_w_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate2 : u ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_u_not_A, fresh_u_not_B, or_false, not_false_eq_true]
  have p0002 :=
    @g_n_3exbidv (.classEq A B)
      (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
        (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) A))
      (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
        (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) B))
      w t u freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      p0001
  have p0003 :=
    @g_anbi2d (.classEq A B)
      (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
              (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
              (.classMem (syn_copk (.cv w) (.cv u)) A)))))
      (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
              (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
              (.classMem (syn_copk (.cv w) (.cv u)) B)))))
      (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) p0002
  have freeVariableCertificate3 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate4 : z ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have p0004 :=
    @g_n_2exbidv (.classEq A B)
      (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u
              (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                (.classMem (syn_copk (.cv w) (.cv u)) A))))))
      (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u
              (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                (.classMem (syn_copk (.cv w) (.cv u)) B))))))
      y z freeVariableCertificate3 freeVariableCertificate4 p0003
  have freeVariableCertificate5 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0005 :=
    @g_abbidv (.classEq A B)
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w
              (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                    (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                    (.classMem (syn_copk (.cv w) (.cv u)) A))))))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w
              (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                    (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                    (.classMem (syn_copk (.cv w) (.cv u)) B))))))))
      x freeVariableCertificate5 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins2k x y z u t w A
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ u from (by exact fresh_w_ne_u))
      (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y))
      (show w ≠ z from (by exact fresh_w_ne_z)) (show t ≠ u from (by exact fresh_t_ne_u))
      (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y))
      (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ x from (by exact fresh_u_ne_x))
      (show u ≠ y from (by exact fresh_u_ne_y)) (show u ≠ z from (by exact fresh_u_ne_z))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins2k x y z u t w B
      (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B)))
      (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B)))
      (by exact (show u ∉ (B).fv from (by exact fresh_u_not_B)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ u from (by exact fresh_w_ne_u))
      (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y))
      (show w ≠ z from (by exact fresh_w_ne_z)) (show t ≠ u from (by exact fresh_t_ne_u))
      (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y))
      (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ x from (by exact fresh_u_ne_x))
      (show u ≠ y from (by exact fresh_u_ne_y)) (show u ≠ z from (by exact fresh_u_ne_z))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0008 :=
    @g_n_3eqtr4g (.classEq A B)
      (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
              (syn_wex w (syn_wex t (syn_wex u
                    (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                      (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                      (.classMem (syn_copk (.cv w) (.cv u)) A)))))))))
      (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
              (syn_wex w (syn_wex t (syn_wex u
                    (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                      (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                      (.classMem (syn_copk (.cv w) (.cv u)) B)))))))))
      (syn_cins2k A) (syn_cins2k B) p0005 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_ins3keq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cins3k A) (syn_cins3k B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  let u : Var := freshVar proofSupport 5
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_w_ne_u : w ≠ u :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have p0000 := @g_eleq2 A B (syn_copk (.cv w) (.cv t))
  have p0001 :=
    @g_n_3anbi3d (.classEq A B) (.classMem (syn_copk (.cv w) (.cv t)) A)
      (.classMem (syn_copk (.cv w) (.cv t)) B)
      (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
      (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) p0000
  have freeVariableCertificate0 : w ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_w_not_A, fresh_w_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate2 : u ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_u_not_A, fresh_u_not_B, or_false, not_false_eq_true]
  have p0002 :=
    @g_n_3exbidv (.classEq A B)
      (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
        (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv t)) A))
      (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
        (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv t)) B))
      w t u freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      p0001
  have p0003 :=
    @g_anbi2d (.classEq A B)
      (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
              (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
              (.classMem (syn_copk (.cv w) (.cv t)) A)))))
      (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
              (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
              (.classMem (syn_copk (.cv w) (.cv t)) B)))))
      (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) p0002
  have freeVariableCertificate3 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate4 : z ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have p0004 :=
    @g_n_2exbidv (.classEq A B)
      (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u
              (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                (.classMem (syn_copk (.cv w) (.cv t)) A))))))
      (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t (syn_wex u
              (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                (.classMem (syn_copk (.cv w) (.cv t)) B))))))
      y z freeVariableCertificate3 freeVariableCertificate4 p0003
  have freeVariableCertificate5 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0005 :=
    @g_abbidv (.classEq A B)
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w
              (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                    (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                    (.classMem (syn_copk (.cv w) (.cv t)) A))))))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w
              (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                    (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                    (.classMem (syn_copk (.cv w) (.cv t)) B))))))))
      x freeVariableCertificate5 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins3k x y z u t w A
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ u from (by exact fresh_w_ne_u))
      (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y))
      (show w ≠ z from (by exact fresh_w_ne_z)) (show t ≠ u from (by exact fresh_t_ne_u))
      (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y))
      (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ x from (by exact fresh_u_ne_x))
      (show u ≠ y from (by exact fresh_u_ne_y)) (show u ≠ z from (by exact fresh_u_ne_z))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins3k x y z u t w B
      (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B)))
      (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B)))
      (by exact (show u ∉ (B).fv from (by exact fresh_u_not_B)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ u from (by exact fresh_w_ne_u))
      (show w ≠ x from (by exact fresh_w_ne_x)) (show w ≠ y from (by exact fresh_w_ne_y))
      (show w ≠ z from (by exact fresh_w_ne_z)) (show t ≠ u from (by exact fresh_t_ne_u))
      (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y))
      (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ x from (by exact fresh_u_ne_x))
      (show u ≠ y from (by exact fresh_u_ne_y)) (show u ≠ z from (by exact fresh_u_ne_z))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0008 :=
    @g_n_3eqtr4g (.classEq A B)
      (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
              (syn_wex w (syn_wex t (syn_wex u
                    (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                      (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                      (.classMem (syn_copk (.cv w) (.cv t)) A)))))))))
      (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
              (syn_wex w (syn_wex t (syn_wex u
                    (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                      (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                      (.classMem (syn_copk (.cv w) (.cv t)) B)))))))))
      (syn_cins3k A) (syn_cins3k B) p0005 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_imakeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cimak A C) (syn_cimak B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 := @g_eleq2 A B (syn_copk (.cv y) (.cv x))
  have freeVariableCertificate0 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0001 :=
    @g_rexbidv (.classEq A B) (.classMem (syn_copk (.cv y) (.cv x)) A)
      (.classMem (syn_copk (.cv y) (.cv x)) B) y C freeVariableCertificate0 p0000
  have freeVariableCertificate1 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0002 :=
    @g_abbidv (.classEq A B) (syn_wrex y C (.classMem (syn_copk (.cv y) (.cv x)) A))
      (syn_wrex y C (.classMem (syn_copk (.cv y) (.cv x)) B)) x freeVariableCertificate1
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_imak x y A C
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_imak x y B C
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B)
      (.cab x (syn_wrex y C (.classMem (syn_copk (.cv y) (.cv x)) A)))
      (.cab x (syn_wrex y C (.classMem (syn_copk (.cv y) (.cv x)) B))) (syn_cimak A C)
      (syn_cimak B C) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_imakeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cimak C A) (syn_cimak C B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    @g_rexeq (.classMem (syn_copk (.cv y) (.cv x)) C) y A B
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have freeVariableCertificate0 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) C))
      (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) C)) x freeVariableCertificate0
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_imak x y C A
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_imak x y C B
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B)
      (.cab x (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) C)))
      (.cab x (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) C))) (syn_cimak C A)
      (syn_cimak C B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_imakeq1i (A : Class) (B : Class) (C : Class)
    (hyp_imakeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cimak A C) (syn_cimak B C)) :=
  by
  have p0000 := @g_imakeq1 A B C
  have p0001 := Nominal.mp hyp_imakeq1i_1 p0000
  exact p0001

@[expose]
noncomputable def g_imakeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_imakeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cimak A C) (syn_cimak B C))) :=
  by
  have p0000 := @g_imakeq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cimak A C) (syn_cimak B C)) hyp_imakeq1d_1
      p0000
  exact p0001

@[expose]
noncomputable def g_imakeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_imakeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cimak C A) (syn_cimak C B))) :=
  by
  have p0000 := @g_imakeq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cimak C A) (syn_cimak C B)) hyp_imakeq1d_1
      p0000
  exact p0001

@[expose]
noncomputable def g_p6eq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cp6 A) (syn_cp6 B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have p0000 := @g_sseq2 A B (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv x))))
  have freeVariableCertificate0 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0001 :=
    @g_abbidv (.classEq A B) (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv x)))) A)
      (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv x)))) B) x
      freeVariableCertificate0 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_p6 x A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_p6 x B
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0004 :=
    @g_n_3eqtr4g (.classEq A B)
      (.cab x (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv x)))) A))
      (.cab x (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv x)))) B)) (syn_cp6 A)
      (syn_cp6 B) p0001 p0002 p0003
  exact p0004

@[expose]
noncomputable def g_sikeq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_csik A) (syn_csik B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have p0000 := @g_eleq2 A B (syn_copk (.cv w) (.cv t))
  have p0001 :=
    @g_n_3anbi3d (.classEq A B) (.classMem (syn_copk (.cv w) (.cv t)) A)
      (.classMem (syn_copk (.cv w) (.cv t)) B) (.classEq (.cv y) (syn_csn (.cv w)))
      (.classEq (.cv z) (syn_csn (.cv t))) p0000
  have freeVariableCertificate0 : w ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_w_not_A, fresh_w_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true]
  have p0002 :=
    @g_n_2exbidv (.classEq A B)
      (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t)))
        (.classMem (syn_copk (.cv w) (.cv t)) A))
      (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t)))
        (.classMem (syn_copk (.cv w) (.cv t)) B))
      w t freeVariableCertificate0 freeVariableCertificate1 p0001
  have p0003 :=
    @g_anbi2d (.classEq A B)
      (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w)))
            (.classEq (.cv z) (syn_csn (.cv t))) (.classMem (syn_copk (.cv w) (.cv t)) A))))
      (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w)))
            (.classEq (.cv z) (syn_csn (.cv t))) (.classMem (syn_copk (.cv w) (.cv t)) B))))
      (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) p0002
  have freeVariableCertificate2 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate3 : z ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have p0004 :=
    @g_n_2exbidv (.classEq A B)
      (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t
            (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t)))
              (.classMem (syn_copk (.cv w) (.cv t)) A)))))
      (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w (syn_wex t
            (syn_w3a (.classEq (.cv y) (syn_csn (.cv w))) (.classEq (.cv z) (syn_csn (.cv t)))
              (.classMem (syn_copk (.cv w) (.cv t)) B)))))
      y z freeVariableCertificate2 freeVariableCertificate3 p0003
  have freeVariableCertificate4 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0005 :=
    @g_abbidv (.classEq A B)
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w
              (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w)))
                  (.classEq (.cv z) (syn_csn (.cv t)))
                  (.classMem (syn_copk (.cv w) (.cv t)) A)))))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) (syn_wex w
              (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w)))
                  (.classEq (.cv z) (syn_csn (.cv t)))
                  (.classMem (syn_copk (.cv w) (.cv t)) B)))))))
      x freeVariableCertificate4 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sik x y z t w A
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ x from (by exact fresh_w_ne_x))
      (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z))
      (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y))
      (show t ≠ z from (by exact fresh_t_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0007 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sik x y z t w B
      (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B)))
      (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ x from (by exact fresh_w_ne_x))
      (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z))
      (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y))
      (show t ≠ z from (by exact fresh_t_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0008 :=
    @g_n_3eqtr4g (.classEq A B)
      (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
              (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w)))
                    (.classEq (.cv z) (syn_csn (.cv t)))
                    (.classMem (syn_copk (.cv w) (.cv t)) A))))))))
      (.cab x (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
              (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv y) (syn_csn (.cv w)))
                    (.classEq (.cv z) (syn_csn (.cv t)))
                    (.classMem (syn_copk (.cv w) (.cv t)) B))))))))
      (syn_csik A) (syn_csik B) p0005 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_opkelopkabg (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (A : Class) (B : Class) (C : Class) (V : Class) (W : Class)
    (_dv_A_y : y ∉ A.fv) (_dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv)
    (dv_ch_z : z ∉ ch.fv) (dv_ph_x : x ∉ ph.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_opkelopkabg_1 : Nominal.NPrf (.classEq A (.cab x (syn_wex y
              (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph))))))
    (hyp_opkelopkabg_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ph ps)))
    (hyp_opkelopkabg_3 : Nominal.NPrf (.imp (.classEq (.cv z) C) (syn_wb ps ch))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B V) (.classMem C W))
        (syn_wb (.classMem (syn_copk B C) A) ch)) :=
  by
  have p0000 := @g_opkex B C
  have p0001 := @g_eqeq1 (.cv x) (syn_copk B C) (syn_copk (.cv y) (.cv z))
  have p0002 := @g_eqcom (syn_copk B C) (syn_copk (.cv y) (.cv z))
  have p0003 :=
    @g_syl6bb (.classEq (.cv x) (syn_copk B C))
      (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
      (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
      (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) p0001 p0002
  have p0004 :=
    @g_anbi1d (.classEq (.cv x) (syn_copk B C))
      (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))
      (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph p0003
  have freeVariableCertificate0 : y ∉ ((Wff.classEq (.cv x) (syn_copk B C))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, dv_B_y, dv_C_y, (Ne.symm dv_x_y), or_false, not_false_eq_true]
  have freeVariableCertificate1 : z ∉ ((Wff.classEq (.cv x) (syn_copk B C))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, dv_B_z, dv_C_z, (Ne.symm dv_x_z), or_false, not_false_eq_true]
  have p0005 :=
    @g_n_2exbidv (.classEq (.cv x) (syn_copk B C))
      (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph)
      (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph) y z
      freeVariableCertificate0 freeVariableCertificate1 p0004
  have freeVariableCertificate2 : x ∉ ((syn_copk B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      dv_B_x, dv_C_x, or_false, not_false_eq_true]
  have freeVariableCertificate3 :
    x ∉
      ((syn_wex y (syn_wex z
            (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, dv_x_y, dv_x_z, dv_B_x, dv_C_x, dv_ph_x, or_false, and_false,
      not_false_eq_true]
  have p0006 :=
    @g_elab2
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph)))
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph)))
      x (syn_copk B C) A freeVariableCertificate2 freeVariableCertificate3 p0000 p0005
      hyp_opkelopkabg_1
  have p0007 := @g_elex B V
  have p0008 := @g_elex C W
  have p0009 := @g_vex y
  have p0010 := @g_vex z
  have p0011 := @g_opkthg (.cv y) (.cv z) B C (syn_cvv) (syn_cvv) (syn_cvv)
  have p0012 :=
    @g_mp3an12 (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv))
      (.classMem C (syn_cvv))
      (syn_wb (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C))
        (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)))
      p0009 p0010 p0011
  have p0013 :=
    @g_adantl (.classMem C (syn_cvv))
      (syn_wb (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C))
        (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)))
      (.classMem B (syn_cvv)) p0012
  have p0014 :=
    @g_anbi1d (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C))
      (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) ph p0013
  have p0015 := @g_anass (.classEq (.cv y) B) (.classEq (.cv z) C) ph
  have p0016 :=
    @g_syl6bb (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph)
      (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) ph)
      (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) ph)) p0014 p0015
  have freeVariableCertificate4 :
    z ∉ ((syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_B_z, dv_C_z, or_false, not_false_eq_true]
  have p0017 :=
    @g_exbidv (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph)
      (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) ph)) z
      freeVariableCertificate4 p0016
  have freeVariableCertificate5 : z ∉ ((Wff.classEq (.cv y) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      dv_B_z, (Ne.symm dv_y_z), or_false, not_false_eq_true]
  have p0018 :=
    @g_n_19_42v (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) ph) z
      freeVariableCertificate5
  have p0019 :=
    @g_syl6bb (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph))
      (syn_wex z (syn_wa (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) ph)))
      (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) ph))) p0017
      p0018
  have freeVariableCertificate6 :
    y ∉ ((syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_B_y, dv_C_y, or_false, not_false_eq_true]
  have p0020 :=
    @g_exbidv (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph))
      (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) ph))) y
      freeVariableCertificate6 p0019
  have p0021 :=
    @g_anbi2d (.classEq (.cv y) B) ph ps (.classEq (.cv z) C) hyp_opkelopkabg_2
  have p0022 :=
    @g_exbidv (.classEq (.cv y) B) (syn_wa (.classEq (.cv z) C) ph)
      (syn_wa (.classEq (.cv z) C) ps) z freeVariableCertificate5 p0021
  have freeVariableCertificate7 : y ∉ ((syn_wex z (syn_wa (.classEq (.cv z) C) ps))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, dv_y_z, dv_C_y, dv_ps_y, or_false, and_false,
      not_false_eq_true]
  have p0023 :=
    @g_ceqsexgv (syn_wex z (syn_wa (.classEq (.cv z) C) ph))
      (syn_wex z (syn_wa (.classEq (.cv z) C) ps)) y B (syn_cvv)
      (by exact (show y ∉ (B).fv from (by exact dv_B_y))) freeVariableCertificate7 p0022
  have p0024 :=
    @g_adantr (.classMem B (syn_cvv))
      (syn_wb (syn_wex y
          (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) ph))))
        (syn_wex z (syn_wa (.classEq (.cv z) C) ps)))
      (.classMem C (syn_cvv)) p0023
  have p0025 :=
    @g_ceqsexgv ps ch z C (syn_cvv) (by exact (show z ∉ (C).fv from (by exact dv_C_z)))
      (by exact (show z ∉ (ch).fv from (by exact dv_ch_z))) hyp_opkelopkabg_3
  have p0026 :=
    @g_adantl (.classMem C (syn_cvv))
      (syn_wb (syn_wex z (syn_wa (.classEq (.cv z) C) ps)) ch) (.classMem B (syn_cvv))
      p0025
  have p0027 :=
    @g_n_3bitrd (syn_wa (.classMem B (syn_cvv)) (.classMem C (syn_cvv)))
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph)))
      (syn_wex y (syn_wa (.classEq (.cv y) B) (syn_wex z (syn_wa (.classEq (.cv z) C) ph))))
      (syn_wex z (syn_wa (.classEq (.cv z) C) ps)) ch p0020 p0024 p0026
  have p0028 :=
    @g_syl2an (.classMem B V) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
      (syn_wb (syn_wex y
          (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph))) ch)
      (.classMem C W) p0007 p0008 p0027
  have p0029 :=
    @g_syl5bb (.classMem (syn_copk B C) A)
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) ph)))
      (syn_wa (.classMem B V) (.classMem C W)) ch p0006 p0028
  exact p0029


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart005`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_opkelopkab (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (A : Class) (B : Class) (C : Class) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_ch_z : z ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_opkelopkab_1 : Nominal.NPrf (.classEq A (.cab x (syn_wex y
              (syn_wex z (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) ph))))))
    (hyp_opkelopkab_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (syn_wb ph ps)))
    (hyp_opkelopkab_3 : Nominal.NPrf (.imp (.classEq (.cv z) C) (syn_wb ps ch)))
    (hyp_opkelopkab_4 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_opkelopkab_5 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf (syn_wb (.classMem (syn_copk B C) A) ch) :=
  by
  have p0000 :=
    @g_opkelopkabg ph ps ch x y z A B C (syn_cvv) (syn_cvv)
      (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by exact (show z ∉ (A).fv from (by exact dv_A_z)))
      (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
      (by exact (show y ∉ (B).fv from (by exact dv_B_y)))
      (by exact (show z ∉ (B).fv from (by exact dv_B_z)))
      (by exact (show x ∉ (C).fv from (by exact dv_C_x)))
      (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
      (by exact (show z ∉ (C).fv from (by exact dv_C_z)))
      (by exact (show z ∉ (ch).fv from (by exact dv_ch_z)))
      (by exact (show x ∉ (ph).fv from (by exact dv_ph_x)))
      (by exact (show y ∉ (ps).fv from (by exact dv_ps_y)))
      (show x ≠ y from (by exact dv_x_y)) (show x ≠ z from (by exact dv_x_z))
      (show y ≠ z from (by exact dv_y_z)) hyp_opkelopkab_1 hyp_opkelopkab_2
      hyp_opkelopkab_3
  have p0001 :=
    @g_mp2an (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
      (syn_wb (.classMem (syn_copk B C) A) ch) hyp_opkelopkab_4 hyp_opkelopkab_5 p0000
  exact p0001

@[expose]
noncomputable def g_opkelxpkg (A : Class) (B : Class) (C : Class) (D : Class) (V : Class)
    (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_cxpk C D))
          (syn_wa (.classMem A C) (.classMem B D)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_xpk z x y C D
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show z ∉ (D).fv from (by exact fresh_z_not_D)))
      (by exact (show x ∉ (D).fv from (by exact fresh_x_not_D)))
      (by exact (show y ∉ (D).fv from (by exact fresh_y_not_D)))
      (show z ≠ x from (by exact fresh_z_ne_x)) (show z ≠ y from (by exact fresh_z_ne_y))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 := @g_eleq1 (.cv x) A C
  have p0002 :=
    @g_anbi1d (.classEq (.cv x) A) (.classMem (.cv x) C) (.classMem A C)
      (.classMem (.cv y) D) p0001
  have p0003 := @g_eleq1 (.cv y) B D
  have p0004 :=
    @g_anbi2d (.classEq (.cv y) B) (.classMem (.cv y) D) (.classMem B D) (.classMem A C)
      p0003
  have freeVariableCertificate0 : x ∉ ((syn_cxpk C D)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_C, fresh_x_not_D, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((syn_cxpk C D)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_y_not_C, fresh_y_not_D, or_false, not_false_eq_true]
  have freeVariableCertificate2 : y ∉ ((syn_wa (.classMem A C) (.classMem B D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_y_not_A,
      fresh_y_not_C, fresh_y_not_B, fresh_y_not_D, or_false, not_false_eq_true]
  have freeVariableCertificate3 :
    z ∉ ((syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_not_C, fresh_z_ne_y, fresh_z_not_D, or_false,
      not_false_eq_true]
  have freeVariableCertificate4 :
    x ∉ ((syn_wa (.classMem A C) (.classMem (.cv y) D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_not_A, fresh_x_not_C, fresh_x_ne_y, fresh_x_not_D, or_false,
      not_false_eq_true]
  have p0005 :=
    @g_opkelopkabg (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D))
      (syn_wa (.classMem A C) (.classMem (.cv y) D))
      (syn_wa (.classMem A C) (.classMem B D)) z x y (syn_cxpk C D) A B V W
      freeVariableCertificate0 freeVariableCertificate1
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4
      (show z ≠ x from (by exact fresh_z_ne_x)) (show z ≠ y from (by exact fresh_z_ne_y))
      (show x ≠ y from (by exact fresh_x_ne_y)) p0000 p0002 p0004
  exact p0005

@[expose]
noncomputable def g_opkelxpk (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_opkelxpk_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opkelxpk_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk A B) (syn_cxpk C D))
        (syn_wa (.classMem A C) (.classMem B D))) :=
  by
  have p0000 := @g_opkelxpkg A B C D (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_copk A B) (syn_cxpk C D))
        (syn_wa (.classMem A C) (.classMem B D)))
      hyp_opkelxpk_1 hyp_opkelxpk_2 p0000
  exact p0001

@[expose]
noncomputable def g_opkelcnvkg (A : Class) (B : Class) (C : Class) (V : Class)
    (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_ccnvk C)) (.classMem (syn_copk B A) C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnvk z x y C
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (show z ≠ x from (by exact fresh_z_ne_x)) (show z ≠ y from (by exact fresh_z_ne_y))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 := @g_opkeq2 (.cv x) A (.cv y)
  have p0002 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_copk (.cv y) (.cv x)) (syn_copk (.cv y) A) C p0001
  have p0003 := @g_opkeq1 (.cv y) B A
  have p0004 := @g_eleq1d (.classEq (.cv y) B) (syn_copk (.cv y) A) (syn_copk B A) C p0003
  have freeVariableCertificate0 : y ∉ ((Wff.classMem (syn_copk B A) C)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_y_not_B, fresh_y_not_A, fresh_y_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate1 : z ∉ ((Wff.classMem (syn_copk (.cv y) (.cv x)) C)).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_y, fresh_z_ne_x, fresh_z_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Wff.classMem (syn_copk (.cv y) A) C)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_y, fresh_x_not_A, fresh_x_not_C, or_false, not_false_eq_true]
  have p0005 :=
    @g_opkelopkabg (.classMem (syn_copk (.cv y) (.cv x)) C)
      (.classMem (syn_copk (.cv y) A) C) (.classMem (syn_copk B A) C) z x y (syn_ccnvk C)
      A B V W
      (by
        exact
          (show x ∉ ((syn_ccnvk C)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
              exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))))
      (by
        exact
          (show y ∉ ((syn_ccnvk C)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
              exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2
      (show z ≠ x from (by exact fresh_z_ne_x)) (show z ≠ y from (by exact fresh_z_ne_y))
      (show x ≠ y from (by exact fresh_x_ne_y)) p0000 p0002 p0004
  exact p0005

@[expose]
noncomputable def g_opkelcnvk (A : Class) (B : Class) (C : Class)
    (hyp_opkelcnvk_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opkelcnvk_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk A B) (syn_ccnvk C)) (.classMem (syn_copk B A) C)) :=
  by
  have p0000 := @g_opkelcnvkg A B C (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_copk A B) (syn_ccnvk C)) (.classMem (syn_copk B A) C))
      hyp_opkelcnvk_1 hyp_opkelcnvk_2 p0000
  exact p0001

@[expose]
noncomputable def g_opkelins2kg (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_cins2k C)) (syn_wex x (syn_wex y (syn_wex z
                (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
                  (.classEq B (syn_copk (.cv y) (.cv z)))
                  (.classMem (syn_copk (.cv x) (.cv z)) C))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv ∪ B.fv ∪
          C.fv ∪
        V.fv ∪
      W.fv
  let w : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_u : z ≠ u := Ne.symm fresh_u_ne_z
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_t_not_C : t ∉ C.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_ne_u : w ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_w : t ≠ w := Ne.symm fresh_w_ne_t
  have fresh_u_ne_t : u ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_u : t ≠ u := Ne.symm fresh_u_ne_t
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins2k t w u z y x C
      (by exact (show x ∉ (C).fv from (by exact dv_C_x)))
      (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
      (by exact (show z ∉ (C).fv from (by exact dv_C_z)))
      (by exact (show t ∉ (C).fv from (by exact fresh_t_not_C)))
      (by exact (show w ∉ (C).fv from (by exact fresh_w_not_C)))
      (by exact (show u ∉ (C).fv from (by exact fresh_u_not_C)))
      (show x ≠ y from (by exact dv_x_y)) (show x ≠ z from (by exact dv_x_z))
      (show x ≠ t from (by exact fresh_x_ne_t)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show x ≠ u from (by exact fresh_x_ne_u)) (show y ≠ z from (by exact dv_y_z))
      (show y ≠ t from (by exact fresh_y_ne_t)) (show y ≠ w from (by exact fresh_y_ne_w))
      (show y ≠ u from (by exact fresh_y_ne_u)) (show z ≠ t from (by exact fresh_z_ne_t))
      (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ u from (by exact fresh_z_ne_u))
      (show t ≠ w from (by exact fresh_t_ne_w)) (show t ≠ u from (by exact fresh_t_ne_u))
      (show w ≠ u from (by exact fresh_w_ne_u))
  have p0001 := @g_eqeq1 (.cv w) A (syn_csn (syn_csn (.cv x)))
  have p0002 :=
    @g_n_3anbi1d (.classEq (.cv w) A) (.classEq (.cv w) (syn_csn (syn_csn (.cv x))))
      (.classEq A (syn_csn (syn_csn (.cv x))))
      (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
      (.classMem (syn_copk (.cv x) (.cv z)) C) p0001
  have freeVariableCertificate0 : x ∉ ((Wff.classEq (.cv w) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_w, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((Wff.classEq (.cv w) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_w, dv_A_y, or_false, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((Wff.classEq (.cv w) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_w, dv_A_z, or_false, not_false_eq_true]
  have p0003 :=
    @g_n_3exbidv (.classEq (.cv w) A)
      (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x))))
        (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) C))
      (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
        (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) C))
      x y z freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      p0002
  have p0004 := @g_eqeq1 (.cv u) B (syn_copk (.cv y) (.cv z))
  have p0005 :=
    @g_n_3anbi2d (.classEq (.cv u) B) (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
      (.classEq B (syn_copk (.cv y) (.cv z))) (.classEq A (syn_csn (syn_csn (.cv x))))
      (.classMem (syn_copk (.cv x) (.cv z)) C) p0004
  have freeVariableCertificate3 : x ∉ ((Wff.classEq (.cv u) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_u, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate4 : y ∉ ((Wff.classEq (.cv u) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_u, dv_B_y, or_false, not_false_eq_true]
  have freeVariableCertificate5 : z ∉ ((Wff.classEq (.cv u) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_u, dv_B_z, or_false, not_false_eq_true]
  have p0006 :=
    @g_n_3exbidv (.classEq (.cv u) B)
      (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
        (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) C))
      (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
        (.classEq B (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv z)) C))
      x y z freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      p0005
  have freeVariableCertificate6 :
    u ∉
      ((syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
                (.classEq B (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv z)) C)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_z, fresh_u_not_C,
      fresh_u_not_A, fresh_u_not_B, fresh_u_ne_y, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate7 :
    t ∉
      ((syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x))))
                (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv z)) C)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_z, fresh_t_not_C,
      fresh_t_ne_w, fresh_t_ne_u, fresh_t_ne_y, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate8 :
    w ∉
      ((syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
                (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv z)) C)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_z, fresh_w_not_C,
      fresh_w_not_A, fresh_w_ne_u, fresh_w_ne_y, or_false, and_false, not_false_eq_true]
  have p0007 :=
    @g_opkelopkabg
      (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x))))
              (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv z)) C)))))
      (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
              (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv z)) C)))))
      (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
              (.classEq B (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv z)) C)))))
      t w u (syn_cins2k C) A B V W
      (by
        exact
          (show w ∉ ((syn_cins2k C)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
              exact (show w ∉ (C).fv from (by exact fresh_w_not_C)))))
      (by
        exact
          (show u ∉ ((syn_cins2k C)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
              exact (show u ∉ (C).fv from (by exact fresh_u_not_C)))))
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A)))
      (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B)))
      (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B)))
      (by exact (show u ∉ (B).fv from (by exact fresh_u_not_B))) freeVariableCertificate6
      freeVariableCertificate7 freeVariableCertificate8
      (show t ≠ w from (by exact fresh_t_ne_w)) (show t ≠ u from (by exact fresh_t_ne_u))
      (show w ≠ u from (by exact fresh_w_ne_u)) p0000 p0003 p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart006`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_opkelins3kg (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_cins3k C)) (syn_wex x (syn_wex y (syn_wex z
                (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
                  (.classEq B (syn_copk (.cv y) (.cv z)))
                  (.classMem (syn_copk (.cv x) (.cv y)) C))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv ∪ B.fv ∪
          C.fv ∪
        V.fv ∪
      W.fv
  let w : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_u : z ≠ u := Ne.symm fresh_u_ne_z
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_u_not_C : u ∉ C.fv := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))))))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
                    (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))))
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_t_not_C : t ∉ C.fv := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_w_ne_u : w ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_w : t ≠ w := Ne.symm fresh_w_ne_t
  have fresh_u_ne_t : u ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_u : t ≠ u := Ne.symm fresh_u_ne_t
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins3k t w u z y x C
      (by exact (show x ∉ (C).fv from (by exact dv_C_x)))
      (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
      (by exact (show z ∉ (C).fv from (by exact dv_C_z)))
      (by exact (show t ∉ (C).fv from (by exact fresh_t_not_C)))
      (by exact (show w ∉ (C).fv from (by exact fresh_w_not_C)))
      (by exact (show u ∉ (C).fv from (by exact fresh_u_not_C)))
      (show x ≠ y from (by exact dv_x_y)) (show x ≠ z from (by exact dv_x_z))
      (show x ≠ t from (by exact fresh_x_ne_t)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show x ≠ u from (by exact fresh_x_ne_u)) (show y ≠ z from (by exact dv_y_z))
      (show y ≠ t from (by exact fresh_y_ne_t)) (show y ≠ w from (by exact fresh_y_ne_w))
      (show y ≠ u from (by exact fresh_y_ne_u)) (show z ≠ t from (by exact fresh_z_ne_t))
      (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ u from (by exact fresh_z_ne_u))
      (show t ≠ w from (by exact fresh_t_ne_w)) (show t ≠ u from (by exact fresh_t_ne_u))
      (show w ≠ u from (by exact fresh_w_ne_u))
  have p0001 := @g_eqeq1 (.cv w) A (syn_csn (syn_csn (.cv x)))
  have p0002 :=
    @g_n_3anbi1d (.classEq (.cv w) A) (.classEq (.cv w) (syn_csn (syn_csn (.cv x))))
      (.classEq A (syn_csn (syn_csn (.cv x))))
      (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
      (.classMem (syn_copk (.cv x) (.cv y)) C) p0001
  have freeVariableCertificate0 : x ∉ ((Wff.classEq (.cv w) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_w, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((Wff.classEq (.cv w) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_w, dv_A_y, or_false, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((Wff.classEq (.cv w) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_w, dv_A_z, or_false, not_false_eq_true]
  have p0003 :=
    @g_n_3exbidv (.classEq (.cv w) A)
      (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x))))
        (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))
      (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
        (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))
      x y z freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      p0002
  have p0004 := @g_eqeq1 (.cv u) B (syn_copk (.cv y) (.cv z))
  have p0005 :=
    @g_n_3anbi2d (.classEq (.cv u) B) (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
      (.classEq B (syn_copk (.cv y) (.cv z))) (.classEq A (syn_csn (syn_csn (.cv x))))
      (.classMem (syn_copk (.cv x) (.cv y)) C) p0004
  have freeVariableCertificate3 : x ∉ ((Wff.classEq (.cv u) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_u, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate4 : y ∉ ((Wff.classEq (.cv u) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_u, dv_B_y, or_false, not_false_eq_true]
  have freeVariableCertificate5 : z ∉ ((Wff.classEq (.cv u) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_u, dv_B_z, or_false, not_false_eq_true]
  have p0006 :=
    @g_n_3exbidv (.classEq (.cv u) B)
      (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
        (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))
      (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
        (.classEq B (syn_copk (.cv y) (.cv z))) (.classMem (syn_copk (.cv x) (.cv y)) C))
      x y z freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      p0005
  have freeVariableCertificate6 :
    u ∉
      ((syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
                (.classEq B (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv y)) C)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, fresh_u_not_C,
      fresh_u_not_A, fresh_u_not_B, fresh_u_ne_z, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate7 :
    t ∉
      ((syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x))))
                (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv y)) C)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, fresh_t_not_C,
      fresh_t_ne_w, fresh_t_ne_u, fresh_t_ne_z, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate8 :
    w ∉
      ((syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
                (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv y)) C)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_C,
      fresh_w_not_A, fresh_w_ne_u, fresh_w_ne_z, or_false, and_false, not_false_eq_true]
  have p0007 :=
    @g_opkelopkabg
      (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq (.cv w) (syn_csn (syn_csn (.cv x))))
              (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv y)) C)))))
      (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
              (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv y)) C)))))
      (syn_wex x (syn_wex y (syn_wex z (syn_w3a (.classEq A (syn_csn (syn_csn (.cv x))))
              (.classEq B (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv y)) C)))))
      t w u (syn_cins3k C) A B V W
      (by
        exact
          (show w ∉ ((syn_cins3k C)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
              exact (show w ∉ (C).fv from (by exact fresh_w_not_C)))))
      (by
        exact
          (show u ∉ ((syn_cins3k C)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
              exact (show u ∉ (C).fv from (by exact fresh_u_not_C)))))
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A)))
      (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B)))
      (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B)))
      (by exact (show u ∉ (B).fv from (by exact fresh_u_not_B))) freeVariableCertificate6
      freeVariableCertificate7 freeVariableCertificate8
      (show t ≠ w from (by exact fresh_t_ne_w)) (show t ≠ u from (by exact fresh_t_ne_u))
      (show w ≠ u from (by exact fresh_w_ne_u)) p0000 p0003 p0006
  exact p0007

@[expose]
noncomputable def g_otkelins2kg (A : Class) (B : Class) (C : Class) (D : Class)
    (T : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C T))
        (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins2k D))
          (.classMem (syn_copk A C) D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ T.fv ∪ V.fv ∪ W.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y_not_T : y ∉ T.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_z_not_C : z ∉ C.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_not_D : z ∉ D.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_z_not_T : z ∉ T.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have p0000 := @g_snex (syn_csn A)
  have p0001 := @g_opkex B C
  have freeVariableCertificate0 : x ∉ ((syn_csn (syn_csn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_A,
      not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((syn_csn (syn_csn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_y_not_A,
      not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((syn_csn (syn_csn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_z_not_A,
      not_false_eq_true]
  have freeVariableCertificate3 : x ∉ ((syn_copk B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate4 : y ∉ ((syn_copk B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_y_not_B, fresh_y_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate5 : z ∉ ((syn_copk B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_z_not_B, fresh_z_not_C, or_false, not_false_eq_true]
  have p0002 :=
    @g_opkelins2kg x y z (syn_csn (syn_csn A)) (syn_copk B C) D (syn_cvv) (syn_cvv)
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      (by exact (show x ∉ (D).fv from (by exact fresh_x_not_D)))
      (by exact (show y ∉ (D).fv from (by exact fresh_y_not_D)))
      (by exact (show z ∉ (D).fv from (by exact fresh_z_not_D)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0003 :=
    @g_mp2an (.classMem (syn_csn (syn_csn A)) (syn_cvv))
      (.classMem (syn_copk B C) (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins2k D))
        (syn_wex x (syn_wex y (syn_wex z
              (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
                (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv z)) D))))))
      p0000 p0001 p0002
  have p0004 :=
    @g_n_3anass (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
      (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
      (.classMem (syn_copk (.cv x) (.cv z)) D)
  have p0005 := @g_eqcom (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x)))
  have p0006 := @g_snex (.cv x)
  have p0007 := @g_sneqb (syn_csn (.cv x)) (syn_csn A) p0006
  have p0008 := @g_vex x
  have p0009 := @g_sneqb (.cv x) A p0008
  have p0010 :=
    @g_bitri (.classEq (syn_csn (syn_csn (.cv x))) (syn_csn (syn_csn A)))
      (.classEq (syn_csn (.cv x)) (syn_csn A)) (.classEq (.cv x) A) p0007 p0009
  have p0011 :=
    @g_bitri (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
      (.classEq (syn_csn (syn_csn (.cv x))) (syn_csn (syn_csn A))) (.classEq (.cv x) A)
      p0005 p0010
  have p0012 :=
    @g_anbi1i (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
      (.classEq (.cv x) A)
      (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk (.cv x) (.cv z)) D))
      p0011
  have p0013 :=
    @g_bitri
      (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
        (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk (.cv x) (.cv z)) D))
      (syn_wa (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
        (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
          (.classMem (syn_copk (.cv x) (.cv z)) D)))
      (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
          (.classMem (syn_copk (.cv x) (.cv z)) D)))
      p0004 p0012
  have p0014 :=
    @g_n_2exbii
      (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
        (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk (.cv x) (.cv z)) D))
      (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
          (.classMem (syn_copk (.cv x) (.cv z)) D)))
      y z p0013
  have freeVariableCertificate6 : y ∉ ((Wff.classEq (.cv x) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate7 : z ∉ ((Wff.classEq (.cv x) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_not_A, or_false, not_false_eq_true]
  have p0015 :=
    @g_n_19_42vv (.classEq (.cv x) A)
      (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk (.cv x) (.cv z)) D))
      y z freeVariableCertificate6 freeVariableCertificate7
  have p0016 :=
    @g_bitri
      (syn_wex y (syn_wex z
          (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
            (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk (.cv x) (.cv z)) D))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) A)
            (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv z)) D)))))
      (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z
            (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv z)) D)))))
      p0014 p0015
  have p0017 :=
    @g_exbii
      (syn_wex y (syn_wex z
          (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
            (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk (.cv x) (.cv z)) D))))
      (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z
            (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv z)) D)))))
      x p0016
  have p0018 :=
    @g_bitri (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins2k D))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
              (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv z)) D)))))
      (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z
              (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv z)) D))))))
      p0003 p0017
  have p0019 := @g_opkeq1 (.cv x) A (.cv z)
  have p0020 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_copk (.cv x) (.cv z)) (syn_copk A (.cv z)) D p0019
  have p0021 :=
    @g_anbi2d (.classEq (.cv x) A) (.classMem (syn_copk (.cv x) (.cv z)) D)
      (.classMem (syn_copk A (.cv z)) D)
      (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) p0020
  have p0022 :=
    @g_n_2exbidv (.classEq (.cv x) A)
      (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk (.cv x) (.cv z)) D))
      (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk A (.cv z)) D))
      y z freeVariableCertificate6 freeVariableCertificate7 p0021
  have freeVariableCertificate8 :
    x ∉
      ((syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk A (.cv z)) D))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, fresh_x_not_B, fresh_x_not_C, fresh_x_ne_y, fresh_x_ne_z,
      fresh_x_not_A, fresh_x_not_D, or_false, and_false, not_false_eq_true]
  have p0023 :=
    @g_ceqsexgv
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk (.cv x) (.cv z)) D))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk A (.cv z)) D))))
      x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate8 p0022
  have p0024 :=
    @g_n_3ad2ant1 (.classMem A V) (.classMem B W)
      (syn_wb (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z
                (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
                  (.classMem (syn_copk (.cv x) (.cv z)) D)))))) (syn_wex y (syn_wex z
            (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk A (.cv z)) D)))))
      (.classMem C T) p0023
  have p0025 := @g_eqcom (syn_copk B C) (syn_copk (.cv y) (.cv z))
  have p0026 := @g_vex y
  have p0027 := @g_vex z
  have p0028 := @g_opkthg (.cv y) (.cv z) B C T (syn_cvv) (syn_cvv)
  have p0029 :=
    @g_mp3an12 (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv)) (.classMem C T)
      (syn_wb (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C))
        (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)))
      p0026 p0027 p0028
  have p0030 :=
    @g_syl5bb (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
      (.classEq (syn_copk (.cv y) (.cv z)) (syn_copk B C)) (.classMem C T)
      (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C)) p0025 p0029
  have p0031 :=
    @g_anbi1d (.classMem C T) (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
      (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C))
      (.classMem (syn_copk A (.cv z)) D) p0030
  have freeVariableCertificate9 : y ∉ ((Wff.classMem C T)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
      fresh_y_not_C, fresh_y_not_T, or_false, not_false_eq_true]
  have freeVariableCertificate10 : z ∉ ((Wff.classMem C T)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
      fresh_z_not_C, fresh_z_not_T, or_false, not_false_eq_true]
  have p0032 :=
    @g_n_2exbidv (.classMem C T)
      (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk A (.cv z)) D))
      (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C))
        (.classMem (syn_copk A (.cv z)) D))
      y z freeVariableCertificate9 freeVariableCertificate10 p0031
  have p0033 :=
    @g_anass (.classEq (.cv y) B) (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)
  have p0034 :=
    @g_exbii
      (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C))
        (.classMem (syn_copk A (.cv z)) D))
      (syn_wa (.classEq (.cv y) B)
        (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))
      z p0033
  have freeVariableCertificate11 : z ∉ ((Wff.classEq (.cv y) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_y, fresh_z_not_B, or_false, not_false_eq_true]
  have p0035 :=
    @g_n_19_42v (.classEq (.cv y) B)
      (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)) z
      freeVariableCertificate11
  have p0036 :=
    @g_bitri
      (syn_wex z (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C))
          (.classMem (syn_copk A (.cv z)) D)))
      (syn_wex z (syn_wa (.classEq (.cv y) B)
          (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))))
      (syn_wa (.classEq (.cv y) B)
        (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))))
      p0034 p0035
  have p0037 :=
    @g_exbii
      (syn_wex z (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C))
          (.classMem (syn_copk A (.cv z)) D)))
      (syn_wa (.classEq (.cv y) B)
        (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))))
      y p0036
  have p0038 :=
    @g_syl6bb (.classMem C T)
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk A (.cv z)) D))))
      (syn_wex y (syn_wex z (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C))
            (.classMem (syn_copk A (.cv z)) D))))
      (syn_wex y (syn_wa (.classEq (.cv y) B)
          (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))))
      p0032 p0037
  have p0039 :=
    @g_adantl (.classMem C T)
      (syn_wb (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk A (.cv z)) D)))) (syn_wex y (syn_wa (.classEq (.cv y) B)
            (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))))))
      (.classMem B W) p0038
  have p0040 :=
    @g_biidd (.classEq (.cv y) B)
      (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))
  have freeVariableCertificate12 :
    y ∉
      ((syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_C, fresh_y_not_A,
      fresh_y_not_D, or_false, and_false, not_false_eq_true]
  have p0041 :=
    @g_ceqsexgv
      (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))
      (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D))) y B W
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) freeVariableCertificate12
      p0040
  have p0042 := @g_opkeq2 (.cv z) C A
  have p0043 := @g_eleq1d (.classEq (.cv z) C) (syn_copk A (.cv z)) (syn_copk A C) D p0042
  have freeVariableCertificate13 : z ∉ ((Wff.classMem (syn_copk A C) D)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_C, fresh_z_not_D, or_false, not_false_eq_true]
  have p0044 :=
    @g_ceqsexgv (.classMem (syn_copk A (.cv z)) D) (.classMem (syn_copk A C) D) z C T
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C))) freeVariableCertificate13
      p0043
  have p0045 :=
    @g_sylan9bb (.classMem B W)
      (syn_wex y (syn_wa (.classEq (.cv y) B)
          (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))))
      (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))
      (.classMem C T) (.classMem (syn_copk A C) D) p0041 p0044
  have p0046 :=
    @g_bitrd (syn_wa (.classMem B W) (.classMem C T))
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk A (.cv z)) D))))
      (syn_wex y (syn_wa (.classEq (.cv y) B)
          (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv z)) D)))))
      (.classMem (syn_copk A C) D) p0039 p0045
  have p0047 :=
    @g_n_3adant1 (.classMem B W) (.classMem C T)
      (syn_wb (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk A (.cv z)) D)))) (.classMem (syn_copk A C) D))
      (.classMem A V) p0046
  have p0048 :=
    @g_bitrd (syn_w3a (.classMem A V) (.classMem B W) (.classMem C T))
      (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z
              (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv z)) D))))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk A (.cv z)) D))))
      (.classMem (syn_copk A C) D) p0024 p0047
  have p0049 :=
    @g_syl5bb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins2k D))
      (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z
              (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv z)) D))))))
      (syn_w3a (.classMem A V) (.classMem B W) (.classMem C T))
      (.classMem (syn_copk A C) D) p0018 p0048
  exact p0049


end NFChoice.DirectNominalPrf.WPPReplay

end
