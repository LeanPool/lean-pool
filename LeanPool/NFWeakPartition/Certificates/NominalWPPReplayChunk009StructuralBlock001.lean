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

/-- Checked nominal proof certificate identified upstream as `g_elpw1101c`. -/
@[expose]
noncomputable def gElpw1101c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
        (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                          (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))))) :=
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
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have p0000 :=
    @gElpw1 y A
      (synCpw1 (synCpw1 (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate0
  have p0001 :=
    (Nominal.biimpRefl (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
        (.classEq A (synCsn (.cv y)))))
  have freeVariableCertificate1 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0002 := @gElpw191c x (.cv y) freeVariableCertificate1
  have p0003 :=
    @gAnbi1i
      (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn
                    (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
      (.classEq A (synCsn (.cv y))) p0002
  have freeVariableCertificate2 : x ∉ ((Wff.classEq A (synCsn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      dv_A_x, fresh_x_ne_y, or_false, not_false_eq_true]
  have p0004 :=
    @gN1941v
      (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
      (.classEq A (synCsn (.cv y))) x freeVariableCertificate2
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWa (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
          (.classEq A (synCsn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
          (.classEq A (synCsn (.cv y)))))
      y p0005
  have p0007 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
          (.classEq A (synCsn (.cv y)))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
            (.classEq A (synCsn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                  (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
        (.classEq A (synCsn (.cv y))))
      y x
  have p0009 :=
    @gSnex
      (synCsn (synCsn
          (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))
  have p0010 :=
    @gSneq (.cv y)
      (synCsn (synCsn (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
  have p0011 :=
    @gEqeq2d
      (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
      (synCsn (.cv y))
      (synCsn (synCsn (synCsn (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
      A p0010
  have freeVariableCertificate3 :
    y ∉
      ((synCsn (synCsn (synCsn (synCsn (synCsn
                  (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉
      ((Wff.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                        (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0012 :=
    @gCeqsexv (.classEq A (synCsn (.cv y)))
      (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                    (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
      y
      (synCsn (synCsn (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
      freeVariableCertificate3 freeVariableCertificate4 p0009 p0011
  have p0013 :=
    @gExbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
          (.classEq A (synCsn (.cv y)))))
      (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                    (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
      x p0012
  have p0014 :=
    @gBitri
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))))
      p0008 p0013
  have p0015 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))))
      p0007 p0014
  have p0016 :=
    @gBitri
      (.classMem A (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))))
      p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_elpw1111c`. -/
@[expose]
noncomputable def gElpw1111c (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (synWb (.classMem A (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))) (synWex x
          (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                            (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))))) :=
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
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have p0000 :=
    @gElpw1 y A
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate0
  have p0001 :=
    (Nominal.biimpRefl (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
        (.classEq A (synCsn (.cv y)))))
  have freeVariableCertificate1 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0002 := @gElpw1101c x (.cv y) freeVariableCertificate1
  have p0003 :=
    @gAnbi1i
      (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
      (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))))
      (.classEq A (synCsn (.cv y))) p0002
  have freeVariableCertificate2 : x ∉ ((Wff.classEq A (synCsn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      dv_A_x, fresh_x_ne_y, or_false, not_false_eq_true]
  have p0004 :=
    @gN1941v
      (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                    (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
      (.classEq A (synCsn (.cv y))) x freeVariableCertificate2
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWa (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                        (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                        (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
          (.classEq A (synCsn (.cv y)))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                        (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
          (.classEq A (synCsn (.cv y)))))
      y p0005
  have p0007 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
          (.classEq A (synCsn (.cv y)))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn
                          (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
            (.classEq A (synCsn (.cv y))))))
      p0001 p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
        (.classEq A (synCsn (.cv y))))
      y x
  have p0009 :=
    @gSnex
      (synCsn (synCsn (synCsn (synCsn
              (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))
  have p0010 :=
    @gSneq (.cv y)
      (synCsn (synCsn (synCsn (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
  have p0011 :=
    @gEqeq2d
      (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                    (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
      (synCsn (.cv y))
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                    (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
      A p0010
  have freeVariableCertificate3 :
    y ∉
      ((synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                    (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉
      ((Wff.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                          (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0012 :=
    @gCeqsexv (.classEq A (synCsn (.cv y)))
      (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))))
      y
      (synCsn (synCsn (synCsn (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))
      freeVariableCertificate3 freeVariableCertificate4 p0009 p0011
  have p0013 :=
    @gExbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                        (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
          (.classEq A (synCsn (.cv y)))))
      (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))))))))
      x p0012
  have p0014 :=
    @gBitri
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn
                          (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn
                          (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                        (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))))
      p0008 p0013
  have p0015 :=
    @gBitri
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (synCsn
                      (synCsn (synCsn
                          (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))
            (.classEq A (synCsn (.cv y))))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                        (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))))
      p0007 p0014
  have p0016 :=
    @gBitri
      (.classMem A (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))
      (synWrex y (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
        (.classEq A (synCsn (.cv y))))
      (synWex x (.classEq A (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn
                        (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))))))))
      p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_pw1ss1c`. -/
@[expose]
noncomputable def gPw1ss1c (A : Class) : Nominal.NPrf (synWss (synCpw1 A) (synC1c)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCpw1 A))
  have p0001 := @gInss2 (synCpw A) (synC1c)
  have p0002 :=
    @gEqsstri (synCpw1 A) (synCin (synCpw A) (synC1c)) (synC1c) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_n_0nel1c`. -/
@[expose]
noncomputable def gN0nel1c : Nominal.NPrf (.neg (.classMem (synC0) (synC1c))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := @gVex x
  have p0001 := @gSnprc (.cv x)
  have p0002 := @gEqcom (synCsn (.cv x)) (synC0)
  have p0003 :=
    @gBitri (.neg (.classMem (.cv x) (synCvv))) (.classEq (synCsn (.cv x)) (synC0))
      (.classEq (synC0) (synCsn (.cv x))) p0001 p0002
  have p0004 :=
    @gCon1bii (.classMem (.cv x) (synCvv)) (.classEq (synC0) (synCsn (.cv x))) p0003
  have p0005 :=
    @gMpbir (.neg (.classEq (synC0) (synCsn (.cv x)))) (.classMem (.cv x) (synCvv))
      p0000 p0004
  have p0006 := @gNex (.classEq (synC0) (synCsn (.cv x))) x p0005
  have p0007 :=
    @gEl1c x (synC0)
      (by
        exact
          (show x ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0008 :=
    @gMtbir (.classMem (synC0) (synC1c))
      (synWex x (.classEq (synC0) (synCsn (.cv x)))) p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_pw0`. -/
@[expose]
noncomputable def gPw0 : Nominal.NPrf (.classEq (synCpw (synC0)) (synCsn (synC0))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := @gSs0b (.cv x)
  have p0001 := @gAbbii (synWss (.cv x) (synC0)) (.classEq (.cv x) (synC0)) x p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw x (synC0)
      (by
        exact
          (show x ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn x (synC0)
      (by
        exact
          (show x ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0004 :=
    @gN3eqtr4i (.cab x (synWss (.cv x) (synC0))) (.cab x (.classEq (.cv x) (synC0)))
      (synCpw (synC0)) (synCsn (synC0)) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_pw10`. -/
@[expose]
noncomputable def gPw10 : Nominal.NPrf (.classEq (synCpw1 (synC0)) (synC0)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have p0000 := (Nominal.classEqRefl (synCpw1 (synC0)))
  have p0001 := @gPw0
  have p0002 := @gIneq1i (synCpw (synC0)) (synCsn (synC0)) (synC1c) p0001
  have freeVariableCertificate0 : x ∉ ((synCsn (synC0))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.notMem_empty,
      not_false_eq_true]
  have p0003 :=
    @gDisj x (synCsn (synC0)) (synC1c) freeVariableCertificate0
      (by
        exact
          (show x ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0004 := @gN0nel1c
  have p0005 :=
    @gElsn x (synC0)
      (by
        exact
          (show x ∉ ((synC0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0006 := @gEleq1 (.cv x) (synC0) (synC1c)
  have p0007 :=
    @gSylbi (.classMem (.cv x) (synCsn (synC0))) (.classEq (.cv x) (synC0))
      (synWb (.classMem (.cv x) (synC1c)) (.classMem (synC0) (synC1c))) p0005 p0006
  have p0008 :=
    @gMtbiri (.classMem (.cv x) (synCsn (synC0))) (.classMem (.cv x) (synC1c))
      (.classMem (synC0) (synC1c)) p0004 p0007
  have p0009 :=
    @gMprgbir (.classEq (synCin (synCsn (synC0)) (synC1c)) (synC0))
      (.neg (.classMem (.cv x) (synC1c))) x (synCsn (synC0)) p0003 p0008
  have p0010 :=
    @gN3eqtri (synCpw1 (synC0)) (synCin (synCpw (synC0)) (synC1c))
      (synCin (synCsn (synC0)) (synC1c)) (synC0) p0000 p0002 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_eqpw1`. -/
@[expose]
noncomputable def gEqpw1 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (synWb (.classEq A (synCpw1 B)) (synWa (synWss A (synC1c))
          (.all x (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B))))) :=
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
  have p0000 := @gPw1ss1c B
  have p0001 := @gSseq1 A (synCpw1 B) (synC1c)
  have p0002 :=
    @gMpbiri (.classEq A (synCpw1 B)) (synWss A (synC1c))
      (synWss (synCpw1 B) (synC1c)) p0000 p0001
  have p0003 :=
    @gSsofeq y A (synCpw1 B) (synC1c)
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by
        exact
          (show y ∉ ((synCpw1 B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
              exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))))
      (by
        exact
          (show y ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0004 :=
    @gMpan2 (synWss A (synC1c)) (synWss (synCpw1 B) (synC1c))
      (synWb (.classEq A (synCpw1 B)) (synWral y (synC1c)
          (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B)))))
      p0000 p0003
  have p0005 :=
    (Nominal.biimpRefl (synWral y (synC1c)
        (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B)))))
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0006 := @gEl1c x (.cv y) freeVariableCertificate0
  have p0007 :=
    @gImbi1i (.classMem (.cv y) (synC1c))
      (synWex x (.classEq (.cv y) (synCsn (.cv x))))
      (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))) p0006
  have freeVariableCertificate1 :
    x ∉ ((synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_y, dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have p0008 :=
    @gN1923v (.classEq (.cv y) (synCsn (.cv x)))
      (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))) x
      freeVariableCertificate1
  have p0009 :=
    @gBitr4i
      (.imp (.classMem (.cv y) (synC1c))
        (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))))
      (.imp (synWex x (.classEq (.cv y) (synCsn (.cv x))))
        (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))))
      (.all x (.imp (.classEq (.cv y) (synCsn (.cv x)))
          (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B)))))
      p0007 p0008
  have p0010 :=
    @gAlbii
      (.imp (.classMem (.cv y) (synC1c))
        (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))))
      (.all x (.imp (.classEq (.cv y) (synCsn (.cv x)))
          (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B)))))
      y p0009
  have p0011 :=
    @gAlcom
      (.imp (.classEq (.cv y) (synCsn (.cv x)))
        (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))))
      x y
  have p0012 :=
    @gBitr4i
      (.all y (.imp (.classMem (.cv y) (synC1c))
          (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B)))))
      (.all y (.all x (.imp (.classEq (.cv y) (synCsn (.cv x)))
            (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))))))
      (.all x (.all y (.imp (.classEq (.cv y) (synCsn (.cv x)))
            (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))))))
      p0010 p0011
  have p0013 :=
    @gBitri
      (synWral y (synC1c) (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))))
      (.all y (.imp (.classMem (.cv y) (synC1c))
          (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B)))))
      (.all x (.all y (.imp (.classEq (.cv y) (synCsn (.cv x)))
            (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))))))
      p0005 p0012
  have p0014 := @gSnex (.cv x)
  have p0015 := @gEleq1 (.cv y) (synCsn (.cv x)) A
  have p0016 := @gEleq1 (.cv y) (synCsn (.cv x)) (synCpw1 B)
  have p0017 :=
    @gBibi12d (.classEq (.cv y) (synCsn (.cv x))) (.classMem (.cv y) A)
      (.classMem (synCsn (.cv x)) A) (.classMem (.cv y) (synCpw1 B))
      (.classMem (synCsn (.cv x)) (synCpw1 B)) p0015 p0016
  have freeVariableCertificate2 : y ∉ ((synCsn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate3 :
    y ∉
      ((synWb (.classMem (synCsn (.cv x)) A)
          (.classMem (synCsn (.cv x)) (synCpw1 B)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, fresh_y_not_B, or_false,
      not_false_eq_true]
  have p0018 :=
    @gCeqsalv (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B)))
      (synWb (.classMem (synCsn (.cv x)) A) (.classMem (synCsn (.cv x)) (synCpw1 B)))
      y (synCsn (.cv x)) freeVariableCertificate2 freeVariableCertificate3 p0014 p0017
  have p0019 := @gSnelpw1 (.cv x) B
  have p0020 :=
    @gBibi2i (.classMem (synCsn (.cv x)) (synCpw1 B)) (.classMem (.cv x) B)
      (.classMem (synCsn (.cv x)) A) p0019
  have p0021 :=
    @gBitri
      (.all y (.imp (.classEq (.cv y) (synCsn (.cv x)))
          (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B)))))
      (synWb (.classMem (synCsn (.cv x)) A) (.classMem (synCsn (.cv x)) (synCpw1 B)))
      (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B)) p0018 p0020
  have p0022 :=
    @gAlbii
      (.all y (.imp (.classEq (.cv y) (synCsn (.cv x)))
          (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B)))))
      (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B)) x p0021
  have p0023 :=
    @gBitri
      (synWral y (synC1c) (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))))
      (.all x (.all y (.imp (.classEq (.cv y) (synCsn (.cv x)))
            (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))))))
      (.all x (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B))) p0013 p0022
  have p0024 :=
    @gSyl6bb (synWss A (synC1c)) (.classEq A (synCpw1 B))
      (synWral y (synC1c) (synWb (.classMem (.cv y) A) (.classMem (.cv y) (synCpw1 B))))
      (.all x (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B))) p0004 p0023
  have p0025 :=
    @gBiadan2 (.classEq A (synCpw1 B)) (synWss A (synC1c))
      (.all x (synWb (.classMem (synCsn (.cv x)) A) (.classMem (.cv x) B))) p0002 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_pw1un`. -/
@[expose]
noncomputable def gPw1un (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCpw1 (synCun A B)) (synCun (synCpw1 A) (synCpw1 B))) :=
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
  have p0000 := @gRexun (.classEq (.cv x) (synCsn (.cv y))) y A B
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((synCun A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0001 :=
    @gElpw1 y (.cv x) (synCun A B) freeVariableCertificate0 freeVariableCertificate1
  have p0002 := @gElun (.cv x) (synCpw1 A) (synCpw1 B)
  have p0003 :=
    @gElpw1 y (.cv x) A freeVariableCertificate0
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0004 :=
    @gElpw1 y (.cv x) B freeVariableCertificate0
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0005 :=
    @gOrbi12i (.classMem (.cv x) (synCpw1 A))
      (synWrex y A (.classEq (.cv x) (synCsn (.cv y)))) (.classMem (.cv x) (synCpw1 B))
      (synWrex y B (.classEq (.cv x) (synCsn (.cv y)))) p0003 p0004
  have p0006 :=
    @gBitri (.classMem (.cv x) (synCun (synCpw1 A) (synCpw1 B)))
      (synWo (.classMem (.cv x) (synCpw1 A)) (.classMem (.cv x) (synCpw1 B)))
      (synWo (synWrex y A (.classEq (.cv x) (synCsn (.cv y))))
        (synWrex y B (.classEq (.cv x) (synCsn (.cv y)))))
      p0002 p0005
  have p0007 :=
    @gN3bitr4i (synWrex y (synCun A B) (.classEq (.cv x) (synCsn (.cv y))))
      (synWo (synWrex y A (.classEq (.cv x) (synCsn (.cv y))))
        (synWrex y B (.classEq (.cv x) (synCsn (.cv y)))))
      (.classMem (.cv x) (synCpw1 (synCun A B)))
      (.classMem (.cv x) (synCun (synCpw1 A) (synCpw1 B))) p0000 p0001 p0006
  have freeVariableCertificate2 : x ∉ ((synCpw1 (synCun A B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate3 : x ∉ ((synCun (synCpw1 A) (synCpw1 B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0008 :=
    @gEqriv x (synCpw1 (synCun A B)) (synCun (synCpw1 A) (synCpw1 B))
      freeVariableCertificate2 freeVariableCertificate3 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_pw1in`. -/
@[expose]
noncomputable def gPw1in (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCpw1 (synCin A B)) (synCin (synCpw1 A) (synCpw1 B))) :=
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
    @gAncom (synWa (.classMem (.cv y) A) (.classMem (.cv x) (synCpw1 B)))
      (.classEq (.cv x) (synCsn (.cv y)))
  have p0001 := @gEleq1 (.cv x) (synCsn (.cv y)) (synCpw1 B)
  have p0002 := @gSnelpw1 (.cv y) B
  have p0003 :=
    @gSyl6bb (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) (synCpw1 B))
      (.classMem (synCsn (.cv y)) (synCpw1 B)) (.classMem (.cv y) B) p0001 p0002
  have p0004 :=
    @gAnbi2d (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) (synCpw1 B))
      (.classMem (.cv y) B) (.classMem (.cv y) A) p0003
  have p0005 := @gElin (.cv y) A B
  have p0006 :=
    @gSyl6bbr (.classEq (.cv x) (synCsn (.cv y)))
      (synWa (.classMem (.cv y) A) (.classMem (.cv x) (synCpw1 B)))
      (synWa (.classMem (.cv y) A) (.classMem (.cv y) B))
      (.classMem (.cv y) (synCin A B)) p0004 p0005
  have p0007 :=
    @gPm532ri (.classEq (.cv x) (synCsn (.cv y)))
      (synWa (.classMem (.cv y) A) (.classMem (.cv x) (synCpw1 B)))
      (.classMem (.cv y) (synCin A B)) p0006
  have p0008 :=
    @gAn12 (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A)
      (.classMem (.cv x) (synCpw1 B))
  have p0009 :=
    @gN3bitr3i
      (synWa (synWa (.classMem (.cv y) A) (.classMem (.cv x) (synCpw1 B)))
        (.classEq (.cv x) (synCsn (.cv y))))
      (synWa (.classEq (.cv x) (synCsn (.cv y)))
        (synWa (.classMem (.cv y) A) (.classMem (.cv x) (synCpw1 B))))
      (synWa (.classMem (.cv y) (synCin A B)) (.classEq (.cv x) (synCsn (.cv y))))
      (synWa (.classMem (.cv y) A)
        (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) (synCpw1 B))))
      p0000 p0007 p0008
  have p0010 :=
    @gRexbii2 (.classEq (.cv x) (synCsn (.cv y)))
      (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) (synCpw1 B))) y
      (synCin A B) A p0009
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((synCin A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0011 :=
    @gElpw1 y (.cv x) (synCin A B) freeVariableCertificate0 freeVariableCertificate1
  have p0012 :=
    @gElpw1 y (.cv x) A freeVariableCertificate0
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0013 :=
    @gAnbi1i (.classMem (.cv x) (synCpw1 A))
      (synWrex y A (.classEq (.cv x) (synCsn (.cv y)))) (.classMem (.cv x) (synCpw1 B))
      p0012
  have p0014 := @gElin (.cv x) (synCpw1 A) (synCpw1 B)
  have freeVariableCertificate2 : y ∉ ((Wff.classMem (.cv x) (synCpw1 B))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_B, or_false, not_false_eq_true]
  have p0015 :=
    @gR1941v (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) (synCpw1 B)) y A
      freeVariableCertificate2
  have p0016 :=
    @gN3bitr4i
      (synWa (.classMem (.cv x) (synCpw1 A)) (.classMem (.cv x) (synCpw1 B)))
      (synWa (synWrex y A (.classEq (.cv x) (synCsn (.cv y))))
        (.classMem (.cv x) (synCpw1 B)))
      (.classMem (.cv x) (synCin (synCpw1 A) (synCpw1 B)))
      (synWrex y A
        (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) (synCpw1 B))))
      p0013 p0014 p0015
  have p0017 :=
    @gN3bitr4i (synWrex y (synCin A B) (.classEq (.cv x) (synCsn (.cv y))))
      (synWrex y A
        (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) (synCpw1 B))))
      (.classMem (.cv x) (synCpw1 (synCin A B)))
      (.classMem (.cv x) (synCin (synCpw1 A) (synCpw1 B))) p0010 p0011 p0016
  have freeVariableCertificate3 : x ∉ ((synCpw1 (synCin A B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate4 : x ∉ ((synCin (synCpw1 A) (synCpw1 B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0018 :=
    @gEqriv x (synCpw1 (synCin A B)) (synCin (synCpw1 A) (synCpw1 B))
      freeVariableCertificate3 freeVariableCertificate4 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_pw1sn`. -/
@[expose]
noncomputable def gPw1sn (A : Class)
    (hyp_pw1sn_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synCpw1 (synCsn A)) (synCsn (synCsn A))) :=
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
  have p0000 := @gSneq (.cv y) A
  have p0001 := @gEqeq2d (.classEq (.cv y) A) (synCsn (.cv y)) (synCsn A) (.cv x) p0000
  have freeVariableCertificate0 : y ∉ ((Wff.classEq (.cv x) (synCsn A))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true]
  have p0002 :=
    @gRexsn (.classEq (.cv x) (synCsn (.cv y))) (.classEq (.cv x) (synCsn A)) y A
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate0
      hyp_pw1sn_1 p0001
  have freeVariableCertificate1 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0003 :=
    @gElpw1 y (.cv x) (synCsn A) freeVariableCertificate1
      (by
        exact
          (show y ∉ ((synCsn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
  have p0004 :=
    @gElsn x (synCsn A)
      (by
        exact
          (show x ∉ ((synCsn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
  have p0005 :=
    @gN3bitr4i (synWrex y (synCsn A) (.classEq (.cv x) (synCsn (.cv y))))
      (.classEq (.cv x) (synCsn A)) (.classMem (.cv x) (synCpw1 (synCsn A)))
      (.classMem (.cv x) (synCsn (synCsn A))) p0002 p0003 p0004
  have freeVariableCertificate2 : x ∉ ((synCpw1 (synCsn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_A,
      not_false_eq_true]
  have freeVariableCertificate3 : x ∉ ((synCsn (synCsn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_A,
      not_false_eq_true]
  have p0006 :=
    @gEqriv x (synCpw1 (synCsn A)) (synCsn (synCsn A)) freeVariableCertificate2
      freeVariableCertificate3 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_pw10b`. -/
@[expose]
noncomputable def gPw10b (A : Class) :
    Nominal.NPrf (synWb (.classEq (synCpw1 A) (synC0)) (.classEq A (synC0))) :=
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
  have p0000 := @gN0 x A (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0001 := @gSnelpw1 (.cv x) A
  have p0002 := @gNe0i (synCpw1 A) (synCsn (.cv x))
  have p0003 :=
    @gSylbir (.classMem (.cv x) A) (.classMem (synCsn (.cv x)) (synCpw1 A))
      (synWne (synCpw1 A) (synC0)) p0001 p0002
  have freeVariableCertificate0 : x ∉ ((synWne (synCpw1 A) (synC0))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0004 :=
    @gExlimiv (.classMem (.cv x) A) (synWne (synCpw1 A) (synC0)) x
      freeVariableCertificate0 p0003
  have p0005 :=
    @gSylbi (synWne A (synC0)) (synWex x (.classMem (.cv x) A))
      (synWne (synCpw1 A) (synC0)) p0000 p0004
  have p0006 := @gNecon4i A (synC0) (synCpw1 A) (synC0) p0005
  have p0007 := @gPw1eq A (synC0)
  have p0008 := @gPw10
  have p0009 :=
    @gSyl6eq (.classEq A (synC0)) (synCpw1 A) (synCpw1 (synC0)) (synC0) p0007 p0008
  have p0010 :=
    @gImpbii (.classEq (synCpw1 A) (synC0)) (.classEq A (synC0)) p0006 p0009
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

/-- Checked nominal proof certificate identified upstream as `g_df1c2`. -/
@[expose]
noncomputable def gDf1c2 : Nominal.NPrf (.classEq (synC1c) (synCpw1 (synCvv))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have p0000 := @gRexv (.classEq (.cv x) (synCsn (.cv y))) y
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0001 :=
    @gElpw1 y (.cv x) (synCvv) freeVariableCertificate0
      (by
        exact
          (show y ∉ ((synCvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0002 := @gEl1c y (.cv x) freeVariableCertificate0
  have p0003 :=
    @gN3bitr4ri (synWrex y (synCvv) (.classEq (.cv x) (synCsn (.cv y))))
      (synWex y (.classEq (.cv x) (synCsn (.cv y))))
      (.classMem (.cv x) (synCpw1 (synCvv))) (.classMem (.cv x) (synC1c)) p0000 p0001
      p0002
  have freeVariableCertificate1 : x ∉ ((synCpw1 (synCvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.notMem_empty,
      not_false_eq_true]
  have p0004 :=
    @gEqriv x (synC1c) (synCpw1 (synCvv))
      (by
        exact
          (show x ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_pw1ss`. -/
@[expose]
noncomputable def gPw1ss (A : Class) (B : Class) :
    Nominal.NPrf (.imp (synWss A B) (synWss (synCpw1 A) (synCpw1 B))) :=
  by
  have p0000 := @gSspwb A B
  have p0001 := @gSsrin (synCpw A) (synCpw B) (synC1c)
  have p0002 :=
    @gSylbi (synWss A B) (synWss (synCpw A) (synCpw B))
      (synWss (synCin (synCpw A) (synC1c)) (synCin (synCpw B) (synC1c))) p0000
      p0001
  have p0003 := (Nominal.classEqRefl (synCpw1 A))
  have p0004 := (Nominal.classEqRefl (synCpw1 B))
  have p0005 :=
    @gN3sstr4g (synWss A B) (synCin (synCpw A) (synC1c))
      (synCin (synCpw B) (synC1c)) (synCpw1 A) (synCpw1 B) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_pw111`. -/
@[expose]
noncomputable def gPw111 (A : Class) (B : Class) :
    Nominal.NPrf (synWb (.classEq (synCpw1 A) (synCpw1 B)) (.classEq A B)) :=
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
  have p0000 := @gSnex (.cv x)
  have p0001 := @gEleq1 (.cv t) (synCsn (.cv x)) (synCpw1 A)
  have p0002 := @gEleq1 (.cv t) (synCsn (.cv x)) (synCpw1 B)
  have p0003 :=
    @gBibi12d (.classEq (.cv t) (synCsn (.cv x))) (.classMem (.cv t) (synCpw1 A))
      (.classMem (synCsn (.cv x)) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))
      (.classMem (synCsn (.cv x)) (synCpw1 B)) p0001 p0002
  have freeVariableCertificate0 : t ∉ ((synCsn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate1 :
    t ∉
      ((synWb (.classMem (synCsn (.cv x)) (synCpw1 A))
          (.classMem (synCsn (.cv x)) (synCpw1 B)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, fresh_t_not_B, or_false,
      not_false_eq_true]
  have p0004 :=
    @gCeqsalv (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B)))
      (synWb (.classMem (synCsn (.cv x)) (synCpw1 A))
        (.classMem (synCsn (.cv x)) (synCpw1 B)))
      t (synCsn (.cv x)) freeVariableCertificate0 freeVariableCertificate1 p0000 p0003
  have p0005 := @gSnelpw1 (.cv x) A
  have p0006 := @gSnelpw1 (.cv x) B
  have p0007 :=
    @gBibi12i (.classMem (synCsn (.cv x)) (synCpw1 A)) (.classMem (.cv x) A)
      (.classMem (synCsn (.cv x)) (synCpw1 B)) (.classMem (.cv x) B) p0005 p0006
  have p0008 :=
    @gBitri
      (.all t (.imp (.classEq (.cv t) (synCsn (.cv x)))
          (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B)))))
      (synWb (.classMem (synCsn (.cv x)) (synCpw1 A))
        (.classMem (synCsn (.cv x)) (synCpw1 B)))
      (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)) p0004 p0007
  have p0009 :=
    @gAlbii
      (.all t (.imp (.classEq (.cv t) (synCsn (.cv x)))
          (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B)))))
      (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0008
  have p0010 := @gPw1ss1c A
  have p0011 := @gPw1ss1c B
  have p0012 :=
    @gSsofeq t (synCpw1 A) (synCpw1 B) (synC1c)
      (by
        exact
          (show t ∉ ((synCpw1 A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
              exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))))
      (by
        exact
          (show t ∉ ((synCpw1 B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
              exact (show t ∉ (B).fv from (by exact fresh_t_not_B)))))
      (by
        exact
          (show t ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0013 :=
    @gMp2an (synWss (synCpw1 A) (synC1c)) (synWss (synCpw1 B) (synC1c))
      (synWb (.classEq (synCpw1 A) (synCpw1 B)) (synWral t (synC1c)
          (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B)))))
      p0010 p0011 p0012
  have p0014 :=
    (Nominal.biimpRefl (synWral t (synC1c)
        (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B)))))
  have freeVariableCertificate2 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0015 := @gEl1c x (.cv t) freeVariableCertificate2
  have p0016 :=
    @gImbi1i (.classMem (.cv t) (synC1c))
      (synWex x (.classEq (.cv t) (synCsn (.cv x))))
      (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))) p0015
  have freeVariableCertificate3 :
    x ∉ ((synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_t, fresh_x_not_A, fresh_x_not_B, or_false,
      not_false_eq_true]
  have p0017 :=
    @gN1923v (.classEq (.cv t) (synCsn (.cv x)))
      (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))) x
      freeVariableCertificate3
  have p0018 :=
    @gBitr4i
      (.imp (.classMem (.cv t) (synC1c))
        (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))))
      (.imp (synWex x (.classEq (.cv t) (synCsn (.cv x))))
        (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))))
      (.all x (.imp (.classEq (.cv t) (synCsn (.cv x)))
          (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B)))))
      p0016 p0017
  have p0019 :=
    @gAlbii
      (.imp (.classMem (.cv t) (synC1c))
        (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))))
      (.all x (.imp (.classEq (.cv t) (synCsn (.cv x)))
          (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B)))))
      t p0018
  have p0020 :=
    @gAlcom
      (.imp (.classEq (.cv t) (synCsn (.cv x)))
        (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))))
      t x
  have p0021 :=
    @gBitri
      (.all t (.imp (.classMem (.cv t) (synC1c))
          (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B)))))
      (.all t (.all x (.imp (.classEq (.cv t) (synCsn (.cv x)))
            (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))))))
      (.all x (.all t (.imp (.classEq (.cv t) (synCsn (.cv x)))
            (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))))))
      p0019 p0020
  have p0022 :=
    @gBitri
      (synWral t (synC1c)
        (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))))
      (.all t (.imp (.classMem (.cv t) (synC1c))
          (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B)))))
      (.all x (.all t (.imp (.classEq (.cv t) (synCsn (.cv x)))
            (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))))))
      p0014 p0021
  have p0023 :=
    @gBitri (.classEq (synCpw1 A) (synCpw1 B))
      (synWral t (synC1c)
        (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))))
      (.all x (.all t (.imp (.classEq (.cv t) (synCsn (.cv x)))
            (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))))))
      p0013 p0022
  have p0024 :=
    @gDfcleq x A B (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0025 :=
    @gN3bitr4i
      (.all x (.all t (.imp (.classEq (.cv t) (synCsn (.cv x)))
            (synWb (.classMem (.cv t) (synCpw1 A)) (.classMem (.cv t) (synCpw1 B))))))
      (.all x (synWb (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.classEq (synCpw1 A) (synCpw1 B)) (.classEq A B) p0009 p0023 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_eluni1g`. -/
@[expose]
noncomputable def gEluni1g (A : Class) (B : Class) (V : Class) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (.classMem A (synCuni1 B)) (.classMem (synCsn A) B))) :=
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
  have p0000 := (Nominal.classEqRefl (synCuni1 B))
  have p0001 := @gEleq2i (synCuni1 B) (synCuni (synCin B (synC1c))) A p0000
  have freeVariableCertificate0 : x ∉ ((synCin B (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_B, or_false, not_false_eq_true]
  have p0002 :=
    @gEluni x A (synCin B (synC1c))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate0
  have p0003 := @gElin (.cv x) B (synC1c)
  have p0004 := @gAncom (.classMem (.cv x) B) (.classMem (.cv x) (synC1c))
  have freeVariableCertificate1 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0005 := @gEl1c y (.cv x) freeVariableCertificate1
  have p0006 :=
    @gAnbi1i (.classMem (.cv x) (synC1c))
      (synWex y (.classEq (.cv x) (synCsn (.cv y)))) (.classMem (.cv x) B) p0005
  have freeVariableCertificate2 : y ∉ ((Wff.classMem (.cv x) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_x, fresh_y_not_B, or_false, not_false_eq_true]
  have p0007 :=
    @gN1941v (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B) y
      freeVariableCertificate2
  have p0008 :=
    @gBitr4i (synWa (.classMem (.cv x) (synC1c)) (.classMem (.cv x) B))
      (synWa (synWex y (.classEq (.cv x) (synCsn (.cv y)))) (.classMem (.cv x) B))
      (synWex y (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B)))
      p0006 p0007
  have p0009 :=
    @gN3bitri (.classMem (.cv x) (synCin B (synC1c)))
      (synWa (.classMem (.cv x) B) (.classMem (.cv x) (synC1c)))
      (synWa (.classMem (.cv x) (synC1c)) (.classMem (.cv x) B))
      (synWex y (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B)))
      p0003 p0004 p0008
  have p0010 :=
    @gAnbi2i (.classMem (.cv x) (synCin B (synC1c)))
      (synWex y (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B)))
      (.classMem A (.cv x)) p0009
  have freeVariableCertificate3 : y ∉ ((Wff.classMem A (.cv x))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0011 :=
    @gN1942v (.classMem A (.cv x))
      (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B)) y
      freeVariableCertificate3
  have p0012 :=
    @gBitr4i (synWa (.classMem A (.cv x)) (.classMem (.cv x) (synCin B (synC1c))))
      (synWa (.classMem A (.cv x))
        (synWex y (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B))))
      (synWex y (synWa (.classMem A (.cv x))
          (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B))))
      p0010 p0011
  have p0013 :=
    @gExbii (synWa (.classMem A (.cv x)) (.classMem (.cv x) (synCin B (synC1c))))
      (synWex y (synWa (.classMem A (.cv x))
          (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B))))
      x p0012
  have p0014 :=
    @gExcom
      (synWa (.classMem A (.cv x))
        (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B)))
      x y
  have p0015 :=
    @gAn12 (.classMem A (.cv x)) (.classEq (.cv x) (synCsn (.cv y)))
      (.classMem (.cv x) B)
  have p0016 :=
    @gExbii
      (synWa (.classMem A (.cv x))
        (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B)))
      (synWa (.classEq (.cv x) (synCsn (.cv y)))
        (synWa (.classMem A (.cv x)) (.classMem (.cv x) B)))
      x p0015
  have p0017 := @gSnex (.cv y)
  have p0018 := @gEleq2 (.cv x) (synCsn (.cv y)) A
  have p0019 := @gVex y
  have p0020 := @gElsnc2 A (.cv y) p0019
  have p0021 :=
    @gSyl6bb (.classEq (.cv x) (synCsn (.cv y))) (.classMem A (.cv x))
      (.classMem A (synCsn (.cv y))) (.classEq A (.cv y)) p0018 p0020
  have p0022 := @gEleq1 (.cv x) (synCsn (.cv y)) B
  have p0023 :=
    @gAnbi12d (.classEq (.cv x) (synCsn (.cv y))) (.classMem A (.cv x))
      (.classEq A (.cv y)) (.classMem (.cv x) B) (.classMem (synCsn (.cv y)) B) p0021
      p0022
  have freeVariableCertificate4 : x ∉ ((synCsn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_y,
      not_false_eq_true]
  have freeVariableCertificate5 :
    x ∉ ((synWa (.classEq A (.cv y)) (.classMem (synCsn (.cv y)) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, fresh_x_not_B, or_false,
      not_false_eq_true]
  have p0024 :=
    @gCeqsexv (synWa (.classMem A (.cv x)) (.classMem (.cv x) B))
      (synWa (.classEq A (.cv y)) (.classMem (synCsn (.cv y)) B)) x (synCsn (.cv y))
      freeVariableCertificate4 freeVariableCertificate5 p0017 p0023
  have p0025 := @gEqcom A (.cv y)
  have p0026 :=
    @gAnbi1i (.classEq A (.cv y)) (.classEq (.cv y) A) (.classMem (synCsn (.cv y)) B)
      p0025
  have p0027 :=
    @gN3bitri
      (synWex x (synWa (.classMem A (.cv x))
          (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B))))
      (synWex x (synWa (.classEq (.cv x) (synCsn (.cv y)))
          (synWa (.classMem A (.cv x)) (.classMem (.cv x) B))))
      (synWa (.classEq A (.cv y)) (.classMem (synCsn (.cv y)) B))
      (synWa (.classEq (.cv y) A) (.classMem (synCsn (.cv y)) B)) p0016 p0024 p0026
  have p0028 :=
    @gExbii
      (synWex x (synWa (.classMem A (.cv x))
          (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B))))
      (synWa (.classEq (.cv y) A) (.classMem (synCsn (.cv y)) B)) y p0027
  have p0029 :=
    @gN3bitri
      (synWex x (synWa (.classMem A (.cv x)) (.classMem (.cv x) (synCin B (synC1c)))))
      (synWex x (synWex y (synWa (.classMem A (.cv x))
            (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B)))))
      (synWex y (synWex x (synWa (.classMem A (.cv x))
            (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) B)))))
      (synWex y (synWa (.classEq (.cv y) A) (.classMem (synCsn (.cv y)) B))) p0013
      p0014 p0028
  have p0030 :=
    @gN3bitri (.classMem A (synCuni1 B)) (.classMem A (synCuni (synCin B (synC1c))))
      (synWex x (synWa (.classMem A (.cv x)) (.classMem (.cv x) (synCin B (synC1c)))))
      (synWex y (synWa (.classEq (.cv y) A) (.classMem (synCsn (.cv y)) B))) p0001
      p0002 p0029
  have p0031 := @gSneq (.cv y) A
  have p0032 := @gEleq1d (.classEq (.cv y) A) (synCsn (.cv y)) (synCsn A) B p0031
  have freeVariableCertificate6 : y ∉ ((Wff.classMem (synCsn A) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0033 :=
    @gCeqsexgv (.classMem (synCsn (.cv y)) B) (.classMem (synCsn A) B) y A V
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate6
      p0032
  have p0034 :=
    @gSyl5bb (.classMem A (synCuni1 B))
      (synWex y (synWa (.classEq (.cv y) A) (.classMem (synCsn (.cv y)) B)))
      (.classMem A V) (.classMem (synCsn A) B) p0030 p0033
  exact p0034

/-- Checked nominal proof certificate identified upstream as `g_eluni1`. -/
@[expose]
noncomputable def gEluni1 (A : Class) (B : Class)
    (hyp_eluni1_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWb (.classMem A (synCuni1 B)) (.classMem (synCsn A) B)) :=
  by
  have p0000 := @gEluni1g A B (synCvv)
  have p0001 := Nominal.mp hyp_eluni1_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elxpk`. -/
@[expose]
noncomputable def gElxpk (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem A (synCxpk B C)) (synWex x (synWex y
            (synWa (.classEq A (synCopk (.cv x) (.cv y)))
              (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))))) :=
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
  have p0000 := @gElex A (synCxpk B C)
  have p0001 := @gOpkex (.cv x) (.cv y)
  have p0002 := @gEleq1 A (synCopk (.cv x) (.cv y)) (synCvv)
  have p0003 :=
    @gMpbiri (.classEq A (synCopk (.cv x) (.cv y))) (.classMem A (synCvv))
      (.classMem (synCopk (.cv x) (.cv y)) (synCvv)) p0001 p0002
  have p0004 :=
    @gAdantr (.classEq A (synCopk (.cv x) (.cv y))) (.classMem A (synCvv))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)) p0003
  have freeVariableCertificate0 : x ∉ ((Wff.classMem A (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((Wff.classMem A (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_y, or_false, not_false_eq_true]
  have p0005 :=
    @gExlimivv
      (synWa (.classEq A (synCopk (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      (.classMem A (synCvv)) x y freeVariableCertificate0 freeVariableCertificate1 p0004
  have p0006 := @gEqeq1 (.cv w) A (synCopk (.cv x) (.cv y))
  have p0007 :=
    @gAnbi1d (.classEq (.cv w) A) (.classEq (.cv w) (synCopk (.cv x) (.cv y)))
      (.classEq A (synCopk (.cv x) (.cv y)))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)) p0006
  have freeVariableCertificate2 : x ∉ ((Wff.classEq (.cv w) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_w, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((Wff.classEq (.cv w) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_w, dv_A_y, or_false, not_false_eq_true]
  have p0008 :=
    @gN2exbidv (.classEq (.cv w) A)
      (synWa (.classEq (.cv w) (synCopk (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      (synWa (.classEq A (synCopk (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      x y freeVariableCertificate2 freeVariableCertificate3 p0007
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXpk w x y B C
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
      ((synWex x (synWex y (synWa (.classEq A (synCopk (.cv x) (.cv y)))
              (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))))).fv :=
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
    @gElab2g
      (synWex x (synWex y (synWa (.classEq (.cv w) (synCopk (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))))
      (synWex x (synWex y (synWa (.classEq A (synCopk (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))))
      w A (synCxpk B C) (synCvv)
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A))) freeVariableCertificate4
      p0008 p0009
  have p0011 :=
    @gPm521nii (.classMem A (synCxpk B C)) (.classMem A (synCvv))
      (synWex x (synWex y (synWa (.classEq A (synCopk (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))))
      p0000 p0005 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_elxpk2`. -/
@[expose]
noncomputable def gElxpk2 (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem A (synCxpk B C))
        (synWrex x B (synWrex y C (.classEq A (synCopk (.cv x) (.cv y)))))) :=
  by
  have p0000 :=
    @gAncom (synWa (.classMem (.cv x) B) (.classMem (.cv y) C))
      (.classEq A (synCopk (.cv x) (.cv y)))
  have p0001 :=
    @gN2exbii
      (synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) C))
        (.classEq A (synCopk (.cv x) (.cv y))))
      (synWa (.classEq A (synCopk (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))
      x y p0000
  have p0002 :=
    @gR2ex (.classEq A (synCopk (.cv x) (.cv y))) x y B C
      (by exact (show y ∉ (B).fv from (by exact dv_B_y)))
      (show x ≠ y from (by exact dv_x_y))
  have p0003 :=
    @gElxpk x y A B C (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
      (by exact (show y ∉ (B).fv from (by exact dv_B_y)))
      (by exact (show x ∉ (C).fv from (by exact dv_C_x)))
      (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
      (show x ≠ y from (by exact dv_x_y))
  have p0004 :=
    @gN3bitr4ri
      (synWex x (synWex y (synWa (synWa (.classMem (.cv x) B) (.classMem (.cv y) C))
            (.classEq A (synCopk (.cv x) (.cv y))))))
      (synWex x (synWex y (synWa (.classEq A (synCopk (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) B) (.classMem (.cv y) C)))))
      (synWrex x B (synWrex y C (.classEq A (synCopk (.cv x) (.cv y)))))
      (.classMem A (synCxpk B C)) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_xpkeq1`. -/
@[expose]
noncomputable def gXpkeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCxpk A C) (synCxpk B C))) :=
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
    @gRexeq (synWrex z C (.classEq (.cv x) (synCopk (.cv y) (.cv z)))) y A B
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have freeVariableCertificate1 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have p0001 :=
    @gElxpk2 y z (.cv x) A C freeVariableCertificate0 freeVariableCertificate1
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0002 :=
    @gElxpk2 y z (.cv x) B C freeVariableCertificate0 freeVariableCertificate1
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0003 :=
    @gN3bitr4g (.classEq A B)
      (synWrex y A (synWrex z C (.classEq (.cv x) (synCopk (.cv y) (.cv z)))))
      (synWrex y B (synWrex z C (.classEq (.cv x) (synCopk (.cv y) (.cv z)))))
      (.classMem (.cv x) (synCxpk A C)) (.classMem (.cv x) (synCxpk B C)) p0000 p0001
      p0002
  have freeVariableCertificate2 : x ∉ ((synCxpk A C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate3 : x ∉ ((synCxpk B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate4 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0004 :=
    @gEqrdv (.classEq A B) x (synCxpk A C) (synCxpk B C) freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_xpkeq2`. -/
@[expose]
noncomputable def gXpkeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCxpk C A) (synCxpk C B))) :=
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
    @gRexeq (.classEq (.cv x) (synCopk (.cv y) (.cv z))) z A B
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
  have freeVariableCertificate0 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0001 :=
    @gRexbidv (.classEq A B) (synWrex z A (.classEq (.cv x) (synCopk (.cv y) (.cv z))))
      (synWrex z B (.classEq (.cv x) (synCopk (.cv y) (.cv z)))) y C
      freeVariableCertificate0 p0000
  have freeVariableCertificate1 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have p0002 :=
    @gElxpk2 y z (.cv x) C A freeVariableCertificate1 freeVariableCertificate2
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0003 :=
    @gElxpk2 y z (.cv x) C B freeVariableCertificate1 freeVariableCertificate2
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0004 :=
    @gN3bitr4g (.classEq A B)
      (synWrex y C (synWrex z A (.classEq (.cv x) (synCopk (.cv y) (.cv z)))))
      (synWrex y C (synWrex z B (.classEq (.cv x) (synCopk (.cv y) (.cv z)))))
      (.classMem (.cv x) (synCxpk C A)) (.classMem (.cv x) (synCxpk C B)) p0001 p0002
      p0003
  have freeVariableCertificate3 : x ∉ ((synCxpk C A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_C, fresh_x_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate4 : x ∉ ((synCxpk C B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_C, fresh_x_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate5 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0005 :=
    @gEqrdv (.classEq A B) x (synCxpk C A) (synCxpk C B) freeVariableCertificate3
      freeVariableCertificate4 freeVariableCertificate5 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_xpkeq12`. -/
@[expose]
noncomputable def gXpkeq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A B) (.classEq C D)) (.classEq (synCxpk A C) (synCxpk B D))) :=
  by
  have p0000 := @gXpkeq1 A B C
  have p0001 := @gXpkeq2 C D B
  have p0002 :=
    @gSylan9eq (.classEq A B) (.classEq C D) (synCxpk A C) (synCxpk B C) (synCxpk B D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_xpkeq12i`. -/
@[expose]
noncomputable def gXpkeq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_xpkeq12i_1 : Nominal.NPrf (.classEq A B))
    (hyp_xpkeq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (synCxpk A C) (synCxpk B D)) :=
  by
  have p0000 := @gXpkeq12 A B C D
  have p0001 :=
    @gMp2an (.classEq A B) (.classEq C D) (.classEq (synCxpk A C) (synCxpk B D))
      hyp_xpkeq12i_1 hyp_xpkeq12i_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_xpkeq2d`. -/
@[expose]
noncomputable def gXpkeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_xpkeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCxpk C A) (synCxpk C B))) :=
  by
  have p0000 := @gXpkeq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCxpk C A) (synCxpk C B)) hyp_xpkeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elvvk`. -/
@[expose]
noncomputable def gElvvk (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem A (synCxpk (synCvv) (synCvv)))
        (synWex x (synWex y (.classEq A (synCopk (.cv x) (.cv y)))))) :=
  by
  have p0000 :=
    @gElxpk x y A (synCvv) (synCvv) (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by
        exact
          (show x ∉ ((synCvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((synCvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((synCvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((synCvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show x ≠ y from (by exact dv_x_y))
  have p0001 := @gVex x
  have p0002 := @gVex y
  have p0003 :=
    @gPm32i (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)) p0001 p0002
  have p0004 :=
    @gBiantru (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
      (.classEq A (synCopk (.cv x) (.cv y))) p0003
  have p0005 :=
    @gN2exbii (.classEq A (synCopk (.cv x) (.cv y)))
      (synWa (.classEq A (synCopk (.cv x) (.cv y)))
        (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))
      x y p0004
  have p0006 :=
    @gBitr4i (.classMem A (synCxpk (synCvv) (synCvv)))
      (synWex x (synWex y (synWa (.classEq A (synCopk (.cv x) (.cv y)))
            (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))))))
      (synWex x (synWex y (.classEq A (synCopk (.cv x) (.cv y))))) p0000 p0005
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

/-- Checked nominal proof certificate identified upstream as `g_opkabssvvk`. -/
@[expose]
noncomputable def gOpkabssvvk (ph : Wff) (x : Var) (y : Var) (z : Var) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (synWss (.cab x (synWex y
            (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) ph))))
        (synCxpk (synCvv) (synCvv))) :=
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
  have p0000 := @gEqid (synCopk (.cv y) (.cv z))
  have p0001 := @gVex y
  have p0002 := @gVex z
  have p0003 := @gOpkeq12 (.cv w) (.cv t) (.cv y) (.cv z)
  have p0004_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq w y) (.objEq t z))
        (.classEq (synCopk (.cv w) (.cv t)) (synCopk (.cv y) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCopk synCpr synCun synCnin synWnan synCcompl synCsn
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
    @gEqeq2d (synWa (.objEq w y) (.objEq t z)) (synCopk (.cv w) (.cv t))
      (synCopk (.cv y) (.cv z)) (synCopk (.cv y) (.cv z)) p0004_e00_recanon
  have p0005_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv w) (.cv y)) (.classEq (.cv t) (.cv z)))
        (synWb (.classEq (synCopk (.cv y) (.cv z)) (synCopk (.cv w) (.cv t)))
          (.classEq (synCopk (.cv y) (.cv z)) (synCopk (.cv y) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWb synCopk synCpr synCun synCnin synWnan synCcompl synCsn
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
    w ∉ ((Wff.classEq (synCopk (.cv y) (.cv z)) (synCopk (.cv y) (.cv z)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true]
  have freeVariableCertificate5 :
    t ∉ ((Wff.classEq (synCopk (.cv y) (.cv z)) (synCopk (.cv y) (.cv z)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_y, fresh_t_ne_z, or_false, not_false_eq_true]
  have p0005 :=
    @gSpc2ev (.classEq (synCopk (.cv y) (.cv z)) (synCopk (.cv w) (.cv t)))
      (.classEq (synCopk (.cv y) (.cv z)) (synCopk (.cv y) (.cv z))) w t (.cv y) (.cv z)
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      (show w ≠ t from (by exact fresh_w_ne_t)) p0001 p0002 p0005_e02_recanon
  have p0006 := Nominal.mp p0000 p0005
  have freeVariableCertificate6 : w ∉ ((synCopk (.cv y) (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true]
  have freeVariableCertificate7 : t ∉ ((synCopk (.cv y) (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_y, fresh_t_ne_z, or_false, not_false_eq_true]
  have p0007 :=
    @gElvvk w t (synCopk (.cv y) (.cv z)) freeVariableCertificate6
      freeVariableCertificate7 (show w ≠ t from (by exact fresh_w_ne_t))
  have p0008 :=
    @gMpbir (.classMem (synCopk (.cv y) (.cv z)) (synCxpk (synCvv) (synCvv)))
      (synWex w (synWex t (.classEq (synCopk (.cv y) (.cv z)) (synCopk (.cv w) (.cv t)))))
      p0006 p0007
  have p0009 := @gEleq1 (.cv x) (synCopk (.cv y) (.cv z)) (synCxpk (synCvv) (synCvv))
  have p0010 :=
    @gMpbiri (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
      (.classMem (.cv x) (synCxpk (synCvv) (synCvv)))
      (.classMem (synCopk (.cv y) (.cv z)) (synCxpk (synCvv) (synCvv))) p0008 p0009
  have p0011 :=
    @gAdantr (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
      (.classMem (.cv x) (synCxpk (synCvv) (synCvv))) ph p0010
  have freeVariableCertificate8 :
    y ∉ ((Wff.classMem (.cv x) (synCxpk (synCvv) (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, (Ne.symm dv_x_y), or_false,
      not_false_eq_true]
  have freeVariableCertificate9 :
    z ∉ ((Wff.classMem (.cv x) (synCxpk (synCvv) (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, (Ne.symm dv_x_z), or_false,
      not_false_eq_true]
  have p0012 :=
    @gExlimivv (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) ph)
      (.classMem (.cv x) (synCxpk (synCvv) (synCvv))) y z freeVariableCertificate8
      freeVariableCertificate9 p0011
  have freeVariableCertificate10 : x ∉ ((synCxpk (synCvv) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0013 :=
    @gAbssi
      (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) ph))) x
      (synCxpk (synCvv) (synCvv)) freeVariableCertificate10 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_opkabssvvki`. -/
@[expose]
noncomputable def gOpkabssvvki (ph : Wff) (x : Var) (y : Var) (z : Var) (A : Class)
    (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (hyp_opkabssvvki_1 : Nominal.NPrf (.classEq A (.cab x (synWex y
              (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) ph)))))) :
    Nominal.NPrf (synWss A (synCxpk (synCvv) (synCvv))) :=
  by
  have p0000 :=
    @gOpkabssvvk ph x y z (show x ≠ y from (by exact dv_x_y))
      (show x ≠ z from (by exact dv_x_z))
  have p0001 :=
    @gEqsstri A
      (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) ph))))
      (synCxpk (synCvv) (synCvv)) hyp_opkabssvvki_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_xpkssvvk`. -/
@[expose]
noncomputable def gXpkssvvk (A : Class) (B : Class) :
    Nominal.NPrf (synWss (synCxpk A B) (synCxpk (synCvv) (synCvv))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXpk x y z A B
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @gOpkabssvvki (synWa (.classMem (.cv y) A) (.classMem (.cv z) B)) x y z
      (synCxpk A B) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ssrelk`. -/
@[expose]
noncomputable def gSsrelk (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWss A (synCxpk (synCvv) (synCvv))) (synWb (synWss A B) (.all x (.all y
              (.imp (.classMem (synCopk (.cv x) (.cv y)) A)
                (.classMem (synCopk (.cv x) (.cv y)) B)))))) :=
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
  have freeVariableCertificate0 : z ∉ ((synCxpk (synCvv) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0000 :=
    @gSsofss z A B (synCxpk (synCvv) (synCvv))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) freeVariableCertificate0
  have p0001 :=
    (Nominal.biimpRefl (synWral z (synCxpk (synCvv) (synCvv))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))
  have freeVariableCertificate1 : x ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_z, not_false_eq_true]
  have freeVariableCertificate2 : y ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_z, not_false_eq_true]
  have p0002 :=
    @gElvvk x y (.cv z) freeVariableCertificate1 freeVariableCertificate2
      (show x ≠ y from (by exact dv_x_y))
  have p0003 :=
    @gImbi1i (.classMem (.cv z) (synCxpk (synCvv) (synCvv)))
      (synWex x (synWex y (.classEq (.cv z) (synCopk (.cv x) (.cv y)))))
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
    @gN1923vv (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
      (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)) x y freeVariableCertificate3
      freeVariableCertificate4
  have p0005 :=
    @gBitr4i
      (.imp (.classMem (.cv z) (synCxpk (synCvv) (synCvv)))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.imp (synWex x (synWex y (.classEq (.cv z) (synCopk (.cv x) (.cv y)))))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
            (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))))
      p0003 p0004
  have p0006 :=
    @gAlbii
      (.imp (.classMem (.cv z) (synCxpk (synCvv) (synCvv)))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
            (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))))
      z p0005
  have p0007 :=
    @gAlrot3
      (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      z x y
  have p0008 :=
    @gBitri
      (.all z (.imp (.classMem (.cv z) (synCxpk (synCvv) (synCvv)))
          (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.all z (.all x (.all y (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
              (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      (.all x (.all y (.all z (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
              (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      p0006 p0007
  have p0009 :=
    @gBitri
      (synWral z (synCxpk (synCvv) (synCvv))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all z (.imp (.classMem (.cv z) (synCxpk (synCvv) (synCvv)))
          (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.all x (.all y (.all z (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
              (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      p0001 p0008
  have p0010 := @gOpkex (.cv x) (.cv y)
  have p0011 := @gEleq1 (.cv z) (synCopk (.cv x) (.cv y)) A
  have p0012 := @gEleq1 (.cv z) (synCopk (.cv x) (.cv y)) B
  have p0013 :=
    @gImbi12d (.classEq (.cv z) (synCopk (.cv x) (.cv y))) (.classMem (.cv z) A)
      (.classMem (synCopk (.cv x) (.cv y)) A) (.classMem (.cv z) B)
      (.classMem (synCopk (.cv x) (.cv y)) B) p0011 p0012
  have freeVariableCertificate5 : z ∉ ((synCopk (.cv x) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate6 :
    z ∉
      ((Wff.imp (.classMem (synCopk (.cv x) (.cv y)) A)
          (.classMem (synCopk (.cv x) (.cv y)) B))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_B, or_false,
      not_false_eq_true]
  have p0014 :=
    @gCeqsalv (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))
      (.imp (.classMem (synCopk (.cv x) (.cv y)) A) (.classMem (synCopk (.cv x) (.cv y)) B))
      z (synCopk (.cv x) (.cv y)) freeVariableCertificate5 freeVariableCertificate6 p0010
      p0013
  have p0015 :=
    @gN2albii
      (.all z (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
          (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.imp (.classMem (synCopk (.cv x) (.cv y)) A) (.classMem (synCopk (.cv x) (.cv y)) B))
      x y p0014
  have p0016 :=
    @gBitri
      (synWral z (synCxpk (synCvv) (synCvv))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.all z (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
              (.imp (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      (.all x (.all y (.imp (.classMem (synCopk (.cv x) (.cv y)) A)
            (.classMem (synCopk (.cv x) (.cv y)) B))))
      p0009 p0015
  have p0017 :=
    @gSyl6bb (synWss A (synCxpk (synCvv) (synCvv))) (synWss A B)
      (synWral z (synCxpk (synCvv) (synCvv))
        (.imp (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classMem (synCopk (.cv x) (.cv y)) A)
            (.classMem (synCopk (.cv x) (.cv y)) B))))
      p0000 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_eqrelk`. -/
@[expose]
noncomputable def gEqrelk (x : Var) (y : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWa (synWss A (synCxpk (synCvv) (synCvv)))
          (synWss B (synCxpk (synCvv) (synCvv)))) (synWb (.classEq A B) (.all x (.all y
              (synWb (.classMem (synCopk (.cv x) (.cv y)) A)
                (.classMem (synCopk (.cv x) (.cv y)) B)))))) :=
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
  have freeVariableCertificate0 : z ∉ ((synCxpk (synCvv) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0000 :=
    @gSsofeq z A B (synCxpk (synCvv) (synCvv))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) freeVariableCertificate0
  have p0001 :=
    (Nominal.biimpRefl (synWral z (synCxpk (synCvv) (synCvv))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))
  have freeVariableCertificate1 : x ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_z, not_false_eq_true]
  have freeVariableCertificate2 : y ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_z, not_false_eq_true]
  have p0002 :=
    @gElvvk x y (.cv z) freeVariableCertificate1 freeVariableCertificate2
      (show x ≠ y from (by exact dv_x_y))
  have p0003 :=
    @gImbi1i (.classMem (.cv z) (synCxpk (synCvv) (synCvv)))
      (synWex x (synWex y (.classEq (.cv z) (synCopk (.cv x) (.cv y)))))
      (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)) p0002
  have freeVariableCertificate3 :
    x ∉ ((synWb (.classMem (.cv z) A) (.classMem (.cv z) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_z, dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉ ((synWb (.classMem (.cv z) A) (.classMem (.cv z) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_z, dv_A_y, dv_B_y, or_false, not_false_eq_true]
  have p0004 :=
    @gN1923vv (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
      (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)) x y freeVariableCertificate3
      freeVariableCertificate4
  have p0005 :=
    @gBitr4i
      (.imp (.classMem (.cv z) (synCxpk (synCvv) (synCvv)))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.imp (synWex x (synWex y (.classEq (.cv z) (synCopk (.cv x) (.cv y)))))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
            (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))))
      p0003 p0004
  have p0006 :=
    @gAlbii
      (.imp (.classMem (.cv z) (synCxpk (synCvv) (synCvv)))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
            (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))))
      z p0005
  have p0007 :=
    @gAlrot3
      (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      z x y
  have p0008 :=
    @gBitri
      (.all z (.imp (.classMem (.cv z) (synCxpk (synCvv) (synCvv)))
          (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.all z (.all x (.all y (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
              (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      (.all x (.all y (.all z (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
              (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      p0006 p0007
  have p0009 := @gOpkex (.cv x) (.cv y)
  have p0010 := @gEleq1 (.cv z) (synCopk (.cv x) (.cv y)) A
  have p0011 := @gEleq1 (.cv z) (synCopk (.cv x) (.cv y)) B
  have p0012 :=
    @gBibi12d (.classEq (.cv z) (synCopk (.cv x) (.cv y))) (.classMem (.cv z) A)
      (.classMem (synCopk (.cv x) (.cv y)) A) (.classMem (.cv z) B)
      (.classMem (synCopk (.cv x) (.cv y)) B) p0010 p0011
  have freeVariableCertificate5 : z ∉ ((synCopk (.cv x) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate6 :
    z ∉
      ((synWb (.classMem (synCopk (.cv x) (.cv y)) A)
          (.classMem (synCopk (.cv x) (.cv y)) B))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_B, or_false,
      not_false_eq_true]
  have p0013 :=
    @gCeqsalv (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))
      (synWb (.classMem (synCopk (.cv x) (.cv y)) A) (.classMem (synCopk (.cv x) (.cv y)) B))
      z (synCopk (.cv x) (.cv y)) freeVariableCertificate5 freeVariableCertificate6 p0009
      p0012
  have p0014 :=
    @gN2albii
      (.all z (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
          (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (synWb (.classMem (synCopk (.cv x) (.cv y)) A) (.classMem (synCopk (.cv x) (.cv y)) B))
      x y p0013
  have p0015 :=
    @gN3bitri
      (synWral z (synCxpk (synCvv) (synCvv))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all z (.imp (.classMem (.cv z) (synCxpk (synCvv) (synCvv)))
          (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.all x (.all y (.all z (.imp (.classEq (.cv z) (synCopk (.cv x) (.cv y)))
              (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      (.all x (.all y (synWb (.classMem (synCopk (.cv x) (.cv y)) A)
            (.classMem (synCopk (.cv x) (.cv y)) B))))
      p0001 p0008 p0014
  have p0016 :=
    @gSyl6bb
      (synWa (synWss A (synCxpk (synCvv) (synCvv)))
        (synWss B (synCxpk (synCvv) (synCvv))))
      (.classEq A B)
      (synWral z (synCxpk (synCvv) (synCvv))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (synWb (.classMem (synCopk (.cv x) (.cv y)) A)
            (.classMem (synCopk (.cv x) (.cv y)) B))))
      p0000 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_eqrelkriiv`. -/
@[expose]
noncomputable def gEqrelkriiv (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y)
    (hyp_eqrelkriiv_1 : Nominal.NPrf (synWss A (synCxpk (synCvv) (synCvv))))
    (hyp_eqrelkriiv_2 : Nominal.NPrf (synWss B (synCxpk (synCvv) (synCvv))))
    (hyp_eqrelkriiv_3 : Nominal.NPrf (synWb (.classMem (synCopk (.cv x) (.cv y)) A)
          (.classMem (synCopk (.cv x) (.cv y)) B))) :
    Nominal.NPrf (.classEq A B) :=
  by
  have p0000 :=
    @gGen2
      (synWb (.classMem (synCopk (.cv x) (.cv y)) A) (.classMem (synCopk (.cv x) (.cv y)) B))
      x y hyp_eqrelkriiv_3
  have p0001 :=
    @gEqrelk x y A B (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
      (by exact (show y ∉ (B).fv from (by exact dv_B_y)))
      (show x ≠ y from (by exact dv_x_y))
  have p0002 :=
    @gMp2an (synWss A (synCxpk (synCvv) (synCvv)))
      (synWss B (synCxpk (synCvv) (synCvv)))
      (synWb (.classEq A B) (.all x (.all y (synWb (.classMem (synCopk (.cv x) (.cv y)) A)
              (.classMem (synCopk (.cv x) (.cv y)) B)))))
      hyp_eqrelkriiv_1 hyp_eqrelkriiv_2 p0001
  have p0003 :=
    @gMpbir (.classEq A B)
      (.all x (.all y (synWb (.classMem (synCopk (.cv x) (.cv y)) A)
            (.classMem (synCopk (.cv x) (.cv y)) B))))
      p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_cnvkeq`. -/
@[expose]
noncomputable def gCnvkeq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCcnvk A) (synCcnvk B))) :=
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
  have p0000 := @gEleq2 A B (synCopk (.cv z) (.cv y))
  have p0001 :=
    @gAnbi2d (.classEq A B) (.classMem (synCopk (.cv z) (.cv y)) A)
      (.classMem (synCopk (.cv z) (.cv y)) B)
      (.classEq (.cv x) (synCopk (.cv y) (.cv z))) p0000
  have freeVariableCertificate0 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : z ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have p0002 :=
    @gN2exbidv (.classEq A B)
      (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk (.cv z) (.cv y)) A))
      (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk (.cv z) (.cv y)) B))
      y z freeVariableCertificate0 freeVariableCertificate1 p0001
  have freeVariableCertificate2 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0003 :=
    @gAbbidv (.classEq A B)
      (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk (.cv z) (.cv y)) A))))
      (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk (.cv z) (.cv y)) B))))
      x freeVariableCertificate2 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnvk x y z A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnvk x y z B
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0006 :=
    @gN3eqtr4g (.classEq A B)
      (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv z) (.cv y)) A)))))
      (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv z) (.cv y)) B)))))
      (synCcnvk A) (synCcnvk B) p0003 p0004 p0005
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

/-- Checked nominal proof certificate identified upstream as `g_ins2keq`. -/
@[expose]
noncomputable def gIns2keq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCins2k A) (synCins2k B))) :=
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
  have p0000 := @gEleq2 A B (synCopk (.cv w) (.cv u))
  have p0001 :=
    @gN3anbi3d (.classEq A B) (.classMem (synCopk (.cv w) (.cv u)) A)
      (.classMem (synCopk (.cv w) (.cv u)) B)
      (.classEq (.cv y) (synCsn (synCsn (.cv w))))
      (.classEq (.cv z) (synCopk (.cv t) (.cv u))) p0000
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
    @gN3exbidv (.classEq A B)
      (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
        (.classEq (.cv z) (synCopk (.cv t) (.cv u))) (.classMem (synCopk (.cv w) (.cv u)) A))
      (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
        (.classEq (.cv z) (synCopk (.cv t) (.cv u))) (.classMem (synCopk (.cv w) (.cv u)) B))
      w t u freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      p0001
  have p0003 :=
    @gAnbi2d (.classEq A B)
      (synWex w (synWex t (synWex u (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
              (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
              (.classMem (synCopk (.cv w) (.cv u)) A)))))
      (synWex w (synWex t (synWex u (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
              (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
              (.classMem (synCopk (.cv w) (.cv u)) B)))))
      (.classEq (.cv x) (synCopk (.cv y) (.cv z))) p0002
  have freeVariableCertificate3 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate4 : z ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have p0004 :=
    @gN2exbidv (.classEq A B)
      (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex w (synWex t (synWex u
              (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                (.classMem (synCopk (.cv w) (.cv u)) A))))))
      (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex w (synWex t (synWex u
              (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                (.classMem (synCopk (.cv w) (.cv u)) B))))))
      y z freeVariableCertificate3 freeVariableCertificate4 p0003
  have freeVariableCertificate5 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0005 :=
    @gAbbidv (.classEq A B)
      (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex w
              (synWex t (synWex u (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                    (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                    (.classMem (synCopk (.cv w) (.cv u)) A))))))))
      (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex w
              (synWex t (synWex u (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                    (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                    (.classMem (synCopk (.cv w) (.cv u)) B))))))))
      x freeVariableCertificate5 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIns2k x y z u t w A
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIns2k x y z u t w B
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
    @gN3eqtr4g (.classEq A B)
      (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
              (synWex w (synWex t (synWex u
                    (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                      (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                      (.classMem (synCopk (.cv w) (.cv u)) A)))))))))
      (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
              (synWex w (synWex t (synWex u
                    (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                      (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                      (.classMem (synCopk (.cv w) (.cv u)) B)))))))))
      (synCins2k A) (synCins2k B) p0005 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_ins3keq`. -/
@[expose]
noncomputable def gIns3keq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCins3k A) (synCins3k B))) :=
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
  have p0000 := @gEleq2 A B (synCopk (.cv w) (.cv t))
  have p0001 :=
    @gN3anbi3d (.classEq A B) (.classMem (synCopk (.cv w) (.cv t)) A)
      (.classMem (synCopk (.cv w) (.cv t)) B)
      (.classEq (.cv y) (synCsn (synCsn (.cv w))))
      (.classEq (.cv z) (synCopk (.cv t) (.cv u))) p0000
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
    @gN3exbidv (.classEq A B)
      (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
        (.classEq (.cv z) (synCopk (.cv t) (.cv u))) (.classMem (synCopk (.cv w) (.cv t)) A))
      (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
        (.classEq (.cv z) (synCopk (.cv t) (.cv u))) (.classMem (synCopk (.cv w) (.cv t)) B))
      w t u freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      p0001
  have p0003 :=
    @gAnbi2d (.classEq A B)
      (synWex w (synWex t (synWex u (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
              (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
              (.classMem (synCopk (.cv w) (.cv t)) A)))))
      (synWex w (synWex t (synWex u (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
              (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
              (.classMem (synCopk (.cv w) (.cv t)) B)))))
      (.classEq (.cv x) (synCopk (.cv y) (.cv z))) p0002
  have freeVariableCertificate3 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate4 : z ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have p0004 :=
    @gN2exbidv (.classEq A B)
      (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex w (synWex t (synWex u
              (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                (.classMem (synCopk (.cv w) (.cv t)) A))))))
      (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex w (synWex t (synWex u
              (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                (.classMem (synCopk (.cv w) (.cv t)) B))))))
      y z freeVariableCertificate3 freeVariableCertificate4 p0003
  have freeVariableCertificate5 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0005 :=
    @gAbbidv (.classEq A B)
      (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex w
              (synWex t (synWex u (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                    (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                    (.classMem (synCopk (.cv w) (.cv t)) A))))))))
      (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex w
              (synWex t (synWex u (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                    (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                    (.classMem (synCopk (.cv w) (.cv t)) B))))))))
      x freeVariableCertificate5 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIns3k x y z u t w A
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIns3k x y z u t w B
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
    @gN3eqtr4g (.classEq A B)
      (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
              (synWex w (synWex t (synWex u
                    (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                      (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                      (.classMem (synCopk (.cv w) (.cv t)) A)))))))))
      (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
              (synWex w (synWex t (synWex u
                    (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                      (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                      (.classMem (synCopk (.cv w) (.cv t)) B)))))))))
      (synCins3k A) (synCins3k B) p0005 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_imakeq1`. -/
@[expose]
noncomputable def gImakeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCimak A C) (synCimak B C))) :=
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
  have p0000 := @gEleq2 A B (synCopk (.cv y) (.cv x))
  have freeVariableCertificate0 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0001 :=
    @gRexbidv (.classEq A B) (.classMem (synCopk (.cv y) (.cv x)) A)
      (.classMem (synCopk (.cv y) (.cv x)) B) y C freeVariableCertificate0 p0000
  have freeVariableCertificate1 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0002 :=
    @gAbbidv (.classEq A B) (synWrex y C (.classMem (synCopk (.cv y) (.cv x)) A))
      (synWrex y C (.classMem (synCopk (.cv y) (.cv x)) B)) x freeVariableCertificate1
      p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfImak x y A C
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfImak x y B C
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0005 :=
    @gN3eqtr4g (.classEq A B)
      (.cab x (synWrex y C (.classMem (synCopk (.cv y) (.cv x)) A)))
      (.cab x (synWrex y C (.classMem (synCopk (.cv y) (.cv x)) B))) (synCimak A C)
      (synCimak B C) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_imakeq2`. -/
@[expose]
noncomputable def gImakeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCimak C A) (synCimak C B))) :=
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
    @gRexeq (.classMem (synCopk (.cv y) (.cv x)) C) y A B
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have freeVariableCertificate0 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0001 :=
    @gAbbidv (.classEq A B) (synWrex y A (.classMem (synCopk (.cv y) (.cv x)) C))
      (synWrex y B (.classMem (synCopk (.cv y) (.cv x)) C)) x freeVariableCertificate0
      p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfImak x y C A
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfImak x y C B
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0004 :=
    @gN3eqtr4g (.classEq A B)
      (.cab x (synWrex y A (.classMem (synCopk (.cv y) (.cv x)) C)))
      (.cab x (synWrex y B (.classMem (synCopk (.cv y) (.cv x)) C))) (synCimak C A)
      (synCimak C B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_imakeq1i`. -/
@[expose]
noncomputable def gImakeq1i (A : Class) (B : Class) (C : Class)
    (hyp_imakeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCimak A C) (synCimak B C)) :=
  by
  have p0000 := @gImakeq1 A B C
  have p0001 := Nominal.mp hyp_imakeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imakeq1d`. -/
@[expose]
noncomputable def gImakeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_imakeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCimak A C) (synCimak B C))) :=
  by
  have p0000 := @gImakeq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCimak A C) (synCimak B C)) hyp_imakeq1d_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imakeq2d`. -/
@[expose]
noncomputable def gImakeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_imakeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCimak C A) (synCimak C B))) :=
  by
  have p0000 := @gImakeq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCimak C A) (synCimak C B)) hyp_imakeq1d_1
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_p6eq`. -/
@[expose]
noncomputable def gP6eq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCp6 A) (synCp6 B))) :=
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
  have p0000 := @gSseq2 A B (synCxpk (synCvv) (synCsn (synCsn (.cv x))))
  have freeVariableCertificate0 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0001 :=
    @gAbbidv (.classEq A B) (synWss (synCxpk (synCvv) (synCsn (synCsn (.cv x)))) A)
      (synWss (synCxpk (synCvv) (synCsn (synCsn (.cv x)))) B) x
      freeVariableCertificate0 p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfP6 x A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfP6 x B
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0004 :=
    @gN3eqtr4g (.classEq A B)
      (.cab x (synWss (synCxpk (synCvv) (synCsn (synCsn (.cv x)))) A))
      (.cab x (synWss (synCxpk (synCvv) (synCsn (synCsn (.cv x)))) B)) (synCp6 A)
      (synCp6 B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_sikeq`. -/
@[expose]
noncomputable def gSikeq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCsik A) (synCsik B))) :=
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
  have p0000 := @gEleq2 A B (synCopk (.cv w) (.cv t))
  have p0001 :=
    @gN3anbi3d (.classEq A B) (.classMem (synCopk (.cv w) (.cv t)) A)
      (.classMem (synCopk (.cv w) (.cv t)) B) (.classEq (.cv y) (synCsn (.cv w)))
      (.classEq (.cv z) (synCsn (.cv t))) p0000
  have freeVariableCertificate0 : w ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_w_not_A, fresh_w_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true]
  have p0002 :=
    @gN2exbidv (.classEq A B)
      (synW3a (.classEq (.cv y) (synCsn (.cv w))) (.classEq (.cv z) (synCsn (.cv t)))
        (.classMem (synCopk (.cv w) (.cv t)) A))
      (synW3a (.classEq (.cv y) (synCsn (.cv w))) (.classEq (.cv z) (synCsn (.cv t)))
        (.classMem (synCopk (.cv w) (.cv t)) B))
      w t freeVariableCertificate0 freeVariableCertificate1 p0001
  have p0003 :=
    @gAnbi2d (.classEq A B)
      (synWex w (synWex t (synW3a (.classEq (.cv y) (synCsn (.cv w)))
            (.classEq (.cv z) (synCsn (.cv t))) (.classMem (synCopk (.cv w) (.cv t)) A))))
      (synWex w (synWex t (synW3a (.classEq (.cv y) (synCsn (.cv w)))
            (.classEq (.cv z) (synCsn (.cv t))) (.classMem (synCopk (.cv w) (.cv t)) B))))
      (.classEq (.cv x) (synCopk (.cv y) (.cv z))) p0002
  have freeVariableCertificate2 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate3 : z ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have p0004 :=
    @gN2exbidv (.classEq A B)
      (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex w (synWex t
            (synW3a (.classEq (.cv y) (synCsn (.cv w))) (.classEq (.cv z) (synCsn (.cv t)))
              (.classMem (synCopk (.cv w) (.cv t)) A)))))
      (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex w (synWex t
            (synW3a (.classEq (.cv y) (synCsn (.cv w))) (.classEq (.cv z) (synCsn (.cv t)))
              (.classMem (synCopk (.cv w) (.cv t)) B)))))
      y z freeVariableCertificate2 freeVariableCertificate3 p0003
  have freeVariableCertificate4 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0005 :=
    @gAbbidv (.classEq A B)
      (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex w
              (synWex t (synW3a (.classEq (.cv y) (synCsn (.cv w)))
                  (.classEq (.cv z) (synCsn (.cv t)))
                  (.classMem (synCopk (.cv w) (.cv t)) A)))))))
      (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) (synWex w
              (synWex t (synW3a (.classEq (.cv y) (synCsn (.cv w)))
                  (.classEq (.cv z) (synCsn (.cv t)))
                  (.classMem (synCopk (.cv w) (.cv t)) B)))))))
      x freeVariableCertificate4 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSik x y z t w A
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSik x y z t w B
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
    @gN3eqtr4g (.classEq A B)
      (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
              (synWex w (synWex t (synW3a (.classEq (.cv y) (synCsn (.cv w)))
                    (.classEq (.cv z) (synCsn (.cv t)))
                    (.classMem (synCopk (.cv w) (.cv t)) A))))))))
      (.cab x (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
              (synWex w (synWex t (synW3a (.classEq (.cv y) (synCsn (.cv w)))
                    (.classEq (.cv z) (synCsn (.cv t)))
                    (.classMem (synCopk (.cv w) (.cv t)) B))))))))
      (synCsik A) (synCsik B) p0005 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_opkelopkabg`. -/
@[expose]
noncomputable def gOpkelopkabg (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (A : Class) (B : Class) (C : Class) (V : Class) (W : Class)
    (_dv_A_y : y ∉ A.fv) (_dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv)
    (dv_ch_z : z ∉ ch.fv) (dv_ph_x : x ∉ ph.fv) (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_opkelopkabg_1 : Nominal.NPrf (.classEq A (.cab x (synWex y
              (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) ph))))))
    (hyp_opkelopkabg_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ph ps)))
    (hyp_opkelopkabg_3 : Nominal.NPrf (.imp (.classEq (.cv z) C) (synWb ps ch))) :
    Nominal.NPrf
      (.imp (synWa (.classMem B V) (.classMem C W))
        (synWb (.classMem (synCopk B C) A) ch)) :=
  by
  have p0000 := @gOpkex B C
  have p0001 := @gEqeq1 (.cv x) (synCopk B C) (synCopk (.cv y) (.cv z))
  have p0002 := @gEqcom (synCopk B C) (synCopk (.cv y) (.cv z))
  have p0003 :=
    @gSyl6bb (.classEq (.cv x) (synCopk B C))
      (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
      (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
      (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) p0001 p0002
  have p0004 :=
    @gAnbi1d (.classEq (.cv x) (synCopk B C))
      (.classEq (.cv x) (synCopk (.cv y) (.cv z)))
      (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) ph p0003
  have freeVariableCertificate0 : y ∉ ((Wff.classEq (.cv x) (synCopk B C))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, dv_B_y, dv_C_y, (Ne.symm dv_x_y), or_false, not_false_eq_true]
  have freeVariableCertificate1 : z ∉ ((Wff.classEq (.cv x) (synCopk B C))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, dv_B_z, dv_C_z, (Ne.symm dv_x_z), or_false, not_false_eq_true]
  have p0005 :=
    @gN2exbidv (.classEq (.cv x) (synCopk B C))
      (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) ph)
      (synWa (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) ph) y z
      freeVariableCertificate0 freeVariableCertificate1 p0004
  have freeVariableCertificate2 : x ∉ ((synCopk B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      dv_B_x, dv_C_x, or_false, not_false_eq_true]
  have freeVariableCertificate3 :
    x ∉
      ((synWex y (synWex z
            (synWa (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) ph)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, dv_x_y, dv_x_z, dv_B_x, dv_C_x, dv_ph_x, or_false, and_false,
      not_false_eq_true]
  have p0006 :=
    @gElab2
      (synWex y (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) ph)))
      (synWex y (synWex z (synWa (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) ph)))
      x (synCopk B C) A freeVariableCertificate2 freeVariableCertificate3 p0000 p0005
      hyp_opkelopkabg_1
  have p0007 := @gElex B V
  have p0008 := @gElex C W
  have p0009 := @gVex y
  have p0010 := @gVex z
  have p0011 := @gOpkthg (.cv y) (.cv z) B C (synCvv) (synCvv) (synCvv)
  have p0012 :=
    @gMp3an12 (.classMem (.cv y) (synCvv)) (.classMem (.cv z) (synCvv))
      (.classMem C (synCvv))
      (synWb (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C))
        (synWa (.classEq (.cv y) B) (.classEq (.cv z) C)))
      p0009 p0010 p0011
  have p0013 :=
    @gAdantl (.classMem C (synCvv))
      (synWb (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C))
        (synWa (.classEq (.cv y) B) (.classEq (.cv z) C)))
      (.classMem B (synCvv)) p0012
  have p0014 :=
    @gAnbi1d (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C))
      (synWa (.classEq (.cv y) B) (.classEq (.cv z) C)) ph p0013
  have p0015 := @gAnass (.classEq (.cv y) B) (.classEq (.cv z) C) ph
  have p0016 :=
    @gSyl6bb (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWa (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) ph)
      (synWa (synWa (.classEq (.cv y) B) (.classEq (.cv z) C)) ph)
      (synWa (.classEq (.cv y) B) (synWa (.classEq (.cv z) C) ph)) p0014 p0015
  have freeVariableCertificate4 :
    z ∉ ((synWa (.classMem B (synCvv)) (.classMem C (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_B_z, dv_C_z, or_false, not_false_eq_true]
  have p0017 :=
    @gExbidv (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWa (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) ph)
      (synWa (.classEq (.cv y) B) (synWa (.classEq (.cv z) C) ph)) z
      freeVariableCertificate4 p0016
  have freeVariableCertificate5 : z ∉ ((Wff.classEq (.cv y) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      dv_B_z, (Ne.symm dv_y_z), or_false, not_false_eq_true]
  have p0018 :=
    @gN1942v (.classEq (.cv y) B) (synWa (.classEq (.cv z) C) ph) z
      freeVariableCertificate5
  have p0019 :=
    @gSyl6bb (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWex z (synWa (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) ph))
      (synWex z (synWa (.classEq (.cv y) B) (synWa (.classEq (.cv z) C) ph)))
      (synWa (.classEq (.cv y) B) (synWex z (synWa (.classEq (.cv z) C) ph))) p0017
      p0018
  have freeVariableCertificate6 :
    y ∉ ((synWa (.classMem B (synCvv)) (.classMem C (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_B_y, dv_C_y, or_false, not_false_eq_true]
  have p0020 :=
    @gExbidv (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWex z (synWa (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) ph))
      (synWa (.classEq (.cv y) B) (synWex z (synWa (.classEq (.cv z) C) ph))) y
      freeVariableCertificate6 p0019
  have p0021 :=
    @gAnbi2d (.classEq (.cv y) B) ph ps (.classEq (.cv z) C) hyp_opkelopkabg_2
  have p0022 :=
    @gExbidv (.classEq (.cv y) B) (synWa (.classEq (.cv z) C) ph)
      (synWa (.classEq (.cv z) C) ps) z freeVariableCertificate5 p0021
  have freeVariableCertificate7 : y ∉ ((synWex z (synWa (.classEq (.cv z) C) ps))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, dv_y_z, dv_C_y, dv_ps_y, or_false, and_false,
      not_false_eq_true]
  have p0023 :=
    @gCeqsexgv (synWex z (synWa (.classEq (.cv z) C) ph))
      (synWex z (synWa (.classEq (.cv z) C) ps)) y B (synCvv)
      (by exact (show y ∉ (B).fv from (by exact dv_B_y))) freeVariableCertificate7 p0022
  have p0024 :=
    @gAdantr (.classMem B (synCvv))
      (synWb (synWex y
          (synWa (.classEq (.cv y) B) (synWex z (synWa (.classEq (.cv z) C) ph))))
        (synWex z (synWa (.classEq (.cv z) C) ps)))
      (.classMem C (synCvv)) p0023
  have p0025 :=
    @gCeqsexgv ps ch z C (synCvv) (by exact (show z ∉ (C).fv from (by exact dv_C_z)))
      (by exact (show z ∉ (ch).fv from (by exact dv_ch_z))) hyp_opkelopkabg_3
  have p0026 :=
    @gAdantl (.classMem C (synCvv))
      (synWb (synWex z (synWa (.classEq (.cv z) C) ps)) ch) (.classMem B (synCvv))
      p0025
  have p0027 :=
    @gN3bitrd (synWa (.classMem B (synCvv)) (.classMem C (synCvv)))
      (synWex y (synWex z (synWa (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) ph)))
      (synWex y (synWa (.classEq (.cv y) B) (synWex z (synWa (.classEq (.cv z) C) ph))))
      (synWex z (synWa (.classEq (.cv z) C) ps)) ch p0020 p0024 p0026
  have p0028 :=
    @gSyl2an (.classMem B V) (.classMem B (synCvv)) (.classMem C (synCvv))
      (synWb (synWex y
          (synWex z (synWa (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) ph))) ch)
      (.classMem C W) p0007 p0008 p0027
  have p0029 :=
    @gSyl5bb (.classMem (synCopk B C) A)
      (synWex y (synWex z (synWa (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) ph)))
      (synWa (.classMem B V) (.classMem C W)) ch p0006 p0028
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

/-- Checked nominal proof certificate identified upstream as `g_opkelopkab`. -/
@[expose]
noncomputable def gOpkelopkab (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (y : Var)
    (z : Var) (A : Class) (B : Class) (C : Class) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_ch_z : z ∉ ch.fv) (dv_ph_x : x ∉ ph.fv)
    (dv_ps_y : y ∉ ps.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z)
    (hyp_opkelopkab_1 : Nominal.NPrf (.classEq A (.cab x (synWex y
              (synWex z (synWa (.classEq (.cv x) (synCopk (.cv y) (.cv z))) ph))))))
    (hyp_opkelopkab_2 : Nominal.NPrf (.imp (.classEq (.cv y) B) (synWb ph ps)))
    (hyp_opkelopkab_3 : Nominal.NPrf (.imp (.classEq (.cv z) C) (synWb ps ch)))
    (hyp_opkelopkab_4 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_opkelopkab_5 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf (synWb (.classMem (synCopk B C) A) ch) :=
  by
  have p0000 :=
    @gOpkelopkabg ph ps ch x y z A B C (synCvv) (synCvv)
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
    @gMp2an (.classMem B (synCvv)) (.classMem C (synCvv))
      (synWb (.classMem (synCopk B C) A) ch) hyp_opkelopkab_4 hyp_opkelopkab_5 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opkelxpkg`. -/
@[expose]
noncomputable def gOpkelxpkg (A : Class) (B : Class) (C : Class) (D : Class) (V : Class)
    (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synCxpk C D))
          (synWa (.classMem A C) (.classMem B D)))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfXpk z x y C D
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show z ∉ (D).fv from (by exact fresh_z_not_D)))
      (by exact (show x ∉ (D).fv from (by exact fresh_x_not_D)))
      (by exact (show y ∉ (D).fv from (by exact fresh_y_not_D)))
      (show z ≠ x from (by exact fresh_z_ne_x)) (show z ≠ y from (by exact fresh_z_ne_y))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 := @gEleq1 (.cv x) A C
  have p0002 :=
    @gAnbi1d (.classEq (.cv x) A) (.classMem (.cv x) C) (.classMem A C)
      (.classMem (.cv y) D) p0001
  have p0003 := @gEleq1 (.cv y) B D
  have p0004 :=
    @gAnbi2d (.classEq (.cv y) B) (.classMem (.cv y) D) (.classMem B D) (.classMem A C)
      p0003
  have freeVariableCertificate0 : x ∉ ((synCxpk C D)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_C, fresh_x_not_D, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((synCxpk C D)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_y_not_C, fresh_y_not_D, or_false, not_false_eq_true]
  have freeVariableCertificate2 : y ∉ ((synWa (.classMem A C) (.classMem B D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, fresh_y_not_A,
      fresh_y_not_C, fresh_y_not_B, fresh_y_not_D, or_false, not_false_eq_true]
  have freeVariableCertificate3 :
    z ∉ ((synWa (.classMem (.cv x) C) (.classMem (.cv y) D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_not_C, fresh_z_ne_y, fresh_z_not_D, or_false,
      not_false_eq_true]
  have freeVariableCertificate4 :
    x ∉ ((synWa (.classMem A C) (.classMem (.cv y) D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_not_A, fresh_x_not_C, fresh_x_ne_y, fresh_x_not_D, or_false,
      not_false_eq_true]
  have p0005 :=
    @gOpkelopkabg (synWa (.classMem (.cv x) C) (.classMem (.cv y) D))
      (synWa (.classMem A C) (.classMem (.cv y) D))
      (synWa (.classMem A C) (.classMem B D)) z x y (synCxpk C D) A B V W
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

/-- Checked nominal proof certificate identified upstream as `g_opkelxpk`. -/
@[expose]
noncomputable def gOpkelxpk (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_opkelxpk_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opkelxpk_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk A B) (synCxpk C D))
        (synWa (.classMem A C) (.classMem B D))) :=
  by
  have p0000 := @gOpkelxpkg A B C D (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (.classMem (synCopk A B) (synCxpk C D))
        (synWa (.classMem A C) (.classMem B D)))
      hyp_opkelxpk_1 hyp_opkelxpk_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opkelcnvkg`. -/
@[expose]
noncomputable def gOpkelcnvkg (A : Class) (B : Class) (C : Class) (V : Class)
    (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synCcnvk C)) (.classMem (synCopk B A) C))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnvk z x y C
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (show z ≠ x from (by exact fresh_z_ne_x)) (show z ≠ y from (by exact fresh_z_ne_y))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 := @gOpkeq2 (.cv x) A (.cv y)
  have p0002 :=
    @gEleq1d (.classEq (.cv x) A) (synCopk (.cv y) (.cv x)) (synCopk (.cv y) A) C p0001
  have p0003 := @gOpkeq1 (.cv y) B A
  have p0004 := @gEleq1d (.classEq (.cv y) B) (synCopk (.cv y) A) (synCopk B A) C p0003
  have freeVariableCertificate0 : y ∉ ((Wff.classMem (synCopk B A) C)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_y_not_B, fresh_y_not_A, fresh_y_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate1 : z ∉ ((Wff.classMem (synCopk (.cv y) (.cv x)) C)).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_y, fresh_z_ne_x, fresh_z_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Wff.classMem (synCopk (.cv y) A) C)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_y, fresh_x_not_A, fresh_x_not_C, or_false, not_false_eq_true]
  have p0005 :=
    @gOpkelopkabg (.classMem (synCopk (.cv y) (.cv x)) C)
      (.classMem (synCopk (.cv y) A) C) (.classMem (synCopk B A) C) z x y (synCcnvk C)
      A B V W
      (by
        exact
          (show x ∉ ((synCcnvk C)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk];
              exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))))
      (by
        exact
          (show y ∉ ((synCcnvk C)).fv from
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

/-- Checked nominal proof certificate identified upstream as `g_opkelcnvk`. -/
@[expose]
noncomputable def gOpkelcnvk (A : Class) (B : Class) (C : Class)
    (hyp_opkelcnvk_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opkelcnvk_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk A B) (synCcnvk C)) (.classMem (synCopk B A) C)) :=
  by
  have p0000 := @gOpkelcnvkg A B C (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (.classMem (synCopk A B) (synCcnvk C)) (.classMem (synCopk B A) C))
      hyp_opkelcnvk_1 hyp_opkelcnvk_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opkelins2kg`. -/
@[expose]
noncomputable def gOpkelins2kg (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synCins2k C)) (synWex x (synWex y (synWex z
                (synW3a (.classEq A (synCsn (synCsn (.cv x))))
                  (.classEq B (synCopk (.cv y) (.cv z)))
                  (.classMem (synCopk (.cv x) (.cv z)) C))))))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIns2k t w u z y x C
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
  have p0001 := @gEqeq1 (.cv w) A (synCsn (synCsn (.cv x)))
  have p0002 :=
    @gN3anbi1d (.classEq (.cv w) A) (.classEq (.cv w) (synCsn (synCsn (.cv x))))
      (.classEq A (synCsn (synCsn (.cv x))))
      (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
      (.classMem (synCopk (.cv x) (.cv z)) C) p0001
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
    @gN3exbidv (.classEq (.cv w) A)
      (synW3a (.classEq (.cv w) (synCsn (synCsn (.cv x))))
        (.classEq (.cv u) (synCopk (.cv y) (.cv z))) (.classMem (synCopk (.cv x) (.cv z)) C))
      (synW3a (.classEq A (synCsn (synCsn (.cv x))))
        (.classEq (.cv u) (synCopk (.cv y) (.cv z))) (.classMem (synCopk (.cv x) (.cv z)) C))
      x y z freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      p0002
  have p0004 := @gEqeq1 (.cv u) B (synCopk (.cv y) (.cv z))
  have p0005 :=
    @gN3anbi2d (.classEq (.cv u) B) (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
      (.classEq B (synCopk (.cv y) (.cv z))) (.classEq A (synCsn (synCsn (.cv x))))
      (.classMem (synCopk (.cv x) (.cv z)) C) p0004
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
    @gN3exbidv (.classEq (.cv u) B)
      (synW3a (.classEq A (synCsn (synCsn (.cv x))))
        (.classEq (.cv u) (synCopk (.cv y) (.cv z))) (.classMem (synCopk (.cv x) (.cv z)) C))
      (synW3a (.classEq A (synCsn (synCsn (.cv x))))
        (.classEq B (synCopk (.cv y) (.cv z))) (.classMem (synCopk (.cv x) (.cv z)) C))
      x y z freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      p0005
  have freeVariableCertificate6 :
    u ∉
      ((synWex x (synWex y (synWex z (synW3a (.classEq A (synCsn (synCsn (.cv x))))
                (.classEq B (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv z)) C)))))).fv :=
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
      ((synWex x (synWex y (synWex z (synW3a (.classEq (.cv w) (synCsn (synCsn (.cv x))))
                (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv z)) C)))))).fv :=
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
      ((synWex x (synWex y (synWex z (synW3a (.classEq A (synCsn (synCsn (.cv x))))
                (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv z)) C)))))).fv :=
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
    @gOpkelopkabg
      (synWex x (synWex y (synWex z (synW3a (.classEq (.cv w) (synCsn (synCsn (.cv x))))
              (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv z)) C)))))
      (synWex x (synWex y (synWex z (synW3a (.classEq A (synCsn (synCsn (.cv x))))
              (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv z)) C)))))
      (synWex x (synWex y (synWex z (synW3a (.classEq A (synCsn (synCsn (.cv x))))
              (.classEq B (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv z)) C)))))
      t w u (synCins2k C) A B V W
      (by
        exact
          (show w ∉ ((synCins2k C)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
              exact (show w ∉ (C).fv from (by exact fresh_w_not_C)))))
      (by
        exact
          (show u ∉ ((synCins2k C)).fv from
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

/-- Checked nominal proof certificate identified upstream as `g_opkelins3kg`. -/
@[expose]
noncomputable def gOpkelins3kg (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (C : Class) (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv)
    (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_C_z : z ∉ C.fv) (dv_x_y : x ≠ y)
    (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synCins3k C)) (synWex x (synWex y (synWex z
                (synW3a (.classEq A (synCsn (synCsn (.cv x))))
                  (.classEq B (synCopk (.cv y) (.cv z)))
                  (.classMem (synCopk (.cv x) (.cv y)) C))))))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIns3k t w u z y x C
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
  have p0001 := @gEqeq1 (.cv w) A (synCsn (synCsn (.cv x)))
  have p0002 :=
    @gN3anbi1d (.classEq (.cv w) A) (.classEq (.cv w) (synCsn (synCsn (.cv x))))
      (.classEq A (synCsn (synCsn (.cv x))))
      (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
      (.classMem (synCopk (.cv x) (.cv y)) C) p0001
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
    @gN3exbidv (.classEq (.cv w) A)
      (synW3a (.classEq (.cv w) (synCsn (synCsn (.cv x))))
        (.classEq (.cv u) (synCopk (.cv y) (.cv z))) (.classMem (synCopk (.cv x) (.cv y)) C))
      (synW3a (.classEq A (synCsn (synCsn (.cv x))))
        (.classEq (.cv u) (synCopk (.cv y) (.cv z))) (.classMem (synCopk (.cv x) (.cv y)) C))
      x y z freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      p0002
  have p0004 := @gEqeq1 (.cv u) B (synCopk (.cv y) (.cv z))
  have p0005 :=
    @gN3anbi2d (.classEq (.cv u) B) (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
      (.classEq B (synCopk (.cv y) (.cv z))) (.classEq A (synCsn (synCsn (.cv x))))
      (.classMem (synCopk (.cv x) (.cv y)) C) p0004
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
    @gN3exbidv (.classEq (.cv u) B)
      (synW3a (.classEq A (synCsn (synCsn (.cv x))))
        (.classEq (.cv u) (synCopk (.cv y) (.cv z))) (.classMem (synCopk (.cv x) (.cv y)) C))
      (synW3a (.classEq A (synCsn (synCsn (.cv x))))
        (.classEq B (synCopk (.cv y) (.cv z))) (.classMem (synCopk (.cv x) (.cv y)) C))
      x y z freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      p0005
  have freeVariableCertificate6 :
    u ∉
      ((synWex x (synWex y (synWex z (synW3a (.classEq A (synCsn (synCsn (.cv x))))
                (.classEq B (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv y)) C)))))).fv :=
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
      ((synWex x (synWex y (synWex z (synW3a (.classEq (.cv w) (synCsn (synCsn (.cv x))))
                (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv y)) C)))))).fv :=
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
      ((synWex x (synWex y (synWex z (synW3a (.classEq A (synCsn (synCsn (.cv x))))
                (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv y)) C)))))).fv :=
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
    @gOpkelopkabg
      (synWex x (synWex y (synWex z (synW3a (.classEq (.cv w) (synCsn (synCsn (.cv x))))
              (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv y)) C)))))
      (synWex x (synWex y (synWex z (synW3a (.classEq A (synCsn (synCsn (.cv x))))
              (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv y)) C)))))
      (synWex x (synWex y (synWex z (synW3a (.classEq A (synCsn (synCsn (.cv x))))
              (.classEq B (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv y)) C)))))
      t w u (synCins3k C) A B V W
      (by
        exact
          (show w ∉ ((synCins3k C)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
              exact (show w ∉ (C).fv from (by exact fresh_w_not_C)))))
      (by
        exact
          (show u ∉ ((synCins3k C)).fv from
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

/-- Checked nominal proof certificate identified upstream as `g_otkelins2kg`. -/
@[expose]
noncomputable def gOtkelins2kg (A : Class) (B : Class) (C : Class) (D : Class)
    (T : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (.classMem B W) (.classMem C T))
        (synWb (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCins2k D))
          (.classMem (synCopk A C) D))) :=
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
  have p0000 := @gSnex (synCsn A)
  have p0001 := @gOpkex B C
  have freeVariableCertificate0 : x ∉ ((synCsn (synCsn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_A,
      not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((synCsn (synCsn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_y_not_A,
      not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((synCsn (synCsn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_z_not_A,
      not_false_eq_true]
  have freeVariableCertificate3 : x ∉ ((synCopk B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate4 : y ∉ ((synCopk B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_y_not_B, fresh_y_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate5 : z ∉ ((synCopk B C)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_z_not_B, fresh_z_not_C, or_false, not_false_eq_true]
  have p0002 :=
    @gOpkelins2kg x y z (synCsn (synCsn A)) (synCopk B C) D (synCvv) (synCvv)
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      (by exact (show x ∉ (D).fv from (by exact fresh_x_not_D)))
      (by exact (show y ∉ (D).fv from (by exact fresh_y_not_D)))
      (by exact (show z ∉ (D).fv from (by exact fresh_z_not_D)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0003 :=
    @gMp2an (.classMem (synCsn (synCsn A)) (synCvv))
      (.classMem (synCopk B C) (synCvv))
      (synWb (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCins2k D))
        (synWex x (synWex y (synWex z
              (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
                (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv z)) D))))))
      p0000 p0001 p0002
  have p0004 :=
    @gN3anass (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
      (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
      (.classMem (synCopk (.cv x) (.cv z)) D)
  have p0005 := @gEqcom (synCsn (synCsn A)) (synCsn (synCsn (.cv x)))
  have p0006 := @gSnex (.cv x)
  have p0007 := @gSneqb (synCsn (.cv x)) (synCsn A) p0006
  have p0008 := @gVex x
  have p0009 := @gSneqb (.cv x) A p0008
  have p0010 :=
    @gBitri (.classEq (synCsn (synCsn (.cv x))) (synCsn (synCsn A)))
      (.classEq (synCsn (.cv x)) (synCsn A)) (.classEq (.cv x) A) p0007 p0009
  have p0011 :=
    @gBitri (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
      (.classEq (synCsn (synCsn (.cv x))) (synCsn (synCsn A))) (.classEq (.cv x) A)
      p0005 p0010
  have p0012 :=
    @gAnbi1i (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
      (.classEq (.cv x) A)
      (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk (.cv x) (.cv z)) D))
      p0011
  have p0013 :=
    @gBitri
      (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
        (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk (.cv x) (.cv z)) D))
      (synWa (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
        (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
          (.classMem (synCopk (.cv x) (.cv z)) D)))
      (synWa (.classEq (.cv x) A) (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
          (.classMem (synCopk (.cv x) (.cv z)) D)))
      p0004 p0012
  have p0014 :=
    @gN2exbii
      (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
        (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk (.cv x) (.cv z)) D))
      (synWa (.classEq (.cv x) A) (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
          (.classMem (synCopk (.cv x) (.cv z)) D)))
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
    @gN1942vv (.classEq (.cv x) A)
      (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk (.cv x) (.cv z)) D))
      y z freeVariableCertificate6 freeVariableCertificate7
  have p0016 :=
    @gBitri
      (synWex y (synWex z
          (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
            (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk (.cv x) (.cv z)) D))))
      (synWex y (synWex z (synWa (.classEq (.cv x) A)
            (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv z)) D)))))
      (synWa (.classEq (.cv x) A) (synWex y (synWex z
            (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv z)) D)))))
      p0014 p0015
  have p0017 :=
    @gExbii
      (synWex y (synWex z
          (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
            (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk (.cv x) (.cv z)) D))))
      (synWa (.classEq (.cv x) A) (synWex y (synWex z
            (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv z)) D)))))
      x p0016
  have p0018 :=
    @gBitri (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCins2k D))
      (synWex x (synWex y (synWex z
            (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
              (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv z)) D)))))
      (synWex x (synWa (.classEq (.cv x) A) (synWex y (synWex z
              (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv z)) D))))))
      p0003 p0017
  have p0019 := @gOpkeq1 (.cv x) A (.cv z)
  have p0020 :=
    @gEleq1d (.classEq (.cv x) A) (synCopk (.cv x) (.cv z)) (synCopk A (.cv z)) D p0019
  have p0021 :=
    @gAnbi2d (.classEq (.cv x) A) (.classMem (synCopk (.cv x) (.cv z)) D)
      (.classMem (synCopk A (.cv z)) D)
      (.classEq (synCopk B C) (synCopk (.cv y) (.cv z))) p0020
  have p0022 :=
    @gN2exbidv (.classEq (.cv x) A)
      (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk (.cv x) (.cv z)) D))
      (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk A (.cv z)) D))
      y z freeVariableCertificate6 freeVariableCertificate7 p0021
  have freeVariableCertificate8 :
    x ∉
      ((synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk A (.cv z)) D))))).fv :=
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
    @gCeqsexgv
      (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk (.cv x) (.cv z)) D))))
      (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk A (.cv z)) D))))
      x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate8 p0022
  have p0024 :=
    @gN3ad2ant1 (.classMem A V) (.classMem B W)
      (synWb (synWex x (synWa (.classEq (.cv x) A) (synWex y (synWex z
                (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
                  (.classMem (synCopk (.cv x) (.cv z)) D)))))) (synWex y (synWex z
            (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk A (.cv z)) D)))))
      (.classMem C T) p0023
  have p0025 := @gEqcom (synCopk B C) (synCopk (.cv y) (.cv z))
  have p0026 := @gVex y
  have p0027 := @gVex z
  have p0028 := @gOpkthg (.cv y) (.cv z) B C T (synCvv) (synCvv)
  have p0029 :=
    @gMp3an12 (.classMem (.cv y) (synCvv)) (.classMem (.cv z) (synCvv)) (.classMem C T)
      (synWb (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C))
        (synWa (.classEq (.cv y) B) (.classEq (.cv z) C)))
      p0026 p0027 p0028
  have p0030 :=
    @gSyl5bb (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
      (.classEq (synCopk (.cv y) (.cv z)) (synCopk B C)) (.classMem C T)
      (synWa (.classEq (.cv y) B) (.classEq (.cv z) C)) p0025 p0029
  have p0031 :=
    @gAnbi1d (.classMem C T) (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
      (synWa (.classEq (.cv y) B) (.classEq (.cv z) C))
      (.classMem (synCopk A (.cv z)) D) p0030
  have freeVariableCertificate9 : y ∉ ((Wff.classMem C T)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
      fresh_y_not_C, fresh_y_not_T, or_false, not_false_eq_true]
  have freeVariableCertificate10 : z ∉ ((Wff.classMem C T)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
      fresh_z_not_C, fresh_z_not_T, or_false, not_false_eq_true]
  have p0032 :=
    @gN2exbidv (.classMem C T)
      (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk A (.cv z)) D))
      (synWa (synWa (.classEq (.cv y) B) (.classEq (.cv z) C))
        (.classMem (synCopk A (.cv z)) D))
      y z freeVariableCertificate9 freeVariableCertificate10 p0031
  have p0033 :=
    @gAnass (.classEq (.cv y) B) (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D)
  have p0034 :=
    @gExbii
      (synWa (synWa (.classEq (.cv y) B) (.classEq (.cv z) C))
        (.classMem (synCopk A (.cv z)) D))
      (synWa (.classEq (.cv y) B)
        (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D)))
      z p0033
  have freeVariableCertificate11 : z ∉ ((Wff.classEq (.cv y) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_y, fresh_z_not_B, or_false, not_false_eq_true]
  have p0035 :=
    @gN1942v (.classEq (.cv y) B)
      (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D)) z
      freeVariableCertificate11
  have p0036 :=
    @gBitri
      (synWex z (synWa (synWa (.classEq (.cv y) B) (.classEq (.cv z) C))
          (.classMem (synCopk A (.cv z)) D)))
      (synWex z (synWa (.classEq (.cv y) B)
          (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D))))
      (synWa (.classEq (.cv y) B)
        (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D))))
      p0034 p0035
  have p0037 :=
    @gExbii
      (synWex z (synWa (synWa (.classEq (.cv y) B) (.classEq (.cv z) C))
          (.classMem (synCopk A (.cv z)) D)))
      (synWa (.classEq (.cv y) B)
        (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D))))
      y p0036
  have p0038 :=
    @gSyl6bb (.classMem C T)
      (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk A (.cv z)) D))))
      (synWex y (synWex z (synWa (synWa (.classEq (.cv y) B) (.classEq (.cv z) C))
            (.classMem (synCopk A (.cv z)) D))))
      (synWex y (synWa (.classEq (.cv y) B)
          (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D)))))
      p0032 p0037
  have p0039 :=
    @gAdantl (.classMem C T)
      (synWb (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk A (.cv z)) D)))) (synWex y (synWa (.classEq (.cv y) B)
            (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D))))))
      (.classMem B W) p0038
  have p0040 :=
    @gBiidd (.classEq (.cv y) B)
      (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D)))
  have freeVariableCertificate12 :
    y ∉
      ((synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D)))).fv :=
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
    @gCeqsexgv
      (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D)))
      (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D))) y B W
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) freeVariableCertificate12
      p0040
  have p0042 := @gOpkeq2 (.cv z) C A
  have p0043 := @gEleq1d (.classEq (.cv z) C) (synCopk A (.cv z)) (synCopk A C) D p0042
  have freeVariableCertificate13 : z ∉ ((Wff.classMem (synCopk A C) D)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_C, fresh_z_not_D, or_false, not_false_eq_true]
  have p0044 :=
    @gCeqsexgv (.classMem (synCopk A (.cv z)) D) (.classMem (synCopk A C) D) z C T
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C))) freeVariableCertificate13
      p0043
  have p0045 :=
    @gSylan9bb (.classMem B W)
      (synWex y (synWa (.classEq (.cv y) B)
          (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D)))))
      (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D)))
      (.classMem C T) (.classMem (synCopk A C) D) p0041 p0044
  have p0046 :=
    @gBitrd (synWa (.classMem B W) (.classMem C T))
      (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk A (.cv z)) D))))
      (synWex y (synWa (.classEq (.cv y) B)
          (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv z)) D)))))
      (.classMem (synCopk A C) D) p0039 p0045
  have p0047 :=
    @gN3adant1 (.classMem B W) (.classMem C T)
      (synWb (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk A (.cv z)) D)))) (.classMem (synCopk A C) D))
      (.classMem A V) p0046
  have p0048 :=
    @gBitrd (synW3a (.classMem A V) (.classMem B W) (.classMem C T))
      (synWex x (synWa (.classEq (.cv x) A) (synWex y (synWex z
              (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv z)) D))))))
      (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk A (.cv z)) D))))
      (.classMem (synCopk A C) D) p0024 p0047
  have p0049 :=
    @gSyl5bb (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCins2k D))
      (synWex x (synWa (.classEq (.cv x) A) (synWex y (synWex z
              (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv z)) D))))))
      (synW3a (.classMem A V) (.classMem B W) (.classMem C T))
      (.classMem (synCopk A C) D) p0018 p0048
  exact p0049


end NFChoice.DirectNominalPrf.WPPReplay

end
