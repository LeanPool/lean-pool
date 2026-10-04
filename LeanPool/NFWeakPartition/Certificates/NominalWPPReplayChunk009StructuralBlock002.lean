/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart007`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_otkelins3kg`. -/
@[expose]
noncomputable def gOtkelins3kg (A : Class) (B : Class) (C : Class) (D : Class)
    (T : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem A V) (.classMem B W) (.classMem C T))
        (synWb (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCins3k D))
          (.classMem (synCopk A B) D))) :=
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
    @gOpkelins3kg x y z (synCsn (synCsn A)) (synCopk B C) D (synCvv) (synCvv)
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
      (synWb (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCins3k D))
        (synWex x (synWex y (synWex z
              (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
                (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv y)) D))))))
      p0000 p0001 p0002
  have p0004 :=
    @gN3anass (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
      (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
      (.classMem (synCopk (.cv x) (.cv y)) D)
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
        (.classMem (synCopk (.cv x) (.cv y)) D))
      p0011
  have p0013 :=
    @gBitri
      (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
        (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk (.cv x) (.cv y)) D))
      (synWa (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
        (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
          (.classMem (synCopk (.cv x) (.cv y)) D)))
      (synWa (.classEq (.cv x) A) (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
          (.classMem (synCopk (.cv x) (.cv y)) D)))
      p0004 p0012
  have p0014 :=
    @gN2exbii
      (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
        (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk (.cv x) (.cv y)) D))
      (synWa (.classEq (.cv x) A) (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
          (.classMem (synCopk (.cv x) (.cv y)) D)))
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
        (.classMem (synCopk (.cv x) (.cv y)) D))
      y z freeVariableCertificate6 freeVariableCertificate7
  have p0016 :=
    @gBitri
      (synWex y (synWex z
          (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
            (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk (.cv x) (.cv y)) D))))
      (synWex y (synWex z (synWa (.classEq (.cv x) A)
            (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv y)) D)))))
      (synWa (.classEq (.cv x) A) (synWex y (synWex z
            (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv y)) D)))))
      p0014 p0015
  have p0017 :=
    @gExbii
      (synWex y (synWex z
          (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
            (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk (.cv x) (.cv y)) D))))
      (synWa (.classEq (.cv x) A) (synWex y (synWex z
            (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv y)) D)))))
      x p0016
  have p0018 := @gOpkeq1 (.cv x) A (.cv y)
  have p0019 :=
    @gEleq1d (.classEq (.cv x) A) (synCopk (.cv x) (.cv y)) (synCopk A (.cv y)) D p0018
  have p0020 :=
    @gAnbi2d (.classEq (.cv x) A) (.classMem (synCopk (.cv x) (.cv y)) D)
      (.classMem (synCopk A (.cv y)) D)
      (.classEq (synCopk B C) (synCopk (.cv y) (.cv z))) p0019
  have p0021 :=
    @gN2exbidv (.classEq (.cv x) A)
      (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk (.cv x) (.cv y)) D))
      (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk A (.cv y)) D))
      y z freeVariableCertificate6 freeVariableCertificate7 p0020
  have freeVariableCertificate8 :
    x ∉
      ((synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk A (.cv y)) D))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, fresh_x_not_B, fresh_x_not_C, fresh_x_ne_y, fresh_x_ne_z,
      fresh_x_not_A, fresh_x_not_D, or_false, and_false, not_false_eq_true]
  have p0022 :=
    @gCeqsexgv
      (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk (.cv x) (.cv y)) D))))
      (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk A (.cv y)) D))))
      x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate8 p0021
  have p0023 :=
    @gSyl5bb
      (synWex x (synWex y (synWex z
            (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
              (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv y)) D)))))
      (synWex x (synWa (.classEq (.cv x) A) (synWex y (synWex z
              (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv y)) D))))))
      (.classMem A V)
      (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk A (.cv y)) D))))
      p0017 p0022
  have p0024 :=
    @gN3ad2ant1 (.classMem A V) (.classMem B W)
      (synWb (synWex x (synWex y (synWex z
              (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
                (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
                (.classMem (synCopk (.cv x) (.cv y)) D))))) (synWex y (synWex z
            (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk A (.cv y)) D)))))
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
      (.classMem (synCopk A (.cv y)) D) p0030
  have p0032 :=
    @gAnass (.classEq (.cv y) B) (.classEq (.cv z) C) (.classMem (synCopk A (.cv y)) D)
  have p0033 :=
    @gSyl6bb (.classMem C T)
      (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk A (.cv y)) D))
      (synWa (synWa (.classEq (.cv y) B) (.classEq (.cv z) C))
        (.classMem (synCopk A (.cv y)) D))
      (synWa (.classEq (.cv y) B)
        (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv y)) D)))
      p0031 p0032
  have freeVariableCertificate9 : y ∉ ((Wff.classMem C T)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
      fresh_y_not_C, fresh_y_not_T, or_false, not_false_eq_true]
  have freeVariableCertificate10 : z ∉ ((Wff.classMem C T)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
      fresh_z_not_C, fresh_z_not_T, or_false, not_false_eq_true]
  have p0034 :=
    @gN2exbidv (.classMem C T)
      (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
        (.classMem (synCopk A (.cv y)) D))
      (synWa (.classEq (.cv y) B)
        (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv y)) D)))
      y z freeVariableCertificate9 freeVariableCertificate10 p0033
  have freeVariableCertificate11 : z ∉ ((Wff.classEq (.cv y) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_y, fresh_z_not_B, or_false, not_false_eq_true]
  have p0035 :=
    @gExdistr (.classEq (.cv y) B)
      (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv y)) D)) y z
      freeVariableCertificate11
  have p0036 :=
    @gSyl6bb (.classMem C T)
      (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk A (.cv y)) D))))
      (synWex y (synWex z (synWa (.classEq (.cv y) B)
            (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv y)) D)))))
      (synWex y (synWa (.classEq (.cv y) B)
          (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv y)) D)))))
      p0034 p0035
  have p0037 :=
    @gAdantl (.classMem C T)
      (synWb (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk A (.cv y)) D)))) (synWex y (synWa (.classEq (.cv y) B)
            (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv y)) D))))))
      (.classMem B W) p0036
  have p0038 := @gOpkeq2 (.cv y) B A
  have p0039 := @gEleq1d (.classEq (.cv y) B) (synCopk A (.cv y)) (synCopk A B) D p0038
  have p0040 :=
    @gAnbi2d (.classEq (.cv y) B) (.classMem (synCopk A (.cv y)) D)
      (.classMem (synCopk A B) D) (.classEq (.cv z) C) p0039
  have p0041 :=
    @gExbidv (.classEq (.cv y) B)
      (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv y)) D))
      (synWa (.classEq (.cv z) C) (.classMem (synCopk A B) D)) z
      freeVariableCertificate11 p0040
  have freeVariableCertificate12 :
    y ∉ ((synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A B) D)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_C, fresh_y_not_A,
      fresh_y_not_B, fresh_y_not_D, or_false, and_false, not_false_eq_true]
  have p0042 :=
    @gCeqsexgv
      (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv y)) D)))
      (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A B) D))) y B W
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) freeVariableCertificate12
      p0041
  have p0043 := @gBiidd (.classEq (.cv z) C) (.classMem (synCopk A B) D)
  have freeVariableCertificate13 : z ∉ ((Wff.classMem (synCopk A B) D)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, fresh_z_not_D, or_false, not_false_eq_true]
  have p0044 :=
    @gCeqsexgv (.classMem (synCopk A B) D) (.classMem (synCopk A B) D) z C T
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C))) freeVariableCertificate13
      p0043
  have p0045 :=
    @gSylan9bb (.classMem B W)
      (synWex y (synWa (.classEq (.cv y) B)
          (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv y)) D)))))
      (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A B) D)))
      (.classMem C T) (.classMem (synCopk A B) D) p0042 p0044
  have p0046 :=
    @gBitrd (synWa (.classMem B W) (.classMem C T))
      (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk A (.cv y)) D))))
      (synWex y (synWa (.classEq (.cv y) B)
          (synWex z (synWa (.classEq (.cv z) C) (.classMem (synCopk A (.cv y)) D)))))
      (.classMem (synCopk A B) D) p0037 p0045
  have p0047 :=
    @gN3adant1 (.classMem B W) (.classMem C T)
      (synWb (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk A (.cv y)) D)))) (.classMem (synCopk A B) D))
      (.classMem A V) p0046
  have p0048 :=
    @gBitrd (synW3a (.classMem A V) (.classMem B W) (.classMem C T))
      (synWex x (synWex y (synWex z
            (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
              (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv y)) D)))))
      (synWex y (synWex z (synWa (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
            (.classMem (synCopk A (.cv y)) D))))
      (.classMem (synCopk A B) D) p0024 p0047
  have p0049 :=
    @gSyl5bb (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCins3k D))
      (synWex x (synWex y (synWex z
            (synW3a (.classEq (synCsn (synCsn A)) (synCsn (synCsn (.cv x))))
              (.classEq (synCopk B C) (synCopk (.cv y) (.cv z)))
              (.classMem (synCopk (.cv x) (.cv y)) D)))))
      (synW3a (.classMem A V) (.classMem B W) (.classMem C T))
      (.classMem (synCopk A B) D) p0003 p0048
  exact p0049

/-- Checked nominal proof certificate identified upstream as `g_otkelins2k`. -/
@[expose]
noncomputable def gOtkelins2k (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_otkelinsk_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_otkelinsk_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_otkelinsk_3 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCins2k D))
        (.classMem (synCopk A C) D)) :=
  by
  have p0000 := @gOtkelins2kg A B C D (synCvv) (synCvv) (synCvv)
  have p0001 :=
    @gMp3an (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv))
      (synWb (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCins2k D))
        (.classMem (synCopk A C) D))
      hyp_otkelinsk_1 hyp_otkelinsk_2 hyp_otkelinsk_3 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_otkelins3k`. -/
@[expose]
noncomputable def gOtkelins3k (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_otkelinsk_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_otkelinsk_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_otkelinsk_3 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCins3k D))
        (.classMem (synCopk A B) D)) :=
  by
  have p0000 := @gOtkelins3kg A B C D (synCvv) (synCvv) (synCvv)
  have p0001 :=
    @gMp3an (.classMem A (synCvv)) (.classMem B (synCvv)) (.classMem C (synCvv))
      (synWb (.classMem (synCopk (synCsn (synCsn A)) (synCopk B C)) (synCins3k D))
        (.classMem (synCopk A B) D))
      hyp_otkelinsk_1 hyp_otkelinsk_2 hyp_otkelinsk_3 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elimakg`. -/
@[expose]
noncomputable def gElimakg (y : Var) (A : Class) (B : Class) (C : Class) (V : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv) :
    Nominal.NPrf
      (.imp (.classMem C V) (synWb (.classMem C (synCimak A B))
          (synWrex y B (.classMem (synCopk (.cv y) C) A)))) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_y : x ≠ y := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have p0000 := @gOpkeq2 (.cv x) C (.cv y)
  have p0001 :=
    @gEleq1d (.classEq (.cv x) C) (synCopk (.cv y) (.cv x)) (synCopk (.cv y) C) A p0000
  have freeVariableCertificate0 : y ∉ ((Wff.classEq (.cv x) C)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_x, dv_C_y, or_false, not_false_eq_true]
  have p0002 :=
    @gRexbidv (.classEq (.cv x) C) (.classMem (synCopk (.cv y) (.cv x)) A)
      (.classMem (synCopk (.cv y) C) A) y B freeVariableCertificate0 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfImak x y A B
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact dv_B_y)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have freeVariableCertificate1 :
    x ∉ ((synWrex y B (.classMem (synCopk (.cv y) C) A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, fresh_x_not_C, fresh_x_not_A,
      or_false, and_false, not_false_eq_true]
  have p0004 :=
    @gElab2g (synWrex y B (.classMem (synCopk (.cv y) (.cv x)) A))
      (synWrex y B (.classMem (synCopk (.cv y) C) A)) x C (synCimak A B) V
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C))) freeVariableCertificate1
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_elimakvg`. -/
@[expose]
noncomputable def gElimakvg (y : Var) (A : Class) (C : Class) (V : Class)
    (dv_A_y : y ∉ A.fv) (dv_C_y : y ∉ C.fv) :
    Nominal.NPrf
      (.imp (.classMem C V) (synWb (.classMem C (synCimak A (synCvv)))
          (synWex y (.classMem (synCopk (.cv y) C) A)))) :=
  by
  have p0000 :=
    @gElimakg y A (synCvv) C V (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by
        exact
          (show y ∉ ((synCvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
  have p0001 := @gRexv (.classMem (synCopk (.cv y) C) A) y
  have p0002 :=
    @gSyl6bb (.classMem C V) (.classMem C (synCimak A (synCvv)))
      (synWrex y (synCvv) (.classMem (synCopk (.cv y) C) A))
      (synWex y (.classMem (synCopk (.cv y) C) A)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_elimak`. -/
@[expose]
noncomputable def gElimak (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv)
    (hyp_elimak_1 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem C (synCimak A B))
        (synWrex y B (.classMem (synCopk (.cv y) C) A))) :=
  by
  have p0000 :=
    @gElimakg y A B C (synCvv) (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by exact (show y ∉ (B).fv from (by exact dv_B_y)))
      (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
  have p0001 := Nominal.mp hyp_elimak_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elimakv`. -/
@[expose]
noncomputable def gElimakv (y : Var) (A : Class) (C : Class) (dv_A_y : y ∉ A.fv)
    (dv_C_y : y ∉ C.fv) (hyp_elimak_1 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem C (synCimak A (synCvv)))
        (synWex y (.classMem (synCopk (.cv y) C) A))) :=
  by
  have p0000 :=
    @gElimakvg y A C (synCvv) (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
  have p0001 := Nominal.mp hyp_elimak_1 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart008`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_opkelcokg`. -/
@[expose]
noncomputable def gOpkelcokg (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (dv_D_x : x ∉ D.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synCcomk C D)) (synWex x
            (synWa (.classMem (synCopk A (.cv x)) D) (.classMem (synCopk (.cv x) B) C))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ D.fv ∪ V.fv ∪ W.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
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
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_w_not_C : w ∉ C.fv := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
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
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_w_ne_y : w ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have p0000 := @gElex A V
  have p0001 := @gElex B W
  have p0002 := (Nominal.classEqRefl (synCcomk C D))
  have p0003 :=
    @gEleq2i (synCcomk C D)
      (synCimak (synCin (synCins2k C) (synCins3k (synCcnvk D))) (synCvv))
      (synCopk A B) p0002
  have p0004 := @gOpkex A B
  have freeVariableCertificate0 :
    y ∉ ((synCin (synCins2k C) (synCins3k (synCcnvk D)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, Finset.mem_union,
      fresh_y_not_C, fresh_y_not_D, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((synCopk A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0005 :=
    @gElimakv y (synCin (synCins2k C) (synCins3k (synCcnvk D))) (synCopk A B)
      freeVariableCertificate0 freeVariableCertificate1 p0004
  have p0006 := @gVex y
  have freeVariableCertificate2 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have freeVariableCertificate3 : z ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_y, not_false_eq_true]
  have freeVariableCertificate4 : w ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_y, not_false_eq_true]
  have freeVariableCertificate5 : x ∉ ((synCopk A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate6 : z ∉ ((synCopk A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate7 : w ∉ ((synCopk A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_w_not_A, fresh_w_not_B, or_false, not_false_eq_true]
  have p0007 :=
    @gOpkelins2kg x z w (.cv y) (synCopk A B) C (synCvv) (synCvv)
      freeVariableCertificate2 freeVariableCertificate3 freeVariableCertificate4
      freeVariableCertificate5 freeVariableCertificate6 freeVariableCertificate7
      (by exact (show x ∉ (C).fv from (by exact dv_C_x)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (by exact (show w ∉ (C).fv from (by exact fresh_w_not_C)))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show z ≠ w from (by exact fresh_z_ne_w))
  have p0008 :=
    @gMp2an (.classMem (.cv y) (synCvv)) (.classMem (synCopk A B) (synCvv))
      (synWb (.classMem (synCopk (.cv y) (synCopk A B)) (synCins2k C)) (synWex x (synWex z
            (synWex w (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv x))))
                (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                (.classMem (synCopk (.cv x) (.cv w)) C))))))
      p0006 p0004 p0007
  have p0009 :=
    @gN3anass (.classEq (.cv y) (synCsn (synCsn (.cv x))))
      (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
      (.classMem (synCopk (.cv x) (.cv w)) C)
  have p0010 :=
    @gN2exbii
      (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv x))))
        (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
        (.classMem (synCopk (.cv x) (.cv w)) C))
      (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x))))
        (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
          (.classMem (synCopk (.cv x) (.cv w)) C)))
      z w p0009
  have freeVariableCertificate8 :
    z ∉ ((Wff.classEq (.cv y) (synCsn (synCsn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate9 :
    w ∉ ((Wff.classEq (.cv y) (synCsn (synCsn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_x, or_false, not_false_eq_true]
  have p0011 :=
    @gN1942vv (.classEq (.cv y) (synCsn (synCsn (.cv x))))
      (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
        (.classMem (synCopk (.cv x) (.cv w)) C))
      z w freeVariableCertificate8 freeVariableCertificate9
  have p0012 :=
    @gBitri
      (synWex z (synWex w (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv x))))
            (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
            (.classMem (synCopk (.cv x) (.cv w)) C))))
      (synWex z (synWex w (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x))))
            (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
              (.classMem (synCopk (.cv x) (.cv w)) C)))))
      (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWex z (synWex w
            (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
              (.classMem (synCopk (.cv x) (.cv w)) C)))))
      p0010 p0011
  have p0013 :=
    @gExbii
      (synWex z (synWex w (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv x))))
            (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
            (.classMem (synCopk (.cv x) (.cv w)) C))))
      (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWex z (synWex w
            (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
              (.classMem (synCopk (.cv x) (.cv w)) C)))))
      x p0012
  have p0014 :=
    @gBitri (.classMem (synCopk (.cv y) (synCopk A B)) (synCins2k C))
      (synWex x (synWex z (synWex w (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv x))))
              (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
              (.classMem (synCopk (.cv x) (.cv w)) C)))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWex z (synWex w
              (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                (.classMem (synCopk (.cv x) (.cv w)) C))))))
      p0008 p0013
  have p0015 :=
    @gAnbi1i (.classMem (synCopk (.cv y) (synCopk A B)) (synCins2k C))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWex z (synWex w
              (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                (.classMem (synCopk (.cv x) (.cv w)) C))))))
      (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D))) p0014
  have p0016 :=
    @gElin (synCopk (.cv y) (synCopk A B)) (synCins2k C) (synCins3k (synCcnvk D))
  have freeVariableCertificate10 :
    x ∉
      ((Wff.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_y, dv_A_x, dv_B_x, dv_D_x, or_false,
      not_false_eq_true]
  have p0017 :=
    @gN1941v
      (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWex z (synWex w
            (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
              (.classMem (synCopk (.cv x) (.cv w)) C)))))
      (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D))) x
      freeVariableCertificate10
  have p0018 :=
    @gN3bitr4i
      (synWa (.classMem (synCopk (.cv y) (synCopk A B)) (synCins2k C))
        (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D))))
      (synWa (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWex z
              (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                  (.classMem (synCopk (.cv x) (.cv w)) C))))))
        (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D))))
      (.classMem (synCopk (.cv y) (synCopk A B))
        (synCin (synCins2k C) (synCins3k (synCcnvk D))))
      (synWex x (synWa (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWex z
              (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                  (.classMem (synCopk (.cv x) (.cv w)) C)))))
          (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D)))))
      p0015 p0016 p0017
  have p0019 :=
    @gExbii
      (.classMem (synCopk (.cv y) (synCopk A B))
        (synCin (synCins2k C) (synCins3k (synCcnvk D))))
      (synWex x (synWa (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWex z
              (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                  (.classMem (synCopk (.cv x) (.cv w)) C)))))
          (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D)))))
      y p0018
  have p0020 :=
    @gExcom
      (synWa (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWex z (synWex w
              (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                (.classMem (synCopk (.cv x) (.cv w)) C)))))
        (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D))))
      y x
  have p0021 :=
    @gAnass (.classEq (.cv y) (synCsn (synCsn (.cv x))))
      (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
            (.classMem (synCopk (.cv x) (.cv w)) C))))
      (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D)))
  have p0022 :=
    @gExbii
      (synWa (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWex z (synWex w
              (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                (.classMem (synCopk (.cv x) (.cv w)) C)))))
        (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D))))
      (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWa (synWex z (synWex w
              (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                (.classMem (synCopk (.cv x) (.cv w)) C))))
          (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D)))))
      y p0021
  have p0023 := @gSnex (synCsn (.cv x))
  have p0024 := @gOpkeq1 (.cv y) (synCsn (synCsn (.cv x))) (synCopk A B)
  have p0025 :=
    @gEleq1d (.classEq (.cv y) (synCsn (synCsn (.cv x))))
      (synCopk (.cv y) (synCopk A B))
      (synCopk (synCsn (synCsn (.cv x))) (synCopk A B)) (synCins3k (synCcnvk D))
      p0024
  have p0026 :=
    @gAnbi2d (.classEq (.cv y) (synCsn (synCsn (.cv x))))
      (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D)))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
        (synCins3k (synCcnvk D)))
      (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
            (.classMem (synCopk (.cv x) (.cv w)) C))))
      p0025
  have freeVariableCertificate11 : y ∉ ((synCsn (synCsn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate12 :
    y ∉
      ((synWa (synWex z (synWex w
              (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                (.classMem (synCopk (.cv x) (.cv w)) C))))
          (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
            (synCins3k (synCcnvk D))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_z,
      fresh_y_ne_w, fresh_y_ne_x, fresh_y_not_C, fresh_y_not_D, or_false, and_false,
      not_false_eq_true]
  have p0027 :=
    @gCeqsexv
      (synWa (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
              (.classMem (synCopk (.cv x) (.cv w)) C))))
        (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D))))
      (synWa (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
              (.classMem (synCopk (.cv x) (.cv w)) C))))
        (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
          (synCins3k (synCcnvk D))))
      y (synCsn (synCsn (.cv x))) freeVariableCertificate11 freeVariableCertificate12
      p0023 p0026
  have p0028 :=
    @gBitri
      (synWex y (synWa (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWex z
              (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                  (.classMem (synCopk (.cv x) (.cv w)) C)))))
          (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D)))))
      (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWa (synWex z
              (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                  (.classMem (synCopk (.cv x) (.cv w)) C))))
            (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D))))))
      (synWa (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
              (.classMem (synCopk (.cv x) (.cv w)) C))))
        (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
          (synCins3k (synCcnvk D))))
      p0022 p0027
  have p0029 :=
    @gExbii
      (synWex y (synWa (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x)))) (synWex z
              (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                  (.classMem (synCopk (.cv x) (.cv w)) C)))))
          (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D)))))
      (synWa (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
              (.classMem (synCopk (.cv x) (.cv w)) C))))
        (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
          (synCins3k (synCcnvk D))))
      x p0028
  have p0030 :=
    @gN3bitri
      (synWex y (.classMem (synCopk (.cv y) (synCopk A B))
          (synCin (synCins2k C) (synCins3k (synCcnvk D)))))
      (synWex y (synWex x (synWa (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x))))
              (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                    (.classMem (synCopk (.cv x) (.cv w)) C)))))
            (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D))))))
      (synWex x (synWex y (synWa (synWa (.classEq (.cv y) (synCsn (synCsn (.cv x))))
              (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                    (.classMem (synCopk (.cv x) (.cv w)) C)))))
            (.classMem (synCopk (.cv y) (synCopk A B)) (synCins3k (synCcnvk D))))))
      (synWex x (synWa (synWex z (synWex w
              (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                (.classMem (synCopk (.cv x) (.cv w)) C))))
          (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
            (synCins3k (synCcnvk D)))))
      p0019 p0020 p0029
  have p0031 :=
    @gN3bitri (.classMem (synCopk A B) (synCcomk C D))
      (.classMem (synCopk A B)
        (synCimak (synCin (synCins2k C) (synCins3k (synCcnvk D))) (synCvv)))
      (synWex y (.classMem (synCopk (.cv y) (synCopk A B))
          (synCin (synCins2k C) (synCins3k (synCcnvk D)))))
      (synWex x (synWa (synWex z (synWex w
              (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                (.classMem (synCopk (.cv x) (.cv w)) C))))
          (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
            (synCins3k (synCcnvk D)))))
      p0003 p0005 p0030
  have p0032 :=
    @gAncom
      (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
            (.classMem (synCopk (.cv x) (.cv w)) C))))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
        (synCins3k (synCcnvk D)))
  have p0033 := @gVex x
  have p0034 := @gOtkelins3kg (.cv x) A B (synCcnvk D) (synCvv) (synCvv) (synCvv)
  have p0035 :=
    @gMp3an1 (.classMem (.cv x) (synCvv)) (.classMem A (synCvv))
      (.classMem B (synCvv))
      (synWb (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
          (synCins3k (synCcnvk D))) (.classMem (synCopk (.cv x) A) (synCcnvk D)))
      p0033 p0034
  have p0036 := @gOpkelcnvkg (.cv x) A D (synCvv) (synCvv)
  have p0037 :=
    @gMpan (.classMem (.cv x) (synCvv)) (.classMem A (synCvv))
      (synWb (.classMem (synCopk (.cv x) A) (synCcnvk D)) (.classMem (synCopk A (.cv x)) D))
      p0033 p0036
  have p0038 :=
    @gAdantr (.classMem A (synCvv))
      (synWb (.classMem (synCopk (.cv x) A) (synCcnvk D)) (.classMem (synCopk A (.cv x)) D))
      (.classMem B (synCvv)) p0037
  have p0039 :=
    @gBitrd (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
        (synCins3k (synCcnvk D)))
      (.classMem (synCopk (.cv x) A) (synCcnvk D)) (.classMem (synCopk A (.cv x)) D)
      p0035 p0038
  have p0040 := @gEqcom (synCopk A B) (synCopk (.cv z) (.cv w))
  have p0041 :=
    @gAnbi1i (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
      (.classEq (synCopk (.cv z) (.cv w)) (synCopk A B))
      (.classMem (synCopk (.cv x) (.cv w)) C) p0040
  have p0042 :=
    @gN2exbii
      (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
        (.classMem (synCopk (.cv x) (.cv w)) C))
      (synWa (.classEq (synCopk (.cv z) (.cv w)) (synCopk A B))
        (.classMem (synCopk (.cv x) (.cv w)) C))
      z w p0041
  have p0043 := @gVex z
  have p0044 := @gVex w
  have p0045 := @gOpkthg (.cv z) (.cv w) A B (synCvv) (synCvv) (synCvv)
  have p0046 :=
    @gMp3an12 (.classMem (.cv z) (synCvv)) (.classMem (.cv w) (synCvv))
      (.classMem B (synCvv))
      (synWb (.classEq (synCopk (.cv z) (.cv w)) (synCopk A B))
        (synWa (.classEq (.cv z) A) (.classEq (.cv w) B)))
      p0043 p0044 p0045
  have p0047 :=
    @gAnbi1d (.classMem B (synCvv)) (.classEq (synCopk (.cv z) (.cv w)) (synCopk A B))
      (synWa (.classEq (.cv z) A) (.classEq (.cv w) B))
      (.classMem (synCopk (.cv x) (.cv w)) C) p0046
  have p0048 :=
    @gAnass (.classEq (.cv z) A) (.classEq (.cv w) B)
      (.classMem (synCopk (.cv x) (.cv w)) C)
  have p0049 :=
    @gSyl6bb (.classMem B (synCvv))
      (synWa (.classEq (synCopk (.cv z) (.cv w)) (synCopk A B))
        (.classMem (synCopk (.cv x) (.cv w)) C))
      (synWa (synWa (.classEq (.cv z) A) (.classEq (.cv w) B))
        (.classMem (synCopk (.cv x) (.cv w)) C))
      (synWa (.classEq (.cv z) A)
        (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C)))
      p0047 p0048
  have freeVariableCertificate13 : z ∉ ((Wff.classMem B (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_z_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate14 : w ∉ ((Wff.classMem B (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_w_not_B, or_false, not_false_eq_true]
  have p0050 :=
    @gN2exbidv (.classMem B (synCvv))
      (synWa (.classEq (synCopk (.cv z) (.cv w)) (synCopk A B))
        (.classMem (synCopk (.cv x) (.cv w)) C))
      (synWa (.classEq (.cv z) A)
        (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C)))
      z w freeVariableCertificate13 freeVariableCertificate14 p0049
  have p0051 :=
    @gAdantl (.classMem B (synCvv))
      (synWb (synWex z (synWex w (synWa (.classEq (synCopk (.cv z) (.cv w)) (synCopk A B))
              (.classMem (synCopk (.cv x) (.cv w)) C)))) (synWex z (synWex w
            (synWa (.classEq (.cv z) A)
              (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C))))))
      (.classMem A (synCvv)) p0050
  have freeVariableCertificate15 : w ∉ ((Wff.classEq (.cv z) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_z, fresh_w_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate16 :
    z ∉ ((synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, fresh_z_ne_w, fresh_z_not_B, fresh_z_ne_x, fresh_z_not_C,
      or_false, not_false_eq_true]
  have p0052 :=
    @gEeanv (.classEq (.cv z) A)
      (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C)) z w
      freeVariableCertificate15 freeVariableCertificate16
  have p0053 :=
    @gSyl6bb (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWex z (synWex w (synWa (.classEq (synCopk (.cv z) (.cv w)) (synCopk A B))
            (.classMem (synCopk (.cv x) (.cv w)) C))))
      (synWex z (synWex w (synWa (.classEq (.cv z) A)
            (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C)))))
      (synWa (synWex z (.classEq (.cv z) A)) (synWex w
          (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C))))
      p0051 p0052
  have p0054 :=
    @gSyl5bb
      (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
            (.classMem (synCopk (.cv x) (.cv w)) C))))
      (synWex z (synWex w (synWa (.classEq (synCopk (.cv z) (.cv w)) (synCopk A B))
            (.classMem (synCopk (.cv x) (.cv w)) C))))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWa (synWex z (.classEq (.cv z) A)) (synWex w
          (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C))))
      p0042 p0053
  have p0055 :=
    @gElisset z A (synCvv) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
  have p0056 :=
    @gBiantrurd (.classMem A (synCvv)) (synWex z (.classEq (.cv z) A))
      (synWex w (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C)))
      p0055
  have p0057 :=
    @gBicomd (.classMem A (synCvv))
      (synWex w (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C)))
      (synWa (synWex z (.classEq (.cv z) A)) (synWex w
          (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C))))
      p0056
  have p0058 := @gOpkeq2 (.cv w) B (.cv x)
  have p0059 :=
    @gEleq1d (.classEq (.cv w) B) (synCopk (.cv x) (.cv w)) (synCopk (.cv x) B) C p0058
  have freeVariableCertificate17 : w ∉ ((Wff.classMem (synCopk (.cv x) B) C)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_x, fresh_w_not_B, fresh_w_not_C, or_false, not_false_eq_true]
  have p0060 :=
    @gCeqsexgv (.classMem (synCopk (.cv x) (.cv w)) C)
      (.classMem (synCopk (.cv x) B) C) w B (synCvv)
      (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) freeVariableCertificate17
      p0059
  have p0061 :=
    @gSylan9bb (.classMem A (synCvv))
      (synWa (synWex z (.classEq (.cv z) A)) (synWex w
          (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C))))
      (synWex w (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C)))
      (.classMem B (synCvv)) (.classMem (synCopk (.cv x) B) C) p0057 p0060
  have p0062 :=
    @gBitrd (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
            (.classMem (synCopk (.cv x) (.cv w)) C))))
      (synWa (synWex z (.classEq (.cv z) A)) (synWex w
          (synWa (.classEq (.cv w) B) (.classMem (synCopk (.cv x) (.cv w)) C))))
      (.classMem (synCopk (.cv x) B) C) p0054 p0061
  have p0063 :=
    @gAnbi12d (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
        (synCins3k (synCcnvk D)))
      (.classMem (synCopk A (.cv x)) D)
      (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
            (.classMem (synCopk (.cv x) (.cv w)) C))))
      (.classMem (synCopk (.cv x) B) C) p0039 p0062
  have p0064 :=
    @gSyl5bb
      (synWa (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
              (.classMem (synCopk (.cv x) (.cv w)) C))))
        (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
          (synCins3k (synCcnvk D))))
      (synWa (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
          (synCins3k (synCcnvk D))) (synWex z (synWex w
            (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
              (.classMem (synCopk (.cv x) (.cv w)) C)))))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWa (.classMem (synCopk A (.cv x)) D) (.classMem (synCopk (.cv x) B) C)) p0032
      p0063
  have freeVariableCertificate18 :
    x ∉ ((synWa (.classMem A (synCvv)) (.classMem B (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have p0065 :=
    @gExbidv (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWa (synWex z (synWex w (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
              (.classMem (synCopk (.cv x) (.cv w)) C))))
        (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
          (synCins3k (synCcnvk D))))
      (synWa (.classMem (synCopk A (.cv x)) D) (.classMem (synCopk (.cv x) B) C)) x
      freeVariableCertificate18 p0064
  have p0066 :=
    @gSyl5bb (.classMem (synCopk A B) (synCcomk C D))
      (synWex x (synWa (synWex z (synWex w
              (synWa (.classEq (synCopk A B) (synCopk (.cv z) (.cv w)))
                (.classMem (synCopk (.cv x) (.cv w)) C))))
          (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk A B))
            (synCins3k (synCcnvk D)))))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWex x (synWa (.classMem (synCopk A (.cv x)) D) (.classMem (synCopk (.cv x) B) C)))
      p0031 p0065
  have p0067 :=
    @gSyl2an (.classMem A V) (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (.classMem (synCopk A B) (synCcomk C D)) (synWex x
          (synWa (.classMem (synCopk A (.cv x)) D) (.classMem (synCopk (.cv x) B) C))))
      (.classMem B W) p0000 p0001 p0066
  exact p0067

/-- Checked nominal proof certificate identified upstream as `g_opkelcok`. -/
@[expose]
noncomputable def gOpkelcok (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (hyp_opkelcok_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opkelcok_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk A B) (synCcomk C D)) (synWex x
          (synWa (.classMem (synCopk A (.cv x)) D) (.classMem (synCopk (.cv x) B) C)))) :=
  by
  have p0000 :=
    @gOpkelcokg x A B C D (synCvv) (synCvv)
      (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
      (by exact (show x ∉ (C).fv from (by exact dv_C_x)))
      (by exact (show x ∉ (D).fv from (by exact dv_D_x)))
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (.classMem (synCopk A B) (synCcomk C D)) (synWex x
          (synWa (.classMem (synCopk A (.cv x)) D) (.classMem (synCopk (.cv x) B) C))))
      hyp_opkelcok_1 hyp_opkelcok_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elp6`. -/
@[expose]
noncomputable def gElp6 (x : Var) (A : Class) (B : Class) (V : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem A V) (synWb (.classMem A (synCp6 B))
          (.all x (.classMem (synCopk (.cv x) (synCsn A)) B)))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ V.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have p0000 := @gSneq (.cv y) A
  have p0001 := @gSneqd (.classEq (.cv y) A) (synCsn (.cv y)) (synCsn A) p0000
  have p0002 :=
    @gXpkeq2d (.classEq (.cv y) A) (synCsn (synCsn (.cv y))) (synCsn (synCsn A))
      (synCvv) p0001
  have p0003 :=
    @gSseq1d (.classEq (.cv y) A) (synCxpk (synCvv) (synCsn (synCsn (.cv y))))
      (synCxpk (synCvv) (synCsn (synCsn A))) B p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfP6 y B
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have freeVariableCertificate0 :
    y ∉ ((synWss (synCxpk (synCvv) (synCsn (synCsn A))) B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0005 :=
    @gElab2g (synWss (synCxpk (synCvv) (synCsn (synCsn (.cv y)))) B)
      (synWss (synCxpk (synCvv) (synCsn (synCsn A))) B) y A (synCp6 B) V
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate0
      p0003 p0004
  have p0006 := @gXpkssvvk (synCvv) (synCsn (synCsn A))
  have freeVariableCertificate1 : x ∉ ((synCxpk (synCvv) (synCsn (synCsn A)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate2 : y ∉ ((synCxpk (synCvv) (synCsn (synCsn A)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_A, or_false, not_false_eq_true]
  have p0007 :=
    @gSsrelk x y (synCxpk (synCvv) (synCsn (synCsn A))) B freeVariableCertificate1
      freeVariableCertificate2 (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @gVex x
  have p0010 := @gVex y
  have p0011 := @gOpkelxpk (.cv x) (.cv y) (synCvv) (synCsn (synCsn A)) p0009 p0010
  have p0012 :=
    @gBiantrur (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCsn (synCsn A)))
      p0009
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn y (synCsn A)
      (by
        exact
          (show y ∉ ((synCsn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
  have p0014 := @gEqabri (.classEq (.cv y) (synCsn A)) y (synCsn (synCsn A)) p0013
  have p0015 :=
    @gN3bitr2i
      (.classMem (synCopk (.cv x) (.cv y)) (synCxpk (synCvv) (synCsn (synCsn A))))
      (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCsn (synCsn A))))
      (.classMem (.cv y) (synCsn (synCsn A))) (.classEq (.cv y) (synCsn A)) p0011 p0012
      p0014
  have p0016 :=
    @gImbi1i
      (.classMem (synCopk (.cv x) (.cv y)) (synCxpk (synCvv) (synCsn (synCsn A))))
      (.classEq (.cv y) (synCsn A)) (.classMem (synCopk (.cv x) (.cv y)) B) p0015
  have p0017 :=
    @gAlbii
      (.imp (.classMem (synCopk (.cv x) (.cv y)) (synCxpk (synCvv) (synCsn (synCsn A))))
        (.classMem (synCopk (.cv x) (.cv y)) B))
      (.imp (.classEq (.cv y) (synCsn A)) (.classMem (synCopk (.cv x) (.cv y)) B)) y
      p0016
  have p0018 := @gSnex A
  have p0019 := @gOpkeq2 (.cv y) (synCsn A) (.cv x)
  have p0020 :=
    @gEleq1d (.classEq (.cv y) (synCsn A)) (synCopk (.cv x) (.cv y))
      (synCopk (.cv x) (synCsn A)) B p0019
  have freeVariableCertificate3 :
    y ∉ ((Wff.classMem (synCopk (.cv x) (synCsn A)) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, fresh_y_not_B, or_false,
      not_false_eq_true]
  have p0021 :=
    @gCeqsalv (.classMem (synCopk (.cv x) (.cv y)) B)
      (.classMem (synCopk (.cv x) (synCsn A)) B) y (synCsn A)
      (by
        exact
          (show y ∉ ((synCsn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
      freeVariableCertificate3 p0018 p0020
  have p0022 :=
    @gBitri
      (.all y (.imp (.classMem (synCopk (.cv x) (.cv y))
            (synCxpk (synCvv) (synCsn (synCsn A))))
          (.classMem (synCopk (.cv x) (.cv y)) B)))
      (.all y (.imp (.classEq (.cv y) (synCsn A)) (.classMem (synCopk (.cv x) (.cv y)) B)))
      (.classMem (synCopk (.cv x) (synCsn A)) B) p0017 p0021
  have p0023 :=
    @gAlbii
      (.all y (.imp (.classMem (synCopk (.cv x) (.cv y))
            (synCxpk (synCvv) (synCsn (synCsn A))))
          (.classMem (synCopk (.cv x) (.cv y)) B)))
      (.classMem (synCopk (.cv x) (synCsn A)) B) x p0022
  have p0024 :=
    @gBitri (synWss (synCxpk (synCvv) (synCsn (synCsn A))) B)
      (.all x (.all y (.imp (.classMem (synCopk (.cv x) (.cv y))
              (synCxpk (synCvv) (synCsn (synCsn A))))
            (.classMem (synCopk (.cv x) (.cv y)) B))))
      (.all x (.classMem (synCopk (.cv x) (synCsn A)) B)) p0008 p0023
  have p0025 :=
    @gSyl6bb (.classMem A V) (.classMem A (synCp6 B))
      (synWss (synCxpk (synCvv) (synCsn (synCsn A))) B)
      (.all x (.classMem (synCopk (.cv x) (synCsn A)) B)) p0005 p0024
  exact p0025


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart009`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_opkelsikg`. -/
@[expose]
noncomputable def gOpkelsikg (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synCsik C)) (synWex x (synWex y
              (synW3a (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y)))
                (.classMem (synCopk (.cv x) (.cv y)) C)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
  let t : Var := freshVar proofSupport 0
  let u : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
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
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_u_ne_x : u ≠ x := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_u : x ≠ u := Ne.symm fresh_u_ne_x
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
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
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_z : t ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have fresh_u_ne_z : u ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_u : z ≠ u := Ne.symm fresh_u_ne_z
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSik z t u y x C
      (by exact (show x ∉ (C).fv from (by exact dv_C_x)))
      (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (by exact (show t ∉ (C).fv from (by exact fresh_t_not_C)))
      (by exact (show u ∉ (C).fv from (by exact fresh_u_not_C)))
      (show x ≠ y from (by exact dv_x_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show x ≠ t from (by exact fresh_x_ne_t)) (show x ≠ u from (by exact fresh_x_ne_u))
      (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ t from (by exact fresh_y_ne_t))
      (show y ≠ u from (by exact fresh_y_ne_u)) (show z ≠ t from (by exact fresh_z_ne_t))
      (show z ≠ u from (by exact fresh_z_ne_u)) (show t ≠ u from (by exact fresh_t_ne_u))
  have p0001 := @gEqeq1 (.cv t) A (synCsn (.cv x))
  have p0002 :=
    @gN3anbi1d (.classEq (.cv t) A) (.classEq (.cv t) (synCsn (.cv x)))
      (.classEq A (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
      (.classMem (synCopk (.cv x) (.cv y)) C) p0001
  have freeVariableCertificate0 : x ∉ ((Wff.classEq (.cv t) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_t, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((Wff.classEq (.cv t) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_t, dv_A_y, or_false, not_false_eq_true]
  have p0003 :=
    @gN2exbidv (.classEq (.cv t) A)
      (synW3a (.classEq (.cv t) (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (.classMem (synCopk (.cv x) (.cv y)) C))
      (synW3a (.classEq A (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (.classMem (synCopk (.cv x) (.cv y)) C))
      x y freeVariableCertificate0 freeVariableCertificate1 p0002
  have p0004 := @gEqeq1 (.cv u) B (synCsn (.cv y))
  have p0005 :=
    @gN3anbi2d (.classEq (.cv u) B) (.classEq (.cv u) (synCsn (.cv y)))
      (.classEq B (synCsn (.cv y))) (.classEq A (synCsn (.cv x)))
      (.classMem (synCopk (.cv x) (.cv y)) C) p0004
  have freeVariableCertificate2 : x ∉ ((Wff.classEq (.cv u) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_u, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((Wff.classEq (.cv u) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_u, dv_B_y, or_false, not_false_eq_true]
  have p0006 :=
    @gN2exbidv (.classEq (.cv u) B)
      (synW3a (.classEq A (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
        (.classMem (synCopk (.cv x) (.cv y)) C))
      (synW3a (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y)))
        (.classMem (synCopk (.cv x) (.cv y)) C))
      x y freeVariableCertificate2 freeVariableCertificate3 p0005
  have freeVariableCertificate4 :
    u ∉
      ((synWex x (synWex y
            (synW3a (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y)))
              (.classMem (synCopk (.cv x) (.cv y)) C))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, fresh_u_not_C,
      fresh_u_not_A, fresh_u_not_B, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate5 :
    z ∉
      ((synWex x (synWex y (synW3a (.classEq (.cv t) (synCsn (.cv x)))
              (.classEq (.cv u) (synCsn (.cv y)))
              (.classMem (synCopk (.cv x) (.cv y)) C))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_C,
      fresh_z_ne_t, fresh_z_ne_u, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate6 :
    t ∉
      ((synWex x (synWex y
            (synW3a (.classEq A (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
              (.classMem (synCopk (.cv x) (.cv y)) C))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, fresh_t_not_C,
      fresh_t_not_A, fresh_t_ne_u, or_false, and_false, not_false_eq_true]
  have p0007 :=
    @gOpkelopkabg
      (synWex x (synWex y (synW3a (.classEq (.cv t) (synCsn (.cv x)))
            (.classEq (.cv u) (synCsn (.cv y))) (.classMem (synCopk (.cv x) (.cv y)) C))))
      (synWex x (synWex y
          (synW3a (.classEq A (synCsn (.cv x))) (.classEq (.cv u) (synCsn (.cv y)))
            (.classMem (synCopk (.cv x) (.cv y)) C))))
      (synWex x (synWex y
          (synW3a (.classEq A (synCsn (.cv x))) (.classEq B (synCsn (.cv y)))
            (.classMem (synCopk (.cv x) (.cv y)) C))))
      z t u (synCsik C) A B V W
      (by
        exact
          (show t ∉ ((synCsik C)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
              exact (show t ∉ (C).fv from (by exact fresh_t_not_C)))))
      (by
        exact
          (show u ∉ ((synCsik C)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
              exact (show u ∉ (C).fv from (by exact fresh_u_not_C)))))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B)))
      (by exact (show u ∉ (B).fv from (by exact fresh_u_not_B))) freeVariableCertificate4
      freeVariableCertificate5 freeVariableCertificate6
      (show z ≠ t from (by exact fresh_z_ne_t)) (show z ≠ u from (by exact fresh_z_ne_u))
      (show t ≠ u from (by exact fresh_t_ne_u)) p0000 p0003 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_opksnelsik`. -/
@[expose]
noncomputable def gOpksnelsik (A : Class) (B : Class) (C : Class)
    (hyp_opksnelsik_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opksnelsik_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn A) (synCsn B)) (synCsik C))
        (.classMem (synCopk A B) C)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have p0000 := @gSnex A
  have p0001 := @gSnex B
  have p0002 :=
    @gOpkelsikg x y (synCsn A) (synCsn B) C (synCvv) (synCvv)
      (by
        exact
          (show x ∉ ((synCsn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      (by
        exact
          (show y ∉ ((synCsn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
      (by
        exact
          (show x ∉ ((synCsn B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))))
      (by
        exact
          (show y ∉ ((synCsn B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))))
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0003 :=
    @gMp2an (.classMem (synCsn A) (synCvv)) (.classMem (synCsn B) (synCvv))
      (synWb (.classMem (synCopk (synCsn A) (synCsn B)) (synCsik C)) (synWex x (synWex y
            (synW3a (.classEq (synCsn A) (synCsn (.cv x)))
              (.classEq (synCsn B) (synCsn (.cv y)))
              (.classMem (synCopk (.cv x) (.cv y)) C)))))
      p0000 p0001 p0002
  have p0004 := @gEqcom (synCsn A) (synCsn (.cv x))
  have p0005 := @gVex x
  have p0006 := @gSneqb (.cv x) A p0005
  have p0007 :=
    @gBitri (.classEq (synCsn A) (synCsn (.cv x)))
      (.classEq (synCsn (.cv x)) (synCsn A)) (.classEq (.cv x) A) p0004 p0006
  have p0008 := @gEqcom (synCsn B) (synCsn (.cv y))
  have p0009 := @gVex y
  have p0010 := @gSneqb (.cv y) B p0009
  have p0011 :=
    @gBitri (.classEq (synCsn B) (synCsn (.cv y)))
      (.classEq (synCsn (.cv y)) (synCsn B)) (.classEq (.cv y) B) p0008 p0010
  have p0012 := @gBiid (.classMem (synCopk (.cv x) (.cv y)) C)
  have p0013 :=
    @gN3anbi123i (.classEq (synCsn A) (synCsn (.cv x))) (.classEq (.cv x) A)
      (.classEq (synCsn B) (synCsn (.cv y))) (.classEq (.cv y) B)
      (.classMem (synCopk (.cv x) (.cv y)) C) (.classMem (synCopk (.cv x) (.cv y)) C)
      p0007 p0011 p0012
  have p0014 :=
    @gN2exbii
      (synW3a (.classEq (synCsn A) (synCsn (.cv x)))
        (.classEq (synCsn B) (synCsn (.cv y))) (.classMem (synCopk (.cv x) (.cv y)) C))
      (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B)
        (.classMem (synCopk (.cv x) (.cv y)) C))
      x y p0013
  have p0015 := @gOpkeq1 (.cv x) A (.cv y)
  have p0016 :=
    @gEleq1d (.classEq (.cv x) A) (synCopk (.cv x) (.cv y)) (synCopk A (.cv y)) C p0015
  have p0017 := @gOpkeq2 (.cv y) B A
  have p0018 := @gEleq1d (.classEq (.cv y) B) (synCopk A (.cv y)) (synCopk A B) C p0017
  have freeVariableCertificate0 : y ∉ ((Wff.classMem (synCopk A B) C)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((Wff.classMem (synCopk A (.cv y)) C)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_not_A, fresh_x_ne_y, fresh_x_not_C, or_false, not_false_eq_true]
  have p0019 :=
    @gCeqsex2v (.classMem (synCopk (.cv x) (.cv y)) C)
      (.classMem (synCopk A (.cv y)) C) (.classMem (synCopk A B) C) x y A B
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) freeVariableCertificate0
      freeVariableCertificate1 (show x ≠ y from (by exact fresh_x_ne_y)) hyp_opksnelsik_1
      hyp_opksnelsik_2 p0016 p0018
  have p0020 :=
    @gBitri
      (synWex x (synWex y (synW3a (.classEq (synCsn A) (synCsn (.cv x)))
            (.classEq (synCsn B) (synCsn (.cv y))) (.classMem (synCopk (.cv x) (.cv y)) C))))
      (synWex x (synWex y (synW3a (.classEq (.cv x) A) (.classEq (.cv y) B)
            (.classMem (synCopk (.cv x) (.cv y)) C))))
      (.classMem (synCopk A B) C) p0014 p0019
  have p0021 :=
    @gBitri (.classMem (synCopk (synCsn A) (synCsn B)) (synCsik C))
      (synWex x (synWex y (synW3a (.classEq (synCsn A) (synCsn (.cv x)))
            (.classEq (synCsn B) (synCsn (.cv y))) (.classMem (synCopk (.cv x) (.cv y)) C))))
      (.classMem (synCopk A B) C) p0003 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_sikssvvk`. -/
@[expose]
noncomputable def gSikssvvk (A : Class) :
    Nominal.NPrf (synWss (synCsik A) (synCxpk (synCvv) (synCvv))) :=
  by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let u : Var := freshVar proofSupport 3
  let x : Var := freshVar proofSupport 4
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_t_ne_z : t ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_u_ne_x : u ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSik x y z u t A
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ x from (by exact fresh_t_ne_x))
      (show t ≠ y from (by exact fresh_t_ne_y)) (show t ≠ z from (by exact fresh_t_ne_z))
      (show u ≠ x from (by exact fresh_u_ne_x)) (show u ≠ y from (by exact fresh_u_ne_y))
      (show u ≠ z from (by exact fresh_u_ne_z)) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @gOpkabssvvki
      (synWex t (synWex u (synW3a (.classEq (.cv y) (synCsn (.cv t)))
            (.classEq (.cv z) (synCsn (.cv u))) (.classMem (synCopk (.cv t) (.cv u)) A))))
      x y z (synCsik A) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart010`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_sikss1c1c`. -/
@[expose]
noncomputable def gSikss1c1c (A : Class) :
    Nominal.NPrf (synWss (synCsik A) (synCxpk (synC1c) (synC1c))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let a : Var := freshVar proofSupport 2
  let b : Var := freshVar proofSupport 3
  let z : Var := freshVar proofSupport 4
  let w : Var := freshVar proofSupport 5
  let t : Var := freshVar proofSupport 6
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
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (h)
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_a_ne_w : a ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_w_ne_a : w ≠ a := Ne.symm fresh_a_ne_w
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_b_ne_z : b ≠ z :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_z_ne_b : z ≠ b := Ne.symm fresh_b_ne_z
  have fresh_b_ne_w : b ≠ w :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_w_ne_b : w ≠ b := Ne.symm fresh_b_ne_w
  have fresh_b_ne_t : b ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_t_ne_b : t ≠ b := Ne.symm fresh_b_ne_t
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_t_ne_w : t ≠ w := Ne.symm fresh_w_ne_t
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSik t z w b a A
      (by exact (show a ∉ (A).fv from (by exact fresh_a_not_A)))
      (by exact (show b ∉ (A).fv from (by exact fresh_b_not_A)))
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (show a ≠ b from (by exact fresh_a_ne_b)) (show a ≠ t from (by exact fresh_a_ne_t))
      (show a ≠ z from (by exact fresh_a_ne_z)) (show a ≠ w from (by exact fresh_a_ne_w))
      (show b ≠ t from (by exact fresh_b_ne_t)) (show b ≠ z from (by exact fresh_b_ne_z))
      (show b ≠ w from (by exact fresh_b_ne_w)) (show t ≠ z from (by exact fresh_t_ne_z))
      (show t ≠ w from (by exact fresh_t_ne_w)) (show z ≠ w from (by exact fresh_z_ne_w))
  have p0001 := @gEqeq1 (.cv z) (.cv x) (synCsn (.cv a))
  have p0002_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z x) (synWb (.classEq (.cv z) (synCsn (.cv a)))
          (.classEq (.cv x) (synCsn (.cv a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 :=
    @gN3anbi1d (.objEq z x) (.classEq (.cv z) (synCsn (.cv a)))
      (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv w) (synCsn (.cv b)))
      (.classMem (synCopk (.cv a) (.cv b)) A) p0002_e00_recanon
  have freeVariableCertificate0 : a ∉ ((Wff.objEq z x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 : b ∉ ((Wff.objEq z x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_x, or_false, not_false_eq_true]
  have p0003 :=
    @gN2exbidv (.objEq z x)
      (synW3a (.classEq (.cv z) (synCsn (.cv a))) (.classEq (.cv w) (synCsn (.cv b)))
        (.classMem (synCopk (.cv a) (.cv b)) A))
      (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv w) (synCsn (.cv b)))
        (.classMem (synCopk (.cv a) (.cv b)) A))
      a b freeVariableCertificate0 freeVariableCertificate1 p0002
  have p0004 := @gEqeq1 (.cv w) (.cv y) (synCsn (.cv b))
  have p0005_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w y) (synWb (.classEq (.cv w) (synCsn (.cv b)))
          (.classEq (.cv y) (synCsn (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @gN3anbi2d (.objEq w y) (.classEq (.cv w) (synCsn (.cv b)))
      (.classEq (.cv y) (synCsn (.cv b))) (.classEq (.cv x) (synCsn (.cv a)))
      (.classMem (synCopk (.cv a) (.cv b)) A) p0005_e00_recanon
  have freeVariableCertificate2 : a ∉ ((Wff.objEq w y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_a_ne_w, fresh_a_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate3 : b ∉ ((Wff.objEq w y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_b_ne_w, fresh_b_ne_y, or_false, not_false_eq_true]
  have p0006 :=
    @gN2exbidv (.objEq w y)
      (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv w) (synCsn (.cv b)))
        (.classMem (synCopk (.cv a) (.cv b)) A))
      (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
        (.classMem (synCopk (.cv a) (.cv b)) A))
      a b freeVariableCertificate2 freeVariableCertificate3 p0005
  have p0007 := @gVex x
  have p0008 := @gVex y
  have p0009_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv x)) (synWb (synWex a (synWex b
              (synW3a (.classEq (.cv z) (synCsn (.cv a))) (.classEq (.cv w) (synCsn (.cv b)))
                (.classMem (synCopk (.cv a) (.cv b)) A)))) (synWex a (synWex b
              (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv w) (synCsn (.cv b)))
                (.classMem (synCopk (.cv a) (.cv b)) A)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0009_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv y)) (synWb (synWex a (synWex b
              (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv w) (synCsn (.cv b)))
                (.classMem (synCopk (.cv a) (.cv b)) A)))) (synWex a (synWex b
              (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
                (.classMem (synCopk (.cv a) (.cv b)) A)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have freeVariableCertificate4 : t ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_x, not_false_eq_true]
  have freeVariableCertificate5 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have freeVariableCertificate6 : w ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_x, not_false_eq_true]
  have freeVariableCertificate7 : t ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_y, not_false_eq_true]
  have freeVariableCertificate8 : z ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_y, not_false_eq_true]
  have freeVariableCertificate9 : w ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_y, not_false_eq_true]
  have freeVariableCertificate10 :
    w ∉
      ((synWex a (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
              (.classEq (.cv y) (synCsn (.cv b)))
              (.classMem (synCopk (.cv a) (.cv b)) A))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_a, fresh_w_ne_b, fresh_w_not_A,
      fresh_w_ne_x, fresh_w_ne_y, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate11 :
    t ∉
      ((synWex a (synWex b (synW3a (.classEq (.cv z) (synCsn (.cv a)))
              (.classEq (.cv w) (synCsn (.cv b)))
              (.classMem (synCopk (.cv a) (.cv b)) A))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_b, fresh_t_not_A,
      fresh_t_ne_z, fresh_t_ne_w, or_false, and_false, not_false_eq_true]
  have freeVariableCertificate12 :
    z ∉
      ((synWex a (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
              (.classEq (.cv w) (synCsn (.cv b)))
              (.classMem (synCopk (.cv a) (.cv b)) A))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_b, fresh_z_not_A,
      fresh_z_ne_x, fresh_z_ne_w, or_false, and_false, not_false_eq_true]
  have p0009 :=
    @gOpkelopkab
      (synWex a (synWex b (synW3a (.classEq (.cv z) (synCsn (.cv a)))
            (.classEq (.cv w) (synCsn (.cv b))) (.classMem (synCopk (.cv a) (.cv b)) A))))
      (synWex a (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
            (.classEq (.cv w) (synCsn (.cv b))) (.classMem (synCopk (.cv a) (.cv b)) A))))
      (synWex a (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
            (.classEq (.cv y) (synCsn (.cv b))) (.classMem (synCopk (.cv a) (.cv b)) A))))
      t z w (synCsik A) (.cv x) (.cv y)
      (by
        exact
          (show z ∉ ((synCsik A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
              exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))))
      (by
        exact
          (show w ∉ ((synCsik A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
              exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))))
      freeVariableCertificate4 freeVariableCertificate5 freeVariableCertificate6
      freeVariableCertificate7 freeVariableCertificate8 freeVariableCertificate9
      freeVariableCertificate10 freeVariableCertificate11 freeVariableCertificate12
      (show t ≠ z from (by exact fresh_t_ne_z)) (show t ≠ w from (by exact fresh_t_ne_w))
      (show z ≠ w from (by exact fresh_z_ne_w)) p0000 p0009_e01_recanon p0009_e02_recanon
      p0007 p0008
  have p0010 := @gOpkeq12 (.cv x) (.cv y) (synCsn (.cv a)) (synCsn (.cv b))
  have p0011 := @gVex a
  have p0012 := @gSnel1c (.cv a) p0011
  have p0013 := @gVex b
  have p0014 := @gSnel1c (.cv b) p0013
  have p0015 :=
    @gOpkelxpkg (synCsn (.cv a)) (synCsn (.cv b)) (synC1c) (synC1c) (synC1c)
      (synC1c)
  have p0016 :=
    @gMp2an (.classMem (synCsn (.cv a)) (synC1c))
      (.classMem (synCsn (.cv b)) (synC1c))
      (synWb (.classMem (synCopk (synCsn (.cv a)) (synCsn (.cv b)))
          (synCxpk (synC1c) (synC1c))) (synWa (.classMem (synCsn (.cv a)) (synC1c))
          (.classMem (synCsn (.cv b)) (synC1c))))
      p0012 p0014 p0015
  have p0017 :=
    @gMpbir2an
      (.classMem (synCopk (synCsn (.cv a)) (synCsn (.cv b))) (synCxpk (synC1c) (synC1c)))
      (.classMem (synCsn (.cv a)) (synC1c)) (.classMem (synCsn (.cv b)) (synC1c))
      p0012 p0014 p0016
  have p0018 :=
    @gSyl6eqel
      (synWa (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b))))
      (synCopk (.cv x) (.cv y)) (synCopk (synCsn (.cv a)) (synCsn (.cv b)))
      (synCxpk (synC1c) (synC1c)) p0010 p0017
  have p0019 :=
    @gN3adant3 (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
      (.classMem (synCopk (.cv x) (.cv y)) (synCxpk (synC1c) (synC1c)))
      (.classMem (synCopk (.cv a) (.cv b)) A) p0018
  have freeVariableCertificate13 :
    a ∉ ((Wff.classMem (synCopk (.cv x) (.cv y)) (synCxpk (synC1c) (synC1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_x, fresh_a_ne_y, or_false,
      not_false_eq_true]
  have freeVariableCertificate14 :
    b ∉ ((Wff.classMem (synCopk (.cv x) (.cv y)) (synCxpk (synC1c) (synC1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_x, fresh_b_ne_y, or_false,
      not_false_eq_true]
  have p0020 :=
    @gExlimivv
      (synW3a (.classEq (.cv x) (synCsn (.cv a))) (.classEq (.cv y) (synCsn (.cv b)))
        (.classMem (synCopk (.cv a) (.cv b)) A))
      (.classMem (synCopk (.cv x) (.cv y)) (synCxpk (synC1c) (synC1c))) a b
      freeVariableCertificate13 freeVariableCertificate14 p0019
  have p0021 :=
    @gSylbi (.classMem (synCopk (.cv x) (.cv y)) (synCsik A))
      (synWex a (synWex b (synW3a (.classEq (.cv x) (synCsn (.cv a)))
            (.classEq (.cv y) (synCsn (.cv b))) (.classMem (synCopk (.cv a) (.cv b)) A))))
      (.classMem (synCopk (.cv x) (.cv y)) (synCxpk (synC1c) (synC1c))) p0009 p0020
  have p0022 :=
    @gGen2
      (.imp (.classMem (synCopk (.cv x) (.cv y)) (synCsik A))
        (.classMem (synCopk (.cv x) (.cv y)) (synCxpk (synC1c) (synC1c))))
      x y p0021
  have p0023 := @gSikssvvk A
  have freeVariableCertificate15 : x ∉ ((synCxpk (synC1c) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate16 : y ∉ ((synCxpk (synC1c) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0024 :=
    @gSsrelk x y (synCsik A) (synCxpk (synC1c) (synC1c))
      (by
        exact
          (show x ∉ ((synCsik A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      (by
        exact
          (show y ∉ ((synCsik A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
      freeVariableCertificate15 freeVariableCertificate16
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @gMpbir (synWss (synCsik A) (synCxpk (synC1c) (synC1c)))
      (.all x (.all y (.imp (.classMem (synCopk (.cv x) (.cv y)) (synCsik A))
            (.classMem (synCopk (.cv x) (.cv y)) (synCxpk (synC1c) (synC1c))))))
      p0022 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_opkelssetkg`. -/
@[expose]
noncomputable def gOpkelssetkg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synCssetk)) (synWss A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSsetk x y z
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 := @gSseq1 (.cv y) A (.cv z)
  have p0002 := @gSseq2 (.cv z) B A
  have freeVariableCertificate0 : z ∉ ((synWss A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((synWss (.cv y) (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_y, fresh_x_ne_z, or_false, not_false_eq_true]
  have freeVariableCertificate2 : y ∉ ((synWss A (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_not_A, fresh_y_ne_z, or_false, not_false_eq_true]
  have p0003 :=
    @gOpkelopkabg (synWss (.cv y) (.cv z)) (synWss A (.cv z)) (synWss A B) x y z
      (synCssetk) A B V W
      (by
        exact
          (show y ∉ ((synCssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show z ∉ ((synCssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z)) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_elssetkg`. -/
@[expose]
noncomputable def gElssetkg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk (synCsn A) B) (synCssetk)) (.classMem A B))) :=
  by
  have p0000 := @gSnex A
  have p0001 := @gOpkelssetkg (synCsn A) B (synCvv) W
  have p0002 :=
    @gMpan (.classMem (synCsn A) (synCvv)) (.classMem B W)
      (synWb (.classMem (synCopk (synCsn A) B) (synCssetk)) (synWss (synCsn A) B))
      p0000 p0001
  have p0003 := @gSnssg A B V
  have p0004 := @gBicomd (.classMem A V) (.classMem A B) (synWss (synCsn A) B) p0003
  have p0005 :=
    @gSylan9bbr (.classMem B W) (.classMem (synCopk (synCsn A) B) (synCssetk))
      (synWss (synCsn A) B) (.classMem A V) (.classMem A B) p0002 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_elssetk`. -/
@[expose]
noncomputable def gElssetk (A : Class) (B : Class)
    (hyp_elssetk_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_elssetk_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn A) B) (synCssetk)) (.classMem A B)) :=
  by
  have p0000 := @gElssetkg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (.classMem (synCopk (synCsn A) B) (synCssetk)) (.classMem A B))
      hyp_elssetk_1 hyp_elssetk_2 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart011`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_opkelimagekg`. -/
@[expose]
noncomputable def gOpkelimagekg (A : Class) (B : Class) (C : Class) (V : Class)
    (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synCimagek C)) (.classEq B (synCimak C A)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ V.fv ∪ W.fv
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
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
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
  have fresh_z_not_C : z ∉ C.fv := by
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
  have p0000 := @gElex A V
  have p0001 := @gElex B W
  have p0002 := @gOpkelxpkg A B (synCvv) (synCvv) (synCvv) (synCvv)
  have p0003 :=
    @gIbir (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCopk A B) (synCxpk (synCvv) (synCvv))) p0002
  have p0004 :=
    @gBiantrurd (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCopk A B) (synCxpk (synCvv) (synCvv)))
      (.neg (.classMem (synCopk A B) (synCimak (synCsymdif (synCins2k (synCssetk))
              (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0003
  have p0005 :=
    @gExnal (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCimak C A))) x
  have p0006 := @gOpkex A B
  have freeVariableCertificate0 :
    y ∉
      ((synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((synCpw1 (synCpw1 (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate2 : y ∉ ((synCopk A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0007 :=
    @gElimak y
      (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
      (synCpw1 (synCpw1 (synC1c))) (synCopk A B) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 p0006
  have p0008 :=
    (Nominal.biimpRefl (synWrex y (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))))
  have freeVariableCertificate3 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0009 := @gElpw121c x (.cv y) freeVariableCertificate3
  have p0010 :=
    @gAnbi1i (.classMem (.cv y) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x))))))
      (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))
      p0009
  have freeVariableCertificate4 :
    x ∉
      ((Wff.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_y, fresh_x_not_A,
      fresh_x_not_B, fresh_x_not_C, or_false, not_false_eq_true]
  have p0011 :=
    @gN1941v (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
      (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))
      x freeVariableCertificate4
  have p0012 :=
    @gBitr4i
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))))
      (synWa (synWex x (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x))))))
        (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
              (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))))
      p0010 p0011
  have p0013 :=
    @gExbii
      (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))))
      (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
              (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))))
      y p0012
  have p0014 :=
    @gExcom
      (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
        (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))))
      y x
  have p0015 := @gSnex (synCsn (synCsn (.cv x)))
  have p0016 := @gOpkeq1 (.cv y) (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B)
  have p0017 :=
    @gEleq1d (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (.cv y) (synCopk A B))
      (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
      (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
      p0016
  have freeVariableCertificate5 : y ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate6 :
    y ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
          (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, fresh_y_not_A,
      fresh_y_not_B, fresh_y_not_C, or_false, not_false_eq_true]
  have p0018 :=
    @gCeqsexv
      (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))
      y (synCsn (synCsn (synCsn (.cv x)))) freeVariableCertificate5
      freeVariableCertificate6 p0015 p0017
  have p0019 :=
    @gExbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
              (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))
      x p0018
  have p0020 :=
    @gN3bitri
      (synWex y (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
              (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))))
      (synWex y (synWex x (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))))))
      (synWex x (synWex y (synWa (.classEq (.cv y) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))))))
      (synWex x (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
          (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))))
      p0013 p0014 p0019
  have p0021 :=
    @gN3bitri
      (.classMem (synCopk A B) (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWrex y (synCpw1 (synCpw1 (synC1c))) (.classMem (synCopk (.cv y) (synCopk A B))
          (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))))
      (synWex y (synWa (.classMem (.cv y) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv y) (synCopk A B)) (synCsymdif (synCins2k (synCssetk))
              (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))))
      (synWex x (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
          (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))))
      p0007 p0008 p0020
  have p0022 :=
    @gElsymdif (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
      (synCins2k (synCssetk))
      (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))
  have p0023 := @gSnex (.cv x)
  have p0024 :=
    @gOtkelins2kg (synCsn (.cv x)) A B (synCssetk) (synCvv) (synCvv) (synCvv)
  have p0025 :=
    @gMp3an1 (.classMem (synCsn (.cv x)) (synCvv)) (.classMem A (synCvv))
      (.classMem B (synCvv))
      (synWb (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
          (synCins2k (synCssetk))) (.classMem (synCopk (synCsn (.cv x)) B) (synCssetk)))
      p0023 p0024
  have p0026 := @gVex x
  have p0027 := @gElssetkg (.cv x) B (synCvv) (synCvv)
  have p0028 :=
    @gMpan (.classMem (.cv x) (synCvv)) (.classMem B (synCvv))
      (synWb (.classMem (synCopk (synCsn (.cv x)) B) (synCssetk)) (.classMem (.cv x) B))
      p0026 p0027
  have p0029 :=
    @gAdantl (.classMem B (synCvv))
      (synWb (.classMem (synCopk (synCsn (.cv x)) B) (synCssetk)) (.classMem (.cv x) B))
      (.classMem A (synCvv)) p0028
  have p0030 :=
    @gBitrd (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) B) (synCssetk)) (.classMem (.cv x) B) p0025
      p0029
  have p0031 :=
    @gOtkelins3kg (synCsn (.cv x)) A B (synCcomk (synCssetk) (synCcnvk (synCsik C)))
      (synCvv) (synCvv) (synCvv)
  have p0032 :=
    @gMp3an1 (.classMem (synCsn (.cv x)) (synCvv)) (.classMem A (synCvv))
      (.classMem B (synCvv))
      (synWb (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
        (.classMem (synCopk (synCsn (.cv x)) A)
          (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
      p0023 p0031
  have freeVariableCertificate7 : z ∉ ((synCsn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
      not_false_eq_true]
  have freeVariableCertificate8 : z ∉ ((synCcnvk (synCsik C))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, fresh_z_not_C,
      not_false_eq_true]
  have p0033 :=
    @gOpkelcokg z (synCsn (.cv x)) A (synCssetk) (synCcnvk (synCsik C)) (synCvv)
      (synCvv) freeVariableCertificate7
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by
        exact
          (show z ∉ ((synCssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate8
  have p0034 :=
    @gMpan (.classMem (synCsn (.cv x)) (synCvv)) (.classMem A (synCvv))
      (synWb (.classMem (synCopk (synCsn (.cv x)) A)
          (synCcomk (synCssetk) (synCcnvk (synCsik C)))) (synWex z (synWa
            (.classMem (synCopk (synCsn (.cv x)) (.cv z)) (synCcnvk (synCsik C)))
            (.classMem (synCopk (.cv z) A) (synCssetk)))))
      p0023 p0033
  have p0035 := @gVex y
  have p0036 := @gElssetkg (.cv y) A (synCvv) (synCvv)
  have p0037 :=
    @gMpan (.classMem (.cv y) (synCvv)) (.classMem A (synCvv))
      (synWb (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk)) (.classMem (.cv y) A))
      p0035 p0036
  have p0038 :=
    @gAnbi1d (.classMem A (synCvv))
      (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk)) (.classMem (.cv y) A)
      (.classMem (synCopk (.cv y) (.cv x)) C) p0037
  have freeVariableCertificate9 : y ∉ ((Wff.classMem A (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_A, or_false, not_false_eq_true]
  have p0039 :=
    @gExbidv (.classMem A (synCvv))
      (synWa (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk))
        (.classMem (synCopk (.cv y) (.cv x)) C))
      (synWa (.classMem (.cv y) A) (.classMem (synCopk (.cv y) (.cv x)) C)) y
      freeVariableCertificate9 p0038
  have p0040 := @gVex z
  have p0041 := @gOpkelcnvk (synCsn (.cv x)) (.cv z) (synCsik C) p0023 p0040
  have p0042 := @gSikss1c1c C
  have p0043 :=
    @gSseli (synCsik C) (synCxpk (synC1c) (synC1c))
      (synCopk (.cv z) (synCsn (.cv x))) p0042
  have p0044 := @gOpkelxpk (.cv z) (synCsn (.cv x)) (synC1c) (synC1c) p0040 p0023
  have freeVariableCertificate10 : y ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_z, not_false_eq_true]
  have p0045 := @gEl1c y (.cv z) freeVariableCertificate10
  have p0046 :=
    @gBiimpi (.classMem (.cv z) (synC1c))
      (synWex y (.classEq (.cv z) (synCsn (.cv y)))) p0045
  have p0047 :=
    @gAdantr (.classMem (.cv z) (synC1c))
      (synWex y (.classEq (.cv z) (synCsn (.cv y))))
      (.classMem (synCsn (.cv x)) (synC1c)) p0046
  have p0048 :=
    @gSylbi
      (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCxpk (synC1c) (synC1c)))
      (synWa (.classMem (.cv z) (synC1c)) (.classMem (synCsn (.cv x)) (synC1c)))
      (synWex y (.classEq (.cv z) (synCsn (.cv y)))) p0044 p0047
  have p0049 :=
    @gSyl (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
      (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCxpk (synC1c) (synC1c)))
      (synWex y (.classEq (.cv z) (synCsn (.cv y)))) p0043 p0048
  have p0050 :=
    @gPm471ri (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
      (synWex y (.classEq (.cv z) (synCsn (.cv y)))) p0049
  have p0051 :=
    @gBitri (.classMem (synCopk (synCsn (.cv x)) (.cv z)) (synCcnvk (synCsik C)))
      (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
      (synWa (synWex y (.classEq (.cv z) (synCsn (.cv y))))
        (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C)))
      p0041 p0050
  have p0052 :=
    @gAnbi1i (.classMem (synCopk (synCsn (.cv x)) (.cv z)) (synCcnvk (synCsik C)))
      (synWa (synWex y (.classEq (.cv z) (synCsn (.cv y))))
        (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C)))
      (.classMem (synCopk (.cv z) A) (synCssetk)) p0051
  have p0053 :=
    @gAnass (synWex y (.classEq (.cv z) (synCsn (.cv y))))
      (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
      (.classMem (synCopk (.cv z) A) (synCssetk))
  have freeVariableCertificate11 :
    y ∉
      ((synWa (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
          (.classMem (synCopk (.cv z) A) (synCssetk)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_z, fresh_y_ne_x,
      fresh_y_not_C, fresh_y_not_A, or_false, not_false_eq_true]
  have p0054 :=
    @gN1941v (.classEq (.cv z) (synCsn (.cv y)))
      (synWa (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
        (.classMem (synCopk (.cv z) A) (synCssetk)))
      y freeVariableCertificate11
  have p0055 :=
    @gBitr4i
      (synWa (synWa (synWex y (.classEq (.cv z) (synCsn (.cv y))))
          (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C)))
        (.classMem (synCopk (.cv z) A) (synCssetk)))
      (synWa (synWex y (.classEq (.cv z) (synCsn (.cv y))))
        (synWa (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
          (.classMem (synCopk (.cv z) A) (synCssetk))))
      (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y)))
          (synWa (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
            (.classMem (synCopk (.cv z) A) (synCssetk)))))
      p0053 p0054
  have p0056 :=
    @gBitri
      (synWa (.classMem (synCopk (synCsn (.cv x)) (.cv z)) (synCcnvk (synCsik C)))
        (.classMem (synCopk (.cv z) A) (synCssetk)))
      (synWa (synWa (synWex y (.classEq (.cv z) (synCsn (.cv y))))
          (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C)))
        (.classMem (synCopk (.cv z) A) (synCssetk)))
      (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y)))
          (synWa (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
            (.classMem (synCopk (.cv z) A) (synCssetk)))))
      p0052 p0055
  have p0057 :=
    @gExbii
      (synWa (.classMem (synCopk (synCsn (.cv x)) (.cv z)) (synCcnvk (synCsik C)))
        (.classMem (synCopk (.cv z) A) (synCssetk)))
      (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y)))
          (synWa (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
            (.classMem (synCopk (.cv z) A) (synCssetk)))))
      z p0056
  have p0058 :=
    @gExcom
      (synWa (.classEq (.cv z) (synCsn (.cv y)))
        (synWa (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
          (.classMem (synCopk (.cv z) A) (synCssetk))))
      z y
  have p0059 := @gSnex (.cv y)
  have p0060 := @gOpkeq1 (.cv z) (synCsn (.cv y)) (synCsn (.cv x))
  have p0061 :=
    @gEleq1d (.classEq (.cv z) (synCsn (.cv y))) (synCopk (.cv z) (synCsn (.cv x)))
      (synCopk (synCsn (.cv y)) (synCsn (.cv x))) (synCsik C) p0060
  have p0062 := @gOpkeq1 (.cv z) (synCsn (.cv y)) A
  have p0063 :=
    @gEleq1d (.classEq (.cv z) (synCsn (.cv y))) (synCopk (.cv z) A)
      (synCopk (synCsn (.cv y)) A) (synCssetk) p0062
  have p0064 :=
    @gAnbi12d (.classEq (.cv z) (synCsn (.cv y)))
      (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
      (.classMem (synCopk (synCsn (.cv y)) (synCsn (.cv x))) (synCsik C))
      (.classMem (synCopk (.cv z) A) (synCssetk))
      (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk)) p0061 p0063
  have p0065 :=
    @gAncom (.classMem (synCopk (synCsn (.cv y)) (synCsn (.cv x))) (synCsik C))
      (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk))
  have p0066 := @gOpksnelsik (.cv y) (.cv x) C p0035 p0026
  have p0067 :=
    @gAnbi2i (.classMem (synCopk (synCsn (.cv y)) (synCsn (.cv x))) (synCsik C))
      (.classMem (synCopk (.cv y) (.cv x)) C)
      (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk)) p0066
  have p0068 :=
    @gBitri
      (synWa (.classMem (synCopk (synCsn (.cv y)) (synCsn (.cv x))) (synCsik C))
        (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk)))
      (synWa (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk))
        (.classMem (synCopk (synCsn (.cv y)) (synCsn (.cv x))) (synCsik C)))
      (synWa (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk))
        (.classMem (synCopk (.cv y) (.cv x)) C))
      p0065 p0067
  have p0069 :=
    @gSyl6bb (.classEq (.cv z) (synCsn (.cv y)))
      (synWa (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
        (.classMem (synCopk (.cv z) A) (synCssetk)))
      (synWa (.classMem (synCopk (synCsn (.cv y)) (synCsn (.cv x))) (synCsik C))
        (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk)))
      (synWa (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk))
        (.classMem (synCopk (.cv y) (.cv x)) C))
      p0064 p0068
  have freeVariableCertificate12 : z ∉ ((synCsn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_y,
      not_false_eq_true]
  have freeVariableCertificate13 :
    z ∉
      ((synWa (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk))
          (.classMem (synCopk (.cv y) (.cv x)) C))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_y, fresh_z_not_A,
      fresh_z_ne_x, fresh_z_not_C, or_false, not_false_eq_true]
  have p0070 :=
    @gCeqsexv
      (synWa (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
        (.classMem (synCopk (.cv z) A) (synCssetk)))
      (synWa (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk))
        (.classMem (synCopk (.cv y) (.cv x)) C))
      z (synCsn (.cv y)) freeVariableCertificate12 freeVariableCertificate13 p0059 p0069
  have p0071 :=
    @gExbii
      (synWex z (synWa (.classEq (.cv z) (synCsn (.cv y)))
          (synWa (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
            (.classMem (synCopk (.cv z) A) (synCssetk)))))
      (synWa (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk))
        (.classMem (synCopk (.cv y) (.cv x)) C))
      y p0070
  have p0072 :=
    @gN3bitri
      (synWex z
        (synWa (.classMem (synCopk (synCsn (.cv x)) (.cv z)) (synCcnvk (synCsik C)))
          (.classMem (synCopk (.cv z) A) (synCssetk))))
      (synWex z (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y)))
            (synWa (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
              (.classMem (synCopk (.cv z) A) (synCssetk))))))
      (synWex y (synWex z (synWa (.classEq (.cv z) (synCsn (.cv y)))
            (synWa (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCsik C))
              (.classMem (synCopk (.cv z) A) (synCssetk))))))
      (synWex y (synWa (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk))
          (.classMem (synCopk (.cv y) (.cv x)) C)))
      p0057 p0058 p0071
  have p0073 :=
    (Nominal.biimpRefl (synWrex y A (.classMem (synCopk (.cv y) (.cv x)) C)))
  have p0074 :=
    @gN3bitr4g (.classMem A (synCvv))
      (synWex y (synWa (.classMem (synCopk (synCsn (.cv y)) A) (synCssetk))
          (.classMem (synCopk (.cv y) (.cv x)) C)))
      (synWex y (synWa (.classMem (.cv y) A) (.classMem (synCopk (.cv y) (.cv x)) C)))
      (synWex z
        (synWa (.classMem (synCopk (synCsn (.cv x)) (.cv z)) (synCcnvk (synCsik C)))
          (.classMem (synCopk (.cv z) A) (synCssetk))))
      (synWrex y A (.classMem (synCopk (.cv y) (.cv x)) C)) p0039 p0072 p0073
  have p0075 :=
    @gBitrd (.classMem A (synCvv))
      (.classMem (synCopk (synCsn (.cv x)) A)
        (synCcomk (synCssetk) (synCcnvk (synCsik C))))
      (synWex z
        (synWa (.classMem (synCopk (synCsn (.cv x)) (.cv z)) (synCcnvk (synCsik C)))
          (.classMem (synCopk (.cv z) A) (synCssetk))))
      (synWrex y A (.classMem (synCopk (.cv y) (.cv x)) C)) p0034 p0074
  have freeVariableCertificate14 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0076 :=
    @gElimak y C A (.cv x) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate14
      p0026
  have p0077 :=
    @gSyl6bbr (.classMem A (synCvv))
      (.classMem (synCopk (synCsn (.cv x)) A)
        (synCcomk (synCssetk) (synCcnvk (synCsik C))))
      (synWrex y A (.classMem (synCopk (.cv y) (.cv x)) C))
      (.classMem (.cv x) (synCimak C A)) p0075 p0076
  have p0078 :=
    @gAdantr (.classMem A (synCvv))
      (synWb (.classMem (synCopk (synCsn (.cv x)) A)
          (synCcomk (synCssetk) (synCcnvk (synCsik C))))
        (.classMem (.cv x) (synCimak C A)))
      (.classMem B (synCvv)) p0077
  have p0079 :=
    @gBitrd (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
      (.classMem (synCopk (synCsn (.cv x)) A)
        (synCcomk (synCssetk) (synCcnvk (synCsik C))))
      (.classMem (.cv x) (synCimak C A)) p0032 p0078
  have p0080 :=
    @gBibi12d (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCins2k (synCssetk)))
      (.classMem (.cv x) B)
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
      (.classMem (.cv x) (synCimak C A)) p0030 p0079
  have p0081 :=
    @gNotbid (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWb (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
          (synCins2k (synCssetk)))
        (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))
      (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCimak C A))) p0080
  have p0082 :=
    @gSyl5bb
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))
      (.neg (synWb (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
            (synCins2k (synCssetk)))
          (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.neg (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCimak C A)))) p0022
      p0081
  have freeVariableCertificate15 :
    x ∉ ((synWa (.classMem A (synCvv)) (.classMem B (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0083 :=
    @gExbidv (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C))))))
      (.neg (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCimak C A)))) x
      freeVariableCertificate15 p0082
  have p0084 :=
    @gSyl5rbb
      (.classMem (synCopk A B) (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWex x (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
          (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWex x (.neg (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCimak C A)))))
      p0021 p0083
  have p0085 :=
    @gSyl5bbr
      (.neg (.all x (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCimak C A)))))
      (synWex x (.neg (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCimak C A)))))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.classMem (synCopk A B) (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0005 p0084
  have p0086 :=
    @gCon1bid (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.all x (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCimak C A))))
      (.classMem (synCopk A B) (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0085
  have p0087 :=
    @gBitr3d (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (.neg (.classMem (synCopk A B) (synCimak (synCsymdif (synCins2k (synCssetk))
              (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
            (synCpw1 (synCpw1 (synC1c))))))
      (synWa (.classMem (synCopk A B) (synCxpk (synCvv) (synCvv))) (.neg
          (.classMem (synCopk A B) (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.all x (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCimak C A)))) p0004
      p0086
  have p0088 := (Nominal.classEqRefl (synCimagek C))
  have p0089 :=
    @gEleq2i (synCimagek C)
      (synCdif (synCxpk (synCvv) (synCvv)) (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCopk A B) p0088
  have p0090 :=
    @gEldif (synCopk A B) (synCxpk (synCvv) (synCvv))
      (synCimak (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
        (synCpw1 (synCpw1 (synC1c))))
  have p0091 :=
    @gBitri (.classMem (synCopk A B) (synCimagek C))
      (.classMem (synCopk A B) (synCdif (synCxpk (synCvv) (synCvv)) (synCimak
            (synCsymdif (synCins2k (synCssetk))
              (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
            (synCpw1 (synCpw1 (synC1c))))))
      (synWa (.classMem (synCopk A B) (synCxpk (synCvv) (synCvv))) (.neg
          (.classMem (synCopk A B) (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
              (synCpw1 (synCpw1 (synC1c)))))))
      p0089 p0090
  have freeVariableCertificate16 : x ∉ ((synCimak C A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, Finset.mem_union,
      fresh_x_not_C, fresh_x_not_A, or_false, not_false_eq_true]
  have p0092 :=
    @gDfcleq x B (synCimak C A)
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) freeVariableCertificate16
  have p0093 :=
    @gN3bitr4g (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWa (.classMem (synCopk A B) (synCxpk (synCvv) (synCvv))) (.neg
          (.classMem (synCopk A B) (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik C)))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.all x (synWb (.classMem (.cv x) B) (.classMem (.cv x) (synCimak C A))))
      (.classMem (synCopk A B) (synCimagek C)) (.classEq B (synCimak C A)) p0087 p0091
      p0092
  have p0094 :=
    @gSyl2an (.classMem A V) (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (.classMem (synCopk A B) (synCimagek C)) (.classEq B (synCimak C A)))
      (.classMem B W) p0000 p0001 p0093
  exact p0094

/-- Checked nominal proof certificate identified upstream as `g_opkelimagek`. -/
@[expose]
noncomputable def gOpkelimagek (A : Class) (B : Class) (C : Class)
    (hyp_opkelimagek_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opkelimagek_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk A B) (synCimagek C)) (.classEq B (synCimak C A))) :=
  by
  have p0000 := @gOpkelimagekg A B C (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (synWb (.classMem (synCopk A B) (synCimagek C)) (.classEq B (synCimak C A)))
      hyp_opkelimagek_1 hyp_opkelimagek_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opkelidkg`. -/
@[expose]
noncomputable def gOpkelidkg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W))
        (synWb (.classMem (synCopk A B) (synCidk)) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
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
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_z_not_B : z ∉ B.fv := by
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIdk z x y
      (show z ≠ x from (by exact fresh_z_ne_x)) (show z ≠ y from (by exact fresh_z_ne_y))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 := @gEqeq1 (.cv x) A (.cv y)
  have p0002 := @gEqeq2 (.cv y) B A
  have p0003_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb (.objEq x y) (.classEq A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0001
  have freeVariableCertificate0 : y ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : z ∉ ((Wff.objEq x y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Wff.classEq A (.cv y))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_not_A, fresh_x_ne_y, or_false, not_false_eq_true]
  have p0003 :=
    @gOpkelopkabg (.objEq x y) (.classEq A (.cv y)) (.classEq A B) z x y (synCidk) A B V
      W
      (by
        exact
          (show x ∉ ((synCidk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((synCidk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2
      (show z ≠ x from (by exact fresh_z_ne_x)) (show z ≠ y from (by exact fresh_z_ne_y))
      (show x ≠ y from (by exact fresh_x_ne_y)) p0000 p0003_e01_recanon p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_cnvkssvvk`. -/
@[expose]
noncomputable def gCnvkssvvk (A : Class) :
    Nominal.NPrf (synWss (synCcnvk A) (synCxpk (synCvv) (synCvv))) :=
  by
  let proofSupport : Finset Var := A.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfCnvk x y z A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @gOpkabssvvki (.classMem (synCopk (.cv z) (.cv y)) A) x y z (synCcnvk A)
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cnvkxpk`. -/
@[expose]
noncomputable def gCnvkxpk (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (synCcnvk (synCxpk A B)) (synCxpk B A)) :=
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
  have p0000 := @gCnvkssvvk (synCxpk A B)
  have p0001 := @gXpkssvvk B A
  have p0002 := @gAncom (.classMem (.cv y) A) (.classMem (.cv x) B)
  have p0003 := @gVex x
  have p0004 := @gVex y
  have p0005 := @gOpkelcnvk (.cv x) (.cv y) (synCxpk A B) p0003 p0004
  have p0006 := @gOpkelxpk (.cv y) (.cv x) A B p0004 p0003
  have p0007 :=
    @gBitri (.classMem (synCopk (.cv x) (.cv y)) (synCcnvk (synCxpk A B)))
      (.classMem (synCopk (.cv y) (.cv x)) (synCxpk A B))
      (synWa (.classMem (.cv y) A) (.classMem (.cv x) B)) p0005 p0006
  have p0008 := @gOpkelxpk (.cv x) (.cv y) B A p0003 p0004
  have p0009 :=
    @gN3bitr4i (synWa (.classMem (.cv y) A) (.classMem (.cv x) B))
      (synWa (.classMem (.cv x) B) (.classMem (.cv y) A))
      (.classMem (synCopk (.cv x) (.cv y)) (synCcnvk (synCxpk A B)))
      (.classMem (synCopk (.cv x) (.cv y)) (synCxpk B A)) p0002 p0007 p0008
  have freeVariableCertificate0 : x ∉ ((synCcnvk (synCxpk A B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((synCcnvk (synCxpk A B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((synCxpk B A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_B, fresh_x_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((synCxpk B A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_y_not_B, fresh_y_not_A, or_false, not_false_eq_true]
  have p0010 :=
    @gEqrelkriiv x y (synCcnvk (synCxpk A B)) (synCxpk B A) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 freeVariableCertificate3
      (show x ≠ y from (by exact fresh_x_ne_y)) p0000 p0001 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart012`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_inxpk`. -/
@[expose]
noncomputable def gInxpk (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.classEq (synCin (synCxpk A B) (synCxpk C D))
        (synCxpk (synCin A C) (synCin B D))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv ∪ D.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_D : x ∉ D.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_D : y ∉ D.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have p0000 := @gInss1 (synCxpk A B) (synCxpk C D)
  have p0001 := @gXpkssvvk A B
  have p0002 :=
    @gSstri (synCin (synCxpk A B) (synCxpk C D)) (synCxpk A B)
      (synCxpk (synCvv) (synCvv)) p0000 p0001
  have p0003 := @gXpkssvvk (synCin A C) (synCin B D)
  have p0004 :=
    @gAn4 (.classMem (.cv x) A) (.classMem (.cv y) B) (.classMem (.cv x) C)
      (.classMem (.cv y) D)
  have p0005 := @gElin (synCopk (.cv x) (.cv y)) (synCxpk A B) (synCxpk C D)
  have p0006 := @gVex x
  have p0007 := @gVex y
  have p0008 := @gOpkelxpk (.cv x) (.cv y) A B p0006 p0007
  have p0009 := @gOpkelxpk (.cv x) (.cv y) C D p0006 p0007
  have p0010 :=
    @gAnbi12i (.classMem (synCopk (.cv x) (.cv y)) (synCxpk A B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (.classMem (synCopk (.cv x) (.cv y)) (synCxpk C D))
      (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)) p0008 p0009
  have p0011 :=
    @gBitri
      (.classMem (synCopk (.cv x) (.cv y)) (synCin (synCxpk A B) (synCxpk C D)))
      (synWa (.classMem (synCopk (.cv x) (.cv y)) (synCxpk A B))
        (.classMem (synCopk (.cv x) (.cv y)) (synCxpk C D)))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
        (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      p0005 p0010
  have p0012 := @gOpkelxpk (.cv x) (.cv y) (synCin A C) (synCin B D) p0006 p0007
  have p0013 := @gElin (.cv x) A C
  have p0014 := @gElin (.cv y) B D
  have p0015 :=
    @gAnbi12i (.classMem (.cv x) (synCin A C))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) C))
      (.classMem (.cv y) (synCin B D))
      (synWa (.classMem (.cv y) B) (.classMem (.cv y) D)) p0013 p0014
  have p0016 :=
    @gBitri (.classMem (synCopk (.cv x) (.cv y)) (synCxpk (synCin A C) (synCin B D)))
      (synWa (.classMem (.cv x) (synCin A C)) (.classMem (.cv y) (synCin B D)))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv x) C))
        (synWa (.classMem (.cv y) B) (.classMem (.cv y) D)))
      p0012 p0015
  have p0017 :=
    @gN3bitr4i
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv y) B))
        (synWa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      (synWa (synWa (.classMem (.cv x) A) (.classMem (.cv x) C))
        (synWa (.classMem (.cv y) B) (.classMem (.cv y) D)))
      (.classMem (synCopk (.cv x) (.cv y)) (synCin (synCxpk A B) (synCxpk C D)))
      (.classMem (synCopk (.cv x) (.cv y)) (synCxpk (synCin A C) (synCin B D))) p0004
      p0011 p0016
  have freeVariableCertificate0 : x ∉ ((synCin (synCxpk A B) (synCxpk C D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, fresh_x_not_D, or_false,
      not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((synCin (synCxpk A B) (synCxpk C D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, fresh_y_not_D, or_false,
      not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((synCxpk (synCin A C) (synCin B D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_C, fresh_x_not_B, fresh_x_not_D, or_false,
      not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((synCxpk (synCin A C) (synCin B D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_C, fresh_y_not_B, fresh_y_not_D, or_false,
      not_false_eq_true]
  have p0018 :=
    @gEqrelkriiv x y (synCin (synCxpk A B) (synCxpk C D))
      (synCxpk (synCin A C) (synCin B D)) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 freeVariableCertificate3
      (show x ≠ y from (by exact fresh_x_ne_y)) p0002 p0003 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_ssetkssvvk`. -/
@[expose]
noncomputable def gSsetkssvvk :
    Nominal.NPrf (synWss (synCssetk) (synCxpk (synCvv) (synCvv))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSsetk x y z
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @gOpkabssvvki (synWss (.cv y) (.cv z)) x y z (synCssetk)
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ins2kss`. -/
@[expose]
noncomputable def gIns2kss (A : Class) :
    Nominal.NPrf
      (synWss (synCins2k A) (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))) :=
  by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  let u : Var := freshVar proofSupport 4
  let x : Var := freshVar proofSupport 5
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (h)
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_w : t ≠ w := Ne.symm fresh_w_ne_t
  have fresh_w_ne_u : w ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_u_ne_w : u ≠ w := Ne.symm fresh_w_ne_u
  have fresh_w_ne_x : w ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have p0000 := @gVex y
  have p0001 := @gVex z
  have freeVariableCertificate0 : w ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_y, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_y, not_false_eq_true]
  have freeVariableCertificate2 : u ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_u_ne_y, not_false_eq_true]
  have freeVariableCertificate3 : w ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_z, not_false_eq_true]
  have freeVariableCertificate4 : t ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_z, not_false_eq_true]
  have freeVariableCertificate5 : u ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_u_ne_z, not_false_eq_true]
  have p0002 :=
    @gOpkelins2kg w t u (.cv y) (.cv z) A (synCvv) (synCvv) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 freeVariableCertificate3
      freeVariableCertificate4 freeVariableCertificate5
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A)))
      (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ u from (by exact fresh_w_ne_u))
      (show t ≠ u from (by exact fresh_t_ne_u))
  have p0003 :=
    @gMp2an (.classMem (.cv y) (synCvv)) (.classMem (.cv z) (synCvv))
      (synWb (.classMem (synCopk (.cv y) (.cv z)) (synCins2k A)) (synWex w (synWex t
            (synWex u (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
                (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
                (.classMem (synCopk (.cv w) (.cv u)) A))))))
      p0000 p0001 p0002
  have p0004 :=
    @gOpkeq12 (.cv y) (.cv z) (synCsn (synCsn (.cv w))) (synCopk (.cv t) (.cv u))
  have p0005 := @gVex w
  have p0006 := @gSnel1c (.cv w) p0005
  have p0007 := @gSnelpw1 (synCsn (.cv w)) (synC1c)
  have p0008 :=
    @gMpbir (.classMem (synCsn (synCsn (.cv w))) (synCpw1 (synC1c)))
      (.classMem (synCsn (.cv w)) (synC1c)) p0006 p0007
  have p0009 := @gVex t
  have p0010 := @gVex u
  have p0011 := @gOpkelxpk (.cv t) (.cv u) (synCvv) (synCvv) p0009 p0010
  have p0012 :=
    @gMpbir2an (.classMem (synCopk (.cv t) (.cv u)) (synCxpk (synCvv) (synCvv)))
      (.classMem (.cv t) (synCvv)) (.classMem (.cv u) (synCvv)) p0009 p0010 p0011
  have p0013 := @gSnex (synCsn (.cv w))
  have p0014 := @gOpkex (.cv t) (.cv u)
  have p0015 :=
    @gOpkelxpk (synCsn (synCsn (.cv w))) (synCopk (.cv t) (.cv u))
      (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)) p0013 p0014
  have p0016 :=
    @gMpbir2an
      (.classMem (synCopk (synCsn (synCsn (.cv w))) (synCopk (.cv t) (.cv u)))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (.classMem (synCsn (synCsn (.cv w))) (synCpw1 (synC1c)))
      (.classMem (synCopk (.cv t) (.cv u)) (synCxpk (synCvv) (synCvv))) p0008 p0012
      p0015
  have p0017 :=
    @gSyl6eqel
      (synWa (.classEq (.cv y) (synCsn (synCsn (.cv w))))
        (.classEq (.cv z) (synCopk (.cv t) (.cv u))))
      (synCopk (.cv y) (.cv z))
      (synCopk (synCsn (synCsn (.cv w))) (synCopk (.cv t) (.cv u)))
      (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) p0004 p0016
  have p0018 :=
    @gN3adant3 (.classEq (.cv y) (synCsn (synCsn (.cv w))))
      (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
      (.classMem (synCopk (.cv y) (.cv z))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (.classMem (synCopk (.cv w) (.cv u)) A) p0017
  have freeVariableCertificate6 :
    u ∉
      ((Wff.classMem (synCopk (.cv y) (.cv z))
          (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_u_ne_y, fresh_u_ne_z, or_false,
      not_false_eq_true]
  have p0019 :=
    @gExlimiv
      (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
        (.classEq (.cv z) (synCopk (.cv t) (.cv u))) (.classMem (synCopk (.cv w) (.cv u)) A))
      (.classMem (synCopk (.cv y) (.cv z))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      u freeVariableCertificate6 p0018
  have freeVariableCertificate7 :
    w ∉
      ((Wff.classMem (synCopk (.cv y) (.cv z))
          (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_w_ne_y, fresh_w_ne_z, or_false,
      not_false_eq_true]
  have freeVariableCertificate8 :
    t ∉
      ((Wff.classMem (synCopk (.cv y) (.cv z))
          (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_y, fresh_t_ne_z, or_false,
      not_false_eq_true]
  have p0020 :=
    @gExlimivv
      (synWex u (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
          (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
          (.classMem (synCopk (.cv w) (.cv u)) A)))
      (.classMem (synCopk (.cv y) (.cv z))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      w t freeVariableCertificate7 freeVariableCertificate8 p0019
  have p0021 :=
    @gSylbi (.classMem (synCopk (.cv y) (.cv z)) (synCins2k A))
      (synWex w (synWex t (synWex u (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv w))))
              (.classEq (.cv z) (synCopk (.cv t) (.cv u)))
              (.classMem (synCopk (.cv w) (.cv u)) A)))))
      (.classMem (synCopk (.cv y) (.cv z))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      p0003 p0020
  have p0022 :=
    @gGen2
      (.imp (.classMem (synCopk (.cv y) (.cv z)) (synCins2k A))
        (.classMem (synCopk (.cv y) (.cv z))
          (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))))
      y z p0021
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIns2k x y z w u t A
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A)))
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ w from (by exact fresh_t_ne_w))
      (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y))
      (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ w from (by exact fresh_u_ne_w))
      (show u ≠ x from (by exact fresh_u_ne_x)) (show u ≠ y from (by exact fresh_u_ne_y))
      (show u ≠ z from (by exact fresh_u_ne_z)) (show w ≠ x from (by exact fresh_w_ne_x))
      (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0024 :=
    @gOpkabssvvki
      (synWex t (synWex u (synWex w (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv t))))
              (.classEq (.cv z) (synCopk (.cv u) (.cv w)))
              (.classMem (synCopk (.cv t) (.cv w)) A)))))
      x y z (synCins2k A) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) p0023
  have freeVariableCertificate9 :
    y ∉ ((synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate10 :
    z ∉ ((synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0025 :=
    @gSsrelk y z (synCins2k A)
      (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))
      (by
        exact
          (show y ∉ ((synCins2k A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
      (by
        exact
          (show z ∉ ((synCins2k A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
              exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))))
      freeVariableCertificate9 freeVariableCertificate10
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @gMpbir
      (synWss (synCins2k A) (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (.all y (.all z (.imp (.classMem (synCopk (.cv y) (.cv z)) (synCins2k A))
            (.classMem (synCopk (.cv y) (.cv z))
              (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))))))
      p0022 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_ins3kss`. -/
@[expose]
noncomputable def gIns3kss (A : Class) :
    Nominal.NPrf
      (synWss (synCins3k A) (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))) :=
  by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  let u : Var := freshVar proofSupport 3
  let w : Var := freshVar proofSupport 4
  let x : Var := freshVar proofSupport 5
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (h)
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (h)
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_w : t ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_u_ne_w : u ≠ w :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_u_ne_x : u ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_w_ne_x : w ≠ x :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have p0000 := @gVex y
  have p0001 := @gVex z
  have freeVariableCertificate0 : t ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_y, not_false_eq_true]
  have freeVariableCertificate1 : u ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_u_ne_y, not_false_eq_true]
  have freeVariableCertificate2 : w ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_y, not_false_eq_true]
  have freeVariableCertificate3 : t ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_z, not_false_eq_true]
  have freeVariableCertificate4 : u ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_u_ne_z, not_false_eq_true]
  have freeVariableCertificate5 : w ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_z, not_false_eq_true]
  have p0002 :=
    @gOpkelins3kg t u w (.cv y) (.cv z) A (synCvv) (synCvv) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 freeVariableCertificate3
      freeVariableCertificate4 freeVariableCertificate5
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A)))
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ w from (by exact fresh_t_ne_w))
      (show u ≠ w from (by exact fresh_u_ne_w))
  have p0003 :=
    @gMp2an (.classMem (.cv y) (synCvv)) (.classMem (.cv z) (synCvv))
      (synWb (.classMem (synCopk (.cv y) (.cv z)) (synCins3k A)) (synWex t (synWex u
            (synWex w (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv t))))
                (.classEq (.cv z) (synCopk (.cv u) (.cv w)))
                (.classMem (synCopk (.cv t) (.cv u)) A))))))
      p0000 p0001 p0002
  have p0004 :=
    @gOpkeq12 (.cv y) (.cv z) (synCsn (synCsn (.cv t))) (synCopk (.cv u) (.cv w))
  have p0005 := @gVex t
  have p0006 := @gSnel1c (.cv t) p0005
  have p0007 := @gSnelpw1 (synCsn (.cv t)) (synC1c)
  have p0008 :=
    @gMpbir (.classMem (synCsn (synCsn (.cv t))) (synCpw1 (synC1c)))
      (.classMem (synCsn (.cv t)) (synC1c)) p0006 p0007
  have p0009 := @gVex u
  have p0010 := @gVex w
  have p0011 := @gOpkelxpk (.cv u) (.cv w) (synCvv) (synCvv) p0009 p0010
  have p0012 :=
    @gMpbir2an (.classMem (synCopk (.cv u) (.cv w)) (synCxpk (synCvv) (synCvv)))
      (.classMem (.cv u) (synCvv)) (.classMem (.cv w) (synCvv)) p0009 p0010 p0011
  have p0013 := @gSnex (synCsn (.cv t))
  have p0014 := @gOpkex (.cv u) (.cv w)
  have p0015 :=
    @gOpkelxpk (synCsn (synCsn (.cv t))) (synCopk (.cv u) (.cv w))
      (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)) p0013 p0014
  have p0016 :=
    @gMpbir2an
      (.classMem (synCopk (synCsn (synCsn (.cv t))) (synCopk (.cv u) (.cv w)))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (.classMem (synCsn (synCsn (.cv t))) (synCpw1 (synC1c)))
      (.classMem (synCopk (.cv u) (.cv w)) (synCxpk (synCvv) (synCvv))) p0008 p0012
      p0015
  have p0017 :=
    @gSyl6eqel
      (synWa (.classEq (.cv y) (synCsn (synCsn (.cv t))))
        (.classEq (.cv z) (synCopk (.cv u) (.cv w))))
      (synCopk (.cv y) (.cv z))
      (synCopk (synCsn (synCsn (.cv t))) (synCopk (.cv u) (.cv w)))
      (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) p0004 p0016
  have p0018 :=
    @gN3adant3 (.classEq (.cv y) (synCsn (synCsn (.cv t))))
      (.classEq (.cv z) (synCopk (.cv u) (.cv w)))
      (.classMem (synCopk (.cv y) (.cv z))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (.classMem (synCopk (.cv t) (.cv u)) A) p0017
  have freeVariableCertificate6 :
    w ∉
      ((Wff.classMem (synCopk (.cv y) (.cv z))
          (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_w_ne_y, fresh_w_ne_z, or_false,
      not_false_eq_true]
  have p0019 :=
    @gExlimiv
      (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv t))))
        (.classEq (.cv z) (synCopk (.cv u) (.cv w))) (.classMem (synCopk (.cv t) (.cv u)) A))
      (.classMem (synCopk (.cv y) (.cv z))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      w freeVariableCertificate6 p0018
  have freeVariableCertificate7 :
    t ∉
      ((Wff.classMem (synCopk (.cv y) (.cv z))
          (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_y, fresh_t_ne_z, or_false,
      not_false_eq_true]
  have freeVariableCertificate8 :
    u ∉
      ((Wff.classMem (synCopk (.cv y) (.cv z))
          (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_u_ne_y, fresh_u_ne_z, or_false,
      not_false_eq_true]
  have p0020 :=
    @gExlimivv
      (synWex w (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv t))))
          (.classEq (.cv z) (synCopk (.cv u) (.cv w)))
          (.classMem (synCopk (.cv t) (.cv u)) A)))
      (.classMem (synCopk (.cv y) (.cv z))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      t u freeVariableCertificate7 freeVariableCertificate8 p0019
  have p0021 :=
    @gSylbi (.classMem (synCopk (.cv y) (.cv z)) (synCins3k A))
      (synWex t (synWex u (synWex w (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv t))))
              (.classEq (.cv z) (synCopk (.cv u) (.cv w)))
              (.classMem (synCopk (.cv t) (.cv u)) A)))))
      (.classMem (synCopk (.cv y) (.cv z))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      p0003 p0020
  have p0022 :=
    @gGen2
      (.imp (.classMem (synCopk (.cv y) (.cv z)) (synCins3k A))
        (.classMem (synCopk (.cv y) (.cv z))
          (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))))
      y z p0021
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIns3k x y z w u t A
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A)))
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ w from (by exact fresh_t_ne_w))
      (show t ≠ x from (by exact fresh_t_ne_x)) (show t ≠ y from (by exact fresh_t_ne_y))
      (show t ≠ z from (by exact fresh_t_ne_z)) (show u ≠ w from (by exact fresh_u_ne_w))
      (show u ≠ x from (by exact fresh_u_ne_x)) (show u ≠ y from (by exact fresh_u_ne_y))
      (show u ≠ z from (by exact fresh_u_ne_z)) (show w ≠ x from (by exact fresh_w_ne_x))
      (show w ≠ y from (by exact fresh_w_ne_y)) (show w ≠ z from (by exact fresh_w_ne_z))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0024 :=
    @gOpkabssvvki
      (synWex t (synWex u (synWex w (synW3a (.classEq (.cv y) (synCsn (synCsn (.cv t))))
              (.classEq (.cv z) (synCopk (.cv u) (.cv w)))
              (.classMem (synCopk (.cv t) (.cv u)) A)))))
      x y z (synCins3k A) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) p0023
  have freeVariableCertificate9 :
    y ∉ ((synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate10 :
    z ∉ ((synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0025 :=
    @gSsrelk y z (synCins3k A)
      (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))
      (by
        exact
          (show y ∉ ((synCins3k A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
      (by
        exact
          (show z ∉ ((synCins3k A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
              exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))))
      freeVariableCertificate9 freeVariableCertificate10
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @gMpbir
      (synWss (synCins3k A) (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (.all y (.all z (.imp (.classMem (synCopk (.cv y) (.cv z)) (synCins3k A))
            (.classMem (synCopk (.cv y) (.cv z))
              (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))))))
      p0022 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_idkssvvk`. -/
@[expose]
noncomputable def gIdkssvvk :
    Nominal.NPrf (synWss (synCidk) (synCxpk (synCvv) (synCvv))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIdk x y z
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @gOpkabssvvki (.objEq y z) x y z (synCidk) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_elimaksn`. -/
@[expose]
noncomputable def gElimaksn (A : Class) (B : Class) (C : Class)
    (hyp_elimaksn_1 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_elimaksn_2 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem C (synCimak A (synCsn B))) (.classMem (synCopk B C) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
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
  have p0000 :=
    @gElimak x A (synCsn B) C (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by
        exact
          (show x ∉ ((synCsn B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))))
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C))) hyp_elimaksn_2
  have p0001 := @gOpkeq1 (.cv x) B C
  have p0002 := @gEleq1d (.classEq (.cv x) B) (synCopk (.cv x) C) (synCopk B C) A p0001
  have freeVariableCertificate0 : x ∉ ((Wff.classMem (synCopk B C) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, or_false, not_false_eq_true]
  have p0003 :=
    @gRexsn (.classMem (synCopk (.cv x) C) A) (.classMem (synCopk B C) A) x B
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) freeVariableCertificate0
      hyp_elimaksn_1 p0002
  have p0004 :=
    @gBitri (.classMem C (synCimak A (synCsn B)))
      (synWrex x (synCsn B) (.classMem (synCopk (.cv x) C) A))
      (.classMem (synCopk B C) A) p0000 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart013`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_xpkvexg`. -/
@[expose]
noncomputable def gXpkvexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCxpk (synCvv) A) (synCvv))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have p0000 := @gXpkeq2 (.cv x) A (synCvv)
  have p0001 :=
    @gEleq1d (.classEq (.cv x) A) (synCxpk (synCvv) (.cv x)) (synCxpk (synCvv) A)
      (synCvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralXpViaCompletenessDev003.axXp x y z a b
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show x ≠ a from (by exact fresh_x_ne_a)) (show x ≠ b from (by exact fresh_x_ne_b))
      (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ a from (by exact fresh_y_ne_a))
      (show y ≠ b from (by exact fresh_y_ne_b)) (show z ≠ a from (by exact fresh_z_ne_a))
      (show z ≠ b from (by exact fresh_z_ne_b)) (show a ≠ b from (by exact fresh_a_ne_b))
  have freeVariableCertificate0 : y ∉ ((synCxpk (synCvv) (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0003 := @gIsset y (synCxpk (synCvv) (.cv x)) freeVariableCertificate0
  have freeVariableCertificate1 : z ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_y, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((synCxpk (synCvv) (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_z_ne_x, or_false, not_false_eq_true]
  have p0004 :=
    @gDfcleq z (.cv y) (synCxpk (synCvv) (.cv x)) freeVariableCertificate1
      freeVariableCertificate2
  have freeVariableCertificate3 : a ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_z, not_false_eq_true]
  have freeVariableCertificate4 : b ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_z, not_false_eq_true]
  have freeVariableCertificate5 : a ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_a_ne_x, not_false_eq_true]
  have freeVariableCertificate6 : b ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_b_ne_x, not_false_eq_true]
  have p0005 :=
    @gElxpk a b (.cv z) (synCvv) (.cv x) freeVariableCertificate3
      freeVariableCertificate4
      (by
        exact
          (show a ∉ ((synCvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show b ∉ ((synCvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate5 freeVariableCertificate6
      (show a ≠ b from (by exact fresh_a_ne_b))
  have p0006 := @gVex a
  have p0007 := @gBiantrur (.classMem (.cv a) (synCvv)) (.objMem b x) p0006
  have p0008 :=
    @gAnbi2i (.objMem b x) (synWa (.classMem (.cv a) (synCvv)) (.objMem b x))
      (.classEq (.cv z) (synCopk (.cv a) (.cv b))) p0007
  have p0009 :=
    @gN2exbii (synWa (.classEq (.cv z) (synCopk (.cv a) (.cv b))) (.objMem b x))
      (synWa (.classEq (.cv z) (synCopk (.cv a) (.cv b)))
        (synWa (.classMem (.cv a) (synCvv)) (.objMem b x)))
      a b p0008
  have p0010_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv z) (synCxpk (synCvv) (.cv x))) (synWex a (synWex b
            (synWa (.classEq (.cv z) (synCopk (.cv a) (.cv b)))
              (synWa (.classMem (.cv a) (synCvv)) (.objMem b x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCxpk synWex synCvv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0010 :=
    @gBitr4i (.classMem (.cv z) (synCxpk (synCvv) (.cv x)))
      (synWex a (synWex b (synWa (.classEq (.cv z) (synCopk (.cv a) (.cv b)))
            (synWa (.classMem (.cv a) (synCvv)) (.objMem b x)))))
      (synWex a
        (synWex b (synWa (.classEq (.cv z) (synCopk (.cv a) (.cv b))) (.objMem b x))))
      p0010_e00_recanon p0009
  have p0011 :=
    @gBibi2i (.classMem (.cv z) (synCxpk (synCvv) (.cv x)))
      (synWex a
        (synWex b (synWa (.classEq (.cv z) (synCopk (.cv a) (.cv b))) (.objMem b x))))
      (.objMem z y) p0010
  have p0012 :=
    @gAlbii (synWb (.objMem z y) (.classMem (.cv z) (synCxpk (synCvv) (.cv x))))
      (synWb (.objMem z y) (synWex a (synWex b
            (synWa (.classEq (.cv z) (synCopk (.cv a) (.cv b))) (.objMem b x)))))
      z p0011
  have p0013_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv y) (synCxpk (synCvv) (.cv x))) (.all z
          (synWb (.objMem z y) (.classMem (.cv z) (synCxpk (synCvv) (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCxpk synWex synCvv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0013 :=
    @gBitri (.classEq (.cv y) (synCxpk (synCvv) (.cv x)))
      (.all z (synWb (.objMem z y) (.classMem (.cv z) (synCxpk (synCvv) (.cv x)))))
      (.all z (synWb (.objMem z y) (synWex a (synWex b
              (synWa (.classEq (.cv z) (synCopk (.cv a) (.cv b))) (.objMem b x))))))
      p0013_e00_recanon p0012
  have p0014 :=
    @gExbii (.classEq (.cv y) (synCxpk (synCvv) (.cv x)))
      (.all z (synWb (.objMem z y) (synWex a (synWex b
              (synWa (.classEq (.cv z) (synCopk (.cv a) (.cv b))) (.objMem b x))))))
      y p0013
  have p0015 :=
    @gBitri (.classMem (synCxpk (synCvv) (.cv x)) (synCvv))
      (synWex y (.classEq (.cv y) (synCxpk (synCvv) (.cv x))))
      (synWex y (.all z (synWb (.objMem z y) (synWex a (synWex b
                (synWa (.classEq (.cv z) (synCopk (.cv a) (.cv b))) (.objMem b x)))))))
      p0003 p0014
  have p0016 :=
    @gMpbir (.classMem (synCxpk (synCvv) (.cv x)) (synCvv))
      (synWex y (.all z (synWb (.objMem z y) (synWex a (synWex b
                (synWa (.classEq (.cv z) (synCopk (.cv a) (.cv b))) (.objMem b x)))))))
      p0002 p0015
  have freeVariableCertificate7 :
    x ∉ ((Wff.classMem (synCxpk (synCvv) A) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0017 :=
    @gVtoclg (.classMem (synCxpk (synCvv) (.cv x)) (synCvv))
      (.classMem (synCxpk (synCvv) A) (synCvv)) x A V
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate7
      p0001 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_cnvkexg`. -/
@[expose]
noncomputable def gCnvkexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCcnvk A) (synCvv))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let y : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_w_ne_y : w ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have p0000 := @gCnvkeq (.cv x) A
  have p0001 :=
    @gEleq1d (.classEq (.cv x) A) (synCcnvk (.cv x)) (synCcnvk A) (synCvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axCnv x y z
      w (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w))
      (show z ≠ w from (by exact fresh_z_ne_w))
  have p0003 := @gInss1 (synCxpk (synCvv) (synCvv)) (.cv y)
  have p0004 := @gCnvkssvvk (.cv x)
  have freeVariableCertificate0 :
    z ∉ ((synCin (synCxpk (synCvv) (synCvv)) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    w ∉ ((synCin (synCxpk (synCvv) (synCvv)) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_w_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((synCcnvk (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
      not_false_eq_true]
  have freeVariableCertificate3 : w ∉ ((synCcnvk (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_x,
      not_false_eq_true]
  have p0005 :=
    @gEqrelk z w (synCin (synCxpk (synCvv) (synCvv)) (.cv y)) (synCcnvk (.cv x))
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      freeVariableCertificate3 (show z ≠ w from (by exact fresh_z_ne_w))
  have p0006 :=
    @gMp2an
      (synWss (synCin (synCxpk (synCvv) (synCvv)) (.cv y)) (synCxpk (synCvv) (synCvv)))
      (synWss (synCcnvk (.cv x)) (synCxpk (synCvv) (synCvv)))
      (synWb (.classEq (synCin (synCxpk (synCvv) (synCvv)) (.cv y)) (synCcnvk (.cv x)))
        (.all z (.all w (synWb (.classMem (synCopk (.cv z) (.cv w))
                (synCin (synCxpk (synCvv) (synCvv)) (.cv y)))
              (.classMem (synCopk (.cv z) (.cv w)) (synCcnvk (.cv x)))))))
      p0003 p0004 p0005
  have p0007 := @gVex z
  have p0008 := @gVex w
  have p0009 := @gOpkelxpk (.cv z) (.cv w) (synCvv) (synCvv) p0007 p0008
  have p0010 :=
    @gMpbir2an (.classMem (synCopk (.cv z) (.cv w)) (synCxpk (synCvv) (synCvv)))
      (.classMem (.cv z) (synCvv)) (.classMem (.cv w) (synCvv)) p0007 p0008 p0009
  have p0011 := @gElin (synCopk (.cv z) (.cv w)) (synCxpk (synCvv) (synCvv)) (.cv y)
  have p0012 :=
    @gMpbiran
      (.classMem (synCopk (.cv z) (.cv w)) (synCin (synCxpk (synCvv) (synCvv)) (.cv y)))
      (.classMem (synCopk (.cv z) (.cv w)) (synCxpk (synCvv) (synCvv)))
      (.classMem (synCopk (.cv z) (.cv w)) (.cv y)) p0010 p0011
  have p0013 := @gOpkelcnvk (.cv z) (.cv w) (.cv x) p0007 p0008
  have p0014 :=
    @gBibi12i
      (.classMem (synCopk (.cv z) (.cv w)) (synCin (synCxpk (synCvv) (synCvv)) (.cv y)))
      (.classMem (synCopk (.cv z) (.cv w)) (.cv y))
      (.classMem (synCopk (.cv z) (.cv w)) (synCcnvk (.cv x)))
      (.classMem (synCopk (.cv w) (.cv z)) (.cv x)) p0012 p0013
  have p0015 :=
    @gN2albii
      (synWb (.classMem (synCopk (.cv z) (.cv w))
          (synCin (synCxpk (synCvv) (synCvv)) (.cv y)))
        (.classMem (synCopk (.cv z) (.cv w)) (synCcnvk (.cv x))))
      (synWb (.classMem (synCopk (.cv z) (.cv w)) (.cv y))
        (.classMem (synCopk (.cv w) (.cv z)) (.cv x)))
      z w p0014
  have p0016 :=
    @gBitri
      (.classEq (synCin (synCxpk (synCvv) (synCvv)) (.cv y)) (synCcnvk (.cv x)))
      (.all z (.all w (synWb (.classMem (synCopk (.cv z) (.cv w))
              (synCin (synCxpk (synCvv) (synCvv)) (.cv y)))
            (.classMem (synCopk (.cv z) (.cv w)) (synCcnvk (.cv x))))))
      (.all z (.all w (synWb (.classMem (synCopk (.cv z) (.cv w)) (.cv y))
            (.classMem (synCopk (.cv w) (.cv z)) (.cv x)))))
      p0006 p0015
  have p0017 :=
    @gBiimpri
      (.classEq (synCin (synCxpk (synCvv) (synCvv)) (.cv y)) (synCcnvk (.cv x)))
      (.all z (.all w (synWb (.classMem (synCopk (.cv z) (.cv w)) (.cv y))
            (.classMem (synCopk (.cv w) (.cv z)) (.cv x)))))
      p0016
  have p0018 := @gVvex
  have p0019 := @gXpkvexg (synCvv) (synCvv)
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := @gVex y
  have p0022 := @gInex (synCxpk (synCvv) (synCvv)) (.cv y) p0020 p0021
  have p0023 :=
    @gSyl6eqelr
      (.all z (.all w (synWb (.classMem (synCopk (.cv z) (.cv w)) (.cv y))
            (.classMem (synCopk (.cv w) (.cv z)) (.cv x)))))
      (synCcnvk (.cv x)) (synCin (synCxpk (synCvv) (synCvv)) (.cv y)) (synCvv) p0017
      p0022
  have freeVariableCertificate4 : y ∉ ((Wff.classMem (synCcnvk (.cv x)) (synCvv))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0024 :=
    @gExlimiv
      (.all z (.all w (synWb (.classMem (synCopk (.cv z) (.cv w)) (.cv y))
            (.classMem (synCopk (.cv w) (.cv z)) (.cv x)))))
      (.classMem (synCcnvk (.cv x)) (synCvv)) y freeVariableCertificate4 p0023
  have p0025 := Nominal.mp p0002 p0024
  have freeVariableCertificate5 : x ∉ ((Wff.classMem (synCcnvk A) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0026 :=
    @gVtoclg (.classMem (synCcnvk (.cv x)) (synCvv))
      (.classMem (synCcnvk A) (synCvv)) x A V
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate5
      p0001 p0025
  exact p0026

/-- Checked nominal proof certificate identified upstream as `g_cnvkex`. -/
@[expose]
noncomputable def gCnvkex (A : Class)
    (hyp_cnvkex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCcnvk A) (synCvv)) :=
  by
  have p0000 := @gCnvkexg A (synCvv)
  have p0001 := Nominal.mp hyp_cnvkex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_xpkexg`. -/
@[expose]
noncomputable def gXpkexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCxpk A B) (synCvv))) :=
  by
  have p0000 := @gCnvkxpk (synCvv) A
  have p0001 := @gXpkvexg A V
  have p0002 := @gCnvkexg (synCxpk (synCvv) A) (synCvv)
  have p0003 :=
    @gSyl (.classMem A V) (.classMem (synCxpk (synCvv) A) (synCvv))
      (.classMem (synCcnvk (synCxpk (synCvv) A)) (synCvv)) p0001 p0002
  have p0004 :=
    @gSyl5eqelr (.classMem A V) (synCxpk A (synCvv)) (synCcnvk (synCxpk (synCvv) A))
      (synCvv) p0000 p0003
  have p0005 := @gXpkvexg B W
  have p0006 := @gInxpk A (synCvv) (synCvv) B
  have p0007 := @gInv1 A
  have p0008 := @gIncom (synCvv) B
  have p0009 := @gInv1 B
  have p0010 := @gEqtri (synCin (synCvv) B) (synCin B (synCvv)) B p0008 p0009
  have p0011 := @gXpkeq12i (synCin A (synCvv)) A (synCin (synCvv) B) B p0007 p0010
  have p0012 :=
    @gEqtri (synCin (synCxpk A (synCvv)) (synCxpk (synCvv) B))
      (synCxpk (synCin A (synCvv)) (synCin (synCvv) B)) (synCxpk A B) p0006 p0011
  have p0013 := @gInexg (synCxpk A (synCvv)) (synCxpk (synCvv) B) (synCvv) (synCvv)
  have p0014 :=
    @gSyl5eqelr
      (synWa (.classMem (synCxpk A (synCvv)) (synCvv))
        (.classMem (synCxpk (synCvv) B) (synCvv)))
      (synCxpk A B) (synCin (synCxpk A (synCvv)) (synCxpk (synCvv) B)) (synCvv)
      p0012 p0013
  have p0015 :=
    @gSyl2an (.classMem A V) (.classMem (synCxpk A (synCvv)) (synCvv))
      (.classMem (synCxpk (synCvv) B) (synCvv)) (.classMem (synCxpk A B) (synCvv))
      (.classMem B W) p0004 p0005 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_xpkex`. -/
@[expose]
noncomputable def gXpkex (A : Class) (B : Class)
    (hyp_xpkex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_xpkex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCxpk A B) (synCvv)) :=
  by
  have p0000 := @gXpkexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCxpk A B) (synCvv)) hyp_xpkex_1 hyp_xpkex_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_p6exg`. -/
@[expose]
noncomputable def gP6exg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCp6 A) (synCvv))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have p0000 := @gP6eq (.cv x) A
  have p0001 :=
    @gEleq1d (.classEq (.cv x) A) (synCp6 (.cv x)) (synCp6 A) (synCvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axTypeLower
      x y z w (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w))
      (show z ≠ w from (by exact fresh_z_ne_w))
  have freeVariableCertificate0 : z ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_y, not_false_eq_true]
  have freeVariableCertificate1 : z ∉ ((synCp6 (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
      not_false_eq_true]
  have p0003 :=
    @gDfcleq z (.cv y) (synCp6 (.cv x)) freeVariableCertificate0
      freeVariableCertificate1
  have p0004 := @gVex z
  have freeVariableCertificate2 : w ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_z, not_false_eq_true]
  have freeVariableCertificate3 : w ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_x, not_false_eq_true]
  have p0005 :=
    @gElp6 w (.cv z) (.cv x) (synCvv) freeVariableCertificate2 freeVariableCertificate3
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gBibi2i (.classMem (.cv z) (synCp6 (.cv x)))
      (.all w (.classMem (synCopk (.cv w) (synCsn (.cv z))) (.cv x))) (.objMem z y)
      p0006
  have p0008 :=
    @gAlbii (synWb (.objMem z y) (.classMem (.cv z) (synCp6 (.cv x))))
      (synWb (.objMem z y) (.all w (.classMem (synCopk (.cv w) (synCsn (.cv z))) (.cv x))))
      z p0007
  have p0009_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv y) (synCp6 (.cv x)))
        (.all z (synWb (.objMem z y) (.classMem (.cv z) (synCp6 (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCp6 synWss synCin synCcompl synCnin synWnan synWa synCxpk
          synWex synCvv synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0009 :=
    @gBitri (.classEq (.cv y) (synCp6 (.cv x)))
      (.all z (synWb (.objMem z y) (.classMem (.cv z) (synCp6 (.cv x)))))
      (.all z (synWb (.objMem z y)
          (.all w (.classMem (synCopk (.cv w) (synCsn (.cv z))) (.cv x)))))
      p0009_e00_recanon p0008
  have p0010 :=
    @gBiimpri (.classEq (.cv y) (synCp6 (.cv x)))
      (.all z (synWb (.objMem z y)
          (.all w (.classMem (synCopk (.cv w) (synCsn (.cv z))) (.cv x)))))
      p0009
  have p0011 := @gVex y
  have p0012 :=
    @gSyl6eqelr
      (.all z (synWb (.objMem z y)
          (.all w (.classMem (synCopk (.cv w) (synCsn (.cv z))) (.cv x)))))
      (synCp6 (.cv x)) (.cv y) (synCvv) p0010 p0011
  have freeVariableCertificate4 : y ∉ ((Wff.classMem (synCp6 (.cv x)) (synCvv))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0013 :=
    @gExlimiv
      (.all z (synWb (.objMem z y)
          (.all w (.classMem (synCopk (.cv w) (synCsn (.cv z))) (.cv x)))))
      (.classMem (synCp6 (.cv x)) (synCvv)) y freeVariableCertificate4 p0012
  have p0014 := Nominal.mp p0002 p0013
  have freeVariableCertificate5 : x ∉ ((Wff.classMem (synCp6 A) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0015 :=
    @gVtoclg (.classMem (synCp6 (.cv x)) (synCvv)) (.classMem (synCp6 A) (synCvv)) x
      A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate5 p0001 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_dfuni12`. -/
@[expose]
noncomputable def gDfuni12 (A : Class) :
    Nominal.NPrf (.classEq (synCuni1 A) (synCp6 (synCxpk (synCvv) A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have freeVariableCertificate0 : z ∉ ((Wff.classMem (synCsn (.cv x)) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_not_A, or_false, not_false_eq_true]
  have p0000 :=
    @gN1927v (.classMem (.cv z) (synCvv)) (.classMem (synCsn (.cv x)) A) z
      freeVariableCertificate0
  have p0001 := @gVex z
  have p0002 := @gSnex (.cv x)
  have p0003 := @gOpkelxpk (.cv z) (synCsn (.cv x)) (synCvv) A p0001 p0002
  have p0004 :=
    @gAlbii (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCxpk (synCvv) A))
      (synWa (.classMem (.cv z) (synCvv)) (.classMem (synCsn (.cv x)) A)) z p0003
  have p0005 := Nominal.gen p0001 z
  have p0006 :=
    @gBiantrur (.all z (.classMem (.cv z) (synCvv))) (.classMem (synCsn (.cv x)) A)
      p0005
  have p0007 :=
    @gN3bitr4ri
      (.all z (synWa (.classMem (.cv z) (synCvv)) (.classMem (synCsn (.cv x)) A)))
      (synWa (.all z (.classMem (.cv z) (synCvv))) (.classMem (synCsn (.cv x)) A))
      (.all z (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCxpk (synCvv) A)))
      (.classMem (synCsn (.cv x)) A) p0000 p0004 p0006
  have p0008 := @gVex x
  have p0009 := @gEluni1 (.cv x) A p0008
  have freeVariableCertificate1 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((synCxpk (synCvv) A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_z_not_A, or_false, not_false_eq_true]
  have p0010 :=
    @gElp6 z (.cv x) (synCxpk (synCvv) A) (synCvv) freeVariableCertificate1
      freeVariableCertificate2
  have p0011 := Nominal.mp p0008 p0010
  have p0012 :=
    @gN3bitr4i (.classMem (synCsn (.cv x)) A)
      (.all z (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCxpk (synCvv) A)))
      (.classMem (.cv x) (synCuni1 A))
      (.classMem (.cv x) (synCp6 (synCxpk (synCvv) A))) p0007 p0009 p0011
  have freeVariableCertificate3 : x ∉ ((synCp6 (synCxpk (synCvv) A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0013 :=
    @gEqriv x (synCuni1 A) (synCp6 (synCxpk (synCvv) A))
      (by
        exact
          (show x ∉ ((synCuni1 A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate3 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_uni1exg`. -/
@[expose]
noncomputable def gUni1exg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCuni1 A) (synCvv))) :=
  by
  have p0000 := @gDfuni12 A
  have p0001 := @gVvex
  have p0002 := @gXpkexg (synCvv) A (synCvv) V
  have p0003 :=
    @gMpan (.classMem (synCvv) (synCvv)) (.classMem A V)
      (.classMem (synCxpk (synCvv) A) (synCvv)) p0001 p0002
  have p0004 := @gP6exg (synCxpk (synCvv) A) (synCvv)
  have p0005 :=
    @gSyl (.classMem A V) (.classMem (synCxpk (synCvv) A) (synCvv))
      (.classMem (synCp6 (synCxpk (synCvv) A)) (synCvv)) p0003 p0004
  have p0006 :=
    @gSyl5eqel (.classMem A V) (synCuni1 A) (synCp6 (synCxpk (synCvv) A)) (synCvv)
      p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_uni1ex`. -/
@[expose]
noncomputable def gUni1ex (A : Class)
    (hyp_uni1ex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCuni1 A) (synCvv)) :=
  by
  have p0000 := @gUni1exg A (synCvv)
  have p0001 := Nominal.mp hyp_uni1ex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ssetkex`. -/
@[expose]
noncomputable def gSsetkex : Nominal.NPrf (.classMem (synCssetk) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have p0000 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axSset x y z
      w (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w))
      (show z ≠ w from (by exact fresh_z_ne_w))
  have p0001 := @gInss1 (synCxpk (synCvv) (synCvv)) (.cv x)
  have p0002 := @gSsetkssvvk
  have freeVariableCertificate0 :
    y ∉ ((synCin (synCxpk (synCvv) (synCvv)) (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_y_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    z ∉ ((synCin (synCxpk (synCvv) (synCvv)) (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_z_ne_x, or_false, not_false_eq_true]
  have p0003 :=
    @gEqrelk y z (synCin (synCxpk (synCvv) (synCvv)) (.cv x)) (synCssetk)
      freeVariableCertificate0 freeVariableCertificate1
      (by
        exact
          (show y ∉ ((synCssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show z ∉ ((synCssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0004 :=
    @gMp2an
      (synWss (synCin (synCxpk (synCvv) (synCvv)) (.cv x)) (synCxpk (synCvv) (synCvv)))
      (synWss (synCssetk) (synCxpk (synCvv) (synCvv)))
      (synWb (.classEq (synCin (synCxpk (synCvv) (synCvv)) (.cv x)) (synCssetk)) (.all y
          (.all z (synWb (.classMem (synCopk (.cv y) (.cv z))
                (synCin (synCxpk (synCvv) (synCvv)) (.cv x)))
              (.classMem (synCopk (.cv y) (.cv z)) (synCssetk))))))
      p0001 p0002 p0003
  have p0005 := @gVex y
  have p0006 := @gVex z
  have p0007 := @gOpkelxpk (.cv y) (.cv z) (synCvv) (synCvv) p0005 p0006
  have p0008 :=
    @gMpbir2an (.classMem (synCopk (.cv y) (.cv z)) (synCxpk (synCvv) (synCvv)))
      (.classMem (.cv y) (synCvv)) (.classMem (.cv z) (synCvv)) p0005 p0006 p0007
  have p0009 := @gElin (synCopk (.cv y) (.cv z)) (synCxpk (synCvv) (synCvv)) (.cv x)
  have p0010 :=
    @gMpbiran
      (.classMem (synCopk (.cv y) (.cv z)) (synCin (synCxpk (synCvv) (synCvv)) (.cv x)))
      (.classMem (synCopk (.cv y) (.cv z)) (synCxpk (synCvv) (synCvv)))
      (.classMem (synCopk (.cv y) (.cv z)) (.cv x)) p0008 p0009
  have p0011 := @gOpkelssetkg (.cv y) (.cv z) (synCvv) (synCvv)
  have p0012 :=
    @gMp2an (.classMem (.cv y) (synCvv)) (.classMem (.cv z) (synCvv))
      (synWb (.classMem (synCopk (.cv y) (.cv z)) (synCssetk)) (synWss (.cv y) (.cv z)))
      p0005 p0006 p0011
  have freeVariableCertificate2 : w ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_y, not_false_eq_true]
  have freeVariableCertificate3 : w ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_z, not_false_eq_true]
  have p0013 :=
    @gDfss2 w (.cv y) (.cv z) freeVariableCertificate2 freeVariableCertificate3
  have p0014_e01_recanon :
    Nominal.NPrf
      (synWb (synWss (.cv y) (.cv z)) (.all w (.imp (.objMem w y) (.objMem w z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @gBitri (.classMem (synCopk (.cv y) (.cv z)) (synCssetk)) (synWss (.cv y) (.cv z))
      (.all w (.imp (.objMem w y) (.objMem w z))) p0012 p0014_e01_recanon
  have p0015 :=
    @gBibi12i
      (.classMem (synCopk (.cv y) (.cv z)) (synCin (synCxpk (synCvv) (synCvv)) (.cv x)))
      (.classMem (synCopk (.cv y) (.cv z)) (.cv x))
      (.classMem (synCopk (.cv y) (.cv z)) (synCssetk))
      (.all w (.imp (.objMem w y) (.objMem w z))) p0010 p0014
  have p0016 :=
    @gN2albii
      (synWb (.classMem (synCopk (.cv y) (.cv z))
          (synCin (synCxpk (synCvv) (synCvv)) (.cv x)))
        (.classMem (synCopk (.cv y) (.cv z)) (synCssetk)))
      (synWb (.classMem (synCopk (.cv y) (.cv z)) (.cv x))
        (.all w (.imp (.objMem w y) (.objMem w z))))
      y z p0015
  have p0017 :=
    @gBitri (.classEq (synCin (synCxpk (synCvv) (synCvv)) (.cv x)) (synCssetk))
      (.all y (.all z (synWb (.classMem (synCopk (.cv y) (.cv z))
              (synCin (synCxpk (synCvv) (synCvv)) (.cv x)))
            (.classMem (synCopk (.cv y) (.cv z)) (synCssetk)))))
      (.all y (.all z (synWb (.classMem (synCopk (.cv y) (.cv z)) (.cv x))
            (.all w (.imp (.objMem w y) (.objMem w z))))))
      p0004 p0016
  have p0018 :=
    @gBiimpri (.classEq (synCin (synCxpk (synCvv) (synCvv)) (.cv x)) (synCssetk))
      (.all y (.all z (synWb (.classMem (synCopk (.cv y) (.cv z)) (.cv x))
            (.all w (.imp (.objMem w y) (.objMem w z))))))
      p0017
  have p0019 := @gVvex
  have p0020 := @gXpkvexg (synCvv) (synCvv)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @gVex x
  have p0023 := @gInex (synCxpk (synCvv) (synCvv)) (.cv x) p0021 p0022
  have p0024 :=
    @gSyl6eqelr
      (.all y (.all z (synWb (.classMem (synCopk (.cv y) (.cv z)) (.cv x))
            (.all w (.imp (.objMem w y) (.objMem w z))))))
      (synCssetk) (synCin (synCxpk (synCvv) (synCvv)) (.cv x)) (synCvv) p0018 p0023
  have freeVariableCertificate4 : x ∉ ((Wff.classMem (synCssetk) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0025 :=
    @gExlimiv
      (.all y (.all z (synWb (.classMem (synCopk (.cv y) (.cv z)) (.cv x))
            (.all w (.imp (.objMem w y) (.objMem w z))))))
      (.classMem (synCssetk) (synCvv)) x freeVariableCertificate4 p0024
  have p0026 := Nominal.mp p0000 p0025
  exact p0026


end NFChoice.DirectNominalPrf.WPPReplay

end
