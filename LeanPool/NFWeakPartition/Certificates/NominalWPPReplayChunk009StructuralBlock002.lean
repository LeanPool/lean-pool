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

@[expose]
noncomputable def g_otkelins3kg (A : Class) (B : Class) (C : Class) (D : Class)
    (T : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem B W) (.classMem C T))
        (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins3k D))
          (.classMem (syn_copk A B) D))) :=
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
    @g_opkelins3kg x y z (syn_csn (syn_csn A)) (syn_copk B C) D (syn_cvv) (syn_cvv)
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
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins3k D))
        (syn_wex x (syn_wex y (syn_wex z
              (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
                (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv y)) D))))))
      p0000 p0001 p0002
  have p0004 :=
    @g_n_3anass (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
      (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
      (.classMem (syn_copk (.cv x) (.cv y)) D)
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
        (.classMem (syn_copk (.cv x) (.cv y)) D))
      p0011
  have p0013 :=
    @g_bitri
      (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
        (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk (.cv x) (.cv y)) D))
      (syn_wa (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
        (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
          (.classMem (syn_copk (.cv x) (.cv y)) D)))
      (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
          (.classMem (syn_copk (.cv x) (.cv y)) D)))
      p0004 p0012
  have p0014 :=
    @g_n_2exbii
      (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
        (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk (.cv x) (.cv y)) D))
      (syn_wa (.classEq (.cv x) A) (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
          (.classMem (syn_copk (.cv x) (.cv y)) D)))
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
        (.classMem (syn_copk (.cv x) (.cv y)) D))
      y z freeVariableCertificate6 freeVariableCertificate7
  have p0016 :=
    @g_bitri
      (syn_wex y (syn_wex z
          (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
            (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk (.cv x) (.cv y)) D))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv x) A)
            (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv y)) D)))))
      (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z
            (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv y)) D)))))
      p0014 p0015
  have p0017 :=
    @g_exbii
      (syn_wex y (syn_wex z
          (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
            (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk (.cv x) (.cv y)) D))))
      (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z
            (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv y)) D)))))
      x p0016
  have p0018 := @g_opkeq1 (.cv x) A (.cv y)
  have p0019 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_copk (.cv x) (.cv y)) (syn_copk A (.cv y)) D p0018
  have p0020 :=
    @g_anbi2d (.classEq (.cv x) A) (.classMem (syn_copk (.cv x) (.cv y)) D)
      (.classMem (syn_copk A (.cv y)) D)
      (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z))) p0019
  have p0021 :=
    @g_n_2exbidv (.classEq (.cv x) A)
      (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk (.cv x) (.cv y)) D))
      (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk A (.cv y)) D))
      y z freeVariableCertificate6 freeVariableCertificate7 p0020
  have freeVariableCertificate8 :
    x ∉
      ((syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk A (.cv y)) D))))).fv :=
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
    @g_ceqsexgv
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk (.cv x) (.cv y)) D))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk A (.cv y)) D))))
      x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate8 p0021
  have p0023 :=
    @g_syl5bb
      (syn_wex x (syn_wex y (syn_wex z
            (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
              (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv y)) D)))))
      (syn_wex x (syn_wa (.classEq (.cv x) A) (syn_wex y (syn_wex z
              (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv y)) D))))))
      (.classMem A V)
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk A (.cv y)) D))))
      p0017 p0022
  have p0024 :=
    @g_n_3ad2ant1 (.classMem A V) (.classMem B W)
      (syn_wb (syn_wex x (syn_wex y (syn_wex z
              (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
                (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
                (.classMem (syn_copk (.cv x) (.cv y)) D))))) (syn_wex y (syn_wex z
            (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk A (.cv y)) D)))))
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
      (.classMem (syn_copk A (.cv y)) D) p0030
  have p0032 :=
    @g_anass (.classEq (.cv y) B) (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)
  have p0033 :=
    @g_syl6bb (.classMem C T)
      (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk A (.cv y)) D))
      (syn_wa (syn_wa (.classEq (.cv y) B) (.classEq (.cv z) C))
        (.classMem (syn_copk A (.cv y)) D))
      (syn_wa (.classEq (.cv y) B)
        (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)))
      p0031 p0032
  have freeVariableCertificate9 : y ∉ ((Wff.classMem C T)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
      fresh_y_not_C, fresh_y_not_T, or_false, not_false_eq_true]
  have freeVariableCertificate10 : z ∉ ((Wff.classMem C T)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
      fresh_z_not_C, fresh_z_not_T, or_false, not_false_eq_true]
  have p0034 :=
    @g_n_2exbidv (.classMem C T)
      (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
        (.classMem (syn_copk A (.cv y)) D))
      (syn_wa (.classEq (.cv y) B)
        (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)))
      y z freeVariableCertificate9 freeVariableCertificate10 p0033
  have freeVariableCertificate11 : z ∉ ((Wff.classEq (.cv y) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_y, fresh_z_not_B, or_false, not_false_eq_true]
  have p0035 :=
    @g_exdistr (.classEq (.cv y) B)
      (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)) y z
      freeVariableCertificate11
  have p0036 :=
    @g_syl6bb (.classMem C T)
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk A (.cv y)) D))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv y) B)
            (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)))))
      (syn_wex y (syn_wa (.classEq (.cv y) B)
          (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)))))
      p0034 p0035
  have p0037 :=
    @g_adantl (.classMem C T)
      (syn_wb (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk A (.cv y)) D)))) (syn_wex y (syn_wa (.classEq (.cv y) B)
            (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D))))))
      (.classMem B W) p0036
  have p0038 := @g_opkeq2 (.cv y) B A
  have p0039 := @g_eleq1d (.classEq (.cv y) B) (syn_copk A (.cv y)) (syn_copk A B) D p0038
  have p0040 :=
    @g_anbi2d (.classEq (.cv y) B) (.classMem (syn_copk A (.cv y)) D)
      (.classMem (syn_copk A B) D) (.classEq (.cv z) C) p0039
  have p0041 :=
    @g_exbidv (.classEq (.cv y) B)
      (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D))
      (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A B) D)) z
      freeVariableCertificate11 p0040
  have freeVariableCertificate12 :
    y ∉ ((syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A B) D)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_C, fresh_y_not_A,
      fresh_y_not_B, fresh_y_not_D, or_false, and_false, not_false_eq_true]
  have p0042 :=
    @g_ceqsexgv
      (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)))
      (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A B) D))) y B W
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) freeVariableCertificate12
      p0041
  have p0043 := @g_biidd (.classEq (.cv z) C) (.classMem (syn_copk A B) D)
  have freeVariableCertificate13 : z ∉ ((Wff.classMem (syn_copk A B) D)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, fresh_z_not_D, or_false, not_false_eq_true]
  have p0044 :=
    @g_ceqsexgv (.classMem (syn_copk A B) D) (.classMem (syn_copk A B) D) z C T
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C))) freeVariableCertificate13
      p0043
  have p0045 :=
    @g_sylan9bb (.classMem B W)
      (syn_wex y (syn_wa (.classEq (.cv y) B)
          (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)))))
      (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A B) D)))
      (.classMem C T) (.classMem (syn_copk A B) D) p0042 p0044
  have p0046 :=
    @g_bitrd (syn_wa (.classMem B W) (.classMem C T))
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk A (.cv y)) D))))
      (syn_wex y (syn_wa (.classEq (.cv y) B)
          (syn_wex z (syn_wa (.classEq (.cv z) C) (.classMem (syn_copk A (.cv y)) D)))))
      (.classMem (syn_copk A B) D) p0037 p0045
  have p0047 :=
    @g_n_3adant1 (.classMem B W) (.classMem C T)
      (syn_wb (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk A (.cv y)) D)))) (.classMem (syn_copk A B) D))
      (.classMem A V) p0046
  have p0048 :=
    @g_bitrd (syn_w3a (.classMem A V) (.classMem B W) (.classMem C T))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
              (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv y)) D)))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
            (.classMem (syn_copk A (.cv y)) D))))
      (.classMem (syn_copk A B) D) p0024 p0047
  have p0049 :=
    @g_syl5bb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins3k D))
      (syn_wex x (syn_wex y (syn_wex z
            (syn_w3a (.classEq (syn_csn (syn_csn A)) (syn_csn (syn_csn (.cv x))))
              (.classEq (syn_copk B C) (syn_copk (.cv y) (.cv z)))
              (.classMem (syn_copk (.cv x) (.cv y)) D)))))
      (syn_w3a (.classMem A V) (.classMem B W) (.classMem C T))
      (.classMem (syn_copk A B) D) p0003 p0048
  exact p0049

@[expose]
noncomputable def g_otkelins2k (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_otkelinsk_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_otkelinsk_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_otkelinsk_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins2k D))
        (.classMem (syn_copk A C) D)) :=
  by
  have p0000 := @g_otkelins2kg A B C D (syn_cvv) (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp3an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins2k D))
        (.classMem (syn_copk A C) D))
      hyp_otkelinsk_1 hyp_otkelinsk_2 hyp_otkelinsk_3 p0000
  exact p0001

@[expose]
noncomputable def g_otkelins3k (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_otkelinsk_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_otkelinsk_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_otkelinsk_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins3k D))
        (.classMem (syn_copk A B) D)) :=
  by
  have p0000 := @g_otkelins3kg A B C D (syn_cvv) (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp3an (.classMem A (syn_cvv)) (.classMem B (syn_cvv)) (.classMem C (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cins3k D))
        (.classMem (syn_copk A B) D))
      hyp_otkelinsk_1 hyp_otkelinsk_2 hyp_otkelinsk_3 p0000
  exact p0001

@[expose]
noncomputable def g_elimakg (y : Var) (A : Class) (B : Class) (C : Class) (V : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv) :
    Nominal.NPrf
      (.imp (.classMem C V) (syn_wb (.classMem C (syn_cimak A B))
          (syn_wrex y B (.classMem (syn_copk (.cv y) C) A)))) :=
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
  have p0000 := @g_opkeq2 (.cv x) C (.cv y)
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) C) (syn_copk (.cv y) (.cv x)) (syn_copk (.cv y) C) A p0000
  have freeVariableCertificate0 : y ∉ ((Wff.classEq (.cv x) C)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_x, dv_C_y, or_false, not_false_eq_true]
  have p0002 :=
    @g_rexbidv (.classEq (.cv x) C) (.classMem (syn_copk (.cv y) (.cv x)) A)
      (.classMem (syn_copk (.cv y) C) A) y B freeVariableCertificate0 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_imak x y A B
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact dv_B_y)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have freeVariableCertificate1 :
    x ∉ ((syn_wrex y B (.classMem (syn_copk (.cv y) C) A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, fresh_x_not_C, fresh_x_not_A,
      or_false, and_false, not_false_eq_true]
  have p0004 :=
    @g_elab2g (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A))
      (syn_wrex y B (.classMem (syn_copk (.cv y) C) A)) x C (syn_cimak A B) V
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C))) freeVariableCertificate1
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_elimakvg (y : Var) (A : Class) (C : Class) (V : Class)
    (dv_A_y : y ∉ A.fv) (dv_C_y : y ∉ C.fv) :
    Nominal.NPrf
      (.imp (.classMem C V) (syn_wb (.classMem C (syn_cimak A (syn_cvv)))
          (syn_wex y (.classMem (syn_copk (.cv y) C) A)))) :=
  by
  have p0000 :=
    @g_elimakg y A (syn_cvv) C V (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by
        exact
          (show y ∉ ((syn_cvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
  have p0001 := @g_rexv (.classMem (syn_copk (.cv y) C) A) y
  have p0002 :=
    @g_syl6bb (.classMem C V) (.classMem C (syn_cimak A (syn_cvv)))
      (syn_wrex y (syn_cvv) (.classMem (syn_copk (.cv y) C) A))
      (syn_wex y (.classMem (syn_copk (.cv y) C) A)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_elimak (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_y : y ∉ A.fv) (dv_B_y : y ∉ B.fv) (dv_C_y : y ∉ C.fv)
    (hyp_elimak_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem C (syn_cimak A B))
        (syn_wrex y B (.classMem (syn_copk (.cv y) C) A))) :=
  by
  have p0000 :=
    @g_elimakg y A B C (syn_cvv) (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
      (by exact (show y ∉ (B).fv from (by exact dv_B_y)))
      (by exact (show y ∉ (C).fv from (by exact dv_C_y)))
  have p0001 := Nominal.mp hyp_elimak_1 p0000
  exact p0001

@[expose]
noncomputable def g_elimakv (y : Var) (A : Class) (C : Class) (dv_A_y : y ∉ A.fv)
    (dv_C_y : y ∉ C.fv) (hyp_elimak_1 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem C (syn_cimak A (syn_cvv)))
        (syn_wex y (.classMem (syn_copk (.cv y) C) A))) :=
  by
  have p0000 :=
    @g_elimakvg y A C (syn_cvv) (by exact (show y ∉ (A).fv from (by exact dv_A_y)))
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

@[expose]
noncomputable def g_opkelcokg (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv)
    (dv_D_x : x ∉ D.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_ccomk C D)) (syn_wex x
            (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C))))) :=
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
  have p0000 := @g_elex A V
  have p0001 := @g_elex B W
  have p0002 := (Nominal.classEqRefl (syn_ccomk C D))
  have p0003 :=
    @g_eleq2i (syn_ccomk C D)
      (syn_cimak (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D))) (syn_cvv))
      (syn_copk A B) p0002
  have p0004 := @g_opkex A B
  have freeVariableCertificate0 :
    y ∉ ((syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, Finset.mem_union,
      fresh_y_not_C, fresh_y_not_D, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((syn_copk A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0005 :=
    @g_elimakv y (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D))) (syn_copk A B)
      freeVariableCertificate0 freeVariableCertificate1 p0004
  have p0006 := @g_vex y
  have freeVariableCertificate2 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have freeVariableCertificate3 : z ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_y, not_false_eq_true]
  have freeVariableCertificate4 : w ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_y, not_false_eq_true]
  have freeVariableCertificate5 : x ∉ ((syn_copk A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate6 : z ∉ ((syn_copk A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate7 : w ∉ ((syn_copk A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_w_not_A, fresh_w_not_B, or_false, not_false_eq_true]
  have p0007 :=
    @g_opkelins2kg x z w (.cv y) (syn_copk A B) C (syn_cvv) (syn_cvv)
      freeVariableCertificate2 freeVariableCertificate3 freeVariableCertificate4
      freeVariableCertificate5 freeVariableCertificate6 freeVariableCertificate7
      (by exact (show x ∉ (C).fv from (by exact dv_C_x)))
      (by exact (show z ∉ (C).fv from (by exact fresh_z_not_C)))
      (by exact (show w ∉ (C).fv from (by exact fresh_w_not_C)))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show z ≠ w from (by exact fresh_z_ne_w))
  have p0008 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (syn_copk A B) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins2k C)) (syn_wex x (syn_wex z
            (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
                (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                (.classMem (syn_copk (.cv x) (.cv w)) C))))))
      p0006 p0004 p0007
  have p0009 :=
    @g_n_3anass (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
      (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
      (.classMem (syn_copk (.cv x) (.cv w)) C)
  have p0010 :=
    @g_n_2exbii
      (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
        (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
        (.classMem (syn_copk (.cv x) (.cv w)) C))
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
        (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
          (.classMem (syn_copk (.cv x) (.cv w)) C)))
      z w p0009
  have freeVariableCertificate8 :
    z ∉ ((Wff.classEq (.cv y) (syn_csn (syn_csn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate9 :
    w ∉ ((Wff.classEq (.cv y) (syn_csn (syn_csn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_x, or_false, not_false_eq_true]
  have p0011 :=
    @g_n_19_42vv (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
      (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
        (.classMem (syn_copk (.cv x) (.cv w)) C))
      z w freeVariableCertificate8 freeVariableCertificate9
  have p0012 :=
    @g_bitri
      (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
            (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
            (.classMem (syn_copk (.cv x) (.cv w)) C))))
      (syn_wex z (syn_wex w (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
            (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
              (.classMem (syn_copk (.cv x) (.cv w)) C)))))
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w
            (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
              (.classMem (syn_copk (.cv x) (.cv w)) C)))))
      p0010 p0011
  have p0013 :=
    @g_exbii
      (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
            (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
            (.classMem (syn_copk (.cv x) (.cv w)) C))))
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w
            (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
              (.classMem (syn_copk (.cv x) (.cv w)) C)))))
      x p0012
  have p0014 :=
    @g_bitri (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins2k C))
      (syn_wex x (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
              (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
              (.classMem (syn_copk (.cv x) (.cv w)) C)))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w
              (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                (.classMem (syn_copk (.cv x) (.cv w)) C))))))
      p0008 p0013
  have p0015 :=
    @g_anbi1i (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins2k C))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w
              (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                (.classMem (syn_copk (.cv x) (.cv w)) C))))))
      (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))) p0014
  have p0016 :=
    @g_elin (syn_copk (.cv y) (syn_copk A B)) (syn_cins2k C) (syn_cins3k (syn_ccnvk D))
  have freeVariableCertificate10 :
    x ∉
      ((Wff.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_y, dv_A_x, dv_B_x, dv_D_x, or_false,
      not_false_eq_true]
  have p0017 :=
    @g_n_19_41v
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w
            (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
              (.classMem (syn_copk (.cv x) (.cv w)) C)))))
      (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))) x
      freeVariableCertificate10
  have p0018 :=
    @g_n_3bitr4i
      (syn_wa (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins2k C))
        (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))
      (syn_wa (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z
              (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                  (.classMem (syn_copk (.cv x) (.cv w)) C))))))
        (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))
      (.classMem (syn_copk (.cv y) (syn_copk A B))
        (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D))))
      (syn_wex x (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z
              (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                  (.classMem (syn_copk (.cv x) (.cv w)) C)))))
          (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))))
      p0015 p0016 p0017
  have p0019 :=
    @g_exbii
      (.classMem (syn_copk (.cv y) (syn_copk A B))
        (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D))))
      (syn_wex x (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z
              (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                  (.classMem (syn_copk (.cv x) (.cv w)) C)))))
          (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))))
      y p0018
  have p0020 :=
    @g_excom
      (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w
              (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                (.classMem (syn_copk (.cv x) (.cv w)) C)))))
        (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))
      y x
  have p0021 :=
    @g_anass (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
      (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
            (.classMem (syn_copk (.cv x) (.cv w)) C))))
      (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))
  have p0022 :=
    @g_exbii
      (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z (syn_wex w
              (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                (.classMem (syn_copk (.cv x) (.cv w)) C)))))
        (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wa (syn_wex z (syn_wex w
              (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                (.classMem (syn_copk (.cv x) (.cv w)) C))))
          (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))))
      y p0021
  have p0023 := @g_snex (syn_csn (.cv x))
  have p0024 := @g_opkeq1 (.cv y) (syn_csn (syn_csn (.cv x))) (syn_copk A B)
  have p0025 :=
    @g_eleq1d (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
      (syn_copk (.cv y) (syn_copk A B))
      (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))
      p0024
  have p0026 :=
    @g_anbi2d (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
      (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
        (syn_cins3k (syn_ccnvk D)))
      (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
            (.classMem (syn_copk (.cv x) (.cv w)) C))))
      p0025
  have freeVariableCertificate11 : y ∉ ((syn_csn (syn_csn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate12 :
    y ∉
      ((syn_wa (syn_wex z (syn_wex w
              (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                (.classMem (syn_copk (.cv x) (.cv w)) C))))
          (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
            (syn_cins3k (syn_ccnvk D))))).fv :=
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
    @g_ceqsexv
      (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
              (.classMem (syn_copk (.cv x) (.cv w)) C))))
        (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))
      (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
              (.classMem (syn_copk (.cv x) (.cv w)) C))))
        (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
          (syn_cins3k (syn_ccnvk D))))
      y (syn_csn (syn_csn (.cv x))) freeVariableCertificate11 freeVariableCertificate12
      p0023 p0026
  have p0028 :=
    @g_bitri
      (syn_wex y (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z
              (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                  (.classMem (syn_copk (.cv x) (.cv w)) C)))))
          (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))))
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wa (syn_wex z
              (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                  (.classMem (syn_copk (.cv x) (.cv w)) C))))
            (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))))
      (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
              (.classMem (syn_copk (.cv x) (.cv w)) C))))
        (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
          (syn_cins3k (syn_ccnvk D))))
      p0022 p0027
  have p0029 :=
    @g_exbii
      (syn_wex y (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x)))) (syn_wex z
              (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                  (.classMem (syn_copk (.cv x) (.cv w)) C)))))
          (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D)))))
      (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
              (.classMem (syn_copk (.cv x) (.cv w)) C))))
        (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
          (syn_cins3k (syn_ccnvk D))))
      x p0028
  have p0030 :=
    @g_n_3bitri
      (syn_wex y (.classMem (syn_copk (.cv y) (syn_copk A B))
          (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D)))))
      (syn_wex y (syn_wex x (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
              (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                    (.classMem (syn_copk (.cv x) (.cv w)) C)))))
            (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))))
      (syn_wex x (syn_wex y (syn_wa (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv x))))
              (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                    (.classMem (syn_copk (.cv x) (.cv w)) C)))))
            (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_cins3k (syn_ccnvk D))))))
      (syn_wex x (syn_wa (syn_wex z (syn_wex w
              (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                (.classMem (syn_copk (.cv x) (.cv w)) C))))
          (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
            (syn_cins3k (syn_ccnvk D)))))
      p0019 p0020 p0029
  have p0031 :=
    @g_n_3bitri (.classMem (syn_copk A B) (syn_ccomk C D))
      (.classMem (syn_copk A B)
        (syn_cimak (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D))) (syn_cvv)))
      (syn_wex y (.classMem (syn_copk (.cv y) (syn_copk A B))
          (syn_cin (syn_cins2k C) (syn_cins3k (syn_ccnvk D)))))
      (syn_wex x (syn_wa (syn_wex z (syn_wex w
              (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                (.classMem (syn_copk (.cv x) (.cv w)) C))))
          (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
            (syn_cins3k (syn_ccnvk D)))))
      p0003 p0005 p0030
  have p0032 :=
    @g_ancom
      (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
            (.classMem (syn_copk (.cv x) (.cv w)) C))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
        (syn_cins3k (syn_ccnvk D)))
  have p0033 := @g_vex x
  have p0034 := @g_otkelins3kg (.cv x) A B (syn_ccnvk D) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0035 :=
    @g_mp3an1 (.classMem (.cv x) (syn_cvv)) (.classMem A (syn_cvv))
      (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
          (syn_cins3k (syn_ccnvk D))) (.classMem (syn_copk (.cv x) A) (syn_ccnvk D)))
      p0033 p0034
  have p0036 := @g_opkelcnvkg (.cv x) A D (syn_cvv) (syn_cvv)
  have p0037 :=
    @g_mpan (.classMem (.cv x) (syn_cvv)) (.classMem A (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv x) A) (syn_ccnvk D)) (.classMem (syn_copk A (.cv x)) D))
      p0033 p0036
  have p0038 :=
    @g_adantr (.classMem A (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv x) A) (syn_ccnvk D)) (.classMem (syn_copk A (.cv x)) D))
      (.classMem B (syn_cvv)) p0037
  have p0039 :=
    @g_bitrd (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
        (syn_cins3k (syn_ccnvk D)))
      (.classMem (syn_copk (.cv x) A) (syn_ccnvk D)) (.classMem (syn_copk A (.cv x)) D)
      p0035 p0038
  have p0040 := @g_eqcom (syn_copk A B) (syn_copk (.cv z) (.cv w))
  have p0041 :=
    @g_anbi1i (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
      (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B))
      (.classMem (syn_copk (.cv x) (.cv w)) C) p0040
  have p0042 :=
    @g_n_2exbii
      (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
        (.classMem (syn_copk (.cv x) (.cv w)) C))
      (syn_wa (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B))
        (.classMem (syn_copk (.cv x) (.cv w)) C))
      z w p0041
  have p0043 := @g_vex z
  have p0044 := @g_vex w
  have p0045 := @g_opkthg (.cv z) (.cv w) A B (syn_cvv) (syn_cvv) (syn_cvv)
  have p0046 :=
    @g_mp3an12 (.classMem (.cv z) (syn_cvv)) (.classMem (.cv w) (syn_cvv))
      (.classMem B (syn_cvv))
      (syn_wb (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B))
        (syn_wa (.classEq (.cv z) A) (.classEq (.cv w) B)))
      p0043 p0044 p0045
  have p0047 :=
    @g_anbi1d (.classMem B (syn_cvv)) (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B))
      (syn_wa (.classEq (.cv z) A) (.classEq (.cv w) B))
      (.classMem (syn_copk (.cv x) (.cv w)) C) p0046
  have p0048 :=
    @g_anass (.classEq (.cv z) A) (.classEq (.cv w) B)
      (.classMem (syn_copk (.cv x) (.cv w)) C)
  have p0049 :=
    @g_syl6bb (.classMem B (syn_cvv))
      (syn_wa (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B))
        (.classMem (syn_copk (.cv x) (.cv w)) C))
      (syn_wa (syn_wa (.classEq (.cv z) A) (.classEq (.cv w) B))
        (.classMem (syn_copk (.cv x) (.cv w)) C))
      (syn_wa (.classEq (.cv z) A)
        (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)))
      p0047 p0048
  have freeVariableCertificate13 : z ∉ ((Wff.classMem B (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_z_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate14 : w ∉ ((Wff.classMem B (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_w_not_B, or_false, not_false_eq_true]
  have p0050 :=
    @g_n_2exbidv (.classMem B (syn_cvv))
      (syn_wa (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B))
        (.classMem (syn_copk (.cv x) (.cv w)) C))
      (syn_wa (.classEq (.cv z) A)
        (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)))
      z w freeVariableCertificate13 freeVariableCertificate14 p0049
  have p0051 :=
    @g_adantl (.classMem B (syn_cvv))
      (syn_wb (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B))
              (.classMem (syn_copk (.cv x) (.cv w)) C)))) (syn_wex z (syn_wex w
            (syn_wa (.classEq (.cv z) A)
              (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))))))
      (.classMem A (syn_cvv)) p0050
  have freeVariableCertificate15 : w ∉ ((Wff.classEq (.cv z) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_z, fresh_w_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate16 :
    z ∉ ((syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, fresh_z_ne_w, fresh_z_not_B, fresh_z_ne_x, fresh_z_not_C,
      or_false, not_false_eq_true]
  have p0052 :=
    @g_eeanv (.classEq (.cv z) A)
      (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)) z w
      freeVariableCertificate15 freeVariableCertificate16
  have p0053 :=
    @g_syl6bb (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B))
            (.classMem (syn_copk (.cv x) (.cv w)) C))))
      (syn_wex z (syn_wex w (syn_wa (.classEq (.cv z) A)
            (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)))))
      (syn_wa (syn_wex z (.classEq (.cv z) A)) (syn_wex w
          (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))))
      p0051 p0052
  have p0054 :=
    @g_syl5bb
      (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
            (.classMem (syn_copk (.cv x) (.cv w)) C))))
      (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk (.cv z) (.cv w)) (syn_copk A B))
            (.classMem (syn_copk (.cv x) (.cv w)) C))))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wa (syn_wex z (.classEq (.cv z) A)) (syn_wex w
          (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))))
      p0042 p0053
  have p0055 :=
    @g_elisset z A (syn_cvv) (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
  have p0056 :=
    @g_biantrurd (.classMem A (syn_cvv)) (syn_wex z (.classEq (.cv z) A))
      (syn_wex w (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)))
      p0055
  have p0057 :=
    @g_bicomd (.classMem A (syn_cvv))
      (syn_wex w (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)))
      (syn_wa (syn_wex z (.classEq (.cv z) A)) (syn_wex w
          (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))))
      p0056
  have p0058 := @g_opkeq2 (.cv w) B (.cv x)
  have p0059 :=
    @g_eleq1d (.classEq (.cv w) B) (syn_copk (.cv x) (.cv w)) (syn_copk (.cv x) B) C p0058
  have freeVariableCertificate17 : w ∉ ((Wff.classMem (syn_copk (.cv x) B) C)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_x, fresh_w_not_B, fresh_w_not_C, or_false, not_false_eq_true]
  have p0060 :=
    @g_ceqsexgv (.classMem (syn_copk (.cv x) (.cv w)) C)
      (.classMem (syn_copk (.cv x) B) C) w B (syn_cvv)
      (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) freeVariableCertificate17
      p0059
  have p0061 :=
    @g_sylan9bb (.classMem A (syn_cvv))
      (syn_wa (syn_wex z (.classEq (.cv z) A)) (syn_wex w
          (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))))
      (syn_wex w (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C)))
      (.classMem B (syn_cvv)) (.classMem (syn_copk (.cv x) B) C) p0057 p0060
  have p0062 :=
    @g_bitrd (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
            (.classMem (syn_copk (.cv x) (.cv w)) C))))
      (syn_wa (syn_wex z (.classEq (.cv z) A)) (syn_wex w
          (syn_wa (.classEq (.cv w) B) (.classMem (syn_copk (.cv x) (.cv w)) C))))
      (.classMem (syn_copk (.cv x) B) C) p0054 p0061
  have p0063 :=
    @g_anbi12d (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
        (syn_cins3k (syn_ccnvk D)))
      (.classMem (syn_copk A (.cv x)) D)
      (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
            (.classMem (syn_copk (.cv x) (.cv w)) C))))
      (.classMem (syn_copk (.cv x) B) C) p0039 p0062
  have p0064 :=
    @g_syl5bb
      (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
              (.classMem (syn_copk (.cv x) (.cv w)) C))))
        (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
          (syn_cins3k (syn_ccnvk D))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
          (syn_cins3k (syn_ccnvk D))) (syn_wex z (syn_wex w
            (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
              (.classMem (syn_copk (.cv x) (.cv w)) C)))))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C)) p0032
      p0063
  have freeVariableCertificate18 :
    x ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have p0065 :=
    @g_exbidv (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wa (syn_wex z (syn_wex w (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
              (.classMem (syn_copk (.cv x) (.cv w)) C))))
        (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
          (syn_cins3k (syn_ccnvk D))))
      (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C)) x
      freeVariableCertificate18 p0064
  have p0066 :=
    @g_syl5bb (.classMem (syn_copk A B) (syn_ccomk C D))
      (syn_wex x (syn_wa (syn_wex z (syn_wex w
              (syn_wa (.classEq (syn_copk A B) (syn_copk (.cv z) (.cv w)))
                (.classMem (syn_copk (.cv x) (.cv w)) C))))
          (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk A B))
            (syn_cins3k (syn_ccnvk D)))))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wex x (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C)))
      p0031 p0065
  have p0067 :=
    @g_syl2an (.classMem A V) (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_copk A B) (syn_ccomk C D)) (syn_wex x
          (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C))))
      (.classMem B W) p0000 p0001 p0066
  exact p0067

@[expose]
noncomputable def g_opkelcok (x : Var) (A : Class) (B : Class) (C : Class) (D : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_D_x : x ∉ D.fv)
    (hyp_opkelcok_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opkelcok_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk A B) (syn_ccomk C D)) (syn_wex x
          (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C)))) :=
  by
  have p0000 :=
    @g_opkelcokg x A B C D (syn_cvv) (syn_cvv)
      (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
      (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
      (by exact (show x ∉ (C).fv from (by exact dv_C_x)))
      (by exact (show x ∉ (D).fv from (by exact dv_D_x)))
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_copk A B) (syn_ccomk C D)) (syn_wex x
          (syn_wa (.classMem (syn_copk A (.cv x)) D) (.classMem (syn_copk (.cv x) B) C))))
      hyp_opkelcok_1 hyp_opkelcok_2 p0000
  exact p0001

@[expose]
noncomputable def g_elp6 (x : Var) (A : Class) (B : Class) (V : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem A V) (syn_wb (.classMem A (syn_cp6 B))
          (.all x (.classMem (syn_copk (.cv x) (syn_csn A)) B)))) :=
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
  have p0000 := @g_sneq (.cv y) A
  have p0001 := @g_sneqd (.classEq (.cv y) A) (syn_csn (.cv y)) (syn_csn A) p0000
  have p0002 :=
    @g_xpkeq2d (.classEq (.cv y) A) (syn_csn (syn_csn (.cv y))) (syn_csn (syn_csn A))
      (syn_cvv) p0001
  have p0003 :=
    @g_sseq1d (.classEq (.cv y) A) (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv y))))
      (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))) B p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_p6 y B
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have freeVariableCertificate0 :
    y ∉ ((syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))) B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0005 :=
    @g_elab2g (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn (.cv y)))) B)
      (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))) B) y A (syn_cp6 B) V
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate0
      p0003 p0004
  have p0006 := @g_xpkssvvk (syn_cvv) (syn_csn (syn_csn A))
  have freeVariableCertificate1 : x ∉ ((syn_cxpk (syn_cvv) (syn_csn (syn_csn A)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate2 : y ∉ ((syn_cxpk (syn_cvv) (syn_csn (syn_csn A)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_A, or_false, not_false_eq_true]
  have p0007 :=
    @g_ssrelk x y (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))) B freeVariableCertificate1
      freeVariableCertificate2 (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0008 := Nominal.mp p0006 p0007
  have p0009 := @g_vex x
  have p0010 := @g_vex y
  have p0011 := @g_opkelxpk (.cv x) (.cv y) (syn_cvv) (syn_csn (syn_csn A)) p0009 p0010
  have p0012 :=
    @g_biantrur (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_csn (syn_csn A)))
      p0009
  have p0013 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn y (syn_csn A)
      (by
        exact
          (show y ∉ ((syn_csn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
  have p0014 := @g_eqabri (.classEq (.cv y) (syn_csn A)) y (syn_csn (syn_csn A)) p0013
  have p0015 :=
    @g_n_3bitr2i
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))))
      (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_csn (syn_csn A))))
      (.classMem (.cv y) (syn_csn (syn_csn A))) (.classEq (.cv y) (syn_csn A)) p0011 p0012
      p0014
  have p0016 :=
    @g_imbi1i
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))))
      (.classEq (.cv y) (syn_csn A)) (.classMem (syn_copk (.cv x) (.cv y)) B) p0015
  have p0017 :=
    @g_albii
      (.imp (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))))
        (.classMem (syn_copk (.cv x) (.cv y)) B))
      (.imp (.classEq (.cv y) (syn_csn A)) (.classMem (syn_copk (.cv x) (.cv y)) B)) y
      p0016
  have p0018 := @g_snex A
  have p0019 := @g_opkeq2 (.cv y) (syn_csn A) (.cv x)
  have p0020 :=
    @g_eleq1d (.classEq (.cv y) (syn_csn A)) (syn_copk (.cv x) (.cv y))
      (syn_copk (.cv x) (syn_csn A)) B p0019
  have freeVariableCertificate3 :
    y ∉ ((Wff.classMem (syn_copk (.cv x) (syn_csn A)) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, fresh_y_not_B, or_false,
      not_false_eq_true]
  have p0021 :=
    @g_ceqsalv (.classMem (syn_copk (.cv x) (.cv y)) B)
      (.classMem (syn_copk (.cv x) (syn_csn A)) B) y (syn_csn A)
      (by
        exact
          (show y ∉ ((syn_csn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
      freeVariableCertificate3 p0018 p0020
  have p0022 :=
    @g_bitri
      (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y))
            (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))))
          (.classMem (syn_copk (.cv x) (.cv y)) B)))
      (.all y (.imp (.classEq (.cv y) (syn_csn A)) (.classMem (syn_copk (.cv x) (.cv y)) B)))
      (.classMem (syn_copk (.cv x) (syn_csn A)) B) p0017 p0021
  have p0023 :=
    @g_albii
      (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y))
            (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))))
          (.classMem (syn_copk (.cv x) (.cv y)) B)))
      (.classMem (syn_copk (.cv x) (syn_csn A)) B) x p0022
  have p0024 :=
    @g_bitri (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))) B)
      (.all x (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y))
              (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))))
            (.classMem (syn_copk (.cv x) (.cv y)) B))))
      (.all x (.classMem (syn_copk (.cv x) (syn_csn A)) B)) p0008 p0023
  have p0025 :=
    @g_syl6bb (.classMem A V) (.classMem A (syn_cp6 B))
      (syn_wss (syn_cxpk (syn_cvv) (syn_csn (syn_csn A))) B)
      (.all x (.classMem (syn_copk (.cv x) (syn_csn A)) B)) p0005 p0024
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

@[expose]
noncomputable def g_opkelsikg (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (V : Class) (W : Class) (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_csik C)) (syn_wex x (syn_wex y
              (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y)))
                (.classMem (syn_copk (.cv x) (.cv y)) C)))))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sik z t u y x C
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
  have p0001 := @g_eqeq1 (.cv t) A (syn_csn (.cv x))
  have p0002 :=
    @g_n_3anbi1d (.classEq (.cv t) A) (.classEq (.cv t) (syn_csn (.cv x)))
      (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
      (.classMem (syn_copk (.cv x) (.cv y)) C) p0001
  have freeVariableCertificate0 : x ∉ ((Wff.classEq (.cv t) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_t, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((Wff.classEq (.cv t) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_t, dv_A_y, or_false, not_false_eq_true]
  have p0003 :=
    @g_n_2exbidv (.classEq (.cv t) A)
      (syn_w3a (.classEq (.cv t) (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (.classMem (syn_copk (.cv x) (.cv y)) C))
      (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (.classMem (syn_copk (.cv x) (.cv y)) C))
      x y freeVariableCertificate0 freeVariableCertificate1 p0002
  have p0004 := @g_eqeq1 (.cv u) B (syn_csn (.cv y))
  have p0005 :=
    @g_n_3anbi2d (.classEq (.cv u) B) (.classEq (.cv u) (syn_csn (.cv y)))
      (.classEq B (syn_csn (.cv y))) (.classEq A (syn_csn (.cv x)))
      (.classMem (syn_copk (.cv x) (.cv y)) C) p0004
  have freeVariableCertificate2 : x ∉ ((Wff.classEq (.cv u) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_u, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((Wff.classEq (.cv u) B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_u, dv_B_y, or_false, not_false_eq_true]
  have p0006 :=
    @g_n_2exbidv (.classEq (.cv u) B)
      (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
        (.classMem (syn_copk (.cv x) (.cv y)) C))
      (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y)))
        (.classMem (syn_copk (.cv x) (.cv y)) C))
      x y freeVariableCertificate2 freeVariableCertificate3 p0005
  have freeVariableCertificate4 :
    u ∉
      ((syn_wex x (syn_wex y
            (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y)))
              (.classMem (syn_copk (.cv x) (.cv y)) C))))).fv :=
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
      ((syn_wex x (syn_wex y (syn_w3a (.classEq (.cv t) (syn_csn (.cv x)))
              (.classEq (.cv u) (syn_csn (.cv y)))
              (.classMem (syn_copk (.cv x) (.cv y)) C))))).fv :=
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
      ((syn_wex x (syn_wex y
            (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
              (.classMem (syn_copk (.cv x) (.cv y)) C))))).fv :=
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
    @g_opkelopkabg
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv t) (syn_csn (.cv x)))
            (.classEq (.cv u) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))))
      (syn_wex x (syn_wex y
          (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq (.cv u) (syn_csn (.cv y)))
            (.classMem (syn_copk (.cv x) (.cv y)) C))))
      (syn_wex x (syn_wex y
          (syn_w3a (.classEq A (syn_csn (.cv x))) (.classEq B (syn_csn (.cv y)))
            (.classMem (syn_copk (.cv x) (.cv y)) C))))
      z t u (syn_csik C) A B V W
      (by
        exact
          (show t ∉ ((syn_csik C)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
              exact (show t ∉ (C).fv from (by exact fresh_t_not_C)))))
      (by
        exact
          (show u ∉ ((syn_csik C)).fv from
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

@[expose]
noncomputable def g_opksnelsik (A : Class) (B : Class) (C : Class)
    (hyp_opksnelsik_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opksnelsik_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn A) (syn_csn B)) (syn_csik C))
        (.classMem (syn_copk A B) C)) :=
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
  have p0000 := @g_snex A
  have p0001 := @g_snex B
  have p0002 :=
    @g_opkelsikg x y (syn_csn A) (syn_csn B) C (syn_cvv) (syn_cvv)
      (by
        exact
          (show x ∉ ((syn_csn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      (by
        exact
          (show y ∉ ((syn_csn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
      (by
        exact
          (show x ∉ ((syn_csn B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))))
      (by
        exact
          (show y ∉ ((syn_csn B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))))
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C)))
      (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0003 :=
    @g_mp2an (.classMem (syn_csn A) (syn_cvv)) (.classMem (syn_csn B) (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn A) (syn_csn B)) (syn_csik C)) (syn_wex x (syn_wex y
            (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv x)))
              (.classEq (syn_csn B) (syn_csn (.cv y)))
              (.classMem (syn_copk (.cv x) (.cv y)) C)))))
      p0000 p0001 p0002
  have p0004 := @g_eqcom (syn_csn A) (syn_csn (.cv x))
  have p0005 := @g_vex x
  have p0006 := @g_sneqb (.cv x) A p0005
  have p0007 :=
    @g_bitri (.classEq (syn_csn A) (syn_csn (.cv x)))
      (.classEq (syn_csn (.cv x)) (syn_csn A)) (.classEq (.cv x) A) p0004 p0006
  have p0008 := @g_eqcom (syn_csn B) (syn_csn (.cv y))
  have p0009 := @g_vex y
  have p0010 := @g_sneqb (.cv y) B p0009
  have p0011 :=
    @g_bitri (.classEq (syn_csn B) (syn_csn (.cv y)))
      (.classEq (syn_csn (.cv y)) (syn_csn B)) (.classEq (.cv y) B) p0008 p0010
  have p0012 := @g_biid (.classMem (syn_copk (.cv x) (.cv y)) C)
  have p0013 :=
    @g_n_3anbi123i (.classEq (syn_csn A) (syn_csn (.cv x))) (.classEq (.cv x) A)
      (.classEq (syn_csn B) (syn_csn (.cv y))) (.classEq (.cv y) B)
      (.classMem (syn_copk (.cv x) (.cv y)) C) (.classMem (syn_copk (.cv x) (.cv y)) C)
      p0007 p0011 p0012
  have p0014 :=
    @g_n_2exbii
      (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv x)))
        (.classEq (syn_csn B) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))
      (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B)
        (.classMem (syn_copk (.cv x) (.cv y)) C))
      x y p0013
  have p0015 := @g_opkeq1 (.cv x) A (.cv y)
  have p0016 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_copk (.cv x) (.cv y)) (syn_copk A (.cv y)) C p0015
  have p0017 := @g_opkeq2 (.cv y) B A
  have p0018 := @g_eleq1d (.classEq (.cv y) B) (syn_copk A (.cv y)) (syn_copk A B) C p0017
  have freeVariableCertificate0 : y ∉ ((Wff.classMem (syn_copk A B) C)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((Wff.classMem (syn_copk A (.cv y)) C)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_not_A, fresh_x_ne_y, fresh_x_not_C, or_false, not_false_eq_true]
  have p0019 :=
    @g_ceqsex2v (.classMem (syn_copk (.cv x) (.cv y)) C)
      (.classMem (syn_copk A (.cv y)) C) (.classMem (syn_copk A B) C) x y A B
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) freeVariableCertificate0
      freeVariableCertificate1 (show x ≠ y from (by exact fresh_x_ne_y)) hyp_opksnelsik_1
      hyp_opksnelsik_2 p0016 p0018
  have p0020 :=
    @g_bitri
      (syn_wex x (syn_wex y (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv x)))
            (.classEq (syn_csn B) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))))
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv x) A) (.classEq (.cv y) B)
            (.classMem (syn_copk (.cv x) (.cv y)) C))))
      (.classMem (syn_copk A B) C) p0014 p0019
  have p0021 :=
    @g_bitri (.classMem (syn_copk (syn_csn A) (syn_csn B)) (syn_csik C))
      (syn_wex x (syn_wex y (syn_w3a (.classEq (syn_csn A) (syn_csn (.cv x)))
            (.classEq (syn_csn B) (syn_csn (.cv y))) (.classMem (syn_copk (.cv x) (.cv y)) C))))
      (.classMem (syn_copk A B) C) p0003 p0020
  exact p0021

@[expose]
noncomputable def g_sikssvvk (A : Class) :
    Nominal.NPrf (syn_wss (syn_csik A) (syn_cxpk (syn_cvv) (syn_cvv))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sik x y z u t A
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
    @g_opkabssvvki
      (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (.cv t)))
            (.classEq (.cv z) (syn_csn (.cv u))) (.classMem (syn_copk (.cv t) (.cv u)) A))))
      x y z (syn_csik A) (show x ≠ y from (by exact fresh_x_ne_y))
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

@[expose]
noncomputable def g_sikss1c1c (A : Class) :
    Nominal.NPrf (syn_wss (syn_csik A) (syn_cxpk (syn_c1c) (syn_c1c))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sik t z w b a A
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
  have p0001 := @g_eqeq1 (.cv z) (.cv x) (syn_csn (.cv a))
  have p0002_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z x) (syn_wb (.classEq (.cv z) (syn_csn (.cv a)))
          (.classEq (.cv x) (syn_csn (.cv a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0001
  have p0002 :=
    @g_n_3anbi1d (.objEq z x) (.classEq (.cv z) (syn_csn (.cv a)))
      (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b)))
      (.classMem (syn_copk (.cv a) (.cv b)) A) p0002_e00_recanon
  have freeVariableCertificate0 : a ∉ ((Wff.objEq z x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 : b ∉ ((Wff.objEq z x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_x, or_false, not_false_eq_true]
  have p0003 :=
    @g_n_2exbidv (.objEq z x)
      (syn_w3a (.classEq (.cv z) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b)))
        (.classMem (syn_copk (.cv a) (.cv b)) A))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b)))
        (.classMem (syn_copk (.cv a) (.cv b)) A))
      a b freeVariableCertificate0 freeVariableCertificate1 p0002
  have p0004 := @g_eqeq1 (.cv w) (.cv y) (syn_csn (.cv b))
  have p0005_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w y) (syn_wb (.classEq (.cv w) (syn_csn (.cv b)))
          (.classEq (.cv y) (syn_csn (.cv b))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @g_n_3anbi2d (.objEq w y) (.classEq (.cv w) (syn_csn (.cv b)))
      (.classEq (.cv y) (syn_csn (.cv b))) (.classEq (.cv x) (syn_csn (.cv a)))
      (.classMem (syn_copk (.cv a) (.cv b)) A) p0005_e00_recanon
  have freeVariableCertificate2 : a ∉ ((Wff.objEq w y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_a_ne_w, fresh_a_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate3 : b ∉ ((Wff.objEq w y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
      Finset.mem_singleton, fresh_b_ne_w, fresh_b_ne_y, or_false, not_false_eq_true]
  have p0006 :=
    @g_n_2exbidv (.objEq w y)
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b)))
        (.classMem (syn_copk (.cv a) (.cv b)) A))
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
        (.classMem (syn_copk (.cv a) (.cv b)) A))
      a b freeVariableCertificate2 freeVariableCertificate3 p0005
  have p0007 := @g_vex x
  have p0008 := @g_vex y
  have p0009_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv x)) (syn_wb (syn_wex a (syn_wex b
              (syn_w3a (.classEq (.cv z) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b)))
                (.classMem (syn_copk (.cv a) (.cv b)) A)))) (syn_wex a (syn_wex b
              (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b)))
                (.classMem (syn_copk (.cv a) (.cv b)) A)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0009_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv y)) (syn_wb (syn_wex a (syn_wex b
              (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv w) (syn_csn (.cv b)))
                (.classMem (syn_copk (.cv a) (.cv b)) A)))) (syn_wex a (syn_wex b
              (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
                (.classMem (syn_copk (.cv a) (.cv b)) A)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex
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
      ((syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
              (.classEq (.cv y) (syn_csn (.cv b)))
              (.classMem (syn_copk (.cv a) (.cv b)) A))))).fv :=
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
      ((syn_wex a (syn_wex b (syn_w3a (.classEq (.cv z) (syn_csn (.cv a)))
              (.classEq (.cv w) (syn_csn (.cv b)))
              (.classMem (syn_copk (.cv a) (.cv b)) A))))).fv :=
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
      ((syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
              (.classEq (.cv w) (syn_csn (.cv b)))
              (.classMem (syn_copk (.cv a) (.cv b)) A))))).fv :=
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
    @g_opkelopkab
      (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv z) (syn_csn (.cv a)))
            (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))))
      (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
            (.classEq (.cv w) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))))
      (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
            (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))))
      t z w (syn_csik A) (.cv x) (.cv y)
      (by
        exact
          (show z ∉ ((syn_csik A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
              exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))))
      (by
        exact
          (show w ∉ ((syn_csik A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
              exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))))
      freeVariableCertificate4 freeVariableCertificate5 freeVariableCertificate6
      freeVariableCertificate7 freeVariableCertificate8 freeVariableCertificate9
      freeVariableCertificate10 freeVariableCertificate11 freeVariableCertificate12
      (show t ≠ z from (by exact fresh_t_ne_z)) (show t ≠ w from (by exact fresh_t_ne_w))
      (show z ≠ w from (by exact fresh_z_ne_w)) p0000 p0009_e01_recanon p0009_e02_recanon
      p0007 p0008
  have p0010 := @g_opkeq12 (.cv x) (.cv y) (syn_csn (.cv a)) (syn_csn (.cv b))
  have p0011 := @g_vex a
  have p0012 := @g_snel1c (.cv a) p0011
  have p0013 := @g_vex b
  have p0014 := @g_snel1c (.cv b) p0013
  have p0015 :=
    @g_opkelxpkg (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_c1c) (syn_c1c) (syn_c1c)
      (syn_c1c)
  have p0016 :=
    @g_mp2an (.classMem (syn_csn (.cv a)) (syn_c1c))
      (.classMem (syn_csn (.cv b)) (syn_c1c))
      (syn_wb (.classMem (syn_copk (syn_csn (.cv a)) (syn_csn (.cv b)))
          (syn_cxpk (syn_c1c) (syn_c1c))) (syn_wa (.classMem (syn_csn (.cv a)) (syn_c1c))
          (.classMem (syn_csn (.cv b)) (syn_c1c))))
      p0012 p0014 p0015
  have p0017 :=
    @g_mpbir2an
      (.classMem (syn_copk (syn_csn (.cv a)) (syn_csn (.cv b))) (syn_cxpk (syn_c1c) (syn_c1c)))
      (.classMem (syn_csn (.cv a)) (syn_c1c)) (.classMem (syn_csn (.cv b)) (syn_c1c))
      p0012 p0014 p0016
  have p0018 :=
    @g_syl6eqel
      (syn_wa (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b))))
      (syn_copk (.cv x) (.cv y)) (syn_copk (syn_csn (.cv a)) (syn_csn (.cv b)))
      (syn_cxpk (syn_c1c) (syn_c1c)) p0010 p0017
  have p0019 :=
    @g_n_3adant3 (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c)))
      (.classMem (syn_copk (.cv a) (.cv b)) A) p0018
  have freeVariableCertificate13 :
    a ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_a_ne_x, fresh_a_ne_y, or_false,
      not_false_eq_true]
  have freeVariableCertificate14 :
    b ∉ ((Wff.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_b_ne_x, fresh_b_ne_y, or_false,
      not_false_eq_true]
  have p0020 :=
    @g_exlimivv
      (syn_w3a (.classEq (.cv x) (syn_csn (.cv a))) (.classEq (.cv y) (syn_csn (.cv b)))
        (.classMem (syn_copk (.cv a) (.cv b)) A))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c))) a b
      freeVariableCertificate13 freeVariableCertificate14 p0019
  have p0021 :=
    @g_sylbi (.classMem (syn_copk (.cv x) (.cv y)) (syn_csik A))
      (syn_wex a (syn_wex b (syn_w3a (.classEq (.cv x) (syn_csn (.cv a)))
            (.classEq (.cv y) (syn_csn (.cv b))) (.classMem (syn_copk (.cv a) (.cv b)) A))))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c))) p0009 p0020
  have p0022 :=
    @g_gen2
      (.imp (.classMem (syn_copk (.cv x) (.cv y)) (syn_csik A))
        (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c))))
      x y p0021
  have p0023 := @g_sikssvvk A
  have freeVariableCertificate15 : x ∉ ((syn_cxpk (syn_c1c) (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate16 : y ∉ ((syn_cxpk (syn_c1c) (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0024 :=
    @g_ssrelk x y (syn_csik A) (syn_cxpk (syn_c1c) (syn_c1c))
      (by
        exact
          (show x ∉ ((syn_csik A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      (by
        exact
          (show y ∉ ((syn_csik A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
      freeVariableCertificate15 freeVariableCertificate16
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0025 := Nominal.mp p0023 p0024
  have p0026 :=
    @g_mpbir (syn_wss (syn_csik A) (syn_cxpk (syn_c1c) (syn_c1c)))
      (.all x (.all y (.imp (.classMem (syn_copk (.cv x) (.cv y)) (syn_csik A))
            (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_c1c) (syn_c1c))))))
      p0022 p0025
  exact p0026

@[expose]
noncomputable def g_opkelssetkg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_cssetk)) (syn_wss A B))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ssetk x y z
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 := @g_sseq1 (.cv y) A (.cv z)
  have p0002 := @g_sseq2 (.cv z) B A
  have freeVariableCertificate0 : z ∉ ((syn_wss A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((syn_wss (.cv y) (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_y, fresh_x_ne_z, or_false, not_false_eq_true]
  have freeVariableCertificate2 : y ∉ ((syn_wss A (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_not_A, fresh_y_ne_z, or_false, not_false_eq_true]
  have p0003 :=
    @g_opkelopkabg (syn_wss (.cv y) (.cv z)) (syn_wss A (.cv z)) (syn_wss A B) x y z
      (syn_cssetk) A B V W
      (by
        exact
          (show y ∉ ((syn_cssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show z ∉ ((syn_cssetk)).fv from
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

@[expose]
noncomputable def g_elssetkg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_cssetk)) (.classMem A B))) :=
  by
  have p0000 := @g_snex A
  have p0001 := @g_opkelssetkg (syn_csn A) B (syn_cvv) W
  have p0002 :=
    @g_mpan (.classMem (syn_csn A) (syn_cvv)) (.classMem B W)
      (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_cssetk)) (syn_wss (syn_csn A) B))
      p0000 p0001
  have p0003 := @g_snssg A B V
  have p0004 := @g_bicomd (.classMem A V) (.classMem A B) (syn_wss (syn_csn A) B) p0003
  have p0005 :=
    @g_sylan9bbr (.classMem B W) (.classMem (syn_copk (syn_csn A) B) (syn_cssetk))
      (syn_wss (syn_csn A) B) (.classMem A V) (.classMem A B) p0002 p0004
  exact p0005

@[expose]
noncomputable def g_elssetk (A : Class) (B : Class)
    (hyp_elssetk_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_elssetk_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_cssetk)) (.classMem A B)) :=
  by
  have p0000 := @g_elssetkg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_cssetk)) (.classMem A B))
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

@[expose]
noncomputable def g_opkelimagekg (A : Class) (B : Class) (C : Class) (V : Class)
    (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_cimagek C)) (.classEq B (syn_cimak C A)))) :=
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
  have p0000 := @g_elex A V
  have p0001 := @g_elex B W
  have p0002 := @g_opkelxpkg A B (syn_cvv) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0003 :=
    @g_ibir (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_copk A B) (syn_cxpk (syn_cvv) (syn_cvv))) p0002
  have p0004 :=
    @g_biantrurd (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_copk A B) (syn_cxpk (syn_cvv) (syn_cvv)))
      (.neg (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0003
  have p0005 :=
    @g_exnal (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A))) x
  have p0006 := @g_opkex A B
  have freeVariableCertificate0 :
    y ∉
      ((syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_C, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate2 : y ∉ ((syn_copk A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0007 :=
    @g_elimak y
      (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk A B) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 p0006
  have p0008 :=
    (Nominal.biimpRefl (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))))
  have freeVariableCertificate3 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0009 := @g_elpw121c x (.cv y) freeVariableCertificate3
  have p0010 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))))
      (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))
      p0009
  have freeVariableCertificate4 :
    x ∉
      ((Wff.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))).fv :=
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
    @g_n_19_41v (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))
      x freeVariableCertificate4
  have p0012 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))
      (syn_wa (syn_wex x (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x))))))
        (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))))
      p0010 p0011
  have p0013 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))
      (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))))
      y p0012
  have p0014 :=
    @g_excom
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
        (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))
      y x
  have p0015 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0016 := @g_opkeq1 (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)
  have p0017 :=
    @g_eleq1d (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (.cv y) (syn_copk A B))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
      (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
      p0016
  have freeVariableCertificate5 : y ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have freeVariableCertificate6 :
    y ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
          (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))).fv :=
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
    @g_ceqsexv
      (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))
      y (syn_csn (syn_csn (syn_csn (.cv x)))) freeVariableCertificate5
      freeVariableCertificate6 p0015 p0017
  have p0019 :=
    @g_exbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))
      x p0018
  have p0020 :=
    @g_n_3bitri
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))))
      (syn_wex y (syn_wex x (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))))
      (syn_wex x (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
          (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))
      p0013 p0014 p0019
  have p0021 :=
    @g_n_3bitri
      (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex y (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv y) (syn_copk A B))
          (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv y) (syn_copk A B)) (syn_csymdif (syn_cins2k (syn_cssetk))
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))))
      (syn_wex x (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
          (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))
      p0007 p0008 p0020
  have p0022 :=
    @g_elsymdif (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
      (syn_cins2k (syn_cssetk))
      (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))
  have p0023 := @g_snex (.cv x)
  have p0024 :=
    @g_otkelins2kg (syn_csn (.cv x)) A B (syn_cssetk) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0025 :=
    @g_mp3an1 (.classMem (syn_csn (.cv x)) (syn_cvv)) (.classMem A (syn_cvv))
      (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
          (syn_cins2k (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)))
      p0023 p0024
  have p0026 := @g_vex x
  have p0027 := @g_elssetkg (.cv x) B (syn_cvv) (syn_cvv)
  have p0028 :=
    @g_mpan (.classMem (.cv x) (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B))
      p0026 p0027
  have p0029 :=
    @g_adantl (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B))
      (.classMem A (syn_cvv)) p0028
  have p0030 :=
    @g_bitrd (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B) p0025
      p0029
  have p0031 :=
    @g_otkelins3kg (syn_csn (.cv x)) A B (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))
      (syn_cvv) (syn_cvv) (syn_cvv)
  have p0032 :=
    @g_mp3an1 (.classMem (syn_csn (.cv x)) (syn_cvv)) (.classMem A (syn_cvv))
      (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
        (.classMem (syn_copk (syn_csn (.cv x)) A)
          (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
      p0023 p0031
  have freeVariableCertificate7 : z ∉ ((syn_csn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
      not_false_eq_true]
  have freeVariableCertificate8 : z ∉ ((syn_ccnvk (syn_csik C))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, fresh_z_not_C,
      not_false_eq_true]
  have p0033 :=
    @g_opkelcokg z (syn_csn (.cv x)) A (syn_cssetk) (syn_ccnvk (syn_csik C)) (syn_cvv)
      (syn_cvv) freeVariableCertificate7
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by
        exact
          (show z ∉ ((syn_cssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate8
  have p0034 :=
    @g_mpan (.classMem (syn_csn (.cv x)) (syn_cvv)) (.classMem A (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) A)
          (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))) (syn_wex z (syn_wa
            (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C)))
            (.classMem (syn_copk (.cv z) A) (syn_cssetk)))))
      p0023 p0033
  have p0035 := @g_vex y
  have p0036 := @g_elssetkg (.cv y) A (syn_cvv) (syn_cvv)
  have p0037 :=
    @g_mpan (.classMem (.cv y) (syn_cvv)) (.classMem A (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (.cv y) A))
      p0035 p0036
  have p0038 :=
    @g_anbi1d (.classMem A (syn_cvv))
      (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (.cv y) A)
      (.classMem (syn_copk (.cv y) (.cv x)) C) p0037
  have freeVariableCertificate9 : y ∉ ((Wff.classMem A (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_A, or_false, not_false_eq_true]
  have p0039 :=
    @g_exbidv (.classMem A (syn_cvv))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))
        (.classMem (syn_copk (.cv y) (.cv x)) C))
      (syn_wa (.classMem (.cv y) A) (.classMem (syn_copk (.cv y) (.cv x)) C)) y
      freeVariableCertificate9 p0038
  have p0040 := @g_vex z
  have p0041 := @g_opkelcnvk (syn_csn (.cv x)) (.cv z) (syn_csik C) p0023 p0040
  have p0042 := @g_sikss1c1c C
  have p0043 :=
    @g_sseli (syn_csik C) (syn_cxpk (syn_c1c) (syn_c1c))
      (syn_copk (.cv z) (syn_csn (.cv x))) p0042
  have p0044 := @g_opkelxpk (.cv z) (syn_csn (.cv x)) (syn_c1c) (syn_c1c) p0040 p0023
  have freeVariableCertificate10 : y ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_z, not_false_eq_true]
  have p0045 := @g_el1c y (.cv z) freeVariableCertificate10
  have p0046 :=
    @g_biimpi (.classMem (.cv z) (syn_c1c))
      (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) p0045
  have p0047 :=
    @g_adantr (.classMem (.cv z) (syn_c1c))
      (syn_wex y (.classEq (.cv z) (syn_csn (.cv y))))
      (.classMem (syn_csn (.cv x)) (syn_c1c)) p0046
  have p0048 :=
    @g_sylbi
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_c1c) (syn_c1c)))
      (syn_wa (.classMem (.cv z) (syn_c1c)) (.classMem (syn_csn (.cv x)) (syn_c1c)))
      (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) p0044 p0047
  have p0049 :=
    @g_syl (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_c1c) (syn_c1c)))
      (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) p0043 p0048
  have p0050 :=
    @g_pm4_71ri (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
      (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) p0049
  have p0051 :=
    @g_bitri (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C)))
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
      (syn_wa (syn_wex y (.classEq (.cv z) (syn_csn (.cv y))))
        (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)))
      p0041 p0050
  have p0052 :=
    @g_anbi1i (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C)))
      (syn_wa (syn_wex y (.classEq (.cv z) (syn_csn (.cv y))))
        (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)))
      (.classMem (syn_copk (.cv z) A) (syn_cssetk)) p0051
  have p0053 :=
    @g_anass (syn_wex y (.classEq (.cv z) (syn_csn (.cv y))))
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
      (.classMem (syn_copk (.cv z) A) (syn_cssetk))
  have freeVariableCertificate11 :
    y ∉
      ((syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
          (.classMem (syn_copk (.cv z) A) (syn_cssetk)))).fv :=
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
    @g_n_19_41v (.classEq (.cv z) (syn_csn (.cv y)))
      (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
        (.classMem (syn_copk (.cv z) A) (syn_cssetk)))
      y freeVariableCertificate11
  have p0055 :=
    @g_bitr4i
      (syn_wa (syn_wa (syn_wex y (.classEq (.cv z) (syn_csn (.cv y))))
          (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)))
        (.classMem (syn_copk (.cv z) A) (syn_cssetk)))
      (syn_wa (syn_wex y (.classEq (.cv z) (syn_csn (.cv y))))
        (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
          (.classMem (syn_copk (.cv z) A) (syn_cssetk))))
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y)))
          (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
            (.classMem (syn_copk (.cv z) A) (syn_cssetk)))))
      p0053 p0054
  have p0056 :=
    @g_bitri
      (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C)))
        (.classMem (syn_copk (.cv z) A) (syn_cssetk)))
      (syn_wa (syn_wa (syn_wex y (.classEq (.cv z) (syn_csn (.cv y))))
          (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C)))
        (.classMem (syn_copk (.cv z) A) (syn_cssetk)))
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y)))
          (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
            (.classMem (syn_copk (.cv z) A) (syn_cssetk)))))
      p0052 p0055
  have p0057 :=
    @g_exbii
      (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C)))
        (.classMem (syn_copk (.cv z) A) (syn_cssetk)))
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y)))
          (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
            (.classMem (syn_copk (.cv z) A) (syn_cssetk)))))
      z p0056
  have p0058 :=
    @g_excom
      (syn_wa (.classEq (.cv z) (syn_csn (.cv y)))
        (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
          (.classMem (syn_copk (.cv z) A) (syn_cssetk))))
      z y
  have p0059 := @g_snex (.cv y)
  have p0060 := @g_opkeq1 (.cv z) (syn_csn (.cv y)) (syn_csn (.cv x))
  have p0061 :=
    @g_eleq1d (.classEq (.cv z) (syn_csn (.cv y))) (syn_copk (.cv z) (syn_csn (.cv x)))
      (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C) p0060
  have p0062 := @g_opkeq1 (.cv z) (syn_csn (.cv y)) A
  have p0063 :=
    @g_eleq1d (.classEq (.cv z) (syn_csn (.cv y))) (syn_copk (.cv z) A)
      (syn_copk (syn_csn (.cv y)) A) (syn_cssetk) p0062
  have p0064 :=
    @g_anbi12d (.classEq (.cv z) (syn_csn (.cv y)))
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
      (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C))
      (.classMem (syn_copk (.cv z) A) (syn_cssetk))
      (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) p0061 p0063
  have p0065 :=
    @g_ancom (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C))
      (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))
  have p0066 := @g_opksnelsik (.cv y) (.cv x) C p0035 p0026
  have p0067 :=
    @g_anbi2i (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C))
      (.classMem (syn_copk (.cv y) (.cv x)) C)
      (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) p0066
  have p0068 :=
    @g_bitri
      (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C))
        (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))
        (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C)))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))
        (.classMem (syn_copk (.cv y) (.cv x)) C))
      p0065 p0067
  have p0069 :=
    @g_syl6bb (.classEq (.cv z) (syn_csn (.cv y)))
      (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
        (.classMem (syn_copk (.cv z) A) (syn_cssetk)))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x))) (syn_csik C))
        (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))
        (.classMem (syn_copk (.cv y) (.cv x)) C))
      p0064 p0068
  have freeVariableCertificate12 : z ∉ ((syn_csn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_y,
      not_false_eq_true]
  have freeVariableCertificate13 :
    z ∉
      ((syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))
          (.classMem (syn_copk (.cv y) (.cv x)) C))).fv :=
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
    @g_ceqsexv
      (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
        (.classMem (syn_copk (.cv z) A) (syn_cssetk)))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))
        (.classMem (syn_copk (.cv y) (.cv x)) C))
      z (syn_csn (.cv y)) freeVariableCertificate12 freeVariableCertificate13 p0059 p0069
  have p0071 :=
    @g_exbii
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_csn (.cv y)))
          (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
            (.classMem (syn_copk (.cv z) A) (syn_cssetk)))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))
        (.classMem (syn_copk (.cv y) (.cv x)) C))
      y p0070
  have p0072 :=
    @g_n_3bitri
      (syn_wex z
        (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C)))
          (.classMem (syn_copk (.cv z) A) (syn_cssetk))))
      (syn_wex z (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y)))
            (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
              (.classMem (syn_copk (.cv z) A) (syn_cssetk))))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv z) (syn_csn (.cv y)))
            (syn_wa (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_csik C))
              (.classMem (syn_copk (.cv z) A) (syn_cssetk))))))
      (syn_wex y (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))
          (.classMem (syn_copk (.cv y) (.cv x)) C)))
      p0057 p0058 p0071
  have p0073 :=
    (Nominal.biimpRefl (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) C)))
  have p0074 :=
    @g_n_3bitr4g (.classMem A (syn_cvv))
      (syn_wex y (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk))
          (.classMem (syn_copk (.cv y) (.cv x)) C)))
      (syn_wex y (syn_wa (.classMem (.cv y) A) (.classMem (syn_copk (.cv y) (.cv x)) C)))
      (syn_wex z
        (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C)))
          (.classMem (syn_copk (.cv z) A) (syn_cssetk))))
      (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) C)) p0039 p0072 p0073
  have p0075 :=
    @g_bitrd (.classMem A (syn_cvv))
      (.classMem (syn_copk (syn_csn (.cv x)) A)
        (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))
      (syn_wex z
        (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv z)) (syn_ccnvk (syn_csik C)))
          (.classMem (syn_copk (.cv z) A) (syn_cssetk))))
      (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) C)) p0034 p0074
  have freeVariableCertificate14 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0076 :=
    @g_elimak y C A (.cv x) (by exact (show y ∉ (C).fv from (by exact fresh_y_not_C)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate14
      p0026
  have p0077 :=
    @g_syl6bbr (.classMem A (syn_cvv))
      (.classMem (syn_copk (syn_csn (.cv x)) A)
        (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))
      (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) C))
      (.classMem (.cv x) (syn_cimak C A)) p0075 p0076
  have p0078 :=
    @g_adantr (.classMem A (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) A)
          (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))
        (.classMem (.cv x) (syn_cimak C A)))
      (.classMem B (syn_cvv)) p0077
  have p0079 :=
    @g_bitrd (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
      (.classMem (syn_copk (syn_csn (.cv x)) A)
        (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))
      (.classMem (.cv x) (syn_cimak C A)) p0032 p0078
  have p0080 :=
    @g_bibi12d (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_cins2k (syn_cssetk)))
      (.classMem (.cv x) B)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
      (.classMem (.cv x) (syn_cimak C A)) p0030 p0079
  have p0081 :=
    @g_notbid (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
          (syn_cins2k (syn_cssetk)))
        (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))
      (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A))) p0080
  have p0082 :=
    @g_syl5bb
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))
      (.neg (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
            (syn_cins2k (syn_cssetk)))
          (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.neg (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A)))) p0022
      p0081
  have freeVariableCertificate15 :
    x ∉ ((syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0083 :=
    @g_exbidv (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C))))))
      (.neg (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A)))) x
      freeVariableCertificate15 p0082
  have p0084 :=
    @g_syl5rbb
      (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex x (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
          (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A)))))
      p0021 p0083
  have p0085 :=
    @g_syl5bbr
      (.neg (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A)))))
      (syn_wex x (.neg (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A)))))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0005 p0084
  have p0086 :=
    @g_con1bid (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A))))
      (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0085
  have p0087 :=
    @g_bitr3d (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (.neg (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wa (.classMem (syn_copk A B) (syn_cxpk (syn_cvv) (syn_cvv))) (.neg
          (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A)))) p0004
      p0086
  have p0088 := (Nominal.classEqRefl (syn_cimagek C))
  have p0089 :=
    @g_eleq2i (syn_cimagek C)
      (syn_cdif (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_copk A B) p0088
  have p0090 :=
    @g_eldif (syn_copk A B) (syn_cxpk (syn_cvv) (syn_cvv))
      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
  have p0091 :=
    @g_bitri (.classMem (syn_copk A B) (syn_cimagek C))
      (.classMem (syn_copk A B) (syn_cdif (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk))
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wa (.classMem (syn_copk A B) (syn_cxpk (syn_cvv) (syn_cvv))) (.neg
          (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0089 p0090
  have freeVariableCertificate16 : x ∉ ((syn_cimak C A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, Finset.mem_union,
      fresh_x_not_C, fresh_x_not_A, or_false, not_false_eq_true]
  have p0092 :=
    @g_dfcleq x B (syn_cimak C A)
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) freeVariableCertificate16
  have p0093 :=
    @g_n_3bitr4g (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wa (.classMem (syn_copk A B) (syn_cxpk (syn_cvv) (syn_cvv))) (.neg
          (.classMem (syn_copk A B) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik C)))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.all x (syn_wb (.classMem (.cv x) B) (.classMem (.cv x) (syn_cimak C A))))
      (.classMem (syn_copk A B) (syn_cimagek C)) (.classEq B (syn_cimak C A)) p0087 p0091
      p0092
  have p0094 :=
    @g_syl2an (.classMem A V) (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_copk A B) (syn_cimagek C)) (.classEq B (syn_cimak C A)))
      (.classMem B W) p0000 p0001 p0093
  exact p0094

@[expose]
noncomputable def g_opkelimagek (A : Class) (B : Class) (C : Class)
    (hyp_opkelimagek_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_opkelimagek_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk A B) (syn_cimagek C)) (.classEq B (syn_cimak C A))) :=
  by
  have p0000 := @g_opkelimagekg A B C (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (.classMem (syn_copk A B) (syn_cimagek C)) (.classEq B (syn_cimak C A)))
      hyp_opkelimagek_1 hyp_opkelimagek_2 p0000
  exact p0001

@[expose]
noncomputable def g_opkelidkg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (.classMem (syn_copk A B) (syn_cidk)) (.classEq A B))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_idk z x y
      (show z ≠ x from (by exact fresh_z_ne_x)) (show z ≠ y from (by exact fresh_z_ne_y))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 := @g_eqeq1 (.cv x) A (.cv y)
  have p0002 := @g_eqeq2 (.cv y) B A
  have p0003_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb (.objEq x y) (.classEq A (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
    @g_opkelopkabg (.objEq x y) (.classEq A (.cv y)) (.classEq A B) z x y (syn_cidk) A B V
      W
      (by
        exact
          (show x ∉ ((syn_cidk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((syn_cidk)).fv from
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

@[expose]
noncomputable def g_cnvkssvvk (A : Class) :
    Nominal.NPrf (syn_wss (syn_ccnvk A) (syn_cxpk (syn_cvv) (syn_cvv))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cnvk x y z A
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @g_opkabssvvki (.classMem (syn_copk (.cv z) (.cv y)) A) x y z (syn_ccnvk A)
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      p0000
  exact p0001

@[expose]
noncomputable def g_cnvkxpk (A : Class) (B : Class) :
    Nominal.NPrf (.classEq (syn_ccnvk (syn_cxpk A B)) (syn_cxpk B A)) :=
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
  have p0000 := @g_cnvkssvvk (syn_cxpk A B)
  have p0001 := @g_xpkssvvk B A
  have p0002 := @g_ancom (.classMem (.cv y) A) (.classMem (.cv x) B)
  have p0003 := @g_vex x
  have p0004 := @g_vex y
  have p0005 := @g_opkelcnvk (.cv x) (.cv y) (syn_cxpk A B) p0003 p0004
  have p0006 := @g_opkelxpk (.cv y) (.cv x) A B p0004 p0003
  have p0007 :=
    @g_bitri (.classMem (syn_copk (.cv x) (.cv y)) (syn_ccnvk (syn_cxpk A B)))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk A B))
      (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B)) p0005 p0006
  have p0008 := @g_opkelxpk (.cv x) (.cv y) B A p0003 p0004
  have p0009 :=
    @g_n_3bitr4i (syn_wa (.classMem (.cv y) A) (.classMem (.cv x) B))
      (syn_wa (.classMem (.cv x) B) (.classMem (.cv y) A))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_ccnvk (syn_cxpk A B)))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk B A)) p0002 p0007 p0008
  have freeVariableCertificate0 : x ∉ ((syn_ccnvk (syn_cxpk A B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((syn_ccnvk (syn_cxpk A B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((syn_cxpk B A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_B, fresh_x_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((syn_cxpk B A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_y_not_B, fresh_y_not_A, or_false, not_false_eq_true]
  have p0010 :=
    @g_eqrelkriiv x y (syn_ccnvk (syn_cxpk A B)) (syn_cxpk B A) freeVariableCertificate0
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

@[expose]
noncomputable def g_inxpk (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.classEq (syn_cin (syn_cxpk A B) (syn_cxpk C D))
        (syn_cxpk (syn_cin A C) (syn_cin B D))) :=
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
  have p0000 := @g_inss1 (syn_cxpk A B) (syn_cxpk C D)
  have p0001 := @g_xpkssvvk A B
  have p0002 :=
    @g_sstri (syn_cin (syn_cxpk A B) (syn_cxpk C D)) (syn_cxpk A B)
      (syn_cxpk (syn_cvv) (syn_cvv)) p0000 p0001
  have p0003 := @g_xpkssvvk (syn_cin A C) (syn_cin B D)
  have p0004 :=
    @g_an4 (.classMem (.cv x) A) (.classMem (.cv y) B) (.classMem (.cv x) C)
      (.classMem (.cv y) D)
  have p0005 := @g_elin (syn_copk (.cv x) (.cv y)) (syn_cxpk A B) (syn_cxpk C D)
  have p0006 := @g_vex x
  have p0007 := @g_vex y
  have p0008 := @g_opkelxpk (.cv x) (.cv y) A B p0006 p0007
  have p0009 := @g_opkelxpk (.cv x) (.cv y) C D p0006 p0007
  have p0010 :=
    @g_anbi12i (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk A B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk C D))
      (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)) p0008 p0009
  have p0011 :=
    @g_bitri
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cin (syn_cxpk A B) (syn_cxpk C D)))
      (syn_wa (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk A B))
        (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk C D)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
        (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      p0005 p0010
  have p0012 := @g_opkelxpk (.cv x) (.cv y) (syn_cin A C) (syn_cin B D) p0006 p0007
  have p0013 := @g_elin (.cv x) A C
  have p0014 := @g_elin (.cv y) B D
  have p0015 :=
    @g_anbi12i (.classMem (.cv x) (syn_cin A C))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C))
      (.classMem (.cv y) (syn_cin B D))
      (syn_wa (.classMem (.cv y) B) (.classMem (.cv y) D)) p0013 p0014
  have p0016 :=
    @g_bitri (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cin A C) (syn_cin B D)))
      (syn_wa (.classMem (.cv x) (syn_cin A C)) (.classMem (.cv y) (syn_cin B D)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C))
        (syn_wa (.classMem (.cv y) B) (.classMem (.cv y) D)))
      p0012 p0015
  have p0017 :=
    @g_n_3bitr4i
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv y) B))
        (syn_wa (.classMem (.cv x) C) (.classMem (.cv y) D)))
      (syn_wa (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) C))
        (syn_wa (.classMem (.cv y) B) (.classMem (.cv y) D)))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cin (syn_cxpk A B) (syn_cxpk C D)))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cxpk (syn_cin A C) (syn_cin B D))) p0004
      p0011 p0016
  have freeVariableCertificate0 : x ∉ ((syn_cin (syn_cxpk A B) (syn_cxpk C D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, fresh_x_not_C, fresh_x_not_D, or_false,
      not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((syn_cin (syn_cxpk A B) (syn_cxpk C D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_B, fresh_y_not_C, fresh_y_not_D, or_false,
      not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((syn_cxpk (syn_cin A C) (syn_cin B D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_C, fresh_x_not_B, fresh_x_not_D, or_false,
      not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((syn_cxpk (syn_cin A C) (syn_cin B D))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
      fresh_y_not_A, fresh_y_not_C, fresh_y_not_B, fresh_y_not_D, or_false,
      not_false_eq_true]
  have p0018 :=
    @g_eqrelkriiv x y (syn_cin (syn_cxpk A B) (syn_cxpk C D))
      (syn_cxpk (syn_cin A C) (syn_cin B D)) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 freeVariableCertificate3
      (show x ≠ y from (by exact fresh_x_ne_y)) p0002 p0003 p0017
  exact p0018

@[expose]
noncomputable def g_ssetkssvvk :
    Nominal.NPrf (syn_wss (syn_cssetk) (syn_cxpk (syn_cvv) (syn_cvv))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ssetk x y z
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @g_opkabssvvki (syn_wss (.cv y) (.cv z)) x y z (syn_cssetk)
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      p0000
  exact p0001

@[expose]
noncomputable def g_ins2kss (A : Class) :
    Nominal.NPrf
      (syn_wss (syn_cins2k A) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) :=
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
  have p0000 := @g_vex y
  have p0001 := @g_vex z
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
    @g_opkelins2kg w t u (.cv y) (.cv z) A (syn_cvv) (syn_cvv) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 freeVariableCertificate3
      freeVariableCertificate4 freeVariableCertificate5
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A)))
      (show w ≠ t from (by exact fresh_w_ne_t)) (show w ≠ u from (by exact fresh_w_ne_u))
      (show t ≠ u from (by exact fresh_t_ne_u))
  have p0003 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins2k A)) (syn_wex w (syn_wex t
            (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
                (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
                (.classMem (syn_copk (.cv w) (.cv u)) A))))))
      p0000 p0001 p0002
  have p0004 :=
    @g_opkeq12 (.cv y) (.cv z) (syn_csn (syn_csn (.cv w))) (syn_copk (.cv t) (.cv u))
  have p0005 := @g_vex w
  have p0006 := @g_snel1c (.cv w) p0005
  have p0007 := @g_snelpw1 (syn_csn (.cv w)) (syn_c1c)
  have p0008 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (.cv w))) (syn_cpw1 (syn_c1c)))
      (.classMem (syn_csn (.cv w)) (syn_c1c)) p0006 p0007
  have p0009 := @g_vex t
  have p0010 := @g_vex u
  have p0011 := @g_opkelxpk (.cv t) (.cv u) (syn_cvv) (syn_cvv) p0009 p0010
  have p0012 :=
    @g_mpbir2an (.classMem (syn_copk (.cv t) (.cv u)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (.classMem (.cv t) (syn_cvv)) (.classMem (.cv u) (syn_cvv)) p0009 p0010 p0011
  have p0013 := @g_snex (syn_csn (.cv w))
  have p0014 := @g_opkex (.cv t) (.cv u)
  have p0015 :=
    @g_opkelxpk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv t) (.cv u))
      (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_mpbir2an
      (.classMem (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv t) (.cv u)))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (.classMem (syn_csn (syn_csn (.cv w))) (syn_cpw1 (syn_c1c)))
      (.classMem (syn_copk (.cv t) (.cv u)) (syn_cxpk (syn_cvv) (syn_cvv))) p0008 p0012
      p0015
  have p0017 :=
    @g_syl6eqel
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
        (.classEq (.cv z) (syn_copk (.cv t) (.cv u))))
      (syn_copk (.cv y) (.cv z))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv t) (.cv u)))
      (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) p0004 p0016
  have p0018 :=
    @g_n_3adant3 (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
      (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
      (.classMem (syn_copk (.cv y) (.cv z))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (.classMem (syn_copk (.cv w) (.cv u)) A) p0017
  have freeVariableCertificate6 :
    u ∉
      ((Wff.classMem (syn_copk (.cv y) (.cv z))
          (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))).fv :=
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
    @g_exlimiv
      (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
        (.classEq (.cv z) (syn_copk (.cv t) (.cv u))) (.classMem (syn_copk (.cv w) (.cv u)) A))
      (.classMem (syn_copk (.cv y) (.cv z))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      u freeVariableCertificate6 p0018
  have freeVariableCertificate7 :
    w ∉
      ((Wff.classMem (syn_copk (.cv y) (.cv z))
          (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))).fv :=
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
      ((Wff.classMem (syn_copk (.cv y) (.cv z))
          (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))).fv :=
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
    @g_exlimivv
      (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
          (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
          (.classMem (syn_copk (.cv w) (.cv u)) A)))
      (.classMem (syn_copk (.cv y) (.cv z))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      w t freeVariableCertificate7 freeVariableCertificate8 p0019
  have p0021 :=
    @g_sylbi (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins2k A))
      (syn_wex w (syn_wex t (syn_wex u (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv w))))
              (.classEq (.cv z) (syn_copk (.cv t) (.cv u)))
              (.classMem (syn_copk (.cv w) (.cv u)) A)))))
      (.classMem (syn_copk (.cv y) (.cv z))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      p0003 p0020
  have p0022 :=
    @g_gen2
      (.imp (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins2k A))
        (.classMem (syn_copk (.cv y) (.cv z))
          (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))))
      y z p0021
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins2k x y z w u t A
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
    @g_opkabssvvki
      (syn_wex t (syn_wex u (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t))))
              (.classEq (.cv z) (syn_copk (.cv u) (.cv w)))
              (.classMem (syn_copk (.cv t) (.cv w)) A)))))
      x y z (syn_cins2k A) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) p0023
  have freeVariableCertificate9 :
    y ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate10 :
    z ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0025 :=
    @g_ssrelk y z (syn_cins2k A)
      (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (by
        exact
          (show y ∉ ((syn_cins2k A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
      (by
        exact
          (show z ∉ ((syn_cins2k A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
              exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))))
      freeVariableCertificate9 freeVariableCertificate10
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @g_mpbir
      (syn_wss (syn_cins2k A) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (.all y (.all z (.imp (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins2k A))
            (.classMem (syn_copk (.cv y) (.cv z))
              (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))))))
      p0022 p0026
  exact p0027

@[expose]
noncomputable def g_ins3kss (A : Class) :
    Nominal.NPrf
      (syn_wss (syn_cins3k A) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))) :=
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
  have p0000 := @g_vex y
  have p0001 := @g_vex z
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
    @g_opkelins3kg t u w (.cv y) (.cv z) A (syn_cvv) (syn_cvv) freeVariableCertificate0
      freeVariableCertificate1 freeVariableCertificate2 freeVariableCertificate3
      freeVariableCertificate4 freeVariableCertificate5
      (by exact (show t ∉ (A).fv from (by exact fresh_t_not_A)))
      (by exact (show u ∉ (A).fv from (by exact fresh_u_not_A)))
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (show t ≠ u from (by exact fresh_t_ne_u)) (show t ≠ w from (by exact fresh_t_ne_w))
      (show u ≠ w from (by exact fresh_u_ne_w))
  have p0003 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins3k A)) (syn_wex t (syn_wex u
            (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t))))
                (.classEq (.cv z) (syn_copk (.cv u) (.cv w)))
                (.classMem (syn_copk (.cv t) (.cv u)) A))))))
      p0000 p0001 p0002
  have p0004 :=
    @g_opkeq12 (.cv y) (.cv z) (syn_csn (syn_csn (.cv t))) (syn_copk (.cv u) (.cv w))
  have p0005 := @g_vex t
  have p0006 := @g_snel1c (.cv t) p0005
  have p0007 := @g_snelpw1 (syn_csn (.cv t)) (syn_c1c)
  have p0008 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (.cv t))) (syn_cpw1 (syn_c1c)))
      (.classMem (syn_csn (.cv t)) (syn_c1c)) p0006 p0007
  have p0009 := @g_vex u
  have p0010 := @g_vex w
  have p0011 := @g_opkelxpk (.cv u) (.cv w) (syn_cvv) (syn_cvv) p0009 p0010
  have p0012 :=
    @g_mpbir2an (.classMem (syn_copk (.cv u) (.cv w)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (.classMem (.cv u) (syn_cvv)) (.classMem (.cv w) (syn_cvv)) p0009 p0010 p0011
  have p0013 := @g_snex (syn_csn (.cv t))
  have p0014 := @g_opkex (.cv u) (.cv w)
  have p0015 :=
    @g_opkelxpk (syn_csn (syn_csn (.cv t))) (syn_copk (.cv u) (.cv w))
      (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) p0013 p0014
  have p0016 :=
    @g_mpbir2an
      (.classMem (syn_copk (syn_csn (syn_csn (.cv t))) (syn_copk (.cv u) (.cv w)))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (.classMem (syn_csn (syn_csn (.cv t))) (syn_cpw1 (syn_c1c)))
      (.classMem (syn_copk (.cv u) (.cv w)) (syn_cxpk (syn_cvv) (syn_cvv))) p0008 p0012
      p0015
  have p0017 :=
    @g_syl6eqel
      (syn_wa (.classEq (.cv y) (syn_csn (syn_csn (.cv t))))
        (.classEq (.cv z) (syn_copk (.cv u) (.cv w))))
      (syn_copk (.cv y) (.cv z))
      (syn_copk (syn_csn (syn_csn (.cv t))) (syn_copk (.cv u) (.cv w)))
      (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) p0004 p0016
  have p0018 :=
    @g_n_3adant3 (.classEq (.cv y) (syn_csn (syn_csn (.cv t))))
      (.classEq (.cv z) (syn_copk (.cv u) (.cv w)))
      (.classMem (syn_copk (.cv y) (.cv z))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (.classMem (syn_copk (.cv t) (.cv u)) A) p0017
  have freeVariableCertificate6 :
    w ∉
      ((Wff.classMem (syn_copk (.cv y) (.cv z))
          (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))).fv :=
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
    @g_exlimiv
      (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t))))
        (.classEq (.cv z) (syn_copk (.cv u) (.cv w))) (.classMem (syn_copk (.cv t) (.cv u)) A))
      (.classMem (syn_copk (.cv y) (.cv z))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      w freeVariableCertificate6 p0018
  have freeVariableCertificate7 :
    t ∉
      ((Wff.classMem (syn_copk (.cv y) (.cv z))
          (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))).fv :=
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
      ((Wff.classMem (syn_copk (.cv y) (.cv z))
          (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))).fv :=
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
    @g_exlimivv
      (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t))))
          (.classEq (.cv z) (syn_copk (.cv u) (.cv w)))
          (.classMem (syn_copk (.cv t) (.cv u)) A)))
      (.classMem (syn_copk (.cv y) (.cv z))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      t u freeVariableCertificate7 freeVariableCertificate8 p0019
  have p0021 :=
    @g_sylbi (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins3k A))
      (syn_wex t (syn_wex u (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t))))
              (.classEq (.cv z) (syn_copk (.cv u) (.cv w)))
              (.classMem (syn_copk (.cv t) (.cv u)) A)))))
      (.classMem (syn_copk (.cv y) (.cv z))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      p0003 p0020
  have p0022 :=
    @g_gen2
      (.imp (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins3k A))
        (.classMem (syn_copk (.cv y) (.cv z))
          (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))))
      y z p0021
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ins3k x y z w u t A
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
    @g_opkabssvvki
      (syn_wex t (syn_wex u (syn_wex w (syn_w3a (.classEq (.cv y) (syn_csn (syn_csn (.cv t))))
              (.classEq (.cv z) (syn_copk (.cv u) (.cv w)))
              (.classMem (syn_copk (.cv t) (.cv u)) A)))))
      x y z (syn_cins3k A) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) p0023
  have freeVariableCertificate9 :
    y ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate10 :
    z ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0025 :=
    @g_ssrelk y z (syn_cins3k A)
      (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (by
        exact
          (show y ∉ ((syn_cins3k A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
      (by
        exact
          (show z ∉ ((syn_cins3k A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
              exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))))
      freeVariableCertificate9 freeVariableCertificate10
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0026 := Nominal.mp p0024 p0025
  have p0027 :=
    @g_mpbir
      (syn_wss (syn_cins3k A) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (.all y (.all z (.imp (.classMem (syn_copk (.cv y) (.cv z)) (syn_cins3k A))
            (.classMem (syn_copk (.cv y) (.cv z))
              (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))))))
      p0022 p0026
  exact p0027

@[expose]
noncomputable def g_idkssvvk :
    Nominal.NPrf (syn_wss (syn_cidk) (syn_cxpk (syn_cvv) (syn_cvv))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_idk x y z
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @g_opkabssvvki (.objEq y z) x y z (syn_cidk) (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) p0000
  exact p0001

@[expose]
noncomputable def g_elimaksn (A : Class) (B : Class) (C : Class)
    (hyp_elimaksn_1 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_elimaksn_2 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem C (syn_cimak A (syn_csn B))) (.classMem (syn_copk B C) A)) :=
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
    @g_elimak x A (syn_csn B) C (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by
        exact
          (show x ∉ ((syn_csn B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))))
      (by exact (show x ∉ (C).fv from (by exact fresh_x_not_C))) hyp_elimaksn_2
  have p0001 := @g_opkeq1 (.cv x) B C
  have p0002 := @g_eleq1d (.classEq (.cv x) B) (syn_copk (.cv x) C) (syn_copk B C) A p0001
  have freeVariableCertificate0 : x ∉ ((Wff.classMem (syn_copk B C) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_x_not_B, fresh_x_not_C, fresh_x_not_A, or_false, not_false_eq_true]
  have p0003 :=
    @g_rexsn (.classMem (syn_copk (.cv x) C) A) (.classMem (syn_copk B C) A) x B
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B))) freeVariableCertificate0
      hyp_elimaksn_1 p0002
  have p0004 :=
    @g_bitri (.classMem C (syn_cimak A (syn_csn B)))
      (syn_wrex x (syn_csn B) (.classMem (syn_copk (.cv x) C) A))
      (.classMem (syn_copk B C) A) p0000 p0003
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

@[expose]
noncomputable def g_xpkvexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cxpk (syn_cvv) A) (syn_cvv))) :=
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
  have p0000 := @g_xpkeq2 (.cv x) A (syn_cvv)
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cxpk (syn_cvv) (.cv x)) (syn_cxpk (syn_cvv) A)
      (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralXpViaCompletenessDev003.axXp x y z a b
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show x ≠ a from (by exact fresh_x_ne_a)) (show x ≠ b from (by exact fresh_x_ne_b))
      (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ a from (by exact fresh_y_ne_a))
      (show y ≠ b from (by exact fresh_y_ne_b)) (show z ≠ a from (by exact fresh_z_ne_a))
      (show z ≠ b from (by exact fresh_z_ne_b)) (show a ≠ b from (by exact fresh_a_ne_b))
  have freeVariableCertificate0 : y ∉ ((syn_cxpk (syn_cvv) (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0003 := @g_isset y (syn_cxpk (syn_cvv) (.cv x)) freeVariableCertificate0
  have freeVariableCertificate1 : z ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_y, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((syn_cxpk (syn_cvv) (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_z_ne_x, or_false, not_false_eq_true]
  have p0004 :=
    @g_dfcleq z (.cv y) (syn_cxpk (syn_cvv) (.cv x)) freeVariableCertificate1
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
    @g_elxpk a b (.cv z) (syn_cvv) (.cv x) freeVariableCertificate3
      freeVariableCertificate4
      (by
        exact
          (show a ∉ ((syn_cvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show b ∉ ((syn_cvv)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
              exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate5 freeVariableCertificate6
      (show a ≠ b from (by exact fresh_a_ne_b))
  have p0006 := @g_vex a
  have p0007 := @g_biantrur (.classMem (.cv a) (syn_cvv)) (.objMem b x) p0006
  have p0008 :=
    @g_anbi2i (.objMem b x) (syn_wa (.classMem (.cv a) (syn_cvv)) (.objMem b x))
      (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) p0007
  have p0009 :=
    @g_n_2exbii (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x))
      (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b)))
        (syn_wa (.classMem (.cv a) (syn_cvv)) (.objMem b x)))
      a b p0008
  have p0010_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv z) (syn_cxpk (syn_cvv) (.cv x))) (syn_wex a (syn_wex b
            (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b)))
              (syn_wa (.classMem (.cv a) (syn_cvv)) (.objMem b x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cxpk syn_wex syn_cvv
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
    @g_bitr4i (.classMem (.cv z) (syn_cxpk (syn_cvv) (.cv x)))
      (syn_wex a (syn_wex b (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b)))
            (syn_wa (.classMem (.cv a) (syn_cvv)) (.objMem b x)))))
      (syn_wex a
        (syn_wex b (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x))))
      p0010_e00_recanon p0009
  have p0011 :=
    @g_bibi2i (.classMem (.cv z) (syn_cxpk (syn_cvv) (.cv x)))
      (syn_wex a
        (syn_wex b (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x))))
      (.objMem z y) p0010
  have p0012 :=
    @g_albii (syn_wb (.objMem z y) (.classMem (.cv z) (syn_cxpk (syn_cvv) (.cv x))))
      (syn_wb (.objMem z y) (syn_wex a (syn_wex b
            (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x)))))
      z p0011
  have p0013_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv y) (syn_cxpk (syn_cvv) (.cv x))) (.all z
          (syn_wb (.objMem z y) (.classMem (.cv z) (syn_cxpk (syn_cvv) (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cxpk syn_wex syn_cvv
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
    @g_bitri (.classEq (.cv y) (syn_cxpk (syn_cvv) (.cv x)))
      (.all z (syn_wb (.objMem z y) (.classMem (.cv z) (syn_cxpk (syn_cvv) (.cv x)))))
      (.all z (syn_wb (.objMem z y) (syn_wex a (syn_wex b
              (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x))))))
      p0013_e00_recanon p0012
  have p0014 :=
    @g_exbii (.classEq (.cv y) (syn_cxpk (syn_cvv) (.cv x)))
      (.all z (syn_wb (.objMem z y) (syn_wex a (syn_wex b
              (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x))))))
      y p0013
  have p0015 :=
    @g_bitri (.classMem (syn_cxpk (syn_cvv) (.cv x)) (syn_cvv))
      (syn_wex y (.classEq (.cv y) (syn_cxpk (syn_cvv) (.cv x))))
      (syn_wex y (.all z (syn_wb (.objMem z y) (syn_wex a (syn_wex b
                (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x)))))))
      p0003 p0014
  have p0016 :=
    @g_mpbir (.classMem (syn_cxpk (syn_cvv) (.cv x)) (syn_cvv))
      (syn_wex y (.all z (syn_wb (.objMem z y) (syn_wex a (syn_wex b
                (syn_wa (.classEq (.cv z) (syn_copk (.cv a) (.cv b))) (.objMem b x)))))))
      p0002 p0015
  have freeVariableCertificate7 :
    x ∉ ((Wff.classMem (syn_cxpk (syn_cvv) A) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0017 :=
    @g_vtoclg (.classMem (syn_cxpk (syn_cvv) (.cv x)) (syn_cvv))
      (.classMem (syn_cxpk (syn_cvv) A) (syn_cvv)) x A V
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate7
      p0001 p0016
  exact p0017

@[expose]
noncomputable def g_cnvkexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_ccnvk A) (syn_cvv))) :=
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
  have p0000 := @g_cnvkeq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_ccnvk (.cv x)) (syn_ccnvk A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axCnv x y z
      w (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w))
      (show z ≠ w from (by exact fresh_z_ne_w))
  have p0003 := @g_inss1 (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)
  have p0004 := @g_cnvkssvvk (.cv x)
  have freeVariableCertificate0 :
    z ∉ ((syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    w ∉ ((syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_w_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((syn_ccnvk (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
      not_false_eq_true]
  have freeVariableCertificate3 : w ∉ ((syn_ccnvk (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_x,
      not_false_eq_true]
  have p0005 :=
    @g_eqrelk z w (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)) (syn_ccnvk (.cv x))
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      freeVariableCertificate3 (show z ≠ w from (by exact fresh_z_ne_w))
  have p0006 :=
    @g_mp2an
      (syn_wss (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wss (syn_ccnvk (.cv x)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wb (.classEq (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)) (syn_ccnvk (.cv x)))
        (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w))
                (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)))
              (.classMem (syn_copk (.cv z) (.cv w)) (syn_ccnvk (.cv x)))))))
      p0003 p0004 p0005
  have p0007 := @g_vex z
  have p0008 := @g_vex w
  have p0009 := @g_opkelxpk (.cv z) (.cv w) (syn_cvv) (syn_cvv) p0007 p0008
  have p0010 :=
    @g_mpbir2an (.classMem (syn_copk (.cv z) (.cv w)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (.classMem (.cv z) (syn_cvv)) (.classMem (.cv w) (syn_cvv)) p0007 p0008 p0009
  have p0011 := @g_elin (syn_copk (.cv z) (.cv w)) (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)
  have p0012 :=
    @g_mpbiran
      (.classMem (syn_copk (.cv z) (.cv w)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)))
      (.classMem (syn_copk (.cv z) (.cv w)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (.classMem (syn_copk (.cv z) (.cv w)) (.cv y)) p0010 p0011
  have p0013 := @g_opkelcnvk (.cv z) (.cv w) (.cv x) p0007 p0008
  have p0014 :=
    @g_bibi12i
      (.classMem (syn_copk (.cv z) (.cv w)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)))
      (.classMem (syn_copk (.cv z) (.cv w)) (.cv y))
      (.classMem (syn_copk (.cv z) (.cv w)) (syn_ccnvk (.cv x)))
      (.classMem (syn_copk (.cv w) (.cv z)) (.cv x)) p0012 p0013
  have p0015 :=
    @g_n_2albii
      (syn_wb (.classMem (syn_copk (.cv z) (.cv w))
          (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)))
        (.classMem (syn_copk (.cv z) (.cv w)) (syn_ccnvk (.cv x))))
      (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (.cv y))
        (.classMem (syn_copk (.cv w) (.cv z)) (.cv x)))
      z w p0014
  have p0016 :=
    @g_bitri
      (.classEq (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)) (syn_ccnvk (.cv x)))
      (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w))
              (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)))
            (.classMem (syn_copk (.cv z) (.cv w)) (syn_ccnvk (.cv x))))))
      (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (.cv y))
            (.classMem (syn_copk (.cv w) (.cv z)) (.cv x)))))
      p0006 p0015
  have p0017 :=
    @g_biimpri
      (.classEq (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)) (syn_ccnvk (.cv x)))
      (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (.cv y))
            (.classMem (syn_copk (.cv w) (.cv z)) (.cv x)))))
      p0016
  have p0018 := @g_vvex
  have p0019 := @g_xpkvexg (syn_cvv) (syn_cvv)
  have p0020 := Nominal.mp p0018 p0019
  have p0021 := @g_vex y
  have p0022 := @g_inex (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y) p0020 p0021
  have p0023 :=
    @g_syl6eqelr
      (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (.cv y))
            (.classMem (syn_copk (.cv w) (.cv z)) (.cv x)))))
      (syn_ccnvk (.cv x)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv y)) (syn_cvv) p0017
      p0022
  have freeVariableCertificate4 : y ∉ ((Wff.classMem (syn_ccnvk (.cv x)) (syn_cvv))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0024 :=
    @g_exlimiv
      (.all z (.all w (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (.cv y))
            (.classMem (syn_copk (.cv w) (.cv z)) (.cv x)))))
      (.classMem (syn_ccnvk (.cv x)) (syn_cvv)) y freeVariableCertificate4 p0023
  have p0025 := Nominal.mp p0002 p0024
  have freeVariableCertificate5 : x ∉ ((Wff.classMem (syn_ccnvk A) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0026 :=
    @g_vtoclg (.classMem (syn_ccnvk (.cv x)) (syn_cvv))
      (.classMem (syn_ccnvk A) (syn_cvv)) x A V
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate5
      p0001 p0025
  exact p0026

@[expose]
noncomputable def g_cnvkex (A : Class)
    (hyp_cnvkex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_ccnvk A) (syn_cvv)) :=
  by
  have p0000 := @g_cnvkexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_cnvkex_1 p0000
  exact p0001

@[expose]
noncomputable def g_xpkexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cxpk A B) (syn_cvv))) :=
  by
  have p0000 := @g_cnvkxpk (syn_cvv) A
  have p0001 := @g_xpkvexg A V
  have p0002 := @g_cnvkexg (syn_cxpk (syn_cvv) A) (syn_cvv)
  have p0003 :=
    @g_syl (.classMem A V) (.classMem (syn_cxpk (syn_cvv) A) (syn_cvv))
      (.classMem (syn_ccnvk (syn_cxpk (syn_cvv) A)) (syn_cvv)) p0001 p0002
  have p0004 :=
    @g_syl5eqelr (.classMem A V) (syn_cxpk A (syn_cvv)) (syn_ccnvk (syn_cxpk (syn_cvv) A))
      (syn_cvv) p0000 p0003
  have p0005 := @g_xpkvexg B W
  have p0006 := @g_inxpk A (syn_cvv) (syn_cvv) B
  have p0007 := @g_inv1 A
  have p0008 := @g_incom (syn_cvv) B
  have p0009 := @g_inv1 B
  have p0010 := @g_eqtri (syn_cin (syn_cvv) B) (syn_cin B (syn_cvv)) B p0008 p0009
  have p0011 := @g_xpkeq12i (syn_cin A (syn_cvv)) A (syn_cin (syn_cvv) B) B p0007 p0010
  have p0012 :=
    @g_eqtri (syn_cin (syn_cxpk A (syn_cvv)) (syn_cxpk (syn_cvv) B))
      (syn_cxpk (syn_cin A (syn_cvv)) (syn_cin (syn_cvv) B)) (syn_cxpk A B) p0006 p0011
  have p0013 := @g_inexg (syn_cxpk A (syn_cvv)) (syn_cxpk (syn_cvv) B) (syn_cvv) (syn_cvv)
  have p0014 :=
    @g_syl5eqelr
      (syn_wa (.classMem (syn_cxpk A (syn_cvv)) (syn_cvv))
        (.classMem (syn_cxpk (syn_cvv) B) (syn_cvv)))
      (syn_cxpk A B) (syn_cin (syn_cxpk A (syn_cvv)) (syn_cxpk (syn_cvv) B)) (syn_cvv)
      p0012 p0013
  have p0015 :=
    @g_syl2an (.classMem A V) (.classMem (syn_cxpk A (syn_cvv)) (syn_cvv))
      (.classMem (syn_cxpk (syn_cvv) B) (syn_cvv)) (.classMem (syn_cxpk A B) (syn_cvv))
      (.classMem B W) p0004 p0005 p0014
  exact p0015

@[expose]
noncomputable def g_xpkex (A : Class) (B : Class)
    (hyp_xpkex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_xpkex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cxpk A B) (syn_cvv)) :=
  by
  have p0000 := @g_xpkexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_cxpk A B) (syn_cvv)) hyp_xpkex_1 hyp_xpkex_2 p0000
  exact p0001

@[expose]
noncomputable def g_p6exg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cp6 A) (syn_cvv))) :=
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
  have p0000 := @g_p6eq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cp6 (.cv x)) (syn_cp6 A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axTypeLower
      x y z w (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w))
      (show z ≠ w from (by exact fresh_z_ne_w))
  have freeVariableCertificate0 : z ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_y, not_false_eq_true]
  have freeVariableCertificate1 : z ∉ ((syn_cp6 (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
      not_false_eq_true]
  have p0003 :=
    @g_dfcleq z (.cv y) (syn_cp6 (.cv x)) freeVariableCertificate0
      freeVariableCertificate1
  have p0004 := @g_vex z
  have freeVariableCertificate2 : w ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_z, not_false_eq_true]
  have freeVariableCertificate3 : w ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_x, not_false_eq_true]
  have p0005 :=
    @g_elp6 w (.cv z) (.cv x) (syn_cvv) freeVariableCertificate2 freeVariableCertificate3
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_bibi2i (.classMem (.cv z) (syn_cp6 (.cv x)))
      (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x))) (.objMem z y)
      p0006
  have p0008 :=
    @g_albii (syn_wb (.objMem z y) (.classMem (.cv z) (syn_cp6 (.cv x))))
      (syn_wb (.objMem z y) (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x))))
      z p0007
  have p0009_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv y) (syn_cp6 (.cv x)))
        (.all z (syn_wb (.objMem z y) (.classMem (.cv z) (syn_cp6 (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cp6 syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cxpk
          syn_wex syn_cvv syn_csn
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
    @g_bitri (.classEq (.cv y) (syn_cp6 (.cv x)))
      (.all z (syn_wb (.objMem z y) (.classMem (.cv z) (syn_cp6 (.cv x)))))
      (.all z (syn_wb (.objMem z y)
          (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x)))))
      p0009_e00_recanon p0008
  have p0010 :=
    @g_biimpri (.classEq (.cv y) (syn_cp6 (.cv x)))
      (.all z (syn_wb (.objMem z y)
          (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x)))))
      p0009
  have p0011 := @g_vex y
  have p0012 :=
    @g_syl6eqelr
      (.all z (syn_wb (.objMem z y)
          (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x)))))
      (syn_cp6 (.cv x)) (.cv y) (syn_cvv) p0010 p0011
  have freeVariableCertificate4 : y ∉ ((Wff.classMem (syn_cp6 (.cv x)) (syn_cvv))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0013 :=
    @g_exlimiv
      (.all z (syn_wb (.objMem z y)
          (.all w (.classMem (syn_copk (.cv w) (syn_csn (.cv z))) (.cv x)))))
      (.classMem (syn_cp6 (.cv x)) (syn_cvv)) y freeVariableCertificate4 p0012
  have p0014 := Nominal.mp p0002 p0013
  have freeVariableCertificate5 : x ∉ ((Wff.classMem (syn_cp6 A) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0015 :=
    @g_vtoclg (.classMem (syn_cp6 (.cv x)) (syn_cvv)) (.classMem (syn_cp6 A) (syn_cvv)) x
      A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate5 p0001 p0014
  exact p0015

@[expose]
noncomputable def g_dfuni12 (A : Class) :
    Nominal.NPrf (.classEq (syn_cuni1 A) (syn_cp6 (syn_cxpk (syn_cvv) A))) :=
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
  have freeVariableCertificate0 : z ∉ ((Wff.classMem (syn_csn (.cv x)) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_not_A, or_false, not_false_eq_true]
  have p0000 :=
    @g_n_19_27v (.classMem (.cv z) (syn_cvv)) (.classMem (syn_csn (.cv x)) A) z
      freeVariableCertificate0
  have p0001 := @g_vex z
  have p0002 := @g_snex (.cv x)
  have p0003 := @g_opkelxpk (.cv z) (syn_csn (.cv x)) (syn_cvv) A p0001 p0002
  have p0004 :=
    @g_albii (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_cvv) A))
      (syn_wa (.classMem (.cv z) (syn_cvv)) (.classMem (syn_csn (.cv x)) A)) z p0003
  have p0005 := Nominal.gen p0001 z
  have p0006 :=
    @g_biantrur (.all z (.classMem (.cv z) (syn_cvv))) (.classMem (syn_csn (.cv x)) A)
      p0005
  have p0007 :=
    @g_n_3bitr4ri
      (.all z (syn_wa (.classMem (.cv z) (syn_cvv)) (.classMem (syn_csn (.cv x)) A)))
      (syn_wa (.all z (.classMem (.cv z) (syn_cvv))) (.classMem (syn_csn (.cv x)) A))
      (.all z (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_cvv) A)))
      (.classMem (syn_csn (.cv x)) A) p0000 p0004 p0006
  have p0008 := @g_vex x
  have p0009 := @g_eluni1 (.cv x) A p0008
  have freeVariableCertificate1 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((syn_cxpk (syn_cvv) A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_z_not_A, or_false, not_false_eq_true]
  have p0010 :=
    @g_elp6 z (.cv x) (syn_cxpk (syn_cvv) A) (syn_cvv) freeVariableCertificate1
      freeVariableCertificate2
  have p0011 := Nominal.mp p0008 p0010
  have p0012 :=
    @g_n_3bitr4i (.classMem (syn_csn (.cv x)) A)
      (.all z (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_cvv) A)))
      (.classMem (.cv x) (syn_cuni1 A))
      (.classMem (.cv x) (syn_cp6 (syn_cxpk (syn_cvv) A))) p0007 p0009 p0011
  have freeVariableCertificate3 : x ∉ ((syn_cp6 (syn_cxpk (syn_cvv) A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0013 :=
    @g_eqriv x (syn_cuni1 A) (syn_cp6 (syn_cxpk (syn_cvv) A))
      (by
        exact
          (show x ∉ ((syn_cuni1 A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate3 p0012
  exact p0013

@[expose]
noncomputable def g_uni1exg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cuni1 A) (syn_cvv))) :=
  by
  have p0000 := @g_dfuni12 A
  have p0001 := @g_vvex
  have p0002 := @g_xpkexg (syn_cvv) A (syn_cvv) V
  have p0003 :=
    @g_mpan (.classMem (syn_cvv) (syn_cvv)) (.classMem A V)
      (.classMem (syn_cxpk (syn_cvv) A) (syn_cvv)) p0001 p0002
  have p0004 := @g_p6exg (syn_cxpk (syn_cvv) A) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem A V) (.classMem (syn_cxpk (syn_cvv) A) (syn_cvv))
      (.classMem (syn_cp6 (syn_cxpk (syn_cvv) A)) (syn_cvv)) p0003 p0004
  have p0006 :=
    @g_syl5eqel (.classMem A V) (syn_cuni1 A) (syn_cp6 (syn_cxpk (syn_cvv) A)) (syn_cvv)
      p0000 p0005
  exact p0006

@[expose]
noncomputable def g_uni1ex (A : Class)
    (hyp_uni1ex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cuni1 A) (syn_cvv)) :=
  by
  have p0000 := @g_uni1exg A (syn_cvv)
  have p0001 := Nominal.mp hyp_uni1ex_1 p0000
  exact p0001

@[expose]
noncomputable def g_ssetkex : Nominal.NPrf (.classMem (syn_cssetk) (syn_cvv)) :=
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
  have p0001 := @g_inss1 (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)
  have p0002 := @g_ssetkssvvk
  have freeVariableCertificate0 :
    y ∉ ((syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_y_ne_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    z ∉ ((syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_z_ne_x, or_false, not_false_eq_true]
  have p0003 :=
    @g_eqrelk y z (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)) (syn_cssetk)
      freeVariableCertificate0 freeVariableCertificate1
      (by
        exact
          (show y ∉ ((syn_cssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show z ∉ ((syn_cssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0004 :=
    @g_mp2an
      (syn_wss (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wss (syn_cssetk) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wb (.classEq (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)) (syn_cssetk)) (.all y
          (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z))
                (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)))
              (.classMem (syn_copk (.cv y) (.cv z)) (syn_cssetk))))))
      p0001 p0002 p0003
  have p0005 := @g_vex y
  have p0006 := @g_vex z
  have p0007 := @g_opkelxpk (.cv y) (.cv z) (syn_cvv) (syn_cvv) p0005 p0006
  have p0008 :=
    @g_mpbir2an (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv)) p0005 p0006 p0007
  have p0009 := @g_elin (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)
  have p0010 :=
    @g_mpbiran
      (.classMem (syn_copk (.cv y) (.cv z)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)))
      (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (.classMem (syn_copk (.cv y) (.cv z)) (.cv x)) p0008 p0009
  have p0011 := @g_opkelssetkg (.cv y) (.cv z) (syn_cvv) (syn_cvv)
  have p0012 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv z) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (syn_cssetk)) (syn_wss (.cv y) (.cv z)))
      p0005 p0006 p0011
  have freeVariableCertificate2 : w ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_y, not_false_eq_true]
  have freeVariableCertificate3 : w ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_z, not_false_eq_true]
  have p0013 :=
    @g_dfss2 w (.cv y) (.cv z) freeVariableCertificate2 freeVariableCertificate3
  have p0014_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wss (.cv y) (.cv z)) (.all w (.imp (.objMem w y) (.objMem w z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
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
    @g_bitri (.classMem (syn_copk (.cv y) (.cv z)) (syn_cssetk)) (syn_wss (.cv y) (.cv z))
      (.all w (.imp (.objMem w y) (.objMem w z))) p0012 p0014_e01_recanon
  have p0015 :=
    @g_bibi12i
      (.classMem (syn_copk (.cv y) (.cv z)) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)))
      (.classMem (syn_copk (.cv y) (.cv z)) (.cv x))
      (.classMem (syn_copk (.cv y) (.cv z)) (syn_cssetk))
      (.all w (.imp (.objMem w y) (.objMem w z))) p0010 p0014
  have p0016 :=
    @g_n_2albii
      (syn_wb (.classMem (syn_copk (.cv y) (.cv z))
          (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)))
        (.classMem (syn_copk (.cv y) (.cv z)) (syn_cssetk)))
      (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (.cv x))
        (.all w (.imp (.objMem w y) (.objMem w z))))
      y z p0015
  have p0017 :=
    @g_bitri (.classEq (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)) (syn_cssetk))
      (.all y (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z))
              (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)))
            (.classMem (syn_copk (.cv y) (.cv z)) (syn_cssetk)))))
      (.all y (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (.cv x))
            (.all w (.imp (.objMem w y) (.objMem w z))))))
      p0004 p0016
  have p0018 :=
    @g_biimpri (.classEq (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)) (syn_cssetk))
      (.all y (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (.cv x))
            (.all w (.imp (.objMem w y) (.objMem w z))))))
      p0017
  have p0019 := @g_vvex
  have p0020 := @g_xpkvexg (syn_cvv) (syn_cvv)
  have p0021 := Nominal.mp p0019 p0020
  have p0022 := @g_vex x
  have p0023 := @g_inex (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x) p0021 p0022
  have p0024 :=
    @g_syl6eqelr
      (.all y (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (.cv x))
            (.all w (.imp (.objMem w y) (.objMem w z))))))
      (syn_cssetk) (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) (.cv x)) (syn_cvv) p0018 p0023
  have freeVariableCertificate4 : x ∉ ((Wff.classMem (syn_cssetk) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0025 :=
    @g_exlimiv
      (.all y (.all z (syn_wb (.classMem (syn_copk (.cv y) (.cv z)) (.cv x))
            (.all w (.imp (.objMem w y) (.objMem w z))))))
      (.classMem (syn_cssetk) (syn_cvv)) x freeVariableCertificate4 p0024
  have p0026 := Nominal.mp p0000 p0025
  exact p0026


end NFChoice.DirectNominalPrf.WPPReplay

end
