/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock002

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart014`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_sikexlem`. -/
@[expose]
noncomputable def gSikexlem (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y)
    (hyp_sikexlem_1 : Nominal.NPrf (synWss A (synCxpk (synC1c) (synC1c))))
    (hyp_sikexlem_2 : Nominal.NPrf (synWss B (synCxpk (synC1c) (synC1c)))) :
    Nominal.NPrf
      (synWb (.classEq A B) (.all x (.all y
            (synWb (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) A)
              (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) B))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
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
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have freeVariableCertificate0 : z ∉ ((synCxpk (synC1c) (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0000 :=
    @gSsofeq z A B (synCxpk (synC1c) (synC1c))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) freeVariableCertificate0
  have p0001 :=
    @gMp2an (synWss A (synCxpk (synC1c) (synC1c)))
      (synWss B (synCxpk (synC1c) (synC1c)))
      (synWb (.classEq A B) (synWral z (synCxpk (synC1c) (synC1c))
          (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      hyp_sikexlem_1 hyp_sikexlem_2 p0000
  have p0002 :=
    (Nominal.biimpRefl (synWral z (synCxpk (synC1c) (synC1c))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))
  have freeVariableCertificate1 : w ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_z, not_false_eq_true]
  have freeVariableCertificate2 : t ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_z, not_false_eq_true]
  have p0003 :=
    @gElxpk w t (.cv z) (synC1c) (synC1c) freeVariableCertificate1
      freeVariableCertificate2
      (by
        exact
          (show w ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show t ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show w ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show t ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show w ≠ t from (by exact fresh_w_ne_t))
  have freeVariableCertificate3 : x ∉ ((Class.cv w)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_w, not_false_eq_true]
  have p0004 := @gEl1c x (.cv w) freeVariableCertificate3
  have freeVariableCertificate4 : y ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_t, not_false_eq_true]
  have p0005 := @gEl1c y (.cv t) freeVariableCertificate4
  have p0006 :=
    @gAnbi12i (.classMem (.cv w) (synC1c))
      (synWex x (.classEq (.cv w) (synCsn (.cv x)))) (.classMem (.cv t) (synC1c))
      (synWex y (.classEq (.cv t) (synCsn (.cv y)))) p0004 p0005
  have freeVariableCertificate5 : y ∉ ((Wff.classEq (.cv w) (synCsn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_w, (Ne.symm dv_x_y), or_false, not_false_eq_true]
  have freeVariableCertificate6 : x ∉ ((Wff.classEq (.cv t) (synCsn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_t, dv_x_y, or_false, not_false_eq_true]
  have p0007 :=
    @gEeanv (.classEq (.cv w) (synCsn (.cv x))) (.classEq (.cv t) (synCsn (.cv y))) x y
      freeVariableCertificate5 freeVariableCertificate6
  have p0008 :=
    @gBitr4i (synWa (.classMem (.cv w) (synC1c)) (.classMem (.cv t) (synC1c)))
      (synWa (synWex x (.classEq (.cv w) (synCsn (.cv x))))
        (synWex y (.classEq (.cv t) (synCsn (.cv y)))))
      (synWex x (synWex y (synWa (.classEq (.cv w) (synCsn (.cv x)))
            (.classEq (.cv t) (synCsn (.cv y))))))
      p0006 p0007
  have p0009 :=
    @gAnbi2i (synWa (.classMem (.cv w) (synC1c)) (.classMem (.cv t) (synC1c)))
      (synWex x (synWex y (synWa (.classEq (.cv w) (synCsn (.cv x)))
            (.classEq (.cv t) (synCsn (.cv y))))))
      (.classEq (.cv z) (synCopk (.cv w) (.cv t))) p0008
  have p0010 :=
    (Nominal.biimpRefl
      (synW3a (.classEq (.cv w) (synCsn (.cv x))) (.classEq (.cv t) (synCsn (.cv y)))
        (.classEq (.cv z) (synCopk (.cv w) (.cv t)))))
  have p0011 :=
    @gAncom
      (synWa (.classEq (.cv w) (synCsn (.cv x))) (.classEq (.cv t) (synCsn (.cv y))))
      (.classEq (.cv z) (synCopk (.cv w) (.cv t)))
  have p0012 :=
    @gBitri
      (synW3a (.classEq (.cv w) (synCsn (.cv x))) (.classEq (.cv t) (synCsn (.cv y)))
        (.classEq (.cv z) (synCopk (.cv w) (.cv t))))
      (synWa (synWa (.classEq (.cv w) (synCsn (.cv x))) (.classEq (.cv t) (synCsn (.cv y))))
        (.classEq (.cv z) (synCopk (.cv w) (.cv t))))
      (synWa (.classEq (.cv z) (synCopk (.cv w) (.cv t)))
        (synWa (.classEq (.cv w) (synCsn (.cv x))) (.classEq (.cv t) (synCsn (.cv y)))))
      p0010 p0011
  have p0013 :=
    @gN2exbii
      (synW3a (.classEq (.cv w) (synCsn (.cv x))) (.classEq (.cv t) (synCsn (.cv y)))
        (.classEq (.cv z) (synCopk (.cv w) (.cv t))))
      (synWa (.classEq (.cv z) (synCopk (.cv w) (.cv t)))
        (synWa (.classEq (.cv w) (synCsn (.cv x))) (.classEq (.cv t) (synCsn (.cv y)))))
      x y p0012
  have freeVariableCertificate7 :
    x ∉ ((Wff.classEq (.cv z) (synCopk (.cv w) (.cv t)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, fresh_x_ne_t, or_false,
      not_false_eq_true]
  have freeVariableCertificate8 :
    y ∉ ((Wff.classEq (.cv z) (synCopk (.cv w) (.cv t)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_w, fresh_y_ne_t, or_false,
      not_false_eq_true]
  have p0014 :=
    @gN1942vv (.classEq (.cv z) (synCopk (.cv w) (.cv t)))
      (synWa (.classEq (.cv w) (synCsn (.cv x))) (.classEq (.cv t) (synCsn (.cv y)))) x
      y freeVariableCertificate7 freeVariableCertificate8
  have p0015 :=
    @gBitri
      (synWex x (synWex y (synW3a (.classEq (.cv w) (synCsn (.cv x)))
            (.classEq (.cv t) (synCsn (.cv y)))
            (.classEq (.cv z) (synCopk (.cv w) (.cv t))))))
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCopk (.cv w) (.cv t)))
            (synWa (.classEq (.cv w) (synCsn (.cv x)))
              (.classEq (.cv t) (synCsn (.cv y)))))))
      (synWa (.classEq (.cv z) (synCopk (.cv w) (.cv t))) (synWex x (synWex y
            (synWa (.classEq (.cv w) (synCsn (.cv x)))
              (.classEq (.cv t) (synCsn (.cv y)))))))
      p0013 p0014
  have p0016 :=
    @gBitr4i
      (synWa (.classEq (.cv z) (synCopk (.cv w) (.cv t)))
        (synWa (.classMem (.cv w) (synC1c)) (.classMem (.cv t) (synC1c))))
      (synWa (.classEq (.cv z) (synCopk (.cv w) (.cv t))) (synWex x (synWex y
            (synWa (.classEq (.cv w) (synCsn (.cv x)))
              (.classEq (.cv t) (synCsn (.cv y)))))))
      (synWex x (synWex y (synW3a (.classEq (.cv w) (synCsn (.cv x)))
            (.classEq (.cv t) (synCsn (.cv y)))
            (.classEq (.cv z) (synCopk (.cv w) (.cv t))))))
      p0009 p0015
  have p0017 :=
    @gN2exbii
      (synWa (.classEq (.cv z) (synCopk (.cv w) (.cv t)))
        (synWa (.classMem (.cv w) (synC1c)) (.classMem (.cv t) (synC1c))))
      (synWex x (synWex y (synW3a (.classEq (.cv w) (synCsn (.cv x)))
            (.classEq (.cv t) (synCsn (.cv y)))
            (.classEq (.cv z) (synCopk (.cv w) (.cv t))))))
      w t p0016
  have p0018 :=
    @gExrot4
      (synW3a (.classEq (.cv w) (synCsn (.cv x))) (.classEq (.cv t) (synCsn (.cv y)))
        (.classEq (.cv z) (synCopk (.cv w) (.cv t))))
      x y w t
  have p0019 :=
    @gBitr4i
      (synWex w (synWex t (synWa (.classEq (.cv z) (synCopk (.cv w) (.cv t)))
            (synWa (.classMem (.cv w) (synC1c)) (.classMem (.cv t) (synC1c))))))
      (synWex w (synWex t (synWex x (synWex y (synW3a (.classEq (.cv w) (synCsn (.cv x)))
                (.classEq (.cv t) (synCsn (.cv y)))
                (.classEq (.cv z) (synCopk (.cv w) (.cv t))))))))
      (synWex x (synWex y (synWex w (synWex t (synW3a (.classEq (.cv w) (synCsn (.cv x)))
                (.classEq (.cv t) (synCsn (.cv y)))
                (.classEq (.cv z) (synCopk (.cv w) (.cv t))))))))
      p0017 p0018
  have p0020 := @gSnex (.cv x)
  have p0021 := @gSnex (.cv y)
  have p0022 := @gOpkeq1 (.cv w) (synCsn (.cv x)) (.cv t)
  have p0023 :=
    @gEqeq2d (.classEq (.cv w) (synCsn (.cv x))) (synCopk (.cv w) (.cv t))
      (synCopk (synCsn (.cv x)) (.cv t)) (.cv z) p0022
  have p0024 := @gOpkeq2 (.cv t) (synCsn (.cv y)) (synCsn (.cv x))
  have p0025 :=
    @gEqeq2d (.classEq (.cv t) (synCsn (.cv y))) (synCopk (synCsn (.cv x)) (.cv t))
      (synCopk (synCsn (.cv x)) (synCsn (.cv y))) (.cv z) p0024
  have freeVariableCertificate9 : w ∉ ((synCsn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_x,
      not_false_eq_true]
  have freeVariableCertificate10 : t ∉ ((synCsn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate11 : w ∉ ((synCsn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_y,
      not_false_eq_true]
  have freeVariableCertificate12 : t ∉ ((synCsn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
      not_false_eq_true]
  have freeVariableCertificate13 :
    t ∉ ((Wff.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_x, fresh_t_ne_y, or_false,
      not_false_eq_true]
  have freeVariableCertificate14 :
    w ∉ ((Wff.classEq (.cv z) (synCopk (synCsn (.cv x)) (.cv t)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_x, fresh_w_ne_t, or_false,
      not_false_eq_true]
  have p0026 :=
    @gCeqsex2v (.classEq (.cv z) (synCopk (.cv w) (.cv t)))
      (.classEq (.cv z) (synCopk (synCsn (.cv x)) (.cv t)))
      (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y)))) w t
      (synCsn (.cv x)) (synCsn (.cv y)) freeVariableCertificate9
      freeVariableCertificate10 freeVariableCertificate11 freeVariableCertificate12
      freeVariableCertificate13 freeVariableCertificate14
      (show w ≠ t from (by exact fresh_w_ne_t)) p0020 p0021 p0023 p0025
  have p0027 :=
    @gN2exbii
      (synWex w (synWex t (synW3a (.classEq (.cv w) (synCsn (.cv x)))
            (.classEq (.cv t) (synCsn (.cv y)))
            (.classEq (.cv z) (synCopk (.cv w) (.cv t))))))
      (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y)))) x y p0026
  have p0028 :=
    @gN3bitri (.classMem (.cv z) (synCxpk (synC1c) (synC1c)))
      (synWex w (synWex t (synWa (.classEq (.cv z) (synCopk (.cv w) (.cv t)))
            (synWa (.classMem (.cv w) (synC1c)) (.classMem (.cv t) (synC1c))))))
      (synWex x (synWex y (synWex w (synWex t (synW3a (.classEq (.cv w) (synCsn (.cv x)))
                (.classEq (.cv t) (synCsn (.cv y)))
                (.classEq (.cv z) (synCopk (.cv w) (.cv t))))))))
      (synWex x (synWex y (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))))
      p0003 p0019 p0027
  have p0029 :=
    @gImbi1i (.classMem (.cv z) (synCxpk (synC1c) (synC1c)))
      (synWex x (synWex y (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))))
      (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)) p0028
  have freeVariableCertificate15 :
    x ∉ ((synWb (.classMem (.cv z) A) (.classMem (.cv z) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_z, dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate16 :
    y ∉ ((synWb (.classMem (.cv z) A) (.classMem (.cv z) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_z, dv_A_y, dv_B_y, or_false, not_false_eq_true]
  have p0030 :=
    @gN1923vv (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))
      (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)) x y freeVariableCertificate15
      freeVariableCertificate16
  have p0031 :=
    @gBitr4i
      (.imp (.classMem (.cv z) (synCxpk (synC1c) (synC1c)))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.imp (synWex x
          (synWex y (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))
            (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))))
      p0029 p0030
  have p0032 :=
    @gAlbii
      (.imp (.classMem (.cv z) (synCxpk (synC1c) (synC1c)))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))
            (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))))
      z p0031
  have p0033 :=
    @gAlrot3
      (.imp (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      z x y
  have p0034 :=
    @gBitri
      (.all z (.imp (.classMem (.cv z) (synCxpk (synC1c) (synC1c)))
          (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.all z (.all x (.all y
            (.imp (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))
              (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      (.all x (.all y (.all z
            (.imp (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))
              (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      p0032 p0033
  have p0035 := @gOpkex (synCsn (.cv x)) (synCsn (.cv y))
  have p0036 := @gEleq1 (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))) A
  have p0037 := @gEleq1 (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))) B
  have p0038 :=
    @gBibi12d (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))
      (.classMem (.cv z) A) (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) A)
      (.classMem (.cv z) B) (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) B)
      p0036 p0037
  have freeVariableCertificate17 :
    z ∉ ((synCopk (synCsn (.cv x)) (synCsn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate18 :
    z ∉
      ((synWb (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) A)
          (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) B))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_B, or_false,
      not_false_eq_true]
  have p0039 :=
    @gCeqsalv (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))
      (synWb (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) A)
        (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) B))
      z (synCopk (synCsn (.cv x)) (synCsn (.cv y))) freeVariableCertificate17
      freeVariableCertificate18 p0035 p0038
  have p0040 :=
    @gN2albii
      (.all z (.imp (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))
          (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (synWb (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) A)
        (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) B))
      x y p0039
  have p0041 :=
    @gN3bitri
      (synWral z (synCxpk (synC1c) (synC1c))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all z (.imp (.classMem (.cv z) (synCxpk (synC1c) (synC1c)))
          (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.all x (.all y (.all z
            (.imp (.classEq (.cv z) (synCopk (synCsn (.cv x)) (synCsn (.cv y))))
              (synWb (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      (.all x (.all y (synWb (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) A)
            (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) B))))
      p0002 p0034 p0040
  have p0042 :=
    @gBitri (.classEq A B)
      (synWral z (synCxpk (synC1c) (synC1c))
        (synWb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (synWb (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) A)
            (.classMem (synCopk (synCsn (.cv x)) (synCsn (.cv y))) B))))
      p0001 p0041
  exact p0042

/-- Checked nominal proof certificate identified upstream as `g_sikexg`. -/
@[expose]
noncomputable def gSikexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCsik A) (synCvv))) :=
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
  have p0000 := @gSikeq (.cv x) A
  have p0001 :=
    @gEleq1d (.classEq (.cv x) A) (synCsik (.cv x)) (synCsik A) (synCvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axSi x y z w
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show x ≠ w from (by exact fresh_x_ne_w)) (show y ≠ z from (by exact fresh_y_ne_z))
      (show y ≠ w from (by exact fresh_y_ne_w)) (show z ≠ w from (by exact fresh_z_ne_w))
  have p0003 := @gInss1 (synCxpk (synC1c) (synC1c)) (.cv y)
  have p0004 := @gSikss1c1c (.cv x)
  have freeVariableCertificate0 :
    z ∉ ((synCin (synCxpk (synC1c) (synC1c)) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    w ∉ ((synCin (synCxpk (synC1c) (synC1c)) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_w_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((synCsik (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
      not_false_eq_true]
  have freeVariableCertificate3 : w ∉ ((synCsik (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_x,
      not_false_eq_true]
  have p0005 :=
    @gSikexlem z w (synCin (synCxpk (synC1c) (synC1c)) (.cv y)) (synCsik (.cv x))
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      freeVariableCertificate3 (show z ≠ w from (by exact fresh_z_ne_w)) p0003 p0004
  have p0006 := @gVex z
  have p0007 := @gSnel1c (.cv z) p0006
  have p0008 := @gVex w
  have p0009 := @gSnel1c (.cv w) p0008
  have p0010 := @gSnex (.cv z)
  have p0011 := @gSnex (.cv w)
  have p0012 :=
    @gOpkelxpk (synCsn (.cv z)) (synCsn (.cv w)) (synC1c) (synC1c) p0010 p0011
  have p0013 :=
    @gMpbir2an
      (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (synCxpk (synC1c) (synC1c)))
      (.classMem (synCsn (.cv z)) (synC1c)) (.classMem (synCsn (.cv w)) (synC1c))
      p0007 p0009 p0012
  have p0014 :=
    @gElin (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (synCxpk (synC1c) (synC1c))
      (.cv y)
  have p0015 :=
    @gMpbiran
      (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w)))
        (synCin (synCxpk (synC1c) (synC1c)) (.cv y)))
      (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (synCxpk (synC1c) (synC1c)))
      (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (.cv y)) p0013 p0014
  have p0016 := @gOpksnelsik (.cv z) (.cv w) (.cv x) p0006 p0008
  have p0017 :=
    @gBibi12i
      (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w)))
        (synCin (synCxpk (synC1c) (synC1c)) (.cv y)))
      (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (.cv y))
      (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (synCsik (.cv x)))
      (.classMem (synCopk (.cv z) (.cv w)) (.cv x)) p0015 p0016
  have p0018 :=
    @gN2albii
      (synWb (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w)))
          (synCin (synCxpk (synC1c) (synC1c)) (.cv y)))
        (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (synCsik (.cv x))))
      (synWb (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (.cv y))
        (.classMem (synCopk (.cv z) (.cv w)) (.cv x)))
      z w p0017
  have p0019 :=
    @gBitri
      (.classEq (synCin (synCxpk (synC1c) (synC1c)) (.cv y)) (synCsik (.cv x)))
      (.all z (.all w (synWb (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w)))
              (synCin (synCxpk (synC1c) (synC1c)) (.cv y)))
            (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (synCsik (.cv x))))))
      (.all z (.all w (synWb (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (.cv y))
            (.classMem (synCopk (.cv z) (.cv w)) (.cv x)))))
      p0005 p0018
  have p0020 :=
    @gBiimpri
      (.classEq (synCin (synCxpk (synC1c) (synC1c)) (.cv y)) (synCsik (.cv x)))
      (.all z (.all w (synWb (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (.cv y))
            (.classMem (synCopk (.cv z) (.cv w)) (.cv x)))))
      p0019
  have p0021 := @gN1cex
  have p0023 := @gXpkex (synC1c) (synC1c) p0021 p0021
  have p0024 := @gVex y
  have p0025 := @gInex (synCxpk (synC1c) (synC1c)) (.cv y) p0023 p0024
  have p0026 :=
    @gSyl6eqelr
      (.all z (.all w (synWb (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (.cv y))
            (.classMem (synCopk (.cv z) (.cv w)) (.cv x)))))
      (synCsik (.cv x)) (synCin (synCxpk (synC1c) (synC1c)) (.cv y)) (synCvv) p0020
      p0025
  have freeVariableCertificate4 : y ∉ ((Wff.classMem (synCsik (.cv x)) (synCvv))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0027 :=
    @gExlimiv
      (.all z (.all w (synWb (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (.cv y))
            (.classMem (synCopk (.cv z) (.cv w)) (.cv x)))))
      (.classMem (synCsik (.cv x)) (synCvv)) y freeVariableCertificate4 p0026
  have p0028 := Nominal.mp p0002 p0027
  have freeVariableCertificate5 : x ∉ ((Wff.classMem (synCsik A) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0029 :=
    @gVtoclg (.classMem (synCsik (.cv x)) (synCvv)) (.classMem (synCsik A) (synCvv))
      x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate5 p0001 p0028
  exact p0029

/-- Checked nominal proof certificate identified upstream as `g_sikex`. -/
@[expose]
noncomputable def gSikex (A : Class)
    (hyp_sikex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCsik A) (synCvv)) :=
  by
  have p0000 := @gSikexg A (synCvv)
  have p0001 := Nominal.mp hyp_sikex_1 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart015`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dfimak2`. -/
@[expose]
noncomputable def gDfimak2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCimak A B) (synCcompl (synCp6
            (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
              (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))) :=
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
  have p0000 :=
    (Nominal.biimpRefl (synWrex y B (.classMem (synCopk (.cv y) (.cv x)) A)))
  have p0001 :=
    @gExancom (.classMem (.cv y) B) (.classMem (synCopk (.cv y) (.cv x)) A) y
  have p0002 := @gVex x
  have freeVariableCertificate0 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have freeVariableCertificate1 :
    z ∉
      ((synCun (synCcompl (synCxpk (synC1c) (synCvv)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
      Finset.notMem_empty, fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have p0003 :=
    @gElp6 z (.cv x)
      (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
        (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))
      (synCvv) freeVariableCertificate0 freeVariableCertificate1
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gElun (synCopk (.cv z) (synCsn (.cv x)))
      (synCcompl (synCxpk (synC1c) (synCvv)))
      (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))
  have p0006 := @gOpkex (.cv z) (synCsn (.cv x))
  have p0007 :=
    @gElcompl (synCopk (.cv z) (synCsn (.cv x))) (synCxpk (synC1c) (synCvv)) p0006
  have p0008 := @gSnex (.cv x)
  have p0009 := @gVex z
  have p0010 := @gOpkelxpk (.cv z) (synCsn (.cv x)) (synC1c) (synCvv) p0009 p0008
  have p0011 :=
    @gMpbiran2
      (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCxpk (synC1c) (synCvv)))
      (.classMem (.cv z) (synC1c)) (.classMem (synCsn (.cv x)) (synCvv)) p0008 p0010
  have p0012 :=
    @gXchbinx
      (.classMem (synCopk (.cv z) (synCsn (.cv x)))
        (synCcompl (synCxpk (synC1c) (synCvv))))
      (.classMem (synCopk (.cv z) (synCsn (.cv x))) (synCxpk (synC1c) (synCvv)))
      (.classMem (.cv z) (synC1c)) p0007 p0011
  have p0013 :=
    @gOrbi1i
      (.classMem (synCopk (.cv z) (synCsn (.cv x)))
        (synCcompl (synCxpk (synC1c) (synCvv))))
      (.neg (.classMem (.cv z) (synC1c)))
      (.classMem (synCopk (.cv z) (synCsn (.cv x)))
        (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))
      p0012
  have p0014 :=
    @gIman (.classMem (.cv z) (synC1c))
      (.classMem (synCopk (.cv z) (synCsn (.cv x)))
        (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))
  have p0015 :=
    @gImor (.classMem (.cv z) (synC1c))
      (.classMem (synCopk (.cv z) (synCsn (.cv x)))
        (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))
  have freeVariableCertificate2 : y ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_z, not_false_eq_true]
  have p0016 := @gEl1c y (.cv z) freeVariableCertificate2
  have p0017 :=
    @gAnbi1i (.classMem (.cv z) (synC1c))
      (synWex y (.classEq (.cv z) (synCsn (.cv y))))
      (.neg (.classMem (synCopk (.cv z) (synCsn (.cv x)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))
      p0016
  have freeVariableCertificate3 :
    y ∉
      ((Wff.neg (.classMem (synCopk (.cv z) (synCsn (.cv x)))
            (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_z, fresh_y_ne_x,
      fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true]
  have p0018 :=
    @gN1941v (.classEq (.cv z) (synCsn (.cv y)))
      (.neg (.classMem (synCopk (.cv z) (synCsn (.cv x)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))
      y freeVariableCertificate3
  have p0019 :=
    @gBitr4i
      (synWa (.classMem (.cv z) (synC1c)) (.neg
          (.classMem (synCopk (.cv z) (synCsn (.cv x)))
            (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))
      (synWa (synWex y (.classEq (.cv z) (synCsn (.cv y)))) (.neg
          (.classMem (synCopk (.cv z) (synCsn (.cv x)))
            (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))
      (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
            (.classMem (synCopk (.cv z) (synCsn (.cv x)))
              (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))))
      p0017 p0018
  have p0020 :=
    @gNotbii
      (synWa (.classMem (.cv z) (synC1c)) (.neg
          (.classMem (synCopk (.cv z) (synCsn (.cv x)))
            (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))
      (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
            (.classMem (synCopk (.cv z) (synCsn (.cv x)))
              (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))))
      p0019
  have p0021 :=
    @gN3bitr3i
      (.imp (.classMem (.cv z) (synC1c)) (.classMem (synCopk (.cv z) (synCsn (.cv x)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))
      (.neg (synWa (.classMem (.cv z) (synC1c)) (.neg
            (.classMem (synCopk (.cv z) (synCsn (.cv x)))
              (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))))
      (synWo (.neg (.classMem (.cv z) (synC1c)))
        (.classMem (synCopk (.cv z) (synCsn (.cv x)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))
      (.neg (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
              (.classMem (synCopk (.cv z) (synCsn (.cv x)))
                (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))))
      p0014 p0015 p0020
  have p0022 :=
    @gN3bitri
      (.classMem (synCopk (.cv z) (synCsn (.cv x)))
        (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))
      (synWo (.classMem (synCopk (.cv z) (synCsn (.cv x)))
          (synCcompl (synCxpk (synC1c) (synCvv))))
        (.classMem (synCopk (.cv z) (synCsn (.cv x)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))
      (synWo (.neg (.classMem (.cv z) (synC1c)))
        (.classMem (synCopk (.cv z) (synCsn (.cv x)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))
      (.neg (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
              (.classMem (synCopk (.cv z) (synCsn (.cv x)))
                (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))))
      p0005 p0013 p0021
  have p0023 :=
    @gAlbii
      (.classMem (synCopk (.cv z) (synCsn (.cv x)))
        (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))
      (.neg (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
              (.classMem (synCopk (.cv z) (synCsn (.cv x)))
                (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))))
      z p0022
  have p0024 :=
    @gAlnex
      (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
            (.classMem (synCopk (.cv z) (synCsn (.cv x)))
              (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))))
      z
  have p0025 :=
    @gExcom
      (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
          (.classMem (synCopk (.cv z) (synCsn (.cv x)))
            (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))
      z y
  have p0026 := @gSnex (.cv y)
  have p0027 := @gOpkeq1 (.cv z) (synCsn (.cv y)) (synCsn (.cv x))
  have p0028 :=
    @gEleq1d (.classEq (.cv z) (synCsn (.cv y))) (synCopk (.cv z) (synCsn (.cv x)))
      (synCopk (synCsn (.cv y)) (synCsn (.cv x)))
      (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))) p0027
  have p0029 := @gVex y
  have p0030 :=
    @gOpksnelsik (.cv y) (.cv x) (synCcompl (synCin A (synCxpk B (synCvv)))) p0029
      p0002
  have p0031 := @gOpkex (.cv y) (.cv x)
  have p0032 :=
    @gElcompl (synCopk (.cv y) (.cv x)) (synCin A (synCxpk B (synCvv))) p0031
  have p0033 :=
    @gBitri
      (.classMem (synCopk (synCsn (.cv y)) (synCsn (.cv x)))
        (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))
      (.classMem (synCopk (.cv y) (.cv x)) (synCcompl (synCin A (synCxpk B (synCvv)))))
      (.neg (.classMem (synCopk (.cv y) (.cv x)) (synCin A (synCxpk B (synCvv)))))
      p0030 p0032
  have p0034 :=
    @gSyl6bb (.classEq (.cv z) (synCsn (.cv y)))
      (.classMem (synCopk (.cv z) (synCsn (.cv x)))
        (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))
      (.classMem (synCopk (synCsn (.cv y)) (synCsn (.cv x)))
        (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))
      (.neg (.classMem (synCopk (.cv y) (.cv x)) (synCin A (synCxpk B (synCvv)))))
      p0028 p0033
  have p0035 :=
    @gNotbid (.classEq (.cv z) (synCsn (.cv y)))
      (.classMem (synCopk (.cv z) (synCsn (.cv x)))
        (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))
      (.neg (.classMem (synCopk (.cv y) (.cv x)) (synCin A (synCxpk B (synCvv)))))
      p0034
  have freeVariableCertificate4 : z ∉ ((synCsn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_y,
      not_false_eq_true]
  have freeVariableCertificate5 :
    z ∉
      ((Wff.neg (.neg (.classMem (synCopk (.cv y) (.cv x))
              (synCin A (synCxpk B (synCvv))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_y, fresh_z_ne_x,
      fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true]
  have p0036 :=
    @gCeqsexv
      (.neg (.classMem (synCopk (.cv z) (synCsn (.cv x)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))
      (.neg (.neg (.classMem (synCopk (.cv y) (.cv x)) (synCin A (synCxpk B (synCvv))))))
      z (synCsn (.cv y)) freeVariableCertificate4 freeVariableCertificate5 p0026 p0035
  have p0037 := @gElin (synCopk (.cv y) (.cv x)) A (synCxpk B (synCvv))
  have p0038 :=
    @gNotnot (.classMem (synCopk (.cv y) (.cv x)) (synCin A (synCxpk B (synCvv))))
  have p0039 := @gOpkelxpk (.cv y) (.cv x) B (synCvv) p0029 p0002
  have p0040 :=
    @gMpbiran2 (.classMem (synCopk (.cv y) (.cv x)) (synCxpk B (synCvv)))
      (.classMem (.cv y) B) (.classMem (.cv x) (synCvv)) p0002 p0039
  have p0041 :=
    @gAnbi2i (.classMem (synCopk (.cv y) (.cv x)) (synCxpk B (synCvv)))
      (.classMem (.cv y) B) (.classMem (synCopk (.cv y) (.cv x)) A) p0040
  have p0042 :=
    @gN3bitr3i (.classMem (synCopk (.cv y) (.cv x)) (synCin A (synCxpk B (synCvv))))
      (synWa (.classMem (synCopk (.cv y) (.cv x)) A)
        (.classMem (synCopk (.cv y) (.cv x)) (synCxpk B (synCvv))))
      (.neg (.neg (.classMem (synCopk (.cv y) (.cv x)) (synCin A (synCxpk B (synCvv))))))
      (synWa (.classMem (synCopk (.cv y) (.cv x)) A) (.classMem (.cv y) B)) p0037 p0038
      p0041
  have p0043 :=
    @gBitri
      (synWex z (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
            (.classMem (synCopk (.cv z) (synCsn (.cv x)))
              (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))))
      (.neg (.neg (.classMem (synCopk (.cv y) (.cv x)) (synCin A (synCxpk B (synCvv))))))
      (synWa (.classMem (synCopk (.cv y) (.cv x)) A) (.classMem (.cv y) B)) p0036 p0042
  have p0044 :=
    @gExbii
      (synWex z (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
            (.classMem (synCopk (.cv z) (synCsn (.cv x)))
              (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))))
      (synWa (.classMem (synCopk (.cv y) (.cv x)) A) (.classMem (.cv y) B)) y p0043
  have p0045 :=
    @gBitri
      (synWex z (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
              (.classMem (synCopk (.cv z) (synCsn (.cv x)))
                (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))))
      (synWex y (synWex z (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
              (.classMem (synCopk (.cv z) (synCsn (.cv x)))
                (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))))
      (synWex y (synWa (.classMem (synCopk (.cv y) (.cv x)) A) (.classMem (.cv y) B)))
      p0025 p0044
  have p0046 :=
    @gXchbinx
      (.all z (.neg (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
                (.classMem (synCopk (.cv z) (synCsn (.cv x)))
                  (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))))))
      (synWex z (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
              (.classMem (synCopk (.cv z) (synCsn (.cv x)))
                (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))))
      (synWex y (synWa (.classMem (synCopk (.cv y) (.cv x)) A) (.classMem (.cv y) B)))
      p0024 p0045
  have p0047 :=
    @gN3bitri
      (.classMem (.cv x) (synCp6 (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
            (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))
      (.all z (.classMem (synCopk (.cv z) (synCsn (.cv x)))
          (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
            (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))
      (.all z (.neg (synWex y (synWa (.classEq (.cv z) (synCsn (.cv y))) (.neg
                (.classMem (synCopk (.cv z) (synCsn (.cv x)))
                  (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))))))
      (.neg (synWex y (synWa (.classMem (synCopk (.cv y) (.cv x)) A) (.classMem (.cv y) B))))
      p0004 p0023 p0046
  have p0048 :=
    @gCon2bii
      (.classMem (.cv x) (synCp6 (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
            (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))
      (synWex y (synWa (.classMem (synCopk (.cv y) (.cv x)) A) (.classMem (.cv y) B)))
      p0047
  have p0049 :=
    @gN3bitri (synWrex y B (.classMem (synCopk (.cv y) (.cv x)) A))
      (synWex y (synWa (.classMem (.cv y) B) (.classMem (synCopk (.cv y) (.cv x)) A)))
      (synWex y (synWa (.classMem (synCopk (.cv y) (.cv x)) A) (.classMem (.cv y) B)))
      (.neg (.classMem (.cv x) (synCp6 (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
              (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))))
      p0000 p0001 p0048
  have freeVariableCertificate6 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0050 :=
    @gElimak y A B (.cv x) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) freeVariableCertificate6
      p0002
  have p0051 :=
    @gElcompl (.cv x)
      (synCp6 (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))
      p0002
  have p0052 :=
    @gN3bitr4i (synWrex y B (.classMem (synCopk (.cv y) (.cv x)) A))
      (.neg (.classMem (.cv x) (synCp6 (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
              (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))))
      (.classMem (.cv x) (synCimak A B))
      (.classMem (.cv x) (synCcompl (synCp6
            (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
              (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))))
      p0049 p0050 p0051
  have freeVariableCertificate7 : x ∉ ((synCimak A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate8 :
    x ∉
      ((synCcompl (synCp6 (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
              (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cp6,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0053 :=
    @gEqriv x (synCimak A B)
      (synCcompl (synCp6 (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
            (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))
      freeVariableCertificate7 freeVariableCertificate8 p0052
  exact p0053

/-- Checked nominal proof certificate identified upstream as `g_imakexg`. -/
@[expose]
noncomputable def gImakexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCimak A B) (synCvv))) :=
  by
  have p0000 := @gDfimak2 A B
  have p0001 := @gN1cex
  have p0002 := @gVvex
  have p0003 := @gXpkex (synC1c) (synCvv) p0001 p0002
  have p0004 := @gComplex (synCxpk (synC1c) (synCvv)) p0003
  have p0006 := @gXpkexg B (synCvv) W (synCvv)
  have p0007 :=
    @gMpan2 (.classMem B W) (.classMem (synCvv) (synCvv))
      (.classMem (synCxpk B (synCvv)) (synCvv)) p0002 p0006
  have p0008 := @gInexg A (synCxpk B (synCvv)) V (synCvv)
  have p0009 :=
    @gSylan2 (.classMem B W) (.classMem A V) (.classMem (synCxpk B (synCvv)) (synCvv))
      (.classMem (synCin A (synCxpk B (synCvv))) (synCvv)) p0007 p0008
  have p0010 := @gComplexg (synCin A (synCxpk B (synCvv))) (synCvv)
  have p0011 := @gSikexg (synCcompl (synCin A (synCxpk B (synCvv)))) (synCvv)
  have p0012 :=
    @gN3syl (synWa (.classMem A V) (.classMem B W))
      (.classMem (synCin A (synCxpk B (synCvv))) (synCvv))
      (.classMem (synCcompl (synCin A (synCxpk B (synCvv)))) (synCvv))
      (.classMem (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))) (synCvv))
      p0009 p0010 p0011
  have p0013 :=
    @gUnexg (synCcompl (synCxpk (synC1c) (synCvv)))
      (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))) (synCvv) (synCvv)
  have p0014 :=
    @gSylancr (synWa (.classMem A V) (.classMem B W))
      (.classMem (synCcompl (synCxpk (synC1c) (synCvv))) (synCvv))
      (.classMem (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))) (synCvv))
      (.classMem (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))) (synCvv))
      p0004 p0012 p0013
  have p0015 :=
    @gP6exg
      (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
        (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))
      (synCvv)
  have p0016 :=
    @gComplexg
      (synCp6 (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))
      (synCvv)
  have p0017 :=
    @gN3syl (synWa (.classMem A V) (.classMem B W))
      (.classMem (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
          (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))) (synCvv))
      (.classMem (synCp6 (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
            (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))) (synCvv))
      (.classMem (synCcompl (synCp6 (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
              (synCsik (synCcompl (synCin A (synCxpk B (synCvv)))))))) (synCvv))
      p0014 p0015 p0016
  have p0018 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCimak A B)
      (synCcompl (synCp6 (synCun (synCcompl (synCxpk (synC1c) (synCvv)))
            (synCsik (synCcompl (synCin A (synCxpk B (synCvv))))))))
      (synCvv) p0000 p0017
  exact p0018

/-- Checked nominal proof certificate identified upstream as `g_imakex`. -/
@[expose]
noncomputable def gImakex (A : Class) (B : Class)
    (hyp_imakex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_imakex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCimak A B) (synCvv)) :=
  by
  have p0000 := @gImakexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCimak A B) (synCvv)) hyp_imakex_1 hyp_imakex_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dfpw12`. -/
@[expose]
noncomputable def gDfpw12 (A : Class) :
    Nominal.NPrf
      (.classEq (synCpw1 A) (synCimak (synCsik (synCxpk A A)) (synCvv))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (h)
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
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0000 :=
    @gElpw1 y (.cv x) A freeVariableCertificate0
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0001 := @gVex x
  have freeVariableCertificate1 : z ∉ ((synCsik (synCxpk A A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_z_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have p0002 :=
    @gElimakv z (synCsik (synCxpk A A)) (.cv x) freeVariableCertificate1
      freeVariableCertificate2 p0001
  have p0003 := @gVex z
  have freeVariableCertificate3 : w ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_z, not_false_eq_true]
  have freeVariableCertificate4 : y ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_z, not_false_eq_true]
  have freeVariableCertificate5 : w ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_x, not_false_eq_true]
  have freeVariableCertificate6 : w ∉ ((synCxpk A A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_w_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate7 : y ∉ ((synCxpk A A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_y_not_A, or_false, not_false_eq_true]
  have p0004 :=
    @gOpkelsikg w y (.cv z) (.cv x) (synCxpk A A) (synCvv) (synCvv)
      freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      freeVariableCertificate0 freeVariableCertificate6 freeVariableCertificate7
      (show w ≠ y from (by exact fresh_w_ne_y))
  have p0005 :=
    @gMp2an (.classMem (.cv z) (synCvv)) (.classMem (.cv x) (synCvv))
      (synWb (.classMem (synCopk (.cv z) (.cv x)) (synCsik (synCxpk A A))) (synWex w
          (synWex y (synW3a (.classEq (.cv z) (synCsn (.cv w)))
              (.classEq (.cv x) (synCsn (.cv y)))
              (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A))))))
      p0003 p0001 p0004
  have p0006 :=
    @gExbii (.classMem (synCopk (.cv z) (.cv x)) (synCsik (synCxpk A A)))
      (synWex w (synWex y (synW3a (.classEq (.cv z) (synCsn (.cv w)))
            (.classEq (.cv x) (synCsn (.cv y)))
            (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A)))))
      z p0005
  have p0007 :=
    @gExrot3
      (synW3a (.classEq (.cv z) (synCsn (.cv w))) (.classEq (.cv x) (synCsn (.cv y)))
        (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A)))
      y z w
  have p0008 :=
    @gBitr4i (synWex z (.classMem (synCopk (.cv z) (.cv x)) (synCsik (synCxpk A A))))
      (synWex z (synWex w (synWex y (synW3a (.classEq (.cv z) (synCsn (.cv w)))
              (.classEq (.cv x) (synCsn (.cv y)))
              (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A))))))
      (synWex y (synWex z (synWex w (synW3a (.classEq (.cv z) (synCsn (.cv w)))
              (.classEq (.cv x) (synCsn (.cv y)))
              (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A))))))
      p0006 p0007
  have p0009 :=
    (Nominal.biimpRefl
      (synW3a (.classEq (.cv z) (synCsn (.cv w))) (.classEq (.cv x) (synCsn (.cv y)))
        (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A))))
  have p0010 := @gVex w
  have p0011 := @gVex y
  have p0012 := @gOpkelxpk (.cv w) (.cv y) A A p0010 p0011
  have p0013 :=
    @gAnbi2i (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A))
      (synWa (.classMem (.cv w) A) (.classMem (.cv y) A))
      (synWa (.classEq (.cv z) (synCsn (.cv w))) (.classEq (.cv x) (synCsn (.cv y))))
      p0012
  have p0014 :=
    @gAn4 (.classEq (.cv z) (synCsn (.cv w))) (.classEq (.cv x) (synCsn (.cv y)))
      (.classMem (.cv w) A) (.classMem (.cv y) A)
  have p0015 :=
    @gN3bitri
      (synW3a (.classEq (.cv z) (synCsn (.cv w))) (.classEq (.cv x) (synCsn (.cv y)))
        (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A)))
      (synWa (synWa (.classEq (.cv z) (synCsn (.cv w))) (.classEq (.cv x) (synCsn (.cv y))))
        (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A)))
      (synWa (synWa (.classEq (.cv z) (synCsn (.cv w))) (.classEq (.cv x) (synCsn (.cv y))))
        (synWa (.classMem (.cv w) A) (.classMem (.cv y) A)))
      (synWa (synWa (.classEq (.cv z) (synCsn (.cv w))) (.classMem (.cv w) A))
        (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A)))
      p0009 p0013 p0014
  have p0016 :=
    @gN2exbii
      (synW3a (.classEq (.cv z) (synCsn (.cv w))) (.classEq (.cv x) (synCsn (.cv y)))
        (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A)))
      (synWa (synWa (.classEq (.cv z) (synCsn (.cv w))) (.classMem (.cv w) A))
        (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A)))
      z w p0015
  have freeVariableCertificate8 :
    z ∉ ((synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
      Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, or_false,
      not_false_eq_true]
  have freeVariableCertificate9 :
    w ∉ ((synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_A, or_false,
      not_false_eq_true]
  have p0017 :=
    @gN1941vv (synWa (.classEq (.cv z) (synCsn (.cv w))) (.classMem (.cv w) A))
      (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A)) z w
      freeVariableCertificate8 freeVariableCertificate9
  have p0018 := @gSneq (.cv w) (.cv y)
  have p0019 := @gEqeq12 (.cv z) (.cv x) (synCsn (.cv w)) (synCsn (.cv y))
  have p0020_e00_recanon :
    Nominal.NPrf (.imp (.objEq w y) (.classEq (synCsn (.cv w)) (synCsn (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0020_e01_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq z x) (.classEq (synCsn (.cv w)) (synCsn (.cv y))))
        (synWb (.classEq (.cv z) (synCsn (.cv w))) (.classEq (.cv x) (synCsn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCsn synWb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0020 :=
    @gSylan2 (.objEq w y) (.objEq z x) (.classEq (synCsn (.cv w)) (synCsn (.cv y)))
      (synWb (.classEq (.cv z) (synCsn (.cv w))) (.classEq (.cv x) (synCsn (.cv y))))
      p0020_e00_recanon p0020_e01_recanon
  have p0021 := @gEleq1 (.cv w) (.cv y) A
  have p0022_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w y) (synWb (.classMem (.cv w) A) (.classMem (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0021
  have p0022 :=
    @gAdantl (.objEq w y) (synWb (.classMem (.cv w) A) (.classMem (.cv y) A))
      (.objEq z x) p0022_e00_recanon
  have p0023 :=
    @gAnbi12d (synWa (.objEq z x) (.objEq w y)) (.classEq (.cv z) (synCsn (.cv w)))
      (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv w) A) (.classMem (.cv y) A)
      p0020 p0022
  have p0024_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
        (synWb (synWa (.classEq (.cv z) (synCsn (.cv w))) (.classMem (.cv w) A))
          (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0023
  have freeVariableCertificate10 : z ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_y, not_false_eq_true]
  have freeVariableCertificate11 : w ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_y, not_false_eq_true]
  have p0024 :=
    @gSpc2ev (synWa (.classEq (.cv z) (synCsn (.cv w))) (.classMem (.cv w) A))
      (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A)) z w (.cv x)
      (.cv y) freeVariableCertificate2 freeVariableCertificate5 freeVariableCertificate10
      freeVariableCertificate11 freeVariableCertificate8 freeVariableCertificate9
      (show z ≠ w from (by exact fresh_z_ne_w)) p0001 p0011 p0024_e02_recanon
  have p0025 :=
    @gPm471ri (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A))
      (synWex z
        (synWex w (synWa (.classEq (.cv z) (synCsn (.cv w))) (.classMem (.cv w) A))))
      p0024
  have p0026 := @gAncom (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A)
  have p0027 :=
    @gBitr3i
      (synWa (synWex z
          (synWex w (synWa (.classEq (.cv z) (synCsn (.cv w))) (.classMem (.cv w) A))))
        (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A)))
      (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A))
      (synWa (.classMem (.cv y) A) (.classEq (.cv x) (synCsn (.cv y)))) p0025 p0026
  have p0028 :=
    @gN3bitri
      (synWex z (synWex w (synW3a (.classEq (.cv z) (synCsn (.cv w)))
            (.classEq (.cv x) (synCsn (.cv y)))
            (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A)))))
      (synWex z (synWex w
          (synWa (synWa (.classEq (.cv z) (synCsn (.cv w))) (.classMem (.cv w) A))
            (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A)))))
      (synWa (synWex z
          (synWex w (synWa (.classEq (.cv z) (synCsn (.cv w))) (.classMem (.cv w) A))))
        (synWa (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv y) A)))
      (synWa (.classMem (.cv y) A) (.classEq (.cv x) (synCsn (.cv y)))) p0016 p0017
      p0027
  have p0029 :=
    @gExbii
      (synWex z (synWex w (synW3a (.classEq (.cv z) (synCsn (.cv w)))
            (.classEq (.cv x) (synCsn (.cv y)))
            (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A)))))
      (synWa (.classMem (.cv y) A) (.classEq (.cv x) (synCsn (.cv y)))) y p0028
  have p0030 := (Nominal.biimpRefl (synWrex y A (.classEq (.cv x) (synCsn (.cv y)))))
  have p0031 :=
    @gBitr4i
      (synWex y (synWex z (synWex w (synW3a (.classEq (.cv z) (synCsn (.cv w)))
              (.classEq (.cv x) (synCsn (.cv y)))
              (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A))))))
      (synWex y (synWa (.classMem (.cv y) A) (.classEq (.cv x) (synCsn (.cv y)))))
      (synWrex y A (.classEq (.cv x) (synCsn (.cv y)))) p0029 p0030
  have p0032 :=
    @gN3bitri (.classMem (.cv x) (synCimak (synCsik (synCxpk A A)) (synCvv)))
      (synWex z (.classMem (synCopk (.cv z) (.cv x)) (synCsik (synCxpk A A))))
      (synWex y (synWex z (synWex w (synW3a (.classEq (.cv z) (synCsn (.cv w)))
              (.classEq (.cv x) (synCsn (.cv y)))
              (.classMem (synCopk (.cv w) (.cv y)) (synCxpk A A))))))
      (synWrex y A (.classEq (.cv x) (synCsn (.cv y)))) p0002 p0008 p0031
  have p0033 :=
    @gBitr4i (.classMem (.cv x) (synCpw1 A))
      (synWrex y A (.classEq (.cv x) (synCsn (.cv y))))
      (.classMem (.cv x) (synCimak (synCsik (synCxpk A A)) (synCvv))) p0000 p0032
  have freeVariableCertificate12 :
    x ∉ ((synCimak (synCsik (synCxpk A A)) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0034 :=
    @gEqriv x (synCpw1 A) (synCimak (synCsik (synCxpk A A)) (synCvv))
      (by
        exact
          (show x ∉ ((synCpw1 A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate12 p0033
  exact p0034

/-- Checked nominal proof certificate identified upstream as `g_pw1exg`. -/
@[expose]
noncomputable def gPw1exg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCpw1 A) (synCvv))) :=
  by
  have p0000 := @gDfpw12 A
  have p0001 := @gXpkexg A A V V
  have p0002 := @gAnidms (.classMem A V) (.classMem (synCxpk A A) (synCvv)) p0001
  have p0003 := @gSikexg (synCxpk A A) (synCvv)
  have p0004 :=
    @gSyl (.classMem A V) (.classMem (synCxpk A A) (synCvv))
      (.classMem (synCsik (synCxpk A A)) (synCvv)) p0002 p0003
  have p0005 := @gVvex
  have p0006 := @gImakexg (synCsik (synCxpk A A)) (synCvv) (synCvv) (synCvv)
  have p0007 :=
    @gSylancl (.classMem A V) (.classMem (synCsik (synCxpk A A)) (synCvv))
      (.classMem (synCvv) (synCvv))
      (.classMem (synCimak (synCsik (synCxpk A A)) (synCvv)) (synCvv)) p0004 p0005
      p0006
  have p0008 :=
    @gSyl5eqel (.classMem A V) (synCpw1 A)
      (synCimak (synCsik (synCxpk A A)) (synCvv)) (synCvv) p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_pw1ex`. -/
@[expose]
noncomputable def gPw1ex (A : Class)
    (hyp_pw1ex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCpw1 A) (synCvv)) :=
  by
  have p0000 := @gPw1exg A (synCvv)
  have p0001 := Nominal.mp hyp_pw1ex_1 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart016`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_insklem`. -/
@[expose]
noncomputable def gInsklem (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z)
    (hyp_insklem_1 : Nominal.NPrf
        (synWss A (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))))
    (hyp_insklem_2 : Nominal.NPrf
        (synWss B (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))) :
    Nominal.NPrf
      (synWb (.classEq A B) (.all x (.all y (.all z (synWb (.classMem
                  (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) A)
                (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))
                  B)))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ z } : Finset Var) ∪ A.fv ∪ B.fv
  let w : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  let u : Var := freshVar proofSupport 2
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
  have fresh_w_ne_z : w ≠ z := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_w_not_B : w ∉ B.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_t_ne_z : t ≠ z := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_u_ne_y : u ≠ y := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_u : y ≠ u := Ne.symm fresh_u_ne_y
  have fresh_u_ne_z : u ≠ z := by
    intro h
    exact
      fresh_u
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_u : z ≠ u := Ne.symm fresh_u_ne_z
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_w : t ≠ w := Ne.symm fresh_w_ne_t
  have fresh_w_ne_u : w ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_u_ne_w : u ≠ w := Ne.symm fresh_w_ne_u
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_u_ne_t : u ≠ t := Ne.symm fresh_t_ne_u
  have freeVariableCertificate0 :
    w ∉ ((synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0000 :=
    @gSsofeq w A B (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) freeVariableCertificate0
  have p0001 :=
    @gMp2an (synWss A (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (synWss B (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (synWb (.classEq A B)
        (synWral w (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))
          (synWb (.classMem (.cv w) A) (.classMem (.cv w) B))))
      hyp_insklem_1 hyp_insklem_2 p0000
  have freeVariableCertificate1 :
    x ∉ ((synWb (.classMem (.cv w) A) (.classMem (.cv w) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_w, dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have p0002 :=
    @gN1923v
      (synWex y (synWex z (.classEq (.cv w)
            (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))))
      (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)) x freeVariableCertificate1
  have freeVariableCertificate2 :
    y ∉ ((synWb (.classMem (.cv w) A) (.classMem (.cv w) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_w, dv_A_y, dv_B_y, or_false, not_false_eq_true]
  have freeVariableCertificate3 :
    z ∉ ((synWb (.classMem (.cv w) A) (.classMem (.cv w) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_w, dv_A_z, dv_B_z, or_false, not_false_eq_true]
  have p0003 :=
    @gN1923vv
      (.classEq (.cv w) (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
      (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)) y z freeVariableCertificate2
      freeVariableCertificate3
  have p0004 :=
    @gAlbii
      (.all y (.all z (.imp (.classEq (.cv w)
              (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
            (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))))
      (.imp (synWex y (synWex z (.classEq (.cv w)
              (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))))
        (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      x p0003
  have freeVariableCertificate4 : y ∉ ((Wff.classMem (.cv t) (synCpw1 (synC1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_t, or_false,
      not_false_eq_true]
  have freeVariableCertificate5 : z ∉ ((Wff.classMem (.cv t) (synCpw1 (synC1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_t, or_false,
      not_false_eq_true]
  have p0005 :=
    @gN1942vv (.classMem (.cv t) (synCpw1 (synC1c)))
      (.classEq (.cv u) (synCopk (.cv y) (.cv z))) y z freeVariableCertificate4
      freeVariableCertificate5
  have p0006 :=
    @gAnbi2i
      (synWex y (synWex z (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
            (.classEq (.cv u) (synCopk (.cv y) (.cv z))))))
      (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
        (synWex y (synWex z (.classEq (.cv u) (synCopk (.cv y) (.cv z))))))
      (.classEq (.cv w) (synCopk (.cv t) (.cv u))) p0005
  have freeVariableCertificate6 :
    y ∉ ((Wff.classEq (.cv w) (synCopk (.cv t) (.cv u)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_w, fresh_y_ne_t, fresh_y_ne_u, or_false,
      not_false_eq_true]
  have freeVariableCertificate7 :
    z ∉ ((Wff.classEq (.cv w) (synCopk (.cv t) (.cv u)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_t, fresh_z_ne_u, or_false,
      not_false_eq_true]
  have p0007 :=
    @gN1942vv (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
      (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
        (.classEq (.cv u) (synCopk (.cv y) (.cv z))))
      y z freeVariableCertificate6 freeVariableCertificate7
  have freeVariableCertificate8 : y ∉ ((Class.cv u)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_u, not_false_eq_true]
  have freeVariableCertificate9 : z ∉ ((Class.cv u)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_u, not_false_eq_true]
  have p0008 :=
    @gElvvk y z (.cv u) freeVariableCertificate8 freeVariableCertificate9
      (show y ≠ z from (by exact dv_y_z))
  have p0009 :=
    @gAnbi2i (.classMem (.cv u) (synCxpk (synCvv) (synCvv)))
      (synWex y (synWex z (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))
      (.classMem (.cv t) (synCpw1 (synC1c))) p0008
  have p0010 :=
    @gAnbi2i
      (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
        (.classMem (.cv u) (synCxpk (synCvv) (synCvv))))
      (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
        (synWex y (synWex z (.classEq (.cv u) (synCopk (.cv y) (.cv z))))))
      (.classEq (.cv w) (synCopk (.cv t) (.cv u))) p0009
  have p0011 :=
    @gN3bitr4ri
      (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u))) (synWex y (synWex z
            (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
              (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))))
      (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
        (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
          (synWex y (synWex z (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))))
      (synWex y (synWex z (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
            (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
              (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))))
      (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
        (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
          (.classMem (.cv u) (synCxpk (synCvv) (synCvv)))))
      p0006 p0007 p0010
  have p0012 :=
    @gN2exbii
      (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
        (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
          (.classMem (.cv u) (synCxpk (synCvv) (synCvv)))))
      (synWex y (synWex z (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
            (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
              (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))))
      t u p0011
  have freeVariableCertificate10 : t ∉ ((Class.cv w)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_w, not_false_eq_true]
  have freeVariableCertificate11 : u ∉ ((Class.cv w)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_u_ne_w, not_false_eq_true]
  have freeVariableCertificate12 : t ∉ ((synCpw1 (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate13 : u ∉ ((synCpw1 (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate14 : t ∉ ((synCxpk (synCvv) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate15 : u ∉ ((synCxpk (synCvv) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0013 :=
    @gElxpk t u (.cv w) (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))
      freeVariableCertificate10 freeVariableCertificate11 freeVariableCertificate12
      freeVariableCertificate13 freeVariableCertificate14 freeVariableCertificate15
      (show t ≠ u from (by exact fresh_t_ne_u))
  have p0014 :=
    @gExrot3
      (.classEq (.cv w) (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
      x y z
  have p0015 :=
    @gExancom (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))
      (.classMem (.cv t) (synCpw1 (synC1c))) t
  have freeVariableCertificate16 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0016 := @gElpw11c x (.cv t) freeVariableCertificate16
  have p0017 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (.cv x)))))
      (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z)))) p0016
  have freeVariableCertificate17 :
    x ∉ ((Wff.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_t, dv_x_y, dv_x_z, or_false,
      not_false_eq_true]
  have p0018 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv x))))
      (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z)))) x
      freeVariableCertificate17
  have p0019 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
        (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z)))))
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (.cv x)))))
        (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z)))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (.cv x))))
          (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))))
      p0017 p0018
  have p0020 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
        (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z)))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (.cv x))))
          (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))))
      t p0019
  have p0021 :=
    @gBitri
      (synWex t (synWa (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))
          (.classMem (.cv t) (synCpw1 (synC1c)))))
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
          (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))))
      (synWex t (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (.cv x))))
            (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z)))))))
      p0015 p0020
  have p0022 :=
    @gAncom (.classMem (.cv t) (synCpw1 (synC1c)))
      (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
  have p0023 :=
    @gAnbi2i
      (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
        (.classEq (.cv u) (synCopk (.cv y) (.cv z))))
      (synWa (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
        (.classMem (.cv t) (synCpw1 (synC1c))))
      (.classEq (.cv w) (synCopk (.cv t) (.cv u))) p0022
  have p0024 :=
    @gAn12 (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
      (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
      (.classMem (.cv t) (synCpw1 (synC1c)))
  have p0025 :=
    @gBitri
      (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
        (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
          (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))
      (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
        (synWa (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
          (.classMem (.cv t) (synCpw1 (synC1c)))))
      (synWa (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
        (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
          (.classMem (.cv t) (synCpw1 (synC1c)))))
      p0023 p0024
  have p0026 :=
    @gN2exbii
      (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
        (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
          (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))
      (synWa (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
        (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
          (.classMem (.cv t) (synCpw1 (synC1c)))))
      t u p0025
  have p0027 := @gOpkex (.cv y) (.cv z)
  have p0028 := @gOpkeq2 (.cv u) (synCopk (.cv y) (.cv z)) (.cv t)
  have p0029 :=
    @gEqeq2d (.classEq (.cv u) (synCopk (.cv y) (.cv z))) (synCopk (.cv t) (.cv u))
      (synCopk (.cv t) (synCopk (.cv y) (.cv z))) (.cv w) p0028
  have p0030 :=
    @gAnbi1d (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
      (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
      (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))
      (.classMem (.cv t) (synCpw1 (synC1c))) p0029
  have freeVariableCertificate18 : u ∉ ((synCopk (.cv y) (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_u_ne_y, fresh_u_ne_z, or_false, not_false_eq_true]
  have freeVariableCertificate19 :
    u ∉
      ((synWa (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))
          (.classMem (.cv t) (synCpw1 (synC1c))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_u_ne_w, fresh_u_ne_t, fresh_u_ne_y,
      fresh_u_ne_z, or_false, not_false_eq_true]
  have p0031 :=
    @gCeqsexv
      (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
        (.classMem (.cv t) (synCpw1 (synC1c))))
      (synWa (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))
        (.classMem (.cv t) (synCpw1 (synC1c))))
      u (synCopk (.cv y) (.cv z)) freeVariableCertificate18 freeVariableCertificate19
      p0027 p0030
  have p0032 :=
    @gExbii
      (synWex u (synWa (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
          (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
            (.classMem (.cv t) (synCpw1 (synC1c))))))
      (synWa (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))
        (.classMem (.cv t) (synCpw1 (synC1c))))
      t p0031
  have p0033 :=
    @gBitri
      (synWex t (synWex u (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
            (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
              (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))))
      (synWex t (synWex u (synWa (.classEq (.cv u) (synCopk (.cv y) (.cv z)))
            (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
              (.classMem (.cv t) (synCpw1 (synC1c)))))))
      (synWex t (synWa (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))
          (.classMem (.cv t) (synCpw1 (synC1c)))))
      p0026 p0032
  have p0034 := @gSnex (synCsn (.cv x))
  have p0035 := @gOpkeq1 (.cv t) (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))
  have p0036 :=
    @gEqeq2d (.classEq (.cv t) (synCsn (synCsn (.cv x))))
      (synCopk (.cv t) (synCopk (.cv y) (.cv z)))
      (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) (.cv w) p0035
  have freeVariableCertificate20 : t ∉ ((synCsn (synCsn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate21 :
    t ∉
      ((Wff.classEq (.cv w)
          (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_x, fresh_t_ne_y, fresh_t_ne_z,
      or_false, not_false_eq_true]
  have p0037 :=
    @gCeqsexv (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))
      (.classEq (.cv w) (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
      t (synCsn (synCsn (.cv x))) freeVariableCertificate20 freeVariableCertificate21
      p0034 p0036
  have p0038 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv x))))
          (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))))
      (.classEq (.cv w) (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
      x p0037
  have p0039 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (.cv x))))
        (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z)))))
      x t
  have p0040 :=
    @gBitr3i
      (synWex x (.classEq (.cv w)
          (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv x))))
            (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z)))))))
      (synWex t (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (.cv x))))
            (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z)))))))
      p0038 p0039
  have p0041 :=
    @gN3bitr4ri
      (synWex t (synWa (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z))))
          (.classMem (.cv t) (synCpw1 (synC1c)))))
      (synWex t (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (.cv x))))
            (.classEq (.cv w) (synCopk (.cv t) (synCopk (.cv y) (.cv z)))))))
      (synWex t (synWex u (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
            (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
              (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))))
      (synWex x (.classEq (.cv w)
          (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))))
      p0021 p0033 p0040
  have p0042 :=
    @gN2exbii
      (synWex x (.classEq (.cv w)
          (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))))
      (synWex t (synWex u (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
            (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
              (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))))
      y z p0041
  have p0043 :=
    @gExrot4
      (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
        (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
          (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))
      y z t u
  have p0044 :=
    @gBitri
      (synWex y (synWex z (synWex x (.classEq (.cv w)
              (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))))))
      (synWex y (synWex z (synWex t (synWex u
              (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
                (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
                  (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))))))
      (synWex t (synWex u (synWex y (synWex z
              (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
                (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
                  (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))))))
      p0042 p0043
  have p0045 :=
    @gBitri
      (synWex x (synWex y (synWex z (.classEq (.cv w)
              (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))))))
      (synWex y (synWex z (synWex x (.classEq (.cv w)
              (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))))))
      (synWex t (synWex u (synWex y (synWex z
              (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
                (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
                  (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))))))
      p0014 p0044
  have p0046 :=
    @gN3bitr4i
      (synWex t (synWex u (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
            (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
              (.classMem (.cv u) (synCxpk (synCvv) (synCvv)))))))
      (synWex t (synWex u (synWex y (synWex z
              (synWa (.classEq (.cv w) (synCopk (.cv t) (.cv u)))
                (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
                  (.classEq (.cv u) (synCopk (.cv y) (.cv z)))))))))
      (.classMem (.cv w) (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (synWex x (synWex y (synWex z (.classEq (.cv w)
              (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))))))
      p0012 p0013 p0045
  have p0047 :=
    @gImbi1i
      (.classMem (.cv w) (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (synWex x (synWex y (synWex z (.classEq (.cv w)
              (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))))))
      (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)) p0046
  have p0048 :=
    @gN3bitr4ri
      (.all x (.imp (synWex y (synWex z (.classEq (.cv w)
                (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))))
          (synWb (.classMem (.cv w) A) (.classMem (.cv w) B))))
      (.imp (synWex x (synWex y (synWex z (.classEq (.cv w)
                (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))))))
        (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      (.all x (.all y (.all z (.imp (.classEq (.cv w)
                (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
              (synWb (.classMem (.cv w) A) (.classMem (.cv w) B))))))
      (.imp (.classMem (.cv w) (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
        (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      p0002 p0004 p0047
  have p0049 :=
    @gAlbii
      (.imp (.classMem (.cv w) (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
        (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      (.all x (.all y (.all z (.imp (.classEq (.cv w)
                (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
              (synWb (.classMem (.cv w) A) (.classMem (.cv w) B))))))
      w p0048
  have p0050 :=
    (Nominal.biimpRefl
      (synWral w (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))
        (synWb (.classMem (.cv w) A) (.classMem (.cv w) B))))
  have p0051 :=
    @gAlcom
      (.all y (.all z (.imp (.classEq (.cv w)
              (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
            (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))))
      w x
  have p0052 :=
    @gAlrot3
      (.imp (.classEq (.cv w) (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
        (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      w y z
  have p0053 :=
    @gAlbii
      (.all w (.all y (.all z (.imp (.classEq (.cv w)
                (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
              (synWb (.classMem (.cv w) A) (.classMem (.cv w) B))))))
      (.all y (.all z (.all w (.imp (.classEq (.cv w)
                (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
              (synWb (.classMem (.cv w) A) (.classMem (.cv w) B))))))
      x p0052
  have p0054 := @gOpkex (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))
  have p0055 :=
    @gEleq1 (.cv w) (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) A
  have p0056 :=
    @gEleq1 (.cv w) (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) B
  have p0057 :=
    @gBibi12d
      (.classEq (.cv w) (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
      (.classMem (.cv w) A)
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) A)
      (.classMem (.cv w) B)
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) B)
      p0055 p0056
  have freeVariableCertificate22 :
    w ∉ ((synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true]
  have freeVariableCertificate23 :
    w ∉
      ((synWb (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) A)
          (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))
            B))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, fresh_w_not_A, fresh_w_not_B, or_false,
      not_false_eq_true]
  have p0058 :=
    @gCeqsalv (synWb (.classMem (.cv w) A) (.classMem (.cv w) B))
      (synWb (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) A)
        (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) B))
      w (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))
      freeVariableCertificate22 freeVariableCertificate23 p0054 p0057
  have p0059 :=
    @gAlbii
      (.all w (.imp (.classEq (.cv w)
            (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
          (synWb (.classMem (.cv w) A) (.classMem (.cv w) B))))
      (synWb (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) A)
        (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) B))
      z p0058
  have p0060 :=
    @gN2albii
      (.all z (.all w (.imp (.classEq (.cv w)
              (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
            (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))))
      (.all z (synWb
          (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) A)
          (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) B)))
      x y p0059
  have p0061 :=
    @gN3bitrri
      (.all w (.all x (.all y (.all z (.imp (.classEq (.cv w)
                  (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
                (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))))))
      (.all x (.all w (.all y (.all z (.imp (.classEq (.cv w)
                  (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
                (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))))))
      (.all x (.all y (.all z (.all w (.imp (.classEq (.cv w)
                  (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
                (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))))))
      (.all x (.all y (.all z (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) A)
              (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))
                B)))))
      p0051 p0053 p0060
  have p0062 :=
    @gN3bitr4i
      (.all w (.imp (.classMem (.cv w)
            (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
          (synWb (.classMem (.cv w) A) (.classMem (.cv w) B))))
      (.all w (.all x (.all y (.all z (.imp (.classEq (.cv w)
                  (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))))
                (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))))))
      (synWral w (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))
        (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      (.all x (.all y (.all z (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) A)
              (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))
                B)))))
      p0049 p0050 p0061
  have p0063 :=
    @gBitri (.classEq A B)
      (synWral w (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))
        (synWb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      (.all x (.all y (.all z (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z))) A)
              (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv z)))
                B)))))
      p0001 p0062
  exact p0063


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart017`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ins2kexg`. -/
@[expose]
noncomputable def gIns2kexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCins2k A) (synCvv))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  let y : Var := freshVar proofSupport 4
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
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_t_ne_y : t ≠ y :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have p0000 := @gIns2keq (.cv x) A
  have p0001 :=
    @gEleq1d (.classEq (.cv x) A) (synCins2k (.cv x)) (synCins2k A) (synCvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axIns2 x y z
      w t (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show x ≠ t from (by exact fresh_x_ne_t)) (show y ≠ z from (by exact fresh_y_ne_z))
      (show y ≠ w from (by exact fresh_y_ne_w)) (show y ≠ t from (by exact fresh_y_ne_t))
      (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ t from (by exact fresh_z_ne_t))
      (show w ≠ t from (by exact fresh_w_ne_t))
  have p0003 :=
    @gInss1 (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y)
  have p0004 := @gIns2kss (.cv x)
  have freeVariableCertificate0 :
    z ∉
      ((synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    w ∉
      ((synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_w_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate2 :
    t ∉
      ((synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_t_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate3 : z ∉ ((synCins2k (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
      not_false_eq_true]
  have freeVariableCertificate4 : w ∉ ((synCins2k (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_x,
      not_false_eq_true]
  have freeVariableCertificate5 : t ∉ ((synCins2k (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have p0005 :=
    @gInsklem z w t
      (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))
      (synCins2k (.cv x)) freeVariableCertificate0 freeVariableCertificate1
      freeVariableCertificate2 freeVariableCertificate3 freeVariableCertificate4
      freeVariableCertificate5 (show z ≠ w from (by exact fresh_z_ne_w))
      (show z ≠ t from (by exact fresh_z_ne_t)) (show w ≠ t from (by exact fresh_w_ne_t))
      p0003 p0004
  have p0006 := @gVex z
  have p0007 := @gSnel1c (.cv z) p0006
  have p0008 := @gSnelpw1 (synCsn (.cv z)) (synC1c)
  have p0009 :=
    @gMpbir (.classMem (synCsn (synCsn (.cv z))) (synCpw1 (synC1c)))
      (.classMem (synCsn (.cv z)) (synC1c)) p0007 p0008
  have p0010 := @gVex w
  have p0011 := @gVex t
  have p0012 := @gOpkelxpk (.cv w) (.cv t) (synCvv) (synCvv) p0010 p0011
  have p0013 :=
    @gMpbir2an (.classMem (synCopk (.cv w) (.cv t)) (synCxpk (synCvv) (synCvv)))
      (.classMem (.cv w) (synCvv)) (.classMem (.cv t) (synCvv)) p0010 p0011 p0012
  have p0014 := @gSnex (synCsn (.cv z))
  have p0015 := @gOpkex (.cv w) (.cv t)
  have p0016 :=
    @gOpkelxpk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t))
      (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)) p0014 p0015
  have p0017 :=
    @gMpbir2an
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (.classMem (synCsn (synCsn (.cv z))) (synCpw1 (synC1c)))
      (.classMem (synCopk (.cv w) (.cv t)) (synCxpk (synCvv) (synCvv))) p0009 p0013
      p0016
  have p0018 :=
    @gElin (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
      (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y)
  have p0019 :=
    @gMpbiran
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
        (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y)))
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t))) (.cv y))
      p0017 p0018
  have p0020 := @gOtkelins2k (.cv z) (.cv w) (.cv t) (.cv x) p0006 p0010 p0011
  have p0021 :=
    @gBibi12i
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
        (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y)))
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t))) (.cv y))
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
        (synCins2k (.cv x)))
      (.classMem (synCopk (.cv z) (.cv t)) (.cv x)) p0019 p0020
  have p0022 :=
    @gAlbii
      (synWb (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
          (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y)))
        (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
          (synCins2k (.cv x))))
      (synWb (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
          (.cv y)) (.classMem (synCopk (.cv z) (.cv t)) (.cv x)))
      t p0021
  have p0023 :=
    @gN2albii
      (.all t (synWb
          (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
            (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y)))
          (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
            (synCins2k (.cv x)))))
      (.all t (synWb
          (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t))) (.cv y))
          (.classMem (synCopk (.cv z) (.cv t)) (.cv x))))
      z w p0022
  have p0024 :=
    @gBitri
      (.classEq (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))
        (synCins2k (.cv x)))
      (.all z (.all w (.all t (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
                (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))
                  (.cv y)))
              (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
                (synCins2k (.cv x)))))))
      (.all z (.all w (.all t (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
                (.cv y)) (.classMem (synCopk (.cv z) (.cv t)) (.cv x))))))
      p0005 p0023
  have p0025 :=
    @gBiimpri
      (.classEq (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))
        (synCins2k (.cv x)))
      (.all z (.all w (.all t (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
                (.cv y)) (.classMem (synCopk (.cv z) (.cv t)) (.cv x))))))
      p0024
  have p0026 := @gN1cex
  have p0027 := @gPw1ex (synC1c) p0026
  have p0028 := @gVvex
  have p0030 := @gXpkex (synCvv) (synCvv) p0028 p0028
  have p0031 := @gXpkex (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)) p0027 p0030
  have p0032 := @gVex y
  have p0033 :=
    @gInex (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y) p0031
      p0032
  have p0034 :=
    @gSyl6eqelr
      (.all z (.all w (.all t (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
                (.cv y)) (.classMem (synCopk (.cv z) (.cv t)) (.cv x))))))
      (synCins2k (.cv x))
      (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))
      (synCvv) p0025 p0033
  have freeVariableCertificate6 :
    y ∉ ((Wff.classMem (synCins2k (.cv x)) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0035 :=
    @gExlimiv
      (.all z (.all w (.all t (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
                (.cv y)) (.classMem (synCopk (.cv z) (.cv t)) (.cv x))))))
      (.classMem (synCins2k (.cv x)) (synCvv)) y freeVariableCertificate6 p0034
  have p0036 := Nominal.mp p0002 p0035
  have freeVariableCertificate7 : x ∉ ((Wff.classMem (synCins2k A) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0037 :=
    @gVtoclg (.classMem (synCins2k (.cv x)) (synCvv))
      (.classMem (synCins2k A) (synCvv)) x A V
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate7
      p0001 p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_ins3kexg`. -/
@[expose]
noncomputable def gIns3kexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCins3k A) (synCvv))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  let y : Var := freshVar proofSupport 4
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
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_t_ne_y : t ≠ y :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have p0000 := @gIns3keq (.cv x) A
  have p0001 :=
    @gEleq1d (.classEq (.cv x) A) (synCins3k (.cv x)) (synCins3k A) (synCvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axIns3 x y z
      w t (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show x ≠ t from (by exact fresh_x_ne_t)) (show y ≠ z from (by exact fresh_y_ne_z))
      (show y ≠ w from (by exact fresh_y_ne_w)) (show y ≠ t from (by exact fresh_y_ne_t))
      (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ t from (by exact fresh_z_ne_t))
      (show w ≠ t from (by exact fresh_w_ne_t))
  have p0003 :=
    @gInss1 (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y)
  have p0004 := @gIns3kss (.cv x)
  have freeVariableCertificate0 :
    z ∉
      ((synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    w ∉
      ((synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_w_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate2 :
    t ∉
      ((synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_t_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate3 : z ∉ ((synCins3k (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
      not_false_eq_true]
  have freeVariableCertificate4 : w ∉ ((synCins3k (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_x,
      not_false_eq_true]
  have freeVariableCertificate5 : t ∉ ((synCins3k (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have p0005 :=
    @gInsklem z w t
      (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))
      (synCins3k (.cv x)) freeVariableCertificate0 freeVariableCertificate1
      freeVariableCertificate2 freeVariableCertificate3 freeVariableCertificate4
      freeVariableCertificate5 (show z ≠ w from (by exact fresh_z_ne_w))
      (show z ≠ t from (by exact fresh_z_ne_t)) (show w ≠ t from (by exact fresh_w_ne_t))
      p0003 p0004
  have p0006 := @gVex z
  have p0007 := @gSnel1c (.cv z) p0006
  have p0008 := @gSnelpw1 (synCsn (.cv z)) (synC1c)
  have p0009 :=
    @gMpbir (.classMem (synCsn (synCsn (.cv z))) (synCpw1 (synC1c)))
      (.classMem (synCsn (.cv z)) (synC1c)) p0007 p0008
  have p0010 := @gVex w
  have p0011 := @gVex t
  have p0012 := @gOpkelxpk (.cv w) (.cv t) (synCvv) (synCvv) p0010 p0011
  have p0013 :=
    @gMpbir2an (.classMem (synCopk (.cv w) (.cv t)) (synCxpk (synCvv) (synCvv)))
      (.classMem (.cv w) (synCvv)) (.classMem (.cv t) (synCvv)) p0010 p0011 p0012
  have p0014 := @gSnex (synCsn (.cv z))
  have p0015 := @gOpkex (.cv w) (.cv t)
  have p0016 :=
    @gOpkelxpk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t))
      (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)) p0014 p0015
  have p0017 :=
    @gMpbir2an
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (.classMem (synCsn (synCsn (.cv z))) (synCpw1 (synC1c)))
      (.classMem (synCopk (.cv w) (.cv t)) (synCxpk (synCvv) (synCvv))) p0009 p0013
      p0016
  have p0018 :=
    @gElin (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
      (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y)
  have p0019 :=
    @gMpbiran
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
        (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y)))
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
        (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))))
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t))) (.cv y))
      p0017 p0018
  have p0020 := @gOtkelins3k (.cv z) (.cv w) (.cv t) (.cv x) p0006 p0010 p0011
  have p0021 :=
    @gBibi12i
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
        (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y)))
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t))) (.cv y))
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
        (synCins3k (.cv x)))
      (.classMem (synCopk (.cv z) (.cv w)) (.cv x)) p0019 p0020
  have p0022 :=
    @gN2albii
      (synWb (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
          (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y)))
        (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
          (synCins3k (.cv x))))
      (synWb (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
          (.cv y)) (.classMem (synCopk (.cv z) (.cv w)) (.cv x)))
      w t p0021
  have p0023 :=
    @gAlbii
      (.all w (.all t (synWb
            (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
              (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y)))
            (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
              (synCins3k (.cv x))))))
      (.all w (.all t (synWb
            (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
              (.cv y)) (.classMem (synCopk (.cv z) (.cv w)) (.cv x)))))
      z p0022
  have p0024 :=
    @gBitri
      (.classEq (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))
        (synCins3k (.cv x)))
      (.all z (.all w (.all t (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
                (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)))
                  (.cv y)))
              (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
                (synCins3k (.cv x)))))))
      (.all z (.all w (.all t (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
                (.cv y)) (.classMem (synCopk (.cv z) (.cv w)) (.cv x))))))
      p0005 p0023
  have p0025 :=
    @gBiimpri
      (.classEq (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))
        (synCins3k (.cv x)))
      (.all z (.all w (.all t (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
                (.cv y)) (.classMem (synCopk (.cv z) (.cv w)) (.cv x))))))
      p0024
  have p0026 := @gN1cex
  have p0027 := @gPw1ex (synC1c) p0026
  have p0028 := @gVvex
  have p0030 := @gXpkex (synCvv) (synCvv) p0028 p0028
  have p0031 := @gXpkex (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv)) p0027 p0030
  have p0032 := @gVex y
  have p0033 :=
    @gInex (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y) p0031
      p0032
  have p0034 :=
    @gSyl6eqelr
      (.all z (.all w (.all t (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
                (.cv y)) (.classMem (synCopk (.cv z) (.cv w)) (.cv x))))))
      (synCins3k (.cv x))
      (synCin (synCxpk (synCpw1 (synC1c)) (synCxpk (synCvv) (synCvv))) (.cv y))
      (synCvv) p0025 p0033
  have freeVariableCertificate6 :
    y ∉ ((Wff.classMem (synCins3k (.cv x)) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0035 :=
    @gExlimiv
      (.all z (.all w (.all t (synWb
              (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv w) (.cv t)))
                (.cv y)) (.classMem (synCopk (.cv z) (.cv w)) (.cv x))))))
      (.classMem (synCins3k (.cv x)) (synCvv)) y freeVariableCertificate6 p0034
  have p0036 := Nominal.mp p0002 p0035
  have freeVariableCertificate7 : x ∉ ((Wff.classMem (synCins3k A) (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0037 :=
    @gVtoclg (.classMem (synCins3k (.cv x)) (synCvv))
      (.classMem (synCins3k A) (synCvv)) x A V
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate7
      p0001 p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_ins2kex`. -/
@[expose]
noncomputable def gIns2kex (A : Class)
    (hyp_inskex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCins2k A) (synCvv)) :=
  by
  have p0000 := @gIns2kexg A (synCvv)
  have p0001 := Nominal.mp hyp_inskex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_ins3kex`. -/
@[expose]
noncomputable def gIns3kex (A : Class)
    (hyp_inskex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCins3k A) (synCvv)) :=
  by
  have p0000 := @gIns3kexg A (synCvv)
  have p0001 := Nominal.mp hyp_inskex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_cokexg`. -/
@[expose]
noncomputable def gCokexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCcomk A B) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCcomk A B))
  have p0001 := @gIns2kexg A V
  have p0002 := @gCnvkexg B W
  have p0003 := @gIns3kexg (synCcnvk B) (synCvv)
  have p0004 :=
    @gSyl (.classMem B W) (.classMem (synCcnvk B) (synCvv))
      (.classMem (synCins3k (synCcnvk B)) (synCvv)) p0002 p0003
  have p0005 := @gInexg (synCins2k A) (synCins3k (synCcnvk B)) (synCvv) (synCvv)
  have p0006 :=
    @gSyl2an (.classMem A V) (.classMem (synCins2k A) (synCvv))
      (.classMem (synCins3k (synCcnvk B)) (synCvv))
      (.classMem (synCin (synCins2k A) (synCins3k (synCcnvk B))) (synCvv))
      (.classMem B W) p0001 p0004 p0005
  have p0007 := @gVvex
  have p0008 :=
    @gImakexg (synCin (synCins2k A) (synCins3k (synCcnvk B))) (synCvv) (synCvv)
      (synCvv)
  have p0009 :=
    @gSylancl (synWa (.classMem A V) (.classMem B W))
      (.classMem (synCin (synCins2k A) (synCins3k (synCcnvk B))) (synCvv))
      (.classMem (synCvv) (synCvv))
      (.classMem (synCimak (synCin (synCins2k A) (synCins3k (synCcnvk B))) (synCvv))
        (synCvv))
      p0006 p0007 p0008
  have p0010 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCcomk A B)
      (synCimak (synCin (synCins2k A) (synCins3k (synCcnvk B))) (synCvv)) (synCvv)
      p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_cokex`. -/
@[expose]
noncomputable def gCokex (A : Class) (B : Class)
    (hyp_cokex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_cokex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCcomk A B) (synCvv)) :=
  by
  have p0000 := @gCokexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCcomk A B) (synCvv)) hyp_cokex_1 hyp_cokex_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_imagekexg`. -/
@[expose]
noncomputable def gImagekexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCimagek A) (synCvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCimagek A))
  have p0001 := @gSikexg A V
  have p0002 := @gCnvkexg (synCsik A) (synCvv)
  have p0003 :=
    @gSyl (.classMem A V) (.classMem (synCsik A) (synCvv))
      (.classMem (synCcnvk (synCsik A)) (synCvv)) p0001 p0002
  have p0004 := @gSsetkex
  have p0005 := @gCokexg (synCssetk) (synCcnvk (synCsik A)) (synCvv) (synCvv)
  have p0006 :=
    @gMpan (.classMem (synCssetk) (synCvv))
      (.classMem (synCcnvk (synCsik A)) (synCvv))
      (.classMem (synCcomk (synCssetk) (synCcnvk (synCsik A))) (synCvv)) p0004 p0005
  have p0007 :=
    @gSyl (.classMem A V) (.classMem (synCcnvk (synCsik A)) (synCvv))
      (.classMem (synCcomk (synCssetk) (synCcnvk (synCsik A))) (synCvv)) p0003 p0006
  have p0008 := @gIns3kexg (synCcomk (synCssetk) (synCcnvk (synCsik A))) (synCvv)
  have p0009 :=
    @gSyl (.classMem A V)
      (.classMem (synCcomk (synCssetk) (synCcnvk (synCsik A))) (synCvv))
      (.classMem (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))) (synCvv))
      p0007 p0008
  have p0011 := @gIns2kex (synCssetk) p0004
  have p0012 :=
    @gSymdifexg (synCins2k (synCssetk))
      (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))) (synCvv) (synCvv)
  have p0013 :=
    @gMpan (.classMem (synCins2k (synCssetk)) (synCvv))
      (.classMem (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))) (synCvv))
      (.classMem (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A))))) (synCvv))
      p0011 p0012
  have p0014 :=
    @gSyl (.classMem A V)
      (.classMem (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))) (synCvv))
      (.classMem (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A))))) (synCvv))
      p0009 p0013
  have p0015 := @gN1cex
  have p0016 := @gPw1ex (synC1c) p0015
  have p0017 := @gPw1ex (synCpw1 (synC1c)) p0016
  have p0018 :=
    @gImakexg
      (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))))
      (synCpw1 (synCpw1 (synC1c))) (synCvv) (synCvv)
  have p0019 :=
    @gMpan2
      (.classMem (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A))))) (synCvv))
      (.classMem (synCpw1 (synCpw1 (synC1c))) (synCvv))
      (.classMem (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))))
          (synCpw1 (synCpw1 (synC1c)))) (synCvv))
      p0017 p0018
  have p0020 :=
    @gSyl (.classMem A V)
      (.classMem (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A))))) (synCvv))
      (.classMem (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))))
          (synCpw1 (synCpw1 (synC1c)))) (synCvv))
      p0014 p0019
  have p0021 := @gVvex
  have p0023 := @gXpkex (synCvv) (synCvv) p0021 p0021
  have p0024 :=
    @gDifexg (synCxpk (synCvv) (synCvv))
      (synCimak (synCsymdif (synCins2k (synCssetk))
          (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))))
        (synCpw1 (synCpw1 (synC1c))))
      (synCvv) (synCvv)
  have p0025 :=
    @gMpan (.classMem (synCxpk (synCvv) (synCvv)) (synCvv))
      (.classMem (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))))
          (synCpw1 (synCpw1 (synC1c)))) (synCvv))
      (.classMem (synCdif (synCxpk (synCvv) (synCvv)) (synCimak
            (synCsymdif (synCins2k (synCssetk))
              (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))))
            (synCpw1 (synCpw1 (synC1c))))) (synCvv))
      p0023 p0024
  have p0026 :=
    @gSyl (.classMem A V)
      (.classMem (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))))
          (synCpw1 (synCpw1 (synC1c)))) (synCvv))
      (.classMem (synCdif (synCxpk (synCvv) (synCvv)) (synCimak
            (synCsymdif (synCins2k (synCssetk))
              (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))))
            (synCpw1 (synCpw1 (synC1c))))) (synCvv))
      p0020 p0025
  have p0027 :=
    @gSyl5eqel (.classMem A V) (synCimagek A)
      (synCdif (synCxpk (synCvv) (synCvv)) (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCcomk (synCssetk) (synCcnvk (synCsik A)))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCvv) p0000 p0026
  exact p0027

/-- Checked nominal proof certificate identified upstream as `g_imagekex`. -/
@[expose]
noncomputable def gImagekex (A : Class)
    (hyp_imagekex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCimagek A) (synCvv)) :=
  by
  have p0000 := @gImagekexg A (synCvv)
  have p0001 := Nominal.mp hyp_imagekex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dfidk2`. -/
@[expose]
noncomputable def gDfidk2 :
    Nominal.NPrf (.classEq (synCidk) (synCin (synCssetk) (synCcnvk (synCssetk)))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have p0000 := @gIdkssvvk
  have p0001 := @gInss1 (synCssetk) (synCcnvk (synCssetk))
  have p0002 := @gSsetkssvvk
  have p0003 :=
    @gSstri (synCin (synCssetk) (synCcnvk (synCssetk))) (synCssetk)
      (synCxpk (synCvv) (synCvv)) p0001 p0002
  have p0004 := @gEqss (.cv x) (.cv y)
  have p0005 := @gVex x
  have p0006 := @gVex y
  have p0007 := @gOpkelidkg (.cv x) (.cv y) (synCvv) (synCvv)
  have p0008_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv)))
        (synWb (.classMem (synCopk (.cv x) (.cv y)) (synCidk)) (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCvv synWb synCopk synCpr synCun synCnin synWnan synCcompl
          synCsn synCidk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0008 :=
    @gMp2an (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))
      (synWb (.classMem (synCopk (.cv x) (.cv y)) (synCidk)) (.objEq x y)) p0005 p0006
      p0008_e02_recanon
  have p0009 := @gElin (synCopk (.cv x) (.cv y)) (synCssetk) (synCcnvk (synCssetk))
  have p0010 := @gOpkelssetkg (.cv x) (.cv y) (synCvv) (synCvv)
  have p0011 :=
    @gMp2an (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))
      (synWb (.classMem (synCopk (.cv x) (.cv y)) (synCssetk)) (synWss (.cv x) (.cv y)))
      p0005 p0006 p0010
  have p0012 := @gOpkelcnvk (.cv x) (.cv y) (synCssetk) p0005 p0006
  have p0013 := @gOpkelssetkg (.cv y) (.cv x) (synCvv) (synCvv)
  have p0014 :=
    @gMp2an (.classMem (.cv y) (synCvv)) (.classMem (.cv x) (synCvv))
      (synWb (.classMem (synCopk (.cv y) (.cv x)) (synCssetk)) (synWss (.cv y) (.cv x)))
      p0006 p0005 p0013
  have p0015 :=
    @gBitri (.classMem (synCopk (.cv x) (.cv y)) (synCcnvk (synCssetk)))
      (.classMem (synCopk (.cv y) (.cv x)) (synCssetk)) (synWss (.cv y) (.cv x)) p0012
      p0014
  have p0016 :=
    @gAnbi12i (.classMem (synCopk (.cv x) (.cv y)) (synCssetk))
      (synWss (.cv x) (.cv y))
      (.classMem (synCopk (.cv x) (.cv y)) (synCcnvk (synCssetk)))
      (synWss (.cv y) (.cv x)) p0011 p0015
  have p0017 :=
    @gBitri
      (.classMem (synCopk (.cv x) (.cv y)) (synCin (synCssetk) (synCcnvk (synCssetk))))
      (synWa (.classMem (synCopk (.cv x) (.cv y)) (synCssetk))
        (.classMem (synCopk (.cv x) (.cv y)) (synCcnvk (synCssetk))))
      (synWa (synWss (.cv x) (.cv y)) (synWss (.cv y) (.cv x))) p0009 p0016
  have p0018_e00_recanon :
    Nominal.NPrf
      (synWb (.objEq x y) (synWa (synWss (.cv x) (.cv y)) (synWss (.cv y) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa synWss synCin synCcompl synCnin synWnan
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0004
  have p0018 :=
    @gN3bitr4i (.objEq x y) (synWa (synWss (.cv x) (.cv y)) (synWss (.cv y) (.cv x)))
      (.classMem (synCopk (.cv x) (.cv y)) (synCidk))
      (.classMem (synCopk (.cv x) (.cv y)) (synCin (synCssetk) (synCcnvk (synCssetk))))
      p0018_e00_recanon p0008 p0017
  have freeVariableCertificate0 :
    x ∉ ((synCin (synCssetk) (synCcnvk (synCssetk)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    y ∉ ((synCin (synCssetk) (synCcnvk (synCssetk)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0019 :=
    @gEqrelkriiv x y (synCidk) (synCin (synCssetk) (synCcnvk (synCssetk)))
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
      freeVariableCertificate0 freeVariableCertificate1
      (show x ≠ y from (by exact fresh_x_ne_y)) p0000 p0003 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_idkex`. -/
@[expose]
noncomputable def gIdkex : Nominal.NPrf (.classMem (synCidk) (synCvv)) :=
  by
  have p0000 := @gDfidk2
  have p0001 := @gSsetkex
  have p0003 := @gCnvkex (synCssetk) p0001
  have p0004 := @gInex (synCssetk) (synCcnvk (synCssetk)) p0001 p0003
  have p0005 :=
    @gEqeltri (synCidk) (synCin (synCssetk) (synCcnvk (synCssetk))) (synCvv) p0000
      p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart018`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dfuni3`. -/
@[expose]
noncomputable def gDfuni3 (A : Class) :
    Nominal.NPrf
      (.classEq (synCuni A) (synCuni1 (synCimak (synCcnvk (synCssetk)) A))) :=
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
  have p0000 := @gVex y
  have p0001 := @gSnex (.cv x)
  have p0002 := @gOpkelcnvk (.cv y) (synCsn (.cv x)) (synCssetk) p0000 p0001
  have p0003 := @gVex x
  have p0004 := @gElssetk (.cv x) (.cv y) p0003 p0000
  have p0005_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)) (.objMem x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @gBitri (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCcnvk (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)) (.objMem x y) p0002
      p0005_e01_recanon
  have p0006 :=
    @gRexbii (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCcnvk (synCssetk)))
      (.objMem x y) y A p0005
  have p0007 := @gEluni1 (.cv x) (synCimak (synCcnvk (synCssetk)) A) p0003
  have freeVariableCertificate0 : y ∉ ((synCcnvk (synCssetk))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((synCsn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have p0008 :=
    @gElimak y (synCcnvk (synCssetk)) A (synCsn (.cv x)) freeVariableCertificate0
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate1
      p0001
  have p0009 :=
    @gBitri (.classMem (.cv x) (synCuni1 (synCimak (synCcnvk (synCssetk)) A)))
      (.classMem (synCsn (.cv x)) (synCimak (synCcnvk (synCssetk)) A))
      (synWrex y A (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCcnvk (synCssetk))))
      p0007 p0008
  have freeVariableCertificate2 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0010 :=
    @gEluni2 y (.cv x) A freeVariableCertificate2
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0011_e02_recanon :
    Nominal.NPrf (synWb (.classMem (.cv x) (synCuni A)) (synWrex y A (.objMem x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCuni synWex synWa synWrex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
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
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0011 :=
    @gN3bitr4ri
      (synWrex y A (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCcnvk (synCssetk))))
      (synWrex y A (.objMem x y))
      (.classMem (.cv x) (synCuni1 (synCimak (synCcnvk (synCssetk)) A)))
      (.classMem (.cv x) (synCuni A)) p0006 p0009 p0011_e02_recanon
  have freeVariableCertificate3 :
    x ∉ ((synCuni1 (synCimak (synCcnvk (synCssetk)) A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0012 :=
    @gEqriv x (synCuni A) (synCuni1 (synCimak (synCcnvk (synCssetk)) A))
      (by
        exact
          (show x ∉ ((synCuni A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate3 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_uniexg`. -/
@[expose]
noncomputable def gUniexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCuni A) (synCvv))) :=
  by
  have p0000 := @gDfuni3 A
  have p0001 := @gSsetkex
  have p0002 := @gCnvkex (synCssetk) p0001
  have p0003 := @gImakexg (synCcnvk (synCssetk)) A (synCvv) V
  have p0004 :=
    @gMpan (.classMem (synCcnvk (synCssetk)) (synCvv)) (.classMem A V)
      (.classMem (synCimak (synCcnvk (synCssetk)) A) (synCvv)) p0002 p0003
  have p0005 := @gUni1exg (synCimak (synCcnvk (synCssetk)) A) (synCvv)
  have p0006 :=
    @gSyl (.classMem A V) (.classMem (synCimak (synCcnvk (synCssetk)) A) (synCvv))
      (.classMem (synCuni1 (synCimak (synCcnvk (synCssetk)) A)) (synCvv)) p0004 p0005
  have p0007 :=
    @gSyl5eqel (.classMem A V) (synCuni A)
      (synCuni1 (synCimak (synCcnvk (synCssetk)) A)) (synCvv) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_uniex`. -/
@[expose]
noncomputable def gUniex (A : Class)
    (hyp_uniex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCuni A) (synCvv)) :=
  by
  have p0000 := @gUniexg A (synCvv)
  have p0001 := Nominal.mp hyp_uniex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_dfint3`. -/
@[expose]
noncomputable def gDfint3 (A : Class) :
    Nominal.NPrf
      (.classEq (synCint A)
        (synCcompl (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A)))) :=
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
  have p0000 := @gVex x
  have p0001 :=
    @gEluni1 (.cv x) (synCimak (synCcnvk (synCcompl (synCssetk))) A) p0000
  have p0002 := @gSnex (.cv x)
  have freeVariableCertificate0 : y ∉ ((synCcnvk (synCcompl (synCssetk)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((synCsn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have p0003 :=
    @gElimak y (synCcnvk (synCcompl (synCssetk))) A (synCsn (.cv x))
      freeVariableCertificate0 (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      freeVariableCertificate1 p0002
  have p0004 :=
    @gBitri
      (.classMem (.cv x) (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A)))
      (.classMem (synCsn (.cv x)) (synCimak (synCcnvk (synCcompl (synCssetk))) A))
      (synWrex y A (.classMem (synCopk (.cv y) (synCsn (.cv x)))
          (synCcnvk (synCcompl (synCssetk)))))
      p0001 p0003
  have p0005 := @gVex y
  have p0006 :=
    @gOpkelcnvk (.cv y) (synCsn (.cv x)) (synCcompl (synCssetk)) p0005 p0002
  have p0007 := @gOpkex (synCsn (.cv x)) (.cv y)
  have p0008 := @gElcompl (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk) p0007
  have p0009 := @gElssetk (.cv x) (.cv y) p0000 p0005
  have p0010_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)) (.objMem x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gNotbii (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)) (.objMem x y)
      p0010_e00_recanon
  have p0011 :=
    @gN3bitri
      (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCcnvk (synCcompl (synCssetk))))
      (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCcompl (synCssetk)))
      (.neg (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)))
      (.neg (.objMem x y)) p0006 p0008 p0010
  have p0012 :=
    @gRexbii
      (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCcnvk (synCcompl (synCssetk))))
      (.neg (.objMem x y)) y A p0011
  have p0013 := @gRexnal (.objMem x y) y A
  have p0014 :=
    @gN3bitri
      (.classMem (.cv x) (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A)))
      (synWrex y A (.classMem (synCopk (.cv y) (synCsn (.cv x)))
          (synCcnvk (synCcompl (synCssetk)))))
      (synWrex y A (.neg (.objMem x y))) (.neg (synWral y A (.objMem x y))) p0004 p0012
      p0013
  have p0015 :=
    @gCon2bii
      (.classMem (.cv x) (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A)))
      (synWral y A (.objMem x y)) p0014
  have freeVariableCertificate2 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0016 :=
    @gElint2 y (.cv x) A freeVariableCertificate2
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) p0000
  have p0017 :=
    @gElcompl (.cv x) (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A))
      p0000
  have p0018_e01_recanon :
    Nominal.NPrf (synWb (.classMem (.cv x) (synCint A)) (synWral y A (.objMem x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCint synWral
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0018 :=
    @gN3bitr4i (synWral y A (.objMem x y))
      (.neg (.classMem (.cv x) (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A))))
      (.classMem (.cv x) (synCint A))
      (.classMem (.cv x)
        (synCcompl (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A))))
      p0015 p0018_e01_recanon p0017
  have freeVariableCertificate3 :
    x ∉
      ((synCcompl (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0019 :=
    @gEqriv x (synCint A)
      (synCcompl (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A)))
      (by
        exact
          (show x ∉ ((synCint A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate3 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_intexg`. -/
@[expose]
noncomputable def gIntexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCint A) (synCvv))) :=
  by
  have p0000 := @gDfint3 A
  have p0001 := @gSsetkex
  have p0002 := @gComplex (synCssetk) p0001
  have p0003 := @gCnvkex (synCcompl (synCssetk)) p0002
  have p0004 := @gImakexg (synCcnvk (synCcompl (synCssetk))) A (synCvv) V
  have p0005 :=
    @gMpan (.classMem (synCcnvk (synCcompl (synCssetk))) (synCvv)) (.classMem A V)
      (.classMem (synCimak (synCcnvk (synCcompl (synCssetk))) A) (synCvv)) p0003
      p0004
  have p0006 := @gUni1exg (synCimak (synCcnvk (synCcompl (synCssetk))) A) (synCvv)
  have p0007 :=
    @gComplexg (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A)) (synCvv)
  have p0008 :=
    @gN3syl (.classMem A V)
      (.classMem (synCimak (synCcnvk (synCcompl (synCssetk))) A) (synCvv))
      (.classMem (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A)) (synCvv))
      (.classMem (synCcompl (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A)))
        (synCvv))
      p0005 p0006 p0007
  have p0009 :=
    @gSyl5eqel (.classMem A V) (synCint A)
      (synCcompl (synCuni1 (synCimak (synCcnvk (synCcompl (synCssetk))) A)))
      (synCvv) p0000 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_intex`. -/
@[expose]
noncomputable def gIntex (A : Class)
    (hyp_intex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCint A) (synCvv)) :=
  by
  have p0000 := @gIntexg A (synCvv)
  have p0001 := Nominal.mp hyp_intex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_setswith`. -/
@[expose]
noncomputable def gSetswith (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.classEq (.cab x (.classMem A (.cv x)))
        (synCif (.classMem A (synCvv)) (synCimak (synCssetk) (synCsn (synCsn A)))
          (synC0))) :=
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
  have p0000 := @gSnex A
  have p0001 := @gOpkeq1 (.cv y) (synCsn A) (.cv x)
  have p0002 :=
    @gEleq1d (.classEq (.cv y) (synCsn A)) (synCopk (.cv y) (.cv x))
      (synCopk (synCsn A) (.cv x)) (synCssetk) p0001
  have freeVariableCertificate0 :
    y ∉ ((Wff.classMem (synCopk (synCsn A) (.cv x)) (synCssetk))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_not_A, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0003 :=
    @gRexsn (.classMem (synCopk (.cv y) (.cv x)) (synCssetk))
      (.classMem (synCopk (synCsn A) (.cv x)) (synCssetk)) y (synCsn A)
      (by
        exact
          (show y ∉ ((synCsn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
      freeVariableCertificate0 p0000 p0002
  have p0004 := @gVex x
  have p0005 := @gElssetkg A (.cv x) (synCvv) (synCvv)
  have p0006 :=
    @gMpan2 (.classMem A (synCvv)) (.classMem (.cv x) (synCvv))
      (synWb (.classMem (synCopk (synCsn A) (.cv x)) (synCssetk)) (.classMem A (.cv x)))
      p0004 p0005
  have p0007 :=
    @gSyl5rbb
      (synWrex y (synCsn (synCsn A)) (.classMem (synCopk (.cv y) (.cv x)) (synCssetk)))
      (.classMem (synCopk (synCsn A) (.cv x)) (synCssetk)) (.classMem A (synCvv))
      (.classMem A (.cv x)) p0003 p0006
  have freeVariableCertificate1 : x ∉ ((Wff.classMem A (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have p0008 :=
    @gAbbidv (.classMem A (synCvv)) (.classMem A (.cv x))
      (synWrex y (synCsn (synCsn A)) (.classMem (synCopk (.cv y) (.cv x)) (synCssetk)))
      x freeVariableCertificate1 p0007
  have freeVariableCertificate2 : x ∉ ((synCsn (synCsn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, dv_A_x,
      not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((synCsn (synCsn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_y_not_A,
      not_false_eq_true]
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfImak x y
      (synCssetk) (synCsn (synCsn A))
      (by
        exact
          (show x ∉ ((synCssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((synCssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate2 freeVariableCertificate3
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0010 :=
    @gSyl6eqr (.classMem A (synCvv)) (.cab x (.classMem A (.cv x)))
      (.cab x (synWrex y (synCsn (synCsn A))
          (.classMem (synCopk (.cv y) (.cv x)) (synCssetk))))
      (synCimak (synCssetk) (synCsn (synCsn A))) p0008 p0009
  have p0011 :=
    @gIftrue (.classMem A (synCvv)) (synCimak (synCssetk) (synCsn (synCsn A)))
      (synC0)
  have p0012 :=
    @gEqtr4d (.classMem A (synCvv)) (.cab x (.classMem A (.cv x)))
      (synCimak (synCssetk) (synCsn (synCsn A)))
      (synCif (.classMem A (synCvv)) (synCimak (synCssetk) (synCsn (synCsn A))) (synC0))
      p0010 p0011
  have p0013 := @gElex A (.cv x)
  have p0014 := @gCon3i (.classMem A (.cv x)) (.classMem A (synCvv)) p0013
  have freeVariableCertificate4 : x ∉ ((Wff.neg (.classMem A (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have p0015 :=
    @gAlrimiv (.neg (.classMem A (synCvv))) (.neg (.classMem A (.cv x))) x
      freeVariableCertificate4 p0014
  have p0016 := @gAb0 (.classMem A (.cv x)) x
  have p0017 :=
    @gSylibr (.neg (.classMem A (synCvv))) (.all x (.neg (.classMem A (.cv x))))
      (.classEq (.cab x (.classMem A (.cv x))) (synC0)) p0015 p0016
  have p0018 :=
    @gIffalse (.classMem A (synCvv)) (synCimak (synCssetk) (synCsn (synCsn A)))
      (synC0)
  have p0019 :=
    @gEqtr4d (.neg (.classMem A (synCvv))) (.cab x (.classMem A (.cv x))) (synC0)
      (synCif (.classMem A (synCvv)) (synCimak (synCssetk) (synCsn (synCsn A))) (synC0))
      p0017 p0018
  have p0020 :=
    @gPm261i (.classMem A (synCvv))
      (.classEq (.cab x (.classMem A (.cv x)))
        (synCif (.classMem A (synCvv)) (synCimak (synCssetk) (synCsn (synCsn A)))
          (synC0)))
      p0012 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_setswithex`. -/
@[expose]
noncomputable def gSetswithex (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classMem (.cab x (.classMem A (.cv x))) (synCvv)) :=
  by
  have p0000 := @gSetswith x A (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
  have p0001 := @gSsetkex
  have p0002 := @gSnex (synCsn A)
  have p0003 := @gImakex (synCssetk) (synCsn (synCsn A)) p0001 p0002
  have p0004 := @gN0ex
  have p0005 :=
    @gIfex (.classMem A (synCvv)) (synCimak (synCssetk) (synCsn (synCsn A)))
      (synC0) p0003 p0004
  have p0006 :=
    @gEqeltri (.cab x (.classMem A (.cv x)))
      (synCif (.classMem A (synCvv)) (synCimak (synCssetk) (synCsn (synCsn A))) (synC0))
      (synCvv) p0000 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ndisjrelk`. -/
@[expose]
noncomputable def gNdisjrelk (A : Class) (B : Class)
    (hyp_ndisjrelk_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_ndisjrelk_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk A B)
          (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))) (synWne (synCin A B) (synC0))) :=
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
  have p0000 := @gSnex (synCsn (synCsn (.cv x)))
  have p0001 := @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B)
  have p0002 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (.cv t) (synCopk A B))
      (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) p0001
  have freeVariableCertificate0 : t ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate1 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_x, fresh_t_not_A,
      fresh_t_not_B, or_false, not_false_eq_true]
  have p0003 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk A B))
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))
      t (synCsn (synCsn (synCsn (.cv x)))) freeVariableCertificate0
      freeVariableCertificate1 p0000 p0002
  have p0004 :=
    @gElin (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
      (synCins3k (synCssetk)) (synCins2k (synCssetk))
  have p0005 := @gSnex (.cv x)
  have p0006 :=
    @gOtkelins3k (synCsn (.cv x)) A B (synCssetk) p0005 hyp_ndisjrelk_1 hyp_ndisjrelk_2
  have p0007 := @gVex x
  have p0008 := @gElssetk (.cv x) A p0007 hyp_ndisjrelk_1
  have p0009 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCins3k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) A) (synCssetk)) (.classMem (.cv x) A) p0006
      p0008
  have p0010 :=
    @gOtkelins2k (synCsn (.cv x)) A B (synCssetk) p0005 hyp_ndisjrelk_1 hyp_ndisjrelk_2
  have p0011 := @gElssetk (.cv x) B p0007 hyp_ndisjrelk_2
  have p0012 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) B) (synCssetk)) (.classMem (.cv x) B) p0010
      p0011
  have p0013 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCins3k (synCssetk)))
      (.classMem (.cv x) A)
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCins2k (synCssetk)))
      (.classMem (.cv x) B) p0009 p0012
  have p0014 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))
      (synWa (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
          (synCins3k (synCssetk)))
        (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
          (synCins2k (synCssetk))))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) p0004 p0013
  have p0015 :=
    @gBitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk A B))
            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) p0003 p0014
  have p0016 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk A B))
            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0015
  have p0017 := @gOpkex A B
  have freeVariableCertificate2 :
    t ∉ ((synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate3 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate4 : t ∉ ((synCopk A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true]
  have p0018 :=
    @gElimak t (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) (synCopk A B) freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4 p0017
  have freeVariableCertificate5 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0019 := @gElpw121c x (.cv t) freeVariableCertificate5
  have p0020 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
      (.classMem (synCopk (.cv t) (synCopk A B))
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))
      p0019
  have freeVariableCertificate6 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk A B))
          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_t, fresh_x_not_A,
      fresh_x_not_B, or_false, not_false_eq_true]
  have p0021 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (.classMem (synCopk (.cv t) (synCopk A B))
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))
      x freeVariableCertificate6
  have p0022 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk A B))
          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))))
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
        (.classMem (synCopk (.cv t) (synCopk A B))
          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk A B))
            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))))
      p0020 p0021
  have p0023 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk A B))
          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk A B))
            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))))
      t p0022
  have p0024 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk A B))
          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))))
  have p0025 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
        (.classMem (synCopk (.cv t) (synCopk A B))
          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))))
      x t
  have p0026 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk A B))
            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))))))
      (synWex t (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk A B))
              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))))))
      (synWrex t (synCpw1 (synCpw1 (synC1c))) (.classMem (synCopk (.cv t) (synCopk A B))
          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk A B))
              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))))))
      p0023 p0024 p0025
  have p0027 :=
    @gBitri
      (.classMem (synCopk A B)
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c))) (.classMem (synCopk (.cv t) (synCopk A B))
          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk A B))
              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))))))
      p0018 p0026
  have freeVariableCertificate7 : x ∉ ((synCin A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0028 := @gN0 x (synCin A B) freeVariableCertificate7
  have p0029 := @gElin (.cv x) A B
  have p0030 :=
    @gExbii (.classMem (.cv x) (synCin A B))
      (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0029
  have p0031 :=
    @gBitri (synWne (synCin A B) (synC0))
      (synWex x (.classMem (.cv x) (synCin A B)))
      (synWex x (synWa (.classMem (.cv x) A) (.classMem (.cv x) B))) p0028 p0030
  have p0032 :=
    @gN3bitr4i
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk A B))
              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))))))
      (synWex x (synWa (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.classMem (synCopk A B)
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWne (synCin A B) (synC0)) p0016 p0027 p0031
  exact p0032

/-- Checked nominal proof certificate identified upstream as `g_abexv`. -/
@[expose]
noncomputable def gAbexv (ph : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (.classMem (.cab x ph) (synCvv)) :=
  by
  have p0000 := @gAbvor0 ph x (by exact (show x ∉ (ph).fv from (by exact dv_ph_x)))
  have p0001 := @gVvex
  have p0002 := @gEleq1 (.cab x ph) (synCvv) (synCvv)
  have p0003 :=
    @gMpbiri (.classEq (.cab x ph) (synCvv)) (.classMem (.cab x ph) (synCvv))
      (.classMem (synCvv) (synCvv)) p0001 p0002
  have p0004 := @gN0ex
  have p0005 := @gEleq1 (.cab x ph) (synC0) (synCvv)
  have p0006 :=
    @gMpbiri (.classEq (.cab x ph) (synC0)) (.classMem (.cab x ph) (synCvv))
      (.classMem (synC0) (synCvv)) p0004 p0005
  have p0007 :=
    @gJaoi (.classEq (.cab x ph) (synCvv)) (.classMem (.cab x ph) (synCvv))
      (.classEq (.cab x ph) (synC0)) p0003 p0006
  have p0008 := Nominal.mp p0000 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_unipw1`. -/
@[expose]
noncomputable def gUnipw1 (A : Class) :
    Nominal.NPrf (.classEq (synCuni (synCpw1 A)) A) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
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
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0000 :=
    @gEluni y (.cv x) (synCpw1 A) freeVariableCertificate0
      (by
        exact
          (show y ∉ ((synCpw1 A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
  have freeVariableCertificate1 : z ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_y, not_false_eq_true]
  have p0001 :=
    @gElpw1 z (.cv y) A freeVariableCertificate1
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
  have p0002 :=
    @gAnbi1i (.classMem (.cv y) (synCpw1 A))
      (synWrex z A (.classEq (.cv y) (synCsn (.cv z)))) (.objMem x y) p0001
  have p0003 := @gAncom (.objMem x y) (.classMem (.cv y) (synCpw1 A))
  have freeVariableCertificate2 : z ∉ ((Wff.objMem x y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_insert,
      Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have p0004 :=
    @gR1941v (.classEq (.cv y) (synCsn (.cv z))) (.objMem x y) z A
      freeVariableCertificate2
  have p0005 :=
    @gN3bitr4i (synWa (.classMem (.cv y) (synCpw1 A)) (.objMem x y))
      (synWa (synWrex z A (.classEq (.cv y) (synCsn (.cv z)))) (.objMem x y))
      (synWa (.objMem x y) (.classMem (.cv y) (synCpw1 A)))
      (synWrex z A (synWa (.classEq (.cv y) (synCsn (.cv z))) (.objMem x y))) p0002
      p0003 p0004
  have p0006 :=
    @gExbii (synWa (.objMem x y) (.classMem (.cv y) (synCpw1 A)))
      (synWrex z A (synWa (.classEq (.cv y) (synCsn (.cv z))) (.objMem x y))) y p0005
  have freeVariableCertificate3 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have p0007 :=
    @gRisset z (.cv x) A freeVariableCertificate3
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
  have p0008 := @gSnex (.cv z)
  have p0009 := @gEleq2 (.cv y) (synCsn (.cv z)) (.cv x)
  have p0010_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (synCsn (.cv z)))
        (synWb (.objMem x y) (.classMem (.cv x) (synCsn (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn synWb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0009
  have freeVariableCertificate4 : y ∉ ((synCsn (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_z,
      not_false_eq_true]
  have freeVariableCertificate5 : y ∉ ((Wff.classMem (.cv x) (synCsn (.cv z)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, or_false, not_false_eq_true]
  have p0010 :=
    @gCeqsexv (.objMem x y) (.classMem (.cv x) (synCsn (.cv z))) y (synCsn (.cv z))
      freeVariableCertificate4 freeVariableCertificate5 p0008 p0010_e01_recanon
  have freeVariableCertificate6 : x ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_z, not_false_eq_true]
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn x (.cv z)
      freeVariableCertificate6
  have p0012_e00_recanon :
    Nominal.NPrf (.classEq (synCsn (.cv z)) (.cab x (.objEq x z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0011
  have p0012 := @gEqabri (.objEq x z) x (synCsn (.cv z)) p0012_e00_recanon
  have p0013 := @gEqucom x z
  have p0014 :=
    @gN3bitri (synWex y (synWa (.classEq (.cv y) (synCsn (.cv z))) (.objMem x y)))
      (.classMem (.cv x) (synCsn (.cv z))) (.objEq x z) (.objEq z x) p0010 p0012 p0013
  have p0015 :=
    @gRexbii (synWex y (synWa (.classEq (.cv y) (synCsn (.cv z))) (.objMem x y)))
      (.objEq z x) z A p0014
  have p0016 :=
    @gRexcom4 (synWa (.classEq (.cv y) (synCsn (.cv z))) (.objMem x y)) z y A
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (show z ≠ y from (by exact fresh_z_ne_y))
  have p0017_e00_recanon :
    Nominal.NPrf (synWb (.classMem (.cv x) A) (synWrex z A (.objEq z x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0017 :=
    @gN3bitr2ri (.classMem (.cv x) A) (synWrex z A (.objEq z x))
      (synWrex z A (synWex y (synWa (.classEq (.cv y) (synCsn (.cv z))) (.objMem x y))))
      (synWex y (synWrex z A (synWa (.classEq (.cv y) (synCsn (.cv z))) (.objMem x y))))
      p0017_e00_recanon p0015 p0016
  have p0018_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv x) (synCuni (synCpw1 A)))
        (synWex y (synWa (.objMem x y) (.classMem (.cv y) (synCpw1 A))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCuni synWex synWa synCpw1 synCin synCcompl synCnin
          synWnan synCpw synWss synC1c
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0018 :=
    @gN3bitri (.classMem (.cv x) (synCuni (synCpw1 A)))
      (synWex y (synWa (.objMem x y) (.classMem (.cv y) (synCpw1 A))))
      (synWex y (synWrex z A (synWa (.classEq (.cv y) (synCsn (.cv z))) (.objMem x y))))
      (.classMem (.cv x) A) p0018_e00_recanon p0006 p0017
  have freeVariableCertificate7 : x ∉ ((synCuni (synCpw1 A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_A,
      not_false_eq_true]
  have p0019 :=
    @gEqriv x (synCuni (synCpw1 A)) A freeVariableCertificate7
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_pw1exb`. -/
@[expose]
noncomputable def gPw1exb (A : Class) :
    Nominal.NPrf (synWb (.classMem (synCpw1 A) (synCvv)) (.classMem A (synCvv))) :=
  by
  have p0000 := @gUnipw1 A
  have p0001 := @gUniexg (synCpw1 A) (synCvv)
  have p0002 :=
    @gSyl5eqelr (.classMem (synCpw1 A) (synCvv)) A (synCuni (synCpw1 A)) (synCvv)
      p0000 p0001
  have p0003 := @gPw1exg A (synCvv)
  have p0004 :=
    @gImpbii (.classMem (synCpw1 A) (synCvv)) (.classMem A (synCvv)) p0002 p0003
  exact p0004


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart019`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dfpw2`. -/
@[expose]
noncomputable def gDfpw2 (A : Class) :
    Nominal.NPrf
      (.classEq (synCpw A) (synCcompl
          (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c)))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
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
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have p0000 := @gVex x
  have freeVariableCertificate0 :
    t ∉ ((synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_t_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_x, not_false_eq_true]
  have p0001 :=
    @gElimak t (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c)
      (.cv x) freeVariableCertificate0
      (by
        exact
          (show t ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0000
  have freeVariableCertificate2 : y ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_t, not_false_eq_true]
  have p0002 := @gEl1c y (.cv t) freeVariableCertificate2
  have p0003 :=
    @gAnbi1i (.classMem (.cv t) (synC1c))
      (synWex y (.classEq (.cv t) (synCsn (.cv y))))
      (.classMem (synCopk (.cv t) (.cv x))
        (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))
      p0002
  have freeVariableCertificate3 :
    y ∉
      ((Wff.classMem (synCopk (.cv t) (.cv x))
          (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_t, fresh_y_ne_x,
      fresh_y_not_A, or_false, not_false_eq_true]
  have p0004 :=
    @gN1941v (.classEq (.cv t) (synCsn (.cv y)))
      (.classMem (synCopk (.cv t) (.cv x))
        (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))
      y freeVariableCertificate3
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv x))
          (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv)))))
      (synWa (synWex y (.classEq (.cv t) (synCsn (.cv y))))
        (.classMem (synCopk (.cv t) (.cv x))
          (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv)))))
      (synWex y (synWa (.classEq (.cv t) (synCsn (.cv y)))
          (.classMem (synCopk (.cv t) (.cv x))
            (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv x))
          (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv)))))
      (synWex y (synWa (.classEq (.cv t) (synCsn (.cv y)))
          (.classMem (synCopk (.cv t) (.cv x))
            (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))))
      t p0005
  have p0007 :=
    (Nominal.biimpRefl (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv x))
          (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))))
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (.cv y))) (.classMem (synCopk (.cv t) (.cv x))
          (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv)))))
      y t
  have p0009 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv x))
            (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))))
      (synWex t (synWex y (synWa (.classEq (.cv t) (synCsn (.cv y)))
            (.classMem (synCopk (.cv t) (.cv x))
              (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv)))))))
      (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv x))
          (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv)))))
      (synWex y (synWex t (synWa (.classEq (.cv t) (synCsn (.cv y)))
            (.classMem (synCopk (.cv t) (.cv x))
              (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv)))))))
      p0006 p0007 p0008
  have p0010 :=
    @gBitri
      (.classMem (.cv x)
        (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c)))
      (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv x))
          (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv)))))
      (synWex y (synWex t (synWa (.classEq (.cv t) (synCsn (.cv y)))
            (.classMem (synCopk (.cv t) (.cv x))
              (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv)))))))
      p0001 p0009
  have p0011 := @gSnex (.cv y)
  have p0012 := @gOpkeq1 (.cv t) (synCsn (.cv y)) (.cv x)
  have p0013 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv y))) (synCopk (.cv t) (.cv x))
      (synCopk (synCsn (.cv y)) (.cv x))
      (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) p0012
  have freeVariableCertificate4 : t ∉ ((synCsn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
      not_false_eq_true]
  have freeVariableCertificate5 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (.cv y)) (.cv x))
          (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_y, fresh_t_ne_x,
      fresh_t_not_A, or_false, not_false_eq_true]
  have p0014 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (.cv x))
        (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))
      (.classMem (synCopk (synCsn (.cv y)) (.cv x))
        (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))
      t (synCsn (.cv y)) freeVariableCertificate4 freeVariableCertificate5 p0011 p0013
  have p0015 :=
    @gEldif (synCopk (synCsn (.cv y)) (.cv x)) (synCssetk)
      (synCxpk (synCpw1 A) (synCvv))
  have p0016 := @gVex y
  have p0017 := @gElssetk (.cv y) (.cv x) p0016 p0000
  have p0018 := @gOpkelxpk (synCsn (.cv y)) (.cv x) (synCpw1 A) (synCvv) p0011 p0000
  have p0019 :=
    @gMpbiran2
      (.classMem (synCopk (synCsn (.cv y)) (.cv x)) (synCxpk (synCpw1 A) (synCvv)))
      (.classMem (synCsn (.cv y)) (synCpw1 A)) (.classMem (.cv x) (synCvv)) p0000 p0018
  have p0020 := @gSnelpw1 (.cv y) A
  have p0021 :=
    @gBitri
      (.classMem (synCopk (synCsn (.cv y)) (.cv x)) (synCxpk (synCpw1 A) (synCvv)))
      (.classMem (synCsn (.cv y)) (synCpw1 A)) (.classMem (.cv y) A) p0019 p0020
  have p0022 :=
    @gNotbii
      (.classMem (synCopk (synCsn (.cv y)) (.cv x)) (synCxpk (synCpw1 A) (synCvv)))
      (.classMem (.cv y) A) p0021
  have p0023_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv y)) (.cv x)) (synCssetk)) (.objMem y x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0017
  have p0023 :=
    @gAnbi12i (.classMem (synCopk (synCsn (.cv y)) (.cv x)) (synCssetk)) (.objMem y x)
      (.neg (.classMem (synCopk (synCsn (.cv y)) (.cv x)) (synCxpk (synCpw1 A) (synCvv))))
      (.neg (.classMem (.cv y) A)) p0023_e00_recanon p0022
  have p0024 := @gAnnim (.objMem y x) (.classMem (.cv y) A)
  have p0025 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (.cv y)) (.cv x))
        (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))
      (synWa (.classMem (synCopk (synCsn (.cv y)) (.cv x)) (synCssetk)) (.neg
          (.classMem (synCopk (synCsn (.cv y)) (.cv x)) (synCxpk (synCpw1 A) (synCvv)))))
      (synWa (.objMem y x) (.neg (.classMem (.cv y) A)))
      (.neg (.imp (.objMem y x) (.classMem (.cv y) A))) p0015 p0023 p0024
  have p0026 :=
    @gBitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv y)))
          (.classMem (synCopk (.cv t) (.cv x))
            (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))))
      (.classMem (synCopk (synCsn (.cv y)) (.cv x))
        (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))
      (.neg (.imp (.objMem y x) (.classMem (.cv y) A))) p0014 p0025
  have p0027 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv y)))
          (.classMem (synCopk (.cv t) (.cv x))
            (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))))))
      (.neg (.imp (.objMem y x) (.classMem (.cv y) A))) y p0026
  have p0028 := @gExnal (.imp (.objMem y x) (.classMem (.cv y) A)) y
  have p0029 :=
    @gN3bitri
      (.classMem (.cv x)
        (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c)))
      (synWex y (synWex t (synWa (.classEq (.cv t) (synCsn (.cv y)))
            (.classMem (synCopk (.cv t) (.cv x))
              (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv)))))))
      (synWex y (.neg (.imp (.objMem y x) (.classMem (.cv y) A))))
      (.neg (.all y (.imp (.objMem y x) (.classMem (.cv y) A)))) p0010 p0027 p0028
  have p0030 :=
    @gCon2bii
      (.classMem (.cv x)
        (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c)))
      (.all y (.imp (.objMem y x) (.classMem (.cv y) A))) p0029
  have p0031 := @gElpw (.cv x) A p0000
  have freeVariableCertificate6 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0032 :=
    @gDfss2 y (.cv x) A freeVariableCertificate6
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0033_e01_recanon :
    Nominal.NPrf
      (synWb (synWss (.cv x) A) (.all y (.imp (.objMem y x) (.classMem (.cv y) A)))) :=
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
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0032
  have p0033 :=
    @gBitri (.classMem (.cv x) (synCpw A)) (synWss (.cv x) A)
      (.all y (.imp (.objMem y x) (.classMem (.cv y) A))) p0031 p0033_e01_recanon
  have p0034 :=
    @gElcompl (.cv x)
      (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c))
      p0000
  have p0035 :=
    @gN3bitr4i (.all y (.imp (.objMem y x) (.classMem (.cv y) A)))
      (.neg (.classMem (.cv x)
          (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c))))
      (.classMem (.cv x) (synCpw A))
      (.classMem (.cv x) (synCcompl
          (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c))))
      p0030 p0033 p0034
  have freeVariableCertificate7 :
    x ∉
      ((synCcompl (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv)))
            (synC1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0036 :=
    @gEqriv x (synCpw A)
      (synCcompl
        (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c)))
      (by
        exact
          (show x ∉ ((synCpw A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate7 p0035
  exact p0036

/-- Checked nominal proof certificate identified upstream as `g_pwexg`. -/
@[expose]
noncomputable def gPwexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCpw A) (synCvv))) :=
  by
  have p0000 := @gDfpw2 A
  have p0001 := @gSsetkex
  have p0002 := @gPw1exg A V
  have p0003 := @gVvex
  have p0004 := @gXpkexg (synCpw1 A) (synCvv) (synCvv) (synCvv)
  have p0005 :=
    @gSylancl (.classMem A V) (.classMem (synCpw1 A) (synCvv))
      (.classMem (synCvv) (synCvv))
      (.classMem (synCxpk (synCpw1 A) (synCvv)) (synCvv)) p0002 p0003 p0004
  have p0006 :=
    @gDifexg (synCssetk) (synCxpk (synCpw1 A) (synCvv)) (synCvv) (synCvv)
  have p0007 :=
    @gSylancr (.classMem A V) (.classMem (synCssetk) (synCvv))
      (.classMem (synCxpk (synCpw1 A) (synCvv)) (synCvv))
      (.classMem (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synCvv))
      p0001 p0005 p0006
  have p0008 := @gN1cex
  have p0009 :=
    @gImakexg (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c)
      (synCvv) (synCvv)
  have p0010 :=
    @gSylancl (.classMem A V)
      (.classMem (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synCvv))
      (.classMem (synC1c) (synCvv))
      (.classMem (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c))
        (synCvv))
      p0007 p0008 p0009
  have p0011 :=
    @gComplexg
      (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c))
      (synCvv)
  have p0012 :=
    @gSyl (.classMem A V)
      (.classMem (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c))
        (synCvv))
      (.classMem (synCcompl
          (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c)))
        (synCvv))
      p0010 p0011
  have p0013 :=
    @gSyl5eqel (.classMem A V) (synCpw A)
      (synCcompl
        (synCimak (synCdif (synCssetk) (synCxpk (synCpw1 A) (synCvv))) (synC1c)))
      (synCvv) p0000 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_pwex`. -/
@[expose]
noncomputable def gPwex (A : Class) (hyp_pwex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCpw A) (synCvv)) :=
  by
  have p0000 := @gPwexg A (synCvv)
  have p0001 := Nominal.mp hyp_pwex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_eqpw1uni`. -/
@[expose]
noncomputable def gEqpw1uni (A : Class) :
    Nominal.NPrf (.imp (synWss A (synC1c)) (.classEq A (synCpw1 (synCuni A)))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
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
  have p0000 := @gSsel A (synC1c) (.cv x)
  have p0001 := @gPw1ss1c (synCuni A)
  have p0002 := @gSseli (synCpw1 (synCuni A)) (synC1c) (.cv x) p0001
  have p0003 :=
    @gA1i
      (.imp (.classMem (.cv x) (synCpw1 (synCuni A))) (.classMem (.cv x) (synC1c)))
      (synWss A (synC1c)) p0002
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0004 := @gEl1c y (.cv x) freeVariableCertificate0
  have p0005 := @gVex y
  have p0006 := @gSnid (.cv y) p0005
  have p0007 := @gEleq2 (.cv x) (synCsn (.cv y)) (.cv y)
  have p0008_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (synCsn (.cv y)))
        (synWb (.objMem y x) (.classMem (.cv y) (synCsn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn synWb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0007
  have freeVariableCertificate1 : x ∉ ((synCsn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_y,
      not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Wff.classMem (.cv y) (synCsn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_y, or_false, not_false_eq_true]
  have p0008 :=
    @gRspcev (.objMem y x) (.classMem (.cv y) (synCsn (.cv y))) x (synCsn (.cv y)) A
      freeVariableCertificate1 (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate2 p0008_e00_recanon
  have p0009 :=
    @gMpan2 (.classMem (synCsn (.cv y)) A) (.classMem (.cv y) (synCsn (.cv y)))
      (synWrex x A (.objMem y x)) p0006 p0008
  have freeVariableCertificate3 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have p0010 := @gEl1c z (.cv x) freeVariableCertificate3
  have freeVariableCertificate4 : y ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_z, not_false_eq_true]
  have p0011 := @gElsn y (.cv z) freeVariableCertificate4
  have p0012 := @gSneq (.cv y) (.cv z)
  have p0013_e00_recanon :
    Nominal.NPrf (.imp (.objEq y z) (.classEq (synCsn (.cv y)) (synCsn (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0013 :=
    @gEleq1d (.objEq y z) (synCsn (.cv y)) (synCsn (.cv z)) A p0013_e00_recanon
  have p0014_e00_recanon :
    Nominal.NPrf (synWb (.classMem (.cv y) (synCsn (.cv z))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0014 :=
    @gSylbi (.classMem (.cv y) (synCsn (.cv z))) (.objEq y z)
      (synWb (.classMem (synCsn (.cv y)) A) (.classMem (synCsn (.cv z)) A))
      p0014_e00_recanon p0013
  have p0015 :=
    @gBiimprcd (.classMem (.cv y) (synCsn (.cv z))) (.classMem (synCsn (.cv y)) A)
      (.classMem (synCsn (.cv z)) A) p0014
  have p0016 := @gEleq1 (.cv x) (synCsn (.cv z)) A
  have p0017 := @gEleq2 (.cv x) (synCsn (.cv z)) (.cv y)
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (synCsn (.cv z)))
        (synWb (.objMem y x) (.classMem (.cv y) (synCsn (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn synWb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0017
  have p0018 :=
    @gImbi1d (.classEq (.cv x) (synCsn (.cv z))) (.objMem y x)
      (.classMem (.cv y) (synCsn (.cv z))) (.classMem (synCsn (.cv y)) A)
      p0018_e00_recanon
  have p0019 :=
    @gImbi12d (.classEq (.cv x) (synCsn (.cv z))) (.classMem (.cv x) A)
      (.classMem (synCsn (.cv z)) A) (.imp (.objMem y x) (.classMem (synCsn (.cv y)) A))
      (.imp (.classMem (.cv y) (synCsn (.cv z))) (.classMem (synCsn (.cv y)) A)) p0016
      p0018
  have p0020 :=
    @gMpbiri (.classEq (.cv x) (synCsn (.cv z)))
      (.imp (.classMem (.cv x) A) (.imp (.objMem y x) (.classMem (synCsn (.cv y)) A)))
      (.imp (.classMem (synCsn (.cv z)) A)
        (.imp (.classMem (.cv y) (synCsn (.cv z))) (.classMem (synCsn (.cv y)) A)))
      p0015 p0019
  have freeVariableCertificate5 :
    z ∉
      ((Wff.imp (.classMem (.cv x) A)
          (.imp (.objMem y x) (.classMem (synCsn (.cv y)) A)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, fresh_z_ne_y,
      or_false, not_false_eq_true]
  have p0021 :=
    @gExlimiv (.classEq (.cv x) (synCsn (.cv z)))
      (.imp (.classMem (.cv x) A) (.imp (.objMem y x) (.classMem (synCsn (.cv y)) A))) z
      freeVariableCertificate5 p0020
  have p0022 :=
    @gSylbi (.classMem (.cv x) (synC1c))
      (synWex z (.classEq (.cv x) (synCsn (.cv z))))
      (.imp (.classMem (.cv x) A) (.imp (.objMem y x) (.classMem (synCsn (.cv y)) A)))
      p0010 p0021
  have p0023 :=
    @gSyli (.classMem (.cv x) A) (synWss A (synC1c)) (.classMem (.cv x) (synC1c))
      (.imp (.objMem y x) (.classMem (synCsn (.cv y)) A)) p0000 p0022
  have freeVariableCertificate6 : x ∉ ((Wff.classMem (synCsn (.cv y)) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_y, fresh_x_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate7 : x ∉ ((synWss A (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0024 :=
    @gRexlimdv (synWss A (synC1c)) (.objMem y x) (.classMem (synCsn (.cv y)) A) x A
      freeVariableCertificate6 freeVariableCertificate7 p0023
  have p0025 :=
    @gImpbid2 (synWss A (synC1c)) (.classMem (synCsn (.cv y)) A)
      (synWrex x A (.objMem y x)) p0009 p0024
  have freeVariableCertificate8 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0026 :=
    @gEluni2 x (.cv y) A freeVariableCertificate8
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0027_e01_recanon :
    Nominal.NPrf (synWb (.classMem (.cv y) (synCuni A)) (synWrex x A (.objMem y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCuni synWex synWa synWrex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
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
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0027 :=
    @gSyl6bbr (synWss A (synC1c)) (.classMem (synCsn (.cv y)) A)
      (synWrex x A (.objMem y x)) (.classMem (.cv y) (synCuni A)) p0025
      p0027_e01_recanon
  have p0028 := @gEleq1 (.cv x) (synCsn (.cv y)) A
  have p0029 := @gEleq1 (.cv x) (synCsn (.cv y)) (synCpw1 (synCuni A))
  have p0030 := @gSnelpw1 (.cv y) (synCuni A)
  have p0031 :=
    @gSyl6bb (.classEq (.cv x) (synCsn (.cv y)))
      (.classMem (.cv x) (synCpw1 (synCuni A)))
      (.classMem (synCsn (.cv y)) (synCpw1 (synCuni A)))
      (.classMem (.cv y) (synCuni A)) p0029 p0030
  have p0032 :=
    @gBibi12d (.classEq (.cv x) (synCsn (.cv y))) (.classMem (.cv x) A)
      (.classMem (synCsn (.cv y)) A) (.classMem (.cv x) (synCpw1 (synCuni A)))
      (.classMem (.cv y) (synCuni A)) p0028 p0031
  have p0033 :=
    @gSyl5ibrcom (synWss A (synC1c))
      (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCpw1 (synCuni A))))
      (.classEq (.cv x) (synCsn (.cv y)))
      (synWb (.classMem (synCsn (.cv y)) A) (.classMem (.cv y) (synCuni A))) p0027
      p0032
  have freeVariableCertificate9 :
    y ∉ ((synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCpw1 (synCuni A))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate10 : y ∉ ((synWss A (synC1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_A, or_false, not_false_eq_true]
  have p0034 :=
    @gExlimdv (synWss A (synC1c)) (.classEq (.cv x) (synCsn (.cv y)))
      (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCpw1 (synCuni A)))) y
      freeVariableCertificate9 freeVariableCertificate10 p0033
  have p0035 :=
    @gSyl5bi (.classMem (.cv x) (synC1c))
      (synWex y (.classEq (.cv x) (synCsn (.cv y)))) (synWss A (synC1c))
      (synWb (.classMem (.cv x) A) (.classMem (.cv x) (synCpw1 (synCuni A)))) p0004
      p0034
  have p0036 :=
    @gPm521ndd (synWss A (synC1c)) (.classMem (.cv x) (synC1c)) (.classMem (.cv x) A)
      (.classMem (.cv x) (synCpw1 (synCuni A))) p0000 p0003 p0035
  have freeVariableCertificate11 : x ∉ ((synCpw1 (synCuni A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_x_not_A,
      not_false_eq_true]
  have p0037 :=
    @gEqrdv (synWss A (synC1c)) x A (synCpw1 (synCuni A))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate11
      freeVariableCertificate7 p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_pw1equn`. -/
@[expose]
noncomputable def gPw1equn (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y)
    (hyp_pw1equn_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_pw1equn_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classEq (synCpw1 C) (synCun A B)) (synWex x (synWex y
            (synW3a (.classEq C (synCun (.cv x) (.cv y)))
              (.classEq A (synCpw1 (.cv x))) (.classEq B (synCpw1 (.cv y))))))) :=
  by
  have p0000 := @gUnipw1 C
  have p0001 := @gUnieq (synCpw1 C) (synCun A B)
  have p0002 :=
    @gSyl5eqr (.classEq (synCpw1 C) (synCun A B)) C (synCuni (synCpw1 C))
      (synCuni (synCun A B)) p0000 p0001
  have p0003 := @gSsun1 A B
  have p0004 := @gSseq2 (synCpw1 C) (synCun A B) A
  have p0005 :=
    @gMpbiri (.classEq (synCpw1 C) (synCun A B)) (synWss A (synCpw1 C))
      (synWss A (synCun A B)) p0003 p0004
  have p0006 := @gPw1ss1c C
  have p0007 :=
    @gSyl6ss (.classEq (synCpw1 C) (synCun A B)) A (synCpw1 C) (synC1c) p0005 p0006
  have p0008 := @gEqpw1uni A
  have p0009 :=
    @gSyl (.classEq (synCpw1 C) (synCun A B)) (synWss A (synC1c))
      (.classEq A (synCpw1 (synCuni A))) p0007 p0008
  have p0010 := @gSsun2 B A
  have p0011 := @gSseq2 (synCpw1 C) (synCun A B) B
  have p0012 :=
    @gMpbiri (.classEq (synCpw1 C) (synCun A B)) (synWss B (synCpw1 C))
      (synWss B (synCun A B)) p0010 p0011
  have p0013 :=
    @gSyl6ss (.classEq (synCpw1 C) (synCun A B)) B (synCpw1 C) (synC1c) p0012 p0006
  have p0014 := @gEqpw1uni B
  have p0015 :=
    @gSyl (.classEq (synCpw1 C) (synCun A B)) (synWss B (synC1c))
      (.classEq B (synCpw1 (synCuni B))) p0013 p0014
  have p0016 := @gUniex A hyp_pw1equn_1
  have p0017 := @gUniex B hyp_pw1equn_2
  have p0018 := @gUneq12 (.cv x) (synCuni A) (.cv y) (synCuni B)
  have p0019 := @gUniun A B
  have p0020 :=
    @gSyl6eqr (synWa (.classEq (.cv x) (synCuni A)) (.classEq (.cv y) (synCuni B)))
      (synCun (.cv x) (.cv y)) (synCun (synCuni A) (synCuni B))
      (synCuni (synCun A B)) p0018 p0019
  have p0021 :=
    @gEqeq2d (synWa (.classEq (.cv x) (synCuni A)) (.classEq (.cv y) (synCuni B)))
      (synCun (.cv x) (.cv y)) (synCuni (synCun A B)) C p0020
  have p0022 := @gPw1eq (.cv x) (synCuni A)
  have p0023 :=
    @gEqeq2d (.classEq (.cv x) (synCuni A)) (synCpw1 (.cv x)) (synCpw1 (synCuni A)) A
      p0022
  have p0024 :=
    @gAdantr (.classEq (.cv x) (synCuni A))
      (synWb (.classEq A (synCpw1 (.cv x))) (.classEq A (synCpw1 (synCuni A))))
      (.classEq (.cv y) (synCuni B)) p0023
  have p0025 := @gPw1eq (.cv y) (synCuni B)
  have p0026 :=
    @gEqeq2d (.classEq (.cv y) (synCuni B)) (synCpw1 (.cv y)) (synCpw1 (synCuni B)) B
      p0025
  have p0027 :=
    @gAdantl (.classEq (.cv y) (synCuni B))
      (synWb (.classEq B (synCpw1 (.cv y))) (.classEq B (synCpw1 (synCuni B))))
      (.classEq (.cv x) (synCuni A)) p0026
  have p0028 :=
    @gN3anbi123d
      (synWa (.classEq (.cv x) (synCuni A)) (.classEq (.cv y) (synCuni B)))
      (.classEq C (synCun (.cv x) (.cv y))) (.classEq C (synCuni (synCun A B)))
      (.classEq A (synCpw1 (.cv x))) (.classEq A (synCpw1 (synCuni A)))
      (.classEq B (synCpw1 (.cv y))) (.classEq B (synCpw1 (synCuni B))) p0021 p0024
      p0027
  have freeVariableCertificate0 :
    x ∉
      ((synW3a (.classEq C (synCuni (synCun A B))) (.classEq A (synCpw1 (synCuni A)))
          (.classEq B (synCpw1 (synCuni B))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, dv_B_x,
      dv_C_x, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    y ∉
      ((synW3a (.classEq C (synCuni (synCun A B))) (.classEq A (synCpw1 (synCuni A)))
          (.classEq B (synCpw1 (synCuni B))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, dv_B_y,
      dv_C_y, dv_A_y, or_false, not_false_eq_true]
  have p0029 :=
    @gSpc2ev
      (synW3a (.classEq C (synCun (.cv x) (.cv y))) (.classEq A (synCpw1 (.cv x)))
        (.classEq B (synCpw1 (.cv y))))
      (synW3a (.classEq C (synCuni (synCun A B))) (.classEq A (synCpw1 (synCuni A)))
        (.classEq B (synCpw1 (synCuni B))))
      x y (synCuni A) (synCuni B)
      (by
        exact
          (show x ∉ ((synCuni A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
              exact (show x ∉ (A).fv from (by exact dv_A_x)))))
      (by
        exact
          (show y ∉ ((synCuni A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
              exact (show y ∉ (A).fv from (by exact dv_A_y)))))
      (by
        exact
          (show x ∉ ((synCuni B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
              exact (show x ∉ (B).fv from (by exact dv_B_x)))))
      (by
        exact
          (show y ∉ ((synCuni B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
              exact (show y ∉ (B).fv from (by exact dv_B_y)))))
      freeVariableCertificate0 freeVariableCertificate1
      (show x ≠ y from (by exact dv_x_y)) p0016 p0017 p0028
  have p0030 :=
    @gSyl3anc (.classEq (synCpw1 C) (synCun A B)) (.classEq C (synCuni (synCun A B)))
      (.classEq A (synCpw1 (synCuni A))) (.classEq B (synCpw1 (synCuni B)))
      (synWex x (synWex y
          (synW3a (.classEq C (synCun (.cv x) (.cv y))) (.classEq A (synCpw1 (.cv x)))
            (.classEq B (synCpw1 (.cv y))))))
      p0002 p0009 p0015 p0029
  have p0031 := @gPw1un (.cv x) (.cv y)
  have p0032 := @gPw1eq C (synCun (.cv x) (.cv y))
  have p0033 := @gUneq12 A (synCpw1 (.cv x)) B (synCpw1 (.cv y))
  have p0034 :=
    @gEqeqan12d (.classEq C (synCun (.cv x) (.cv y)))
      (synWa (.classEq A (synCpw1 (.cv x))) (.classEq B (synCpw1 (.cv y))))
      (synCpw1 C) (synCpw1 (synCun (.cv x) (.cv y))) (synCun A B)
      (synCun (synCpw1 (.cv x)) (synCpw1 (.cv y))) p0032 p0033
  have p0035 :=
    @gN3impb (.classEq C (synCun (.cv x) (.cv y))) (.classEq A (synCpw1 (.cv x)))
      (.classEq B (synCpw1 (.cv y)))
      (synWb (.classEq (synCpw1 C) (synCun A B))
        (.classEq (synCpw1 (synCun (.cv x) (.cv y)))
          (synCun (synCpw1 (.cv x)) (synCpw1 (.cv y)))))
      p0034
  have p0036 :=
    @gMpbiri
      (synW3a (.classEq C (synCun (.cv x) (.cv y))) (.classEq A (synCpw1 (.cv x)))
        (.classEq B (synCpw1 (.cv y))))
      (.classEq (synCpw1 C) (synCun A B))
      (.classEq (synCpw1 (synCun (.cv x) (.cv y)))
        (synCun (synCpw1 (.cv x)) (synCpw1 (.cv y))))
      p0031 p0035
  have freeVariableCertificate2 : x ∉ ((Wff.classEq (synCpw1 C) (synCun A B))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, dv_C_x,
      dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((Wff.classEq (synCpw1 C) (synCun A B))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, dv_C_y,
      dv_A_y, dv_B_y, or_false, not_false_eq_true]
  have p0037 :=
    @gExlimivv
      (synW3a (.classEq C (synCun (.cv x) (.cv y))) (.classEq A (synCpw1 (.cv x)))
        (.classEq B (synCpw1 (.cv y))))
      (.classEq (synCpw1 C) (synCun A B)) x y freeVariableCertificate2
      freeVariableCertificate3 p0036
  have p0038 :=
    @gImpbii (.classEq (synCpw1 C) (synCun A B))
      (synWex x (synWex y
          (synW3a (.classEq C (synCun (.cv x) (.cv y))) (.classEq A (synCpw1 (.cv x)))
            (.classEq B (synCpw1 (.cv y))))))
      p0030 p0037
  exact p0038


end NFChoice.DirectNominalPrf.WPPReplay

end
