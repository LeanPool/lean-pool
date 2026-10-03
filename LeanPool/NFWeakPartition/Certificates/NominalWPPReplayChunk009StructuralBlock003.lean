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

@[expose]
noncomputable def g_sikexlem (x : Var) (y : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_x_y : x ≠ y)
    (hyp_sikexlem_1 : Nominal.NPrf (syn_wss A (syn_cxpk (syn_c1c) (syn_c1c))))
    (hyp_sikexlem_2 : Nominal.NPrf (syn_wss B (syn_cxpk (syn_c1c) (syn_c1c)))) :
    Nominal.NPrf
      (syn_wb (.classEq A B) (.all x (.all y
            (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A)
              (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B))))) :=
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
  have freeVariableCertificate0 : z ∉ ((syn_cxpk (syn_c1c) (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0000 :=
    @g_ssofeq z A B (syn_cxpk (syn_c1c) (syn_c1c))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B))) freeVariableCertificate0
  have p0001 :=
    @g_mp2an (syn_wss A (syn_cxpk (syn_c1c) (syn_c1c)))
      (syn_wss B (syn_cxpk (syn_c1c) (syn_c1c)))
      (syn_wb (.classEq A B) (syn_wral z (syn_cxpk (syn_c1c) (syn_c1c))
          (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      hyp_sikexlem_1 hyp_sikexlem_2 p0000
  have p0002 :=
    (Nominal.biimpRefl (syn_wral z (syn_cxpk (syn_c1c) (syn_c1c))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))
  have freeVariableCertificate1 : w ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_z, not_false_eq_true]
  have freeVariableCertificate2 : t ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_z, not_false_eq_true]
  have p0003 :=
    @g_elxpk w t (.cv z) (syn_c1c) (syn_c1c) freeVariableCertificate1
      freeVariableCertificate2
      (by
        exact
          (show w ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show t ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show w ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show t ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (show w ≠ t from (by exact fresh_w_ne_t))
  have freeVariableCertificate3 : x ∉ ((Class.cv w)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_w, not_false_eq_true]
  have p0004 := @g_el1c x (.cv w) freeVariableCertificate3
  have freeVariableCertificate4 : y ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_t, not_false_eq_true]
  have p0005 := @g_el1c y (.cv t) freeVariableCertificate4
  have p0006 :=
    @g_anbi12i (.classMem (.cv w) (syn_c1c))
      (syn_wex x (.classEq (.cv w) (syn_csn (.cv x)))) (.classMem (.cv t) (syn_c1c))
      (syn_wex y (.classEq (.cv t) (syn_csn (.cv y)))) p0004 p0005
  have freeVariableCertificate5 : y ∉ ((Wff.classEq (.cv w) (syn_csn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_w, (Ne.symm dv_x_y), or_false, not_false_eq_true]
  have freeVariableCertificate6 : x ∉ ((Wff.classEq (.cv t) (syn_csn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_t, dv_x_y, or_false, not_false_eq_true]
  have p0007 :=
    @g_eeanv (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))) x y
      freeVariableCertificate5 freeVariableCertificate6
  have p0008 :=
    @g_bitr4i (syn_wa (.classMem (.cv w) (syn_c1c)) (.classMem (.cv t) (syn_c1c)))
      (syn_wa (syn_wex x (.classEq (.cv w) (syn_csn (.cv x))))
        (syn_wex y (.classEq (.cv t) (syn_csn (.cv y)))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_csn (.cv x)))
            (.classEq (.cv t) (syn_csn (.cv y))))))
      p0006 p0007
  have p0009 :=
    @g_anbi2i (syn_wa (.classMem (.cv w) (syn_c1c)) (.classMem (.cv t) (syn_c1c)))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv w) (syn_csn (.cv x)))
            (.classEq (.cv t) (syn_csn (.cv y))))))
      (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) p0008
  have p0010 :=
    (Nominal.biimpRefl
      (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y)))
        (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))))
  have p0011 :=
    @g_ancom
      (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))))
      (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))
  have p0012 :=
    @g_bitri
      (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y)))
        (.classEq (.cv z) (syn_copk (.cv w) (.cv t))))
      (syn_wa (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y))))
        (.classEq (.cv z) (syn_copk (.cv w) (.cv t))))
      (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))
        (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y)))))
      p0010 p0011
  have p0013 :=
    @g_n_2exbii
      (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y)))
        (.classEq (.cv z) (syn_copk (.cv w) (.cv t))))
      (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))
        (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y)))))
      x y p0012
  have freeVariableCertificate7 :
    x ∉ ((Wff.classEq (.cv z) (syn_copk (.cv w) (.cv t)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_w, fresh_x_ne_t, or_false,
      not_false_eq_true]
  have freeVariableCertificate8 :
    y ∉ ((Wff.classEq (.cv z) (syn_copk (.cv w) (.cv t)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_w, fresh_y_ne_t, or_false,
      not_false_eq_true]
  have p0014 :=
    @g_n_19_42vv (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))
      (syn_wa (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y)))) x
      y freeVariableCertificate7 freeVariableCertificate8
  have p0015 :=
    @g_bitri
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv w) (syn_csn (.cv x)))
            (.classEq (.cv t) (syn_csn (.cv y)))
            (.classEq (.cv z) (syn_copk (.cv w) (.cv t))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))
            (syn_wa (.classEq (.cv w) (syn_csn (.cv x)))
              (.classEq (.cv t) (syn_csn (.cv y)))))))
      (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (syn_wex x (syn_wex y
            (syn_wa (.classEq (.cv w) (syn_csn (.cv x)))
              (.classEq (.cv t) (syn_csn (.cv y)))))))
      p0013 p0014
  have p0016 :=
    @g_bitr4i
      (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))
        (syn_wa (.classMem (.cv w) (syn_c1c)) (.classMem (.cv t) (syn_c1c))))
      (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t))) (syn_wex x (syn_wex y
            (syn_wa (.classEq (.cv w) (syn_csn (.cv x)))
              (.classEq (.cv t) (syn_csn (.cv y)))))))
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv w) (syn_csn (.cv x)))
            (.classEq (.cv t) (syn_csn (.cv y)))
            (.classEq (.cv z) (syn_copk (.cv w) (.cv t))))))
      p0009 p0015
  have p0017 :=
    @g_n_2exbii
      (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))
        (syn_wa (.classMem (.cv w) (syn_c1c)) (.classMem (.cv t) (syn_c1c))))
      (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv w) (syn_csn (.cv x)))
            (.classEq (.cv t) (syn_csn (.cv y)))
            (.classEq (.cv z) (syn_copk (.cv w) (.cv t))))))
      w t p0016
  have p0018 :=
    @g_exrot4
      (syn_w3a (.classEq (.cv w) (syn_csn (.cv x))) (.classEq (.cv t) (syn_csn (.cv y)))
        (.classEq (.cv z) (syn_copk (.cv w) (.cv t))))
      x y w t
  have p0019 :=
    @g_bitr4i
      (syn_wex w (syn_wex t (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))
            (syn_wa (.classMem (.cv w) (syn_c1c)) (.classMem (.cv t) (syn_c1c))))))
      (syn_wex w (syn_wex t (syn_wex x (syn_wex y (syn_w3a (.classEq (.cv w) (syn_csn (.cv x)))
                (.classEq (.cv t) (syn_csn (.cv y)))
                (.classEq (.cv z) (syn_copk (.cv w) (.cv t))))))))
      (syn_wex x (syn_wex y (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv w) (syn_csn (.cv x)))
                (.classEq (.cv t) (syn_csn (.cv y)))
                (.classEq (.cv z) (syn_copk (.cv w) (.cv t))))))))
      p0017 p0018
  have p0020 := @g_snex (.cv x)
  have p0021 := @g_snex (.cv y)
  have p0022 := @g_opkeq1 (.cv w) (syn_csn (.cv x)) (.cv t)
  have p0023 :=
    @g_eqeq2d (.classEq (.cv w) (syn_csn (.cv x))) (syn_copk (.cv w) (.cv t))
      (syn_copk (syn_csn (.cv x)) (.cv t)) (.cv z) p0022
  have p0024 := @g_opkeq2 (.cv t) (syn_csn (.cv y)) (syn_csn (.cv x))
  have p0025 :=
    @g_eqeq2d (.classEq (.cv t) (syn_csn (.cv y))) (syn_copk (syn_csn (.cv x)) (.cv t))
      (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) (.cv z) p0024
  have freeVariableCertificate9 : w ∉ ((syn_csn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_x,
      not_false_eq_true]
  have freeVariableCertificate10 : t ∉ ((syn_csn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate11 : w ∉ ((syn_csn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_y,
      not_false_eq_true]
  have freeVariableCertificate12 : t ∉ ((syn_csn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
      not_false_eq_true]
  have freeVariableCertificate13 :
    t ∉ ((Wff.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_x, fresh_t_ne_y, or_false,
      not_false_eq_true]
  have freeVariableCertificate14 :
    w ∉ ((Wff.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (.cv t)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_x, fresh_w_ne_t, or_false,
      not_false_eq_true]
  have p0026 :=
    @g_ceqsex2v (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))
      (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (.cv t)))
      (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) w t
      (syn_csn (.cv x)) (syn_csn (.cv y)) freeVariableCertificate9
      freeVariableCertificate10 freeVariableCertificate11 freeVariableCertificate12
      freeVariableCertificate13 freeVariableCertificate14
      (show w ≠ t from (by exact fresh_w_ne_t)) p0020 p0021 p0023 p0025
  have p0027 :=
    @g_n_2exbii
      (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv w) (syn_csn (.cv x)))
            (.classEq (.cv t) (syn_csn (.cv y)))
            (.classEq (.cv z) (syn_copk (.cv w) (.cv t))))))
      (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))) x y p0026
  have p0028 :=
    @g_n_3bitri (.classMem (.cv z) (syn_cxpk (syn_c1c) (syn_c1c)))
      (syn_wex w (syn_wex t (syn_wa (.classEq (.cv z) (syn_copk (.cv w) (.cv t)))
            (syn_wa (.classMem (.cv w) (syn_c1c)) (.classMem (.cv t) (syn_c1c))))))
      (syn_wex x (syn_wex y (syn_wex w (syn_wex t (syn_w3a (.classEq (.cv w) (syn_csn (.cv x)))
                (.classEq (.cv t) (syn_csn (.cv y)))
                (.classEq (.cv z) (syn_copk (.cv w) (.cv t))))))))
      (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))))
      p0003 p0019 p0027
  have p0029 :=
    @g_imbi1i (.classMem (.cv z) (syn_cxpk (syn_c1c) (syn_c1c)))
      (syn_wex x (syn_wex y (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))))
      (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)) p0028
  have freeVariableCertificate15 :
    x ∉ ((syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_z, dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate16 :
    y ∉ ((syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_z, dv_A_y, dv_B_y, or_false, not_false_eq_true]
  have p0030 :=
    @g_n_19_23vv (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))
      (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)) x y freeVariableCertificate15
      freeVariableCertificate16
  have p0031 :=
    @g_bitr4i
      (.imp (.classMem (.cv z) (syn_cxpk (syn_c1c) (syn_c1c)))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.imp (syn_wex x
          (syn_wex y (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))
            (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))))
      p0029 p0030
  have p0032 :=
    @g_albii
      (.imp (.classMem (.cv z) (syn_cxpk (syn_c1c) (syn_c1c)))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))
            (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))))
      z p0031
  have p0033 :=
    @g_alrot3
      (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      z x y
  have p0034 :=
    @g_bitri
      (.all z (.imp (.classMem (.cv z) (syn_cxpk (syn_c1c) (syn_c1c)))
          (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.all z (.all x (.all y
            (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))
              (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      (.all x (.all y (.all z
            (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))
              (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      p0032 p0033
  have p0035 := @g_opkex (syn_csn (.cv x)) (syn_csn (.cv y))
  have p0036 := @g_eleq1 (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A
  have p0037 := @g_eleq1 (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B
  have p0038 :=
    @g_bibi12d (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))
      (.classMem (.cv z) A) (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A)
      (.classMem (.cv z) B) (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B)
      p0036 p0037
  have freeVariableCertificate17 :
    z ∉ ((syn_copk (syn_csn (.cv x)) (syn_csn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate18 :
    z ∉
      ((syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A)
          (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, fresh_z_not_B, or_false,
      not_false_eq_true]
  have p0039 :=
    @g_ceqsalv (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A)
        (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B))
      z (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) freeVariableCertificate17
      freeVariableCertificate18 p0035 p0038
  have p0040 :=
    @g_n_2albii
      (.all z (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))
          (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A)
        (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B))
      x y p0039
  have p0041 :=
    @g_n_3bitri
      (syn_wral z (syn_cxpk (syn_c1c) (syn_c1c))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all z (.imp (.classMem (.cv z) (syn_cxpk (syn_c1c) (syn_c1c)))
          (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))
      (.all x (.all y (.all z
            (.imp (.classEq (.cv z) (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))))
              (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B))))))
      (.all x (.all y (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A)
            (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B))))
      p0002 p0034 p0040
  have p0042 :=
    @g_bitri (.classEq A B)
      (syn_wral z (syn_cxpk (syn_c1c) (syn_c1c))
        (syn_wb (.classMem (.cv z) A) (.classMem (.cv z) B)))
      (.all x (.all y (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) A)
            (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (.cv y))) B))))
      p0001 p0041
  exact p0042

@[expose]
noncomputable def g_sikexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_csik A) (syn_cvv))) :=
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
  have p0000 := @g_sikeq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_csik (.cv x)) (syn_csik A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axSi x y z w
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show x ≠ w from (by exact fresh_x_ne_w)) (show y ≠ z from (by exact fresh_y_ne_z))
      (show y ≠ w from (by exact fresh_y_ne_w)) (show z ≠ w from (by exact fresh_z_ne_w))
  have p0003 := @g_inss1 (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)
  have p0004 := @g_sikss1c1c (.cv x)
  have freeVariableCertificate0 :
    z ∉ ((syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_z_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    w ∉ ((syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_w_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((syn_csik (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
      not_false_eq_true]
  have freeVariableCertificate3 : w ∉ ((syn_csik (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_x,
      not_false_eq_true]
  have p0005 :=
    @g_sikexlem z w (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)) (syn_csik (.cv x))
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2
      freeVariableCertificate3 (show z ≠ w from (by exact fresh_z_ne_w)) p0003 p0004
  have p0006 := @g_vex z
  have p0007 := @g_snel1c (.cv z) p0006
  have p0008 := @g_vex w
  have p0009 := @g_snel1c (.cv w) p0008
  have p0010 := @g_snex (.cv z)
  have p0011 := @g_snex (.cv w)
  have p0012 :=
    @g_opkelxpk (syn_csn (.cv z)) (syn_csn (.cv w)) (syn_c1c) (syn_c1c) p0010 p0011
  have p0013 :=
    @g_mpbir2an
      (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_cxpk (syn_c1c) (syn_c1c)))
      (.classMem (syn_csn (.cv z)) (syn_c1c)) (.classMem (syn_csn (.cv w)) (syn_c1c))
      p0007 p0009 p0012
  have p0014 :=
    @g_elin (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_cxpk (syn_c1c) (syn_c1c))
      (.cv y)
  have p0015 :=
    @g_mpbiran
      (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w)))
        (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)))
      (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_cxpk (syn_c1c) (syn_c1c)))
      (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y)) p0013 p0014
  have p0016 := @g_opksnelsik (.cv z) (.cv w) (.cv x) p0006 p0008
  have p0017 :=
    @g_bibi12i
      (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w)))
        (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)))
      (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y))
      (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_csik (.cv x)))
      (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)) p0015 p0016
  have p0018 :=
    @g_n_2albii
      (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w)))
          (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)))
        (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_csik (.cv x))))
      (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y))
        (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))
      z w p0017
  have p0019 :=
    @g_bitri
      (.classEq (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)) (syn_csik (.cv x)))
      (.all z (.all w (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w)))
              (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)))
            (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_csik (.cv x))))))
      (.all z (.all w (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y))
            (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))))
      p0005 p0018
  have p0020 :=
    @g_biimpri
      (.classEq (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)) (syn_csik (.cv x)))
      (.all z (.all w (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y))
            (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))))
      p0019
  have p0021 := @g_n_1cex
  have p0023 := @g_xpkex (syn_c1c) (syn_c1c) p0021 p0021
  have p0024 := @g_vex y
  have p0025 := @g_inex (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y) p0023 p0024
  have p0026 :=
    @g_syl6eqelr
      (.all z (.all w (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y))
            (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))))
      (syn_csik (.cv x)) (syn_cin (syn_cxpk (syn_c1c) (syn_c1c)) (.cv y)) (syn_cvv) p0020
      p0025
  have freeVariableCertificate4 : y ∉ ((Wff.classMem (syn_csik (.cv x)) (syn_cvv))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0027 :=
    @g_exlimiv
      (.all z (.all w (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (.cv y))
            (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))))
      (.classMem (syn_csik (.cv x)) (syn_cvv)) y freeVariableCertificate4 p0026
  have p0028 := Nominal.mp p0002 p0027
  have freeVariableCertificate5 : x ∉ ((Wff.classMem (syn_csik A) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0029 :=
    @g_vtoclg (.classMem (syn_csik (.cv x)) (syn_cvv)) (.classMem (syn_csik A) (syn_cvv))
      x A V (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate5 p0001 p0028
  exact p0029

@[expose]
noncomputable def g_sikex (A : Class)
    (hyp_sikex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_csik A) (syn_cvv)) :=
  by
  have p0000 := @g_sikexg A (syn_cvv)
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

@[expose]
noncomputable def g_dfimak2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_cimak A B) (syn_ccompl (syn_cp6
            (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
              (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))) :=
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
    (Nominal.biimpRefl (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A)))
  have p0001 :=
    @g_exancom (.classMem (.cv y) B) (.classMem (syn_copk (.cv y) (.cv x)) A) y
  have p0002 := @g_vex x
  have freeVariableCertificate0 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have freeVariableCertificate1 :
    z ∉
      ((syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))).fv :=
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
    @g_elp6 z (.cv x)
      (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
        (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))
      (syn_cvv) freeVariableCertificate0 freeVariableCertificate1
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_elun (syn_copk (.cv z) (syn_csn (.cv x)))
      (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
      (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))
  have p0006 := @g_opkex (.cv z) (syn_csn (.cv x))
  have p0007 :=
    @g_elcompl (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_c1c) (syn_cvv)) p0006
  have p0008 := @g_snex (.cv x)
  have p0009 := @g_vex z
  have p0010 := @g_opkelxpk (.cv z) (syn_csn (.cv x)) (syn_c1c) (syn_cvv) p0009 p0008
  have p0011 :=
    @g_mpbiran2
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_c1c) (syn_cvv)))
      (.classMem (.cv z) (syn_c1c)) (.classMem (syn_csn (.cv x)) (syn_cvv)) p0008 p0010
  have p0012 :=
    @g_xchbinx
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
        (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))))
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x))) (syn_cxpk (syn_c1c) (syn_cvv)))
      (.classMem (.cv z) (syn_c1c)) p0007 p0011
  have p0013 :=
    @g_orbi1i
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
        (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))))
      (.neg (.classMem (.cv z) (syn_c1c)))
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
        (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))
      p0012
  have p0014 :=
    @g_iman (.classMem (.cv z) (syn_c1c))
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
        (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))
  have p0015 :=
    @g_imor (.classMem (.cv z) (syn_c1c))
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
        (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))
  have freeVariableCertificate2 : y ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_z, not_false_eq_true]
  have p0016 := @g_el1c y (.cv z) freeVariableCertificate2
  have p0017 :=
    @g_anbi1i (.classMem (.cv z) (syn_c1c))
      (syn_wex y (.classEq (.cv z) (syn_csn (.cv y))))
      (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))
      p0016
  have freeVariableCertificate3 :
    y ∉
      ((Wff.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
            (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))).fv :=
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
    @g_n_19_41v (.classEq (.cv z) (syn_csn (.cv y)))
      (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))
      y freeVariableCertificate3
  have p0019 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv z) (syn_c1c)) (.neg
          (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
            (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))
      (syn_wa (syn_wex y (.classEq (.cv z) (syn_csn (.cv y)))) (.neg
          (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
            (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
            (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
              (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))
      p0017 p0018
  have p0020 :=
    @g_notbii
      (syn_wa (.classMem (.cv z) (syn_c1c)) (.neg
          (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
            (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
            (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
              (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))
      p0019
  have p0021 :=
    @g_n_3bitr3i
      (.imp (.classMem (.cv z) (syn_c1c)) (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))
      (.neg (syn_wa (.classMem (.cv z) (syn_c1c)) (.neg
            (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
              (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))
      (syn_wo (.neg (.classMem (.cv z) (syn_c1c)))
        (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))
      (.neg (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
              (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
                (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))))
      p0014 p0015 p0020
  have p0022 :=
    @g_n_3bitri
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
        (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))
      (syn_wo (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
          (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))))
        (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))
      (syn_wo (.neg (.classMem (.cv z) (syn_c1c)))
        (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))
      (.neg (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
              (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
                (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))))
      p0005 p0013 p0021
  have p0023 :=
    @g_albii
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
        (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))
      (.neg (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
              (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
                (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))))
      z p0022
  have p0024 :=
    @g_alnex
      (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
            (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
              (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))
      z
  have p0025 :=
    @g_excom
      (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
          (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
            (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))
      z y
  have p0026 := @g_snex (.cv y)
  have p0027 := @g_opkeq1 (.cv z) (syn_csn (.cv y)) (syn_csn (.cv x))
  have p0028 :=
    @g_eleq1d (.classEq (.cv z) (syn_csn (.cv y))) (syn_copk (.cv z) (syn_csn (.cv x)))
      (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x)))
      (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))) p0027
  have p0029 := @g_vex y
  have p0030 :=
    @g_opksnelsik (.cv y) (.cv x) (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))) p0029
      p0002
  have p0031 := @g_opkex (.cv y) (.cv x)
  have p0032 :=
    @g_elcompl (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))) p0031
  have p0033 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x)))
        (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))
      (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv)))))
      p0030 p0032
  have p0034 :=
    @g_syl6bb (.classEq (.cv z) (syn_csn (.cv y)))
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
        (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))
      (.classMem (syn_copk (syn_csn (.cv y)) (syn_csn (.cv x)))
        (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))
      (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv)))))
      p0028 p0033
  have p0035 :=
    @g_notbid (.classEq (.cv z) (syn_csn (.cv y)))
      (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
        (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))
      (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv)))))
      p0034
  have freeVariableCertificate4 : z ∉ ((syn_csn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_y,
      not_false_eq_true]
  have freeVariableCertificate5 :
    z ∉
      ((Wff.neg (.neg (.classMem (syn_copk (.cv y) (.cv x))
              (syn_cin A (syn_cxpk B (syn_cvv))))))).fv :=
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
    @g_ceqsexv
      (.neg (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))
      (.neg (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))))))
      z (syn_csn (.cv y)) freeVariableCertificate4 freeVariableCertificate5 p0026 p0035
  have p0037 := @g_elin (syn_copk (.cv y) (.cv x)) A (syn_cxpk B (syn_cvv))
  have p0038 :=
    @g_notnot (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))))
  have p0039 := @g_opkelxpk (.cv y) (.cv x) B (syn_cvv) p0029 p0002
  have p0040 :=
    @g_mpbiran2 (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk B (syn_cvv)))
      (.classMem (.cv y) B) (.classMem (.cv x) (syn_cvv)) p0002 p0039
  have p0041 :=
    @g_anbi2i (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk B (syn_cvv)))
      (.classMem (.cv y) B) (.classMem (syn_copk (.cv y) (.cv x)) A) p0040
  have p0042 :=
    @g_n_3bitr3i (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))))
      (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A)
        (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk B (syn_cvv))))
      (.neg (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))))))
      (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B)) p0037 p0038
      p0041
  have p0043 :=
    @g_bitri
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
            (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
              (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))
      (.neg (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin A (syn_cxpk B (syn_cvv))))))
      (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B)) p0036 p0042
  have p0044 :=
    @g_exbii
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
            (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
              (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))
      (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B)) y p0043
  have p0045 :=
    @g_bitri
      (syn_wex z (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
              (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
                (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
              (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
                (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))))
      (syn_wex y (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B)))
      p0025 p0044
  have p0046 :=
    @g_xchbinx
      (.all z (.neg (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
                (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
                  (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))))
      (syn_wex z (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
              (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
                (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))))
      (syn_wex y (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B)))
      p0024 p0045
  have p0047 :=
    @g_n_3bitri
      (.classMem (.cv x) (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
            (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))
      (.all z (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
          (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
            (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))
      (.all z (.neg (syn_wex y (syn_wa (.classEq (.cv z) (syn_csn (.cv y))) (.neg
                (.classMem (syn_copk (.cv z) (syn_csn (.cv x)))
                  (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))))
      (.neg (syn_wex y (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B))))
      p0004 p0023 p0046
  have p0048 :=
    @g_con2bii
      (.classMem (.cv x) (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
            (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))
      (syn_wex y (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B)))
      p0047
  have p0049 :=
    @g_n_3bitri (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A))
      (syn_wex y (syn_wa (.classMem (.cv y) B) (.classMem (syn_copk (.cv y) (.cv x)) A)))
      (syn_wex y (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) A) (.classMem (.cv y) B)))
      (.neg (.classMem (.cv x) (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
              (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))
      p0000 p0001 p0048
  have freeVariableCertificate6 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0050 :=
    @g_elimak y A B (.cv x) (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B))) freeVariableCertificate6
      p0002
  have p0051 :=
    @g_elcompl (.cv x)
      (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))
      p0002
  have p0052 :=
    @g_n_3bitr4i (syn_wrex y B (.classMem (syn_copk (.cv y) (.cv x)) A))
      (.neg (.classMem (.cv x) (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
              (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))
      (.classMem (.cv x) (syn_cimak A B))
      (.classMem (.cv x) (syn_ccompl (syn_cp6
            (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
              (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))))
      p0049 p0050 p0051
  have freeVariableCertificate7 : x ∉ ((syn_cimak A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate8 :
    x ∉
      ((syn_ccompl (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
              (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))).fv :=
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
    @g_eqriv x (syn_cimak A B)
      (syn_ccompl (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
            (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))
      freeVariableCertificate7 freeVariableCertificate8 p0052
  exact p0053

@[expose]
noncomputable def g_imakexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cimak A B) (syn_cvv))) :=
  by
  have p0000 := @g_dfimak2 A B
  have p0001 := @g_n_1cex
  have p0002 := @g_vvex
  have p0003 := @g_xpkex (syn_c1c) (syn_cvv) p0001 p0002
  have p0004 := @g_complex (syn_cxpk (syn_c1c) (syn_cvv)) p0003
  have p0006 := @g_xpkexg B (syn_cvv) W (syn_cvv)
  have p0007 :=
    @g_mpan2 (.classMem B W) (.classMem (syn_cvv) (syn_cvv))
      (.classMem (syn_cxpk B (syn_cvv)) (syn_cvv)) p0002 p0006
  have p0008 := @g_inexg A (syn_cxpk B (syn_cvv)) V (syn_cvv)
  have p0009 :=
    @g_sylan2 (.classMem B W) (.classMem A V) (.classMem (syn_cxpk B (syn_cvv)) (syn_cvv))
      (.classMem (syn_cin A (syn_cxpk B (syn_cvv))) (syn_cvv)) p0007 p0008
  have p0010 := @g_complexg (syn_cin A (syn_cxpk B (syn_cvv))) (syn_cvv)
  have p0011 := @g_sikexg (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))) (syn_cvv)
  have p0012 :=
    @g_n_3syl (syn_wa (.classMem A V) (.classMem B W))
      (.classMem (syn_cin A (syn_cxpk B (syn_cvv))) (syn_cvv))
      (.classMem (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))) (syn_cvv))
      (.classMem (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))) (syn_cvv))
      p0009 p0010 p0011
  have p0013 :=
    @g_unexg (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
      (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))) (syn_cvv) (syn_cvv)
  have p0014 :=
    @g_sylancr (syn_wa (.classMem A V) (.classMem B W))
      (.classMem (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv))) (syn_cvv))
      (.classMem (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))) (syn_cvv))
      (.classMem (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))) (syn_cvv))
      p0004 p0012 p0013
  have p0015 :=
    @g_p6exg
      (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
        (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))
      (syn_cvv)
  have p0016 :=
    @g_complexg
      (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))
      (syn_cvv)
  have p0017 :=
    @g_n_3syl (syn_wa (.classMem A V) (.classMem B W))
      (.classMem (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
          (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))) (syn_cvv))
      (.classMem (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
            (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))) (syn_cvv))
      (.classMem (syn_ccompl (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
              (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv)))))))) (syn_cvv))
      p0014 p0015 p0016
  have p0018 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cimak A B)
      (syn_ccompl (syn_cp6 (syn_cun (syn_ccompl (syn_cxpk (syn_c1c) (syn_cvv)))
            (syn_csik (syn_ccompl (syn_cin A (syn_cxpk B (syn_cvv))))))))
      (syn_cvv) p0000 p0017
  exact p0018

@[expose]
noncomputable def g_imakex (A : Class) (B : Class)
    (hyp_imakex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_imakex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cimak A B) (syn_cvv)) :=
  by
  have p0000 := @g_imakexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_cimak A B) (syn_cvv)) hyp_imakex_1 hyp_imakex_2 p0000
  exact p0001

@[expose]
noncomputable def g_dfpw12 (A : Class) :
    Nominal.NPrf
      (.classEq (syn_cpw1 A) (syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv))) :=
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
    @g_elpw1 y (.cv x) A freeVariableCertificate0
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0001 := @g_vex x
  have freeVariableCertificate1 : z ∉ ((syn_csik (syn_cxpk A A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_z_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate2 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have p0002 :=
    @g_elimakv z (syn_csik (syn_cxpk A A)) (.cv x) freeVariableCertificate1
      freeVariableCertificate2 p0001
  have p0003 := @g_vex z
  have freeVariableCertificate3 : w ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_z, not_false_eq_true]
  have freeVariableCertificate4 : y ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_z, not_false_eq_true]
  have freeVariableCertificate5 : w ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_x, not_false_eq_true]
  have freeVariableCertificate6 : w ∉ ((syn_cxpk A A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_w_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate7 : y ∉ ((syn_cxpk A A)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk, Finset.mem_union,
      fresh_y_not_A, or_false, not_false_eq_true]
  have p0004 :=
    @g_opkelsikg w y (.cv z) (.cv x) (syn_cxpk A A) (syn_cvv) (syn_cvv)
      freeVariableCertificate3 freeVariableCertificate4 freeVariableCertificate5
      freeVariableCertificate0 freeVariableCertificate6 freeVariableCertificate7
      (show w ≠ y from (by exact fresh_w_ne_y))
  have p0005 :=
    @g_mp2an (.classMem (.cv z) (syn_cvv)) (.classMem (.cv x) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv z) (.cv x)) (syn_csik (syn_cxpk A A))) (syn_wex w
          (syn_wex y (syn_w3a (.classEq (.cv z) (syn_csn (.cv w)))
              (.classEq (.cv x) (syn_csn (.cv y)))
              (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))))))
      p0003 p0001 p0004
  have p0006 :=
    @g_exbii (.classMem (syn_copk (.cv z) (.cv x)) (syn_csik (syn_cxpk A A)))
      (syn_wex w (syn_wex y (syn_w3a (.classEq (.cv z) (syn_csn (.cv w)))
            (.classEq (.cv x) (syn_csn (.cv y)))
            (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))))
      z p0005
  have p0007 :=
    @g_exrot3
      (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y)))
        (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))
      y z w
  have p0008 :=
    @g_bitr4i (syn_wex z (.classMem (syn_copk (.cv z) (.cv x)) (syn_csik (syn_cxpk A A))))
      (syn_wex z (syn_wex w (syn_wex y (syn_w3a (.classEq (.cv z) (syn_csn (.cv w)))
              (.classEq (.cv x) (syn_csn (.cv y)))
              (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))))))
      (syn_wex y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv z) (syn_csn (.cv w)))
              (.classEq (.cv x) (syn_csn (.cv y)))
              (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))))))
      p0006 p0007
  have p0009 :=
    (Nominal.biimpRefl
      (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y)))
        (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))))
  have p0010 := @g_vex w
  have p0011 := @g_vex y
  have p0012 := @g_opkelxpk (.cv w) (.cv y) A A p0010 p0011
  have p0013 :=
    @g_anbi2i (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))
      (syn_wa (.classMem (.cv w) A) (.classMem (.cv y) A))
      (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))))
      p0012
  have p0014 :=
    @g_an4 (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y)))
      (.classMem (.cv w) A) (.classMem (.cv y) A)
  have p0015 :=
    @g_n_3bitri
      (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y)))
        (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))))
        (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))))
        (syn_wa (.classMem (.cv w) A) (.classMem (.cv y) A)))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A))
        (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)))
      p0009 p0013 p0014
  have p0016 :=
    @g_n_2exbii
      (syn_w3a (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y)))
        (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A))
        (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)))
      z w p0015
  have freeVariableCertificate8 :
    z ∉ ((syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
      Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_not_A, or_false,
      not_false_eq_true]
  have freeVariableCertificate9 :
    w ∉ ((syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
      Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_not_A, or_false,
      not_false_eq_true]
  have p0017 :=
    @g_n_19_41vv (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)) z w
      freeVariableCertificate8 freeVariableCertificate9
  have p0018 := @g_sneq (.cv w) (.cv y)
  have p0019 := @g_eqeq12 (.cv z) (.cv x) (syn_csn (.cv w)) (syn_csn (.cv y))
  have p0020_e00_recanon :
    Nominal.NPrf (.imp (.objEq w y) (.classEq (syn_csn (.cv w)) (syn_csn (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0020_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq z x) (.classEq (syn_csn (.cv w)) (syn_csn (.cv y))))
        (syn_wb (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_csn syn_wb
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
    @g_sylan2 (.objEq w y) (.objEq z x) (.classEq (syn_csn (.cv w)) (syn_csn (.cv y)))
      (syn_wb (.classEq (.cv z) (syn_csn (.cv w))) (.classEq (.cv x) (syn_csn (.cv y))))
      p0020_e00_recanon p0020_e01_recanon
  have p0021 := @g_eleq1 (.cv w) (.cv y) A
  have p0022_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w y) (syn_wb (.classMem (.cv w) A) (.classMem (.cv y) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0021
  have p0022 :=
    @g_adantl (.objEq w y) (syn_wb (.classMem (.cv w) A) (.classMem (.cv y) A))
      (.objEq z x) p0022_e00_recanon
  have p0023 :=
    @g_anbi12d (syn_wa (.objEq z x) (.objEq w y)) (.classEq (.cv z) (syn_csn (.cv w)))
      (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv w) A) (.classMem (.cv y) A)
      p0020 p0022
  have p0024_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv z) (.cv x)) (.classEq (.cv w) (.cv y)))
        (syn_wb (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A))
          (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wb
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
    @g_spc2ev (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)) z w (.cv x)
      (.cv y) freeVariableCertificate2 freeVariableCertificate5 freeVariableCertificate10
      freeVariableCertificate11 freeVariableCertificate8 freeVariableCertificate9
      (show z ≠ w from (by exact fresh_z_ne_w)) p0001 p0011 p0024_e02_recanon
  have p0025 :=
    @g_pm4_71ri (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))
      (syn_wex z
        (syn_wex w (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A))))
      p0024
  have p0026 := @g_ancom (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)
  have p0027 :=
    @g_bitr3i
      (syn_wa (syn_wex z
          (syn_wex w (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A))))
        (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)))
      (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A))
      (syn_wa (.classMem (.cv y) A) (.classEq (.cv x) (syn_csn (.cv y)))) p0025 p0026
  have p0028 :=
    @g_n_3bitri
      (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv z) (syn_csn (.cv w)))
            (.classEq (.cv x) (syn_csn (.cv y)))
            (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))))
      (syn_wex z (syn_wex w
          (syn_wa (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A))
            (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)))))
      (syn_wa (syn_wex z
          (syn_wex w (syn_wa (.classEq (.cv z) (syn_csn (.cv w))) (.classMem (.cv w) A))))
        (syn_wa (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv y) A)))
      (syn_wa (.classMem (.cv y) A) (.classEq (.cv x) (syn_csn (.cv y)))) p0016 p0017
      p0027
  have p0029 :=
    @g_exbii
      (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv z) (syn_csn (.cv w)))
            (.classEq (.cv x) (syn_csn (.cv y)))
            (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A)))))
      (syn_wa (.classMem (.cv y) A) (.classEq (.cv x) (syn_csn (.cv y)))) y p0028
  have p0030 := (Nominal.biimpRefl (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))))
  have p0031 :=
    @g_bitr4i
      (syn_wex y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv z) (syn_csn (.cv w)))
              (.classEq (.cv x) (syn_csn (.cv y)))
              (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))))))
      (syn_wex y (syn_wa (.classMem (.cv y) A) (.classEq (.cv x) (syn_csn (.cv y)))))
      (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))) p0029 p0030
  have p0032 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv)))
      (syn_wex z (.classMem (syn_copk (.cv z) (.cv x)) (syn_csik (syn_cxpk A A))))
      (syn_wex y (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv z) (syn_csn (.cv w)))
              (.classEq (.cv x) (syn_csn (.cv y)))
              (.classMem (syn_copk (.cv w) (.cv y)) (syn_cxpk A A))))))
      (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y)))) p0002 p0008 p0031
  have p0033 :=
    @g_bitr4i (.classMem (.cv x) (syn_cpw1 A))
      (syn_wrex y A (.classEq (.cv x) (syn_csn (.cv y))))
      (.classMem (.cv x) (syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv))) p0000 p0032
  have freeVariableCertificate12 :
    x ∉ ((syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0034 :=
    @g_eqriv x (syn_cpw1 A) (syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv))
      (by
        exact
          (show x ∉ ((syn_cpw1 A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate12 p0033
  exact p0034

@[expose]
noncomputable def g_pw1exg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cpw1 A) (syn_cvv))) :=
  by
  have p0000 := @g_dfpw12 A
  have p0001 := @g_xpkexg A A V V
  have p0002 := @g_anidms (.classMem A V) (.classMem (syn_cxpk A A) (syn_cvv)) p0001
  have p0003 := @g_sikexg (syn_cxpk A A) (syn_cvv)
  have p0004 :=
    @g_syl (.classMem A V) (.classMem (syn_cxpk A A) (syn_cvv))
      (.classMem (syn_csik (syn_cxpk A A)) (syn_cvv)) p0002 p0003
  have p0005 := @g_vvex
  have p0006 := @g_imakexg (syn_csik (syn_cxpk A A)) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0007 :=
    @g_sylancl (.classMem A V) (.classMem (syn_csik (syn_cxpk A A)) (syn_cvv))
      (.classMem (syn_cvv) (syn_cvv))
      (.classMem (syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv)) (syn_cvv)) p0004 p0005
      p0006
  have p0008 :=
    @g_syl5eqel (.classMem A V) (syn_cpw1 A)
      (syn_cimak (syn_csik (syn_cxpk A A)) (syn_cvv)) (syn_cvv) p0000 p0007
  exact p0008

@[expose]
noncomputable def g_pw1ex (A : Class)
    (hyp_pw1ex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cpw1 A) (syn_cvv)) :=
  by
  have p0000 := @g_pw1exg A (syn_cvv)
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

@[expose]
noncomputable def g_insklem (x : Var) (y : Var) (z : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z)
    (dv_y_z : y ≠ z)
    (hyp_insklem_1 : Nominal.NPrf
        (syn_wss A (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))))
    (hyp_insklem_2 : Nominal.NPrf
        (syn_wss B (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))) :
    Nominal.NPrf
      (syn_wb (.classEq A B) (.all x (.all y (.all z (syn_wb (.classMem
                  (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A)
                (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))
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
    w ∉ ((syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0000 :=
    @g_ssofeq w A B (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (by exact (show w ∉ (A).fv from (by exact fresh_w_not_A)))
      (by exact (show w ∉ (B).fv from (by exact fresh_w_not_B))) freeVariableCertificate0
  have p0001 :=
    @g_mp2an (syn_wss A (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (syn_wss B (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (syn_wb (.classEq A B)
        (syn_wral w (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))
          (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))
      hyp_insklem_1 hyp_insklem_2 p0000
  have freeVariableCertificate1 :
    x ∉ ((syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_w, dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have p0002 :=
    @g_n_19_23v
      (syn_wex y (syn_wex z (.classEq (.cv w)
            (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))))
      (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)) x freeVariableCertificate1
  have freeVariableCertificate2 :
    y ∉ ((syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_ne_w, dv_A_y, dv_B_y, or_false, not_false_eq_true]
  have freeVariableCertificate3 :
    z ∉ ((syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_z_ne_w, dv_A_z, dv_B_z, or_false, not_false_eq_true]
  have p0003 :=
    @g_n_19_23vv
      (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
      (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)) y z freeVariableCertificate2
      freeVariableCertificate3
  have p0004 :=
    @g_albii
      (.all y (.all z (.imp (.classEq (.cv w)
              (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
            (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))))
      (.imp (syn_wex y (syn_wex z (.classEq (.cv w)
              (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))))
        (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      x p0003
  have freeVariableCertificate4 : y ∉ ((Wff.classMem (.cv t) (syn_cpw1 (syn_c1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_t, or_false,
      not_false_eq_true]
  have freeVariableCertificate5 : z ∉ ((Wff.classMem (.cv t) (syn_cpw1 (syn_c1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_t, or_false,
      not_false_eq_true]
  have p0005 :=
    @g_n_19_42vv (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) y z freeVariableCertificate4
      freeVariableCertificate5
  have p0006 :=
    @g_anbi2i
      (syn_wex y (syn_wex z (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
            (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
        (syn_wex y (syn_wex z (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))
      (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) p0005
  have freeVariableCertificate6 :
    y ∉ ((Wff.classEq (.cv w) (syn_copk (.cv t) (.cv u)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_w, fresh_y_ne_t, fresh_y_ne_u, or_false,
      not_false_eq_true]
  have freeVariableCertificate7 :
    z ∉ ((Wff.classEq (.cv w) (syn_copk (.cv t) (.cv u)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_t, fresh_z_ne_u, or_false,
      not_false_eq_true]
  have p0007 :=
    @g_n_19_42vv (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
        (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))
      y z freeVariableCertificate6 freeVariableCertificate7
  have freeVariableCertificate8 : y ∉ ((Class.cv u)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_u, not_false_eq_true]
  have freeVariableCertificate9 : z ∉ ((Class.cv u)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_u, not_false_eq_true]
  have p0008 :=
    @g_elvvk y z (.cv u) freeVariableCertificate8 freeVariableCertificate9
      (show y ≠ z from (by exact dv_y_z))
  have p0009 :=
    @g_anbi2i (.classMem (.cv u) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wex y (syn_wex z (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))
      (.classMem (.cv t) (syn_cpw1 (syn_c1c))) p0008
  have p0010 :=
    @g_anbi2i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
        (.classMem (.cv u) (syn_cxpk (syn_cvv) (syn_cvv))))
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
        (syn_wex y (syn_wex z (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))))
      (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) p0009
  have p0011 :=
    @g_n_3bitr4ri
      (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) (syn_wex y (syn_wex z
            (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
              (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))))
      (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
        (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
          (syn_wex y (syn_wex z (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
            (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
              (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))))
      (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
        (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
          (.classMem (.cv u) (syn_cxpk (syn_cvv) (syn_cvv)))))
      p0006 p0007 p0010
  have p0012 :=
    @g_n_2exbii
      (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
        (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
          (.classMem (.cv u) (syn_cxpk (syn_cvv) (syn_cvv)))))
      (syn_wex y (syn_wex z (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
            (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
              (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))))
      t u p0011
  have freeVariableCertificate10 : t ∉ ((Class.cv w)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_w, not_false_eq_true]
  have freeVariableCertificate11 : u ∉ ((Class.cv w)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_u_ne_w, not_false_eq_true]
  have freeVariableCertificate12 : t ∉ ((syn_cpw1 (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate13 : u ∉ ((syn_cpw1 (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate14 : t ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate15 : u ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0013 :=
    @g_elxpk t u (.cv w) (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))
      freeVariableCertificate10 freeVariableCertificate11 freeVariableCertificate12
      freeVariableCertificate13 freeVariableCertificate14 freeVariableCertificate15
      (show t ≠ u from (by exact fresh_t_ne_u))
  have p0014 :=
    @g_exrot3
      (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
      x y z
  have p0015 :=
    @g_exancom (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))
      (.classMem (.cv t) (syn_cpw1 (syn_c1c))) t
  have freeVariableCertificate16 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0016 := @g_elpw11c x (.cv t) freeVariableCertificate16
  have p0017 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))))
      (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) p0016
  have freeVariableCertificate17 :
    x ∉ ((Wff.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_t, dv_x_y, dv_x_z, or_false,
      not_false_eq_true]
  have p0018 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))
      (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))) x
      freeVariableCertificate17
  have p0019 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
        (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))))
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))))
        (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))
          (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))))
      p0017 p0018
  have p0020 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
        (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))
          (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))))
      t p0019
  have p0021 :=
    @g_bitri
      (syn_wex t (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))
          (.classMem (.cv t) (syn_cpw1 (syn_c1c)))))
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
          (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))
            (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))))))
      p0015 p0020
  have p0022 :=
    @g_ancom (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
  have p0023 :=
    @g_anbi2i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
        (.classEq (.cv u) (syn_copk (.cv y) (.cv z))))
      (syn_wa (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
        (.classMem (.cv t) (syn_cpw1 (syn_c1c))))
      (.classEq (.cv w) (syn_copk (.cv t) (.cv u))) p0022
  have p0024 :=
    @g_an12 (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
      (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
      (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
  have p0025 :=
    @g_bitri
      (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
        (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
          (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))
      (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
        (syn_wa (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
          (.classMem (.cv t) (syn_cpw1 (syn_c1c)))))
      (syn_wa (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
        (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
          (.classMem (.cv t) (syn_cpw1 (syn_c1c)))))
      p0023 p0024
  have p0026 :=
    @g_n_2exbii
      (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
        (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
          (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))
      (syn_wa (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
        (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
          (.classMem (.cv t) (syn_cpw1 (syn_c1c)))))
      t u p0025
  have p0027 := @g_opkex (.cv y) (.cv z)
  have p0028 := @g_opkeq2 (.cv u) (syn_copk (.cv y) (.cv z)) (.cv t)
  have p0029 :=
    @g_eqeq2d (.classEq (.cv u) (syn_copk (.cv y) (.cv z))) (syn_copk (.cv t) (.cv u))
      (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))) (.cv w) p0028
  have p0030 :=
    @g_anbi1d (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
      (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
      (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))
      (.classMem (.cv t) (syn_cpw1 (syn_c1c))) p0029
  have freeVariableCertificate18 : u ∉ ((syn_copk (.cv y) (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_u_ne_y, fresh_u_ne_z, or_false, not_false_eq_true]
  have freeVariableCertificate19 :
    u ∉
      ((syn_wa (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))
          (.classMem (.cv t) (syn_cpw1 (syn_c1c))))).fv :=
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
    @g_ceqsexv
      (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
        (.classMem (.cv t) (syn_cpw1 (syn_c1c))))
      (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))
        (.classMem (.cv t) (syn_cpw1 (syn_c1c))))
      u (syn_copk (.cv y) (.cv z)) freeVariableCertificate18 freeVariableCertificate19
      p0027 p0030
  have p0032 :=
    @g_exbii
      (syn_wex u (syn_wa (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
          (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
            (.classMem (.cv t) (syn_cpw1 (syn_c1c))))))
      (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))
        (.classMem (.cv t) (syn_cpw1 (syn_c1c))))
      t p0031
  have p0033 :=
    @g_bitri
      (syn_wex t (syn_wex u (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
            (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
              (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))))
      (syn_wex t (syn_wex u (syn_wa (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))
            (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
              (.classMem (.cv t) (syn_cpw1 (syn_c1c)))))))
      (syn_wex t (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))
          (.classMem (.cv t) (syn_cpw1 (syn_c1c)))))
      p0026 p0032
  have p0034 := @g_snex (syn_csn (.cv x))
  have p0035 := @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))
  have p0036 :=
    @g_eqeq2d (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))
      (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))
      (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) (.cv w) p0035
  have freeVariableCertificate20 : t ∉ ((syn_csn (syn_csn (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate21 :
    t ∉
      ((Wff.classEq (.cv w)
          (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_x, fresh_t_ne_y, fresh_t_ne_z,
      or_false, not_false_eq_true]
  have p0037 :=
    @g_ceqsexv (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))
      (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
      t (syn_csn (syn_csn (.cv x))) freeVariableCertificate20 freeVariableCertificate21
      p0034 p0036
  have p0038 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))
          (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))))
      (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
      x p0037
  have p0039 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))
        (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))))
      x t
  have p0040 :=
    @g_bitr3i
      (syn_wex x (.classEq (.cv w)
          (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))
            (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))))))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))
            (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))))))
      p0038 p0039
  have p0041 :=
    @g_n_3bitr4ri
      (syn_wex t (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))))
          (.classMem (.cv t) (syn_cpw1 (syn_c1c)))))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))
            (.classEq (.cv w) (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))))))
      (syn_wex t (syn_wex u (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
            (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
              (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))))
      (syn_wex x (.classEq (.cv w)
          (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))))
      p0021 p0033 p0040
  have p0042 :=
    @g_n_2exbii
      (syn_wex x (.classEq (.cv w)
          (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))))
      (syn_wex t (syn_wex u (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
            (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
              (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))))
      y z p0041
  have p0043 :=
    @g_exrot4
      (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
        (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
          (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))
      y z t u
  have p0044 :=
    @g_bitri
      (syn_wex y (syn_wex z (syn_wex x (.classEq (.cv w)
              (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))))))
      (syn_wex y (syn_wex z (syn_wex t (syn_wex u
              (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
                (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
                  (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))))))
      (syn_wex t (syn_wex u (syn_wex y (syn_wex z
              (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
                (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
                  (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))))))
      p0042 p0043
  have p0045 :=
    @g_bitri
      (syn_wex x (syn_wex y (syn_wex z (.classEq (.cv w)
              (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))))))
      (syn_wex y (syn_wex z (syn_wex x (.classEq (.cv w)
              (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))))))
      (syn_wex t (syn_wex u (syn_wex y (syn_wex z
              (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
                (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
                  (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))))))
      p0014 p0044
  have p0046 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wex u (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
            (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
              (.classMem (.cv u) (syn_cxpk (syn_cvv) (syn_cvv)))))))
      (syn_wex t (syn_wex u (syn_wex y (syn_wex z
              (syn_wa (.classEq (.cv w) (syn_copk (.cv t) (.cv u)))
                (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
                  (.classEq (.cv u) (syn_copk (.cv y) (.cv z)))))))))
      (.classMem (.cv w) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (syn_wex x (syn_wex y (syn_wex z (.classEq (.cv w)
              (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))))))
      p0012 p0013 p0045
  have p0047 :=
    @g_imbi1i
      (.classMem (.cv w) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (syn_wex x (syn_wex y (syn_wex z (.classEq (.cv w)
              (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))))))
      (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)) p0046
  have p0048 :=
    @g_n_3bitr4ri
      (.all x (.imp (syn_wex y (syn_wex z (.classEq (.cv w)
                (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))))
          (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))
      (.imp (syn_wex x (syn_wex y (syn_wex z (.classEq (.cv w)
                (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))))))
        (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      (.all x (.all y (.all z (.imp (.classEq (.cv w)
                (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
              (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))))
      (.imp (.classMem (.cv w) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
        (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      p0002 p0004 p0047
  have p0049 :=
    @g_albii
      (.imp (.classMem (.cv w) (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
        (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      (.all x (.all y (.all z (.imp (.classEq (.cv w)
                (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
              (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))))
      w p0048
  have p0050 :=
    (Nominal.biimpRefl
      (syn_wral w (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))
        (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))
  have p0051 :=
    @g_alcom
      (.all y (.all z (.imp (.classEq (.cv w)
              (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
            (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))))
      w x
  have p0052 :=
    @g_alrot3
      (.imp (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
        (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      w y z
  have p0053 :=
    @g_albii
      (.all w (.all y (.all z (.imp (.classEq (.cv w)
                (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
              (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))))
      (.all y (.all z (.all w (.imp (.classEq (.cv w)
                (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
              (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))))
      x p0052
  have p0054 := @g_opkex (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))
  have p0055 :=
    @g_eleq1 (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A
  have p0056 :=
    @g_eleq1 (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B
  have p0057 :=
    @g_bibi12d
      (.classEq (.cv w) (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
      (.classMem (.cv w) A)
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A)
      (.classMem (.cv w) B)
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B)
      p0055 p0056
  have freeVariableCertificate22 :
    w ∉ ((syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true]
  have freeVariableCertificate23 :
    w ∉
      ((syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A)
          (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))
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
    @g_ceqsalv (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A)
        (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B))
      w (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))
      freeVariableCertificate22 freeVariableCertificate23 p0054 p0057
  have p0059 :=
    @g_albii
      (.all w (.imp (.classEq (.cv w)
            (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
          (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A)
        (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B))
      z p0058
  have p0060 :=
    @g_n_2albii
      (.all z (.all w (.imp (.classEq (.cv w)
              (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
            (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))))
      (.all z (syn_wb
          (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A)
          (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) B)))
      x y p0059
  have p0061 :=
    @g_n_3bitrri
      (.all w (.all x (.all y (.all z (.imp (.classEq (.cv w)
                  (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
                (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))))))
      (.all x (.all w (.all y (.all z (.imp (.classEq (.cv w)
                  (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
                (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))))))
      (.all x (.all y (.all z (.all w (.imp (.classEq (.cv w)
                  (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
                (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))))))
      (.all x (.all y (.all z (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A)
              (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))
                B)))))
      p0051 p0053 p0060
  have p0062 :=
    @g_n_3bitr4i
      (.all w (.imp (.classMem (.cv w)
            (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
          (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B))))
      (.all w (.all x (.all y (.all z (.imp (.classEq (.cv w)
                  (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))))
                (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))))))
      (syn_wral w (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))
        (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      (.all x (.all y (.all z (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A)
              (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))
                B)))))
      p0049 p0050 p0061
  have p0063 :=
    @g_bitri (.classEq A B)
      (syn_wral w (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))
        (syn_wb (.classMem (.cv w) A) (.classMem (.cv w) B)))
      (.all x (.all y (.all z (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z))) A)
              (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))
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

@[expose]
noncomputable def g_ins2kexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cins2k A) (syn_cvv))) :=
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
  have p0000 := @g_ins2keq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cins2k (.cv x)) (syn_cins2k A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axIns2 x y z
      w t (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show x ≠ t from (by exact fresh_x_ne_t)) (show y ≠ z from (by exact fresh_y_ne_z))
      (show y ≠ w from (by exact fresh_y_ne_w)) (show y ≠ t from (by exact fresh_y_ne_t))
      (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ t from (by exact fresh_z_ne_t))
      (show w ≠ t from (by exact fresh_w_ne_t))
  have p0003 :=
    @g_inss1 (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)
  have p0004 := @g_ins2kss (.cv x)
  have freeVariableCertificate0 :
    z ∉
      ((syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))).fv :=
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
      ((syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))).fv :=
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
      ((syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_t_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate3 : z ∉ ((syn_cins2k (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
      not_false_eq_true]
  have freeVariableCertificate4 : w ∉ ((syn_cins2k (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_x,
      not_false_eq_true]
  have freeVariableCertificate5 : t ∉ ((syn_cins2k (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have p0005 :=
    @g_insklem z w t
      (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))
      (syn_cins2k (.cv x)) freeVariableCertificate0 freeVariableCertificate1
      freeVariableCertificate2 freeVariableCertificate3 freeVariableCertificate4
      freeVariableCertificate5 (show z ≠ w from (by exact fresh_z_ne_w))
      (show z ≠ t from (by exact fresh_z_ne_t)) (show w ≠ t from (by exact fresh_w_ne_t))
      p0003 p0004
  have p0006 := @g_vex z
  have p0007 := @g_snel1c (.cv z) p0006
  have p0008 := @g_snelpw1 (syn_csn (.cv z)) (syn_c1c)
  have p0009 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (.cv z))) (syn_cpw1 (syn_c1c)))
      (.classMem (syn_csn (.cv z)) (syn_c1c)) p0007 p0008
  have p0010 := @g_vex w
  have p0011 := @g_vex t
  have p0012 := @g_opkelxpk (.cv w) (.cv t) (syn_cvv) (syn_cvv) p0010 p0011
  have p0013 :=
    @g_mpbir2an (.classMem (syn_copk (.cv w) (.cv t)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (.classMem (.cv w) (syn_cvv)) (.classMem (.cv t) (syn_cvv)) p0010 p0011 p0012
  have p0014 := @g_snex (syn_csn (.cv z))
  have p0015 := @g_opkex (.cv w) (.cv t)
  have p0016 :=
    @g_opkelxpk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))
      (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) p0014 p0015
  have p0017 :=
    @g_mpbir2an
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (.classMem (syn_csn (syn_csn (.cv z))) (syn_cpw1 (syn_c1c)))
      (.classMem (syn_copk (.cv w) (.cv t)) (syn_cxpk (syn_cvv) (syn_cvv))) p0009 p0013
      p0016
  have p0018 :=
    @g_elin (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
      (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)
  have p0019 :=
    @g_mpbiran
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
        (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y))
      p0017 p0018
  have p0020 := @g_otkelins2k (.cv z) (.cv w) (.cv t) (.cv x) p0006 p0010 p0011
  have p0021 :=
    @g_bibi12i
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
        (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
        (syn_cins2k (.cv x)))
      (.classMem (syn_copk (.cv z) (.cv t)) (.cv x)) p0019 p0020
  have p0022 :=
    @g_albii
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
          (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)))
        (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
          (syn_cins2k (.cv x))))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
          (.cv y)) (.classMem (syn_copk (.cv z) (.cv t)) (.cv x)))
      t p0021
  have p0023 :=
    @g_n_2albii
      (.all t (syn_wb
          (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
            (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)))
          (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
            (syn_cins2k (.cv x)))))
      (.all t (syn_wb
          (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y))
          (.classMem (syn_copk (.cv z) (.cv t)) (.cv x))))
      z w p0022
  have p0024 :=
    @g_bitri
      (.classEq (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))
        (syn_cins2k (.cv x)))
      (.all z (.all w (.all t (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
                (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))
                  (.cv y)))
              (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
                (syn_cins2k (.cv x)))))))
      (.all z (.all w (.all t (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
                (.cv y)) (.classMem (syn_copk (.cv z) (.cv t)) (.cv x))))))
      p0005 p0023
  have p0025 :=
    @g_biimpri
      (.classEq (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))
        (syn_cins2k (.cv x)))
      (.all z (.all w (.all t (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
                (.cv y)) (.classMem (syn_copk (.cv z) (.cv t)) (.cv x))))))
      p0024
  have p0026 := @g_n_1cex
  have p0027 := @g_pw1ex (syn_c1c) p0026
  have p0028 := @g_vvex
  have p0030 := @g_xpkex (syn_cvv) (syn_cvv) p0028 p0028
  have p0031 := @g_xpkex (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) p0027 p0030
  have p0032 := @g_vex y
  have p0033 :=
    @g_inex (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y) p0031
      p0032
  have p0034 :=
    @g_syl6eqelr
      (.all z (.all w (.all t (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
                (.cv y)) (.classMem (syn_copk (.cv z) (.cv t)) (.cv x))))))
      (syn_cins2k (.cv x))
      (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))
      (syn_cvv) p0025 p0033
  have freeVariableCertificate6 :
    y ∉ ((Wff.classMem (syn_cins2k (.cv x)) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0035 :=
    @g_exlimiv
      (.all z (.all w (.all t (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
                (.cv y)) (.classMem (syn_copk (.cv z) (.cv t)) (.cv x))))))
      (.classMem (syn_cins2k (.cv x)) (syn_cvv)) y freeVariableCertificate6 p0034
  have p0036 := Nominal.mp p0002 p0035
  have freeVariableCertificate7 : x ∉ ((Wff.classMem (syn_cins2k A) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0037 :=
    @g_vtoclg (.classMem (syn_cins2k (.cv x)) (syn_cvv))
      (.classMem (syn_cins2k A) (syn_cvv)) x A V
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate7
      p0001 p0036
  exact p0037

@[expose]
noncomputable def g_ins3kexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cins3k A) (syn_cvv))) :=
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
  have p0000 := @g_ins3keq (.cv x) A
  have p0001 :=
    @g_eleq1d (.classEq (.cv x) A) (syn_cins3k (.cv x)) (syn_cins3k A) (syn_cvv) p0000
  have p0002 :=
    NFChoice.DirectNominalPrf.Nominal.NFLiteralRemainingViaCompletenessDev001.axIns3 x y z
      w t (show x ≠ y from (by exact fresh_x_ne_y))
      (show x ≠ z from (by exact fresh_x_ne_z)) (show x ≠ w from (by exact fresh_x_ne_w))
      (show x ≠ t from (by exact fresh_x_ne_t)) (show y ≠ z from (by exact fresh_y_ne_z))
      (show y ≠ w from (by exact fresh_y_ne_w)) (show y ≠ t from (by exact fresh_y_ne_t))
      (show z ≠ w from (by exact fresh_z_ne_w)) (show z ≠ t from (by exact fresh_z_ne_t))
      (show w ≠ t from (by exact fresh_w_ne_t))
  have p0003 :=
    @g_inss1 (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)
  have p0004 := @g_ins3kss (.cv x)
  have freeVariableCertificate0 :
    z ∉
      ((syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))).fv :=
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
      ((syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))).fv :=
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
      ((syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_t_ne_y, or_false, not_false_eq_true]
  have freeVariableCertificate3 : z ∉ ((syn_cins3k (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
      not_false_eq_true]
  have freeVariableCertificate4 : w ∉ ((syn_cins3k (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_w_ne_x,
      not_false_eq_true]
  have freeVariableCertificate5 : t ∉ ((syn_cins3k (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have p0005 :=
    @g_insklem z w t
      (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))
      (syn_cins3k (.cv x)) freeVariableCertificate0 freeVariableCertificate1
      freeVariableCertificate2 freeVariableCertificate3 freeVariableCertificate4
      freeVariableCertificate5 (show z ≠ w from (by exact fresh_z_ne_w))
      (show z ≠ t from (by exact fresh_z_ne_t)) (show w ≠ t from (by exact fresh_w_ne_t))
      p0003 p0004
  have p0006 := @g_vex z
  have p0007 := @g_snel1c (.cv z) p0006
  have p0008 := @g_snelpw1 (syn_csn (.cv z)) (syn_c1c)
  have p0009 :=
    @g_mpbir (.classMem (syn_csn (syn_csn (.cv z))) (syn_cpw1 (syn_c1c)))
      (.classMem (syn_csn (.cv z)) (syn_c1c)) p0007 p0008
  have p0010 := @g_vex w
  have p0011 := @g_vex t
  have p0012 := @g_opkelxpk (.cv w) (.cv t) (syn_cvv) (syn_cvv) p0010 p0011
  have p0013 :=
    @g_mpbir2an (.classMem (syn_copk (.cv w) (.cv t)) (syn_cxpk (syn_cvv) (syn_cvv)))
      (.classMem (.cv w) (syn_cvv)) (.classMem (.cv t) (syn_cvv)) p0010 p0011 p0012
  have p0014 := @g_snex (syn_csn (.cv z))
  have p0015 := @g_opkex (.cv w) (.cv t)
  have p0016 :=
    @g_opkelxpk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))
      (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) p0014 p0015
  have p0017 :=
    @g_mpbir2an
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (.classMem (syn_csn (syn_csn (.cv z))) (syn_cpw1 (syn_c1c)))
      (.classMem (syn_copk (.cv w) (.cv t)) (syn_cxpk (syn_cvv) (syn_cvv))) p0009 p0013
      p0016
  have p0018 :=
    @g_elin (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
      (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)
  have p0019 :=
    @g_mpbiran
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
        (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
        (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y))
      p0017 p0018
  have p0020 := @g_otkelins3k (.cv z) (.cv w) (.cv t) (.cv x) p0006 p0010 p0011
  have p0021 :=
    @g_bibi12i
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
        (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t))) (.cv y))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
        (syn_cins3k (.cv x)))
      (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)) p0019 p0020
  have p0022 :=
    @g_n_2albii
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
          (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)))
        (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
          (syn_cins3k (.cv x))))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
          (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))
      w t p0021
  have p0023 :=
    @g_albii
      (.all w (.all t (syn_wb
            (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
              (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y)))
            (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
              (syn_cins3k (.cv x))))))
      (.all w (.all t (syn_wb
            (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
              (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x)))))
      z p0022
  have p0024 :=
    @g_bitri
      (.classEq (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))
        (syn_cins3k (.cv x)))
      (.all z (.all w (.all t (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
                (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)))
                  (.cv y)))
              (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
                (syn_cins3k (.cv x)))))))
      (.all z (.all w (.all t (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
                (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))))))
      p0005 p0023
  have p0025 :=
    @g_biimpri
      (.classEq (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))
        (syn_cins3k (.cv x)))
      (.all z (.all w (.all t (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
                (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))))))
      p0024
  have p0026 := @g_n_1cex
  have p0027 := @g_pw1ex (syn_c1c) p0026
  have p0028 := @g_vvex
  have p0030 := @g_xpkex (syn_cvv) (syn_cvv) p0028 p0028
  have p0031 := @g_xpkex (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv)) p0027 p0030
  have p0032 := @g_vex y
  have p0033 :=
    @g_inex (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y) p0031
      p0032
  have p0034 :=
    @g_syl6eqelr
      (.all z (.all w (.all t (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
                (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))))))
      (syn_cins3k (.cv x))
      (syn_cin (syn_cxpk (syn_cpw1 (syn_c1c)) (syn_cxpk (syn_cvv) (syn_cvv))) (.cv y))
      (syn_cvv) p0025 p0033
  have freeVariableCertificate6 :
    y ∉ ((Wff.classMem (syn_cins3k (.cv x)) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0035 :=
    @g_exlimiv
      (.all z (.all w (.all t (syn_wb
              (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv w) (.cv t)))
                (.cv y)) (.classMem (syn_copk (.cv z) (.cv w)) (.cv x))))))
      (.classMem (syn_cins3k (.cv x)) (syn_cvv)) y freeVariableCertificate6 p0034
  have p0036 := Nominal.mp p0002 p0035
  have freeVariableCertificate7 : x ∉ ((Wff.classMem (syn_cins3k A) (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0037 :=
    @g_vtoclg (.classMem (syn_cins3k (.cv x)) (syn_cvv))
      (.classMem (syn_cins3k A) (syn_cvv)) x A V
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate7
      p0001 p0036
  exact p0037

@[expose]
noncomputable def g_ins2kex (A : Class)
    (hyp_inskex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cins2k A) (syn_cvv)) :=
  by
  have p0000 := @g_ins2kexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_inskex_1 p0000
  exact p0001

@[expose]
noncomputable def g_ins3kex (A : Class)
    (hyp_inskex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cins3k A) (syn_cvv)) :=
  by
  have p0000 := @g_ins3kexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_inskex_1 p0000
  exact p0001

@[expose]
noncomputable def g_cokexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_ccomk A B) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_ccomk A B))
  have p0001 := @g_ins2kexg A V
  have p0002 := @g_cnvkexg B W
  have p0003 := @g_ins3kexg (syn_ccnvk B) (syn_cvv)
  have p0004 :=
    @g_syl (.classMem B W) (.classMem (syn_ccnvk B) (syn_cvv))
      (.classMem (syn_cins3k (syn_ccnvk B)) (syn_cvv)) p0002 p0003
  have p0005 := @g_inexg (syn_cins2k A) (syn_cins3k (syn_ccnvk B)) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_syl2an (.classMem A V) (.classMem (syn_cins2k A) (syn_cvv))
      (.classMem (syn_cins3k (syn_ccnvk B)) (syn_cvv))
      (.classMem (syn_cin (syn_cins2k A) (syn_cins3k (syn_ccnvk B))) (syn_cvv))
      (.classMem B W) p0001 p0004 p0005
  have p0007 := @g_vvex
  have p0008 :=
    @g_imakexg (syn_cin (syn_cins2k A) (syn_cins3k (syn_ccnvk B))) (syn_cvv) (syn_cvv)
      (syn_cvv)
  have p0009 :=
    @g_sylancl (syn_wa (.classMem A V) (.classMem B W))
      (.classMem (syn_cin (syn_cins2k A) (syn_cins3k (syn_ccnvk B))) (syn_cvv))
      (.classMem (syn_cvv) (syn_cvv))
      (.classMem (syn_cimak (syn_cin (syn_cins2k A) (syn_cins3k (syn_ccnvk B))) (syn_cvv))
        (syn_cvv))
      p0006 p0007 p0008
  have p0010 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_ccomk A B)
      (syn_cimak (syn_cin (syn_cins2k A) (syn_cins3k (syn_ccnvk B))) (syn_cvv)) (syn_cvv)
      p0000 p0009
  exact p0010

@[expose]
noncomputable def g_cokex (A : Class) (B : Class)
    (hyp_cokex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_cokex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_ccomk A B) (syn_cvv)) :=
  by
  have p0000 := @g_cokexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_ccomk A B) (syn_cvv)) hyp_cokex_1 hyp_cokex_2 p0000
  exact p0001

@[expose]
noncomputable def g_imagekexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cimagek A) (syn_cvv))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cimagek A))
  have p0001 := @g_sikexg A V
  have p0002 := @g_cnvkexg (syn_csik A) (syn_cvv)
  have p0003 :=
    @g_syl (.classMem A V) (.classMem (syn_csik A) (syn_cvv))
      (.classMem (syn_ccnvk (syn_csik A)) (syn_cvv)) p0001 p0002
  have p0004 := @g_ssetkex
  have p0005 := @g_cokexg (syn_cssetk) (syn_ccnvk (syn_csik A)) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_mpan (.classMem (syn_cssetk) (syn_cvv))
      (.classMem (syn_ccnvk (syn_csik A)) (syn_cvv))
      (.classMem (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_syl (.classMem A V) (.classMem (syn_ccnvk (syn_csik A)) (syn_cvv))
      (.classMem (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))) (syn_cvv)) p0003 p0006
  have p0008 := @g_ins3kexg (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))) (syn_cvv)
  have p0009 :=
    @g_syl (.classMem A V)
      (.classMem (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))) (syn_cvv))
      (.classMem (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))) (syn_cvv))
      p0007 p0008
  have p0011 := @g_ins2kex (syn_cssetk) p0004
  have p0012 :=
    @g_symdifexg (syn_cins2k (syn_cssetk))
      (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))) (syn_cvv) (syn_cvv)
  have p0013 :=
    @g_mpan (.classMem (syn_cins2k (syn_cssetk)) (syn_cvv))
      (.classMem (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))) (syn_cvv))
      (.classMem (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cvv))
      p0011 p0012
  have p0014 :=
    @g_syl (.classMem A V)
      (.classMem (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))) (syn_cvv))
      (.classMem (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cvv))
      p0009 p0013
  have p0015 := @g_n_1cex
  have p0016 := @g_pw1ex (syn_c1c) p0015
  have p0017 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0016
  have p0018 :=
    @g_imakexg
      (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_cvv) (syn_cvv)
  have p0019 :=
    @g_mpan2
      (.classMem (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cvv))
      (.classMem (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_cvv))
      (.classMem (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cvv))
      p0017 p0018
  have p0020 :=
    @g_syl (.classMem A V)
      (.classMem (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A))))) (syn_cvv))
      (.classMem (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cvv))
      p0014 p0019
  have p0021 := @g_vvex
  have p0023 := @g_xpkex (syn_cvv) (syn_cvv) p0021 p0021
  have p0024 :=
    @g_difexg (syn_cxpk (syn_cvv) (syn_cvv))
      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_cvv) (syn_cvv)
  have p0025 :=
    @g_mpan (.classMem (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv))
      (.classMem (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cvv))
      (.classMem (syn_cdif (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk))
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cvv))
      p0023 p0024
  have p0026 :=
    @g_syl (.classMem A V)
      (.classMem (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))) (syn_cvv))
      (.classMem (syn_cdif (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk))
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cvv))
      p0020 p0025
  have p0027 :=
    @g_syl5eqel (.classMem A V) (syn_cimagek A)
      (syn_cdif (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_ccnvk (syn_csik A)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cvv) p0000 p0026
  exact p0027

@[expose]
noncomputable def g_imagekex (A : Class)
    (hyp_imagekex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cimagek A) (syn_cvv)) :=
  by
  have p0000 := @g_imagekexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_imagekex_1 p0000
  exact p0001

@[expose]
noncomputable def g_dfidk2 :
    Nominal.NPrf (.classEq (syn_cidk) (syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk)))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have p0000 := @g_idkssvvk
  have p0001 := @g_inss1 (syn_cssetk) (syn_ccnvk (syn_cssetk))
  have p0002 := @g_ssetkssvvk
  have p0003 :=
    @g_sstri (syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk))) (syn_cssetk)
      (syn_cxpk (syn_cvv) (syn_cvv)) p0001 p0002
  have p0004 := @g_eqss (.cv x) (.cv y)
  have p0005 := @g_vex x
  have p0006 := @g_vex y
  have p0007 := @g_opkelidkg (.cv x) (.cv y) (syn_cvv) (syn_cvv)
  have p0008_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
        (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) (syn_cidk)) (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cvv syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl
          syn_csn syn_cidk syn_wex
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
    @g_mp2an (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) (syn_cidk)) (.objEq x y)) p0005 p0006
      p0008_e02_recanon
  have p0009 := @g_elin (syn_copk (.cv x) (.cv y)) (syn_cssetk) (syn_ccnvk (syn_cssetk))
  have p0010 := @g_opkelssetkg (.cv x) (.cv y) (syn_cvv) (syn_cvv)
  have p0011 :=
    @g_mp2an (.classMem (.cv x) (syn_cvv)) (.classMem (.cv y) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) (syn_cssetk)) (syn_wss (.cv x) (.cv y)))
      p0005 p0006 p0010
  have p0012 := @g_opkelcnvk (.cv x) (.cv y) (syn_cssetk) p0005 p0006
  have p0013 := @g_opkelssetkg (.cv y) (.cv x) (syn_cvv) (syn_cvv)
  have p0014 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv y) (.cv x)) (syn_cssetk)) (syn_wss (.cv y) (.cv x)))
      p0006 p0005 p0013
  have p0015 :=
    @g_bitri (.classMem (syn_copk (.cv x) (.cv y)) (syn_ccnvk (syn_cssetk)))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cssetk)) (syn_wss (.cv y) (.cv x)) p0012
      p0014
  have p0016 :=
    @g_anbi12i (.classMem (syn_copk (.cv x) (.cv y)) (syn_cssetk))
      (syn_wss (.cv x) (.cv y))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_ccnvk (syn_cssetk)))
      (syn_wss (.cv y) (.cv x)) p0011 p0015
  have p0017 :=
    @g_bitri
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk))))
      (syn_wa (.classMem (syn_copk (.cv x) (.cv y)) (syn_cssetk))
        (.classMem (syn_copk (.cv x) (.cv y)) (syn_ccnvk (syn_cssetk))))
      (syn_wa (syn_wss (.cv x) (.cv y)) (syn_wss (.cv y) (.cv x))) p0009 p0016
  have p0018_e00_recanon :
    Nominal.NPrf
      (syn_wb (.objEq x y) (syn_wa (syn_wss (.cv x) (.cv y)) (syn_wss (.cv y) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
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
    @g_n_3bitr4i (.objEq x y) (syn_wa (syn_wss (.cv x) (.cv y)) (syn_wss (.cv y) (.cv x)))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cidk))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk))))
      p0018_e00_recanon p0008 p0017
  have freeVariableCertificate0 :
    x ∉ ((syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    y ∉ ((syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0019 :=
    @g_eqrelkriiv x y (syn_cidk) (syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk)))
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
      freeVariableCertificate0 freeVariableCertificate1
      (show x ≠ y from (by exact fresh_x_ne_y)) p0000 p0003 p0018
  exact p0019

@[expose]
noncomputable def g_idkex : Nominal.NPrf (.classMem (syn_cidk) (syn_cvv)) :=
  by
  have p0000 := @g_dfidk2
  have p0001 := @g_ssetkex
  have p0003 := @g_cnvkex (syn_cssetk) p0001
  have p0004 := @g_inex (syn_cssetk) (syn_ccnvk (syn_cssetk)) p0001 p0003
  have p0005 :=
    @g_eqeltri (syn_cidk) (syn_cin (syn_cssetk) (syn_ccnvk (syn_cssetk))) (syn_cvv) p0000
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

@[expose]
noncomputable def g_dfuni3 (A : Class) :
    Nominal.NPrf
      (.classEq (syn_cuni A) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A))) :=
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
  have p0000 := @g_vex y
  have p0001 := @g_snex (.cv x)
  have p0002 := @g_opkelcnvk (.cv y) (syn_csn (.cv x)) (syn_cssetk) p0000 p0001
  have p0003 := @g_vex x
  have p0004 := @g_elssetk (.cv x) (.cv y) p0003 p0000
  have p0005_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
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
    @g_bitri (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y) p0002
      p0005_e01_recanon
  have p0006 :=
    @g_rexbii (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_cssetk)))
      (.objMem x y) y A p0005
  have p0007 := @g_eluni1 (.cv x) (syn_cimak (syn_ccnvk (syn_cssetk)) A) p0003
  have freeVariableCertificate0 : y ∉ ((syn_ccnvk (syn_cssetk))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((syn_csn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have p0008 :=
    @g_elimak y (syn_ccnvk (syn_cssetk)) A (syn_csn (.cv x)) freeVariableCertificate0
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate1
      p0001
  have p0009 :=
    @g_bitri (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A)))
      (.classMem (syn_csn (.cv x)) (syn_cimak (syn_ccnvk (syn_cssetk)) A))
      (syn_wrex y A (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_cssetk))))
      p0007 p0008
  have freeVariableCertificate2 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0010 :=
    @g_eluni2 y (.cv x) A freeVariableCertificate2
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0011_e02_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_cuni A)) (syn_wrex y A (.objMem x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa syn_wrex
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
    @g_n_3bitr4ri
      (syn_wrex y A (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_cssetk))))
      (syn_wrex y A (.objMem x y))
      (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A)))
      (.classMem (.cv x) (syn_cuni A)) p0006 p0009 p0011_e02_recanon
  have freeVariableCertificate3 :
    x ∉ ((syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0012 :=
    @g_eqriv x (syn_cuni A) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A))
      (by
        exact
          (show x ∉ ((syn_cuni A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate3 p0011
  exact p0012

@[expose]
noncomputable def g_uniexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cuni A) (syn_cvv))) :=
  by
  have p0000 := @g_dfuni3 A
  have p0001 := @g_ssetkex
  have p0002 := @g_cnvkex (syn_cssetk) p0001
  have p0003 := @g_imakexg (syn_ccnvk (syn_cssetk)) A (syn_cvv) V
  have p0004 :=
    @g_mpan (.classMem (syn_ccnvk (syn_cssetk)) (syn_cvv)) (.classMem A V)
      (.classMem (syn_cimak (syn_ccnvk (syn_cssetk)) A) (syn_cvv)) p0002 p0003
  have p0005 := @g_uni1exg (syn_cimak (syn_ccnvk (syn_cssetk)) A) (syn_cvv)
  have p0006 :=
    @g_syl (.classMem A V) (.classMem (syn_cimak (syn_ccnvk (syn_cssetk)) A) (syn_cvv))
      (.classMem (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A)) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_syl5eqel (.classMem A V) (syn_cuni A)
      (syn_cuni1 (syn_cimak (syn_ccnvk (syn_cssetk)) A)) (syn_cvv) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_uniex (A : Class)
    (hyp_uniex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cuni A) (syn_cvv)) :=
  by
  have p0000 := @g_uniexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_uniex_1 p0000
  exact p0001

@[expose]
noncomputable def g_dfint3 (A : Class) :
    Nominal.NPrf
      (.classEq (syn_cint A)
        (syn_ccompl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)))) :=
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
  have p0000 := @g_vex x
  have p0001 :=
    @g_eluni1 (.cv x) (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A) p0000
  have p0002 := @g_snex (.cv x)
  have freeVariableCertificate0 : y ∉ ((syn_ccnvk (syn_ccompl (syn_cssetk)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((syn_csn (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
      not_false_eq_true]
  have p0003 :=
    @g_elimak y (syn_ccnvk (syn_ccompl (syn_cssetk))) A (syn_csn (.cv x))
      freeVariableCertificate0 (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      freeVariableCertificate1 p0002
  have p0004 :=
    @g_bitri
      (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)))
      (.classMem (syn_csn (.cv x)) (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A))
      (syn_wrex y A (.classMem (syn_copk (.cv y) (syn_csn (.cv x)))
          (syn_ccnvk (syn_ccompl (syn_cssetk)))))
      p0001 p0003
  have p0005 := @g_vex y
  have p0006 :=
    @g_opkelcnvk (.cv y) (syn_csn (.cv x)) (syn_ccompl (syn_cssetk)) p0005 p0002
  have p0007 := @g_opkex (syn_csn (.cv x)) (.cv y)
  have p0008 := @g_elcompl (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk) p0007
  have p0009 := @g_elssetk (.cv x) (.cv y) p0000 p0005
  have p0010_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
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
    @g_notbii (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y)
      p0010_e00_recanon
  have p0011 :=
    @g_n_3bitri
      (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_ccompl (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_ccompl (syn_cssetk)))
      (.neg (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)))
      (.neg (.objMem x y)) p0006 p0008 p0010
  have p0012 :=
    @g_rexbii
      (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk (syn_ccompl (syn_cssetk))))
      (.neg (.objMem x y)) y A p0011
  have p0013 := @g_rexnal (.objMem x y) y A
  have p0014 :=
    @g_n_3bitri
      (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)))
      (syn_wrex y A (.classMem (syn_copk (.cv y) (syn_csn (.cv x)))
          (syn_ccnvk (syn_ccompl (syn_cssetk)))))
      (syn_wrex y A (.neg (.objMem x y))) (.neg (syn_wral y A (.objMem x y))) p0004 p0012
      p0013
  have p0015 :=
    @g_con2bii
      (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)))
      (syn_wral y A (.objMem x y)) p0014
  have freeVariableCertificate2 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0016 :=
    @g_elint2 y (.cv x) A freeVariableCertificate2
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) p0000
  have p0017 :=
    @g_elcompl (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A))
      p0000
  have p0018_e01_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_cint A)) (syn_wral y A (.objMem x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cint syn_wral
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
    @g_n_3bitr4i (syn_wral y A (.objMem x y))
      (.neg (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A))))
      (.classMem (.cv x) (syn_cint A))
      (.classMem (.cv x)
        (syn_ccompl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A))))
      p0015 p0018_e01_recanon p0017
  have freeVariableCertificate3 :
    x ∉
      ((syn_ccompl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0019 :=
    @g_eqriv x (syn_cint A)
      (syn_ccompl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)))
      (by
        exact
          (show x ∉ ((syn_cint A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate3 p0018
  exact p0019

@[expose]
noncomputable def g_intexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cint A) (syn_cvv))) :=
  by
  have p0000 := @g_dfint3 A
  have p0001 := @g_ssetkex
  have p0002 := @g_complex (syn_cssetk) p0001
  have p0003 := @g_cnvkex (syn_ccompl (syn_cssetk)) p0002
  have p0004 := @g_imakexg (syn_ccnvk (syn_ccompl (syn_cssetk))) A (syn_cvv) V
  have p0005 :=
    @g_mpan (.classMem (syn_ccnvk (syn_ccompl (syn_cssetk))) (syn_cvv)) (.classMem A V)
      (.classMem (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A) (syn_cvv)) p0003
      p0004
  have p0006 := @g_uni1exg (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A) (syn_cvv)
  have p0007 :=
    @g_complexg (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)) (syn_cvv)
  have p0008 :=
    @g_n_3syl (.classMem A V)
      (.classMem (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A) (syn_cvv))
      (.classMem (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)) (syn_cvv))
      (.classMem (syn_ccompl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)))
        (syn_cvv))
      p0005 p0006 p0007
  have p0009 :=
    @g_syl5eqel (.classMem A V) (syn_cint A)
      (syn_ccompl (syn_cuni1 (syn_cimak (syn_ccnvk (syn_ccompl (syn_cssetk))) A)))
      (syn_cvv) p0000 p0008
  exact p0009

@[expose]
noncomputable def g_intex (A : Class)
    (hyp_intex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cint A) (syn_cvv)) :=
  by
  have p0000 := @g_intexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_intex_1 p0000
  exact p0001

@[expose]
noncomputable def g_setswith (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.classEq (.cab x (.classMem A (.cv x)))
        (syn_cif (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A)))
          (syn_c0))) :=
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
  have p0000 := @g_snex A
  have p0001 := @g_opkeq1 (.cv y) (syn_csn A) (.cv x)
  have p0002 :=
    @g_eleq1d (.classEq (.cv y) (syn_csn A)) (syn_copk (.cv y) (.cv x))
      (syn_copk (syn_csn A) (.cv x)) (syn_cssetk) p0001
  have freeVariableCertificate0 :
    y ∉ ((Wff.classMem (syn_copk (syn_csn A) (.cv x)) (syn_cssetk))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_not_A, fresh_y_ne_x, or_false,
      not_false_eq_true]
  have p0003 :=
    @g_rexsn (.classMem (syn_copk (.cv y) (.cv x)) (syn_cssetk))
      (.classMem (syn_copk (syn_csn A) (.cv x)) (syn_cssetk)) y (syn_csn A)
      (by
        exact
          (show y ∉ ((syn_csn A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
      freeVariableCertificate0 p0000 p0002
  have p0004 := @g_vex x
  have p0005 := @g_elssetkg A (.cv x) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_mpan2 (.classMem A (syn_cvv)) (.classMem (.cv x) (syn_cvv))
      (syn_wb (.classMem (syn_copk (syn_csn A) (.cv x)) (syn_cssetk)) (.classMem A (.cv x)))
      p0004 p0005
  have p0007 :=
    @g_syl5rbb
      (syn_wrex y (syn_csn (syn_csn A)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cssetk)))
      (.classMem (syn_copk (syn_csn A) (.cv x)) (syn_cssetk)) (.classMem A (syn_cvv))
      (.classMem A (.cv x)) p0003 p0006
  have freeVariableCertificate1 : x ∉ ((Wff.classMem A (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have p0008 :=
    @g_abbidv (.classMem A (syn_cvv)) (.classMem A (.cv x))
      (syn_wrex y (syn_csn (syn_csn A)) (.classMem (syn_copk (.cv y) (.cv x)) (syn_cssetk)))
      x freeVariableCertificate1 p0007
  have freeVariableCertificate2 : x ∉ ((syn_csn (syn_csn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, dv_A_x,
      not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((syn_csn (syn_csn A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_y_not_A,
      not_false_eq_true]
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_imak x y
      (syn_cssetk) (syn_csn (syn_csn A))
      (by
        exact
          (show x ∉ ((syn_cssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show y ∉ ((syn_cssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate2 freeVariableCertificate3
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0010 :=
    @g_syl6eqr (.classMem A (syn_cvv)) (.cab x (.classMem A (.cv x)))
      (.cab x (syn_wrex y (syn_csn (syn_csn A))
          (.classMem (syn_copk (.cv y) (.cv x)) (syn_cssetk))))
      (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) p0008 p0009
  have p0011 :=
    @g_iftrue (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A)))
      (syn_c0)
  have p0012 :=
    @g_eqtr4d (.classMem A (syn_cvv)) (.cab x (.classMem A (.cv x)))
      (syn_cimak (syn_cssetk) (syn_csn (syn_csn A)))
      (syn_cif (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) (syn_c0))
      p0010 p0011
  have p0013 := @g_elex A (.cv x)
  have p0014 := @g_con3i (.classMem A (.cv x)) (.classMem A (syn_cvv)) p0013
  have freeVariableCertificate4 : x ∉ ((Wff.neg (.classMem A (syn_cvv)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have p0015 :=
    @g_alrimiv (.neg (.classMem A (syn_cvv))) (.neg (.classMem A (.cv x))) x
      freeVariableCertificate4 p0014
  have p0016 := @g_ab0 (.classMem A (.cv x)) x
  have p0017 :=
    @g_sylibr (.neg (.classMem A (syn_cvv))) (.all x (.neg (.classMem A (.cv x))))
      (.classEq (.cab x (.classMem A (.cv x))) (syn_c0)) p0015 p0016
  have p0018 :=
    @g_iffalse (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A)))
      (syn_c0)
  have p0019 :=
    @g_eqtr4d (.neg (.classMem A (syn_cvv))) (.cab x (.classMem A (.cv x))) (syn_c0)
      (syn_cif (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) (syn_c0))
      p0017 p0018
  have p0020 :=
    @g_pm2_61i (.classMem A (syn_cvv))
      (.classEq (.cab x (.classMem A (.cv x)))
        (syn_cif (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A)))
          (syn_c0)))
      p0012 p0019
  exact p0020

@[expose]
noncomputable def g_setswithex (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf (.classMem (.cab x (.classMem A (.cv x))) (syn_cvv)) :=
  by
  have p0000 := @g_setswith x A (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
  have p0001 := @g_ssetkex
  have p0002 := @g_snex (syn_csn A)
  have p0003 := @g_imakex (syn_cssetk) (syn_csn (syn_csn A)) p0001 p0002
  have p0004 := @g_n_0ex
  have p0005 :=
    @g_ifex (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A)))
      (syn_c0) p0003 p0004
  have p0006 :=
    @g_eqeltri (.cab x (.classMem A (.cv x)))
      (syn_cif (.classMem A (syn_cvv)) (syn_cimak (syn_cssetk) (syn_csn (syn_csn A))) (syn_c0))
      (syn_cvv) p0000 p0005
  exact p0006

@[expose]
noncomputable def g_ndisjrelk (A : Class) (B : Class)
    (hyp_ndisjrelk_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_ndisjrelk_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk A B)
          (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_wne (syn_cin A B) (syn_c0))) :=
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
  have p0000 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0001 := @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B)
  have p0002 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (.cv t) (syn_copk A B))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) p0001
  have freeVariableCertificate0 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
      not_false_eq_true]
  have freeVariableCertificate1 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))).fv :=
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
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk A B))
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))
      t (syn_csn (syn_csn (syn_csn (.cv x)))) freeVariableCertificate0
      freeVariableCertificate1 p0000 p0002
  have p0004 :=
    @g_elin (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
      (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))
  have p0005 := @g_snex (.cv x)
  have p0006 :=
    @g_otkelins3k (syn_csn (.cv x)) A B (syn_cssetk) p0005 hyp_ndisjrelk_1 hyp_ndisjrelk_2
  have p0007 := @g_vex x
  have p0008 := @g_elssetk (.cv x) A p0007 hyp_ndisjrelk_1
  have p0009 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_cins3k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) A) (syn_cssetk)) (.classMem (.cv x) A) p0006
      p0008
  have p0010 :=
    @g_otkelins2k (syn_csn (.cv x)) A B (syn_cssetk) p0005 hyp_ndisjrelk_1 hyp_ndisjrelk_2
  have p0011 := @g_elssetk (.cv x) B p0007 hyp_ndisjrelk_2
  have p0012 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B) p0010
      p0011
  have p0013 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_cins3k (syn_cssetk)))
      (.classMem (.cv x) A)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_cins2k (syn_cssetk)))
      (.classMem (.cv x) B) p0009 p0012
  have p0014 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
          (syn_cins3k (syn_cssetk)))
        (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
          (syn_cins2k (syn_cssetk))))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) p0004 p0013
  have p0015 :=
    @g_bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk A B))
            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk A B))
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) p0003 p0014
  have p0016 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk A B))
            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0015
  have p0017 := @g_opkex A B
  have freeVariableCertificate2 :
    t ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate3 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate4 : t ∉ ((syn_copk A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk, Finset.mem_union,
      fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true]
  have p0018 :=
    @g_elimak t (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk A B) freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4 p0017
  have freeVariableCertificate5 : x ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_t, not_false_eq_true]
  have p0019 := @g_elpw121c x (.cv t) freeVariableCertificate5
  have p0020 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
      (.classMem (syn_copk (.cv t) (syn_copk A B))
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))
      p0019
  have freeVariableCertificate6 :
    x ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk A B))
          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))).fv :=
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
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (.classMem (syn_copk (.cv t) (syn_copk A B))
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))
      x freeVariableCertificate6
  have p0022 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk A B))
          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
        (.classMem (syn_copk (.cv t) (syn_copk A B))
          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk A B))
            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))))
      p0020 p0021
  have p0023 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk A B))
          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk A B))
            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))))
      t p0022
  have p0024 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk A B))
          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))))
  have p0025 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
        (.classMem (syn_copk (.cv t) (syn_copk A B))
          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))
      x t
  have p0026 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk A B))
            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))))))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk A B))
              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk A B))
          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk A B))
              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))))
      p0023 p0024 p0025
  have p0027 :=
    @g_bitri
      (.classMem (syn_copk A B)
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) (.classMem (syn_copk (.cv t) (syn_copk A B))
          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk A B))
              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))))
      p0018 p0026
  have freeVariableCertificate7 : x ∉ ((syn_cin A B)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0028 := @g_n0 x (syn_cin A B) freeVariableCertificate7
  have p0029 := @g_elin (.cv x) A B
  have p0030 :=
    @g_exbii (.classMem (.cv x) (syn_cin A B))
      (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)) x p0029
  have p0031 :=
    @g_bitri (syn_wne (syn_cin A B) (syn_c0))
      (syn_wex x (.classMem (.cv x) (syn_cin A B)))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B))) p0028 p0030
  have p0032 :=
    @g_n_3bitr4i
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk A B))
              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))))))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (.classMem (.cv x) B)))
      (.classMem (syn_copk A B)
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wne (syn_cin A B) (syn_c0)) p0016 p0027 p0031
  exact p0032

@[expose]
noncomputable def g_abexv (ph : Wff) (x : Var) (dv_ph_x : x ∉ ph.fv) :
    Nominal.NPrf (.classMem (.cab x ph) (syn_cvv)) :=
  by
  have p0000 := @g_abvor0 ph x (by exact (show x ∉ (ph).fv from (by exact dv_ph_x)))
  have p0001 := @g_vvex
  have p0002 := @g_eleq1 (.cab x ph) (syn_cvv) (syn_cvv)
  have p0003 :=
    @g_mpbiri (.classEq (.cab x ph) (syn_cvv)) (.classMem (.cab x ph) (syn_cvv))
      (.classMem (syn_cvv) (syn_cvv)) p0001 p0002
  have p0004 := @g_n_0ex
  have p0005 := @g_eleq1 (.cab x ph) (syn_c0) (syn_cvv)
  have p0006 :=
    @g_mpbiri (.classEq (.cab x ph) (syn_c0)) (.classMem (.cab x ph) (syn_cvv))
      (.classMem (syn_c0) (syn_cvv)) p0004 p0005
  have p0007 :=
    @g_jaoi (.classEq (.cab x ph) (syn_cvv)) (.classMem (.cab x ph) (syn_cvv))
      (.classEq (.cab x ph) (syn_c0)) p0003 p0006
  have p0008 := Nominal.mp p0000 p0007
  exact p0008

@[expose]
noncomputable def g_unipw1 (A : Class) :
    Nominal.NPrf (.classEq (syn_cuni (syn_cpw1 A)) A) :=
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
    @g_eluni y (.cv x) (syn_cpw1 A) freeVariableCertificate0
      (by
        exact
          (show y ∉ ((syn_cpw1 A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
              exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))))
  have freeVariableCertificate1 : z ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_y, not_false_eq_true]
  have p0001 :=
    @g_elpw1 z (.cv y) A freeVariableCertificate1
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
  have p0002 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 A))
      (syn_wrex z A (.classEq (.cv y) (syn_csn (.cv z)))) (.objMem x y) p0001
  have p0003 := @g_ancom (.objMem x y) (.classMem (.cv y) (syn_cpw1 A))
  have freeVariableCertificate2 : z ∉ ((Wff.objMem x y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_insert,
      Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true]
  have p0004 :=
    @g_r19_41v (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y) z A
      freeVariableCertificate2
  have p0005 :=
    @g_n_3bitr4i (syn_wa (.classMem (.cv y) (syn_cpw1 A)) (.objMem x y))
      (syn_wa (syn_wrex z A (.classEq (.cv y) (syn_csn (.cv z)))) (.objMem x y))
      (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpw1 A)))
      (syn_wrex z A (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y))) p0002
      p0003 p0004
  have p0006 :=
    @g_exbii (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpw1 A)))
      (syn_wrex z A (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y))) y p0005
  have freeVariableCertificate3 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have p0007 :=
    @g_risset z (.cv x) A freeVariableCertificate3
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
  have p0008 := @g_snex (.cv z)
  have p0009 := @g_eleq2 (.cv y) (syn_csn (.cv z)) (.cv x)
  have p0010_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (syn_csn (.cv z)))
        (syn_wb (.objMem x y) (.classMem (.cv x) (syn_csn (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn syn_wb
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
  have freeVariableCertificate4 : y ∉ ((syn_csn (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_z,
      not_false_eq_true]
  have freeVariableCertificate5 : y ∉ ((Wff.classMem (.cv x) (syn_csn (.cv z)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, or_false, not_false_eq_true]
  have p0010 :=
    @g_ceqsexv (.objMem x y) (.classMem (.cv x) (syn_csn (.cv z))) y (syn_csn (.cv z))
      freeVariableCertificate4 freeVariableCertificate5 p0008 p0010_e01_recanon
  have freeVariableCertificate6 : x ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_z, not_false_eq_true]
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x (.cv z)
      freeVariableCertificate6
  have p0012_e00_recanon :
    Nominal.NPrf (.classEq (syn_csn (.cv z)) (.cab x (.objEq x z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0011
  have p0012 := @g_eqabri (.objEq x z) x (syn_csn (.cv z)) p0012_e00_recanon
  have p0013 := @g_equcom x z
  have p0014 :=
    @g_n_3bitri (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y)))
      (.classMem (.cv x) (syn_csn (.cv z))) (.objEq x z) (.objEq z x) p0010 p0012 p0013
  have p0015 :=
    @g_rexbii (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y)))
      (.objEq z x) z A p0014
  have p0016 :=
    @g_rexcom4 (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y)) z y A
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (show z ≠ y from (by exact fresh_z_ne_y))
  have p0017_e00_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv x) A) (syn_wrex z A (.objEq z x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
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
    @g_n_3bitr2ri (.classMem (.cv x) A) (syn_wrex z A (.objEq z x))
      (syn_wrex z A (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y))))
      (syn_wex y (syn_wrex z A (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y))))
      p0017_e00_recanon p0015 p0016
  have p0018_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv x) (syn_cuni (syn_cpw1 A)))
        (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpw1 A))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa syn_cpw1 syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cpw syn_wss syn_c1c
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
    @g_n_3bitri (.classMem (.cv x) (syn_cuni (syn_cpw1 A)))
      (syn_wex y (syn_wa (.objMem x y) (.classMem (.cv y) (syn_cpw1 A))))
      (syn_wex y (syn_wrex z A (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (.objMem x y))))
      (.classMem (.cv x) A) p0018_e00_recanon p0006 p0017
  have freeVariableCertificate7 : x ∉ ((syn_cuni (syn_cpw1 A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_A,
      not_false_eq_true]
  have p0019 :=
    @g_eqriv x (syn_cuni (syn_cpw1 A)) A freeVariableCertificate7
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) p0018
  exact p0019

@[expose]
noncomputable def g_pw1exb (A : Class) :
    Nominal.NPrf (syn_wb (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem A (syn_cvv))) :=
  by
  have p0000 := @g_unipw1 A
  have p0001 := @g_uniexg (syn_cpw1 A) (syn_cvv)
  have p0002 :=
    @g_syl5eqelr (.classMem (syn_cpw1 A) (syn_cvv)) A (syn_cuni (syn_cpw1 A)) (syn_cvv)
      p0000 p0001
  have p0003 := @g_pw1exg A (syn_cvv)
  have p0004 :=
    @g_impbii (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem A (syn_cvv)) p0002 p0003
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

@[expose]
noncomputable def g_dfpw2 (A : Class) :
    Nominal.NPrf
      (.classEq (syn_cpw A) (syn_ccompl
          (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)))) :=
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
  have p0000 := @g_vex x
  have freeVariableCertificate0 :
    t ∉ ((syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))).fv := by
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
    @g_elimak t (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)
      (.cv x) freeVariableCertificate0
      (by
        exact
          (show t ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 p0000
  have freeVariableCertificate2 : y ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_t, not_false_eq_true]
  have p0002 := @g_el1c y (.cv t) freeVariableCertificate2
  have p0003 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c))
      (syn_wex y (.classEq (.cv t) (syn_csn (.cv y))))
      (.classMem (syn_copk (.cv t) (.cv x))
        (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))
      p0002
  have freeVariableCertificate3 :
    y ∉
      ((Wff.classMem (syn_copk (.cv t) (.cv x))
          (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))).fv :=
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
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv y)))
      (.classMem (syn_copk (.cv t) (.cv x))
        (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))
      y freeVariableCertificate3
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv x))
          (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))
      (syn_wa (syn_wex y (.classEq (.cv t) (syn_csn (.cv y))))
        (.classMem (syn_copk (.cv t) (.cv x))
          (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))
      (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (.cv y)))
          (.classMem (syn_copk (.cv t) (.cv x))
            (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv x))
          (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))
      (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (.cv y)))
          (.classMem (syn_copk (.cv t) (.cv x))
            (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))))
      t p0005
  have p0007 :=
    (Nominal.biimpRefl (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv x))
          (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))))
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) (.classMem (syn_copk (.cv t) (.cv x))
          (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))
      y t
  have p0009 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv x))
            (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))))
      (syn_wex t (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (.cv y)))
            (.classMem (syn_copk (.cv t) (.cv x))
              (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))))
      (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv x))
          (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))
      (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv y)))
            (.classMem (syn_copk (.cv t) (.cv x))
              (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))))
      p0006 p0007 p0008
  have p0010 :=
    @g_bitri
      (.classMem (.cv x)
        (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)))
      (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv x))
          (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))
      (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv y)))
            (.classMem (syn_copk (.cv t) (.cv x))
              (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))))
      p0001 p0009
  have p0011 := @g_snex (.cv y)
  have p0012 := @g_opkeq1 (.cv t) (syn_csn (.cv y)) (.cv x)
  have p0013 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv y))) (syn_copk (.cv t) (.cv x))
      (syn_copk (syn_csn (.cv y)) (.cv x))
      (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) p0012
  have freeVariableCertificate4 : t ∉ ((syn_csn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
      not_false_eq_true]
  have freeVariableCertificate5 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (.cv y)) (.cv x))
          (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))).fv :=
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
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (.cv x))
        (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x))
        (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))
      t (syn_csn (.cv y)) freeVariableCertificate4 freeVariableCertificate5 p0011 p0013
  have p0015 :=
    @g_eldif (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cssetk)
      (syn_cxpk (syn_cpw1 A) (syn_cvv))
  have p0016 := @g_vex y
  have p0017 := @g_elssetk (.cv y) (.cv x) p0016 p0000
  have p0018 := @g_opkelxpk (syn_csn (.cv y)) (.cv x) (syn_cpw1 A) (syn_cvv) p0011 p0000
  have p0019 :=
    @g_mpbiran2
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cxpk (syn_cpw1 A) (syn_cvv)))
      (.classMem (syn_csn (.cv y)) (syn_cpw1 A)) (.classMem (.cv x) (syn_cvv)) p0000 p0018
  have p0020 := @g_snelpw1 (.cv y) A
  have p0021 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cxpk (syn_cpw1 A) (syn_cvv)))
      (.classMem (syn_csn (.cv y)) (syn_cpw1 A)) (.classMem (.cv y) A) p0019 p0020
  have p0022 :=
    @g_notbii
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cxpk (syn_cpw1 A) (syn_cvv)))
      (.classMem (.cv y) A) p0021
  have p0023_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cssetk)) (.objMem y x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
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
    @g_anbi12i (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cssetk)) (.objMem y x)
      (.neg (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cxpk (syn_cpw1 A) (syn_cvv))))
      (.neg (.classMem (.cv y) A)) p0023_e00_recanon p0022
  have p0024 := @g_annim (.objMem y x) (.classMem (.cv y) A)
  have p0025 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x))
        (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cssetk)) (.neg
          (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))
      (syn_wa (.objMem y x) (.neg (.classMem (.cv y) A)))
      (.neg (.imp (.objMem y x) (.classMem (.cv y) A))) p0015 p0023 p0024
  have p0026 :=
    @g_bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv y)))
          (.classMem (syn_copk (.cv t) (.cv x))
            (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))))
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x))
        (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))
      (.neg (.imp (.objMem y x) (.classMem (.cv y) A))) p0014 p0025
  have p0027 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv y)))
          (.classMem (syn_copk (.cv t) (.cv x))
            (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))))))
      (.neg (.imp (.objMem y x) (.classMem (.cv y) A))) y p0026
  have p0028 := @g_exnal (.imp (.objMem y x) (.classMem (.cv y) A)) y
  have p0029 :=
    @g_n_3bitri
      (.classMem (.cv x)
        (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)))
      (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv y)))
            (.classMem (syn_copk (.cv t) (.cv x))
              (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))))))
      (syn_wex y (.neg (.imp (.objMem y x) (.classMem (.cv y) A))))
      (.neg (.all y (.imp (.objMem y x) (.classMem (.cv y) A)))) p0010 p0027 p0028
  have p0030 :=
    @g_con2bii
      (.classMem (.cv x)
        (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)))
      (.all y (.imp (.objMem y x) (.classMem (.cv y) A))) p0029
  have p0031 := @g_elpw (.cv x) A p0000
  have freeVariableCertificate6 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0032 :=
    @g_dfss2 y (.cv x) A freeVariableCertificate6
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
  have p0033_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wss (.cv x) A) (.all y (.imp (.objMem y x) (.classMem (.cv y) A)))) :=
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
    @g_bitri (.classMem (.cv x) (syn_cpw A)) (syn_wss (.cv x) A)
      (.all y (.imp (.objMem y x) (.classMem (.cv y) A))) p0031 p0033_e01_recanon
  have p0034 :=
    @g_elcompl (.cv x)
      (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))
      p0000
  have p0035 :=
    @g_n_3bitr4i (.all y (.imp (.objMem y x) (.classMem (.cv y) A)))
      (.neg (.classMem (.cv x)
          (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))))
      (.classMem (.cv x) (syn_cpw A))
      (.classMem (.cv x) (syn_ccompl
          (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))))
      p0030 p0033 p0034
  have freeVariableCertificate7 :
    x ∉
      ((syn_ccompl (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)))
            (syn_c1c)))).fv :=
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
    @g_eqriv x (syn_cpw A)
      (syn_ccompl
        (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)))
      (by
        exact
          (show x ∉ ((syn_cpw A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw];
              exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))))
      freeVariableCertificate7 p0035
  exact p0036

@[expose]
noncomputable def g_pwexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cpw A) (syn_cvv))) :=
  by
  have p0000 := @g_dfpw2 A
  have p0001 := @g_ssetkex
  have p0002 := @g_pw1exg A V
  have p0003 := @g_vvex
  have p0004 := @g_xpkexg (syn_cpw1 A) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_sylancl (.classMem A V) (.classMem (syn_cpw1 A) (syn_cvv))
      (.classMem (syn_cvv) (syn_cvv))
      (.classMem (syn_cxpk (syn_cpw1 A) (syn_cvv)) (syn_cvv)) p0002 p0003 p0004
  have p0006 :=
    @g_difexg (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv)) (syn_cvv) (syn_cvv)
  have p0007 :=
    @g_sylancr (.classMem A V) (.classMem (syn_cssetk) (syn_cvv))
      (.classMem (syn_cxpk (syn_cpw1 A) (syn_cvv)) (syn_cvv))
      (.classMem (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_cvv))
      p0001 p0005 p0006
  have p0008 := @g_n_1cex
  have p0009 :=
    @g_imakexg (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)
      (syn_cvv) (syn_cvv)
  have p0010 :=
    @g_sylancl (.classMem A V)
      (.classMem (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_cvv))
      (.classMem (syn_c1c) (syn_cvv))
      (.classMem (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))
        (syn_cvv))
      p0007 p0008 p0009
  have p0011 :=
    @g_complexg
      (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))
      (syn_cvv)
  have p0012 :=
    @g_syl (.classMem A V)
      (.classMem (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c))
        (syn_cvv))
      (.classMem (syn_ccompl
          (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)))
        (syn_cvv))
      p0010 p0011
  have p0013 :=
    @g_syl5eqel (.classMem A V) (syn_cpw A)
      (syn_ccompl
        (syn_cimak (syn_cdif (syn_cssetk) (syn_cxpk (syn_cpw1 A) (syn_cvv))) (syn_c1c)))
      (syn_cvv) p0000 p0012
  exact p0013

@[expose]
noncomputable def g_pwex (A : Class) (hyp_pwex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cpw A) (syn_cvv)) :=
  by
  have p0000 := @g_pwexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_pwex_1 p0000
  exact p0001

@[expose]
noncomputable def g_eqpw1uni (A : Class) :
    Nominal.NPrf (.imp (syn_wss A (syn_c1c)) (.classEq A (syn_cpw1 (syn_cuni A)))) :=
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
  have p0000 := @g_ssel A (syn_c1c) (.cv x)
  have p0001 := @g_pw1ss1c (syn_cuni A)
  have p0002 := @g_sseli (syn_cpw1 (syn_cuni A)) (syn_c1c) (.cv x) p0001
  have p0003 :=
    @g_a1i
      (.imp (.classMem (.cv x) (syn_cpw1 (syn_cuni A))) (.classMem (.cv x) (syn_c1c)))
      (syn_wss A (syn_c1c)) p0002
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0004 := @g_el1c y (.cv x) freeVariableCertificate0
  have p0005 := @g_vex y
  have p0006 := @g_snid (.cv y) p0005
  have p0007 := @g_eleq2 (.cv x) (syn_csn (.cv y)) (.cv y)
  have p0008_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (syn_csn (.cv y)))
        (syn_wb (.objMem y x) (.classMem (.cv y) (syn_csn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn syn_wb
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
  have freeVariableCertificate1 : x ∉ ((syn_csn (.cv y))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_y,
      not_false_eq_true]
  have freeVariableCertificate2 : x ∉ ((Wff.classMem (.cv y) (syn_csn (.cv y)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, fresh_x_ne_y, or_false, not_false_eq_true]
  have p0008 :=
    @g_rspcev (.objMem y x) (.classMem (.cv y) (syn_csn (.cv y))) x (syn_csn (.cv y)) A
      freeVariableCertificate1 (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      freeVariableCertificate2 p0008_e00_recanon
  have p0009 :=
    @g_mpan2 (.classMem (syn_csn (.cv y)) A) (.classMem (.cv y) (syn_csn (.cv y)))
      (syn_wrex x A (.objMem y x)) p0006 p0008
  have freeVariableCertificate3 : z ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_x, not_false_eq_true]
  have p0010 := @g_el1c z (.cv x) freeVariableCertificate3
  have freeVariableCertificate4 : y ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_z, not_false_eq_true]
  have p0011 := @g_elsn y (.cv z) freeVariableCertificate4
  have p0012 := @g_sneq (.cv y) (.cv z)
  have p0013_e00_recanon :
    Nominal.NPrf (.imp (.objEq y z) (.classEq (syn_csn (.cv y)) (syn_csn (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0013 :=
    @g_eleq1d (.objEq y z) (syn_csn (.cv y)) (syn_csn (.cv z)) A p0013_e00_recanon
  have p0014_e00_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv y) (syn_csn (.cv z))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
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
    @g_sylbi (.classMem (.cv y) (syn_csn (.cv z))) (.objEq y z)
      (syn_wb (.classMem (syn_csn (.cv y)) A) (.classMem (syn_csn (.cv z)) A))
      p0014_e00_recanon p0013
  have p0015 :=
    @g_biimprcd (.classMem (.cv y) (syn_csn (.cv z))) (.classMem (syn_csn (.cv y)) A)
      (.classMem (syn_csn (.cv z)) A) p0014
  have p0016 := @g_eleq1 (.cv x) (syn_csn (.cv z)) A
  have p0017 := @g_eleq2 (.cv x) (syn_csn (.cv z)) (.cv y)
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (syn_csn (.cv z)))
        (syn_wb (.objMem y x) (.classMem (.cv y) (syn_csn (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn syn_wb
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
    @g_imbi1d (.classEq (.cv x) (syn_csn (.cv z))) (.objMem y x)
      (.classMem (.cv y) (syn_csn (.cv z))) (.classMem (syn_csn (.cv y)) A)
      p0018_e00_recanon
  have p0019 :=
    @g_imbi12d (.classEq (.cv x) (syn_csn (.cv z))) (.classMem (.cv x) A)
      (.classMem (syn_csn (.cv z)) A) (.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A))
      (.imp (.classMem (.cv y) (syn_csn (.cv z))) (.classMem (syn_csn (.cv y)) A)) p0016
      p0018
  have p0020 :=
    @g_mpbiri (.classEq (.cv x) (syn_csn (.cv z)))
      (.imp (.classMem (.cv x) A) (.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A)))
      (.imp (.classMem (syn_csn (.cv z)) A)
        (.imp (.classMem (.cv y) (syn_csn (.cv z))) (.classMem (syn_csn (.cv y)) A)))
      p0015 p0019
  have freeVariableCertificate5 :
    z ∉
      ((Wff.imp (.classMem (.cv x) A)
          (.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A)))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CoreFVSimp.fv_wff_objMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, fresh_z_ne_x, fresh_z_not_A, fresh_z_ne_y,
      or_false, not_false_eq_true]
  have p0021 :=
    @g_exlimiv (.classEq (.cv x) (syn_csn (.cv z)))
      (.imp (.classMem (.cv x) A) (.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A))) z
      freeVariableCertificate5 p0020
  have p0022 :=
    @g_sylbi (.classMem (.cv x) (syn_c1c))
      (syn_wex z (.classEq (.cv x) (syn_csn (.cv z))))
      (.imp (.classMem (.cv x) A) (.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A)))
      p0010 p0021
  have p0023 :=
    @g_syli (.classMem (.cv x) A) (syn_wss A (syn_c1c)) (.classMem (.cv x) (syn_c1c))
      (.imp (.objMem y x) (.classMem (syn_csn (.cv y)) A)) p0000 p0022
  have freeVariableCertificate6 : x ∉ ((Wff.classMem (syn_csn (.cv y)) A)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_y, fresh_x_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate7 : x ∉ ((syn_wss A (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0024 :=
    @g_rexlimdv (syn_wss A (syn_c1c)) (.objMem y x) (.classMem (syn_csn (.cv y)) A) x A
      freeVariableCertificate6 freeVariableCertificate7 p0023
  have p0025 :=
    @g_impbid2 (syn_wss A (syn_c1c)) (.classMem (syn_csn (.cv y)) A)
      (syn_wrex x A (.objMem y x)) p0009 p0024
  have freeVariableCertificate8 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have p0026 :=
    @g_eluni2 x (.cv y) A freeVariableCertificate8
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
  have p0027_e01_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv y) (syn_cuni A)) (syn_wrex x A (.objMem y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa syn_wrex
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
    @g_syl6bbr (syn_wss A (syn_c1c)) (.classMem (syn_csn (.cv y)) A)
      (syn_wrex x A (.objMem y x)) (.classMem (.cv y) (syn_cuni A)) p0025
      p0027_e01_recanon
  have p0028 := @g_eleq1 (.cv x) (syn_csn (.cv y)) A
  have p0029 := @g_eleq1 (.cv x) (syn_csn (.cv y)) (syn_cpw1 (syn_cuni A))
  have p0030 := @g_snelpw1 (.cv y) (syn_cuni A)
  have p0031 :=
    @g_syl6bb (.classEq (.cv x) (syn_csn (.cv y)))
      (.classMem (.cv x) (syn_cpw1 (syn_cuni A)))
      (.classMem (syn_csn (.cv y)) (syn_cpw1 (syn_cuni A)))
      (.classMem (.cv y) (syn_cuni A)) p0029 p0030
  have p0032 :=
    @g_bibi12d (.classEq (.cv x) (syn_csn (.cv y))) (.classMem (.cv x) A)
      (.classMem (syn_csn (.cv y)) A) (.classMem (.cv x) (syn_cpw1 (syn_cuni A)))
      (.classMem (.cv y) (syn_cuni A)) p0028 p0031
  have p0033 :=
    @g_syl5ibrcom (syn_wss A (syn_c1c))
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cpw1 (syn_cuni A))))
      (.classEq (.cv x) (syn_csn (.cv y)))
      (syn_wb (.classMem (syn_csn (.cv y)) A) (.classMem (.cv y) (syn_cuni A))) p0027
      p0032
  have freeVariableCertificate9 :
    y ∉ ((syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cpw1 (syn_cuni A))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union,
      Finset.mem_singleton, fresh_y_ne_x, fresh_y_not_A, or_false, not_false_eq_true]
  have freeVariableCertificate10 : y ∉ ((syn_wss A (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_A, or_false, not_false_eq_true]
  have p0034 :=
    @g_exlimdv (syn_wss A (syn_c1c)) (.classEq (.cv x) (syn_csn (.cv y)))
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cpw1 (syn_cuni A)))) y
      freeVariableCertificate9 freeVariableCertificate10 p0033
  have p0035 :=
    @g_syl5bi (.classMem (.cv x) (syn_c1c))
      (syn_wex y (.classEq (.cv x) (syn_csn (.cv y)))) (syn_wss A (syn_c1c))
      (syn_wb (.classMem (.cv x) A) (.classMem (.cv x) (syn_cpw1 (syn_cuni A)))) p0004
      p0034
  have p0036 :=
    @g_pm5_21ndd (syn_wss A (syn_c1c)) (.classMem (.cv x) (syn_c1c)) (.classMem (.cv x) A)
      (.classMem (.cv x) (syn_cpw1 (syn_cuni A))) p0000 p0003 p0035
  have freeVariableCertificate11 : x ∉ ((syn_cpw1 (syn_cuni A))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, fresh_x_not_A,
      not_false_eq_true]
  have p0037 :=
    @g_eqrdv (syn_wss A (syn_c1c)) x A (syn_cpw1 (syn_cuni A))
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A))) freeVariableCertificate11
      freeVariableCertificate7 p0036
  exact p0037

@[expose]
noncomputable def g_pw1equn (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y)
    (hyp_pw1equn_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_pw1equn_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cpw1 C) (syn_cun A B)) (syn_wex x (syn_wex y
            (syn_w3a (.classEq C (syn_cun (.cv x) (.cv y)))
              (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_cpw1 (.cv y))))))) :=
  by
  have p0000 := @g_unipw1 C
  have p0001 := @g_unieq (syn_cpw1 C) (syn_cun A B)
  have p0002 :=
    @g_syl5eqr (.classEq (syn_cpw1 C) (syn_cun A B)) C (syn_cuni (syn_cpw1 C))
      (syn_cuni (syn_cun A B)) p0000 p0001
  have p0003 := @g_ssun1 A B
  have p0004 := @g_sseq2 (syn_cpw1 C) (syn_cun A B) A
  have p0005 :=
    @g_mpbiri (.classEq (syn_cpw1 C) (syn_cun A B)) (syn_wss A (syn_cpw1 C))
      (syn_wss A (syn_cun A B)) p0003 p0004
  have p0006 := @g_pw1ss1c C
  have p0007 :=
    @g_syl6ss (.classEq (syn_cpw1 C) (syn_cun A B)) A (syn_cpw1 C) (syn_c1c) p0005 p0006
  have p0008 := @g_eqpw1uni A
  have p0009 :=
    @g_syl (.classEq (syn_cpw1 C) (syn_cun A B)) (syn_wss A (syn_c1c))
      (.classEq A (syn_cpw1 (syn_cuni A))) p0007 p0008
  have p0010 := @g_ssun2 B A
  have p0011 := @g_sseq2 (syn_cpw1 C) (syn_cun A B) B
  have p0012 :=
    @g_mpbiri (.classEq (syn_cpw1 C) (syn_cun A B)) (syn_wss B (syn_cpw1 C))
      (syn_wss B (syn_cun A B)) p0010 p0011
  have p0013 :=
    @g_syl6ss (.classEq (syn_cpw1 C) (syn_cun A B)) B (syn_cpw1 C) (syn_c1c) p0012 p0006
  have p0014 := @g_eqpw1uni B
  have p0015 :=
    @g_syl (.classEq (syn_cpw1 C) (syn_cun A B)) (syn_wss B (syn_c1c))
      (.classEq B (syn_cpw1 (syn_cuni B))) p0013 p0014
  have p0016 := @g_uniex A hyp_pw1equn_1
  have p0017 := @g_uniex B hyp_pw1equn_2
  have p0018 := @g_uneq12 (.cv x) (syn_cuni A) (.cv y) (syn_cuni B)
  have p0019 := @g_uniun A B
  have p0020 :=
    @g_syl6eqr (syn_wa (.classEq (.cv x) (syn_cuni A)) (.classEq (.cv y) (syn_cuni B)))
      (syn_cun (.cv x) (.cv y)) (syn_cun (syn_cuni A) (syn_cuni B))
      (syn_cuni (syn_cun A B)) p0018 p0019
  have p0021 :=
    @g_eqeq2d (syn_wa (.classEq (.cv x) (syn_cuni A)) (.classEq (.cv y) (syn_cuni B)))
      (syn_cun (.cv x) (.cv y)) (syn_cuni (syn_cun A B)) C p0020
  have p0022 := @g_pw1eq (.cv x) (syn_cuni A)
  have p0023 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cuni A)) (syn_cpw1 (.cv x)) (syn_cpw1 (syn_cuni A)) A
      p0022
  have p0024 :=
    @g_adantr (.classEq (.cv x) (syn_cuni A))
      (syn_wb (.classEq A (syn_cpw1 (.cv x))) (.classEq A (syn_cpw1 (syn_cuni A))))
      (.classEq (.cv y) (syn_cuni B)) p0023
  have p0025 := @g_pw1eq (.cv y) (syn_cuni B)
  have p0026 :=
    @g_eqeq2d (.classEq (.cv y) (syn_cuni B)) (syn_cpw1 (.cv y)) (syn_cpw1 (syn_cuni B)) B
      p0025
  have p0027 :=
    @g_adantl (.classEq (.cv y) (syn_cuni B))
      (syn_wb (.classEq B (syn_cpw1 (.cv y))) (.classEq B (syn_cpw1 (syn_cuni B))))
      (.classEq (.cv x) (syn_cuni A)) p0026
  have p0028 :=
    @g_n_3anbi123d
      (syn_wa (.classEq (.cv x) (syn_cuni A)) (.classEq (.cv y) (syn_cuni B)))
      (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq C (syn_cuni (syn_cun A B)))
      (.classEq A (syn_cpw1 (.cv x))) (.classEq A (syn_cpw1 (syn_cuni A)))
      (.classEq B (syn_cpw1 (.cv y))) (.classEq B (syn_cpw1 (syn_cuni B))) p0021 p0024
      p0027
  have freeVariableCertificate0 :
    x ∉
      ((syn_w3a (.classEq C (syn_cuni (syn_cun A B))) (.classEq A (syn_cpw1 (syn_cuni A)))
          (.classEq B (syn_cpw1 (syn_cuni B))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, dv_B_x,
      dv_C_x, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate1 :
    y ∉
      ((syn_w3a (.classEq C (syn_cuni (syn_cun A B))) (.classEq A (syn_cpw1 (syn_cuni A)))
          (.classEq B (syn_cpw1 (syn_cuni B))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, dv_B_y,
      dv_C_y, dv_A_y, or_false, not_false_eq_true]
  have p0029 :=
    @g_spc2ev
      (syn_w3a (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x)))
        (.classEq B (syn_cpw1 (.cv y))))
      (syn_w3a (.classEq C (syn_cuni (syn_cun A B))) (.classEq A (syn_cpw1 (syn_cuni A)))
        (.classEq B (syn_cpw1 (syn_cuni B))))
      x y (syn_cuni A) (syn_cuni B)
      (by
        exact
          (show x ∉ ((syn_cuni A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
              exact (show x ∉ (A).fv from (by exact dv_A_x)))))
      (by
        exact
          (show y ∉ ((syn_cuni A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
              exact (show y ∉ (A).fv from (by exact dv_A_y)))))
      (by
        exact
          (show x ∉ ((syn_cuni B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
              exact (show x ∉ (B).fv from (by exact dv_B_x)))))
      (by
        exact
          (show y ∉ ((syn_cuni B)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
              exact (show y ∉ (B).fv from (by exact dv_B_y)))))
      freeVariableCertificate0 freeVariableCertificate1
      (show x ≠ y from (by exact dv_x_y)) p0016 p0017 p0028
  have p0030 :=
    @g_syl3anc (.classEq (syn_cpw1 C) (syn_cun A B)) (.classEq C (syn_cuni (syn_cun A B)))
      (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_cpw1 (syn_cuni B)))
      (syn_wex x (syn_wex y
          (syn_w3a (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x)))
            (.classEq B (syn_cpw1 (.cv y))))))
      p0002 p0009 p0015 p0029
  have p0031 := @g_pw1un (.cv x) (.cv y)
  have p0032 := @g_pw1eq C (syn_cun (.cv x) (.cv y))
  have p0033 := @g_uneq12 A (syn_cpw1 (.cv x)) B (syn_cpw1 (.cv y))
  have p0034 :=
    @g_eqeqan12d (.classEq C (syn_cun (.cv x) (.cv y)))
      (syn_wa (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_cpw1 (.cv y))))
      (syn_cpw1 C) (syn_cpw1 (syn_cun (.cv x) (.cv y))) (syn_cun A B)
      (syn_cun (syn_cpw1 (.cv x)) (syn_cpw1 (.cv y))) p0032 p0033
  have p0035 :=
    @g_n_3impb (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x)))
      (.classEq B (syn_cpw1 (.cv y)))
      (syn_wb (.classEq (syn_cpw1 C) (syn_cun A B))
        (.classEq (syn_cpw1 (syn_cun (.cv x) (.cv y)))
          (syn_cun (syn_cpw1 (.cv x)) (syn_cpw1 (.cv y)))))
      p0034
  have p0036 :=
    @g_mpbiri
      (syn_w3a (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x)))
        (.classEq B (syn_cpw1 (.cv y))))
      (.classEq (syn_cpw1 C) (syn_cun A B))
      (.classEq (syn_cpw1 (syn_cun (.cv x) (.cv y)))
        (syn_cun (syn_cpw1 (.cv x)) (syn_cpw1 (.cv y))))
      p0031 p0035
  have freeVariableCertificate2 : x ∉ ((Wff.classEq (syn_cpw1 C) (syn_cun A B))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, dv_C_x,
      dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate3 : y ∉ ((Wff.classEq (syn_cpw1 C) (syn_cun A B))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union, dv_C_y,
      dv_A_y, dv_B_y, or_false, not_false_eq_true]
  have p0037 :=
    @g_exlimivv
      (syn_w3a (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x)))
        (.classEq B (syn_cpw1 (.cv y))))
      (.classEq (syn_cpw1 C) (syn_cun A B)) x y freeVariableCertificate2
      freeVariableCertificate3 p0036
  have p0038 :=
    @g_impbii (.classEq (syn_cpw1 C) (syn_cun A B))
      (syn_wex x (syn_wex y
          (syn_w3a (.classEq C (syn_cun (.cv x) (.cv y))) (.classEq A (syn_cpw1 (.cv x)))
            (.classEq B (syn_cpw1 (.cv y))))))
      p0030 p0037
  exact p0038


end NFChoice.DirectNominalPrf.WPPReplay

end
