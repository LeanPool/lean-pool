/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart041`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_lefinlteq (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem A V) (.classMem B W) (syn_wne A (syn_c0)))
        (syn_wb (.classMem (syn_copk A B) (syn_clefin))
          (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ V.fv ∪ W.fv
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
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have freeVariableCertificate0 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0000 := @g_nnc0suc y (.cv x) freeVariableCertificate0
  have p0001 := @g_addceq2 (.cv x) (syn_c0c) A
  have p0002 := @g_addcid1 A
  have p0003 :=
    @g_syl6req (.classEq (.cv x) (syn_c0c)) (syn_cplc A (.cv x)) (syn_cplc A (syn_c0c)) A
      p0001 p0002
  have p0004 := @g_addceq2 (.cv x) (syn_cplc (.cv y) (syn_c1c)) A
  have p0005 := @g_addcass A (.cv y) (syn_c1c)
  have p0006 :=
    @g_syl6eqr (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_cplc A (.cv x))
      (syn_cplc A (syn_cplc (.cv y) (syn_c1c))) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))
      p0004 p0005
  have p0007 :=
    @g_reximi (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
      (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))) y
      (syn_cnnc) p0006
  have p0008 :=
    @g_orim12i (.classEq (.cv x) (syn_c0c)) (.classEq A (syn_cplc A (.cv x)))
      (syn_wrex y (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
      p0003 p0007
  have p0009 :=
    @g_sylbi (.classMem (.cv x) (syn_cnnc))
      (syn_wo (.classEq (.cv x) (syn_c0c))
        (syn_wrex y (syn_cnnc) (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))))
      (syn_wo (.classEq A (syn_cplc A (.cv x))) (syn_wrex y (syn_cnnc)
          (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))))
      p0000 p0008
  have p0010 :=
    @g_orcomd (.classMem (.cv x) (syn_cnnc)) (.classEq A (syn_cplc A (.cv x)))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
      p0009
  have p0011 := @g_eqeq1 B (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))
  have freeVariableCertificate1 : y ∉ ((Wff.classEq B (syn_cplc A (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_y_not_B, fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true]
  have p0012 :=
    @g_rexbidv (.classEq B (syn_cplc A (.cv x)))
      (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))
      (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))) y
      (syn_cnnc) freeVariableCertificate1 p0011
  have p0013 := @g_eqeq2 B (syn_cplc A (.cv x)) A
  have p0014 :=
    @g_orbi12d (.classEq B (syn_cplc A (.cv x)))
      (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
      (syn_wrex y (syn_cnnc)
        (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
      (.classEq A B) (.classEq A (syn_cplc A (.cv x))) p0012 p0013
  have p0015 :=
    @g_syl5ibrcom (.classMem (.cv x) (syn_cnnc))
      (syn_wo (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
        (.classEq A B))
      (.classEq B (syn_cplc A (.cv x)))
      (syn_wo (syn_wrex y (syn_cnnc)
          (.classEq (syn_cplc A (.cv x)) (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
        (.classEq A (syn_cplc A (.cv x))))
      p0010 p0014
  have freeVariableCertificate2 :
    x ∉
      ((syn_wo (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
          (.classEq A B))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_x_not_B,
      fresh_x_not_A, fresh_x_ne_y, or_false, and_false, not_false_eq_true]
  have p0016 :=
    @g_rexlimiv (.classEq B (syn_cplc A (.cv x)))
      (syn_wo (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
        (.classEq A B))
      x (syn_cnnc) freeVariableCertificate2 p0015
  have p0017 :=
    @g_eqeq2i (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))
      (syn_cplc A (syn_cplc (.cv y) (syn_c1c))) B p0005
  have p0018 := @g_peano2 (.cv y)
  have p0019 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (syn_cplc A (.cv x))
      (syn_cplc A (syn_cplc (.cv y) (syn_c1c))) B p0004
  have freeVariableCertificate3 : x ∉ ((syn_cplc (.cv y) (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_ne_y, or_false,
      not_false_eq_true]
  have freeVariableCertificate4 :
    x ∉ ((Wff.classEq B (syn_cplc A (syn_cplc (.cv y) (syn_c1c))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_x_not_B, fresh_x_not_A,
      fresh_x_ne_y, or_false, not_false_eq_true]
  have p0020 :=
    @g_rspcev (.classEq B (syn_cplc A (.cv x)))
      (.classEq B (syn_cplc A (syn_cplc (.cv y) (syn_c1c)))) x
      (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc) freeVariableCertificate3
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate4 p0019
  have p0021 :=
    @g_sylan (.classMem (.cv y) (syn_cnnc))
      (.classMem (syn_cplc (.cv y) (syn_c1c)) (syn_cnnc))
      (.classEq B (syn_cplc A (syn_cplc (.cv y) (syn_c1c))))
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) p0018 p0020
  have p0022 :=
    @g_sylan2b (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))
      (.classMem (.cv y) (syn_cnnc))
      (.classEq B (syn_cplc A (syn_cplc (.cv y) (syn_c1c))))
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) p0017 p0021
  have freeVariableCertificate5 :
    y ∉ ((syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, Finset.notMem_empty, fresh_y_not_B, fresh_y_not_A,
      fresh_y_ne_x, or_false, and_false, not_false_eq_true]
  have p0023 :=
    @g_rexlimiva (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) y (syn_cnnc)
      freeVariableCertificate5 p0022
  have p0024 := @g_peano1
  have p0025 := @g_eqcomi (syn_cplc A (syn_c0c)) A p0002
  have p0026 :=
    @g_eqeq2d (.classEq (.cv x) (syn_c0c)) (syn_cplc A (.cv x)) (syn_cplc A (syn_c0c)) A
      p0001
  have freeVariableCertificate6 : x ∉ ((Wff.classEq A (syn_cplc A (syn_c0c)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_A, or_false, not_false_eq_true]
  have p0027 :=
    @g_rspcev (.classEq A (syn_cplc A (.cv x))) (.classEq A (syn_cplc A (syn_c0c))) x
      (syn_c0c) (syn_cnnc)
      (by
        exact
          (show x ∉ ((syn_c0c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      (by
        exact
          (show x ∉ ((syn_cnnc)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
              exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate6 p0026
  have p0028 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cnnc)) (.classEq A (syn_cplc A (syn_c0c)))
      (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc A (.cv x)))) p0024 p0025 p0027
  have p0029 := @g_eqeq1 A B (syn_cplc A (.cv x))
  have freeVariableCertificate7 : x ∉ ((Wff.classEq A B)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
      fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true]
  have p0030 :=
    @g_rexbidv (.classEq A B) (.classEq A (syn_cplc A (.cv x)))
      (.classEq B (syn_cplc A (.cv x))) x (syn_cnnc) freeVariableCertificate7 p0029
  have p0031 :=
    @g_mpbii (.classEq A B) (syn_wrex x (syn_cnnc) (.classEq A (syn_cplc A (.cv x))))
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) p0028 p0030
  have p0032 :=
    @g_jaoi (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) (.classEq A B) p0023 p0031
  have p0033 :=
    @g_impbii (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x))))
      (syn_wo (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
        (.classEq A B))
      p0016 p0032
  have p0034 :=
    @g_a1i
      (syn_wb (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))) (syn_wo
          (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
          (.classEq A B)))
      (syn_w3a (.classMem A V) (.classMem B W) (syn_wne A (syn_c0))) p0033
  have p0035 :=
    @g_opklefing x A B V W (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
  have p0036 :=
    @g_n_3adant3 (.classMem A V) (.classMem B W)
      (syn_wb (.classMem (syn_copk A B) (syn_clefin))
        (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x)))))
      (syn_wne A (syn_c0)) p0035
  have p0037 :=
    @g_opkltfing y A B V W (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
  have p0038 :=
    @g_adantr (syn_wa (.classMem A V) (.classMem B W))
      (syn_wb (.classMem (syn_copk A B) (syn_cltfin)) (syn_wa (syn_wne A (syn_c0))
          (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))))
      (syn_wne A (syn_c0)) p0037
  have p0039 :=
    @g_ibar (syn_wne A (syn_c0))
      (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
  have p0040 :=
    @g_adantl (syn_wne A (syn_c0))
      (syn_wb (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
        (syn_wa (syn_wne A (syn_c0))
          (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))))
      (syn_wa (.classMem A V) (.classMem B W)) p0039
  have p0041 :=
    @g_bitr4d (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0)))
      (.classMem (syn_copk A B) (syn_cltfin))
      (syn_wa (syn_wne A (syn_c0))
        (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))))
      (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c)))) p0038
      p0040
  have p0042 :=
    @g_orbi1d (syn_wa (syn_wa (.classMem A V) (.classMem B W)) (syn_wne A (syn_c0)))
      (.classMem (syn_copk A B) (syn_cltfin))
      (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
      (.classEq A B) p0041
  have p0043 :=
    @g_n_3impa (.classMem A V) (.classMem B W) (syn_wne A (syn_c0))
      (syn_wb (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) (syn_wo
          (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
          (.classEq A B)))
      p0042
  have p0044 :=
    @g_n_3bitr4d (syn_w3a (.classMem A V) (.classMem B W) (syn_wne A (syn_c0)))
      (syn_wrex x (syn_cnnc) (.classEq B (syn_cplc A (.cv x))))
      (syn_wo (syn_wrex y (syn_cnnc) (.classEq B (syn_cplc (syn_cplc A (.cv y)) (syn_c1c))))
        (.classEq A B))
      (.classMem (syn_copk A B) (syn_clefin))
      (syn_wo (.classMem (syn_copk A B) (syn_cltfin)) (.classEq A B)) p0034 p0036 p0043
  exact p0044


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart042`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ltfinex : Nominal.NPrf (.classMem (syn_cltfin) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  let c : Var := freshVar proofSupport 5
  let a : Var := freshVar proofSupport 6
  let b : Var := freshVar proofSupport 7
  let d : Var := freshVar proofSupport 8
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
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
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
  have fresh_y_ne_c : y ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_c_ne_y : c ≠ y := Ne.symm fresh_y_ne_c
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_d : y ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
  have fresh_d_ne_y : d ≠ y := Ne.symm fresh_y_ne_d
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
  have fresh_z_ne_c : z ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_c_ne_z : c ≠ z := Ne.symm fresh_z_ne_c
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_z_ne_d : z ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 2) (j := 8) (by decide)
  have fresh_d_ne_z : d ≠ z := Ne.symm fresh_z_ne_d
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_w : t ≠ w := Ne.symm fresh_w_ne_t
  have fresh_w_ne_c : w ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_c_ne_w : c ≠ w := Ne.symm fresh_w_ne_c
  have fresh_w_ne_a : w ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_a_ne_w : a ≠ w := Ne.symm fresh_w_ne_a
  have fresh_w_ne_b : w ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_b_ne_w : b ≠ w := Ne.symm fresh_w_ne_b
  have fresh_w_ne_d : w ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_d_ne_w : d ≠ w := Ne.symm fresh_w_ne_d
  have fresh_t_ne_c : t ≠ c :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_c_ne_t : c ≠ t := Ne.symm fresh_t_ne_c
  have fresh_t_ne_a : t ≠ a :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_a_ne_t : a ≠ t := Ne.symm fresh_t_ne_a
  have fresh_t_ne_b : t ≠ b :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_b_ne_t : b ≠ t := Ne.symm fresh_t_ne_b
  have fresh_t_ne_d : t ≠ d :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 4) (j := 8) (by decide)
  have fresh_d_ne_t : d ≠ t := Ne.symm fresh_t_ne_d
  have fresh_c_ne_a : c ≠ a :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_a_ne_c : a ≠ c := Ne.symm fresh_c_ne_a
  have fresh_c_ne_b : c ≠ b :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_b_ne_c : b ≠ c := Ne.symm fresh_c_ne_b
  have fresh_c_ne_d : c ≠ d :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
  have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 6) (j := 8) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 7) (j := 8) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  let syntaxClass0000 : Class :=
    (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0001 : Class := (syn_ccompl syntaxClass0000)
  let syntaxClass0002 : Class := (syn_csik syntaxClass0001)
  let syntaxClass0003 : Class := (syn_csik syntaxClass0002)
  let syntaxClass0004 : Class := (syn_csik syntaxClass0003)
  let syntaxClass0005 : Class := (syn_csik syntaxClass0004)
  let syntaxClass0006 : Class := (syn_csik syntaxClass0005)
  let syntaxClass0007 : Class := (syn_csik syntaxClass0006)
  let syntaxClass0008 : Class := (syn_csik syntaxClass0007)
  let syntaxClass0009 : Class := (syn_cins3k syntaxClass0008)
  let syntaxClass0010 : Class :=
    (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
  let syntaxClass0011 : Class := (syn_cins2k syntaxClass0010)
  let syntaxClass0012 : Class := (syn_cins2k syntaxClass0011)
  let syntaxClass0013 : Class :=
    (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))
  let syntaxClass0014 : Class := (syn_csik syntaxClass0013)
  let syntaxClass0015 : Class := (syn_csik syntaxClass0014)
  let syntaxClass0016 : Class := (syn_cins3k syntaxClass0015)
  let syntaxClass0017 : Class := (syn_cins3k syntaxClass0013)
  let syntaxClass0018 : Class := (syn_cins2k syntaxClass0017)
  let syntaxClass0019 : Class := (syn_cun syntaxClass0016 syntaxClass0018)
  let syntaxClass0020 : Class := (syn_csymdif syntaxClass0012 syntaxClass0019)
  let syntaxClass0021 : Class :=
    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  let syntaxClass0022 : Class := (syn_cpw1 syntaxClass0021)
  let syntaxClass0023 : Class := (syn_cpw1 syntaxClass0022)
  let syntaxClass0024 : Class := (syn_cpw1 syntaxClass0023)
  let syntaxClass0025 : Class := (syn_cpw1 syntaxClass0024)
  let syntaxClass0026 : Class := (syn_cimak syntaxClass0020 syntaxClass0025)
  let syntaxClass0027 : Class := (syn_ccompl syntaxClass0026)
  let syntaxClass0028 : Class := (syn_cin syntaxClass0009 syntaxClass0027)
  let syntaxClass0029 : Class :=
    (syn_cin (syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk))))) syntaxClass0028)
  let syntaxClass0030 : Class := (syn_cimak syntaxClass0029 syntaxClass0022)
  let syntaxClass0031 : Class :=
    (syn_cin (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))) syntaxClass0030)
  let syntaxClass0032 : Class :=
    (syn_cimak syntaxClass0031
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  let syntaxClass0033 : Class := (syn_cins2k syntaxClass0032)
  let syntaxClass0034 : Class :=
    (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
      syntaxClass0033)
  let syntaxClass0035 : Class :=
    (syn_cimak syntaxClass0034
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  let syntaxClass0036 : Class := (syn_ccompl syntaxClass0035)
  let syntaxClass0037 : Class := (syn_cins3k syntaxClass0001)
  let syntaxClass0038 : Class :=
    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
      (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))
  let syntaxClass0039 : Class :=
    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) syntaxClass0038)
  let syntaxClass0040 : Class :=
    (syn_cimak syntaxClass0039 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  let syntaxClass0041 : Class := (syn_cdif syntaxClass0037 syntaxClass0040)
  let syntaxClass0042 : Class :=
    (syn_cimak syntaxClass0041 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0043 : Class := (syn_cimagek syntaxClass0042)
  let syntaxClass0044 : Class := (syn_cins2k syntaxClass0043)
  let syntaxClass0045 : Class := (syn_cins2k syntaxClass0044)
  let syntaxClass0046 : Class := (syn_cin syntaxClass0036 syntaxClass0045)
  let syntaxClass0047 : Class :=
    (syn_cimak syntaxClass0046 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  let syntaxClass0048 : Class :=
    (syn_cimak syntaxClass0047 (syn_cpw1 (syn_cpw1 (syn_cnnc))))
  let syntaxClass0049 : Class :=
    (syn_cdif syntaxClass0048 (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))
  let syntaxFormula0050 : Wff := (.classMem (.cv x) syntaxClass0049)
  let syntaxFormula0051 : Wff := (Wff.classMem (.cv x) syntaxClass0049)
  let syntaxFormula0052 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))) syntaxClass0047)
  let syntaxFormula0053 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cnnc)))) syntaxFormula0052)
  let syntaxFormula0054 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv w)))) syntaxFormula0052)
  let syntaxFormula0055 : Wff := (syn_wrex w (syn_cnnc) syntaxFormula0054)
  let syntaxFormula0056 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cnnc))) syntaxFormula0052)
  let syntaxFormula0057 : Wff := (syn_wex t syntaxFormula0054)
  let syntaxFormula0058 : Wff := (syn_wrex w (syn_cnnc) syntaxFormula0057)
  let syntaxFormula0059 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))
      syntaxClass0047)
  let syntaxClass0060 : Class :=
    (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z))))
  let syntaxFormula0061 : Wff := (.classMem syntaxClass0060 syntaxClass0046)
  let syntaxFormula0062 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) syntaxFormula0061)
  let syntaxFormula0063 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      syntaxFormula0061)
  let syntaxFormula0064 : Wff := (syn_wex x syntaxFormula0063)
  let syntaxFormula0065 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0061)
  let syntaxFormula0066 : Wff := (syn_wex t syntaxFormula0063)
  let syntaxFormula0067 : Wff := (syn_wex x syntaxFormula0066)
  let syntaxClass0068 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z))))
  let syntaxFormula0069 : Wff := (.classMem syntaxClass0068 syntaxClass0046)
  let syntaxFormula0070 : Wff :=
    (.classMem (.cv t)
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  let syntaxFormula0071 : Wff :=
    (.classEq (.cv t)
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))))))
  let syntaxClass0072 : Class := (syn_copk (.cv t) syntaxClass0068)
  let syntaxFormula0073 : Wff := (.classMem syntaxClass0072 syntaxClass0034)
  let syntaxFormula0074 : Wff := (syn_wa syntaxFormula0070 syntaxFormula0073)
  let syntaxFormula0075 : Wff := (syn_wa syntaxFormula0071 syntaxFormula0073)
  let syntaxFormula0076 : Wff := (syn_wex c syntaxFormula0075)
  let syntaxFormula0077 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      syntaxFormula0073)
  let syntaxFormula0078 : Wff := (syn_wex t syntaxFormula0075)
  let syntaxFormula0079 : Wff := (syn_wex c syntaxFormula0078)
  let syntaxClass0080 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))))
      syntaxClass0068)
  let syntaxFormula0081 : Wff := (.classMem syntaxClass0080 syntaxClass0034)
  let syntaxFormula0082 : Wff :=
    (.classMem syntaxClass0080
      (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
  let syntaxClass0083 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z))))
  let syntaxFormula0084 : Wff :=
    (.classEq (.cv t)
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))))
  let syntaxClass0085 : Class := (syn_copk (.cv t) syntaxClass0083)
  let syntaxFormula0086 : Wff := (.classMem syntaxClass0085 syntaxClass0031)
  let syntaxFormula0087 : Wff := (syn_wa syntaxFormula0070 syntaxFormula0086)
  let syntaxFormula0088 : Wff := (syn_wa syntaxFormula0084 syntaxFormula0086)
  let syntaxFormula0089 : Wff := (syn_wex b syntaxFormula0088)
  let syntaxFormula0090 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      syntaxFormula0086)
  let syntaxFormula0091 : Wff := (syn_wex t syntaxFormula0088)
  let syntaxFormula0092 : Wff := (syn_wex b syntaxFormula0091)
  let syntaxClass0093 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
      syntaxClass0083)
  let syntaxFormula0094 : Wff := (.classMem syntaxClass0093 syntaxClass0031)
  let syntaxFormula0095 : Wff :=
    (.classMem syntaxClass0093 (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
  let syntaxFormula0096 : Wff := (.classMem (.cv t) syntaxClass0022)
  let syntaxClass0097 : Class :=
    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))))
  let syntaxClass0098 : Class := (syn_csn syntaxClass0097)
  let syntaxFormula0099 : Wff := (.classEq (.cv t) syntaxClass0098)
  let syntaxClass0100 : Class := (syn_copk (.cv t) syntaxClass0093)
  let syntaxFormula0101 : Wff := (.classMem syntaxClass0100 syntaxClass0029)
  let syntaxFormula0102 : Wff := (syn_wa syntaxFormula0096 syntaxFormula0101)
  let syntaxFormula0103 : Wff := (syn_wa syntaxFormula0099 syntaxFormula0101)
  let syntaxFormula0104 : Wff := (syn_wex a syntaxFormula0103)
  let syntaxFormula0105 : Wff := (syn_wrex t syntaxClass0022 syntaxFormula0101)
  let syntaxFormula0106 : Wff := (syn_wex t syntaxFormula0103)
  let syntaxFormula0107 : Wff := (syn_wex a syntaxFormula0106)
  let syntaxClass0108 : Class := (syn_copk syntaxClass0098 syntaxClass0093)
  let syntaxFormula0109 : Wff := (.classMem syntaxClass0108 syntaxClass0029)
  let syntaxFormula0110 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
        (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z))))
      (syn_cins2k (syn_cins3k (syn_cssetk))))
  let syntaxFormula0111 : Wff :=
    (.classMem syntaxClass0108 (syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk))))))
  let syntaxFormula0112 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (syn_csn (.cv b))))
      syntaxClass0003)
  let syntaxFormula0113 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))
        (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0005)
  let syntaxFormula0114 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))) syntaxClass0007)
  let syntaxFormula0115 : Wff := (.classMem syntaxClass0108 syntaxClass0009)
  let syntaxFormula0116 : Wff := (.classMem (.cv t) syntaxClass0025)
  let syntaxClass0117 : Class :=
    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))))))
  let syntaxClass0118 : Class := (syn_csn syntaxClass0117)
  let syntaxClass0119 : Class := (syn_csn syntaxClass0118)
  let syntaxClass0120 : Class := (syn_csn syntaxClass0119)
  let syntaxClass0121 : Class := (syn_csn syntaxClass0120)
  let syntaxFormula0122 : Wff := (.classEq (.cv t) syntaxClass0121)
  let syntaxClass0123 : Class := (syn_copk (.cv t) syntaxClass0108)
  let syntaxFormula0124 : Wff := (.classMem syntaxClass0123 syntaxClass0020)
  let syntaxFormula0125 : Wff := (syn_wa syntaxFormula0116 syntaxFormula0124)
  let syntaxFormula0126 : Wff := (syn_wa syntaxFormula0122 syntaxFormula0124)
  let syntaxFormula0127 : Wff := (syn_wex d syntaxFormula0126)
  let syntaxFormula0128 : Wff := (syn_wrex t syntaxClass0025 syntaxFormula0124)
  let syntaxFormula0129 : Wff := (syn_wex t syntaxFormula0126)
  let syntaxFormula0130 : Wff := (syn_wex d syntaxFormula0129)
  let syntaxClass0131 : Class := (syn_copk syntaxClass0121 syntaxClass0108)
  let syntaxFormula0132 : Wff := (.classMem syntaxClass0131 syntaxClass0020)
  let syntaxFormula0133 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))
        (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
  let syntaxClass0134 : Class := (syn_copk syntaxClass0117 syntaxClass0083)
  let syntaxFormula0135 : Wff := (.classMem syntaxClass0134 syntaxClass0010)
  let syntaxFormula0136 : Wff := (.classMem syntaxClass0131 syntaxClass0012)
  let syntaxClass0137 : Class := (syn_copk syntaxClass0119 syntaxClass0093)
  let syntaxFormula0138 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))
        (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
  let syntaxFormula0139 : Wff :=
    (.classMem (syn_copk
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))
  let syntaxClass0140 : Class := (syn_copk syntaxClass0118 syntaxClass0097)
  let syntaxFormula0141 : Wff := (.classMem syntaxClass0140 syntaxClass0014)
  let syntaxFormula0142 : Wff := (.classMem syntaxClass0131 syntaxClass0016)
  let syntaxFormula0143 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))))
        (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
  let syntaxClass0144 : Class :=
    (syn_copk syntaxClass0117
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))))
  let syntaxFormula0145 : Wff := (.classMem syntaxClass0144 syntaxClass0013)
  let syntaxFormula0146 : Wff := (.classMem syntaxClass0131 syntaxClass0018)
  let syntaxFormula0147 : Wff := (.classMem syntaxClass0131 syntaxClass0019)
  let syntaxFormula0148 : Wff := (syn_wb syntaxFormula0136 syntaxFormula0147)
  let syntaxFormula0149 : Wff := (.classMem syntaxClass0108 syntaxClass0026)
  let syntaxFormula0150 : Wff := (.classMem syntaxClass0108 syntaxClass0027)
  let syntaxFormula0151 : Wff := (.classMem syntaxClass0108 syntaxClass0028)
  let syntaxFormula0152 : Wff :=
    (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
      (.classEq (.cv c) (syn_cun (.cv a) (.cv b))))
  let syntaxFormula0153 : Wff := (.classMem syntaxClass0093 syntaxClass0030)
  let syntaxFormula0154 : Wff := (syn_wrex a (.cv y) syntaxFormula0152)
  let syntaxFormula0155 : Wff := (.classMem syntaxClass0083 syntaxClass0032)
  let syntaxFormula0156 : Wff := (syn_wrex b (.cv w) syntaxFormula0154)
  let syntaxFormula0157 : Wff := (syn_wrex b (.cv w) syntaxFormula0152)
  let syntaxFormula0158 : Wff := (syn_wrex a (.cv y) syntaxFormula0157)
  let syntaxFormula0159 : Wff := (.classMem syntaxClass0080 syntaxClass0033)
  let syntaxFormula0160 : Wff := (syn_wb syntaxFormula0082 syntaxFormula0159)
  let syntaxFormula0161 : Wff := (.classMem syntaxClass0068 syntaxClass0035)
  let syntaxClass0162 : Class := (.cab c syntaxFormula0158)
  let syntaxFormula0163 : Wff := (.classEq (.cv x) syntaxClass0162)
  let syntaxFormula0164 : Wff := (.classMem syntaxClass0068 syntaxClass0036)
  let syntaxClass0165 : Class := (syn_cimak syntaxClass0042 (.cv x))
  let syntaxFormula0166 : Wff := (.classMem (syn_copk (.cv x) (.cv z)) syntaxClass0043)
  let syntaxFormula0167 : Wff := (.classMem syntaxClass0068 syntaxClass0045)
  let syntaxFormula0168 : Wff :=
    (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (.cv w)))
      (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))))
  let syntaxFormula0169 : Wff := (.classMem (syn_copk (.cv y) (.cv z)) syntaxClass0048)
  let syntaxFormula0170 : Wff :=
    (syn_wrex w (syn_cnnc) (.classEq (.cv z) (syn_cplc (syn_cplc (.cv y) (.cv w)) (syn_c1c))))
  let syntaxFormula0171 : Wff := (syn_wa (syn_wne (.cv y) (syn_c0)) syntaxFormula0170)
  let syntaxFormula0172 : Wff := (.classMem (syn_copk (.cv y) (.cv z)) syntaxClass0049)
  let syntaxFormula0173 : Wff :=
    (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) syntaxFormula0050)
  let syntaxFormula0174 : Wff :=
    (syn_wa (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) syntaxFormula0171)
  let syntaxFormula0175 : Wff :=
    (syn_wa (syn_wex y (syn_wex z (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))))
      syntaxFormula0050)
  let syntaxFormula0176 : Wff := (syn_wex z syntaxFormula0174)
  let syntaxFormula0177 : Wff := (syn_wex y syntaxFormula0176)
  let syntaxClass0178 : Class := (syn_cin (syn_cxpk (syn_cvv) (syn_cvv)) syntaxClass0049)
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ltfin x y z w
      (show y ≠ z from (by exact fresh_y_ne_z)) (show y ≠ w from (by exact fresh_y_ne_w))
      (show y ≠ x from (by exact fresh_y_ne_x)) (show z ≠ w from (by exact fresh_z_ne_w))
      (show z ≠ x from (by exact fresh_z_ne_x)) (show w ≠ x from (by exact fresh_w_ne_x))
  have p0001 := @g_elin (.cv x) (syn_cxpk (syn_cvv) (syn_cvv)) syntaxClass0049
  have freshnessCertificate0000 : y ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show y ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show y ≠ x from (by exact fresh_y_ne_x)))))
  have freshnessCertificate0001 : z ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show z ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show z ≠ x from (by exact fresh_z_ne_x)))))
  have p0002 :=
    @g_elvvk y z (.cv x) (by exact freshnessCertificate0000)
      (by exact freshnessCertificate0001) (show y ≠ z from (by exact fresh_y_ne_z))
  have p0003 :=
    @g_anbi1i (.classMem (.cv x) (syn_cxpk (syn_cvv) (syn_cvv)))
      (syn_wex y (syn_wex z (.classEq (.cv x) (syn_copk (.cv y) (.cv z)))))
      syntaxFormula0050 p0002
  have freshnessCertificate0002 : y ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0003 : y ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0002)
  have freshnessCertificate0004 : y ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0003)
  have freshnessCertificate0005 :
    y ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0004)
  have freshnessCertificate0006 :
    y ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0005)
  have freshnessCertificate0007 :
    y ∉ ((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0006)
  have freshnessCertificate0008 :
    y ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0004)
  have freshnessCertificate0009 :
    y ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0008)
  have freshnessCertificate0010 : y ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0002)
  have freshnessCertificate0011 : y ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0010)
  have freshnessCertificate0012 :
    y ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0011)
  have freshnessCertificate0013 :
    y ∉ ((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0012)
  have freshnessCertificate0014 : y ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0002)
  have freshnessCertificate0015 :
    y ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0010 freshnessCertificate0014))
  have freshnessCertificate0016 :
    y ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0015)
  have freshnessCertificate0017 : y ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0018 : y ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0017)
  have freshnessCertificate0019 : y ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0018)
  have freshnessCertificate0020 :
    y ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0016 freshnessCertificate0019))
  have freshnessCertificate0021 : y ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0020)
  have freshnessCertificate0022 : y ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0021)
  have freshnessCertificate0023 : y ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0022)
  have freshnessCertificate0024 : y ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0023)
  have freshnessCertificate0025 : y ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0024)
  have freshnessCertificate0026 : y ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0025)
  have freshnessCertificate0027 : y ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0026)
  have freshnessCertificate0028 : y ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0027)
  have freshnessCertificate0029 : y ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0028)
  have freshnessCertificate0030 : y ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0029)
  have freshnessCertificate0031 :
    y ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0006)
  have freshnessCertificate0032 : y ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0031)
  have freshnessCertificate0033 : y ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0032)
  have freshnessCertificate0034 : y ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0033)
  have freshnessCertificate0035 :
    y ∉
      ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0031)
  have freshnessCertificate0036 : y ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0035)
  have freshnessCertificate0037 : y ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0036)
  have freshnessCertificate0038 : y ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0037)
  have freshnessCertificate0039 : y ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0038)
  have freshnessCertificate0040 : y ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0036)
  have freshnessCertificate0041 : y ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0040)
  have freshnessCertificate0042 : y ∉ ((syntaxClass0016).fv) ∪ ((syntaxClass0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0039 freshnessCertificate0041))
  have freshnessCertificate0043 : y ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0042)
  have freshnessCertificate0044 : y ∉ ((syntaxClass0012).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0034 freshnessCertificate0043))
  have freshnessCertificate0045 : y ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0044)
  have freshnessCertificate0046 : y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0019)
  have freshnessCertificate0047 :
    y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0046)
  have freshnessCertificate0048 :
    y ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0047)
  have freshnessCertificate0049 :
    y ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0048)
  have freshnessCertificate0050 : y ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0049)
  have freshnessCertificate0051 : y ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0050)
  have freshnessCertificate0052 : y ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0051)
  have freshnessCertificate0053 : y ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0052)
  have freshnessCertificate0054 : y ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0053)
  have freshnessCertificate0055 : y ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0025).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0045 freshnessCertificate0054))
  have freshnessCertificate0056 : y ∉ (syntaxClass0026).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0055)
  have freshnessCertificate0057 : y ∉ (syntaxClass0027).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0056)
  have freshnessCertificate0058 : y ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0027).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0030 freshnessCertificate0057))
  have freshnessCertificate0059 : y ∉ (syntaxClass0028).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0058)
  have freshnessCertificate0060 :
    y ∉
      (((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv) ∪
        ((syntaxClass0028).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0013 freshnessCertificate0059))
  have freshnessCertificate0061 : y ∉ (syntaxClass0029).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0060)
  have freshnessCertificate0062 : y ∉ ((syntaxClass0029).fv) ∪ ((syntaxClass0022).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0061 freshnessCertificate0051))
  have freshnessCertificate0063 : y ∉ (syntaxClass0030).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0062)
  have freshnessCertificate0064 :
    y ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0030).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0009 freshnessCertificate0063))
  have freshnessCertificate0065 : y ∉ (syntaxClass0031).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0064)
  have freshnessCertificate0066 :
    y ∉
      ((syntaxClass0031).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0065 freshnessCertificate0049))
  have freshnessCertificate0067 : y ∉ (syntaxClass0032).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0066)
  have freshnessCertificate0068 : y ∉ (syntaxClass0033).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0067)
  have freshnessCertificate0069 :
    y ∉
      (((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv) ∪
        ((syntaxClass0033).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0007 freshnessCertificate0068))
  have freshnessCertificate0070 : y ∉ (syntaxClass0034).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0069)
  have freshnessCertificate0071 :
    y ∉
      ((syntaxClass0034).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0070 freshnessCertificate0049))
  have freshnessCertificate0072 : y ∉ (syntaxClass0035).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0071)
  have freshnessCertificate0073 : y ∉ (syntaxClass0036).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0072)
  have freshnessCertificate0074 : y ∉ (syntaxClass0037).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0022)
  have freshnessCertificate0075 : y ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0014)
  have freshnessCertificate0076 :
    y ∉
      (((syn_cins2k (syn_cins3k (syn_cssetk)))).fv) ∪
        (((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0011 freshnessCertificate0008))
  have freshnessCertificate0077 : y ∉ (syntaxClass0038).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0076)
  have freshnessCertificate0078 :
    y ∉ (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪ ((syntaxClass0038).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0075 freshnessCertificate0077))
  have freshnessCertificate0079 : y ∉ (syntaxClass0039).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0078)
  have freshnessCertificate0080 :
    y ∉
      ((syntaxClass0039).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0079 freshnessCertificate0047))
  have freshnessCertificate0081 : y ∉ (syntaxClass0040).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0080)
  have freshnessCertificate0082 : y ∉ ((syntaxClass0037).fv) ∪ ((syntaxClass0040).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0074 freshnessCertificate0081))
  have freshnessCertificate0083 : y ∉ (syntaxClass0041).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0082)
  have freshnessCertificate0084 :
    y ∉ ((syntaxClass0041).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0083 freshnessCertificate0019))
  have freshnessCertificate0085 : y ∉ (syntaxClass0042).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0084)
  have freshnessCertificate0086 : y ∉ (syntaxClass0043).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek];
      exact freshnessCertificate0085)
  have freshnessCertificate0087 : y ∉ (syntaxClass0044).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0086)
  have freshnessCertificate0088 : y ∉ (syntaxClass0045).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0087)
  have freshnessCertificate0089 : y ∉ ((syntaxClass0036).fv) ∪ ((syntaxClass0045).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0073 freshnessCertificate0088))
  have freshnessCertificate0090 : y ∉ (syntaxClass0046).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0089)
  have freshnessCertificate0091 :
    y ∉ ((syntaxClass0046).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0090 freshnessCertificate0046))
  have freshnessCertificate0092 : y ∉ (syntaxClass0047).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0091)
  have freshnessCertificate0093 : y ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0094 : y ∉ ((syn_cpw1 (syn_cnnc))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0093)
  have freshnessCertificate0095 : y ∉ ((syn_cpw1 (syn_cpw1 (syn_cnnc)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0094)
  have freshnessCertificate0096 :
    y ∉ ((syntaxClass0047).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cnnc)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0092 freshnessCertificate0095))
  have freshnessCertificate0097 : y ∉ (syntaxClass0048).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0096)
  have freshnessCertificate0098 : y ∉ ((syn_c0)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
      exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0099 : y ∉ ((syn_csn (syn_c0))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0098)
  have freshnessCertificate0100 : y ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show y ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0101 : y ∉ (((syn_csn (syn_c0))).fv) ∪ (((syn_cvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0099 freshnessCertificate0100))
  have freshnessCertificate0102 : y ∉ ((syn_cxpk (syn_csn (syn_c0)) (syn_cvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0101)
  have freshnessCertificate0103 :
    y ∉ ((syntaxClass0048).fv) ∪ (((syn_cxpk (syn_csn (syn_c0)) (syn_cvv))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0097 freshnessCertificate0102))
  have freshnessCertificate0104 : y ∉ (syntaxClass0049).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0103)
  have freshnessCertificate0105 : y ∉ (((Class.cv x)).fv) ∪ ((syntaxClass0049).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0000 freshnessCertificate0104))
  have freshnessCertificate0106 : y ∉ (syntaxFormula0051).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0105)
  have freshnessCertificate0107 : z ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0108 : z ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0107)
  have freshnessCertificate0109 : z ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0108)
  have freshnessCertificate0110 :
    z ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0109)
  have freshnessCertificate0111 :
    z ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0110)
  have freshnessCertificate0112 :
    z ∉ ((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0111)
  have freshnessCertificate0113 :
    z ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0109)
  have freshnessCertificate0114 :
    z ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0113)
  have freshnessCertificate0115 : z ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0107)
  have freshnessCertificate0116 : z ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0115)
  have freshnessCertificate0117 :
    z ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0116)
  have freshnessCertificate0118 :
    z ∉ ((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0117)
  have freshnessCertificate0119 : z ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0107)
  have freshnessCertificate0120 :
    z ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0115 freshnessCertificate0119))
  have freshnessCertificate0121 :
    z ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0120)
  have freshnessCertificate0122 : z ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0123 : z ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0122)
  have freshnessCertificate0124 : z ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0123)
  have freshnessCertificate0125 :
    z ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0121 freshnessCertificate0124))
  have freshnessCertificate0126 : z ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0125)
  have freshnessCertificate0127 : z ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0126)
  have freshnessCertificate0128 : z ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0127)
  have freshnessCertificate0129 : z ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0128)
  have freshnessCertificate0130 : z ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0129)
  have freshnessCertificate0131 : z ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0130)
  have freshnessCertificate0132 : z ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0131)
  have freshnessCertificate0133 : z ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0132)
  have freshnessCertificate0134 : z ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0133)
  have freshnessCertificate0135 : z ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0134)
  have freshnessCertificate0136 :
    z ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0111)
  have freshnessCertificate0137 : z ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0136)
  have freshnessCertificate0138 : z ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0137)
  have freshnessCertificate0139 : z ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0138)
  have freshnessCertificate0140 :
    z ∉
      ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0136)
  have freshnessCertificate0141 : z ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0140)
  have freshnessCertificate0142 : z ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0141)
  have freshnessCertificate0143 : z ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0142)
  have freshnessCertificate0144 : z ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0143)
  have freshnessCertificate0145 : z ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0141)
  have freshnessCertificate0146 : z ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0145)
  have freshnessCertificate0147 : z ∉ ((syntaxClass0016).fv) ∪ ((syntaxClass0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0144 freshnessCertificate0146))
  have freshnessCertificate0148 : z ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0147)
  have freshnessCertificate0149 : z ∉ ((syntaxClass0012).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0139 freshnessCertificate0148))
  have freshnessCertificate0150 : z ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0149)
  have freshnessCertificate0151 : z ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0124)
  have freshnessCertificate0152 :
    z ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0151)
  have freshnessCertificate0153 :
    z ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0152)
  have freshnessCertificate0154 :
    z ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0153)
  have freshnessCertificate0155 : z ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0154)
  have freshnessCertificate0156 : z ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0155)
  have freshnessCertificate0157 : z ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0156)
  have freshnessCertificate0158 : z ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0157)
  have freshnessCertificate0159 : z ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0158)
  have freshnessCertificate0160 : z ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0025).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0150 freshnessCertificate0159))
  have freshnessCertificate0161 : z ∉ (syntaxClass0026).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0160)
  have freshnessCertificate0162 : z ∉ (syntaxClass0027).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0161)
  have freshnessCertificate0163 : z ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0027).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0135 freshnessCertificate0162))
  have freshnessCertificate0164 : z ∉ (syntaxClass0028).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0163)
  have freshnessCertificate0165 :
    z ∉
      (((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv) ∪
        ((syntaxClass0028).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0118 freshnessCertificate0164))
  have freshnessCertificate0166 : z ∉ (syntaxClass0029).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0165)
  have freshnessCertificate0167 : z ∉ ((syntaxClass0029).fv) ∪ ((syntaxClass0022).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0166 freshnessCertificate0156))
  have freshnessCertificate0168 : z ∉ (syntaxClass0030).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0167)
  have freshnessCertificate0169 :
    z ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0030).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0114 freshnessCertificate0168))
  have freshnessCertificate0170 : z ∉ (syntaxClass0031).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0169)
  have freshnessCertificate0171 :
    z ∉
      ((syntaxClass0031).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0170 freshnessCertificate0154))
  have freshnessCertificate0172 : z ∉ (syntaxClass0032).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0171)
  have freshnessCertificate0173 : z ∉ (syntaxClass0033).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0172)
  have freshnessCertificate0174 :
    z ∉
      (((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv) ∪
        ((syntaxClass0033).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0112 freshnessCertificate0173))
  have freshnessCertificate0175 : z ∉ (syntaxClass0034).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0174)
  have freshnessCertificate0176 :
    z ∉
      ((syntaxClass0034).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0175 freshnessCertificate0154))
  have freshnessCertificate0177 : z ∉ (syntaxClass0035).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0176)
  have freshnessCertificate0178 : z ∉ (syntaxClass0036).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0177)
  have freshnessCertificate0179 : z ∉ (syntaxClass0037).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0127)
  have freshnessCertificate0180 : z ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0119)
  have freshnessCertificate0181 :
    z ∉
      (((syn_cins2k (syn_cins3k (syn_cssetk)))).fv) ∪
        (((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0116 freshnessCertificate0113))
  have freshnessCertificate0182 : z ∉ (syntaxClass0038).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0181)
  have freshnessCertificate0183 :
    z ∉ (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪ ((syntaxClass0038).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0180 freshnessCertificate0182))
  have freshnessCertificate0184 : z ∉ (syntaxClass0039).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0183)
  have freshnessCertificate0185 :
    z ∉
      ((syntaxClass0039).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0184 freshnessCertificate0152))
  have freshnessCertificate0186 : z ∉ (syntaxClass0040).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0185)
  have freshnessCertificate0187 : z ∉ ((syntaxClass0037).fv) ∪ ((syntaxClass0040).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0179 freshnessCertificate0186))
  have freshnessCertificate0188 : z ∉ (syntaxClass0041).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0187)
  have freshnessCertificate0189 :
    z ∉ ((syntaxClass0041).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0188 freshnessCertificate0124))
  have freshnessCertificate0190 : z ∉ (syntaxClass0042).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0189)
  have freshnessCertificate0191 : z ∉ (syntaxClass0043).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek];
      exact freshnessCertificate0190)
  have freshnessCertificate0192 : z ∉ (syntaxClass0044).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0191)
  have freshnessCertificate0193 : z ∉ (syntaxClass0045).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0192)
  have freshnessCertificate0194 : z ∉ ((syntaxClass0036).fv) ∪ ((syntaxClass0045).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0178 freshnessCertificate0193))
  have freshnessCertificate0195 : z ∉ (syntaxClass0046).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0194)
  have freshnessCertificate0196 :
    z ∉ ((syntaxClass0046).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0195 freshnessCertificate0151))
  have freshnessCertificate0197 : z ∉ (syntaxClass0047).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0196)
  have freshnessCertificate0198 : z ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0199 : z ∉ ((syn_cpw1 (syn_cnnc))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0198)
  have freshnessCertificate0200 : z ∉ ((syn_cpw1 (syn_cpw1 (syn_cnnc)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0199)
  have freshnessCertificate0201 :
    z ∉ ((syntaxClass0047).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cnnc)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0197 freshnessCertificate0200))
  have freshnessCertificate0202 : z ∉ (syntaxClass0048).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0201)
  have freshnessCertificate0203 : z ∉ ((syn_c0)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
      exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0204 : z ∉ ((syn_csn (syn_c0))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0203)
  have freshnessCertificate0205 : z ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show z ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0206 : z ∉ (((syn_csn (syn_c0))).fv) ∪ (((syn_cvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0204 freshnessCertificate0205))
  have freshnessCertificate0207 : z ∉ ((syn_cxpk (syn_csn (syn_c0)) (syn_cvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0206)
  have freshnessCertificate0208 :
    z ∉ ((syntaxClass0048).fv) ∪ (((syn_cxpk (syn_csn (syn_c0)) (syn_cvv))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0202 freshnessCertificate0207))
  have freshnessCertificate0209 : z ∉ (syntaxClass0049).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0208)
  have freshnessCertificate0210 : z ∉ (((Class.cv x)).fv) ∪ ((syntaxClass0049).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0001 freshnessCertificate0209))
  have freshnessCertificate0211 : z ∉ (syntaxFormula0051).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0210)
  have p0004 :=
    @g_n_19_41vv (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) syntaxFormula0050 y z
      (by exact freshnessCertificate0106) (by exact freshnessCertificate0211)
  have p0005 := @g_eleq1 (.cv x) (syn_copk (.cv y) (.cv z)) syntaxClass0049
  have p0006 := @g_opkex (.cv y) (.cv z)
  have freshnessCertificate0212 : t ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0213 : t ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0212)
  have freshnessCertificate0214 : t ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0213)
  have freshnessCertificate0215 :
    t ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0214)
  have freshnessCertificate0216 :
    t ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0215)
  have freshnessCertificate0217 :
    t ∉ ((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0216)
  have freshnessCertificate0218 :
    t ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0214)
  have freshnessCertificate0219 :
    t ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0218)
  have freshnessCertificate0220 : t ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0212)
  have freshnessCertificate0221 : t ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0220)
  have freshnessCertificate0222 :
    t ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0221)
  have freshnessCertificate0223 :
    t ∉ ((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0222)
  have freshnessCertificate0224 : t ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0212)
  have freshnessCertificate0225 :
    t ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0220 freshnessCertificate0224))
  have freshnessCertificate0226 :
    t ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0225)
  have freshnessCertificate0227 : t ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0228 : t ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0227)
  have freshnessCertificate0229 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0228)
  have freshnessCertificate0230 :
    t ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0226 freshnessCertificate0229))
  have freshnessCertificate0231 : t ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0230)
  have freshnessCertificate0232 : t ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0231)
  have freshnessCertificate0233 : t ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0232)
  have freshnessCertificate0234 : t ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0233)
  have freshnessCertificate0235 : t ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0234)
  have freshnessCertificate0236 : t ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0235)
  have freshnessCertificate0237 : t ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0236)
  have freshnessCertificate0238 : t ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0237)
  have freshnessCertificate0239 : t ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0238)
  have freshnessCertificate0240 : t ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0239)
  have freshnessCertificate0241 :
    t ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0216)
  have freshnessCertificate0242 : t ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0241)
  have freshnessCertificate0243 : t ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0242)
  have freshnessCertificate0244 : t ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0243)
  have freshnessCertificate0245 :
    t ∉
      ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0241)
  have freshnessCertificate0246 : t ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0245)
  have freshnessCertificate0247 : t ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0246)
  have freshnessCertificate0248 : t ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0247)
  have freshnessCertificate0249 : t ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0248)
  have freshnessCertificate0250 : t ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0246)
  have freshnessCertificate0251 : t ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0250)
  have freshnessCertificate0252 : t ∉ ((syntaxClass0016).fv) ∪ ((syntaxClass0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0249 freshnessCertificate0251))
  have freshnessCertificate0253 : t ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0252)
  have freshnessCertificate0254 : t ∉ ((syntaxClass0012).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0244 freshnessCertificate0253))
  have freshnessCertificate0255 : t ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0254)
  have freshnessCertificate0256 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0229)
  have freshnessCertificate0257 :
    t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0256)
  have freshnessCertificate0258 :
    t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0257)
  have freshnessCertificate0259 :
    t ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0258)
  have freshnessCertificate0260 : t ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0259)
  have freshnessCertificate0261 : t ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0260)
  have freshnessCertificate0262 : t ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0261)
  have freshnessCertificate0263 : t ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0262)
  have freshnessCertificate0264 : t ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0263)
  have freshnessCertificate0265 : t ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0025).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0255 freshnessCertificate0264))
  have freshnessCertificate0266 : t ∉ (syntaxClass0026).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0265)
  have freshnessCertificate0267 : t ∉ (syntaxClass0027).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0266)
  have freshnessCertificate0268 : t ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0027).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0240 freshnessCertificate0267))
  have freshnessCertificate0269 : t ∉ (syntaxClass0028).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0268)
  have freshnessCertificate0270 :
    t ∉
      (((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv) ∪
        ((syntaxClass0028).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0223 freshnessCertificate0269))
  have freshnessCertificate0271 : t ∉ (syntaxClass0029).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0270)
  have freshnessCertificate0272 : t ∉ ((syntaxClass0029).fv) ∪ ((syntaxClass0022).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0271 freshnessCertificate0261))
  have freshnessCertificate0273 : t ∉ (syntaxClass0030).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0272)
  have freshnessCertificate0274 :
    t ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0030).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0219 freshnessCertificate0273))
  have freshnessCertificate0275 : t ∉ (syntaxClass0031).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0274)
  have freshnessCertificate0276 :
    t ∉
      ((syntaxClass0031).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0275 freshnessCertificate0259))
  have freshnessCertificate0277 : t ∉ (syntaxClass0032).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0276)
  have freshnessCertificate0278 : t ∉ (syntaxClass0033).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0277)
  have freshnessCertificate0279 :
    t ∉
      (((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv) ∪
        ((syntaxClass0033).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0217 freshnessCertificate0278))
  have freshnessCertificate0280 : t ∉ (syntaxClass0034).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0279)
  have freshnessCertificate0281 :
    t ∉
      ((syntaxClass0034).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0280 freshnessCertificate0259))
  have freshnessCertificate0282 : t ∉ (syntaxClass0035).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0281)
  have freshnessCertificate0283 : t ∉ (syntaxClass0036).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0282)
  have freshnessCertificate0284 : t ∉ (syntaxClass0037).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0232)
  have freshnessCertificate0285 : t ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0224)
  have freshnessCertificate0286 :
    t ∉
      (((syn_cins2k (syn_cins3k (syn_cssetk)))).fv) ∪
        (((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0221 freshnessCertificate0218))
  have freshnessCertificate0287 : t ∉ (syntaxClass0038).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0286)
  have freshnessCertificate0288 :
    t ∉ (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪ ((syntaxClass0038).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0285 freshnessCertificate0287))
  have freshnessCertificate0289 : t ∉ (syntaxClass0039).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0288)
  have freshnessCertificate0290 :
    t ∉
      ((syntaxClass0039).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0289 freshnessCertificate0257))
  have freshnessCertificate0291 : t ∉ (syntaxClass0040).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0290)
  have freshnessCertificate0292 : t ∉ ((syntaxClass0037).fv) ∪ ((syntaxClass0040).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0284 freshnessCertificate0291))
  have freshnessCertificate0293 : t ∉ (syntaxClass0041).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0292)
  have freshnessCertificate0294 :
    t ∉ ((syntaxClass0041).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0293 freshnessCertificate0229))
  have freshnessCertificate0295 : t ∉ (syntaxClass0042).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0294)
  have freshnessCertificate0296 : t ∉ (syntaxClass0043).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek];
      exact freshnessCertificate0295)
  have freshnessCertificate0297 : t ∉ (syntaxClass0044).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0296)
  have freshnessCertificate0298 : t ∉ (syntaxClass0045).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0297)
  have freshnessCertificate0299 : t ∉ ((syntaxClass0036).fv) ∪ ((syntaxClass0045).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0283 freshnessCertificate0298))
  have freshnessCertificate0300 : t ∉ (syntaxClass0046).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0299)
  have freshnessCertificate0301 :
    t ∉ ((syntaxClass0046).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0300 freshnessCertificate0256))
  have freshnessCertificate0302 : t ∉ (syntaxClass0047).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0301)
  have freshnessCertificate0303 : t ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0304 : t ∉ ((syn_cpw1 (syn_cnnc))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0303)
  have freshnessCertificate0305 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_cnnc)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0304)
  have freshnessCertificate0306 : t ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ y from (by exact fresh_t_ne_y)))))
  have freshnessCertificate0307 : t ∉ ((Class.cv z)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ z } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ z from (by exact fresh_t_ne_z)))))
  have freshnessCertificate0308 : t ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0306 freshnessCertificate0307))
  have freshnessCertificate0309 : t ∉ ((syn_copk (.cv y) (.cv z))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0308)
  have p0007 :=
    @g_elimak t syntaxClass0047 (syn_cpw1 (syn_cpw1 (syn_cnnc)))
      (syn_copk (.cv y) (.cv z)) (by exact freshnessCertificate0302)
      (by exact freshnessCertificate0305) (by exact freshnessCertificate0309) p0006
  have freshnessCertificate0310 : w ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ t from (by exact fresh_w_ne_t)))))
  have freshnessCertificate0311 : w ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have p0008 :=
    @g_elpw12 w (.cv t) (syn_cnnc) (by exact freshnessCertificate0310)
      (by exact freshnessCertificate0311)
  have p0009 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cnnc))))
      (syn_wrex w (syn_cnnc) (.classEq (.cv t) (syn_csn (syn_csn (.cv w)))))
      syntaxFormula0052 p0008
  have freshnessCertificate0312 : w ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ y from (by exact fresh_w_ne_y)))))
  have freshnessCertificate0313 : w ∉ ((Class.cv z)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show w ∉ ({ z } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show w ≠ z from (by exact fresh_w_ne_z)))))
  have freshnessCertificate0314 : w ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0312 freshnessCertificate0313))
  have freshnessCertificate0315 : w ∉ ((syn_copk (.cv y) (.cv z))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0314)
  have freshnessCertificate0316 :
    w ∉ (((Class.cv t)).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0310 freshnessCertificate0315))
  have freshnessCertificate0317 :
    w ∉ ((syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0316)
  have freshnessCertificate0318 : w ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0319 : w ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0318)
  have freshnessCertificate0320 : w ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0319)
  have freshnessCertificate0321 :
    w ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0320)
  have freshnessCertificate0322 :
    w ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0321)
  have freshnessCertificate0323 :
    w ∉ ((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0322)
  have freshnessCertificate0324 :
    w ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0320)
  have freshnessCertificate0325 :
    w ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0324)
  have freshnessCertificate0326 : w ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0318)
  have freshnessCertificate0327 : w ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0326)
  have freshnessCertificate0328 :
    w ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0327)
  have freshnessCertificate0329 :
    w ∉ ((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0328)
  have freshnessCertificate0330 : w ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0318)
  have freshnessCertificate0331 :
    w ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0326 freshnessCertificate0330))
  have freshnessCertificate0332 :
    w ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0331)
  have freshnessCertificate0333 : w ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show w ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0334 : w ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0333)
  have freshnessCertificate0335 : w ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0334)
  have freshnessCertificate0336 :
    w ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0332 freshnessCertificate0335))
  have freshnessCertificate0337 : w ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0336)
  have freshnessCertificate0338 : w ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0337)
  have freshnessCertificate0339 : w ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0338)
  have freshnessCertificate0340 : w ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0339)
  have freshnessCertificate0341 : w ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0340)
  have freshnessCertificate0342 : w ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0341)
  have freshnessCertificate0343 : w ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0342)
  have freshnessCertificate0344 : w ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0343)
  have freshnessCertificate0345 : w ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0344)
  have freshnessCertificate0346 : w ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0345)
  have freshnessCertificate0347 :
    w ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0322)
  have freshnessCertificate0348 : w ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0347)
  have freshnessCertificate0349 : w ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0348)
  have freshnessCertificate0350 : w ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0349)
  have freshnessCertificate0351 :
    w ∉
      ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0347)
  have freshnessCertificate0352 : w ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0351)
  have freshnessCertificate0353 : w ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0352)
  have freshnessCertificate0354 : w ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0353)
  have freshnessCertificate0355 : w ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0354)
  have freshnessCertificate0356 : w ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0352)
  have freshnessCertificate0357 : w ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0356)
  have freshnessCertificate0358 : w ∉ ((syntaxClass0016).fv) ∪ ((syntaxClass0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0355 freshnessCertificate0357))
  have freshnessCertificate0359 : w ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0358)
  have freshnessCertificate0360 : w ∉ ((syntaxClass0012).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0350 freshnessCertificate0359))
  have freshnessCertificate0361 : w ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0360)
  have freshnessCertificate0362 : w ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0335)
  have freshnessCertificate0363 :
    w ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0362)
  have freshnessCertificate0364 :
    w ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0363)
  have freshnessCertificate0365 :
    w ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0364)
  have freshnessCertificate0366 : w ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0365)
  have freshnessCertificate0367 : w ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0366)
  have freshnessCertificate0368 : w ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0367)
  have freshnessCertificate0369 : w ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0368)
  have freshnessCertificate0370 : w ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0369)
  have freshnessCertificate0371 : w ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0025).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0361 freshnessCertificate0370))
  have freshnessCertificate0372 : w ∉ (syntaxClass0026).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0371)
  have freshnessCertificate0373 : w ∉ (syntaxClass0027).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0372)
  have freshnessCertificate0374 : w ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0027).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0346 freshnessCertificate0373))
  have freshnessCertificate0375 : w ∉ (syntaxClass0028).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0374)
  have freshnessCertificate0376 :
    w ∉
      (((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv) ∪
        ((syntaxClass0028).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0329 freshnessCertificate0375))
  have freshnessCertificate0377 : w ∉ (syntaxClass0029).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0376)
  have freshnessCertificate0378 : w ∉ ((syntaxClass0029).fv) ∪ ((syntaxClass0022).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0377 freshnessCertificate0367))
  have freshnessCertificate0379 : w ∉ (syntaxClass0030).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0378)
  have freshnessCertificate0380 :
    w ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0030).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0325 freshnessCertificate0379))
  have freshnessCertificate0381 : w ∉ (syntaxClass0031).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0380)
  have freshnessCertificate0382 :
    w ∉
      ((syntaxClass0031).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0381 freshnessCertificate0365))
  have freshnessCertificate0383 : w ∉ (syntaxClass0032).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0382)
  have freshnessCertificate0384 : w ∉ (syntaxClass0033).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0383)
  have freshnessCertificate0385 :
    w ∉
      (((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv) ∪
        ((syntaxClass0033).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0323 freshnessCertificate0384))
  have freshnessCertificate0386 : w ∉ (syntaxClass0034).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0385)
  have freshnessCertificate0387 :
    w ∉
      ((syntaxClass0034).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0386 freshnessCertificate0365))
  have freshnessCertificate0388 : w ∉ (syntaxClass0035).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0387)
  have freshnessCertificate0389 : w ∉ (syntaxClass0036).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0388)
  have freshnessCertificate0390 : w ∉ (syntaxClass0037).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0338)
  have freshnessCertificate0391 : w ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0330)
  have freshnessCertificate0392 :
    w ∉
      (((syn_cins2k (syn_cins3k (syn_cssetk)))).fv) ∪
        (((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0327 freshnessCertificate0324))
  have freshnessCertificate0393 : w ∉ (syntaxClass0038).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0392)
  have freshnessCertificate0394 :
    w ∉ (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪ ((syntaxClass0038).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0391 freshnessCertificate0393))
  have freshnessCertificate0395 : w ∉ (syntaxClass0039).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0394)
  have freshnessCertificate0396 :
    w ∉
      ((syntaxClass0039).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0395 freshnessCertificate0363))
  have freshnessCertificate0397 : w ∉ (syntaxClass0040).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0396)
  have freshnessCertificate0398 : w ∉ ((syntaxClass0037).fv) ∪ ((syntaxClass0040).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0390 freshnessCertificate0397))
  have freshnessCertificate0399 : w ∉ (syntaxClass0041).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0398)
  have freshnessCertificate0400 :
    w ∉ ((syntaxClass0041).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0399 freshnessCertificate0335))
  have freshnessCertificate0401 : w ∉ (syntaxClass0042).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0400)
  have freshnessCertificate0402 : w ∉ (syntaxClass0043).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek];
      exact freshnessCertificate0401)
  have freshnessCertificate0403 : w ∉ (syntaxClass0044).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0402)
  have freshnessCertificate0404 : w ∉ (syntaxClass0045).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0403)
  have freshnessCertificate0405 : w ∉ ((syntaxClass0036).fv) ∪ ((syntaxClass0045).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0389 freshnessCertificate0404))
  have freshnessCertificate0406 : w ∉ (syntaxClass0046).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0405)
  have freshnessCertificate0407 :
    w ∉ ((syntaxClass0046).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0406 freshnessCertificate0362))
  have freshnessCertificate0408 : w ∉ (syntaxClass0047).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0407)
  have freshnessCertificate0409 :
    w ∉ (((syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))).fv) ∪ ((syntaxClass0047).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0317 freshnessCertificate0408))
  have freshnessCertificate0410 :
    w ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv z))) syntaxClass0047)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0409)
  have p0010 :=
    @g_r19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv w)))) syntaxFormula0052 w
      (syn_cnnc) (by exact freshnessCertificate0410)
  have p0011 :=
    @g_bitr4i syntaxFormula0053
      (syn_wa (syn_wrex w (syn_cnnc) (.classEq (.cv t) (syn_csn (syn_csn (.cv w)))))
        syntaxFormula0052)
      syntaxFormula0055 p0009 p0010
  have p0012 := @g_exbii syntaxFormula0053 syntaxFormula0055 t p0011
  have p0013 := (Nominal.biimpRefl syntaxFormula0056)
  have p0014 :=
    @g_rexcom4 syntaxFormula0054 w t (syn_cnnc) (by exact freshnessCertificate0303)
      (show w ≠ t from (by exact fresh_w_ne_t))
  have p0015 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0053) (syn_wex t syntaxFormula0055)
      syntaxFormula0056 syntaxFormula0058 p0012 p0013 p0014
  have p0016 := @g_snex (syn_csn (.cv w))
  have p0017 := @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z))
  have p0018 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv w))))
      (syn_copk (.cv t) (syn_copk (.cv y) (.cv z)))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z))) syntaxClass0047
      p0017
  have freshnessCertificate0411 : t ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ w from (by exact fresh_t_ne_w)))))
  have freshnessCertificate0412 : t ∉ ((syn_csn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0411)
  have freshnessCertificate0413 : t ∉ ((syn_csn (syn_csn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0412)
  have freshnessCertificate0414 :
    t ∉ (((syn_csn (syn_csn (.cv w)))).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0413 freshnessCertificate0309))
  have freshnessCertificate0415 :
    t ∉ ((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0414)
  have freshnessCertificate0416 :
    t ∉
      (((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv) ∪
        ((syntaxClass0047).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0415 freshnessCertificate0302))
  have freshnessCertificate0417 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))
          syntaxClass0047)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0416)
  have p0019 :=
    @g_ceqsexv syntaxFormula0052 syntaxFormula0059 t (syn_csn (syn_csn (.cv w)))
      (by exact freshnessCertificate0413) (by exact freshnessCertificate0417) p0016 p0018
  have p0020 := @g_opkex (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z))
  have p0021 :=
    @g_elimak t syntaxClass0046 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))
      (by exact freshnessCertificate0300) (by exact freshnessCertificate0256)
      (by exact freshnessCertificate0415) p0020
  have freshnessCertificate0418 : x ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ t from (by exact fresh_x_ne_t)))))
  have p0022 := @g_elpw131c x (.cv t) (by exact freshnessCertificate0418)
  have p0023 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      syntaxFormula0061 p0022
  have freshnessCertificate0419 : x ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ w from (by exact fresh_x_ne_w)))))
  have freshnessCertificate0420 : x ∉ ((syn_csn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0419)
  have freshnessCertificate0421 : x ∉ ((syn_csn (syn_csn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0420)
  have freshnessCertificate0422 : x ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ y from (by exact fresh_x_ne_y)))))
  have freshnessCertificate0423 : x ∉ ((Class.cv z)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show x ∉ ({ z } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show x ≠ z from (by exact fresh_x_ne_z)))))
  have freshnessCertificate0424 : x ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0422 freshnessCertificate0423))
  have freshnessCertificate0425 : x ∉ ((syn_copk (.cv y) (.cv z))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0424)
  have freshnessCertificate0426 :
    x ∉ (((syn_csn (syn_csn (.cv w)))).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0421 freshnessCertificate0425))
  have freshnessCertificate0427 :
    x ∉ ((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0426)
  have freshnessCertificate0428 :
    x ∉
      (((Class.cv t)).fv) ∪
        (((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0418 freshnessCertificate0427))
  have freshnessCertificate0429 : x ∉ (syntaxClass0060).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0428)
  have freshnessCertificate0430 : x ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0431 : x ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0430)
  have freshnessCertificate0432 : x ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0431)
  have freshnessCertificate0433 :
    x ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0432)
  have freshnessCertificate0434 :
    x ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0433)
  have freshnessCertificate0435 :
    x ∉ ((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0434)
  have freshnessCertificate0436 :
    x ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0432)
  have freshnessCertificate0437 :
    x ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0436)
  have freshnessCertificate0438 : x ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0430)
  have freshnessCertificate0439 : x ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0438)
  have freshnessCertificate0440 :
    x ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0439)
  have freshnessCertificate0441 :
    x ∉ ((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0440)
  have freshnessCertificate0442 : x ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0430)
  have freshnessCertificate0443 :
    x ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0438 freshnessCertificate0442))
  have freshnessCertificate0444 :
    x ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0443)
  have freshnessCertificate0445 : x ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0446 : x ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0445)
  have freshnessCertificate0447 : x ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0446)
  have freshnessCertificate0448 :
    x ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0444 freshnessCertificate0447))
  have freshnessCertificate0449 : x ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0448)
  have freshnessCertificate0450 : x ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0449)
  have freshnessCertificate0451 : x ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0450)
  have freshnessCertificate0452 : x ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0451)
  have freshnessCertificate0453 : x ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0452)
  have freshnessCertificate0454 : x ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0453)
  have freshnessCertificate0455 : x ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0454)
  have freshnessCertificate0456 : x ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0455)
  have freshnessCertificate0457 : x ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0456)
  have freshnessCertificate0458 : x ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0457)
  have freshnessCertificate0459 :
    x ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0434)
  have freshnessCertificate0460 : x ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0459)
  have freshnessCertificate0461 : x ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0460)
  have freshnessCertificate0462 : x ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0461)
  have freshnessCertificate0463 :
    x ∉
      ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0459)
  have freshnessCertificate0464 : x ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0463)
  have freshnessCertificate0465 : x ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0464)
  have freshnessCertificate0466 : x ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0465)
  have freshnessCertificate0467 : x ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0466)
  have freshnessCertificate0468 : x ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0464)
  have freshnessCertificate0469 : x ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0468)
  have freshnessCertificate0470 : x ∉ ((syntaxClass0016).fv) ∪ ((syntaxClass0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0467 freshnessCertificate0469))
  have freshnessCertificate0471 : x ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0470)
  have freshnessCertificate0472 : x ∉ ((syntaxClass0012).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0462 freshnessCertificate0471))
  have freshnessCertificate0473 : x ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0472)
  have freshnessCertificate0474 : x ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0447)
  have freshnessCertificate0475 :
    x ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0474)
  have freshnessCertificate0476 :
    x ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0475)
  have freshnessCertificate0477 :
    x ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0476)
  have freshnessCertificate0478 : x ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0477)
  have freshnessCertificate0479 : x ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0478)
  have freshnessCertificate0480 : x ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0479)
  have freshnessCertificate0481 : x ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0480)
  have freshnessCertificate0482 : x ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0481)
  have freshnessCertificate0483 : x ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0025).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0473 freshnessCertificate0482))
  have freshnessCertificate0484 : x ∉ (syntaxClass0026).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0483)
  have freshnessCertificate0485 : x ∉ (syntaxClass0027).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0484)
  have freshnessCertificate0486 : x ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0027).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0458 freshnessCertificate0485))
  have freshnessCertificate0487 : x ∉ (syntaxClass0028).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0486)
  have freshnessCertificate0488 :
    x ∉
      (((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv) ∪
        ((syntaxClass0028).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0441 freshnessCertificate0487))
  have freshnessCertificate0489 : x ∉ (syntaxClass0029).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0488)
  have freshnessCertificate0490 : x ∉ ((syntaxClass0029).fv) ∪ ((syntaxClass0022).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0489 freshnessCertificate0479))
  have freshnessCertificate0491 : x ∉ (syntaxClass0030).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0490)
  have freshnessCertificate0492 :
    x ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0030).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0437 freshnessCertificate0491))
  have freshnessCertificate0493 : x ∉ (syntaxClass0031).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0492)
  have freshnessCertificate0494 :
    x ∉
      ((syntaxClass0031).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0493 freshnessCertificate0477))
  have freshnessCertificate0495 : x ∉ (syntaxClass0032).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0494)
  have freshnessCertificate0496 : x ∉ (syntaxClass0033).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0495)
  have freshnessCertificate0497 :
    x ∉
      (((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv) ∪
        ((syntaxClass0033).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0435 freshnessCertificate0496))
  have freshnessCertificate0498 : x ∉ (syntaxClass0034).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0497)
  have freshnessCertificate0499 :
    x ∉
      ((syntaxClass0034).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0498 freshnessCertificate0477))
  have freshnessCertificate0500 : x ∉ (syntaxClass0035).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0499)
  have freshnessCertificate0501 : x ∉ (syntaxClass0036).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0500)
  have freshnessCertificate0502 : x ∉ (syntaxClass0037).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0450)
  have freshnessCertificate0503 : x ∉ ((syn_cins2k (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0442)
  have freshnessCertificate0504 :
    x ∉
      (((syn_cins2k (syn_cins3k (syn_cssetk)))).fv) ∪
        (((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0439 freshnessCertificate0436))
  have freshnessCertificate0505 : x ∉ (syntaxClass0038).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0504)
  have freshnessCertificate0506 :
    x ∉ (((syn_cins2k (syn_cins2k (syn_cssetk)))).fv) ∪ ((syntaxClass0038).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0503 freshnessCertificate0505))
  have freshnessCertificate0507 : x ∉ (syntaxClass0039).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0506)
  have freshnessCertificate0508 :
    x ∉
      ((syntaxClass0039).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0507 freshnessCertificate0475))
  have freshnessCertificate0509 : x ∉ (syntaxClass0040).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0508)
  have freshnessCertificate0510 : x ∉ ((syntaxClass0037).fv) ∪ ((syntaxClass0040).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0502 freshnessCertificate0509))
  have freshnessCertificate0511 : x ∉ (syntaxClass0041).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0510)
  have freshnessCertificate0512 :
    x ∉ ((syntaxClass0041).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0511 freshnessCertificate0447))
  have freshnessCertificate0513 : x ∉ (syntaxClass0042).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0512)
  have freshnessCertificate0514 : x ∉ (syntaxClass0043).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek];
      exact freshnessCertificate0513)
  have freshnessCertificate0515 : x ∉ (syntaxClass0044).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0514)
  have freshnessCertificate0516 : x ∉ (syntaxClass0045).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0515)
  have freshnessCertificate0517 : x ∉ ((syntaxClass0036).fv) ∪ ((syntaxClass0045).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0501 freshnessCertificate0516))
  have freshnessCertificate0518 : x ∉ (syntaxClass0046).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0517)
  have freshnessCertificate0519 : x ∉ ((syntaxClass0060).fv) ∪ ((syntaxClass0046).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0429 freshnessCertificate0518))
  have freshnessCertificate0520 :
    x ∉ ((Wff.classMem syntaxClass0060 syntaxClass0046)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0519)
  have p0024 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      syntaxFormula0061 x (by exact freshnessCertificate0520)
  have p0025 :=
    @g_bitr4i syntaxFormula0062
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
        syntaxFormula0061)
      syntaxFormula0064 p0023 p0024
  have p0026 := @g_exbii syntaxFormula0062 syntaxFormula0064 t p0025
  have p0027 := (Nominal.biimpRefl syntaxFormula0065)
  have p0028 := @g_excom syntaxFormula0063 x t
  have p0029 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0062) (syn_wex t syntaxFormula0064)
      syntaxFormula0065 syntaxFormula0067 p0026 p0027 p0028
  have p0030 := @g_snex (syn_csn (syn_csn (syn_csn (.cv x))))
  have p0031 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))
  have p0032 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      syntaxClass0060 syntaxClass0068 syntaxClass0046 p0031
  have freshnessCertificate0521 : t ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ x from (by exact fresh_t_ne_x)))))
  have freshnessCertificate0522 : t ∉ ((syn_csn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0521)
  have freshnessCertificate0523 : t ∉ ((syn_csn (syn_csn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0522)
  have freshnessCertificate0524 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0523)
  have freshnessCertificate0525 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0524)
  have freshnessCertificate0526 :
    t ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv) ∪
        (((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0525 freshnessCertificate0415))
  have freshnessCertificate0527 : t ∉ (syntaxClass0068).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0526)
  have freshnessCertificate0528 : t ∉ ((syntaxClass0068).fv) ∪ ((syntaxClass0046).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0527 freshnessCertificate0300))
  have freshnessCertificate0529 :
    t ∉ ((Wff.classMem syntaxClass0068 syntaxClass0046)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0528)
  have p0033 :=
    @g_ceqsexv syntaxFormula0061 syntaxFormula0069 t
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))) (by exact freshnessCertificate0525)
      (by exact freshnessCertificate0529) p0030 p0032
  have p0034 := @g_elin syntaxClass0068 syntaxClass0036 syntaxClass0045
  have p0035 :=
    @g_opkex (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))
  have p0036 :=
    @g_elimak t syntaxClass0034
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      syntaxClass0068 (by exact freshnessCertificate0280)
      (by exact freshnessCertificate0259) (by exact freshnessCertificate0527) p0035
  have freshnessCertificate0530 : c ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ t from (by exact fresh_c_ne_t)))))
  have p0037 := @g_elpw161c c (.cv t) (by exact freshnessCertificate0530)
  have p0038 :=
    @g_anbi1i syntaxFormula0070 (syn_wex c syntaxFormula0071) syntaxFormula0073 p0037
  have freshnessCertificate0531 : c ∉ ((Class.cv x)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ x } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ x from (by exact fresh_c_ne_x)))))
  have freshnessCertificate0532 : c ∉ ((syn_csn (.cv x))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0531)
  have freshnessCertificate0533 : c ∉ ((syn_csn (syn_csn (.cv x)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0532)
  have freshnessCertificate0534 : c ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0533)
  have freshnessCertificate0535 :
    c ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0534)
  have freshnessCertificate0536 : c ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ w from (by exact fresh_c_ne_w)))))
  have freshnessCertificate0537 : c ∉ ((syn_csn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0536)
  have freshnessCertificate0538 : c ∉ ((syn_csn (syn_csn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0537)
  have freshnessCertificate0539 : c ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ y from (by exact fresh_c_ne_y)))))
  have freshnessCertificate0540 : c ∉ ((Class.cv z)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show c ∉ ({ z } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show c ≠ z from (by exact fresh_c_ne_z)))))
  have freshnessCertificate0541 : c ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0539 freshnessCertificate0540))
  have freshnessCertificate0542 : c ∉ ((syn_copk (.cv y) (.cv z))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0541)
  have freshnessCertificate0543 :
    c ∉ (((syn_csn (syn_csn (.cv w)))).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0538 freshnessCertificate0542))
  have freshnessCertificate0544 :
    c ∉ ((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0543)
  have freshnessCertificate0545 :
    c ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))).fv) ∪
        (((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0535 freshnessCertificate0544))
  have freshnessCertificate0546 : c ∉ (syntaxClass0068).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0545)
  have freshnessCertificate0547 : c ∉ (((Class.cv t)).fv) ∪ ((syntaxClass0068).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0530 freshnessCertificate0546))
  have freshnessCertificate0548 : c ∉ (syntaxClass0072).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0547)
  have freshnessCertificate0549 : c ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0550 : c ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0549)
  have freshnessCertificate0551 : c ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0550)
  have freshnessCertificate0552 :
    c ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0551)
  have freshnessCertificate0553 :
    c ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0552)
  have freshnessCertificate0554 :
    c ∉ ((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0553)
  have freshnessCertificate0555 :
    c ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0551)
  have freshnessCertificate0556 :
    c ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0555)
  have freshnessCertificate0557 : c ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0549)
  have freshnessCertificate0558 : c ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0557)
  have freshnessCertificate0559 :
    c ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0558)
  have freshnessCertificate0560 :
    c ∉ ((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0559)
  have freshnessCertificate0561 : c ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0549)
  have freshnessCertificate0562 :
    c ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0557 freshnessCertificate0561))
  have freshnessCertificate0563 :
    c ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0562)
  have freshnessCertificate0564 : c ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show c ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0565 : c ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0564)
  have freshnessCertificate0566 : c ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0565)
  have freshnessCertificate0567 :
    c ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0563 freshnessCertificate0566))
  have freshnessCertificate0568 : c ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0567)
  have freshnessCertificate0569 : c ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0568)
  have freshnessCertificate0570 : c ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0569)
  have freshnessCertificate0571 : c ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0570)
  have freshnessCertificate0572 : c ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0571)
  have freshnessCertificate0573 : c ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0572)
  have freshnessCertificate0574 : c ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0573)
  have freshnessCertificate0575 : c ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0574)
  have freshnessCertificate0576 : c ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0575)
  have freshnessCertificate0577 : c ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0576)
  have freshnessCertificate0578 :
    c ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0553)
  have freshnessCertificate0579 : c ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0578)
  have freshnessCertificate0580 : c ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0579)
  have freshnessCertificate0581 : c ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0580)
  have freshnessCertificate0582 :
    c ∉
      ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0578)
  have freshnessCertificate0583 : c ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0582)
  have freshnessCertificate0584 : c ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0583)
  have freshnessCertificate0585 : c ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0584)
  have freshnessCertificate0586 : c ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0585)
  have freshnessCertificate0587 : c ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0583)
  have freshnessCertificate0588 : c ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0587)
  have freshnessCertificate0589 : c ∉ ((syntaxClass0016).fv) ∪ ((syntaxClass0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0586 freshnessCertificate0588))
  have freshnessCertificate0590 : c ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0589)
  have freshnessCertificate0591 : c ∉ ((syntaxClass0012).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0581 freshnessCertificate0590))
  have freshnessCertificate0592 : c ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0591)
  have freshnessCertificate0593 : c ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0566)
  have freshnessCertificate0594 :
    c ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0593)
  have freshnessCertificate0595 :
    c ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0594)
  have freshnessCertificate0596 :
    c ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0595)
  have freshnessCertificate0597 : c ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0596)
  have freshnessCertificate0598 : c ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0597)
  have freshnessCertificate0599 : c ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0598)
  have freshnessCertificate0600 : c ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0599)
  have freshnessCertificate0601 : c ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0600)
  have freshnessCertificate0602 : c ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0025).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0592 freshnessCertificate0601))
  have freshnessCertificate0603 : c ∉ (syntaxClass0026).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0602)
  have freshnessCertificate0604 : c ∉ (syntaxClass0027).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0603)
  have freshnessCertificate0605 : c ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0027).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0577 freshnessCertificate0604))
  have freshnessCertificate0606 : c ∉ (syntaxClass0028).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0605)
  have freshnessCertificate0607 :
    c ∉
      (((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv) ∪
        ((syntaxClass0028).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0560 freshnessCertificate0606))
  have freshnessCertificate0608 : c ∉ (syntaxClass0029).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0607)
  have freshnessCertificate0609 : c ∉ ((syntaxClass0029).fv) ∪ ((syntaxClass0022).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0608 freshnessCertificate0598))
  have freshnessCertificate0610 : c ∉ (syntaxClass0030).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0609)
  have freshnessCertificate0611 :
    c ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0030).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0556 freshnessCertificate0610))
  have freshnessCertificate0612 : c ∉ (syntaxClass0031).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0611)
  have freshnessCertificate0613 :
    c ∉
      ((syntaxClass0031).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0612 freshnessCertificate0596))
  have freshnessCertificate0614 : c ∉ (syntaxClass0032).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0613)
  have freshnessCertificate0615 : c ∉ (syntaxClass0033).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0614)
  have freshnessCertificate0616 :
    c ∉
      (((syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv) ∪
        ((syntaxClass0033).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0554 freshnessCertificate0615))
  have freshnessCertificate0617 : c ∉ (syntaxClass0034).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0616)
  have freshnessCertificate0618 : c ∉ ((syntaxClass0072).fv) ∪ ((syntaxClass0034).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0548 freshnessCertificate0617))
  have freshnessCertificate0619 :
    c ∉ ((Wff.classMem syntaxClass0072 syntaxClass0034)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0618)
  have p0039 :=
    @g_n_19_41v syntaxFormula0071 syntaxFormula0073 c (by exact freshnessCertificate0619)
  have p0040 :=
    @g_bitr4i syntaxFormula0074 (syn_wa (syn_wex c syntaxFormula0071) syntaxFormula0073)
      syntaxFormula0076 p0038 p0039
  have p0041 := @g_exbii syntaxFormula0074 syntaxFormula0076 t p0040
  have p0042 := (Nominal.biimpRefl syntaxFormula0077)
  have p0043 := @g_excom syntaxFormula0075 c t
  have p0044 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0074) (syn_wex t syntaxFormula0076)
      syntaxFormula0077 syntaxFormula0079 p0041 p0042 p0043
  have p0045 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))))
  have p0046 :=
    @g_opkeq1 (.cv t)
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))))
      syntaxClass0068
  have p0047 :=
    @g_eleq1d syntaxFormula0071 syntaxClass0072 syntaxClass0080 syntaxClass0034 p0046
  have freshnessCertificate0620 : t ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ c from (by exact fresh_t_ne_c)))))
  have freshnessCertificate0621 : t ∉ ((syn_csn (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0620)
  have freshnessCertificate0622 : t ∉ ((syn_csn (syn_csn (.cv c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0621)
  have freshnessCertificate0623 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0622)
  have freshnessCertificate0624 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0623)
  have freshnessCertificate0625 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0624)
  have freshnessCertificate0626 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0625)
  have freshnessCertificate0627 :
    t ∉
      ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0626)
  have freshnessCertificate0628 :
    t ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))))).fv) ∪
        ((syntaxClass0068).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0627 freshnessCertificate0527))
  have freshnessCertificate0629 : t ∉ (syntaxClass0080).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0628)
  have freshnessCertificate0630 : t ∉ ((syntaxClass0080).fv) ∪ ((syntaxClass0034).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0629 freshnessCertificate0280))
  have freshnessCertificate0631 :
    t ∉ ((Wff.classMem syntaxClass0080 syntaxClass0034)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0630)
  have p0048 :=
    @g_ceqsexv syntaxFormula0073 syntaxFormula0081 t
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))))
      (by exact freshnessCertificate0627) (by exact freshnessCertificate0631) p0045 p0047
  have p0049 :=
    @g_elsymdif syntaxClass0080
      (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
      syntaxClass0033
  have p0050 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))
  have p0051 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0050 p0030 p0020
  have p0052 := @g_snex (syn_csn (syn_csn (syn_csn (.cv c))))
  have p0053 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0054 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))
      (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csik (syn_csik (syn_csik (syn_cssetk))))
      p0052 p0053
  have p0055 := @g_snex (syn_csn (syn_csn (.cv c)))
  have p0056 := @g_snex (syn_csn (.cv x))
  have p0057 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (.cv c)))) (syn_csn (syn_csn (.cv x)))
      (syn_csik (syn_csik (syn_cssetk))) p0055 p0056
  have p0058 := @g_snex (syn_csn (.cv c))
  have p0059 := @g_snex (.cv x)
  have p0060 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv c))) (syn_csn (.cv x)) (syn_csik (syn_cssetk))
      p0058 p0059
  have p0061 := @g_snex (.cv c)
  have p0062 := @g_vex x
  have p0063 := @g_opksnelsik (syn_csn (.cv c)) (.cv x) (syn_cssetk) p0061 p0062
  have p0064 := @g_vex c
  have p0065 := @g_elssetk (.cv c) (.cv x) p0064 p0062
  have p0066_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv c)) (.cv x)) (syn_cssetk)) (.objMem c x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
      p0065
  have p0066 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv c))) (syn_csn (.cv x)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv c)) (.cv x)) (syn_cssetk)) (.objMem c x) p0063
      p0066_e01_recanon
  have p0067 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))
          (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv c)))) (syn_csn (syn_csn (.cv x))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv c))) (syn_csn (.cv x)))
        (syn_csik (syn_cssetk)))
      (.objMem c x) p0057 p0060 p0066
  have p0068 :=
    @g_n_3bitri syntaxFormula0082
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))
          (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
        (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))
          (syn_csn (syn_csn (syn_csn (.cv x))))) (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
      (.objMem c x) p0051 p0054 p0067
  have p0069 :=
    @g_opkex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))
  have freshnessCertificate0632 :
    t ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))).fv) ∪
        (((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0625 freshnessCertificate0415))
  have freshnessCertificate0633 : t ∉ (syntaxClass0083).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0632)
  have p0070 :=
    @g_elimak t syntaxClass0031
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      syntaxClass0083 (by exact freshnessCertificate0275)
      (by exact freshnessCertificate0259) (by exact freshnessCertificate0633) p0069
  have freshnessCertificate0634 : b ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ t from (by exact fresh_b_ne_t)))))
  have p0071 := @g_elpw161c b (.cv t) (by exact freshnessCertificate0634)
  have p0072 :=
    @g_anbi1i syntaxFormula0070 (syn_wex b syntaxFormula0084) syntaxFormula0086 p0071
  have freshnessCertificate0635 : b ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ c from (by exact fresh_b_ne_c)))))
  have freshnessCertificate0636 : b ∉ ((syn_csn (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0635)
  have freshnessCertificate0637 : b ∉ ((syn_csn (syn_csn (.cv c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0636)
  have freshnessCertificate0638 : b ∉ ((syn_csn (syn_csn (syn_csn (.cv c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0637)
  have freshnessCertificate0639 :
    b ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0638)
  have freshnessCertificate0640 :
    b ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0639)
  have freshnessCertificate0641 : b ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ w from (by exact fresh_b_ne_w)))))
  have freshnessCertificate0642 : b ∉ ((syn_csn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0641)
  have freshnessCertificate0643 : b ∉ ((syn_csn (syn_csn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0642)
  have freshnessCertificate0644 : b ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ y from (by exact fresh_b_ne_y)))))
  have freshnessCertificate0645 : b ∉ ((Class.cv z)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show b ∉ ({ z } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show b ≠ z from (by exact fresh_b_ne_z)))))
  have freshnessCertificate0646 : b ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0644 freshnessCertificate0645))
  have freshnessCertificate0647 : b ∉ ((syn_copk (.cv y) (.cv z))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0646)
  have freshnessCertificate0648 :
    b ∉ (((syn_csn (syn_csn (.cv w)))).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0643 freshnessCertificate0647))
  have freshnessCertificate0649 :
    b ∉ ((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0648)
  have freshnessCertificate0650 :
    b ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))).fv) ∪
        (((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0640 freshnessCertificate0649))
  have freshnessCertificate0651 : b ∉ (syntaxClass0083).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0650)
  have freshnessCertificate0652 : b ∉ (((Class.cv t)).fv) ∪ ((syntaxClass0083).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0634 freshnessCertificate0651))
  have freshnessCertificate0653 : b ∉ (syntaxClass0085).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0652)
  have freshnessCertificate0654 : b ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0655 : b ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0654)
  have freshnessCertificate0656 : b ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0655)
  have freshnessCertificate0657 :
    b ∉ ((syn_cins3k (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0656)
  have freshnessCertificate0658 :
    b ∉ ((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0657)
  have freshnessCertificate0659 : b ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0654)
  have freshnessCertificate0660 : b ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0659)
  have freshnessCertificate0661 :
    b ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0660)
  have freshnessCertificate0662 :
    b ∉ ((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0661)
  have freshnessCertificate0663 : b ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0654)
  have freshnessCertificate0664 :
    b ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0659 freshnessCertificate0663))
  have freshnessCertificate0665 :
    b ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0664)
  have freshnessCertificate0666 : b ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show b ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0667 : b ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0666)
  have freshnessCertificate0668 : b ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0667)
  have freshnessCertificate0669 :
    b ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0665 freshnessCertificate0668))
  have freshnessCertificate0670 : b ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0669)
  have freshnessCertificate0671 : b ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0670)
  have freshnessCertificate0672 : b ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0671)
  have freshnessCertificate0673 : b ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0672)
  have freshnessCertificate0674 : b ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0673)
  have freshnessCertificate0675 : b ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0674)
  have freshnessCertificate0676 : b ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0675)
  have freshnessCertificate0677 : b ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0676)
  have freshnessCertificate0678 : b ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0677)
  have freshnessCertificate0679 : b ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0678)
  have freshnessCertificate0680 :
    b ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0656)
  have freshnessCertificate0681 :
    b ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0680)
  have freshnessCertificate0682 :
    b ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0681)
  have freshnessCertificate0683 : b ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0682)
  have freshnessCertificate0684 : b ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0683)
  have freshnessCertificate0685 : b ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0684)
  have freshnessCertificate0686 :
    b ∉
      ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0682)
  have freshnessCertificate0687 : b ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0686)
  have freshnessCertificate0688 : b ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0687)
  have freshnessCertificate0689 : b ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0688)
  have freshnessCertificate0690 : b ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0689)
  have freshnessCertificate0691 : b ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0687)
  have freshnessCertificate0692 : b ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0691)
  have freshnessCertificate0693 : b ∉ ((syntaxClass0016).fv) ∪ ((syntaxClass0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0690 freshnessCertificate0692))
  have freshnessCertificate0694 : b ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0693)
  have freshnessCertificate0695 : b ∉ ((syntaxClass0012).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0685 freshnessCertificate0694))
  have freshnessCertificate0696 : b ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0695)
  have freshnessCertificate0697 : b ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0668)
  have freshnessCertificate0698 :
    b ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0697)
  have freshnessCertificate0699 :
    b ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0698)
  have freshnessCertificate0700 :
    b ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0699)
  have freshnessCertificate0701 : b ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0700)
  have freshnessCertificate0702 : b ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0701)
  have freshnessCertificate0703 : b ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0702)
  have freshnessCertificate0704 : b ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0703)
  have freshnessCertificate0705 : b ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0704)
  have freshnessCertificate0706 : b ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0025).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0696 freshnessCertificate0705))
  have freshnessCertificate0707 : b ∉ (syntaxClass0026).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0706)
  have freshnessCertificate0708 : b ∉ (syntaxClass0027).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0707)
  have freshnessCertificate0709 : b ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0027).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0679 freshnessCertificate0708))
  have freshnessCertificate0710 : b ∉ (syntaxClass0028).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0709)
  have freshnessCertificate0711 :
    b ∉
      (((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv) ∪
        ((syntaxClass0028).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0662 freshnessCertificate0710))
  have freshnessCertificate0712 : b ∉ (syntaxClass0029).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0711)
  have freshnessCertificate0713 : b ∉ ((syntaxClass0029).fv) ∪ ((syntaxClass0022).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0712 freshnessCertificate0702))
  have freshnessCertificate0714 : b ∉ (syntaxClass0030).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0713)
  have freshnessCertificate0715 :
    b ∉
      (((syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))).fv) ∪
        ((syntaxClass0030).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0658 freshnessCertificate0714))
  have freshnessCertificate0716 : b ∉ (syntaxClass0031).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0715)
  have freshnessCertificate0717 : b ∉ ((syntaxClass0085).fv) ∪ ((syntaxClass0031).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0653 freshnessCertificate0716))
  have freshnessCertificate0718 :
    b ∉ ((Wff.classMem syntaxClass0085 syntaxClass0031)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0717)
  have p0073 :=
    @g_n_19_41v syntaxFormula0084 syntaxFormula0086 b (by exact freshnessCertificate0718)
  have p0074 :=
    @g_bitr4i syntaxFormula0087 (syn_wa (syn_wex b syntaxFormula0084) syntaxFormula0086)
      syntaxFormula0089 p0072 p0073
  have p0075 := @g_exbii syntaxFormula0087 syntaxFormula0089 t p0074
  have p0076 := (Nominal.biimpRefl syntaxFormula0090)
  have p0077 := @g_excom syntaxFormula0088 b t
  have p0078 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0087) (syn_wex t syntaxFormula0089)
      syntaxFormula0090 syntaxFormula0092 p0075 p0076 p0077
  have p0079 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
  have p0080 :=
    @g_opkeq1 (.cv t)
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
      syntaxClass0083
  have p0081 :=
    @g_eleq1d syntaxFormula0084 syntaxClass0085 syntaxClass0093 syntaxClass0031 p0080
  have freshnessCertificate0719 : t ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ b from (by exact fresh_t_ne_b)))))
  have freshnessCertificate0720 : t ∉ ((syn_csn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0719)
  have freshnessCertificate0721 : t ∉ ((syn_csn (syn_csn (.cv b)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0720)
  have freshnessCertificate0722 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv b))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0721)
  have freshnessCertificate0723 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0722)
  have freshnessCertificate0724 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0723)
  have freshnessCertificate0725 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0724)
  have freshnessCertificate0726 :
    t ∉
      ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0725)
  have freshnessCertificate0727 :
    t ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))).fv) ∪
        ((syntaxClass0083).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0726 freshnessCertificate0633))
  have freshnessCertificate0728 : t ∉ (syntaxClass0093).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0727)
  have freshnessCertificate0729 : t ∉ ((syntaxClass0093).fv) ∪ ((syntaxClass0031).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0728 freshnessCertificate0275))
  have freshnessCertificate0730 :
    t ∉ ((Wff.classMem syntaxClass0093 syntaxClass0031)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0729)
  have p0082 :=
    @g_ceqsexv syntaxFormula0086 syntaxFormula0094 t
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
      (by exact freshnessCertificate0726) (by exact freshnessCertificate0730) p0079 p0081
  have p0083 :=
    @g_elin syntaxClass0093 (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))
      syntaxClass0030
  have p0084 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
  have p0085 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))
      (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) p0084 p0050 p0020
  have p0086 := @g_snex (syn_csn (syn_csn (.cv b)))
  have p0087 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_csn (syn_csn (.cv w)))
      (syn_copk (.cv y) (.cv z)) (syn_csik (syn_csik (syn_cssetk))) p0086 p0016 p0006
  have p0088 := @g_snex (syn_csn (.cv b))
  have p0089 := @g_snex (.cv w)
  have p0090 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv b))) (syn_csn (.cv w)) (syn_csik (syn_cssetk))
      p0088 p0089
  have p0091 := @g_snex (.cv b)
  have p0092 := @g_vex w
  have p0093 := @g_opksnelsik (syn_csn (.cv b)) (.cv w) (syn_cssetk) p0091 p0092
  have p0094 := @g_vex b
  have p0095 := @g_elssetk (.cv b) (.cv w) p0094 p0092
  have p0096_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv b)) (.cv w)) (syn_cssetk)) (.objMem b w)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
      p0095
  have p0096 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_csn (syn_csn (.cv w))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (.cv w)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv b)) (.cv w)) (syn_cssetk)) (.objMem b w) p0090
      p0093 p0096_e02_recanon
  have p0097 :=
    @g_n_3bitri syntaxFormula0095
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
          (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z))))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_csn (syn_csn (.cv w))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.objMem b w) p0085 p0087 p0096
  have p0098 :=
    @g_opkex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
      syntaxClass0083
  have p0099 :=
    @g_elimak t syntaxClass0029 syntaxClass0022 syntaxClass0093
      (by exact freshnessCertificate0271) (by exact freshnessCertificate0261)
      (by exact freshnessCertificate0728) p0098
  have freshnessCertificate0731 : a ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ t from (by exact fresh_a_ne_t)))))
  have p0100 := @g_elpw181c a (.cv t) (by exact freshnessCertificate0731)
  have p0101 :=
    @g_anbi1i syntaxFormula0096 (syn_wex a syntaxFormula0099) syntaxFormula0101 p0100
  have freshnessCertificate0732 : a ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ b from (by exact fresh_a_ne_b)))))
  have freshnessCertificate0733 : a ∉ ((syn_csn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0732)
  have freshnessCertificate0734 : a ∉ ((syn_csn (syn_csn (.cv b)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0733)
  have freshnessCertificate0735 : a ∉ ((syn_csn (syn_csn (syn_csn (.cv b))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0734)
  have freshnessCertificate0736 :
    a ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0735)
  have freshnessCertificate0737 :
    a ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0736)
  have freshnessCertificate0738 :
    a ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0737)
  have freshnessCertificate0739 :
    a ∉
      ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0738)
  have freshnessCertificate0740 : a ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ c from (by exact fresh_a_ne_c)))))
  have freshnessCertificate0741 : a ∉ ((syn_csn (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0740)
  have freshnessCertificate0742 : a ∉ ((syn_csn (syn_csn (.cv c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0741)
  have freshnessCertificate0743 : a ∉ ((syn_csn (syn_csn (syn_csn (.cv c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0742)
  have freshnessCertificate0744 :
    a ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0743)
  have freshnessCertificate0745 :
    a ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0744)
  have freshnessCertificate0746 : a ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ w from (by exact fresh_a_ne_w)))))
  have freshnessCertificate0747 : a ∉ ((syn_csn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0746)
  have freshnessCertificate0748 : a ∉ ((syn_csn (syn_csn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0747)
  have freshnessCertificate0749 : a ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ y from (by exact fresh_a_ne_y)))))
  have freshnessCertificate0750 : a ∉ ((Class.cv z)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show a ∉ ({ z } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show a ≠ z from (by exact fresh_a_ne_z)))))
  have freshnessCertificate0751 : a ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0749 freshnessCertificate0750))
  have freshnessCertificate0752 : a ∉ ((syn_copk (.cv y) (.cv z))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0751)
  have freshnessCertificate0753 :
    a ∉ (((syn_csn (syn_csn (.cv w)))).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0748 freshnessCertificate0752))
  have freshnessCertificate0754 :
    a ∉ ((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0753)
  have freshnessCertificate0755 :
    a ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))).fv) ∪
        (((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0745 freshnessCertificate0754))
  have freshnessCertificate0756 : a ∉ (syntaxClass0083).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0755)
  have freshnessCertificate0757 :
    a ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))).fv) ∪
        ((syntaxClass0083).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0739 freshnessCertificate0756))
  have freshnessCertificate0758 : a ∉ (syntaxClass0093).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0757)
  have freshnessCertificate0759 : a ∉ (((Class.cv t)).fv) ∪ ((syntaxClass0093).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0731 freshnessCertificate0758))
  have freshnessCertificate0760 : a ∉ (syntaxClass0100).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0759)
  have freshnessCertificate0761 : a ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0762 : a ∉ ((syn_cins3k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0761)
  have freshnessCertificate0763 : a ∉ ((syn_cins2k (syn_cins3k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0762)
  have freshnessCertificate0764 :
    a ∉ ((syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0763)
  have freshnessCertificate0765 :
    a ∉ ((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0764)
  have freshnessCertificate0766 : a ∉ ((syn_cins2k (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0761)
  have freshnessCertificate0767 :
    a ∉ (((syn_cins3k (syn_cssetk))).fv) ∪ (((syn_cins2k (syn_cssetk))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0762 freshnessCertificate0766))
  have freshnessCertificate0768 :
    a ∉ ((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0767)
  have freshnessCertificate0769 : a ∉ ((syn_c1c)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
      exact (show a ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0770 : a ∉ ((syn_cpw1 (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0769)
  have freshnessCertificate0771 : a ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0770)
  have freshnessCertificate0772 :
    a ∉
      (((syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))).fv) ∪
        (((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0768 freshnessCertificate0771))
  have freshnessCertificate0773 : a ∉ (syntaxClass0000).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0772)
  have freshnessCertificate0774 : a ∉ (syntaxClass0001).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0773)
  have freshnessCertificate0775 : a ∉ (syntaxClass0002).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0774)
  have freshnessCertificate0776 : a ∉ (syntaxClass0003).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0775)
  have freshnessCertificate0777 : a ∉ (syntaxClass0004).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0776)
  have freshnessCertificate0778 : a ∉ (syntaxClass0005).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0777)
  have freshnessCertificate0779 : a ∉ (syntaxClass0006).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0778)
  have freshnessCertificate0780 : a ∉ (syntaxClass0007).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0779)
  have freshnessCertificate0781 : a ∉ (syntaxClass0008).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0780)
  have freshnessCertificate0782 : a ∉ (syntaxClass0009).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0781)
  have freshnessCertificate0783 : a ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0761)
  have freshnessCertificate0784 : a ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0783)
  have freshnessCertificate0785 :
    a ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0784)
  have freshnessCertificate0786 :
    a ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0785)
  have freshnessCertificate0787 :
    a ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0786)
  have freshnessCertificate0788 : a ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0787)
  have freshnessCertificate0789 : a ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0788)
  have freshnessCertificate0790 : a ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0789)
  have freshnessCertificate0791 :
    a ∉
      ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0787)
  have freshnessCertificate0792 : a ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0791)
  have freshnessCertificate0793 : a ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0792)
  have freshnessCertificate0794 : a ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0793)
  have freshnessCertificate0795 : a ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0794)
  have freshnessCertificate0796 : a ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0792)
  have freshnessCertificate0797 : a ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0796)
  have freshnessCertificate0798 : a ∉ ((syntaxClass0016).fv) ∪ ((syntaxClass0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0795 freshnessCertificate0797))
  have freshnessCertificate0799 : a ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0798)
  have freshnessCertificate0800 : a ∉ ((syntaxClass0012).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0790 freshnessCertificate0799))
  have freshnessCertificate0801 : a ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0800)
  have freshnessCertificate0802 : a ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0771)
  have freshnessCertificate0803 :
    a ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0802)
  have freshnessCertificate0804 :
    a ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0803)
  have freshnessCertificate0805 :
    a ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0804)
  have freshnessCertificate0806 : a ∉ (syntaxClass0021).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0805)
  have freshnessCertificate0807 : a ∉ (syntaxClass0022).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0806)
  have freshnessCertificate0808 : a ∉ (syntaxClass0023).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0807)
  have freshnessCertificate0809 : a ∉ (syntaxClass0024).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0808)
  have freshnessCertificate0810 : a ∉ (syntaxClass0025).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0809)
  have freshnessCertificate0811 : a ∉ ((syntaxClass0020).fv) ∪ ((syntaxClass0025).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0801 freshnessCertificate0810))
  have freshnessCertificate0812 : a ∉ (syntaxClass0026).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0811)
  have freshnessCertificate0813 : a ∉ (syntaxClass0027).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl];
      exact freshnessCertificate0812)
  have freshnessCertificate0814 : a ∉ ((syntaxClass0009).fv) ∪ ((syntaxClass0027).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0782 freshnessCertificate0813))
  have freshnessCertificate0815 : a ∉ (syntaxClass0028).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0814)
  have freshnessCertificate0816 :
    a ∉
      (((syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))).fv) ∪
        ((syntaxClass0028).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0765 freshnessCertificate0815))
  have freshnessCertificate0817 : a ∉ (syntaxClass0029).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0816)
  have freshnessCertificate0818 : a ∉ ((syntaxClass0100).fv) ∪ ((syntaxClass0029).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0760 freshnessCertificate0817))
  have freshnessCertificate0819 :
    a ∉ ((Wff.classMem syntaxClass0100 syntaxClass0029)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0818)
  have p0102 :=
    @g_n_19_41v syntaxFormula0099 syntaxFormula0101 a (by exact freshnessCertificate0819)
  have p0103 :=
    @g_bitr4i syntaxFormula0102 (syn_wa (syn_wex a syntaxFormula0099) syntaxFormula0101)
      syntaxFormula0104 p0101 p0102
  have p0104 := @g_exbii syntaxFormula0102 syntaxFormula0104 t p0103
  have p0105 := (Nominal.biimpRefl syntaxFormula0105)
  have p0106 := @g_excom syntaxFormula0103 a t
  have p0107 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0102) (syn_wex t syntaxFormula0104)
      syntaxFormula0105 syntaxFormula0107 p0104 p0105 p0106
  have p0108 := @g_snex syntaxClass0097
  have p0109 := @g_opkeq1 (.cv t) syntaxClass0098 syntaxClass0093
  have p0110 :=
    @g_eleq1d syntaxFormula0099 syntaxClass0100 syntaxClass0108 syntaxClass0029 p0109
  have freshnessCertificate0820 : t ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ a from (by exact fresh_t_ne_a)))))
  have freshnessCertificate0821 : t ∉ ((syn_csn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0820)
  have freshnessCertificate0822 : t ∉ ((syn_csn (syn_csn (.cv a)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0821)
  have freshnessCertificate0823 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv a))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0822)
  have freshnessCertificate0824 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0823)
  have freshnessCertificate0825 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0824)
  have freshnessCertificate0826 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0825)
  have freshnessCertificate0827 :
    t ∉
      ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0826)
  have freshnessCertificate0828 : t ∉ (syntaxClass0097).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0827)
  have freshnessCertificate0829 : t ∉ (syntaxClass0098).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0828)
  have freshnessCertificate0830 : t ∉ ((syntaxClass0098).fv) ∪ ((syntaxClass0093).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0829 freshnessCertificate0728))
  have freshnessCertificate0831 : t ∉ (syntaxClass0108).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0830)
  have freshnessCertificate0832 : t ∉ ((syntaxClass0108).fv) ∪ ((syntaxClass0029).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0831 freshnessCertificate0271))
  have freshnessCertificate0833 :
    t ∉ ((Wff.classMem syntaxClass0108 syntaxClass0029)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0832)
  have p0111 :=
    @g_ceqsexv syntaxFormula0101 syntaxFormula0109 t syntaxClass0098
      (by exact freshnessCertificate0829) (by exact freshnessCertificate0833) p0108 p0110
  have p0112 :=
    @g_elin syntaxClass0108
      (syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk))))) syntaxClass0028
  have p0113 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))
  have p0114 :=
    @g_otkelins2k
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
      syntaxClass0083 (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))) p0113 p0079
      p0069
  have p0115 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))
  have p0116 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))
      (syn_cins2k (syn_cins3k (syn_cssetk))) p0115 p0050 p0020
  have p0117 := @g_snex (syn_csn (syn_csn (.cv a)))
  have p0118 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_csn (syn_csn (.cv w)))
      (syn_copk (.cv y) (.cv z)) (syn_cins3k (syn_cssetk)) p0117 p0016 p0006
  have p0119 := @g_snex (.cv a)
  have p0120 := @g_vex y
  have p0121 := @g_vex z
  have p0122 :=
    @g_otkelins3k (syn_csn (.cv a)) (.cv y) (.cv z) (syn_cssetk) p0119 p0120 p0121
  have p0123 := @g_vex a
  have p0124 := @g_elssetk (.cv a) (.cv y) p0123 p0120
  have p0125_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv a)) (.cv y)) (syn_cssetk)) (.objMem a y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
      p0124
  have p0125 :=
    @g_n_3bitri syntaxFormula0110
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (.cv y) (.cv z)))
        (syn_cins3k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv a)) (.cv y)) (syn_cssetk)) (.objMem a y) p0118
      p0122 p0125_e02_recanon
  have p0126 :=
    @g_n_3bitri syntaxFormula0111
      (.classMem (syn_copk
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))))
          syntaxClass0083) (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))
      syntaxFormula0110 (.objMem a y) p0114 p0116 p0125
  have p0127 := @g_elin syntaxClass0108 syntaxClass0009 syntaxClass0027
  have p0128 :=
    @g_otkelins3k
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
      syntaxClass0083 syntaxClass0008 p0113 p0079 p0069
  have p0129 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
  have p0130 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
  have p0131 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))) syntaxClass0007
      p0129 p0130
  have p0132 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0006 p0115
      p0084
  have p0133 := @g_snex (syn_csn (syn_csn (syn_csn (.cv a))))
  have p0134 := @g_snex (syn_csn (syn_csn (syn_csn (.cv b))))
  have p0135 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))) syntaxClass0005 p0133 p0134
  have p0136 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (.cv a))))
      (syn_csn (syn_csn (syn_csn (.cv b)))) syntaxClass0004 p0117 p0086
  have p0137 := @g_snex (syn_csn (.cv a))
  have p0138 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv a))) (syn_csn (syn_csn (.cv b))) syntaxClass0003
      p0137 p0088
  have p0139 :=
    @g_opksnelsik (syn_csn (.cv a)) (syn_csn (.cv b)) syntaxClass0002 p0119 p0091
  have p0140 := @g_opksnelsik (.cv a) (.cv b) syntaxClass0001 p0123 p0094
  have p0141 := @g_ndisjrelk (.cv a) (.cv b) p0123 p0094
  have p0142 :=
    @g_notbii (.classMem (syn_copk (.cv a) (.cv b)) syntaxClass0000)
      (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0)) p0141
  have p0143 := @g_opkex (.cv a) (.cv b)
  have p0144 := @g_elcompl (syn_copk (.cv a) (.cv b)) syntaxClass0000 p0143
  have p0145 := (Nominal.biimpRefl (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0)))
  have p0146 :=
    @g_con2bii (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0))
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0145
  have p0147 :=
    @g_n_3bitr4i (.neg (.classMem (syn_copk (.cv a) (.cv b)) syntaxClass0000))
      (.neg (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0)))
      (.classMem (syn_copk (.cv a) (.cv b)) syntaxClass0001)
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0142 p0144 p0146
  have p0148 :=
    @g_n_3bitri syntaxFormula0112
      (.classMem (syn_copk (syn_csn (.cv a)) (syn_csn (.cv b))) syntaxClass0002)
      (.classMem (syn_copk (.cv a) (.cv b)) syntaxClass0001)
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0139 p0140 p0147
  have p0149 :=
    @g_n_3bitri syntaxFormula0113
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv a))))
          (syn_csn (syn_csn (syn_csn (.cv b))))) syntaxClass0004)
      syntaxFormula0112 (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0136 p0138 p0148
  have p0150 :=
    @g_n_3bitri syntaxFormula0114
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))) syntaxClass0006)
      syntaxFormula0113 (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0132 p0135 p0149
  have p0151 :=
    @g_n_3bitri syntaxFormula0115
      (.classMem (syn_copk
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))))
        syntaxClass0008)
      syntaxFormula0114 (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0128 p0131 p0150
  have p0152 := @g_opkex syntaxClass0098 syntaxClass0093
  have p0153 :=
    @g_elimak t syntaxClass0020 syntaxClass0025 syntaxClass0108
      (by exact freshnessCertificate0255) (by exact freshnessCertificate0264)
      (by exact freshnessCertificate0831) p0152
  have freshnessCertificate0834 : d ∉ ((Class.cv t)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show d ∉ ({ t } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show d ≠ t from (by exact fresh_d_ne_t)))))
  have p0154 := @g_elpw1111c d (.cv t) (by exact freshnessCertificate0834)
  have p0155 :=
    @g_anbi1i syntaxFormula0116 (syn_wex d syntaxFormula0122) syntaxFormula0124 p0154
  have freshnessCertificate0835 : d ∉ ((Class.cv a)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show d ∉ ({ a } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show d ≠ a from (by exact fresh_d_ne_a)))))
  have freshnessCertificate0836 : d ∉ ((syn_csn (.cv a))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0835)
  have freshnessCertificate0837 : d ∉ ((syn_csn (syn_csn (.cv a)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0836)
  have freshnessCertificate0838 : d ∉ ((syn_csn (syn_csn (syn_csn (.cv a))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0837)
  have freshnessCertificate0839 :
    d ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0838)
  have freshnessCertificate0840 :
    d ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0839)
  have freshnessCertificate0841 :
    d ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0840)
  have freshnessCertificate0842 :
    d ∉
      ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0841)
  have freshnessCertificate0843 : d ∉ (syntaxClass0097).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0842)
  have freshnessCertificate0844 : d ∉ (syntaxClass0098).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0843)
  have freshnessCertificate0845 : d ∉ ((Class.cv b)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show d ∉ ({ b } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show d ≠ b from (by exact fresh_d_ne_b)))))
  have freshnessCertificate0846 : d ∉ ((syn_csn (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0845)
  have freshnessCertificate0847 : d ∉ ((syn_csn (syn_csn (.cv b)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0846)
  have freshnessCertificate0848 : d ∉ ((syn_csn (syn_csn (syn_csn (.cv b))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0847)
  have freshnessCertificate0849 :
    d ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0848)
  have freshnessCertificate0850 :
    d ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0849)
  have freshnessCertificate0851 :
    d ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0850)
  have freshnessCertificate0852 :
    d ∉
      ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0851)
  have freshnessCertificate0853 : d ∉ ((Class.cv c)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show d ∉ ({ c } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show d ≠ c from (by exact fresh_d_ne_c)))))
  have freshnessCertificate0854 : d ∉ ((syn_csn (.cv c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0853)
  have freshnessCertificate0855 : d ∉ ((syn_csn (syn_csn (.cv c)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0854)
  have freshnessCertificate0856 : d ∉ ((syn_csn (syn_csn (syn_csn (.cv c))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0855)
  have freshnessCertificate0857 :
    d ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0856)
  have freshnessCertificate0858 :
    d ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0857)
  have freshnessCertificate0859 : d ∉ ((Class.cv w)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show d ∉ ({ w } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show d ≠ w from (by exact fresh_d_ne_w)))))
  have freshnessCertificate0860 : d ∉ ((syn_csn (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0859)
  have freshnessCertificate0861 : d ∉ ((syn_csn (syn_csn (.cv w)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0860)
  have freshnessCertificate0862 : d ∉ ((Class.cv y)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show d ∉ ({ y } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show d ≠ y from (by exact fresh_d_ne_y)))))
  have freshnessCertificate0863 : d ∉ ((Class.cv z)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show d ∉ ({ z } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show d ≠ z from (by exact fresh_d_ne_z)))))
  have freshnessCertificate0864 : d ∉ (((Class.cv y)).fv) ∪ (((Class.cv z)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0862 freshnessCertificate0863))
  have freshnessCertificate0865 : d ∉ ((syn_copk (.cv y) (.cv z))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0864)
  have freshnessCertificate0866 :
    d ∉ (((syn_csn (syn_csn (.cv w)))).fv) ∪ (((syn_copk (.cv y) (.cv z))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0861 freshnessCertificate0865))
  have freshnessCertificate0867 :
    d ∉ ((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0866)
  have freshnessCertificate0868 :
    d ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))).fv) ∪
        (((syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0858 freshnessCertificate0867))
  have freshnessCertificate0869 : d ∉ (syntaxClass0083).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0868)
  have freshnessCertificate0870 :
    d ∉
      (((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))).fv) ∪
        ((syntaxClass0083).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0852 freshnessCertificate0869))
  have freshnessCertificate0871 : d ∉ (syntaxClass0093).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0870)
  have freshnessCertificate0872 : d ∉ ((syntaxClass0098).fv) ∪ ((syntaxClass0093).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0844 freshnessCertificate0871))
  have freshnessCertificate0873 : d ∉ (syntaxClass0108).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0872)
  have freshnessCertificate0874 : d ∉ (((Class.cv t)).fv) ∪ ((syntaxClass0108).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0834 freshnessCertificate0873))
  have freshnessCertificate0875 : d ∉ (syntaxClass0123).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0874)
  have freshnessCertificate0876 : d ∉ ((syn_cssetk)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
      exact (show d ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0877 : d ∉ ((syn_csik (syn_cssetk))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0876)
  have freshnessCertificate0878 : d ∉ ((syn_csik (syn_csik (syn_cssetk)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0877)
  have freshnessCertificate0879 :
    d ∉ ((syn_csik (syn_csik (syn_csik (syn_cssetk))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0878)
  have freshnessCertificate0880 :
    d ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0879)
  have freshnessCertificate0881 :
    d ∉ ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0880)
  have freshnessCertificate0882 : d ∉ (syntaxClass0010).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0881)
  have freshnessCertificate0883 : d ∉ (syntaxClass0011).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0882)
  have freshnessCertificate0884 : d ∉ (syntaxClass0012).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0883)
  have freshnessCertificate0885 :
    d ∉
      ((syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0881)
  have freshnessCertificate0886 : d ∉ (syntaxClass0013).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0885)
  have freshnessCertificate0887 : d ∉ (syntaxClass0014).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0886)
  have freshnessCertificate0888 : d ∉ (syntaxClass0015).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik];
      exact freshnessCertificate0887)
  have freshnessCertificate0889 : d ∉ (syntaxClass0016).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0888)
  have freshnessCertificate0890 : d ∉ (syntaxClass0017).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k];
      exact freshnessCertificate0886)
  have freshnessCertificate0891 : d ∉ (syntaxClass0018).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k];
      exact freshnessCertificate0890)
  have freshnessCertificate0892 : d ∉ ((syntaxClass0016).fv) ∪ ((syntaxClass0018).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0889 freshnessCertificate0891))
  have freshnessCertificate0893 : d ∉ (syntaxClass0019).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0892)
  have freshnessCertificate0894 : d ∉ ((syntaxClass0012).fv) ∪ ((syntaxClass0019).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0884 freshnessCertificate0893))
  have freshnessCertificate0895 : d ∉ (syntaxClass0020).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif];
      exact freshnessCertificate0894)
  have freshnessCertificate0896 : d ∉ ((syntaxClass0123).fv) ∪ ((syntaxClass0020).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0875 freshnessCertificate0895))
  have freshnessCertificate0897 :
    d ∉ ((Wff.classMem syntaxClass0123 syntaxClass0020)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0896)
  have p0156 :=
    @g_n_19_41v syntaxFormula0122 syntaxFormula0124 d (by exact freshnessCertificate0897)
  have p0157 :=
    @g_bitr4i syntaxFormula0125 (syn_wa (syn_wex d syntaxFormula0122) syntaxFormula0124)
      syntaxFormula0127 p0155 p0156
  have p0158 := @g_exbii syntaxFormula0125 syntaxFormula0127 t p0157
  have p0159 := (Nominal.biimpRefl syntaxFormula0128)
  have p0160 := @g_excom syntaxFormula0126 d t
  have p0161 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0125) (syn_wex t syntaxFormula0127)
      syntaxFormula0128 syntaxFormula0130 p0158 p0159 p0160
  have p0162 := @g_snex syntaxClass0120
  have p0163 := @g_opkeq1 (.cv t) syntaxClass0121 syntaxClass0108
  have p0164 :=
    @g_eleq1d syntaxFormula0122 syntaxClass0123 syntaxClass0131 syntaxClass0020 p0163
  have freshnessCertificate0898 : t ∉ ((Class.cv d)).fv :=
    (by
      rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
      exact
        (show t ∉ ({ d } : Finset Var) from
          (by
            simpa only [Finset.mem_singleton] using
              (show t ≠ d from (by exact fresh_t_ne_d)))))
  have freshnessCertificate0899 : t ∉ ((syn_csn (.cv d))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0898)
  have freshnessCertificate0900 : t ∉ ((syn_csn (syn_csn (.cv d)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0899)
  have freshnessCertificate0901 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv d))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0900)
  have freshnessCertificate0902 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0901)
  have freshnessCertificate0903 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0902)
  have freshnessCertificate0904 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0903)
  have freshnessCertificate0905 :
    t ∉
      ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0904)
  have freshnessCertificate0906 : t ∉ (syntaxClass0117).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0905)
  have freshnessCertificate0907 : t ∉ (syntaxClass0118).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0906)
  have freshnessCertificate0908 : t ∉ (syntaxClass0119).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0907)
  have freshnessCertificate0909 : t ∉ (syntaxClass0120).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0908)
  have freshnessCertificate0910 : t ∉ (syntaxClass0121).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0909)
  have freshnessCertificate0911 : t ∉ ((syntaxClass0121).fv) ∪ ((syntaxClass0108).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0910 freshnessCertificate0831))
  have freshnessCertificate0912 : t ∉ (syntaxClass0131).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk];
      exact freshnessCertificate0911)
  have freshnessCertificate0913 : t ∉ ((syntaxClass0131).fv) ∪ ((syntaxClass0020).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0912 freshnessCertificate0255))
  have freshnessCertificate0914 :
    t ∉ ((Wff.classMem syntaxClass0131 syntaxClass0020)).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]; exact freshnessCertificate0913)
  have p0165 :=
    @g_ceqsexv syntaxFormula0124 syntaxFormula0132 t syntaxClass0121
      (by exact freshnessCertificate0910) (by exact freshnessCertificate0914) p0162 p0164
  have p0166 := @g_elsymdif syntaxClass0131 syntaxClass0012 syntaxClass0019
  have p0167 := @g_snex syntaxClass0118
  have p0168 :=
    @g_otkelins2k syntaxClass0119 syntaxClass0098 syntaxClass0093 syntaxClass0011 p0167
      p0108 p0098
  have p0169 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))))
  have p0170 :=
    @g_otkelins2k syntaxClass0117
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
      syntaxClass0083 syntaxClass0010 p0169 p0079 p0069
  have p0171 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))
  have p0172 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z)))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0171 p0050
      p0020
  have p0173 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))
  have p0174 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0173 p0052
  have p0175 := @g_snex (syn_csn (syn_csn (syn_csn (.cv d))))
  have p0176 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))
      (syn_csn (syn_csn (syn_csn (.cv c)))) (syn_csik (syn_csik (syn_csik (syn_cssetk))))
      p0175 p0055
  have p0177 := @g_snex (syn_csn (syn_csn (.cv d)))
  have p0178 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (.cv d)))) (syn_csn (syn_csn (.cv c)))
      (syn_csik (syn_csik (syn_cssetk))) p0177 p0058
  have p0179 := @g_snex (syn_csn (.cv d))
  have p0180 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv d))) (syn_csn (.cv c)) (syn_csik (syn_cssetk))
      p0179 p0061
  have p0181 := @g_snex (.cv d)
  have p0182 := @g_opksnelsik (syn_csn (.cv d)) (.cv c) (syn_cssetk) p0181 p0064
  have p0183 := @g_vex d
  have p0184 := @g_elssetk (.cv d) (.cv c) p0183 p0064
  have p0185_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv d)) (.cv c)) (syn_cssetk)) (.objMem d c)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
      p0184
  have p0185 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv d)))) (syn_csn (syn_csn (.cv c))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv d))) (syn_csn (.cv c)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv d)) (.cv c)) (syn_cssetk)) (.objMem d c) p0180
      p0182 p0185_e02_recanon
  have p0186 :=
    @g_n_3bitri syntaxFormula0133
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))
          (syn_csn (syn_csn (syn_csn (.cv c))))) (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv d)))) (syn_csn (syn_csn (.cv c))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.objMem d c) p0176 p0178 p0185
  have p0187 :=
    @g_n_3bitri syntaxFormula0135
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c)))))))
        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
      syntaxFormula0133 (.objMem d c) p0172 p0174 p0186
  have p0188 :=
    @g_n_3bitri syntaxFormula0136 (.classMem syntaxClass0137 syntaxClass0011)
      syntaxFormula0135 (.objMem d c) p0168 p0170 p0187
  have p0189 :=
    @g_otkelins3k syntaxClass0119 syntaxClass0098 syntaxClass0093 syntaxClass0015 p0167
      p0108 p0098
  have p0190 := @g_snex syntaxClass0117
  have p0191 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))))
  have p0192 := @g_opksnelsik syntaxClass0118 syntaxClass0097 syntaxClass0014 p0190 p0191
  have p0193 :=
    @g_opksnelsik syntaxClass0117
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))))
      syntaxClass0013 p0169 p0113
  have p0194 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))))
  have p0195 :=
    @g_opksnelsik
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))) p0194
      p0129
  have p0196 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0171 p0115
  have p0197 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0173 p0133
  have p0198 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))
      (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_csik (syn_csik (syn_csik (syn_cssetk))))
      p0175 p0117
  have p0199 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (.cv d)))) (syn_csn (syn_csn (.cv a)))
      (syn_csik (syn_csik (syn_cssetk))) p0177 p0137
  have p0200 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv d))) (syn_csn (.cv a)) (syn_csik (syn_cssetk))
      p0179 p0119
  have p0201 := @g_opksnelsik (syn_csn (.cv d)) (.cv a) (syn_cssetk) p0181 p0123
  have p0202 := @g_elssetk (.cv d) (.cv a) p0183 p0123
  have p0203_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv d)) (.cv a)) (syn_cssetk)) (.objMem d a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
      p0202
  have p0203 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv d)))) (syn_csn (syn_csn (.cv a))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv d))) (syn_csn (.cv a)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv d)) (.cv a)) (syn_cssetk)) (.objMem d a) p0200
      p0201 p0203_e02_recanon
  have p0204 :=
    @g_n_3bitri syntaxFormula0138
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))
          (syn_csn (syn_csn (syn_csn (.cv a))))) (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv d)))) (syn_csn (syn_csn (.cv a))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.objMem d a) p0198 p0199 p0203
  have p0205 :=
    @g_n_3bitri syntaxFormula0139
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))
        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
      syntaxFormula0138 (.objMem d a) p0196 p0197 p0204
  have p0206 :=
    @g_n_3bitri syntaxFormula0141
      (.classMem (syn_copk syntaxClass0117
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))))
        syntaxClass0013)
      syntaxFormula0139 (.objMem d a) p0193 p0195 p0205
  have p0207 :=
    @g_n_3bitri syntaxFormula0142
      (.classMem (syn_copk syntaxClass0119 syntaxClass0098) syntaxClass0015)
      syntaxFormula0141 (.objMem d a) p0189 p0192 p0206
  have p0208 :=
    @g_otkelins2k syntaxClass0119 syntaxClass0098 syntaxClass0093 syntaxClass0017 p0167
      p0108 p0098
  have p0209 :=
    @g_otkelins3k syntaxClass0117
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
      syntaxClass0083 syntaxClass0013 p0169 p0079 p0069
  have p0210 :=
    @g_opksnelsik
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))) p0194
      p0130
  have p0211 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0171 p0084
  have p0212 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0173 p0134
  have p0213 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))
      (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_csik (syn_csik (syn_csik (syn_cssetk))))
      p0175 p0086
  have p0214 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (.cv d)))) (syn_csn (syn_csn (.cv b)))
      (syn_csik (syn_csik (syn_cssetk))) p0177 p0088
  have p0215 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv d))) (syn_csn (.cv b)) (syn_csik (syn_cssetk))
      p0179 p0091
  have p0216 := @g_opksnelsik (syn_csn (.cv d)) (.cv b) (syn_cssetk) p0181 p0094
  have p0217 := @g_elssetk (.cv d) (.cv b) p0183 p0094
  have p0218_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv d)) (.cv b)) (syn_cssetk)) (.objMem d b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
      p0217
  have p0218 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv d))) (syn_csn (.cv b)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv d)) (.cv b)) (syn_cssetk)) (.objMem d b) p0216
      p0218_e01_recanon
  have p0219 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))
          (syn_csn (syn_csn (syn_csn (.cv b))))) (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv d)))) (syn_csn (syn_csn (.cv b))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv d))) (syn_csn (.cv b)))
        (syn_csik (syn_cssetk)))
      (.objMem d b) p0214 p0215 p0218
  have p0220 :=
    @g_n_3bitri syntaxFormula0143
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))
          (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
        (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv d)))))
          (syn_csn (syn_csn (syn_csn (.cv b))))) (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
      (.objMem d b) p0212 p0213 p0219
  have p0221 :=
    @g_n_3bitri syntaxFormula0145
      (.classMem (syn_copk
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv d))))))))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))
      syntaxFormula0143 (.objMem d b) p0210 p0211 p0220
  have p0222 :=
    @g_n_3bitri syntaxFormula0146 (.classMem syntaxClass0137 syntaxClass0017)
      syntaxFormula0145 (.objMem d b) p0208 p0209 p0221
  have p0223 :=
    @g_orbi12i syntaxFormula0142 (.objMem d a) syntaxFormula0146 (.objMem d b) p0207 p0222
  have p0224 := @g_elun syntaxClass0131 syntaxClass0016 syntaxClass0018
  have p0225 := @g_elun (.cv d) (.cv a) (.cv b)
  have p0226_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv d) (syn_cun (.cv a) (.cv b)))
        (syn_wo (.objMem d a) (.objMem d b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl, syn_wo]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0225
  have p0226 :=
    @g_n_3bitr4i (syn_wo syntaxFormula0142 syntaxFormula0146)
      (syn_wo (.objMem d a) (.objMem d b)) syntaxFormula0147
      (.classMem (.cv d) (syn_cun (.cv a) (.cv b))) p0223 p0224 p0226_e02_recanon
  have p0227 :=
    @g_bibi12i syntaxFormula0136 (.objMem d c) syntaxFormula0147
      (.classMem (.cv d) (syn_cun (.cv a) (.cv b))) p0188 p0226
  have p0228 :=
    @g_notbii syntaxFormula0148
      (syn_wb (.objMem d c) (.classMem (.cv d) (syn_cun (.cv a) (.cv b)))) p0227
  have p0229 :=
    @g_n_3bitri syntaxFormula0129 syntaxFormula0132 (.neg syntaxFormula0148)
      (.neg (syn_wb (.objMem d c) (.classMem (.cv d) (syn_cun (.cv a) (.cv b))))) p0165
      p0166 p0228
  have p0230 :=
    @g_exbii syntaxFormula0129
      (.neg (syn_wb (.objMem d c) (.classMem (.cv d) (syn_cun (.cv a) (.cv b))))) d p0229
  have p0231 :=
    @g_n_3bitri syntaxFormula0149 syntaxFormula0128 syntaxFormula0130
      (syn_wex d (.neg (syn_wb (.objMem d c) (.classMem (.cv d) (syn_cun (.cv a) (.cv b))))))
      p0153 p0161 p0230
  have p0232 :=
    @g_notbii syntaxFormula0149
      (syn_wex d (.neg (syn_wb (.objMem d c) (.classMem (.cv d) (syn_cun (.cv a) (.cv b))))))
      p0231
  have p0233 := @g_elcompl syntaxClass0108 syntaxClass0026 p0152
  have freshnessCertificate0915 : d ∉ (((Class.cv a)).fv) ∪ (((Class.cv b)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0835 freshnessCertificate0845))
  have freshnessCertificate0916 : d ∉ ((syn_cun (.cv a) (.cv b))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun];
      exact freshnessCertificate0915)
  have p0234 :=
    @g_dfcleq d (.cv c) (syn_cun (.cv a) (.cv b)) (by exact freshnessCertificate0853)
      (by exact freshnessCertificate0916)
  have p0235 :=
    @g_alex (syn_wb (.objMem d c) (.classMem (.cv d) (syn_cun (.cv a) (.cv b)))) d
  have p0236_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv c) (syn_cun (.cv a) (.cv b)))
        (.all d (syn_wb (.objMem d c) (.classMem (.cv d) (syn_cun (.cv a) (.cv b)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl]
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
      p0234
  have p0236 :=
    @g_bitri (.classEq (.cv c) (syn_cun (.cv a) (.cv b)))
      (.all d (syn_wb (.objMem d c) (.classMem (.cv d) (syn_cun (.cv a) (.cv b)))))
      (.neg (syn_wex d
          (.neg (syn_wb (.objMem d c) (.classMem (.cv d) (syn_cun (.cv a) (.cv b)))))))
      p0236_e00_recanon p0235
  have p0237 :=
    @g_n_3bitr4i (.neg syntaxFormula0149)
      (.neg (syn_wex d
          (.neg (syn_wb (.objMem d c) (.classMem (.cv d) (syn_cun (.cv a) (.cv b)))))))
      syntaxFormula0150 (.classEq (.cv c) (syn_cun (.cv a) (.cv b))) p0232 p0233 p0236
  have p0238 :=
    @g_anbi12i syntaxFormula0115 (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
      syntaxFormula0150 (.classEq (.cv c) (syn_cun (.cv a) (.cv b))) p0151 p0237
  have p0239 :=
    @g_bitri syntaxFormula0151 (syn_wa syntaxFormula0115 syntaxFormula0150)
      syntaxFormula0152 p0127 p0238
  have p0240 :=
    @g_anbi12i syntaxFormula0111 (.objMem a y) syntaxFormula0151 syntaxFormula0152 p0126
      p0239
  have p0241 :=
    @g_n_3bitri syntaxFormula0106 syntaxFormula0109
      (syn_wa syntaxFormula0111 syntaxFormula0151)
      (syn_wa (.objMem a y) syntaxFormula0152) p0111 p0112 p0240
  have p0242 :=
    @g_exbii syntaxFormula0106 (syn_wa (.objMem a y) syntaxFormula0152) a p0241
  have p0243 :=
    @g_n_3bitri syntaxFormula0153 syntaxFormula0105 syntaxFormula0107
      (syn_wex a (syn_wa (.objMem a y) syntaxFormula0152)) p0099 p0107 p0242
  have p0244 := (Nominal.biimpRefl syntaxFormula0154)
  have p0245_e01_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0154 (syn_wex a (syn_wa (.objMem a y) syntaxFormula0152))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wex, syn_wa]
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
      p0244
  have p0245 :=
    @g_bitr4i syntaxFormula0153 (syn_wex a (syn_wa (.objMem a y) syntaxFormula0152))
      syntaxFormula0154 p0243 p0245_e01_recanon
  have p0246 :=
    @g_anbi12i syntaxFormula0095 (.objMem b w) syntaxFormula0153 syntaxFormula0154 p0097
      p0245
  have p0247 :=
    @g_n_3bitri syntaxFormula0091 syntaxFormula0094
      (syn_wa syntaxFormula0095 syntaxFormula0153)
      (syn_wa (.objMem b w) syntaxFormula0154) p0082 p0083 p0246
  have p0248 :=
    @g_exbii syntaxFormula0091 (syn_wa (.objMem b w) syntaxFormula0154) b p0247
  have p0249 :=
    @g_n_3bitri syntaxFormula0155 syntaxFormula0090 syntaxFormula0092
      (syn_wex b (syn_wa (.objMem b w) syntaxFormula0154)) p0070 p0078 p0248
  have p0250 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv c))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (syn_csn (syn_csn (.cv w))) (syn_copk (.cv y) (.cv z))) syntaxClass0032
      p0050 p0030 p0020
  have p0251 :=
    @g_rexcom syntaxFormula0152 a b (.cv y) (.cv w) (by exact freshnessCertificate0644)
      (by exact freshnessCertificate0746) (show a ≠ b from (by exact fresh_a_ne_b))
  have p0252 := (Nominal.biimpRefl syntaxFormula0156)
  have p0253_e01_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0156 (syn_wex b (syn_wa (.objMem b w) syntaxFormula0154))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wex, syn_wa]
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
      p0252
  have p0253 :=
    @g_bitri syntaxFormula0158 syntaxFormula0156
      (syn_wex b (syn_wa (.objMem b w) syntaxFormula0154)) p0251 p0253_e01_recanon
  have p0254 :=
    @g_n_3bitr4i syntaxFormula0155 (syn_wex b (syn_wa (.objMem b w) syntaxFormula0154))
      syntaxFormula0159 syntaxFormula0158 p0249 p0250 p0253
  have p0255 :=
    @g_bibi12i syntaxFormula0082 (.objMem c x) syntaxFormula0159 syntaxFormula0158 p0068
      p0254
  have p0256 := @g_notbii syntaxFormula0160 (syn_wb (.objMem c x) syntaxFormula0158) p0255
  have p0257 :=
    @g_n_3bitri syntaxFormula0078 syntaxFormula0081 (.neg syntaxFormula0160)
      (.neg (syn_wb (.objMem c x) syntaxFormula0158)) p0048 p0049 p0256
  have p0258 :=
    @g_exbii syntaxFormula0078 (.neg (syn_wb (.objMem c x) syntaxFormula0158)) c p0257
  have p0259 :=
    @g_n_3bitri syntaxFormula0161 syntaxFormula0077 syntaxFormula0079
      (syn_wex c (.neg (syn_wb (.objMem c x) syntaxFormula0158))) p0036 p0044 p0258
  have p0260 :=
    @g_notbii syntaxFormula0161
      (syn_wex c (.neg (syn_wb (.objMem c x) syntaxFormula0158))) p0259
  have p0261 := @g_elcompl syntaxClass0068 syntaxClass0035 p0035
  have p0262 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addc c a b (.cv y)
      (.cv w) (by exact freshnessCertificate0539) (by exact freshnessCertificate0749)
      (by exact freshnessCertificate0644) (by exact freshnessCertificate0536)
      (by exact freshnessCertificate0746) (by exact freshnessCertificate0641)
      (show c ≠ a from (by exact fresh_c_ne_a)) (show c ≠ b from (by exact fresh_c_ne_b))
      (show a ≠ b from (by exact fresh_a_ne_b))
  have p0263 := @g_eqeq2i (syn_cplc (.cv y) (.cv w)) syntaxClass0162 (.cv x) p0262
  have p0264 := @g_eqabb syntaxFormula0158 c (.cv x) (by exact freshnessCertificate0531)
  have p0265 := @g_alex (syn_wb (.objMem c x) syntaxFormula0158) c
  have p0266_e01_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0163 (.all c (syn_wb (.objMem c x) syntaxFormula0158))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb]
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
      p0264
  have p0266 :=
    @g_n_3bitri (.classEq (.cv x) (syn_cplc (.cv y) (.cv w))) syntaxFormula0163
      (.all c (syn_wb (.objMem c x) syntaxFormula0158))
      (.neg (syn_wex c (.neg (syn_wb (.objMem c x) syntaxFormula0158)))) p0263
      p0266_e01_recanon p0265
  have p0267 :=
    @g_n_3bitr4i (.neg syntaxFormula0161)
      (.neg (syn_wex c (.neg (syn_wb (.objMem c x) syntaxFormula0158)))) syntaxFormula0164
      (.classEq (.cv x) (syn_cplc (.cv y) (.cv w))) p0260 p0261 p0266
  have p0268 :=
    @g_otkelins2k (syn_csn (syn_csn (.cv x))) (syn_csn (syn_csn (.cv w)))
      (syn_copk (.cv y) (.cv z)) syntaxClass0044 p0056 p0016 p0006
  have p0269 := @g_otkelins2k (.cv x) (.cv y) (.cv z) syntaxClass0043 p0062 p0120 p0121
  have p0270 := @g_opkelimagek (.cv x) (.cv z) syntaxClass0042 p0062 p0121
  have p0271 := @g_dfaddc2 (.cv x) (syn_c1c)
  have p0272 := @g_eqeq2i (syn_cplc (.cv x) (syn_c1c)) syntaxClass0165 (.cv z) p0271
  have p0273 :=
    @g_bitr4i syntaxFormula0166 (.classEq (.cv z) syntaxClass0165)
      (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) p0270 p0272
  have p0274 :=
    @g_n_3bitri syntaxFormula0167
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv z)))
        syntaxClass0044)
      syntaxFormula0166 (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) p0268 p0269 p0273
  have p0275 :=
    @g_anbi12i syntaxFormula0164 (.classEq (.cv x) (syn_cplc (.cv y) (.cv w)))
      syntaxFormula0167 (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c))) p0267 p0274
  have p0276 :=
    @g_n_3bitri syntaxFormula0066 syntaxFormula0069
      (syn_wa syntaxFormula0164 syntaxFormula0167) syntaxFormula0168 p0033 p0034 p0275
  have p0277 := @g_exbii syntaxFormula0066 syntaxFormula0168 x p0276
  have p0278 :=
    @g_n_3bitri syntaxFormula0059 syntaxFormula0065 syntaxFormula0067
      (syn_wex x syntaxFormula0168) p0021 p0029 p0277
  have p0279 := @g_addcex (.cv y) (.cv w) p0120 p0092
  have p0280 := @g_addceq1 (.cv x) (syn_cplc (.cv y) (.cv w)) (syn_c1c)
  have p0281 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cplc (.cv y) (.cv w))) (syn_cplc (.cv x) (syn_c1c))
      (syn_cplc (syn_cplc (.cv y) (.cv w)) (syn_c1c)) (.cv z) p0280
  have freshnessCertificate0917 : x ∉ (((Class.cv y)).fv) ∪ (((Class.cv w)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0422 freshnessCertificate0419))
  have freshnessCertificate0918 : x ∉ ((syn_cplc (.cv y) (.cv w))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0917)
  have freshnessCertificate0919 :
    x ∉ (((syn_cplc (.cv y) (.cv w))).fv) ∪ (((syn_c1c)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0918 freshnessCertificate0445))
  have freshnessCertificate0920 :
    x ∉ ((syn_cplc (syn_cplc (.cv y) (.cv w)) (syn_c1c))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc];
      exact freshnessCertificate0919)
  have freshnessCertificate0921 :
    x ∉ (((Class.cv z)).fv) ∪ (((syn_cplc (syn_cplc (.cv y) (.cv w)) (syn_c1c))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0423 freshnessCertificate0920))
  have freshnessCertificate0922 :
    x ∉ ((Wff.classEq (.cv z) (syn_cplc (syn_cplc (.cv y) (.cv w)) (syn_c1c)))).fv :=
    (by rw [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]; exact freshnessCertificate0921)
  have p0282 :=
    @g_ceqsexv (.classEq (.cv z) (syn_cplc (.cv x) (syn_c1c)))
      (.classEq (.cv z) (syn_cplc (syn_cplc (.cv y) (.cv w)) (syn_c1c))) x
      (syn_cplc (.cv y) (.cv w)) (by exact freshnessCertificate0918)
      (by exact freshnessCertificate0922) p0279 p0281
  have p0283 :=
    @g_n_3bitri syntaxFormula0057 syntaxFormula0059 (syn_wex x syntaxFormula0168)
      (.classEq (.cv z) (syn_cplc (syn_cplc (.cv y) (.cv w)) (syn_c1c))) p0019 p0278 p0282
  have p0284 :=
    @g_rexbii syntaxFormula0057
      (.classEq (.cv z) (syn_cplc (syn_cplc (.cv y) (.cv w)) (syn_c1c))) w (syn_cnnc)
      p0283
  have p0285 :=
    @g_n_3bitri syntaxFormula0169 syntaxFormula0056 syntaxFormula0058 syntaxFormula0170
      p0007 p0015 p0284
  have p0286 := @g_opkelxpk (.cv y) (.cv z) (syn_csn (syn_c0)) (syn_cvv) p0120 p0121
  have p0287 :=
    @g_mpbiran2
      (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))
      (.classMem (.cv y) (syn_csn (syn_c0))) (.classMem (.cv z) (syn_cvv)) p0121 p0286
  have p0288 := @g_elsnc (.cv y) (syn_c0) p0120
  have p0289 :=
    @g_bitri
      (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))
      (.classMem (.cv y) (syn_csn (syn_c0))) (.classEq (.cv y) (syn_c0)) p0287 p0288
  have p0290 :=
    @g_notbii
      (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))
      (.classEq (.cv y) (syn_c0)) p0289
  have p0291 :=
    @g_anbi12i syntaxFormula0169 syntaxFormula0170
      (.neg (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv))))
      (.neg (.classEq (.cv y) (syn_c0))) p0285 p0290
  have p0292 :=
    @g_eldif (syn_copk (.cv y) (.cv z)) syntaxClass0048
      (syn_cxpk (syn_csn (syn_c0)) (syn_cvv))
  have p0293 := @g_ancom (syn_wne (.cv y) (syn_c0)) syntaxFormula0170
  have p0294 := (Nominal.biimpRefl (syn_wne (.cv y) (syn_c0)))
  have p0295 :=
    @g_anbi2i (syn_wne (.cv y) (syn_c0)) (.neg (.classEq (.cv y) (syn_c0)))
      syntaxFormula0170 p0294
  have p0296 :=
    @g_bitri syntaxFormula0171 (syn_wa syntaxFormula0170 (syn_wne (.cv y) (syn_c0)))
      (syn_wa syntaxFormula0170 (.neg (.classEq (.cv y) (syn_c0)))) p0293 p0295
  have p0297 :=
    @g_n_3bitr4i
      (syn_wa syntaxFormula0169 (.neg
          (.classMem (syn_copk (.cv y) (.cv z)) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))))
      (syn_wa syntaxFormula0170 (.neg (.classEq (.cv y) (syn_c0)))) syntaxFormula0172
      syntaxFormula0171 p0291 p0292 p0296
  have p0298 :=
    @g_syl6bb (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) syntaxFormula0050
      syntaxFormula0172 syntaxFormula0171 p0005 p0297
  have p0299 :=
    @g_pm5_32i (.classEq (.cv x) (syn_copk (.cv y) (.cv z))) syntaxFormula0050
      syntaxFormula0171 p0298
  have p0300 := @g_n_2exbii syntaxFormula0173 syntaxFormula0174 y z p0299
  have p0301 :=
    @g_bitr3i syntaxFormula0175 (syn_wex y (syn_wex z syntaxFormula0173))
      syntaxFormula0177 p0004 p0300
  have p0302 :=
    @g_n_3bitri (.classMem (.cv x) syntaxClass0178)
      (syn_wa (.classMem (.cv x) (syn_cxpk (syn_cvv) (syn_cvv))) syntaxFormula0050)
      syntaxFormula0175 syntaxFormula0177 p0001 p0003 p0301
  have freshnessCertificate0923 : x ∉ ((syn_cvv)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0924 : x ∉ (((syn_cvv)).fv) ∪ (((syn_cvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0923 freshnessCertificate0923))
  have freshnessCertificate0925 : x ∉ ((syn_cxpk (syn_cvv) (syn_cvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0924)
  have freshnessCertificate0926 :
    x ∉ ((syntaxClass0046).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0518 freshnessCertificate0474))
  have freshnessCertificate0927 : x ∉ (syntaxClass0047).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0926)
  have freshnessCertificate0928 : x ∉ ((syn_cnnc)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0929 : x ∉ ((syn_cpw1 (syn_cnnc))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0928)
  have freshnessCertificate0930 : x ∉ ((syn_cpw1 (syn_cpw1 (syn_cnnc)))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1];
      exact freshnessCertificate0929)
  have freshnessCertificate0931 :
    x ∉ ((syntaxClass0047).fv) ∪ (((syn_cpw1 (syn_cpw1 (syn_cnnc)))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0927 freshnessCertificate0930))
  have freshnessCertificate0932 : x ∉ (syntaxClass0048).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak];
      exact freshnessCertificate0931)
  have freshnessCertificate0933 : x ∉ ((syn_c0)).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
      exact (show x ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))
  have freshnessCertificate0934 : x ∉ ((syn_csn (syn_c0))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn];
      exact freshnessCertificate0933)
  have freshnessCertificate0935 : x ∉ (((syn_csn (syn_c0))).fv) ∪ (((syn_cvv)).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0934 freshnessCertificate0923))
  have freshnessCertificate0936 : x ∉ ((syn_cxpk (syn_csn (syn_c0)) (syn_cvv))).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk];
      exact freshnessCertificate0935)
  have freshnessCertificate0937 :
    x ∉ ((syntaxClass0048).fv) ∪ (((syn_cxpk (syn_csn (syn_c0)) (syn_cvv))).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0932 freshnessCertificate0936))
  have freshnessCertificate0938 : x ∉ (syntaxClass0049).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif];
      exact freshnessCertificate0937)
  have freshnessCertificate0939 :
    x ∉ (((syn_cxpk (syn_cvv) (syn_cvv))).fv) ∪ ((syntaxClass0049).fv) :=
    (by
      with_reducible
        exact
          (not_mem_support_union _ _ _ freshnessCertificate0925 freshnessCertificate0938))
  have freshnessCertificate0940 : x ∉ (syntaxClass0178).fv :=
    (by
      rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin];
      exact freshnessCertificate0939)
  have p0303 :=
    @g_eqabi syntaxFormula0177 x syntaxClass0178 (by exact freshnessCertificate0940) p0302
  have p0304 :=
    @g_eqtr4i (syn_cltfin) (.cab x syntaxFormula0177) syntaxClass0178 p0000 p0303
  have p0305 := @g_vvex
  have p0307 := @g_xpkex (syn_cvv) (syn_cvv) p0305 p0305
  have p0308 := @g_ssetkex
  have p0309 := @g_sikex (syn_cssetk) p0308
  have p0310 := @g_sikex (syn_csik (syn_cssetk)) p0309
  have p0311 := @g_sikex (syn_csik (syn_csik (syn_cssetk))) p0310
  have p0312 := @g_sikex (syn_csik (syn_csik (syn_csik (syn_cssetk)))) p0311
  have p0313 := @g_ins3kex (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0312
  have p0314 := @g_ins3kex (syn_csik (syn_csik (syn_cssetk))) p0310
  have p0315 := @g_ins2kex (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) p0314
  have p0317 := @g_ins3kex (syn_cssetk) p0308
  have p0318 := @g_ins2kex (syn_cins3k (syn_cssetk)) p0317
  have p0319 := @g_ins2kex (syn_cins2k (syn_cins3k (syn_cssetk))) p0318
  have p0320 := @g_ins2kex (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))) p0319
  have p0322 := @g_ins2kex (syn_cssetk) p0308
  have p0323 := @g_inex (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)) p0317 p0322
  have p0324 := @g_n_1cex
  have p0325 := @g_pw1ex (syn_c1c) p0324
  have p0326 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0325
  have p0327 :=
    @g_imakex (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0323 p0326
  have p0328 := @g_complex syntaxClass0000 p0327
  have p0329 := @g_sikex syntaxClass0001 p0328
  have p0330 := @g_sikex syntaxClass0002 p0329
  have p0331 := @g_sikex syntaxClass0003 p0330
  have p0332 := @g_sikex syntaxClass0004 p0331
  have p0333 := @g_sikex syntaxClass0005 p0332
  have p0334 := @g_sikex syntaxClass0006 p0333
  have p0335 := @g_sikex syntaxClass0007 p0334
  have p0336 := @g_ins3kex syntaxClass0008 p0335
  have p0337 := @g_sikex (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0312
  have p0338 :=
    @g_ins3kex (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0337
  have p0339 := @g_ins2kex syntaxClass0010 p0338
  have p0340 := @g_ins2kex syntaxClass0011 p0339
  have p0341 :=
    @g_sikex (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0337
  have p0342 :=
    @g_sikex
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))) p0341
  have p0343 := @g_sikex syntaxClass0013 p0342
  have p0344 := @g_sikex syntaxClass0014 p0343
  have p0345 := @g_ins3kex syntaxClass0015 p0344
  have p0346 := @g_ins3kex syntaxClass0013 p0342
  have p0347 := @g_ins2kex syntaxClass0017 p0346
  have p0348 := @g_unex syntaxClass0016 syntaxClass0018 p0345 p0347
  have p0349 := @g_symdifex syntaxClass0012 syntaxClass0019 p0340 p0348
  have p0350 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0326
  have p0351 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0350
  have p0352 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0351
  have p0353 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0352
  have p0354 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0353
  have p0355 := @g_pw1ex syntaxClass0021 p0354
  have p0356 := @g_pw1ex syntaxClass0022 p0355
  have p0357 := @g_pw1ex syntaxClass0023 p0356
  have p0358 := @g_pw1ex syntaxClass0024 p0357
  have p0359 := @g_imakex syntaxClass0020 syntaxClass0025 p0349 p0358
  have p0360 := @g_complex syntaxClass0026 p0359
  have p0361 := @g_inex syntaxClass0009 syntaxClass0027 p0336 p0360
  have p0362 :=
    @g_inex (syn_cins2k (syn_cins2k (syn_cins2k (syn_cins3k (syn_cssetk)))))
      syntaxClass0028 p0320 p0361
  have p0363 := @g_imakex syntaxClass0029 syntaxClass0022 p0362 p0355
  have p0364 :=
    @g_inex (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))) syntaxClass0030
      p0315 p0363
  have p0365 :=
    @g_imakex syntaxClass0031
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0364
      p0353
  have p0366 := @g_ins2kex syntaxClass0032 p0365
  have p0367 :=
    @g_symdifex (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
      syntaxClass0033 p0313 p0366
  have p0368 :=
    @g_imakex syntaxClass0034
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) p0367
      p0353
  have p0369 := @g_complex syntaxClass0035 p0368
  have p0370 := @g_addcexlem
  have p0371 := @g_imakex syntaxClass0041 (syn_cpw1 (syn_cpw1 (syn_c1c))) p0370 p0326
  have p0372 := @g_imagekex syntaxClass0042 p0371
  have p0373 := @g_ins2kex syntaxClass0043 p0372
  have p0374 := @g_ins2kex syntaxClass0044 p0373
  have p0375 := @g_inex syntaxClass0036 syntaxClass0045 p0369 p0374
  have p0376 :=
    @g_imakex syntaxClass0046 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0375 p0350
  have p0377 := @g_nncex
  have p0378 := @g_pw1ex (syn_cnnc) p0377
  have p0379 := @g_pw1ex (syn_cpw1 (syn_cnnc)) p0378
  have p0380 := @g_imakex syntaxClass0047 (syn_cpw1 (syn_cpw1 (syn_cnnc))) p0376 p0379
  have p0381 := @g_snex (syn_c0)
  have p0383 := @g_xpkex (syn_csn (syn_c0)) (syn_cvv) p0381 p0305
  have p0384 :=
    @g_difex syntaxClass0048 (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)) p0380 p0383
  have p0385 := @g_inex (syn_cxpk (syn_cvv) (syn_cvv)) syntaxClass0049 p0307 p0384
  have p0386 := @g_eqeltri (syn_cltfin) syntaxClass0178 (syn_cvv) p0304 p0385
  exact p0386


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart043`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ltfintrilem1 (m : Var) (n : Var) (dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.classMem (.cab m (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0))
              (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
                (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := ({ m } : Finset Var) ∪ ({ n } : Finset Var)
  let t : Var := freshVar proofSupport 0
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_m : t ≠ m := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_t_ne_n : t ≠ n := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have p0000 :=
    @g_unab (.neg (.classMem (.cv n) (syn_cnnc)))
      (syn_wo (.classEq (.cv m) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
      m
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn m (syn_c0)
      (by
        exact
          (show m ∉ ((syn_c0)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0];
              exact (show m ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
  have p0002 :=
    @g_elun (.cv m) (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))
      (syn_csn (.cv n))
  have p0003 := @g_vex m
  have freeVariableCertificate0 : t ∉ ((syn_ccnvk (syn_cltfin))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate1 : t ∉ ((syn_csn (.cv n))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_n,
      not_false_eq_true]
  have freeVariableCertificate2 : t ∉ ((Class.cv m)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_m, not_false_eq_true]
  have p0004 :=
    @g_elimak t (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)) (.cv m)
      freeVariableCertificate0 freeVariableCertificate1 freeVariableCertificate2 p0003
  have p0005 := @g_vex n
  have p0006 := @g_opkeq1 (.cv t) (.cv n) (.cv m)
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq t n) (.classEq (syn_copk (.cv t) (.cv m)) (syn_copk (.cv n) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @g_eleq1d (.objEq t n) (syn_copk (.cv t) (.cv m)) (syn_copk (.cv n) (.cv m))
      (syn_ccnvk (syn_cltfin)) p0007_e00_recanon
  have p0008_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv t) (.cv n))
        (syn_wb (.classMem (syn_copk (.cv t) (.cv m)) (syn_ccnvk (syn_cltfin)))
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_ccnvk (syn_cltfin))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_ccnvk syn_wex syn_cltfin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have freeVariableCertificate3 : t ∉ ((Class.cv n)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_n, not_false_eq_true]
  have freeVariableCertificate4 :
    t ∉ ((Wff.classMem (syn_copk (.cv n) (.cv m)) (syn_ccnvk (syn_cltfin)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_n, fresh_t_ne_m, or_false,
      not_false_eq_true]
  have p0008 :=
    @g_rexsn (.classMem (syn_copk (.cv t) (.cv m)) (syn_ccnvk (syn_cltfin)))
      (.classMem (syn_copk (.cv n) (.cv m)) (syn_ccnvk (syn_cltfin))) t (.cv n)
      freeVariableCertificate3 freeVariableCertificate4 p0005 p0008_e01_recanon
  have p0009 :=
    @g_bitri (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))))
      (syn_wrex t (syn_csn (.cv n))
        (.classMem (syn_copk (.cv t) (.cv m)) (syn_ccnvk (syn_cltfin))))
      (.classMem (syn_copk (.cv n) (.cv m)) (syn_ccnvk (syn_cltfin))) p0004 p0008
  have p0010 := @g_opkelcnvk (.cv n) (.cv m) (syn_cltfin) p0005 p0003
  have p0011 :=
    @g_bitri (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))))
      (.classMem (syn_copk (.cv n) (.cv m)) (syn_ccnvk (syn_cltfin)))
      (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) p0009 p0010
  have p0012 := @g_elsnc (.cv m) (.cv n) p0003
  have p0013_e01_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv m) (syn_csn (.cv n))) (.objEq m n)) :=
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
      p0012
  have p0013 :=
    @g_orbi12i (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))))
      (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin))
      (.classMem (.cv m) (syn_csn (.cv n))) (.objEq m n) p0011 p0013_e01_recanon
  have p0014 :=
    @g_bitri
      (.classMem (.cv m) (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))
          (syn_csn (.cv n))))
      (syn_wo (.classMem (.cv m) (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))))
        (.classMem (.cv m) (syn_csn (.cv n))))
      (syn_wo (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)) p0002
      p0013
  have p0015 :=
    @g_elimak t (syn_cltfin) (syn_csn (.cv n)) (.cv m)
      (by
        exact
          (show t ∉ ((syn_cltfin)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate1 freeVariableCertificate2 p0003
  have p0016_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq t n) (.classEq (syn_copk (.cv t) (.cv m)) (syn_copk (.cv n) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0016 :=
    @g_eleq1d (.objEq t n) (syn_copk (.cv t) (.cv m)) (syn_copk (.cv n) (.cv m))
      (syn_cltfin) p0016_e00_recanon
  have p0017_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv t) (.cv n))
        (syn_wb (.classMem (syn_copk (.cv t) (.cv m)) (syn_cltfin))
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cltfin syn_wex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have freeVariableCertificate5 :
    t ∉ ((Wff.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_n, fresh_t_ne_m, or_false,
      not_false_eq_true]
  have p0017 :=
    @g_rexsn (.classMem (syn_copk (.cv t) (.cv m)) (syn_cltfin))
      (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) t (.cv n)
      freeVariableCertificate3 freeVariableCertificate5 p0005 p0017_e01_recanon
  have p0018 :=
    @g_bitri (.classMem (.cv m) (syn_cimak (syn_cltfin) (syn_csn (.cv n))))
      (syn_wrex t (syn_csn (.cv n)) (.classMem (syn_copk (.cv t) (.cv m)) (syn_cltfin)))
      (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) p0015 p0017
  have p0019 :=
    @g_orbi12i
      (.classMem (.cv m) (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))
          (syn_csn (.cv n))))
      (syn_wo (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n))
      (.classMem (.cv m) (syn_cimak (syn_cltfin) (syn_csn (.cv n))))
      (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)) p0014 p0018
  have p0020 :=
    @g_elun (.cv m)
      (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))
      (syn_cimak (syn_cltfin) (syn_csn (.cv n)))
  have p0021 :=
    (Nominal.biimpRefl (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
        (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
  have p0022 :=
    @g_n_3bitr4i
      (syn_wo (.classMem (.cv m) (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))
            (syn_csn (.cv n)))) (.classMem (.cv m) (syn_cimak (syn_cltfin) (syn_csn (.cv n)))))
      (syn_wo (syn_wo (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n))
        (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))
      (.classMem (.cv m) (syn_cun
          (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))
          (syn_cimak (syn_cltfin) (syn_csn (.cv n)))))
      (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
        (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))
      p0019 p0020 p0021
  have freeVariableCertificate6 :
    m ∉
      ((syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))
            (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cltfin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, dv_m_n, or_false, not_false_eq_true]
  have p0023 :=
    @g_eqabi
      (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
        (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))
      m
      (syn_cun
        (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))
        (syn_cimak (syn_cltfin) (syn_csn (.cv n))))
      freeVariableCertificate6 p0022
  have p0024 :=
    @g_uneq12i (syn_csn (syn_c0)) (.cab m (.classEq (.cv m) (syn_c0)))
      (syn_cun
        (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))
        (syn_cimak (syn_cltfin) (syn_csn (.cv n))))
      (.cab m (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
      p0001 p0023
  have p0025 :=
    @g_unab (.classEq (.cv m) (syn_c0))
      (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
        (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))
      m
  have p0026 :=
    @g_eqtri
      (syn_cun (syn_csn (syn_c0)) (syn_cun
          (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))
          (syn_cimak (syn_cltfin) (syn_csn (.cv n)))))
      (syn_cun (.cab m (.classEq (.cv m) (syn_c0))) (.cab m
          (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
            (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))
      (.cab m (syn_wo (.classEq (.cv m) (syn_c0))
          (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
            (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))
      p0024 p0025
  have p0027 :=
    @g_uneq2i
      (syn_cun (syn_csn (syn_c0)) (syn_cun
          (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))
          (syn_cimak (syn_cltfin) (syn_csn (.cv n)))))
      (.cab m (syn_wo (.classEq (.cv m) (syn_c0))
          (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
            (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))
      (.cab m (.neg (.classMem (.cv n) (syn_cnnc)))) p0026
  have p0028 :=
    @g_imor (.classMem (.cv n) (syn_cnnc))
      (.imp (syn_wne (.cv m) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
  have p0029 := (Nominal.biimpRefl (syn_wne (.cv m) (syn_c0)))
  have p0030 :=
    @g_imbi1i (syn_wne (.cv m) (syn_c0)) (.neg (.classEq (.cv m) (syn_c0)))
      (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
        (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))
      p0029
  have p0031 :=
    (Nominal.biimpRefl (syn_wo (.classEq (.cv m) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))
  have p0032 :=
    @g_bitr4i
      (.imp (syn_wne (.cv m) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
      (.imp (.neg (.classEq (.cv m) (syn_c0)))
        (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
      (syn_wo (.classEq (.cv m) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
      p0030 p0031
  have p0033 :=
    @g_orbi2i
      (.imp (syn_wne (.cv m) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
      (syn_wo (.classEq (.cv m) (syn_c0))
        (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
          (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))
      (.neg (.classMem (.cv n) (syn_cnnc))) p0032
  have p0034 :=
    @g_bitri
      (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0))
          (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
            (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))
      (syn_wo (.neg (.classMem (.cv n) (syn_cnnc))) (.imp (syn_wne (.cv m) (syn_c0))
          (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
            (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))
      (syn_wo (.neg (.classMem (.cv n) (syn_cnnc))) (syn_wo (.classEq (.cv m) (syn_c0))
          (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
            (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))
      p0028 p0033
  have p0035 :=
    @g_abbii
      (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0))
          (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
            (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))
      (syn_wo (.neg (.classMem (.cv n) (syn_cnnc))) (syn_wo (.classEq (.cv m) (syn_c0))
          (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
            (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin)))))
      m p0034
  have p0036 :=
    @g_n_3eqtr4i
      (syn_cun (.cab m (.neg (.classMem (.cv n) (syn_cnnc)))) (.cab m
          (syn_wo (.classEq (.cv m) (syn_c0))
            (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
              (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))))
      (.cab m (syn_wo (.neg (.classMem (.cv n) (syn_cnnc))) (syn_wo (.classEq (.cv m) (syn_c0))
            (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
              (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))))
      (syn_cun (.cab m (.neg (.classMem (.cv n) (syn_cnnc)))) (syn_cun (syn_csn (syn_c0))
          (syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))
              (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n))))))
      (.cab m (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0))
            (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
              (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))))
      p0000 p0027 p0035
  have freeVariableCertificate7 : m ∉ ((Wff.neg (.classMem (.cv n) (syn_cnnc)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, dv_m_n, or_false, not_false_eq_true]
  have p0037 := @g_abexv (.neg (.classMem (.cv n) (syn_cnnc))) m freeVariableCertificate7
  have p0038 := @g_snex (syn_c0)
  have p0039 := @g_ltfinex
  have p0040 := @g_cnvkex (syn_cltfin) p0039
  have p0041 := @g_snex (.cv n)
  have p0042 := @g_imakex (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)) p0040 p0041
  have p0043 :=
    @g_unex (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)) p0042
      p0041
  have p0045 := @g_imakex (syn_cltfin) (syn_csn (.cv n)) p0039 p0041
  have p0046 :=
    @g_unex
      (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))
      (syn_cimak (syn_cltfin) (syn_csn (.cv n))) p0043 p0045
  have p0047 :=
    @g_unex (syn_csn (syn_c0))
      (syn_cun
        (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))
        (syn_cimak (syn_cltfin) (syn_csn (.cv n))))
      p0038 p0046
  have p0048 :=
    @g_unex (.cab m (.neg (.classMem (.cv n) (syn_cnnc))))
      (syn_cun (syn_csn (syn_c0)) (syn_cun
          (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n))) (syn_csn (.cv n)))
          (syn_cimak (syn_cltfin) (syn_csn (.cv n)))))
      p0037 p0047
  have p0049 :=
    @g_eqeltrri
      (syn_cun (.cab m (.neg (.classMem (.cv n) (syn_cnnc)))) (syn_cun (syn_csn (syn_c0))
          (syn_cun (syn_cun (syn_cimak (syn_ccnvk (syn_cltfin)) (syn_csn (.cv n)))
              (syn_csn (.cv n))) (syn_cimak (syn_cltfin) (syn_csn (.cv n))))))
      (.cab m (.imp (.classMem (.cv n) (syn_cnnc)) (.imp (syn_wne (.cv m) (syn_c0))
            (syn_w3o (.classMem (syn_copk (.cv m) (.cv n)) (syn_cltfin)) (.objEq m n)
              (.classMem (syn_copk (.cv n) (.cv m)) (syn_cltfin))))))
      (syn_cvv) p0036 p0048
  exact p0049


end NFChoice.DirectNominalPrf.WPPReplay

end
