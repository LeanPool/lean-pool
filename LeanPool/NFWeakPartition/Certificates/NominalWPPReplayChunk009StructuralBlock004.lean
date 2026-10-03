/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk009StructuralBlock003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk009StructuralPart020`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_pw1eqadj (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y)
    (hyp_pw1eqadj_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_pw1eqadj_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_wex x (syn_wex y
            (syn_w3a (.classEq C (syn_cun (.cv x) (syn_csn (.cv y))))
              (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y))))))) :=
  by
  have p0000 := @g_unieq (syn_cpw1 C) (syn_cun A (syn_csn B))
  have p0001 := @g_unipw1 C
  have p0002 := @g_uniun A (syn_csn B)
  have p0003 :=
    @g_n_3eqtr3g (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_cuni (syn_cpw1 C))
      (syn_cuni (syn_cun A (syn_csn B))) C (syn_cun (syn_cuni A) (syn_cuni (syn_csn B)))
      p0000 p0001 p0002
  have p0004 := @g_unisn B hyp_pw1eqadj_2
  have p0005 := @g_pw1ss1c C
  have p0006 := @g_ssun2 (syn_csn B) A
  have p0007 := @g_snid B hyp_pw1eqadj_2
  have p0008 := @g_sselii (syn_csn B) (syn_cun A (syn_csn B)) B p0006 p0007
  have p0009 := @g_eleq2 (syn_cpw1 C) (syn_cun A (syn_csn B)) B
  have p0010 :=
    @g_mpbiri (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (.classMem B (syn_cpw1 C))
      (.classMem B (syn_cun A (syn_csn B))) p0008 p0009
  have p0011 :=
    @g_sseldi (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_cpw1 C) (syn_c1c) B
      p0005 p0010
  have p0012 := @g_el1c x B (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
  have p0013 := @g_vex x
  have p0014 := @g_unisn (.cv x) p0013
  have p0015 := @g_sneqi (syn_cuni (syn_csn (.cv x))) (.cv x) p0014
  have p0016 := @g_eqcomi (syn_csn (syn_cuni (syn_csn (.cv x)))) (syn_csn (.cv x)) p0015
  have p0017 := @g_id (.classEq B (syn_csn (.cv x)))
  have p0018 := @g_unieq B (syn_csn (.cv x))
  have p0019 :=
    @g_sneqd (.classEq B (syn_csn (.cv x))) (syn_cuni B) (syn_cuni (syn_csn (.cv x)))
      p0018
  have p0020 :=
    @g_n_3eqtr4a (.classEq B (syn_csn (.cv x))) (syn_csn (.cv x))
      (syn_csn (syn_cuni (syn_csn (.cv x)))) B (syn_csn (syn_cuni B)) p0016 p0017 p0019
  have freeVariableCertificate0 : x ∉ ((Wff.classEq B (syn_csn (syn_cuni B)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, dv_B_x,
      or_false, not_false_eq_true]
  have p0021 :=
    @g_exlimiv (.classEq B (syn_csn (.cv x))) (.classEq B (syn_csn (syn_cuni B))) x
      freeVariableCertificate0 p0020
  have p0022 :=
    @g_sylbi (.classMem B (syn_c1c)) (syn_wex x (.classEq B (syn_csn (.cv x))))
      (.classEq B (syn_csn (syn_cuni B))) p0012 p0021
  have p0023 :=
    @g_syl (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (.classMem B (syn_c1c))
      (.classEq B (syn_csn (syn_cuni B))) p0011 p0022
  have p0024 :=
    @g_syl5eq (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_cuni (syn_csn B)) B
      (syn_csn (syn_cuni B)) p0004 p0023
  have p0025 :=
    @g_uneq2d (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_cuni (syn_csn B))
      (syn_csn (syn_cuni B)) (syn_cuni A) p0024
  have p0026 :=
    @g_eqtrd (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) C
      (syn_cun (syn_cuni A) (syn_cuni (syn_csn B)))
      (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))) p0003 p0025
  have p0027 := @g_ssun1 A (syn_csn B)
  have p0028 := @g_sseq2 (syn_cpw1 C) (syn_cun A (syn_csn B)) A
  have p0029 :=
    @g_mpbiri (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_wss A (syn_cpw1 C))
      (syn_wss A (syn_cun A (syn_csn B))) p0027 p0028
  have p0030 :=
    @g_syl6ss (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) A (syn_cpw1 C) (syn_c1c)
      p0029 p0005
  have p0031 := @g_eqpw1uni A
  have p0032 :=
    @g_syl (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) (syn_wss A (syn_c1c))
      (.classEq A (syn_cpw1 (syn_cuni A))) p0030 p0031
  have p0033 := @g_uniex A hyp_pw1eqadj_1
  have p0034 := @g_uniex B hyp_pw1eqadj_2
  have p0035 := @g_sneq (.cv y) (syn_cuni B)
  have p0036 := @g_uneq12 (.cv x) (syn_cuni A) (syn_csn (.cv y)) (syn_csn (syn_cuni B))
  have p0037 :=
    @g_sylan2 (.classEq (.cv y) (syn_cuni B)) (.classEq (.cv x) (syn_cuni A))
      (.classEq (syn_csn (.cv y)) (syn_csn (syn_cuni B)))
      (.classEq (syn_cun (.cv x) (syn_csn (.cv y)))
        (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))))
      p0035 p0036
  have p0038 :=
    @g_eqeq2d (syn_wa (.classEq (.cv x) (syn_cuni A)) (.classEq (.cv y) (syn_cuni B)))
      (syn_cun (.cv x) (syn_csn (.cv y))) (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))) C
      p0037
  have p0039 := @g_pw1eq (.cv x) (syn_cuni A)
  have p0040 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cuni A)) (syn_cpw1 (.cv x)) (syn_cpw1 (syn_cuni A)) A
      p0039
  have p0041 :=
    @g_adantr (.classEq (.cv x) (syn_cuni A))
      (syn_wb (.classEq A (syn_cpw1 (.cv x))) (.classEq A (syn_cpw1 (syn_cuni A))))
      (.classEq (.cv y) (syn_cuni B)) p0040
  have p0042 :=
    @g_eqeq2d (.classEq (.cv y) (syn_cuni B)) (syn_csn (.cv y)) (syn_csn (syn_cuni B)) B
      p0035
  have p0043 :=
    @g_adantl (.classEq (.cv y) (syn_cuni B))
      (syn_wb (.classEq B (syn_csn (.cv y))) (.classEq B (syn_csn (syn_cuni B))))
      (.classEq (.cv x) (syn_cuni A)) p0042
  have p0044 :=
    @g_n_3anbi123d
      (syn_wa (.classEq (.cv x) (syn_cuni A)) (.classEq (.cv y) (syn_cuni B)))
      (.classEq C (syn_cun (.cv x) (syn_csn (.cv y))))
      (.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))))
      (.classEq A (syn_cpw1 (.cv x))) (.classEq A (syn_cpw1 (syn_cuni A)))
      (.classEq B (syn_csn (.cv y))) (.classEq B (syn_csn (syn_cuni B))) p0038 p0041 p0043
  have freeVariableCertificate1 :
    x ∉
      ((syn_w3a (.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))))
          (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_csn (syn_cuni B))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, dv_B_x,
      dv_C_x, dv_A_x, or_false, not_false_eq_true]
  have freeVariableCertificate2 :
    y ∉
      ((syn_w3a (.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))))
          (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_csn (syn_cuni B))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, dv_B_y,
      dv_C_y, dv_A_y, or_false, not_false_eq_true]
  have p0045 :=
    @g_spc2ev
      (syn_w3a (.classEq C (syn_cun (.cv x) (syn_csn (.cv y))))
        (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y))))
      (syn_w3a (.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))))
        (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_csn (syn_cuni B))))
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
      freeVariableCertificate1 freeVariableCertificate2
      (show x ≠ y from (by exact dv_x_y)) p0033 p0034 p0044
  have p0046 :=
    @g_syl3anc (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B)))
      (.classEq C (syn_cun (syn_cuni A) (syn_csn (syn_cuni B))))
      (.classEq A (syn_cpw1 (syn_cuni A))) (.classEq B (syn_csn (syn_cuni B)))
      (syn_wex x (syn_wex y (syn_w3a (.classEq C (syn_cun (.cv x) (syn_csn (.cv y))))
            (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y))))))
      p0026 p0032 p0023 p0045
  have p0047 := @g_pw1un (.cv x) (syn_csn (.cv y))
  have p0048 := @g_vex y
  have p0049 := @g_pw1sn (.cv y) p0048
  have p0050 :=
    @g_uneq2i (syn_cpw1 (syn_csn (.cv y))) (syn_csn (syn_csn (.cv y))) (syn_cpw1 (.cv x))
      p0049
  have p0051 :=
    @g_eqtri (syn_cpw1 (syn_cun (.cv x) (syn_csn (.cv y))))
      (syn_cun (syn_cpw1 (.cv x)) (syn_cpw1 (syn_csn (.cv y))))
      (syn_cun (syn_cpw1 (.cv x)) (syn_csn (syn_csn (.cv y)))) p0047 p0050
  have p0052 := @g_pw1eq C (syn_cun (.cv x) (syn_csn (.cv y)))
  have p0053 := @g_sneq B (syn_csn (.cv y))
  have p0054 := @g_uneq12 A (syn_cpw1 (.cv x)) (syn_csn B) (syn_csn (syn_csn (.cv y)))
  have p0055 :=
    @g_sylan2 (.classEq B (syn_csn (.cv y))) (.classEq A (syn_cpw1 (.cv x)))
      (.classEq (syn_csn B) (syn_csn (syn_csn (.cv y))))
      (.classEq (syn_cun A (syn_csn B))
        (syn_cun (syn_cpw1 (.cv x)) (syn_csn (syn_csn (.cv y)))))
      p0053 p0054
  have p0056 :=
    @g_eqeqan12d (.classEq C (syn_cun (.cv x) (syn_csn (.cv y))))
      (syn_wa (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y)))) (syn_cpw1 C)
      (syn_cpw1 (syn_cun (.cv x) (syn_csn (.cv y)))) (syn_cun A (syn_csn B))
      (syn_cun (syn_cpw1 (.cv x)) (syn_csn (syn_csn (.cv y)))) p0052 p0055
  have p0057 :=
    @g_n_3impb (.classEq C (syn_cun (.cv x) (syn_csn (.cv y))))
      (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y)))
      (syn_wb (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B)))
        (.classEq (syn_cpw1 (syn_cun (.cv x) (syn_csn (.cv y))))
          (syn_cun (syn_cpw1 (.cv x)) (syn_csn (syn_csn (.cv y))))))
      p0056
  have p0058 :=
    @g_mpbiri
      (syn_w3a (.classEq C (syn_cun (.cv x) (syn_csn (.cv y))))
        (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y))))
      (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B)))
      (.classEq (syn_cpw1 (syn_cun (.cv x) (syn_csn (.cv y))))
        (syn_cun (syn_cpw1 (.cv x)) (syn_csn (syn_csn (.cv y)))))
      p0051 p0057
  have freeVariableCertificate3 :
    x ∉ ((Wff.classEq (syn_cpw1 C) (syn_cun A (syn_csn B)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, dv_C_x,
      dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉ ((Wff.classEq (syn_cpw1 C) (syn_cun A (syn_csn B)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, dv_C_y,
      dv_A_y, dv_B_y, or_false, not_false_eq_true]
  have p0059 :=
    @g_exlimivv
      (syn_w3a (.classEq C (syn_cun (.cv x) (syn_csn (.cv y))))
        (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y))))
      (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B))) x y freeVariableCertificate3
      freeVariableCertificate4 p0058
  have p0060 :=
    @g_impbii (.classEq (syn_cpw1 C) (syn_cun A (syn_csn B)))
      (syn_wex x (syn_wex y (syn_w3a (.classEq C (syn_cun (.cv x) (syn_csn (.cv y))))
            (.classEq A (syn_cpw1 (.cv x))) (.classEq B (syn_csn (.cv y))))))
      p0046 p0059
  exact p0060

@[expose]
noncomputable def g_sspw1 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_sspw1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wss A (syn_cpw1 B))
        (syn_wex x (syn_wa (syn_wss (.cv x) B) (.classEq A (syn_cpw1 (.cv x)))))) :=
  by
  have p0000 := @g_uniss A (syn_cpw1 B)
  have p0001 := @g_unipw1 B
  have p0002 :=
    @g_syl6sseq (syn_wss A (syn_cpw1 B)) (syn_cuni A) (syn_cuni (syn_cpw1 B)) B p0000
      p0001
  have p0003 := @g_pw1ss1c B
  have p0004 := @g_sstr A (syn_cpw1 B) (syn_c1c)
  have p0005 :=
    @g_mpan2 (syn_wss A (syn_cpw1 B)) (syn_wss (syn_cpw1 B) (syn_c1c))
      (syn_wss A (syn_c1c)) p0003 p0004
  have p0006 := @g_eqpw1uni A
  have p0007 :=
    @g_syl (syn_wss A (syn_cpw1 B)) (syn_wss A (syn_c1c))
      (.classEq A (syn_cpw1 (syn_cuni A))) p0005 p0006
  have p0008 := @g_uniex A hyp_sspw1_1
  have p0009 := @g_sseq1 (.cv x) (syn_cuni A) B
  have p0010 := @g_pw1eq (.cv x) (syn_cuni A)
  have p0011 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cuni A)) (syn_cpw1 (.cv x)) (syn_cpw1 (syn_cuni A)) A
      p0010
  have p0012 :=
    @g_anbi12d (.classEq (.cv x) (syn_cuni A)) (syn_wss (.cv x) B)
      (syn_wss (syn_cuni A) B) (.classEq A (syn_cpw1 (.cv x)))
      (.classEq A (syn_cpw1 (syn_cuni A))) p0009 p0011
  have freeVariableCertificate0 :
    x ∉ ((syn_wa (syn_wss (syn_cuni A) B) (.classEq A (syn_cpw1 (syn_cuni A))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, dv_A_x,
      dv_B_x, or_false, not_false_eq_true]
  have p0013 :=
    @g_spcev (syn_wa (syn_wss (.cv x) B) (.classEq A (syn_cpw1 (.cv x))))
      (syn_wa (syn_wss (syn_cuni A) B) (.classEq A (syn_cpw1 (syn_cuni A)))) x
      (syn_cuni A)
      (by
        exact
          (show x ∉ ((syn_cuni A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
              exact (show x ∉ (A).fv from (by exact dv_A_x)))))
      freeVariableCertificate0 p0008 p0012
  have p0014 :=
    @g_syl2anc (syn_wss A (syn_cpw1 B)) (syn_wss (syn_cuni A) B)
      (.classEq A (syn_cpw1 (syn_cuni A)))
      (syn_wex x (syn_wa (syn_wss (.cv x) B) (.classEq A (syn_cpw1 (.cv x))))) p0002 p0007
      p0013
  have p0015 := @g_pw1ss (.cv x) B
  have p0016 := @g_sseq1 A (syn_cpw1 (.cv x)) (syn_cpw1 B)
  have p0017 :=
    @g_syl5ibr (syn_wss (.cv x) B) (syn_wss A (syn_cpw1 B))
      (.classEq A (syn_cpw1 (.cv x))) (syn_wss (syn_cpw1 (.cv x)) (syn_cpw1 B)) p0015
      p0016
  have p0018 :=
    @g_impcom (.classEq A (syn_cpw1 (.cv x))) (syn_wss (.cv x) B) (syn_wss A (syn_cpw1 B))
      p0017
  have freeVariableCertificate1 : x ∉ ((syn_wss A (syn_cpw1 B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, dv_A_x,
      dv_B_x, or_false, not_false_eq_true]
  have p0019 :=
    @g_exlimiv (syn_wa (syn_wss (.cv x) B) (.classEq A (syn_cpw1 (.cv x))))
      (syn_wss A (syn_cpw1 B)) x freeVariableCertificate1 p0018
  have p0020 :=
    @g_impbii (syn_wss A (syn_cpw1 B))
      (syn_wex x (syn_wa (syn_wss (.cv x) B) (.classEq A (syn_cpw1 (.cv x))))) p0014 p0019
  exact p0020

@[expose]
noncomputable def g_dfiota2 (ph : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (syn_cio x ph) (syn_cuni (.cab y (.all x (syn_wb ph (.objEq x y)))))) :=
  by
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iota ph x y
      (by exact (show y ∉ (ph).fv from (by exact dv_ph_y)))
      (show x ≠ y from (by exact dv_x_y))
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
      not_false_eq_true]
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x (.cv y)
      freeVariableCertificate0
  have p0002_e00_recanon :
    Nominal.NPrf (.classEq (syn_csn (.cv y)) (.cab x (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0001
  have p0002 :=
    @g_eqeq2i (syn_csn (.cv y)) (.cab x (.objEq x y)) (.cab x ph) p0002_e00_recanon
  have p0003 := @g_abbib ph (.objEq x y) x
  have p0004 :=
    @g_bitri (.classEq (.cab x ph) (syn_csn (.cv y)))
      (.classEq (.cab x ph) (.cab x (.objEq x y))) (.all x (syn_wb ph (.objEq x y))) p0002
      p0003
  have p0005 :=
    @g_abbii (.classEq (.cab x ph) (syn_csn (.cv y))) (.all x (syn_wb ph (.objEq x y))) y
      p0004
  have p0006 :=
    @g_unieqi (.cab y (.classEq (.cab x ph) (syn_csn (.cv y))))
      (.cab y (.all x (syn_wb ph (.objEq x y)))) p0005
  have p0007 :=
    @g_eqtri (syn_cio x ph) (syn_cuni (.cab y (.classEq (.cab x ph) (syn_csn (.cv y)))))
      (syn_cuni (.cab y (.all x (syn_wb ph (.objEq x y))))) p0000 p0006
  exact p0007

@[expose]
noncomputable def g_nfiota1 (ph : Wff) (x : Var) :
    Nominal.NPrf (syn_wnfc x (syn_cio x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_ph : y ∉ ph.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have p0000 :=
    @g_dfiota2 ph x y (by exact (show y ∉ (ph).fv from (by exact fresh_y_not_ph)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 := @g_nfaba1 (syn_wb ph (.classEq (.cv x) (.cv y))) x y
  have p0002 := @g_nfuni x (.cab y (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))) p0001
  have p0003_e00_recanon :
    Nominal.NPrf
      (.classEq (syn_cio x ph)
        (syn_cuni (.cab y (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cio syn_cuni syn_wex syn_wa syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.classMem
            · exact Nominal.RecanonTransportDev.TRecanonClass.same _
            · apply Nominal.RecanonTransportDev.TRecanonClass.cab
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0003 :=
    @g_nfcxfr x (syn_cio x ph)
      (syn_cuni (.cab y (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))))
      p0003_e00_recanon p0002
  exact p0003

@[expose]
noncomputable def g_iotabi (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (.all x (syn_wb ph ps)) (.classEq (syn_cio x ph) (syn_cio x ps))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ps.fv ∪ ({ x } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_not_ps : z ∉ ps.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have p0000 := @g_abbib ph ps x
  have p0001 :=
    @g_biimpri (.classEq (.cab x ph) (.cab x ps)) (.all x (syn_wb ph ps)) p0000
  have p0002 :=
    @g_eqeq1d (.all x (syn_wb ph ps)) (.cab x ph) (.cab x ps) (syn_csn (.cv z)) p0001
  have freeVariableCertificate0 : z ∉ ((Wff.all x (syn_wb ph ps))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, Finset.mem_union,
      Finset.mem_erase, fresh_z_not_ph, fresh_z_not_ps, or_false, and_false,
      not_false_eq_true]
  have p0003 :=
    @g_abbidv (.all x (syn_wb ph ps)) (.classEq (.cab x ph) (syn_csn (.cv z)))
      (.classEq (.cab x ps) (syn_csn (.cv z))) z freeVariableCertificate0 p0002
  have p0004 :=
    @g_unieqd (.all x (syn_wb ph ps)) (.cab z (.classEq (.cab x ph) (syn_csn (.cv z))))
      (.cab z (.classEq (.cab x ps) (syn_csn (.cv z)))) p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iota ph x z
      (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
      (show x ≠ z from (by exact fresh_x_ne_z))
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_iota ps x z
      (by exact (show z ∉ (ps).fv from (by exact fresh_z_not_ps)))
      (show x ≠ z from (by exact fresh_x_ne_z))
  have p0007 :=
    @g_n_3eqtr4g (.all x (syn_wb ph ps))
      (syn_cuni (.cab z (.classEq (.cab x ph) (syn_csn (.cv z)))))
      (syn_cuni (.cab z (.classEq (.cab x ps) (syn_csn (.cv z))))) (syn_cio x ph)
      (syn_cio x ps) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_uniabio (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.all x (syn_wb ph (.objEq x y))) (.classEq (syn_cuni (.cab x ph)) (.cv y))) :=
  by
  have p0000 := @g_abbib ph (.objEq x y) x
  have p0001 :=
    @g_biimpri (.classEq (.cab x ph) (.cab x (.objEq x y)))
      (.all x (syn_wb ph (.objEq x y))) p0000
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
      not_false_eq_true]
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn x (.cv y)
      freeVariableCertificate0
  have p0003_e01_recanon :
    Nominal.NPrf (.classEq (syn_csn (.cv y)) (.cab x (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0002
  have p0003 :=
    @g_syl6eqr (.all x (syn_wb ph (.objEq x y))) (.cab x ph) (.cab x (.objEq x y))
      (syn_csn (.cv y)) p0001 p0003_e01_recanon
  have p0004 :=
    @g_unieqd (.all x (syn_wb ph (.objEq x y))) (.cab x ph) (syn_csn (.cv y)) p0003
  have p0005 := @g_vex y
  have p0006 := @g_unisn (.cv y) p0005
  have p0007 :=
    @g_syl6eq (.all x (syn_wb ph (.objEq x y))) (syn_cuni (.cab x ph))
      (syn_cuni (syn_csn (.cv y))) (.cv y) p0004 p0006
  exact p0007

@[expose]
noncomputable def g_iotaval (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))
        (.classEq (syn_cio x ph) (.cv y))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have p0000 :=
    @g_dfiota2 ph x z (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
      (show x ≠ z from (by exact fresh_x_ne_z))
  have p0001 := @g_vex y
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
      not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_z, not_false_eq_true]
  have p0002 :=
    @g_sbeqalb ph x (.cv y) (.cv z) (syn_cvv) freeVariableCertificate0
      freeVariableCertificate1
  have p0003 := @g_equcomi y z
  have p0004_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) (.cv z)) (.classEq (.cv z) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0003
  have p0004 :=
    @g_syl6 (.classMem (.cv y) (syn_cvv))
      (syn_wa (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))
        (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))
      (.classEq (.cv y) (.cv z)) (.classEq (.cv z) (.cv y)) p0002 p0004_e01_recanon
  have p0005 := Nominal.mp p0001 p0004
  have p0006 :=
    @g_ex (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))
      (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (.classEq (.cv z) (.cv y)) p0005
  have p0007 := @g_equequ2 y z x
  have p0008_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv z))
        (syn_wb (.classEq (.cv x) (.cv y)) (.classEq (.cv x) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0007
  have p0008 :=
    @g_eqcoms (syn_wb (.classEq (.cv x) (.cv y)) (.classEq (.cv x) (.cv z))) (.cv y)
      (.cv z) p0008_e00_recanon
  have p0009 :=
    @g_bibi2d (.classEq (.cv z) (.cv y)) (.classEq (.cv x) (.cv y))
      (.classEq (.cv x) (.cv z)) ph p0008
  have p0010 :=
    @g_biimpd (.classEq (.cv z) (.cv y)) (syn_wb ph (.classEq (.cv x) (.cv y)))
      (syn_wb ph (.classEq (.cv x) (.cv z))) p0009
  have freeVariableCertificate2 : x ∉ ((Wff.classEq (.cv z) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_z, dv_x_y, or_false, not_false_eq_true]
  have p0011 :=
    @g_alimdv (.classEq (.cv z) (.cv y)) (syn_wb ph (.classEq (.cv x) (.cv y)))
      (syn_wb ph (.classEq (.cv x) (.cv z))) x freeVariableCertificate2 p0010
  have p0012 :=
    @g_com12 (.classEq (.cv z) (.cv y)) (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))
      (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) p0011
  have p0013 :=
    @g_impbid (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))
      (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (.classEq (.cv z) (.cv y)) p0006
      p0012
  have freeVariableCertificate3 :
    z ∉ ((Wff.all x (syn_wb ph (.classEq (.cv x) (.cv y))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x, fresh_z_ne_y, or_false,
      and_false, not_false_eq_true]
  have p0014 :=
    @g_alrimiv (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))
      (syn_wb (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (.classEq (.cv z) (.cv y)))
      z freeVariableCertificate3 p0013
  have p0015 :=
    @g_uniabio (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) z y
      (show z ≠ y from (by exact fresh_z_ne_y))
  have p0016_e01_recanon :
    Nominal.NPrf
      (.imp (.all z (syn_wb (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))
            (.classEq (.cv z) (.cv y))))
        (.classEq (syn_cuni (.cab z (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))))
          (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cuni syn_wex syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0016 :=
    @g_syl (.all x (syn_wb ph (.classEq (.cv x) (.cv y))))
      (.all z (syn_wb (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))
          (.classEq (.cv z) (.cv y))))
      (.classEq (syn_cuni (.cab z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))) (.cv y))
      p0014 p0016_e01_recanon
  have p0017_e00_recanon :
    Nominal.NPrf
      (.classEq (syn_cio x ph)
        (syn_cuni (.cab z (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cio syn_cuni syn_wex syn_wa syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.classMem
            · exact Nominal.RecanonTransportDev.TRecanonClass.same _
            · apply Nominal.RecanonTransportDev.TRecanonClass.cab
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0017 :=
    @g_syl5eq (.all x (syn_wb ph (.classEq (.cv x) (.cv y)))) (syn_cio x ph)
      (syn_cuni (.cab z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))) (.cv y)
      p0017_e00_recanon p0016
  exact p0017

@[expose]
noncomputable def g_iota1 (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_weu x ph) (syn_wb ph (.classEq (syn_cio x ph) (.cv x)))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have p0000 :=
    Nominal.dfEu x z ph (show x ≠ z from (by exact fresh_x_ne_z))
      (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
  have p0001 := @g_sp (syn_wb ph (.classEq (.cv x) (.cv z))) x
  have p0002 := @g_iotaval ph x z (show x ≠ z from (by exact fresh_x_ne_z))
  have p0003 :=
    @g_eqeq2d (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (syn_cio x ph) (.cv z)
      (.cv x) p0002
  have p0004 :=
    @g_bitr4d (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) ph
      (.classEq (.cv x) (.cv z)) (.classEq (.cv x) (syn_cio x ph)) p0001 p0003
  have p0005 := @g_eqcom (.cv x) (syn_cio x ph)
  have p0006 :=
    @g_syl6bb (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) ph
      (.classEq (.cv x) (syn_cio x ph)) (.classEq (syn_cio x ph) (.cv x)) p0004 p0005
  have freeVariableCertificate0 :
    z ∉ ((syn_wb ph (.classEq (syn_cio x ph) (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x, or_false, and_false,
      not_false_eq_true]
  have p0007 :=
    @g_exlimiv (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))
      (syn_wb ph (.classEq (syn_cio x ph) (.cv x))) z freeVariableCertificate0 p0006
  have p0008_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0008 :=
    @g_sylbi (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))
      (syn_wb ph (.classEq (syn_cio x ph) (.cv x))) p0008_e00_recanon p0007
  exact p0008

@[expose]
noncomputable def g_iotanul (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (.neg (syn_weu x ph)) (.classEq (syn_cio x ph) (syn_c0))) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have p0000 :=
    Nominal.dfEu x z ph (show x ≠ z from (by exact fresh_x_ne_z))
      (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
  have p0001 :=
    @g_dfiota2 ph x z (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
      (show x ≠ z from (by exact fresh_x_ne_z))
  have p0002 := @g_alnex (.all x (syn_wb ph (.objEq x z))) z
  have p0003 := Nominal.ax1 (.neg (.all x (syn_wb ph (.objEq x z)))) (.objEq z z)
  have p0004 := @g_eqidd (.neg (.all x (syn_wb ph (.objEq x z)))) (.cv z)
  have p0005_e01_recanon :
    Nominal.NPrf (.imp (.neg (.all x (syn_wb ph (.objEq x z)))) (.objEq z z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0004
  have p0005 :=
    @g_impbid1 (.neg (.all x (syn_wb ph (.objEq x z)))) (.objEq z z)
      (.neg (.all x (syn_wb ph (.objEq x z)))) p0003 p0005_e01_recanon
  have p0006 :=
    @g_con2bid (.neg (.all x (syn_wb ph (.objEq x z)))) (.objEq z z)
      (.all x (syn_wb ph (.objEq x z))) p0005
  have p0007 :=
    @g_alimi (.neg (.all x (syn_wb ph (.objEq x z))))
      (syn_wb (.all x (syn_wb ph (.objEq x z))) (.neg (.objEq z z))) z p0006
  have p0008 := @g_abbib (.all x (syn_wb ph (.objEq x z))) (.neg (.objEq z z)) z
  have p0009 :=
    @g_sylibr (.all z (.neg (.all x (syn_wb ph (.objEq x z)))))
      (.all z (syn_wb (.all x (syn_wb ph (.objEq x z))) (.neg (.objEq z z))))
      (.classEq (.cab z (.all x (syn_wb ph (.objEq x z)))) (.cab z (.neg (.objEq z z))))
      p0007 p0008
  have p0010 := @g_dfnul2 z
  have p0011_e01_recanon :
    Nominal.NPrf (.classEq (syn_c0) (.cab z (.neg (.objEq z z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cvv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0010
  have p0011 :=
    @g_syl6eqr (.all z (.neg (.all x (syn_wb ph (.objEq x z)))))
      (.cab z (.all x (syn_wb ph (.objEq x z)))) (.cab z (.neg (.objEq z z))) (syn_c0)
      p0009 p0011_e01_recanon
  have p0012 :=
    @g_sylbir (.neg (syn_wex z (.all x (syn_wb ph (.objEq x z)))))
      (.all z (.neg (.all x (syn_wb ph (.objEq x z)))))
      (.classEq (.cab z (.all x (syn_wb ph (.objEq x z)))) (syn_c0)) p0002 p0011
  have p0013 :=
    @g_unieqd (.neg (syn_wex z (.all x (syn_wb ph (.objEq x z)))))
      (.cab z (.all x (syn_wb ph (.objEq x z)))) (syn_c0) p0012
  have p0014 := @g_uni0
  have p0015 :=
    @g_syl6eq (.neg (syn_wex z (.all x (syn_wb ph (.objEq x z)))))
      (syn_cuni (.cab z (.all x (syn_wb ph (.objEq x z))))) (syn_cuni (syn_c0)) (syn_c0)
      p0013 p0014
  have p0016 :=
    @g_syl5eq (.neg (syn_wex z (.all x (syn_wb ph (.objEq x z))))) (syn_cio x ph)
      (syn_cuni (.cab z (.all x (syn_wb ph (.objEq x z))))) (syn_c0) p0001 p0015
  have p0017 :=
    @g_sylnbi (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.objEq x z))))
      (.classEq (syn_cio x ph) (syn_c0)) p0000 p0016
  exact p0017

@[expose]
noncomputable def g_iotaex (ph : Wff) (x : Var) :
    Nominal.NPrf (.classMem (syn_cio x ph) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have p0000 := @g_iotaval ph x z (show x ≠ z from (by exact fresh_x_ne_z))
  have p0001 :=
    @g_eqcomd (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))) (syn_cio x ph) (.cv z) p0000
  have p0002 :=
    @g_eximi (.all x (syn_wb ph (.classEq (.cv x) (.cv z))))
      (.classEq (.cv z) (syn_cio x ph)) z p0001
  have p0003 :=
    Nominal.dfEu x z ph (show x ≠ z from (by exact fresh_x_ne_z))
      (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
  have freeVariableCertificate0 : z ∉ ((syn_cio x ph)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio, Finset.mem_erase,
      fresh_z_not_ph, and_false, not_false_eq_true]
  have p0004 := @g_isset z (syn_cio x ph) freeVariableCertificate0
  have p0005_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_weu syn_wex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0005 :=
    @g_n_3imtr4i (syn_wex z (.all x (syn_wb ph (.classEq (.cv x) (.cv z)))))
      (syn_wex z (.classEq (.cv z) (syn_cio x ph))) (syn_weu x ph)
      (.classMem (syn_cio x ph) (syn_cvv)) p0002 p0005_e01_recanon p0004
  have p0006 := @g_iotanul ph x
  have p0007 := @g_n_0ex
  have p0008 :=
    @g_syl6eqel (.neg (syn_weu x ph)) (syn_cio x ph) (syn_c0) (syn_cvv) p0006 p0007
  have p0009 := @g_pm2_61i (syn_weu x ph) (.classMem (syn_cio x ph) (syn_cvv)) p0005 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart021`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_iota4 (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_weu x ph) (syn_wsbc (syn_cio x ph) x ph)) :=
  by
  let proofSupport : Finset Var := ph.fv ∪ ({ x } : Finset Var)
  let z : Var := freshVar proofSupport 0
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_ph : z ∉ ph.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have p0000 :=
    Nominal.dfEu x z ph (show x ≠ z from (by exact fresh_x_ne_z))
      (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
  have p0001 := @g_bi2 ph (.objEq x z)
  have p0002 := @g_alimi (syn_wb ph (.objEq x z)) (.imp (.objEq x z) ph) x p0001
  have p0003 := @g_sb2 ph x z
  have p0004 :=
    @g_syl (.all x (syn_wb ph (.objEq x z))) (.all x (.imp (.objEq x z) ph))
      (syn_wsb z x ph) p0002 p0003
  have p0005 := @g_iotaval ph x z (show x ≠ z from (by exact fresh_x_ne_z))
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp (.all x (syn_wb ph (.objEq x z))) (.classEq (syn_cio x ph) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cio syn_cuni syn_wex syn_wa syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.all
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0006 :=
    @g_eqcomd (.all x (syn_wb ph (.objEq x z))) (syn_cio x ph) (.cv z) p0006_e00_recanon
  have p0007 := @g_dfsbcq2 ph x z (syn_cio x ph)
  have p0008 :=
    @g_syl (.all x (syn_wb ph (.objEq x z))) (.classEq (.cv z) (syn_cio x ph))
      (syn_wb (syn_wsb z x ph) (syn_wsbc (syn_cio x ph) x ph)) p0006 p0007
  have p0009 :=
    @g_mpbid (.all x (syn_wb ph (.objEq x z))) (syn_wsb z x ph)
      (syn_wsbc (syn_cio x ph) x ph) p0004 p0008
  have freeVariableCertificate0 : z ∉ ((syn_wsbc (syn_cio x ph) x ph)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio, Finset.mem_union,
      Finset.mem_erase, fresh_z_not_ph, or_false, and_false, not_false_eq_true]
  have p0010 :=
    @g_exlimiv (.all x (syn_wb ph (.objEq x z))) (syn_wsbc (syn_cio x ph) x ph) z
      freeVariableCertificate0 p0009
  have p0011 :=
    @g_sylbi (syn_weu x ph) (syn_wex z (.all x (syn_wb ph (.objEq x z))))
      (syn_wsbc (syn_cio x ph) x ph) p0000 p0010
  exact p0011

@[expose]
noncomputable def g_iotabidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_iotabidv_1 : Nominal.NPrf (.imp ph (syn_wb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cio x ps) (syn_cio x ch))) :=
  by
  have p0000 :=
    @g_alrimiv ph (syn_wb ps ch) x (by exact (show x ∉ (ph).fv from (by exact dv_ph_x)))
      hyp_iotabidv_1
  have p0001 := @g_iotabi ps ch x
  have p0002 :=
    @g_syl ph (.all x (syn_wb ps ch)) (.classEq (syn_cio x ps) (syn_cio x ch)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_iotacl (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (syn_weu x ph) (.classMem (syn_cio x ph) (.cab x ph))) :=
  by
  have p0000 := @g_iota4 ph x
  have p0001 := (Nominal.biimpRefl (syn_wsbc (syn_cio x ph) x ph))
  have p0002 :=
    @g_sylib (syn_weu x ph) (syn_wsbc (syn_cio x ph) x ph)
      (.classMem (syn_cio x ph) (.cab x ph)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_reiotacl2 (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (syn_wreu x A ph)
        (.classMem (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) (syn_crab x A ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (syn_wreu x A ph))
  have p0001 := @g_iotacl (syn_wa (.classMem (.cv x) A) ph) x
  have p0002 :=
    @g_sylbi (syn_wreu x A ph) (syn_weu x (syn_wa (.classMem (.cv x) A) ph))
      (.classMem (syn_cio x (syn_wa (.classMem (.cv x) A) ph))
        (.cab x (syn_wa (.classMem (.cv x) A) ph)))
      p0000 p0001
  have p0003 := (Nominal.classEqRefl (syn_crab x A ph))
  have p0004 :=
    @g_syl6eleqr (syn_wreu x A ph) (syn_cio x (syn_wa (.classMem (.cv x) A) ph))
      (.cab x (syn_wa (.classMem (.cv x) A) ph)) (syn_crab x A ph) p0002 p0003
  exact p0004

@[expose]
noncomputable def g_reiotacl (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (syn_wreu x A ph) (.classMem (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) A)) :=
  by
  have p0000 := @g_ssrab2 ph x A (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
  have p0001 := @g_a1i (syn_wss (syn_crab x A ph) A) (syn_wreu x A ph) p0000
  have p0002 := @g_reiotacl2 ph x A
  have p0003 :=
    @g_sseldd (syn_wreu x A ph) (syn_crab x A ph) A
      (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_iota2df (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (B : Class)
    (V : Class) (hyp_iota2df_1 : Nominal.NPrf (.imp ph (.classMem B V)))
    (hyp_iota2df_2 : Nominal.NPrf (.imp ph (syn_weu x ps)))
    (hyp_iota2df_3 : Nominal.NPrf (.imp (syn_wa ph (.classEq (.cv x) B)) (syn_wb ps ch)))
    (hyp_iota2df_4 : Nominal.NPrf (syn_wnf x ph))
    (hyp_iota2df_5 : Nominal.NPrf (.imp ph (syn_wnf x ch)))
    (hyp_iota2df_6 : Nominal.NPrf (.imp ph (syn_wnfc x B))) :
    Nominal.NPrf (.imp ph (syn_wb ch (.classEq (syn_cio x ps) B))) :=
  by
  have p0000 := @g_nfiota1 ps x
  have p0001 := @g_a1i (syn_wnfc x (syn_cio x ps)) ph p0000
  have p0002 := @g_nfeqd ph x (syn_cio x ps) B p0001 hyp_iota2df_6
  have p0003 := @g_nfbid ph ch (.classEq (syn_cio x ps) B) x hyp_iota2df_5 p0002
  have p0004 := @g_simpr ph (.classEq (.cv x) B)
  have p0005 := @g_eqeq2d (syn_wa ph (.classEq (.cv x) B)) (.cv x) B (syn_cio x ps) p0004
  have p0006 :=
    @g_bibi12d (syn_wa ph (.classEq (.cv x) B)) ps ch (.classEq (syn_cio x ps) (.cv x))
      (.classEq (syn_cio x ps) B) hyp_iota2df_3 p0005
  have p0007 :=
    @g_ex ph (.classEq (.cv x) B)
      (syn_wb (syn_wb ps (.classEq (syn_cio x ps) (.cv x)))
        (syn_wb ch (.classEq (syn_cio x ps) B)))
      p0006
  have p0008 :=
    @g_alrimi ph
      (.imp (.classEq (.cv x) B) (syn_wb (syn_wb ps (.classEq (syn_cio x ps) (.cv x)))
          (syn_wb ch (.classEq (syn_cio x ps) B))))
      x hyp_iota2df_4 p0007
  have p0009 := @g_iota1 ps x
  have p0010 :=
    @g_syl ph (syn_weu x ps) (syn_wb ps (.classEq (syn_cio x ps) (.cv x))) hyp_iota2df_2
      p0009
  have p0011 :=
    @g_alrimi ph (syn_wb ps (.classEq (syn_cio x ps) (.cv x))) x hyp_iota2df_4 p0010
  have p0012 :=
    @g_vtoclgft (syn_wb ps (.classEq (syn_cio x ps) (.cv x)))
      (syn_wb ch (.classEq (syn_cio x ps) B)) x B V
  have p0013 :=
    @g_syl221anc ph (syn_wnfc x B) (syn_wnf x (syn_wb ch (.classEq (syn_cio x ps) B)))
      (.all x (.imp (.classEq (.cv x) B) (syn_wb (syn_wb ps (.classEq (syn_cio x ps) (.cv x)))
            (syn_wb ch (.classEq (syn_cio x ps) B)))))
      (.all x (syn_wb ps (.classEq (syn_cio x ps) (.cv x)))) (.classMem B V)
      (syn_wb ch (.classEq (syn_cio x ps) B)) hyp_iota2df_6 p0003 p0008 p0011
      hyp_iota2df_1 p0012
  exact p0013

@[expose]
noncomputable def g_iota2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_iota2_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A B) (syn_weu x ph)) (syn_wb ps (.classEq (syn_cio x ph) A))) :=
  by
  have p0000 := @g_elex A B
  have p0001 := @g_simpl (.classMem A (syn_cvv)) (syn_weu x ph)
  have p0002 := @g_simpr (.classMem A (syn_cvv)) (syn_weu x ph)
  have p0003 :=
    @g_adantl (.classEq (.cv x) A) (syn_wb ph ps)
      (syn_wa (.classMem A (syn_cvv)) (syn_weu x ph)) hyp_iota2_1
  have freeVariableCertificate0 : x ∉ ((Wff.classMem A (syn_cvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have p0004 := @g_nfv (.classMem A (syn_cvv)) x freeVariableCertificate0
  have p0005 := @g_nfeu1 ph x
  have p0006 := @g_nfan (.classMem A (syn_cvv)) (syn_weu x ph) x p0004 p0005
  have p0007 :=
    @g_nfvd (syn_wa (.classMem A (syn_cvv)) (syn_weu x ph)) ps x
      (by exact (show x ∉ (ps).fv from (by exact dv_ps_x)))
  have p0008 :=
    @g_nfcvd (syn_wa (.classMem A (syn_cvv)) (syn_weu x ph)) x A
      (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
  have p0009 :=
    @g_iota2df (syn_wa (.classMem A (syn_cvv)) (syn_weu x ph)) ph ps x A (syn_cvv) p0001
      p0002 p0003 p0006 p0007 p0008
  have p0010 :=
    @g_sylan (.classMem A B) (.classMem A (syn_cvv)) (syn_weu x ph)
      (syn_wb ps (.classEq (syn_cio x ph) A)) p0000 p0009
  exact p0010

@[expose]
noncomputable def g_reiota2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_reiota2_1 : Nominal.NPrf (.imp (.classEq (.cv x) B) (syn_wb ph ps))) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem B A) (syn_wreu x A ph))
        (syn_wb ps (.classEq (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) B))) :=
  by
  have p0000 := @g_simpl (.classMem B A) (syn_wreu x A ph)
  have p0001 :=
    @g_biantrurd (syn_wa (.classMem B A) (syn_wreu x A ph)) (.classMem B A) ps p0000
  have p0002 := (Nominal.biimpRefl (syn_wreu x A ph))
  have p0003 := @g_eleq1 (.cv x) B A
  have p0004 :=
    @g_anbi12d (.classEq (.cv x) B) (.classMem (.cv x) A) (.classMem B A) ph ps p0003
      hyp_reiota2_1
  have freeVariableCertificate0 : x ∉ ((syn_wa (.classMem B A) ps)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, dv_B_x, dv_A_x,
      dv_ps_x, or_false, not_false_eq_true]
  have p0005 :=
    @g_iota2 (syn_wa (.classMem (.cv x) A) ph) (syn_wa (.classMem B A) ps) x B A
      (by exact (show x ∉ (B).fv from (by exact dv_B_x))) freeVariableCertificate0 p0004
  have p0006 :=
    @g_sylan2b (syn_wreu x A ph) (.classMem B A)
      (syn_weu x (syn_wa (.classMem (.cv x) A) ph))
      (syn_wb (syn_wa (.classMem B A) ps)
        (.classEq (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) B))
      p0002 p0005
  have p0007 :=
    @g_bitrd (syn_wa (.classMem B A) (syn_wreu x A ph)) ps (syn_wa (.classMem B A) ps)
      (.classEq (syn_cio x (syn_wa (.classMem (.cv x) A) ph)) B) p0001 p0006
  exact p0007


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart022`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_dfaddc2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_cplc A B) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
          A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  let w : Var := freshVar proofSupport 4
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
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_t_ne_w : t ≠ w :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_w_ne_t : w ≠ t := Ne.symm fresh_t_ne_w
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addc x y z A B
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 := @g_vex x
  have freeVariableCertificate0 :
    y ∉
      ((syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 B)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.notMem_empty, fresh_y_not_B, or_false, not_false_eq_true]
  have freeVariableCertificate1 : y ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_y_ne_x, not_false_eq_true]
  have p0002 :=
    @g_elimak y
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
      A (.cv x) freeVariableCertificate0
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate1
      p0001
  have p0003 := @g_opkex (.cv y) (.cv x)
  have freeVariableCertificate2 :
    t ∉
      ((syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate3 : t ∉ ((syn_cpw1 (syn_cpw1 B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_t_not_B,
      not_false_eq_true]
  have freeVariableCertificate4 : t ∉ ((syn_copk (.cv y) (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_y, fresh_t_ne_x, or_false, not_false_eq_true]
  have p0004 :=
    @g_elimak t
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 B)) (syn_copk (.cv y) (.cv x)) freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4 p0003
  have freeVariableCertificate5 : z ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_t, not_false_eq_true]
  have p0005 :=
    @g_elpw12 z (.cv t) B freeVariableCertificate5
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
  have p0006 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 B)))
      (syn_wrex z B (.classEq (.cv t) (syn_csn (syn_csn (.cv z)))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0005
  have freeVariableCertificate6 :
    z ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
              (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_t, fresh_z_ne_y, fresh_z_ne_x,
      or_false, not_false_eq_true]
  have p0007 :=
    @g_r19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      z B freeVariableCertificate6
  have p0008 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 B)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
              (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (syn_wrex z B (.classEq (.cv t) (syn_csn (syn_csn (.cv z)))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
              (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wrex z B (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0006 p0007
  have p0009 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 B)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
              (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wrex z B (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      t p0008
  have p0010 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 B))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
              (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
  have p0011 :=
    @g_rexcom4
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
              (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      z t B (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B)))
      (show z ≠ t from (by exact fresh_z_ne_t))
  have p0012 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 B)))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex t (syn_wrex z B (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
                  (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 B))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
              (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wrex z B (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
                  (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0009 p0010 p0011
  have p0013 := @g_snex (syn_csn (.cv z))
  have p0014 := @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))
  have p0015 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
      (syn_copk (.cv t) (syn_copk (.cv y) (.cv x)))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0014
  have freeVariableCertificate7 : t ∉ ((syn_csn (syn_csn (.cv z)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_z,
      not_false_eq_true]
  have freeVariableCertificate8 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) (syn_cdif
            (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_z, fresh_t_ne_y, fresh_t_ne_x,
      or_false, not_false_eq_true]
  have p0016 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) (syn_cdif
          (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      t (syn_csn (syn_csn (.cv z))) freeVariableCertificate7 freeVariableCertificate8
      p0013 p0015
  have p0017 :=
    @g_eldif (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
      (syn_cins3k (syn_ccompl
          (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  have p0018 := @g_opkex (.cv z) (.cv y)
  have p0019 :=
    @g_elcompl (syn_copk (.cv z) (.cv y))
      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0018
  have p0020 := @g_vex z
  have p0021 := @g_vex y
  have p0022 := @g_ndisjrelk (.cv z) (.cv y) p0020 p0021
  have p0023 :=
    @g_necon2bbii
      (.classMem (syn_copk (.cv z) (.cv y))
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cin (.cv z) (.cv y)) (syn_c0) p0022
  have p0024 :=
    @g_bitr4i
      (.classMem (syn_copk (.cv z) (.cv y)) (syn_ccompl
          (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.neg (.classMem (syn_copk (.cv z) (.cv y))
          (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0)) p0019 p0023
  have p0025 :=
    @g_otkelins3k (.cv z) (.cv y) (.cv x)
      (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0020 p0021 p0001
  have p0026 := @g_incom (.cv y) (.cv z)
  have p0027 :=
    @g_eqeq1i (syn_cin (.cv y) (.cv z)) (syn_cin (.cv z) (.cv y)) (syn_c0) p0026
  have p0028 :=
    @g_n_3bitr4i
      (.classMem (syn_copk (.cv z) (.cv y)) (syn_ccompl
          (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (syn_cin (.cv z) (.cv y)) (syn_c0))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) (syn_cins3k
          (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0)) p0024 p0025 p0027
  have freeVariableCertificate9 : w ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_x, not_false_eq_true]
  have freeVariableCertificate10 : w ∉ ((syn_cun (.cv y) (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true]
  have p0029 :=
    @g_dfcleq w (.cv x) (syn_cun (.cv y) (.cv z)) freeVariableCertificate9
      freeVariableCertificate10
  have p0030 := @g_opkex (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))
  have freeVariableCertificate11 :
    t ∉
      ((syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate12 :
    t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate13 :
    t ∉ ((syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_z, fresh_t_ne_y, fresh_t_ne_x, or_false, not_false_eq_true]
  have p0031 :=
    @g_elimak t
      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
      freeVariableCertificate11 freeVariableCertificate12 freeVariableCertificate13 p0030
  have p0032 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))))
  have freeVariableCertificate14 : w ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_t, not_false_eq_true]
  have p0033 := @g_elpw141c w (.cv t) freeVariableCertificate14
  have p0034 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wex w (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))))
      (.classMem (syn_copk (.cv t)
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
            (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))
      p0033
  have freeVariableCertificate15 :
    w ∉
      ((Wff.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_w_ne_t, fresh_w_ne_z, fresh_w_ne_y,
      fresh_w_ne_x, or_false, not_false_eq_true]
  have p0035 :=
    @g_n_19_41v
      (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
      (.classMem (syn_copk (.cv t)
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
            (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))
      w freeVariableCertificate15
  have p0036 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))))
      (syn_wa (syn_wex w
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))))
        (.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))))
      (syn_wex w (syn_wa
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
          (.classMem (syn_copk (.cv t)
              (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))))
      p0034 p0035
  have p0037 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))))
      (syn_wex w (syn_wa
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
          (.classMem (syn_copk (.cv t)
              (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))))
      t p0036
  have p0038 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
        (.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))))
      w t
  have p0039 :=
    @g_bitr4i
      (syn_wex t
        (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
          (.classMem (syn_copk (.cv t)
              (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))))
      (syn_wex t (syn_wex w (syn_wa
            (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
            (.classMem (syn_copk (.cv t)
                (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))))))
      (syn_wex w (syn_wex t (syn_wa
            (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
            (.classMem (syn_copk (.cv t)
                (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))))))
      p0037 p0038
  have p0040 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classMem
          (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))))
      (syn_wex t
        (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
          (.classMem (syn_copk (.cv t)
              (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))))
      (syn_wex w (syn_wex t (syn_wa
            (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
            (.classMem (syn_copk (.cv t)
                (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))))))
      p0031 p0032 p0039
  have p0041 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))
  have p0042 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
  have p0043 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
      (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
      (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
        (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
      p0042
  have freeVariableCertificate16 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_w,
      not_false_eq_true]
  have freeVariableCertificate17 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_w, fresh_t_ne_z, fresh_t_ne_y,
      fresh_t_ne_x, or_false, not_false_eq_true]
  have p0044 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t)
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
            (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
            (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))
      t (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
      freeVariableCertificate16 freeVariableCertificate17 p0041 p0043
  have p0045 :=
    @g_elsymdif
      (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
        (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
      (syn_cins2k (syn_cins2k (syn_cssetk)))
      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))
  have p0046 := @g_snex (syn_csn (syn_csn (.cv w)))
  have p0047 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (.cv w)))) (syn_csn (syn_csn (.cv z)))
      (syn_copk (.cv y) (.cv x)) (syn_cins2k (syn_cssetk)) p0046 p0013 p0003
  have p0048 := @g_snex (.cv w)
  have p0049 :=
    @g_otkelins2k (syn_csn (.cv w)) (.cv y) (.cv x) (syn_cssetk) p0048 p0021 p0001
  have p0050 := @g_vex w
  have p0051 := @g_elssetk (.cv w) (.cv x) p0050 p0001
  have p0052_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv w)) (.cv x)) (syn_cssetk)) (.objMem w x)) :=
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
      p0051
  have p0052 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_cins2k (syn_cins2k (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv w)))) (syn_copk (.cv y) (.cv x)))
        (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv w)) (.cv x)) (syn_cssetk)) (.objMem w x) p0047
      p0049 p0052_e02_recanon
  have p0053 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (.cv w)))) (syn_csn (syn_csn (.cv z)))
      (syn_copk (.cv y) (.cv x)) (syn_cins3k (syn_cssetk)) p0046 p0013 p0003
  have p0054 :=
    @g_otkelins3k (syn_csn (.cv w)) (.cv y) (.cv x) (syn_cssetk) p0048 p0021 p0001
  have p0055 := @g_elssetk (.cv w) (.cv y) p0050 p0021
  have p0056_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv w)) (.cv y)) (syn_cssetk)) (.objMem w y)) :=
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
      p0055
  have p0056 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_cins2k (syn_cins3k (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv w)))) (syn_copk (.cv y) (.cv x)))
        (syn_cins3k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv w)) (.cv y)) (syn_cssetk)) (.objMem w y) p0053
      p0054 p0056_e02_recanon
  have p0057 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (.cv w)))) (syn_csn (syn_csn (.cv z)))
      (syn_copk (.cv y) (.cv x)) (syn_csik (syn_csik (syn_cssetk))) p0046 p0013 p0003
  have p0058 := @g_snex (syn_csn (.cv w))
  have p0059 := @g_snex (.cv z)
  have p0060 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv w))) (syn_csn (.cv z)) (syn_csik (syn_cssetk))
      p0058 p0059
  have p0061 := @g_opksnelsik (syn_csn (.cv w)) (.cv z) (syn_cssetk) p0048 p0020
  have p0062 := @g_elssetk (.cv w) (.cv z) p0050 p0020
  have p0063_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv w)) (.cv z)) (syn_cssetk)) (.objMem w z)) :=
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
      p0062
  have p0063 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv w))) (syn_csn (.cv z)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv w)) (.cv z)) (syn_cssetk)) (.objMem w z) p0061
      p0063_e01_recanon
  have p0064 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv w)))) (syn_csn (syn_csn (.cv z))))
        (syn_csik (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv w))) (syn_csn (.cv z)))
        (syn_csik (syn_cssetk)))
      (.objMem w z) p0057 p0060 p0063
  have p0065 :=
    @g_orbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_cins2k (syn_cins3k (syn_cssetk))))
      (.objMem w y)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))
      (.objMem w z) p0056 p0064
  have p0066 :=
    @g_elun
      (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
        (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
      (syn_cins2k (syn_cins3k (syn_cssetk)))
      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
  have p0067 := @g_elun (.cv w) (.cv y) (.cv z)
  have p0068_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv w) (syn_cun (.cv y) (.cv z)))
        (syn_wo (.objMem w y) (.objMem w z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wo
        simp (config := { failIfUnchanged := false }) only []
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
      p0067
  have p0068 :=
    @g_n_3bitr4i
      (syn_wo (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_cins2k (syn_cins3k (syn_cssetk)))) (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
      (syn_wo (.objMem w y) (.objMem w z))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
      (.classMem (.cv w) (syn_cun (.cv y) (.cv z))) p0065 p0066 p0068_e02_recanon
  have p0069 :=
    @g_bibi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_cins2k (syn_cins2k (syn_cssetk))))
      (.objMem w x)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
      (.classMem (.cv w) (syn_cun (.cv y) (.cv z))) p0052 p0068
  have p0070 :=
    @g_notbii
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_cins2k (syn_cins2k (syn_cssetk)))) (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
            (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))
      (syn_wb (.objMem w x) (.classMem (.cv w) (syn_cun (.cv y) (.cv z)))) p0069
  have p0071 :=
    @g_n_3bitri
      (syn_wex t (syn_wa
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
          (.classMem (syn_copk (.cv t)
              (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
            (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))
      (.neg (syn_wb (.classMem
            (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
              (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
            (syn_cins2k (syn_cins2k (syn_cssetk)))) (.classMem
            (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
              (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))))
      (.neg (syn_wb (.objMem w x) (.classMem (.cv w) (syn_cun (.cv y) (.cv z))))) p0044
      p0045 p0070
  have p0072 :=
    @g_exbii
      (syn_wex t (syn_wa
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
          (.classMem (syn_copk (.cv t)
              (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))))))
      (.neg (syn_wb (.objMem w x) (.classMem (.cv w) (syn_cun (.cv y) (.cv z))))) w p0071
  have p0073 :=
    @g_exnal (syn_wb (.objMem w x) (.classMem (.cv w) (syn_cun (.cv y) (.cv z)))) w
  have p0074 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wex w (syn_wex t (syn_wa
            (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
            (.classMem (syn_copk (.cv t)
                (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))))))
      (syn_wex w (.neg (syn_wb (.objMem w x) (.classMem (.cv w) (syn_cun (.cv y) (.cv z))))))
      (.neg (.all w (syn_wb (.objMem w x) (.classMem (.cv w) (syn_cun (.cv y) (.cv z))))))
      p0040 p0072 p0073
  have p0075 :=
    @g_con2bii
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.all w (syn_wb (.objMem w x) (.classMem (.cv w) (syn_cun (.cv y) (.cv z))))) p0074
  have p0076_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))
        (.all w (syn_wb (.objMem w x) (.classMem (.cv w) (syn_cun (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl
        simp (config := { failIfUnchanged := false }) only []
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
      p0029
  have p0076 :=
    @g_bitr2i (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))
      (.all w (syn_wb (.objMem w x) (.classMem (.cv w) (syn_cun (.cv y) (.cv z)))))
      (.neg (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0076_e00_recanon p0075
  have p0077 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) (syn_cins3k
          (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
      (.neg (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classEq (.cv x) (syn_cun (.cv y) (.cv z))) p0028 p0076
  have p0078 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) (syn_cdif
          (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
          (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (.neg
          (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
            (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))
      p0016 p0017 p0077
  have p0079 :=
    @g_rexbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))
      z B p0078
  have p0080 :=
    @g_n_3bitri
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 B))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
              (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wrex z B (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_cdif (syn_cins3k
                  (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))
      p0004 p0012 p0079
  have p0081 :=
    @g_rexbii
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B))))
      (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
          (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))
      y A p0080
  have p0082 :=
    @g_bitri
      (.classMem (.cv x) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
          A))
      (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 B)))))
      (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))))
      p0002 p0081
  have freeVariableCertificate18 :
    x ∉
      ((syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
          A)).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.notMem_empty, fresh_x_not_B, fresh_x_not_A, or_false, not_false_eq_true]
  have p0083 :=
    @g_eqabi
      (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv y) (.cv z))))))
      x
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
        A)
      freeVariableCertificate18 p0082
  have p0084 :=
    @g_eqtr4i (syn_cplc A B)
      (.cab x (syn_wrex y A (syn_wrex z B (syn_wa (.classEq (syn_cin (.cv y) (.cv z)) (syn_c0))
              (.classEq (.cv x) (syn_cun (.cv y) (.cv z)))))))
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
        A)
      p0000 p0083
  exact p0084


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart023`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_addcexlem :
    Nominal.NPrf
      (.classMem (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cvv)) :=
  by
  have p0000 := @g_ssetkex
  have p0001 := @g_ins3kex (syn_cssetk) p0000
  have p0003 := @g_ins2kex (syn_cssetk) p0000
  have p0004 := @g_inex (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)) p0001 p0003
  have p0005 := @g_n_1cex
  have p0006 := @g_pw1ex (syn_c1c) p0005
  have p0007 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0006
  have p0008 :=
    @g_imakex (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0004 p0007
  have p0009 :=
    @g_complex
      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0008
  have p0010 :=
    @g_ins3kex
      (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0009
  have p0011 := @g_ins2kex (syn_cins2k (syn_cssetk)) p0003
  have p0012 := @g_ins2kex (syn_cins3k (syn_cssetk)) p0001
  have p0014 := @g_sikex (syn_cssetk) p0000
  have p0015 := @g_sikex (syn_csik (syn_cssetk)) p0014
  have p0016 := @g_ins3kex (syn_csik (syn_csik (syn_cssetk))) p0015
  have p0017 :=
    @g_unex (syn_cins2k (syn_cins3k (syn_cssetk)))
      (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) p0012 p0016
  have p0018 :=
    @g_symdifex (syn_cins2k (syn_cins2k (syn_cssetk)))
      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))
      p0011 p0017
  have p0019 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0007
  have p0020 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0019
  have p0021 :=
    @g_imakex
      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0018 p0020
  have p0022 :=
    @g_difex
      (syn_cins3k (syn_ccompl
          (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0010 p0021
  exact p0022

@[expose]
noncomputable def g_addceq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cplc A C) (syn_cplc B C))) :=
  by
  have p0000 :=
    @g_imakeq2 A B
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 C)))
  have p0001 := @g_dfaddc2 A C
  have p0002 := @g_dfaddc2 B C
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B)
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 C)))
        A)
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 C)))
        B)
      (syn_cplc A C) (syn_cplc B C) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_addceq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cplc C A) (syn_cplc C B))) :=
  by
  have p0000 := @g_pw1eq A B
  have p0001 := @g_pw1eq (syn_cpw1 A) (syn_cpw1 B)
  have p0002 :=
    @g_syl (.classEq A B) (.classEq (syn_cpw1 A) (syn_cpw1 B))
      (.classEq (syn_cpw1 (syn_cpw1 A)) (syn_cpw1 (syn_cpw1 B))) p0000 p0001
  have p0003 :=
    @g_imakeq2d (.classEq A B) (syn_cpw1 (syn_cpw1 A)) (syn_cpw1 (syn_cpw1 B))
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0002
  have p0004 :=
    @g_imakeq1d (.classEq A B)
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 A)))
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
      C p0003
  have p0005 := @g_dfaddc2 C A
  have p0006 := @g_dfaddc2 C B
  have p0007 :=
    @g_n_3eqtr4g (.classEq A B)
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 A)))
        C)
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
        C)
      (syn_cplc C A) (syn_cplc C B) p0004 p0005 p0006
  exact p0007

@[expose]
noncomputable def g_addceq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq A C) (.classEq B D)) (.classEq (syn_cplc A B) (syn_cplc C D))) :=
  by
  have p0000 := @g_addceq1 A C B
  have p0001 := @g_addceq2 B D C
  have p0002 :=
    @g_sylan9eq (.classEq A C) (.classEq B D) (syn_cplc A B) (syn_cplc C B) (syn_cplc C D)
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_addceq1i (A : Class) (B : Class) (C : Class)
    (hyp_addceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cplc A C) (syn_cplc B C)) :=
  by
  have p0000 := @g_addceq1 A B C
  have p0001 := Nominal.mp hyp_addceqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_addceq2i (A : Class) (B : Class) (C : Class)
    (hyp_addceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (syn_cplc C A) (syn_cplc C B)) :=
  by
  have p0000 := @g_addceq2 A B C
  have p0001 := Nominal.mp hyp_addceqi_1 p0000
  exact p0001

@[expose]
noncomputable def g_addceq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_addceqi_1 : Nominal.NPrf (.classEq A B))
    (hyp_addceqi_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (syn_cplc A C) (syn_cplc B D)) :=
  by
  have p0000 := @g_addceq12 A C B D
  have p0001 :=
    @g_mp2an (.classEq A B) (.classEq C D) (.classEq (syn_cplc A C) (syn_cplc B D))
      hyp_addceqi_1 hyp_addceqi_2 p0000
  exact p0001

@[expose]
noncomputable def g_addceq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_addceqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cplc A C) (syn_cplc B C))) :=
  by
  have p0000 := @g_addceq1 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cplc A C) (syn_cplc B C)) hyp_addceqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_addceq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_addceqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cplc C A) (syn_cplc C B))) :=
  by
  have p0000 := @g_addceq2 A B C
  have p0001 :=
    @g_syl ph (.classEq A B) (.classEq (syn_cplc C A) (syn_cplc C B)) hyp_addceqd_1 p0000
  exact p0001

@[expose]
noncomputable def g_addceq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_addceqd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_addceqd_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (syn_cplc A C) (syn_cplc B D))) :=
  by
  have p0000 := @g_addceq12 A C B D
  have p0001 :=
    @g_syl2anc ph (.classEq A B) (.classEq C D) (.classEq (syn_cplc A C) (syn_cplc B D))
      hyp_addceqd_1 hyp_addceqd_2 p0000
  exact p0001

@[expose]
noncomputable def g_n_0cex : Nominal.NPrf (.classMem (syn_c0c) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_c0c))
  have p0001 := @g_snex (syn_c0)
  have p0002 := @g_eqeltri (syn_c0c) (syn_csn (syn_c0)) (syn_cvv) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_addcexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W)) (.classMem (syn_cplc A B) (syn_cvv))) :=
  by
  have p0000 := @g_dfaddc2 A B
  have p0001 := @g_pw1exg B W
  have p0002 := @g_pw1exg (syn_cpw1 B) (syn_cvv)
  have p0003 := @g_addcexlem
  have p0004 :=
    @g_imakexg
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 B)) (syn_cvv) (syn_cvv)
  have p0005 :=
    @g_mpan
      (.classMem (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cvv))
      (.classMem (syn_cpw1 (syn_cpw1 B)) (syn_cvv))
      (.classMem (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
        (syn_cvv))
      p0003 p0004
  have p0006 :=
    @g_n_3syl (.classMem B W) (.classMem (syn_cpw1 B) (syn_cvv))
      (.classMem (syn_cpw1 (syn_cpw1 B)) (syn_cvv))
      (.classMem (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
        (syn_cvv))
      p0001 p0002 p0005
  have p0007 :=
    @g_imakexg
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
      A (syn_cvv) V
  have p0008 :=
    @g_sylan (.classMem B W)
      (.classMem (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
        (syn_cvv))
      (.classMem A V)
      (.classMem (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
          A) (syn_cvv))
      p0006 p0007
  have p0009 :=
    @g_ancoms (.classMem B W) (.classMem A V)
      (.classMem (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
          A) (syn_cvv))
      p0008
  have p0010 :=
    @g_syl5eqel (syn_wa (.classMem A V) (.classMem B W)) (syn_cplc A B)
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 B)))
        A)
      (syn_cvv) p0000 p0009
  exact p0010

@[expose]
noncomputable def g_addcex (A : Class) (B : Class)
    (hyp_addcex_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_addcex_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cplc A B) (syn_cvv)) :=
  by
  have p0000 := @g_addcexg A B (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_cplc A B) (syn_cvv)) hyp_addcex_1 hyp_addcex_2 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk009StructuralPart024`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_dfnnc2 (x : Var) :
    Nominal.NPrf
      (.classEq (syn_cnnc) (syn_cint (syn_cdif (.cab x (.classMem (syn_c0c) (.cv x))) (syn_cimak
              (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak
                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var)
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  let w : Var := freshVar proofSupport 3
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact fresh_y (Finset.mem_singleton.mpr h)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_t_ne_w : t ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_t : w ≠ t := Ne.symm fresh_t_ne_w
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_nnc z y
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @g_eldif (.cv y) (.cab x (.classMem (syn_c0c) (.cv x)))
      (syn_cimak (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek
                (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c))
  have p0002 := @g_vex y
  have p0003 := @g_eleq2 (.cv x) (.cv y) (syn_c0c)
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((Wff.classMem (syn_c0c) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_x_ne_y, or_false, not_false_eq_true]
  have p0004 :=
    @g_elab (.classMem (syn_c0c) (.cv x)) (.classMem (syn_c0c) (.cv y)) x (.cv y)
      freeVariableCertificate0 freeVariableCertificate1 p0002 p0003
  have p0005 := @g_snex (.cv z)
  have p0006 := @g_opkeq1 (.cv t) (syn_csn (.cv z)) (.cv y)
  have p0007 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv z))) (syn_copk (.cv t) (.cv y))
      (syn_copk (syn_csn (.cv z)) (.cv y))
      (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif
                  (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0006
  have freeVariableCertificate2 : t ∉ ((syn_csn (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_z,
      not_false_eq_true]
  have freeVariableCertificate3 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cdif (syn_cssetk)
            (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                        (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_z, fresh_t_ne_y, or_false,
      not_false_eq_true]
  have p0008 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
            (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cdif (syn_cssetk)
          (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      t (syn_csn (.cv z)) freeVariableCertificate2 freeVariableCertificate3 p0005 p0007
  have p0009 :=
    @g_eldif (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk)
      (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                  (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0010 := @g_vex z
  have p0011 := @g_elssetk (.cv z) (.cv y) p0010 p0002
  have p0012 := @g_snex (.cv w)
  have p0013 := @g_opkeq2 (.cv t) (syn_csn (.cv w)) (syn_csn (.cv z))
  have p0014 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv w))) (syn_copk (syn_csn (.cv z)) (.cv t))
      (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w)))
      (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0013
  have p0015 := @g_vex w
  have p0016 :=
    @g_opksnelsik (.cv z) (.cv w)
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0010 p0015
  have p0017 :=
    @g_syl6bb (.classEq (.cv t) (syn_csn (.cv w)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
              (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv w))) (syn_csik (syn_cimagek
            (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (.cv z) (.cv w)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0014 p0016
  have p0018 := @g_opkeq1 (.cv t) (syn_csn (.cv w)) (.cv y)
  have p0019 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv w))) (syn_copk (.cv t) (.cv y))
      (syn_copk (syn_csn (.cv w)) (.cv y)) (syn_cssetk) p0018
  have p0020 :=
    @g_anbi12d (.classEq (.cv t) (syn_csn (.cv w)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
              (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (.cv z) (.cv w)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))
      (.classMem (syn_copk (syn_csn (.cv w)) (.cv y)) (syn_cssetk)) p0017 p0019
  have freeVariableCertificate4 : t ∉ ((syn_csn (.cv w))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_w,
      not_false_eq_true]
  have freeVariableCertificate5 :
    t ∉
      ((syn_wa (.classMem (syn_copk (.cv z) (.cv w)) (syn_cimagek (syn_cimak (syn_cdif
                  (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))
          (.classMem (syn_copk (syn_csn (.cv w)) (.cv y)) (syn_cssetk)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_t_ne_z, fresh_t_ne_w, fresh_t_ne_y,
      or_false, not_false_eq_true]
  have p0021 :=
    @g_ceqsexv
      (syn_wa (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)))
      (syn_wa (.classMem (syn_copk (.cv z) (.cv w)) (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classMem (syn_copk (syn_csn (.cv w)) (.cv y)) (syn_cssetk)))
      t (syn_csn (.cv w)) freeVariableCertificate4 freeVariableCertificate5 p0012 p0020
  have p0022 :=
    @g_opkelimagekg (.cv z) (.cv w)
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_cvv) (syn_cvv)
  have p0023 :=
    @g_mp2an (.classMem (.cv z) (syn_cvv)) (.classMem (.cv w) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv z) (.cv w)) (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classEq (.cv w) (syn_cimak (syn_cimak
              (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv z))))
      p0010 p0015 p0022
  have p0024 := @g_dfaddc2 (.cv z) (syn_c1c)
  have p0025 :=
    @g_eqeq2i (syn_cplc (.cv z) (syn_c1c))
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv z))
      (.cv w) p0024
  have p0026 :=
    @g_bitr4i
      (.classMem (syn_copk (.cv z) (.cv w)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (.cv w) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv z)))
      (.classEq (.cv w) (syn_cplc (.cv z) (syn_c1c))) p0023 p0025
  have p0027 := @g_elssetk (.cv w) (.cv y) p0015 p0002
  have p0028_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv w)) (.cv y)) (syn_cssetk)) (.objMem w y)) :=
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
      p0027
  have p0028 :=
    @g_anbi12i
      (.classMem (syn_copk (.cv z) (.cv w)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (.cv w) (syn_cplc (.cv z) (syn_c1c)))
      (.classMem (syn_copk (syn_csn (.cv w)) (.cv y)) (syn_cssetk)) (.objMem w y) p0026
      p0028_e01_recanon
  have p0029 :=
    @g_bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv w))) (syn_wa
            (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)))))
      (syn_wa (.classMem (syn_copk (.cv z) (.cv w)) (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classMem (syn_copk (syn_csn (.cv w)) (.cv y)) (syn_cssetk)))
      (syn_wa (.classEq (.cv w) (syn_cplc (.cv z) (syn_c1c))) (.objMem w y)) p0021 p0028
  have p0030 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv w))) (syn_wa
            (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)))))
      (syn_wa (.classEq (.cv w) (syn_cplc (.cv z) (syn_c1c))) (.objMem w y)) w p0029
  have freeVariableCertificate6 : t ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_y, not_false_eq_true]
  have freeVariableCertificate7 :
    t ∉
      ((syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0031 :=
    @g_opkelcok t (syn_csn (.cv z)) (.cv y) (syn_cssetk)
      (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      freeVariableCertificate2 freeVariableCertificate6
      (by
        exact
          (show t ∉ ((syn_cssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate7 p0005 p0002
  have freeVariableCertificate8 : w ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_t, not_false_eq_true]
  have p0032 := @g_el1c w (.cv t) freeVariableCertificate8
  have p0033 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c))
      (syn_wex w (.classEq (.cv t) (syn_csn (.cv w))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)))
      p0032
  have freeVariableCertificate9 :
    w ∉
      ((syn_wa (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                  (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_w_ne_z, fresh_w_ne_t, fresh_w_ne_y,
      or_false, not_false_eq_true]
  have p0034 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv w)))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)))
      w freeVariableCertificate9
  have p0035 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_c1c)) (syn_wa
          (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                  (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))))
      (syn_wa (syn_wex w (.classEq (.cv t) (syn_csn (.cv w)))) (syn_wa
          (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                  (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))))
      (syn_wex w (syn_wa (.classEq (.cv t) (syn_csn (.cv w))) (syn_wa
            (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)))))
      p0033 p0034
  have p0036 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_c1c)) (syn_wa
          (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                  (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))))
      (syn_wex w (syn_wa (.classEq (.cv t) (syn_csn (.cv w))) (syn_wa
            (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)))))
      t p0035
  have p0037 :=
    @g_sikss1c1c
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0038 :=
    @g_sseli
      (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cxpk (syn_c1c) (syn_c1c)) (syn_copk (syn_csn (.cv z)) (.cv t)) p0037
  have p0039 := @g_vex t
  have p0040 := @g_opkelxpk (syn_csn (.cv z)) (.cv t) (syn_c1c) (syn_c1c) p0005 p0039
  have p0041 :=
    @g_simprbi
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_cxpk (syn_c1c) (syn_c1c)))
      (.classMem (syn_csn (.cv z)) (syn_c1c)) (.classMem (.cv t) (syn_c1c)) p0040
  have p0042 :=
    @g_syl
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
              (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_cxpk (syn_c1c) (syn_c1c)))
      (.classMem (.cv t) (syn_c1c)) p0038 p0041
  have p0043 :=
    @g_pm4_71ri
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
              (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (.cv t) (syn_c1c)) p0042
  have p0044 :=
    @g_anbi1i
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
              (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (syn_csn (.cv z)) (.cv t))
          (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)) p0043
  have p0045 :=
    @g_anass (.classMem (.cv t) (syn_c1c))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
              (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))
  have p0046 :=
    @g_bitri
      (syn_wa (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)))
      (syn_wa (syn_wa (.classMem (.cv t) (syn_c1c))
          (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                  (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)))
      (syn_wa (.classMem (.cv t) (syn_c1c)) (syn_wa
          (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                  (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))))
      p0044 p0045
  have p0047 :=
    @g_exbii
      (syn_wa (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)))
      (syn_wa (.classMem (.cv t) (syn_c1c)) (syn_wa
          (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                  (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))))
      t p0046
  have p0048 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (.cv w))) (syn_wa
          (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                  (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))))
      w t
  have p0049 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (syn_wa
            (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk)))))
      (syn_wex t (syn_wex w (syn_wa (.classEq (.cv t) (syn_csn (.cv w))) (syn_wa
              (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))))))
      (syn_wex t (syn_wa (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek
                (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))))
      (syn_wex w (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv w))) (syn_wa
              (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))))))
      p0036 p0047 p0048
  have p0050 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_ccomk (syn_cssetk) (syn_csik
            (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex t (syn_wa (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek
                (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))))
      (syn_wex w (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv w))) (syn_wa
              (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))))))
      p0031 p0049
  have freeVariableCertificate10 : w ∉ ((syn_cplc (.cv z) (syn_c1c))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_w_ne_z, or_false,
      not_false_eq_true]
  have freeVariableCertificate11 : w ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_y, not_false_eq_true]
  have p0051 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV w
      (syn_cplc (.cv z) (syn_c1c)) (.cv y) freeVariableCertificate10 freeVariableCertificate11)
  have p0052_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)) (syn_wex w
          (syn_wa (.classEq (.cv w) (syn_cplc (.cv z) (syn_c1c))) (.objMem w y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa syn_c1c
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
      p0051
  have p0052 :=
    @g_n_3bitr4i
      (syn_wex w (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv w))) (syn_wa
              (.classMem (syn_copk (syn_csn (.cv z)) (.cv t)) (syn_csik (syn_cimagek (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (.classMem (syn_copk (.cv t) (.cv y)) (syn_cssetk))))))
      (syn_wex w (syn_wa (.classEq (.cv w) (syn_cplc (.cv z) (syn_c1c))) (.objMem w y)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_ccomk (syn_cssetk) (syn_csik
            (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)) p0030 p0050 p0052_e02_recanon
  have p0053 :=
    @g_notbii
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_ccomk (syn_cssetk) (syn_csik
            (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)) p0052
  have p0054_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk)) (.objMem z y)) :=
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
      p0011
  have p0054 :=
    @g_anbi12i (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk)) (.objMem z y)
      (.neg (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_ccomk (syn_cssetk) (syn_csik
              (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.neg (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y))) p0054_e00_recanon p0053
  have p0055 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cdif (syn_cssetk)
          (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk)) (.neg
          (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_ccomk (syn_cssetk) (syn_csik
                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wa (.objMem z y) (.neg (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)))) p0009
      p0054
  have p0056 :=
    @g_bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv z)))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
                (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cdif (syn_cssetk)
          (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.objMem z y) (.neg (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)))) p0008
      p0055
  have p0057 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv z)))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
                (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wa (.objMem z y) (.neg (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)))) z
      p0056
  have freeVariableCertificate12 :
    t ∉
      ((syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak
                  (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have p0058 :=
    @g_elimak t
      (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif
                  (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_c1c) (.cv y) freeVariableCertificate12
      (by
        exact
          (show t ∉ ((syn_c1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate6 p0002
  have freeVariableCertificate13 : z ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_t, not_false_eq_true]
  have p0059 := @g_el1c z (.cv t) freeVariableCertificate13
  have p0060 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c))
      (syn_wex z (.classEq (.cv t) (syn_csn (.cv z))))
      (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
            (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0059
  have freeVariableCertificate14 :
    z ∉
      ((Wff.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
              (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))).fv :=
    by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_singleton, Finset.notMem_empty, fresh_z_ne_t, fresh_z_ne_y, or_false,
      not_false_eq_true]
  have p0061 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv z)))
      (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
            (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      z freeVariableCertificate14
  have p0062 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv y))
          (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wa (syn_wex z (.classEq (.cv t) (syn_csn (.cv z))))
        (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
              (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (.cv z)))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
                (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0060 p0061
  have p0063 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv y))
          (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (.cv z)))
          (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
                (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      t p0062
  have p0064 :=
    (Nominal.biimpRefl (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv y))
          (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
  have p0065 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (.cv z))) (.classMem (syn_copk (.cv t) (.cv y))
          (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      z t
  have p0066 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv y))
            (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wex t (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (.cv z)))
            (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
                  (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk)
            (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                        (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv z)))
            (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
                  (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      p0063 p0064 p0065
  have p0067 :=
    @g_bitri
      (.classMem (.cv y) (syn_cimak (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik
                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c)))
      (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk)
            (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                        (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv z)))
            (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
                  (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      p0058 p0066
  have p0068 :=
    (Nominal.biimpRefl
      (syn_wrex z (.cv y) (.neg (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)))))
  have p0069_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex z (.cv y) (.neg (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y))))
        (syn_wex z (syn_wa (.objMem z y)
            (.neg (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_cplc, syn_c1c]
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
      p0068
  have p0069 :=
    @g_n_3bitr4i
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv z)))
            (.classMem (syn_copk (.cv t) (.cv y)) (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
                  (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_wex z (syn_wa (.objMem z y) (.neg (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)))))
      (.classMem (.cv y) (syn_cimak (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik
                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c)))
      (syn_wrex z (.cv y) (.neg (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)))) p0057
      p0067 p0069_e02_recanon
  have p0070 := @g_rexnal (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)) z (.cv y)
  have p0071 :=
    @g_bitr2i
      (.classMem (.cv y) (syn_cimak (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik
                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c)))
      (syn_wrex z (.cv y) (.neg (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y))))
      (.neg (syn_wral z (.cv y) (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)))) p0069
      p0070
  have p0072 :=
    @g_con1bii (syn_wral z (.cv y) (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)))
      (.classMem (.cv y) (syn_cimak (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik
                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c)))
      p0071
  have p0073 :=
    @g_anbi12i (.classMem (.cv y) (.cab x (.classMem (syn_c0c) (.cv x))))
      (.classMem (syn_c0c) (.cv y))
      (.neg (.classMem (.cv y) (syn_cimak (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk)
                (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c))))
      (syn_wral z (.cv y) (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y))) p0004 p0072
  have p0074 :=
    @g_bitri
      (.classMem (.cv y) (syn_cdif (.cab x (.classMem (syn_c0c) (.cv x))) (syn_cimak
            (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c))))
      (syn_wa (.classMem (.cv y) (.cab x (.classMem (syn_c0c) (.cv x)))) (.neg
          (.classMem (.cv y) (syn_cimak (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik
                    (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c)))))
      (syn_wa (.classMem (syn_c0c) (.cv y))
        (syn_wral z (.cv y) (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y))))
      p0001 p0073
  have freeVariableCertificate15 :
    y ∉
      ((syn_cdif (.cab x (.classMem (syn_c0c) (.cv x))) (syn_cimak (syn_cdif (syn_cssetk)
              (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                          (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c)))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
      NFChoice.Compiler.CoreFVSimp.fv_class_cab,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
      Finset.mem_erase, Finset.mem_singleton, Finset.notMem_empty, fresh_y_ne_x, or_false,
      and_false, not_false_eq_true]
  have p0075 :=
    @g_eqabi
      (syn_wa (.classMem (syn_c0c) (.cv y))
        (syn_wral z (.cv y) (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y))))
      y
      (syn_cdif (.cab x (.classMem (syn_c0c) (.cv x))) (syn_cimak (syn_cdif (syn_cssetk)
            (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                        (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c)))
      freeVariableCertificate15 p0074
  have p0076 :=
    @g_inteqi
      (syn_cdif (.cab x (.classMem (syn_c0c) (.cv x))) (syn_cimak (syn_cdif (syn_cssetk)
            (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                        (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c)))
      (.cab y (syn_wa (.classMem (syn_c0c) (.cv y))
          (syn_wral z (.cv y) (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y)))))
      p0075
  have p0077 :=
    @g_eqtr4i (syn_cnnc)
      (syn_cint (.cab y (syn_wa (.classMem (syn_c0c) (.cv y))
            (syn_wral z (.cv y) (.classMem (syn_cplc (.cv z) (syn_c1c)) (.cv y))))))
      (syn_cint (syn_cdif (.cab x (.classMem (syn_c0c) (.cv x))) (syn_cimak
            (syn_cdif (syn_cssetk) (syn_ccomk (syn_cssetk) (syn_csik (syn_cimagek (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_c1c))))
      p0000 p0076
  exact p0077


end NFChoice.DirectNominalPrf.WPPReplay

end
