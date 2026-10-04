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

/-- Checked nominal proof certificate identified upstream as `g_pw1eqadj`. -/
@[expose]
noncomputable def gPw1eqadj (x : Var) (y : Var) (A : Class) (B : Class) (C : Class)
    (dv_A_x : x ∉ A.fv) (dv_A_y : y ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_B_y : y ∉ B.fv)
    (dv_C_x : x ∉ C.fv) (dv_C_y : y ∉ C.fv) (dv_x_y : x ≠ y)
    (hyp_pw1eqadj_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_pw1eqadj_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (synWb (.classEq (synCpw1 C) (synCun A (synCsn B))) (synWex x (synWex y
            (synW3a (.classEq C (synCun (.cv x) (synCsn (.cv y))))
              (.classEq A (synCpw1 (.cv x))) (.classEq B (synCsn (.cv y))))))) :=
  by
  have p0000 := @gUnieq (synCpw1 C) (synCun A (synCsn B))
  have p0001 := @gUnipw1 C
  have p0002 := @gUniun A (synCsn B)
  have p0003 :=
    @gN3eqtr3g (.classEq (synCpw1 C) (synCun A (synCsn B))) (synCuni (synCpw1 C))
      (synCuni (synCun A (synCsn B))) C (synCun (synCuni A) (synCuni (synCsn B)))
      p0000 p0001 p0002
  have p0004 := @gUnisn B hyp_pw1eqadj_2
  have p0005 := @gPw1ss1c C
  have p0006 := @gSsun2 (synCsn B) A
  have p0007 := @gSnid B hyp_pw1eqadj_2
  have p0008 := @gSselii (synCsn B) (synCun A (synCsn B)) B p0006 p0007
  have p0009 := @gEleq2 (synCpw1 C) (synCun A (synCsn B)) B
  have p0010 :=
    @gMpbiri (.classEq (synCpw1 C) (synCun A (synCsn B))) (.classMem B (synCpw1 C))
      (.classMem B (synCun A (synCsn B))) p0008 p0009
  have p0011 :=
    @gSseldi (.classEq (synCpw1 C) (synCun A (synCsn B))) (synCpw1 C) (synC1c) B
      p0005 p0010
  have p0012 := @gEl1c x B (by exact (show x ∉ (B).fv from (by exact dv_B_x)))
  have p0013 := @gVex x
  have p0014 := @gUnisn (.cv x) p0013
  have p0015 := @gSneqi (synCuni (synCsn (.cv x))) (.cv x) p0014
  have p0016 := @gEqcomi (synCsn (synCuni (synCsn (.cv x)))) (synCsn (.cv x)) p0015
  have p0017 := @gId (.classEq B (synCsn (.cv x)))
  have p0018 := @gUnieq B (synCsn (.cv x))
  have p0019 :=
    @gSneqd (.classEq B (synCsn (.cv x))) (synCuni B) (synCuni (synCsn (.cv x)))
      p0018
  have p0020 :=
    @gN3eqtr4a (.classEq B (synCsn (.cv x))) (synCsn (.cv x))
      (synCsn (synCuni (synCsn (.cv x)))) B (synCsn (synCuni B)) p0016 p0017 p0019
  have freeVariableCertificate0 : x ∉ ((Wff.classEq B (synCsn (synCuni B)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni, Finset.mem_union, dv_B_x,
      or_false, not_false_eq_true]
  have p0021 :=
    @gExlimiv (.classEq B (synCsn (.cv x))) (.classEq B (synCsn (synCuni B))) x
      freeVariableCertificate0 p0020
  have p0022 :=
    @gSylbi (.classMem B (synC1c)) (synWex x (.classEq B (synCsn (.cv x))))
      (.classEq B (synCsn (synCuni B))) p0012 p0021
  have p0023 :=
    @gSyl (.classEq (synCpw1 C) (synCun A (synCsn B))) (.classMem B (synC1c))
      (.classEq B (synCsn (synCuni B))) p0011 p0022
  have p0024 :=
    @gSyl5eq (.classEq (synCpw1 C) (synCun A (synCsn B))) (synCuni (synCsn B)) B
      (synCsn (synCuni B)) p0004 p0023
  have p0025 :=
    @gUneq2d (.classEq (synCpw1 C) (synCun A (synCsn B))) (synCuni (synCsn B))
      (synCsn (synCuni B)) (synCuni A) p0024
  have p0026 :=
    @gEqtrd (.classEq (synCpw1 C) (synCun A (synCsn B))) C
      (synCun (synCuni A) (synCuni (synCsn B)))
      (synCun (synCuni A) (synCsn (synCuni B))) p0003 p0025
  have p0027 := @gSsun1 A (synCsn B)
  have p0028 := @gSseq2 (synCpw1 C) (synCun A (synCsn B)) A
  have p0029 :=
    @gMpbiri (.classEq (synCpw1 C) (synCun A (synCsn B))) (synWss A (synCpw1 C))
      (synWss A (synCun A (synCsn B))) p0027 p0028
  have p0030 :=
    @gSyl6ss (.classEq (synCpw1 C) (synCun A (synCsn B))) A (synCpw1 C) (synC1c)
      p0029 p0005
  have p0031 := @gEqpw1uni A
  have p0032 :=
    @gSyl (.classEq (synCpw1 C) (synCun A (synCsn B))) (synWss A (synC1c))
      (.classEq A (synCpw1 (synCuni A))) p0030 p0031
  have p0033 := @gUniex A hyp_pw1eqadj_1
  have p0034 := @gUniex B hyp_pw1eqadj_2
  have p0035 := @gSneq (.cv y) (synCuni B)
  have p0036 := @gUneq12 (.cv x) (synCuni A) (synCsn (.cv y)) (synCsn (synCuni B))
  have p0037 :=
    @gSylan2 (.classEq (.cv y) (synCuni B)) (.classEq (.cv x) (synCuni A))
      (.classEq (synCsn (.cv y)) (synCsn (synCuni B)))
      (.classEq (synCun (.cv x) (synCsn (.cv y)))
        (synCun (synCuni A) (synCsn (synCuni B))))
      p0035 p0036
  have p0038 :=
    @gEqeq2d (synWa (.classEq (.cv x) (synCuni A)) (.classEq (.cv y) (synCuni B)))
      (synCun (.cv x) (synCsn (.cv y))) (synCun (synCuni A) (synCsn (synCuni B))) C
      p0037
  have p0039 := @gPw1eq (.cv x) (synCuni A)
  have p0040 :=
    @gEqeq2d (.classEq (.cv x) (synCuni A)) (synCpw1 (.cv x)) (synCpw1 (synCuni A)) A
      p0039
  have p0041 :=
    @gAdantr (.classEq (.cv x) (synCuni A))
      (synWb (.classEq A (synCpw1 (.cv x))) (.classEq A (synCpw1 (synCuni A))))
      (.classEq (.cv y) (synCuni B)) p0040
  have p0042 :=
    @gEqeq2d (.classEq (.cv y) (synCuni B)) (synCsn (.cv y)) (synCsn (synCuni B)) B
      p0035
  have p0043 :=
    @gAdantl (.classEq (.cv y) (synCuni B))
      (synWb (.classEq B (synCsn (.cv y))) (.classEq B (synCsn (synCuni B))))
      (.classEq (.cv x) (synCuni A)) p0042
  have p0044 :=
    @gN3anbi123d
      (synWa (.classEq (.cv x) (synCuni A)) (.classEq (.cv y) (synCuni B)))
      (.classEq C (synCun (.cv x) (synCsn (.cv y))))
      (.classEq C (synCun (synCuni A) (synCsn (synCuni B))))
      (.classEq A (synCpw1 (.cv x))) (.classEq A (synCpw1 (synCuni A)))
      (.classEq B (synCsn (.cv y))) (.classEq B (synCsn (synCuni B))) p0038 p0041 p0043
  have freeVariableCertificate1 :
    x ∉
      ((synW3a (.classEq C (synCun (synCuni A) (synCsn (synCuni B))))
          (.classEq A (synCpw1 (synCuni A))) (.classEq B (synCsn (synCuni B))))).fv :=
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
      ((synW3a (.classEq C (synCun (synCuni A) (synCsn (synCuni B))))
          (.classEq A (synCpw1 (synCuni A))) (.classEq B (synCsn (synCuni B))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, dv_B_y,
      dv_C_y, dv_A_y, or_false, not_false_eq_true]
  have p0045 :=
    @gSpc2ev
      (synW3a (.classEq C (synCun (.cv x) (synCsn (.cv y))))
        (.classEq A (synCpw1 (.cv x))) (.classEq B (synCsn (.cv y))))
      (synW3a (.classEq C (synCun (synCuni A) (synCsn (synCuni B))))
        (.classEq A (synCpw1 (synCuni A))) (.classEq B (synCsn (synCuni B))))
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
      freeVariableCertificate1 freeVariableCertificate2
      (show x ≠ y from (by exact dv_x_y)) p0033 p0034 p0044
  have p0046 :=
    @gSyl3anc (.classEq (synCpw1 C) (synCun A (synCsn B)))
      (.classEq C (synCun (synCuni A) (synCsn (synCuni B))))
      (.classEq A (synCpw1 (synCuni A))) (.classEq B (synCsn (synCuni B)))
      (synWex x (synWex y (synW3a (.classEq C (synCun (.cv x) (synCsn (.cv y))))
            (.classEq A (synCpw1 (.cv x))) (.classEq B (synCsn (.cv y))))))
      p0026 p0032 p0023 p0045
  have p0047 := @gPw1un (.cv x) (synCsn (.cv y))
  have p0048 := @gVex y
  have p0049 := @gPw1sn (.cv y) p0048
  have p0050 :=
    @gUneq2i (synCpw1 (synCsn (.cv y))) (synCsn (synCsn (.cv y))) (synCpw1 (.cv x))
      p0049
  have p0051 :=
    @gEqtri (synCpw1 (synCun (.cv x) (synCsn (.cv y))))
      (synCun (synCpw1 (.cv x)) (synCpw1 (synCsn (.cv y))))
      (synCun (synCpw1 (.cv x)) (synCsn (synCsn (.cv y)))) p0047 p0050
  have p0052 := @gPw1eq C (synCun (.cv x) (synCsn (.cv y)))
  have p0053 := @gSneq B (synCsn (.cv y))
  have p0054 := @gUneq12 A (synCpw1 (.cv x)) (synCsn B) (synCsn (synCsn (.cv y)))
  have p0055 :=
    @gSylan2 (.classEq B (synCsn (.cv y))) (.classEq A (synCpw1 (.cv x)))
      (.classEq (synCsn B) (synCsn (synCsn (.cv y))))
      (.classEq (synCun A (synCsn B))
        (synCun (synCpw1 (.cv x)) (synCsn (synCsn (.cv y)))))
      p0053 p0054
  have p0056 :=
    @gEqeqan12d (.classEq C (synCun (.cv x) (synCsn (.cv y))))
      (synWa (.classEq A (synCpw1 (.cv x))) (.classEq B (synCsn (.cv y)))) (synCpw1 C)
      (synCpw1 (synCun (.cv x) (synCsn (.cv y)))) (synCun A (synCsn B))
      (synCun (synCpw1 (.cv x)) (synCsn (synCsn (.cv y)))) p0052 p0055
  have p0057 :=
    @gN3impb (.classEq C (synCun (.cv x) (synCsn (.cv y))))
      (.classEq A (synCpw1 (.cv x))) (.classEq B (synCsn (.cv y)))
      (synWb (.classEq (synCpw1 C) (synCun A (synCsn B)))
        (.classEq (synCpw1 (synCun (.cv x) (synCsn (.cv y))))
          (synCun (synCpw1 (.cv x)) (synCsn (synCsn (.cv y))))))
      p0056
  have p0058 :=
    @gMpbiri
      (synW3a (.classEq C (synCun (.cv x) (synCsn (.cv y))))
        (.classEq A (synCpw1 (.cv x))) (.classEq B (synCsn (.cv y))))
      (.classEq (synCpw1 C) (synCun A (synCsn B)))
      (.classEq (synCpw1 (synCun (.cv x) (synCsn (.cv y))))
        (synCun (synCpw1 (.cv x)) (synCsn (synCsn (.cv y)))))
      p0051 p0057
  have freeVariableCertificate3 :
    x ∉ ((Wff.classEq (synCpw1 C) (synCun A (synCsn B)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, dv_C_x,
      dv_A_x, dv_B_x, or_false, not_false_eq_true]
  have freeVariableCertificate4 :
    y ∉ ((Wff.classEq (synCpw1 C) (synCun A (synCsn B)))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, dv_C_y,
      dv_A_y, dv_B_y, or_false, not_false_eq_true]
  have p0059 :=
    @gExlimivv
      (synW3a (.classEq C (synCun (.cv x) (synCsn (.cv y))))
        (.classEq A (synCpw1 (.cv x))) (.classEq B (synCsn (.cv y))))
      (.classEq (synCpw1 C) (synCun A (synCsn B))) x y freeVariableCertificate3
      freeVariableCertificate4 p0058
  have p0060 :=
    @gImpbii (.classEq (synCpw1 C) (synCun A (synCsn B)))
      (synWex x (synWex y (synW3a (.classEq C (synCun (.cv x) (synCsn (.cv y))))
            (.classEq A (synCpw1 (.cv x))) (.classEq B (synCsn (.cv y))))))
      p0046 p0059
  exact p0060

/-- Checked nominal proof certificate identified upstream as `g_sspw1`. -/
@[expose]
noncomputable def gSspw1 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_sspw1_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (synWss A (synCpw1 B))
        (synWex x (synWa (synWss (.cv x) B) (.classEq A (synCpw1 (.cv x)))))) :=
  by
  have p0000 := @gUniss A (synCpw1 B)
  have p0001 := @gUnipw1 B
  have p0002 :=
    @gSyl6sseq (synWss A (synCpw1 B)) (synCuni A) (synCuni (synCpw1 B)) B p0000
      p0001
  have p0003 := @gPw1ss1c B
  have p0004 := @gSstr A (synCpw1 B) (synC1c)
  have p0005 :=
    @gMpan2 (synWss A (synCpw1 B)) (synWss (synCpw1 B) (synC1c))
      (synWss A (synC1c)) p0003 p0004
  have p0006 := @gEqpw1uni A
  have p0007 :=
    @gSyl (synWss A (synCpw1 B)) (synWss A (synC1c))
      (.classEq A (synCpw1 (synCuni A))) p0005 p0006
  have p0008 := @gUniex A hyp_sspw1_1
  have p0009 := @gSseq1 (.cv x) (synCuni A) B
  have p0010 := @gPw1eq (.cv x) (synCuni A)
  have p0011 :=
    @gEqeq2d (.classEq (.cv x) (synCuni A)) (synCpw1 (.cv x)) (synCpw1 (synCuni A)) A
      p0010
  have p0012 :=
    @gAnbi12d (.classEq (.cv x) (synCuni A)) (synWss (.cv x) B)
      (synWss (synCuni A) B) (.classEq A (synCpw1 (.cv x)))
      (.classEq A (synCpw1 (synCuni A))) p0009 p0011
  have freeVariableCertificate0 :
    x ∉ ((synWa (synWss (synCuni A) B) (.classEq A (synCpw1 (synCuni A))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, dv_A_x,
      dv_B_x, or_false, not_false_eq_true]
  have p0013 :=
    @gSpcev (synWa (synWss (.cv x) B) (.classEq A (synCpw1 (.cv x))))
      (synWa (synWss (synCuni A) B) (.classEq A (synCpw1 (synCuni A)))) x
      (synCuni A)
      (by
        exact
          (show x ∉ ((synCuni A)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni];
              exact (show x ∉ (A).fv from (by exact dv_A_x)))))
      freeVariableCertificate0 p0008 p0012
  have p0014 :=
    @gSyl2anc (synWss A (synCpw1 B)) (synWss (synCuni A) B)
      (.classEq A (synCpw1 (synCuni A)))
      (synWex x (synWa (synWss (.cv x) B) (.classEq A (synCpw1 (.cv x))))) p0002 p0007
      p0013
  have p0015 := @gPw1ss (.cv x) B
  have p0016 := @gSseq1 A (synCpw1 (.cv x)) (synCpw1 B)
  have p0017 :=
    @gSyl5ibr (synWss (.cv x) B) (synWss A (synCpw1 B))
      (.classEq A (synCpw1 (.cv x))) (synWss (synCpw1 (.cv x)) (synCpw1 B)) p0015
      p0016
  have p0018 :=
    @gImpcom (.classEq A (synCpw1 (.cv x))) (synWss (.cv x) B) (synWss A (synCpw1 B))
      p0017
  have freeVariableCertificate1 : x ∉ ((synWss A (synCpw1 B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union, dv_A_x,
      dv_B_x, or_false, not_false_eq_true]
  have p0019 :=
    @gExlimiv (synWa (synWss (.cv x) B) (.classEq A (synCpw1 (.cv x))))
      (synWss A (synCpw1 B)) x freeVariableCertificate1 p0018
  have p0020 :=
    @gImpbii (synWss A (synCpw1 B))
      (synWex x (synWa (synWss (.cv x) B) (.classEq A (synCpw1 (.cv x))))) p0014 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_dfiota2`. -/
@[expose]
noncomputable def gDfiota2 (ph : Wff) (x : Var) (y : Var) (dv_ph_y : y ∉ ph.fv)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCio x ph) (synCuni (.cab y (.all x (synWb ph (.objEq x y)))))) :=
  by
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIota ph x y
      (by exact (show y ∉ (ph).fv from (by exact dv_ph_y)))
      (show x ≠ y from (by exact dv_x_y))
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
      not_false_eq_true]
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn x (.cv y)
      freeVariableCertificate0
  have p0002_e00_recanon :
    Nominal.NPrf (.classEq (synCsn (.cv y)) (.cab x (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0001
  have p0002 :=
    @gEqeq2i (synCsn (.cv y)) (.cab x (.objEq x y)) (.cab x ph) p0002_e00_recanon
  have p0003 := @gAbbib ph (.objEq x y) x
  have p0004 :=
    @gBitri (.classEq (.cab x ph) (synCsn (.cv y)))
      (.classEq (.cab x ph) (.cab x (.objEq x y))) (.all x (synWb ph (.objEq x y))) p0002
      p0003
  have p0005 :=
    @gAbbii (.classEq (.cab x ph) (synCsn (.cv y))) (.all x (synWb ph (.objEq x y))) y
      p0004
  have p0006 :=
    @gUnieqi (.cab y (.classEq (.cab x ph) (synCsn (.cv y))))
      (.cab y (.all x (synWb ph (.objEq x y)))) p0005
  have p0007 :=
    @gEqtri (synCio x ph) (synCuni (.cab y (.classEq (.cab x ph) (synCsn (.cv y)))))
      (synCuni (.cab y (.all x (synWb ph (.objEq x y))))) p0000 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_nfiota1`. -/
@[expose]
noncomputable def gNfiota1 (ph : Wff) (x : Var) :
    Nominal.NPrf (synWnfc x (synCio x ph)) :=
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
    @gDfiota2 ph x y (by exact (show y ∉ (ph).fv from (by exact fresh_y_not_ph)))
      (show x ≠ y from (by exact fresh_x_ne_y))
  have p0001 := @gNfaba1 (synWb ph (.classEq (.cv x) (.cv y))) x y
  have p0002 := @gNfuni x (.cab y (.all x (synWb ph (.classEq (.cv x) (.cv y))))) p0001
  have p0003_e00_recanon :
    Nominal.NPrf
      (.classEq (synCio x ph)
        (synCuni (.cab y (.all x (synWb ph (.classEq (.cv x) (.cv y))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCio synCuni synWex synWa synCsn
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
    @gNfcxfr x (synCio x ph)
      (synCuni (.cab y (.all x (synWb ph (.classEq (.cv x) (.cv y))))))
      p0003_e00_recanon p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_iotabi`. -/
@[expose]
noncomputable def gIotabi (ph : Wff) (ps : Wff) (x : Var) :
    Nominal.NPrf
      (.imp (.all x (synWb ph ps)) (.classEq (synCio x ph) (synCio x ps))) :=
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
  have p0000 := @gAbbib ph ps x
  have p0001 :=
    @gBiimpri (.classEq (.cab x ph) (.cab x ps)) (.all x (synWb ph ps)) p0000
  have p0002 :=
    @gEqeq1d (.all x (synWb ph ps)) (.cab x ph) (.cab x ps) (synCsn (.cv z)) p0001
  have freeVariableCertificate0 : z ∉ ((Wff.all x (synWb ph ps))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb, Finset.mem_union,
      Finset.mem_erase, fresh_z_not_ph, fresh_z_not_ps, or_false, and_false,
      not_false_eq_true]
  have p0003 :=
    @gAbbidv (.all x (synWb ph ps)) (.classEq (.cab x ph) (synCsn (.cv z)))
      (.classEq (.cab x ps) (synCsn (.cv z))) z freeVariableCertificate0 p0002
  have p0004 :=
    @gUnieqd (.all x (synWb ph ps)) (.cab z (.classEq (.cab x ph) (synCsn (.cv z))))
      (.cab z (.classEq (.cab x ps) (synCsn (.cv z)))) p0003
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIota ph x z
      (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
      (show x ≠ z from (by exact fresh_x_ne_z))
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIota ps x z
      (by exact (show z ∉ (ps).fv from (by exact fresh_z_not_ps)))
      (show x ≠ z from (by exact fresh_x_ne_z))
  have p0007 :=
    @gN3eqtr4g (.all x (synWb ph ps))
      (synCuni (.cab z (.classEq (.cab x ph) (synCsn (.cv z)))))
      (synCuni (.cab z (.classEq (.cab x ps) (synCsn (.cv z))))) (synCio x ph)
      (synCio x ps) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_uniabio`. -/
@[expose]
noncomputable def gUniabio (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.all x (synWb ph (.objEq x y))) (.classEq (synCuni (.cab x ph)) (.cv y))) :=
  by
  have p0000 := @gAbbib ph (.objEq x y) x
  have p0001 :=
    @gBiimpri (.classEq (.cab x ph) (.cab x (.objEq x y)))
      (.all x (synWb ph (.objEq x y))) p0000
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
      not_false_eq_true]
  have p0002 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn x (.cv y)
      freeVariableCertificate0
  have p0003_e01_recanon :
    Nominal.NPrf (.classEq (synCsn (.cv y)) (.cab x (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.classEq
        · exact Nominal.RecanonTransportDev.TRecanonClass.same _
        · apply Nominal.RecanonTransportDev.TRecanonClass.cab
          exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0002
  have p0003 :=
    @gSyl6eqr (.all x (synWb ph (.objEq x y))) (.cab x ph) (.cab x (.objEq x y))
      (synCsn (.cv y)) p0001 p0003_e01_recanon
  have p0004 :=
    @gUnieqd (.all x (synWb ph (.objEq x y))) (.cab x ph) (synCsn (.cv y)) p0003
  have p0005 := @gVex y
  have p0006 := @gUnisn (.cv y) p0005
  have p0007 :=
    @gSyl6eq (.all x (synWb ph (.objEq x y))) (synCuni (.cab x ph))
      (synCuni (synCsn (.cv y))) (.cv y) p0004 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_iotaval`. -/
@[expose]
noncomputable def gIotaval (ph : Wff) (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.all x (synWb ph (.classEq (.cv x) (.cv y))))
        (.classEq (synCio x ph) (.cv y))) :=
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
    @gDfiota2 ph x z (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
      (show x ≠ z from (by exact fresh_x_ne_z))
  have p0001 := @gVex y
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
      not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((Class.cv z)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_z, not_false_eq_true]
  have p0002 :=
    @gSbeqalb ph x (.cv y) (.cv z) (synCvv) freeVariableCertificate0
      freeVariableCertificate1
  have p0003 := @gEqucomi y z
  have p0004_e01_recanon :
    Nominal.NPrf (.imp (.classEq (.cv y) (.cv z)) (.classEq (.cv z) (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0003
  have p0004 :=
    @gSyl6 (.classMem (.cv y) (synCvv))
      (synWa (.all x (synWb ph (.classEq (.cv x) (.cv y))))
        (.all x (synWb ph (.classEq (.cv x) (.cv z)))))
      (.classEq (.cv y) (.cv z)) (.classEq (.cv z) (.cv y)) p0002 p0004_e01_recanon
  have p0005 := Nominal.mp p0001 p0004
  have p0006 :=
    @gEx (.all x (synWb ph (.classEq (.cv x) (.cv y))))
      (.all x (synWb ph (.classEq (.cv x) (.cv z)))) (.classEq (.cv z) (.cv y)) p0005
  have p0007 := @gEquequ2 y z x
  have p0008_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv z))
        (synWb (.classEq (.cv x) (.cv y)) (.classEq (.cv x) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gEqcoms (synWb (.classEq (.cv x) (.cv y)) (.classEq (.cv x) (.cv z))) (.cv y)
      (.cv z) p0008_e00_recanon
  have p0009 :=
    @gBibi2d (.classEq (.cv z) (.cv y)) (.classEq (.cv x) (.cv y))
      (.classEq (.cv x) (.cv z)) ph p0008
  have p0010 :=
    @gBiimpd (.classEq (.cv z) (.cv y)) (synWb ph (.classEq (.cv x) (.cv y)))
      (synWb ph (.classEq (.cv x) (.cv z))) p0009
  have freeVariableCertificate2 : x ∉ ((Wff.classEq (.cv z) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_x_ne_z, dv_x_y, or_false, not_false_eq_true]
  have p0011 :=
    @gAlimdv (.classEq (.cv z) (.cv y)) (synWb ph (.classEq (.cv x) (.cv y)))
      (synWb ph (.classEq (.cv x) (.cv z))) x freeVariableCertificate2 p0010
  have p0012 :=
    @gCom12 (.classEq (.cv z) (.cv y)) (.all x (synWb ph (.classEq (.cv x) (.cv y))))
      (.all x (synWb ph (.classEq (.cv x) (.cv z)))) p0011
  have p0013 :=
    @gImpbid (.all x (synWb ph (.classEq (.cv x) (.cv y))))
      (.all x (synWb ph (.classEq (.cv x) (.cv z)))) (.classEq (.cv z) (.cv y)) p0006
      p0012
  have freeVariableCertificate3 :
    z ∉ ((Wff.all x (synWb ph (.classEq (.cv x) (.cv y))))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x, fresh_z_ne_y, or_false,
      and_false, not_false_eq_true]
  have p0014 :=
    @gAlrimiv (.all x (synWb ph (.classEq (.cv x) (.cv y))))
      (synWb (.all x (synWb ph (.classEq (.cv x) (.cv z)))) (.classEq (.cv z) (.cv y)))
      z freeVariableCertificate3 p0013
  have p0015 :=
    @gUniabio (.all x (synWb ph (.classEq (.cv x) (.cv z)))) z y
      (show z ≠ y from (by exact fresh_z_ne_y))
  have p0016_e01_recanon :
    Nominal.NPrf
      (.imp (.all z (synWb (.all x (synWb ph (.classEq (.cv x) (.cv z))))
            (.classEq (.cv z) (.cv y))))
        (.classEq (synCuni (.cab z (.all x (synWb ph (.classEq (.cv x) (.cv z))))))
          (.cv y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCuni synWex synWa
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
    @gSyl (.all x (synWb ph (.classEq (.cv x) (.cv y))))
      (.all z (synWb (.all x (synWb ph (.classEq (.cv x) (.cv z))))
          (.classEq (.cv z) (.cv y))))
      (.classEq (synCuni (.cab z (.all x (synWb ph (.classEq (.cv x) (.cv z)))))) (.cv y))
      p0014 p0016_e01_recanon
  have p0017_e00_recanon :
    Nominal.NPrf
      (.classEq (synCio x ph)
        (synCuni (.cab z (.all x (synWb ph (.classEq (.cv x) (.cv z))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCio synCuni synWex synWa synCsn
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
    @gSyl5eq (.all x (synWb ph (.classEq (.cv x) (.cv y)))) (synCio x ph)
      (synCuni (.cab z (.all x (synWb ph (.classEq (.cv x) (.cv z)))))) (.cv y)
      p0017_e00_recanon p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_iota1`. -/
@[expose]
noncomputable def gIota1 (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWeu x ph) (synWb ph (.classEq (synCio x ph) (.cv x)))) :=
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
  have p0001 := @gSp (synWb ph (.classEq (.cv x) (.cv z))) x
  have p0002 := @gIotaval ph x z (show x ≠ z from (by exact fresh_x_ne_z))
  have p0003 :=
    @gEqeq2d (.all x (synWb ph (.classEq (.cv x) (.cv z)))) (synCio x ph) (.cv z)
      (.cv x) p0002
  have p0004 :=
    @gBitr4d (.all x (synWb ph (.classEq (.cv x) (.cv z)))) ph
      (.classEq (.cv x) (.cv z)) (.classEq (.cv x) (synCio x ph)) p0001 p0003
  have p0005 := @gEqcom (.cv x) (synCio x ph)
  have p0006 :=
    @gSyl6bb (.all x (synWb ph (.classEq (.cv x) (.cv z)))) ph
      (.classEq (.cv x) (synCio x ph)) (.classEq (synCio x ph) (.cv x)) p0004 p0005
  have freeVariableCertificate0 :
    z ∉ ((synWb ph (.classEq (synCio x ph) (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
      Finset.mem_singleton, fresh_z_not_ph, fresh_z_ne_x, or_false, and_false,
      not_false_eq_true]
  have p0007 :=
    @gExlimiv (.all x (synWb ph (.classEq (.cv x) (.cv z))))
      (synWb ph (.classEq (synCio x ph) (.cv x))) z freeVariableCertificate0 p0006
  have p0008_e00_recanon :
    Nominal.NPrf
      (synWb (synWeu x ph) (synWex z (.all x (synWb ph (.classEq (.cv x) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex
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
    @gSylbi (synWeu x ph) (synWex z (.all x (synWb ph (.classEq (.cv x) (.cv z)))))
      (synWb ph (.classEq (synCio x ph) (.cv x))) p0008_e00_recanon p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_iotanul`. -/
@[expose]
noncomputable def gIotanul (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (.neg (synWeu x ph)) (.classEq (synCio x ph) (synC0))) :=
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
    @gDfiota2 ph x z (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
      (show x ≠ z from (by exact fresh_x_ne_z))
  have p0002 := @gAlnex (.all x (synWb ph (.objEq x z))) z
  have p0003 := Nominal.ax1 (.neg (.all x (synWb ph (.objEq x z)))) (.objEq z z)
  have p0004 := @gEqidd (.neg (.all x (synWb ph (.objEq x z)))) (.cv z)
  have p0005_e01_recanon :
    Nominal.NPrf (.imp (.neg (.all x (synWb ph (.objEq x z)))) (.objEq z z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0004
  have p0005 :=
    @gImpbid1 (.neg (.all x (synWb ph (.objEq x z)))) (.objEq z z)
      (.neg (.all x (synWb ph (.objEq x z)))) p0003 p0005_e01_recanon
  have p0006 :=
    @gCon2bid (.neg (.all x (synWb ph (.objEq x z)))) (.objEq z z)
      (.all x (synWb ph (.objEq x z))) p0005
  have p0007 :=
    @gAlimi (.neg (.all x (synWb ph (.objEq x z))))
      (synWb (.all x (synWb ph (.objEq x z))) (.neg (.objEq z z))) z p0006
  have p0008 := @gAbbib (.all x (synWb ph (.objEq x z))) (.neg (.objEq z z)) z
  have p0009 :=
    @gSylibr (.all z (.neg (.all x (synWb ph (.objEq x z)))))
      (.all z (synWb (.all x (synWb ph (.objEq x z))) (.neg (.objEq z z))))
      (.classEq (.cab z (.all x (synWb ph (.objEq x z)))) (.cab z (.neg (.objEq z z))))
      p0007 p0008
  have p0010 := @gDfnul2 z
  have p0011_e01_recanon :
    Nominal.NPrf (.classEq (synC0) (.cab z (.neg (.objEq z z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synC0 synCdif synCin synCcompl synCnin synWnan synWa synCvv
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
    @gSyl6eqr (.all z (.neg (.all x (synWb ph (.objEq x z)))))
      (.cab z (.all x (synWb ph (.objEq x z)))) (.cab z (.neg (.objEq z z))) (synC0)
      p0009 p0011_e01_recanon
  have p0012 :=
    @gSylbir (.neg (synWex z (.all x (synWb ph (.objEq x z)))))
      (.all z (.neg (.all x (synWb ph (.objEq x z)))))
      (.classEq (.cab z (.all x (synWb ph (.objEq x z)))) (synC0)) p0002 p0011
  have p0013 :=
    @gUnieqd (.neg (synWex z (.all x (synWb ph (.objEq x z)))))
      (.cab z (.all x (synWb ph (.objEq x z)))) (synC0) p0012
  have p0014 := @gUni0
  have p0015 :=
    @gSyl6eq (.neg (synWex z (.all x (synWb ph (.objEq x z)))))
      (synCuni (.cab z (.all x (synWb ph (.objEq x z))))) (synCuni (synC0)) (synC0)
      p0013 p0014
  have p0016 :=
    @gSyl5eq (.neg (synWex z (.all x (synWb ph (.objEq x z))))) (synCio x ph)
      (synCuni (.cab z (.all x (synWb ph (.objEq x z))))) (synC0) p0001 p0015
  have p0017 :=
    @gSylnbi (synWeu x ph) (synWex z (.all x (synWb ph (.objEq x z))))
      (.classEq (synCio x ph) (synC0)) p0000 p0016
  exact p0017

/-- Checked nominal proof certificate identified upstream as `g_iotaex`. -/
@[expose]
noncomputable def gIotaex (ph : Wff) (x : Var) :
    Nominal.NPrf (.classMem (synCio x ph) (synCvv)) :=
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
  have p0000 := @gIotaval ph x z (show x ≠ z from (by exact fresh_x_ne_z))
  have p0001 :=
    @gEqcomd (.all x (synWb ph (.classEq (.cv x) (.cv z)))) (synCio x ph) (.cv z) p0000
  have p0002 :=
    @gEximi (.all x (synWb ph (.classEq (.cv x) (.cv z))))
      (.classEq (.cv z) (synCio x ph)) z p0001
  have p0003 :=
    Nominal.dfEu x z ph (show x ≠ z from (by exact fresh_x_ne_z))
      (by exact (show z ∉ (ph).fv from (by exact fresh_z_not_ph)))
  have freeVariableCertificate0 : z ∉ ((synCio x ph)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio, Finset.mem_erase,
      fresh_z_not_ph, and_false, not_false_eq_true]
  have p0004 := @gIsset z (synCio x ph) freeVariableCertificate0
  have p0005_e01_recanon :
    Nominal.NPrf
      (synWb (synWeu x ph) (synWex z (.all x (synWb ph (.classEq (.cv x) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWeu synWex
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
    @gN3imtr4i (synWex z (.all x (synWb ph (.classEq (.cv x) (.cv z)))))
      (synWex z (.classEq (.cv z) (synCio x ph))) (synWeu x ph)
      (.classMem (synCio x ph) (synCvv)) p0002 p0005_e01_recanon p0004
  have p0006 := @gIotanul ph x
  have p0007 := @gN0ex
  have p0008 :=
    @gSyl6eqel (.neg (synWeu x ph)) (synCio x ph) (synC0) (synCvv) p0006 p0007
  have p0009 := @gPm261i (synWeu x ph) (.classMem (synCio x ph) (synCvv)) p0005 p0008
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

/-- Checked nominal proof certificate identified upstream as `g_iota4`. -/
@[expose]
noncomputable def gIota4 (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWeu x ph) (synWsbc (synCio x ph) x ph)) :=
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
  have p0001 := @gBi2 ph (.objEq x z)
  have p0002 := @gAlimi (synWb ph (.objEq x z)) (.imp (.objEq x z) ph) x p0001
  have p0003 := @gSb2 ph x z
  have p0004 :=
    @gSyl (.all x (synWb ph (.objEq x z))) (.all x (.imp (.objEq x z) ph))
      (synWsb z x ph) p0002 p0003
  have p0005 := @gIotaval ph x z (show x ≠ z from (by exact fresh_x_ne_z))
  have p0006_e00_recanon :
    Nominal.NPrf
      (.imp (.all x (synWb ph (.objEq x z))) (.classEq (synCio x ph) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCio synCuni synWex synWa synCsn
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
    @gEqcomd (.all x (synWb ph (.objEq x z))) (synCio x ph) (.cv z) p0006_e00_recanon
  have p0007 := @gDfsbcq2 ph x z (synCio x ph)
  have p0008 :=
    @gSyl (.all x (synWb ph (.objEq x z))) (.classEq (.cv z) (synCio x ph))
      (synWb (synWsb z x ph) (synWsbc (synCio x ph) x ph)) p0006 p0007
  have p0009 :=
    @gMpbid (.all x (synWb ph (.objEq x z))) (synWsb z x ph)
      (synWsbc (synCio x ph) x ph) p0004 p0008
  have freeVariableCertificate0 : z ∉ ((synWsbc (synCio x ph) x ph)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsbc,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cio, Finset.mem_union,
      Finset.mem_erase, fresh_z_not_ph, or_false, and_false, not_false_eq_true]
  have p0010 :=
    @gExlimiv (.all x (synWb ph (.objEq x z))) (synWsbc (synCio x ph) x ph) z
      freeVariableCertificate0 p0009
  have p0011 :=
    @gSylbi (synWeu x ph) (synWex z (.all x (synWb ph (.objEq x z))))
      (synWsbc (synCio x ph) x ph) p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_iotabidv`. -/
@[expose]
noncomputable def gIotabidv (ph : Wff) (ps : Wff) (ch : Wff) (x : Var)
    (dv_ph_x : x ∉ ph.fv) (hyp_iotabidv_1 : Nominal.NPrf (.imp ph (synWb ps ch))) :
    Nominal.NPrf (.imp ph (.classEq (synCio x ps) (synCio x ch))) :=
  by
  have p0000 :=
    @gAlrimiv ph (synWb ps ch) x (by exact (show x ∉ (ph).fv from (by exact dv_ph_x)))
      hyp_iotabidv_1
  have p0001 := @gIotabi ps ch x
  have p0002 :=
    @gSyl ph (.all x (synWb ps ch)) (.classEq (synCio x ps) (synCio x ch)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_iotacl`. -/
@[expose]
noncomputable def gIotacl (ph : Wff) (x : Var) :
    Nominal.NPrf (.imp (synWeu x ph) (.classMem (synCio x ph) (.cab x ph))) :=
  by
  have p0000 := @gIota4 ph x
  have p0001 := (Nominal.biimpRefl (synWsbc (synCio x ph) x ph))
  have p0002 :=
    @gSylib (synWeu x ph) (synWsbc (synCio x ph) x ph)
      (.classMem (synCio x ph) (.cab x ph)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_reiotacl2`. -/
@[expose]
noncomputable def gReiotacl2 (ph : Wff) (x : Var) (A : Class) :
    Nominal.NPrf
      (.imp (synWreu x A ph)
        (.classMem (synCio x (synWa (.classMem (.cv x) A) ph)) (synCrab x A ph))) :=
  by
  have p0000 := (Nominal.biimpRefl (synWreu x A ph))
  have p0001 := @gIotacl (synWa (.classMem (.cv x) A) ph) x
  have p0002 :=
    @gSylbi (synWreu x A ph) (synWeu x (synWa (.classMem (.cv x) A) ph))
      (.classMem (synCio x (synWa (.classMem (.cv x) A) ph))
        (.cab x (synWa (.classMem (.cv x) A) ph)))
      p0000 p0001
  have p0003 := (Nominal.classEqRefl (synCrab x A ph))
  have p0004 :=
    @gSyl6eleqr (synWreu x A ph) (synCio x (synWa (.classMem (.cv x) A) ph))
      (.cab x (synWa (.classMem (.cv x) A) ph)) (synCrab x A ph) p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_reiotacl`. -/
@[expose]
noncomputable def gReiotacl (ph : Wff) (x : Var) (A : Class) (dv_A_x : x ∉ A.fv) :
    Nominal.NPrf
      (.imp (synWreu x A ph) (.classMem (synCio x (synWa (.classMem (.cv x) A) ph)) A)) :=
  by
  have p0000 := @gSsrab2 ph x A (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
  have p0001 := @gA1i (synWss (synCrab x A ph) A) (synWreu x A ph) p0000
  have p0002 := @gReiotacl2 ph x A
  have p0003 :=
    @gSseldd (synWreu x A ph) (synCrab x A ph) A
      (synCio x (synWa (.classMem (.cv x) A) ph)) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_iota2df`. -/
@[expose]
noncomputable def gIota2df (ph : Wff) (ps : Wff) (ch : Wff) (x : Var) (B : Class)
    (V : Class) (hyp_iota2df_1 : Nominal.NPrf (.imp ph (.classMem B V)))
    (hyp_iota2df_2 : Nominal.NPrf (.imp ph (synWeu x ps)))
    (hyp_iota2df_3 : Nominal.NPrf (.imp (synWa ph (.classEq (.cv x) B)) (synWb ps ch)))
    (hyp_iota2df_4 : Nominal.NPrf (synWnf x ph))
    (hyp_iota2df_5 : Nominal.NPrf (.imp ph (synWnf x ch)))
    (hyp_iota2df_6 : Nominal.NPrf (.imp ph (synWnfc x B))) :
    Nominal.NPrf (.imp ph (synWb ch (.classEq (synCio x ps) B))) :=
  by
  have p0000 := @gNfiota1 ps x
  have p0001 := @gA1i (synWnfc x (synCio x ps)) ph p0000
  have p0002 := @gNfeqd ph x (synCio x ps) B p0001 hyp_iota2df_6
  have p0003 := @gNfbid ph ch (.classEq (synCio x ps) B) x hyp_iota2df_5 p0002
  have p0004 := @gSimpr ph (.classEq (.cv x) B)
  have p0005 := @gEqeq2d (synWa ph (.classEq (.cv x) B)) (.cv x) B (synCio x ps) p0004
  have p0006 :=
    @gBibi12d (synWa ph (.classEq (.cv x) B)) ps ch (.classEq (synCio x ps) (.cv x))
      (.classEq (synCio x ps) B) hyp_iota2df_3 p0005
  have p0007 :=
    @gEx ph (.classEq (.cv x) B)
      (synWb (synWb ps (.classEq (synCio x ps) (.cv x)))
        (synWb ch (.classEq (synCio x ps) B)))
      p0006
  have p0008 :=
    @gAlrimi ph
      (.imp (.classEq (.cv x) B) (synWb (synWb ps (.classEq (synCio x ps) (.cv x)))
          (synWb ch (.classEq (synCio x ps) B))))
      x hyp_iota2df_4 p0007
  have p0009 := @gIota1 ps x
  have p0010 :=
    @gSyl ph (synWeu x ps) (synWb ps (.classEq (synCio x ps) (.cv x))) hyp_iota2df_2
      p0009
  have p0011 :=
    @gAlrimi ph (synWb ps (.classEq (synCio x ps) (.cv x))) x hyp_iota2df_4 p0010
  have p0012 :=
    @gVtoclgft (synWb ps (.classEq (synCio x ps) (.cv x)))
      (synWb ch (.classEq (synCio x ps) B)) x B V
  have p0013 :=
    @gSyl221anc ph (synWnfc x B) (synWnf x (synWb ch (.classEq (synCio x ps) B)))
      (.all x (.imp (.classEq (.cv x) B) (synWb (synWb ps (.classEq (synCio x ps) (.cv x)))
            (synWb ch (.classEq (synCio x ps) B)))))
      (.all x (synWb ps (.classEq (synCio x ps) (.cv x)))) (.classMem B V)
      (synWb ch (.classEq (synCio x ps) B)) hyp_iota2df_6 p0003 p0008 p0011
      hyp_iota2df_1 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_iota2`. -/
@[expose]
noncomputable def gIota2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_iota2_1 : Nominal.NPrf (.imp (.classEq (.cv x) A) (synWb ph ps))) :
    Nominal.NPrf
      (.imp (synWa (.classMem A B) (synWeu x ph)) (synWb ps (.classEq (synCio x ph) A))) :=
  by
  have p0000 := @gElex A B
  have p0001 := @gSimpl (.classMem A (synCvv)) (synWeu x ph)
  have p0002 := @gSimpr (.classMem A (synCvv)) (synWeu x ph)
  have p0003 :=
    @gAdantl (.classEq (.cv x) A) (synWb ph ps)
      (synWa (.classMem A (synCvv)) (synWeu x ph)) hyp_iota2_1
  have freeVariableCertificate0 : x ∉ ((Wff.classMem A (synCvv))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
      Finset.notMem_empty, dv_A_x, or_false, not_false_eq_true]
  have p0004 := @gNfv (.classMem A (synCvv)) x freeVariableCertificate0
  have p0005 := @gNfeu1 ph x
  have p0006 := @gNfan (.classMem A (synCvv)) (synWeu x ph) x p0004 p0005
  have p0007 :=
    @gNfvd (synWa (.classMem A (synCvv)) (synWeu x ph)) ps x
      (by exact (show x ∉ (ps).fv from (by exact dv_ps_x)))
  have p0008 :=
    @gNfcvd (synWa (.classMem A (synCvv)) (synWeu x ph)) x A
      (by exact (show x ∉ (A).fv from (by exact dv_A_x)))
  have p0009 :=
    @gIota2df (synWa (.classMem A (synCvv)) (synWeu x ph)) ph ps x A (synCvv) p0001
      p0002 p0003 p0006 p0007 p0008
  have p0010 :=
    @gSylan (.classMem A B) (.classMem A (synCvv)) (synWeu x ph)
      (synWb ps (.classEq (synCio x ph) A)) p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_reiota2`. -/
@[expose]
noncomputable def gReiota2 (ph : Wff) (ps : Wff) (x : Var) (A : Class) (B : Class)
    (dv_A_x : x ∉ A.fv) (dv_B_x : x ∉ B.fv) (dv_ps_x : x ∉ ps.fv)
    (hyp_reiota2_1 : Nominal.NPrf (.imp (.classEq (.cv x) B) (synWb ph ps))) :
    Nominal.NPrf
      (.imp (synWa (.classMem B A) (synWreu x A ph))
        (synWb ps (.classEq (synCio x (synWa (.classMem (.cv x) A) ph)) B))) :=
  by
  have p0000 := @gSimpl (.classMem B A) (synWreu x A ph)
  have p0001 :=
    @gBiantrurd (synWa (.classMem B A) (synWreu x A ph)) (.classMem B A) ps p0000
  have p0002 := (Nominal.biimpRefl (synWreu x A ph))
  have p0003 := @gEleq1 (.cv x) B A
  have p0004 :=
    @gAnbi12d (.classEq (.cv x) B) (.classMem (.cv x) A) (.classMem B A) ph ps p0003
      hyp_reiota2_1
  have freeVariableCertificate0 : x ∉ ((synWa (.classMem B A) ps)).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
      NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union, dv_B_x, dv_A_x,
      dv_ps_x, or_false, not_false_eq_true]
  have p0005 :=
    @gIota2 (synWa (.classMem (.cv x) A) ph) (synWa (.classMem B A) ps) x B A
      (by exact (show x ∉ (B).fv from (by exact dv_B_x))) freeVariableCertificate0 p0004
  have p0006 :=
    @gSylan2b (synWreu x A ph) (.classMem B A)
      (synWeu x (synWa (.classMem (.cv x) A) ph))
      (synWb (synWa (.classMem B A) ps)
        (.classEq (synCio x (synWa (.classMem (.cv x) A) ph)) B))
      p0002 p0005
  have p0007 :=
    @gBitrd (synWa (.classMem B A) (synWreu x A ph)) ps (synWa (.classMem B A) ps)
      (.classEq (synCio x (synWa (.classMem (.cv x) A) ph)) B) p0001 p0006
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

/-- Checked nominal proof certificate identified upstream as `g_dfaddc2`. -/
@[expose]
noncomputable def gDfaddc2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCplc A B) (synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAddc x y z A B
      (by exact (show x ∉ (A).fv from (by exact fresh_x_not_A)))
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A)))
      (by exact (show z ∉ (A).fv from (by exact fresh_z_not_A)))
      (by exact (show x ∉ (B).fv from (by exact fresh_x_not_B)))
      (by exact (show y ∉ (B).fv from (by exact fresh_y_not_B)))
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
      (show x ≠ y from (by exact fresh_x_ne_y)) (show x ≠ z from (by exact fresh_x_ne_z))
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 := @gVex x
  have freeVariableCertificate0 :
    y ∉
      ((synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 B)))).fv :=
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
    @gElimak y
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
      A (.cv x) freeVariableCertificate0
      (by exact (show y ∉ (A).fv from (by exact fresh_y_not_A))) freeVariableCertificate1
      p0001
  have p0003 := @gOpkex (.cv y) (.cv x)
  have freeVariableCertificate2 :
    t ∉
      ((synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
  have freeVariableCertificate3 : t ∉ ((synCpw1 (synCpw1 B))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_t_not_B,
      not_false_eq_true]
  have freeVariableCertificate4 : t ∉ ((synCopk (.cv y) (.cv x))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_y, fresh_t_ne_x, or_false, not_false_eq_true]
  have p0004 :=
    @gElimak t
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 B)) (synCopk (.cv y) (.cv x)) freeVariableCertificate2
      freeVariableCertificate3 freeVariableCertificate4 p0003
  have freeVariableCertificate5 : z ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_t, not_false_eq_true]
  have p0005 :=
    @gElpw12 z (.cv t) B freeVariableCertificate5
      (by exact (show z ∉ (B).fv from (by exact fresh_z_not_B)))
  have p0006 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 B)))
      (synWrex z B (.classEq (.cv t) (synCsn (synCsn (.cv z)))))
      (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0005
  have freeVariableCertificate6 :
    z ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
              (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
    @gR1941v (.classEq (.cv t) (synCsn (synCsn (.cv z))))
      (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      z B freeVariableCertificate6
  have p0008 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 B)))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
              (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (synWrex z B (.classEq (.cv t) (synCsn (synCsn (.cv z)))))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
              (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWrex z B (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
          (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      p0006 p0007
  have p0009 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 B)))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
              (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWrex z B (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
          (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      t p0008
  have p0010 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 B))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
              (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
  have p0011 :=
    @gRexcom4
      (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
              (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      z t B (by exact (show t ∉ (B).fv from (by exact fresh_t_not_B)))
      (show z ≠ t from (by exact fresh_z_ne_t))
  have p0012 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 B)))
          (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex t (synWrex z B (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
            (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
                  (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWrex t (synCpw1 (synCpw1 B))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
              (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWrex z B (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
            (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
                  (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0009 p0010 p0011
  have p0013 := @gSnex (synCsn (.cv z))
  have p0014 := @gOpkeq1 (.cv t) (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))
  have p0015 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv z))))
      (synCopk (.cv t) (synCopk (.cv y) (.cv x)))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0014
  have freeVariableCertificate7 : t ∉ ((synCsn (synCsn (.cv z)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_z,
      not_false_eq_true]
  have freeVariableCertificate8 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) (synCdif
            (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) (synCdif
          (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      t (synCsn (synCsn (.cv z))) freeVariableCertificate7 freeVariableCertificate8
      p0013 p0015
  have p0017 :=
    @gEldif (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
      (synCins3k (synCcompl
          (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
          (synCun (synCins2k (synCins3k (synCssetk)))
            (synCins3k (synCsik (synCsik (synCssetk))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  have p0018 := @gOpkex (.cv z) (.cv y)
  have p0019 :=
    @gElcompl (synCopk (.cv z) (.cv y))
      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0018
  have p0020 := @gVex z
  have p0021 := @gVex y
  have p0022 := @gNdisjrelk (.cv z) (.cv y) p0020 p0021
  have p0023 :=
    @gNecon2bbii
      (.classMem (synCopk (.cv z) (.cv y))
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCin (.cv z) (.cv y)) (synC0) p0022
  have p0024 :=
    @gBitr4i
      (.classMem (synCopk (.cv z) (.cv y)) (synCcompl
          (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.neg (.classMem (synCopk (.cv z) (.cv y))
          (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (synCin (.cv z) (.cv y)) (synC0)) p0019 p0023
  have p0025 :=
    @gOtkelins3k (.cv z) (.cv y) (.cv x)
      (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      p0020 p0021 p0001
  have p0026 := @gIncom (.cv y) (.cv z)
  have p0027 :=
    @gEqeq1i (synCin (.cv y) (.cv z)) (synCin (.cv z) (.cv y)) (synC0) p0026
  have p0028 :=
    @gN3bitr4i
      (.classMem (synCopk (.cv z) (.cv y)) (synCcompl
          (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (synCin (.cv z) (.cv y)) (synC0))
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) (synCins3k
          (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classEq (synCin (.cv y) (.cv z)) (synC0)) p0024 p0025 p0027
  have freeVariableCertificate9 : w ∉ ((Class.cv x)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_x, not_false_eq_true]
  have freeVariableCertificate10 : w ∉ ((synCun (.cv y) (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true]
  have p0029 :=
    @gDfcleq w (.cv x) (synCun (.cv y) (.cv z)) freeVariableCertificate9
      freeVariableCertificate10
  have p0030 := @gOpkex (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))
  have freeVariableCertificate11 :
    t ∉
      ((synCsymdif (synCins2k (synCins2k (synCssetk)))
          (synCun (synCins2k (synCins3k (synCssetk)))
            (synCins3k (synCsik (synCsik (synCssetk))))))).fv :=
    by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik, Finset.mem_union,
      Finset.notMem_empty, or_false, not_false_eq_true]
  have freeVariableCertificate12 :
    t ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.notMem_empty,
      not_false_eq_true]
  have freeVariableCertificate13 :
    t ∉ ((synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      fresh_t_ne_z, fresh_t_ne_y, fresh_t_ne_x, or_false, not_false_eq_true]
  have p0031 :=
    @gElimak t
      (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk)))
          (synCins3k (synCsik (synCsik (synCssetk))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
      freeVariableCertificate11 freeVariableCertificate12 freeVariableCertificate13 p0030
  have p0032 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk)))))))))
  have freeVariableCertificate14 : w ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_t, not_false_eq_true]
  have p0033 := @gElpw141c w (.cv t) freeVariableCertificate14
  have p0034 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWex w (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))))
      (.classMem (synCopk (.cv t)
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCsymdif (synCins2k (synCins2k (synCssetk)))
          (synCun (synCins2k (synCins3k (synCssetk)))
            (synCins3k (synCsik (synCsik (synCssetk)))))))
      p0033
  have freeVariableCertificate15 :
    w ∉
      ((Wff.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk)))))))).fv :=
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
    @gN1941v
      (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
      (.classMem (synCopk (.cv t)
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCsymdif (synCins2k (synCins2k (synCssetk)))
          (synCun (synCins2k (synCins3k (synCssetk)))
            (synCins3k (synCsik (synCsik (synCssetk)))))))
      w freeVariableCertificate15
  have p0036 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
        (.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))))
      (synWa (synWex w
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))))
        (.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))))
      (synWex w (synWa
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
          (.classMem (synCopk (.cv t)
              (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk)))))))))
      p0034 p0035
  have p0037 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
        (.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))))
      (synWex w (synWa
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
          (.classMem (synCopk (.cv t)
              (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk)))))))))
      t p0036
  have p0038 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
        (.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))))
      w t
  have p0039 :=
    @gBitr4i
      (synWex t
        (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
          (.classMem (synCopk (.cv t)
              (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk)))))))))
      (synWex t (synWex w (synWa
            (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
            (.classMem (synCopk (.cv t)
                (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))))))
      (synWex w (synWex t (synWa
            (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
            (.classMem (synCopk (.cv t)
                (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))))))
      p0037 p0038
  have p0040 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) (.classMem
          (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))))
      (synWex t
        (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
          (.classMem (synCopk (.cv t)
              (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk)))))))))
      (synWex w (synWex t (synWa
            (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
            (.classMem (synCopk (.cv t)
                (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))))))
      p0031 p0032 p0039
  have p0041 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv w)))))
  have p0042 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
  have p0043 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
      (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
      (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
        (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
      (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk)))
          (synCins3k (synCsik (synCsik (synCssetk))))))
      p0042
  have freeVariableCertificate16 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_w,
      not_false_eq_true]
  have freeVariableCertificate17 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk)))))))).fv :=
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
    @gCeqsexv
      (.classMem (synCopk (.cv t)
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCsymdif (synCins2k (synCins2k (synCssetk)))
          (synCun (synCins2k (synCins3k (synCssetk)))
            (synCins3k (synCsik (synCsik (synCssetk)))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCsymdif (synCins2k (synCins2k (synCssetk)))
          (synCun (synCins2k (synCins3k (synCssetk)))
            (synCins3k (synCsik (synCsik (synCssetk)))))))
      t (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
      freeVariableCertificate16 freeVariableCertificate17 p0041 p0043
  have p0045 :=
    @gElsymdif
      (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
        (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
      (synCins2k (synCins2k (synCssetk)))
      (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))
  have p0046 := @gSnex (synCsn (synCsn (.cv w)))
  have p0047 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (.cv w)))) (synCsn (synCsn (.cv z)))
      (synCopk (.cv y) (.cv x)) (synCins2k (synCssetk)) p0046 p0013 p0003
  have p0048 := @gSnex (.cv w)
  have p0049 :=
    @gOtkelins2k (synCsn (.cv w)) (.cv y) (.cv x) (synCssetk) p0048 p0021 p0001
  have p0050 := @gVex w
  have p0051 := @gElssetk (.cv w) (.cv x) p0050 p0001
  have p0052_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv w)) (.cv x)) (synCssetk)) (.objMem w x)) :=
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
      p0051
  have p0052 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCins2k (synCins2k (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv w)))) (synCopk (.cv y) (.cv x)))
        (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv w)) (.cv x)) (synCssetk)) (.objMem w x) p0047
      p0049 p0052_e02_recanon
  have p0053 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (.cv w)))) (synCsn (synCsn (.cv z)))
      (synCopk (.cv y) (.cv x)) (synCins3k (synCssetk)) p0046 p0013 p0003
  have p0054 :=
    @gOtkelins3k (synCsn (.cv w)) (.cv y) (.cv x) (synCssetk) p0048 p0021 p0001
  have p0055 := @gElssetk (.cv w) (.cv y) p0050 p0021
  have p0056_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv w)) (.cv y)) (synCssetk)) (.objMem w y)) :=
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
      p0055
  have p0056 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCins2k (synCins3k (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv w)))) (synCopk (.cv y) (.cv x)))
        (synCins3k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv w)) (.cv y)) (synCssetk)) (.objMem w y) p0053
      p0054 p0056_e02_recanon
  have p0057 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (.cv w)))) (synCsn (synCsn (.cv z)))
      (synCopk (.cv y) (.cv x)) (synCsik (synCsik (synCssetk))) p0046 p0013 p0003
  have p0058 := @gSnex (synCsn (.cv w))
  have p0059 := @gSnex (.cv z)
  have p0060 :=
    @gOpksnelsik (synCsn (synCsn (.cv w))) (synCsn (.cv z)) (synCsik (synCssetk))
      p0058 p0059
  have p0061 := @gOpksnelsik (synCsn (.cv w)) (.cv z) (synCssetk) p0048 p0020
  have p0062 := @gElssetk (.cv w) (.cv z) p0050 p0020
  have p0063_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv w)) (.cv z)) (synCssetk)) (.objMem w z)) :=
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
      p0062
  have p0063 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv w))) (synCsn (.cv z)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv w)) (.cv z)) (synCssetk)) (.objMem w z) p0061
      p0063_e01_recanon
  have p0064 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCins3k (synCsik (synCsik (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv w)))) (synCsn (synCsn (.cv z))))
        (synCsik (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (.cv w))) (synCsn (.cv z)))
        (synCsik (synCssetk)))
      (.objMem w z) p0057 p0060 p0063
  have p0065 :=
    @gOrbi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCins2k (synCins3k (synCssetk))))
      (.objMem w y)
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCins3k (synCsik (synCsik (synCssetk)))))
      (.objMem w z) p0056 p0064
  have p0066 :=
    @gElun
      (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
        (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
      (synCins2k (synCins3k (synCssetk)))
      (synCins3k (synCsik (synCsik (synCssetk))))
  have p0067 := @gElun (.cv w) (.cv y) (.cv z)
  have p0068_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv w) (synCun (.cv y) (.cv z)))
        (synWo (.objMem w y) (.objMem w z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synWo
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
    @gN3bitr4i
      (synWo (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCins2k (synCins3k (synCssetk)))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCins3k (synCsik (synCsik (synCssetk))))))
      (synWo (.objMem w y) (.objMem w z))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCun (synCins2k (synCins3k (synCssetk)))
          (synCins3k (synCsik (synCsik (synCssetk))))))
      (.classMem (.cv w) (synCun (.cv y) (.cv z))) p0065 p0066 p0068_e02_recanon
  have p0069 :=
    @gBibi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCins2k (synCins2k (synCssetk))))
      (.objMem w x)
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCun (synCins2k (synCins3k (synCssetk)))
          (synCins3k (synCsik (synCsik (synCssetk))))))
      (.classMem (.cv w) (synCun (.cv y) (.cv z))) p0052 p0068
  have p0070 :=
    @gNotbii
      (synWb (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCins2k (synCins2k (synCssetk)))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCun (synCins2k (synCins3k (synCssetk)))
            (synCins3k (synCsik (synCsik (synCssetk)))))))
      (synWb (.objMem w x) (.classMem (.cv w) (synCun (.cv y) (.cv z)))) p0069
  have p0071 :=
    @gN3bitri
      (synWex t (synWa
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
          (.classMem (synCopk (.cv t)
              (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk)))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
        (synCsymdif (synCins2k (synCins2k (synCssetk)))
          (synCun (synCins2k (synCins3k (synCssetk)))
            (synCins3k (synCsik (synCsik (synCssetk)))))))
      (.neg (synWb (.classMem
            (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
              (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
            (synCins2k (synCins2k (synCssetk)))) (.classMem
            (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
              (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))))
      (.neg (synWb (.objMem w x) (.classMem (.cv w) (synCun (.cv y) (.cv z))))) p0044
      p0045 p0070
  have p0072 :=
    @gExbii
      (synWex t (synWa
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
          (.classMem (synCopk (.cv t)
              (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk)))))))))
      (.neg (synWb (.objMem w x) (.classMem (.cv w) (synCun (.cv y) (.cv z))))) w p0071
  have p0073 :=
    @gExnal (synWb (.objMem w x) (.classMem (.cv w) (synCun (.cv y) (.cv z)))) w
  have p0074 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synWex w (synWex t (synWa
            (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
            (.classMem (synCopk (.cv t)
                (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))))))
      (synWex w (.neg (synWb (.objMem w x) (.classMem (.cv w) (synCun (.cv y) (.cv z))))))
      (.neg (.all w (synWb (.objMem w x) (.classMem (.cv w) (synCun (.cv y) (.cv z))))))
      p0040 p0072 p0073
  have p0075 :=
    @gCon2bii
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (.all w (synWb (.objMem w x) (.classMem (.cv w) (synCun (.cv y) (.cv z))))) p0074
  have p0076_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv x) (synCun (.cv y) (.cv z)))
        (.all w (synWb (.objMem w x) (.classMem (.cv w) (synCun (.cv y) (.cv z)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl
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
    @gBitr2i (.classEq (.cv x) (synCun (.cv y) (.cv z)))
      (.all w (synWb (.objMem w x) (.classMem (.cv w) (synCun (.cv y) (.cv z)))))
      (.neg (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0076_e00_recanon p0075
  have p0077 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) (synCins3k
          (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classEq (synCin (.cv y) (.cv z)) (synC0))
      (.neg (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (.classEq (.cv x) (synCun (.cv y) (.cv z))) p0028 p0076
  have p0078 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
          (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) (synCdif
          (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synWa (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
          (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))) (.neg
          (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
            (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
        (.classEq (.cv x) (synCun (.cv y) (.cv z))))
      p0016 p0017 p0077
  have p0079 :=
    @gRexbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
          (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
        (.classEq (.cv x) (synCun (.cv y) (.cv z))))
      z B p0078
  have p0080 :=
    @gN3bitri
      (.classMem (synCopk (.cv y) (.cv x)) (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B))))
      (synWrex t (synCpw1 (synCpw1 B))
        (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
              (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWrex z B (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
            (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCdif (synCins3k
                  (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWrex z B (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
          (.classEq (.cv x) (synCun (.cv y) (.cv z)))))
      p0004 p0012 p0079
  have p0081 :=
    @gRexbii
      (.classMem (synCopk (.cv y) (.cv x)) (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B))))
      (synWrex z B (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
          (.classEq (.cv x) (synCun (.cv y) (.cv z)))))
      y A p0080
  have p0082 :=
    @gBitri
      (.classMem (.cv x) (synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
          A))
      (synWrex y A (.classMem (synCopk (.cv y) (.cv x)) (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 B)))))
      (synWrex y A (synWrex z B (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
            (.classEq (.cv x) (synCun (.cv y) (.cv z))))))
      p0002 p0081
  have freeVariableCertificate18 :
    x ∉
      ((synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
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
    @gEqabi
      (synWrex y A (synWrex z B (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
            (.classEq (.cv x) (synCun (.cv y) (.cv z))))))
      x
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
        A)
      freeVariableCertificate18 p0082
  have p0084 :=
    @gEqtr4i (synCplc A B)
      (.cab x (synWrex y A (synWrex z B (synWa (.classEq (synCin (.cv y) (.cv z)) (synC0))
              (.classEq (.cv x) (synCun (.cv y) (.cv z)))))))
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
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

/-- Checked nominal proof certificate identified upstream as `g_addcexlem`. -/
@[expose]
noncomputable def gAddcexlem :
    Nominal.NPrf
      (.classMem (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCvv)) :=
  by
  have p0000 := @gSsetkex
  have p0001 := @gIns3kex (synCssetk) p0000
  have p0003 := @gIns2kex (synCssetk) p0000
  have p0004 := @gInex (synCins3k (synCssetk)) (synCins2k (synCssetk)) p0001 p0003
  have p0005 := @gN1cex
  have p0006 := @gPw1ex (synC1c) p0005
  have p0007 := @gPw1ex (synCpw1 (synC1c)) p0006
  have p0008 :=
    @gImakex (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) p0004 p0007
  have p0009 :=
    @gComplex
      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0008
  have p0010 :=
    @gIns3kex
      (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      p0009
  have p0011 := @gIns2kex (synCins2k (synCssetk)) p0003
  have p0012 := @gIns2kex (synCins3k (synCssetk)) p0001
  have p0014 := @gSikex (synCssetk) p0000
  have p0015 := @gSikex (synCsik (synCssetk)) p0014
  have p0016 := @gIns3kex (synCsik (synCsik (synCssetk))) p0015
  have p0017 :=
    @gUnex (synCins2k (synCins3k (synCssetk)))
      (synCins3k (synCsik (synCsik (synCssetk)))) p0012 p0016
  have p0018 :=
    @gSymdifex (synCins2k (synCins2k (synCssetk)))
      (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))
      p0011 p0017
  have p0019 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0007
  have p0020 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0019
  have p0021 :=
    @gImakex
      (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk)))
          (synCins3k (synCsik (synCsik (synCssetk))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0018 p0020
  have p0022 :=
    @gDifex
      (synCins3k (synCcompl
          (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
          (synCun (synCins2k (synCins3k (synCssetk)))
            (synCins3k (synCsik (synCsik (synCssetk))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0010 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_addceq1`. -/
@[expose]
noncomputable def gAddceq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCplc A C) (synCplc B C))) :=
  by
  have p0000 :=
    @gImakeq2 A B
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 C)))
  have p0001 := @gDfaddc2 A C
  have p0002 := @gDfaddc2 B C
  have p0003 :=
    @gN3eqtr4g (.classEq A B)
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 C)))
        A)
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 C)))
        B)
      (synCplc A C) (synCplc B C) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_addceq2`. -/
@[expose]
noncomputable def gAddceq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCplc C A) (synCplc C B))) :=
  by
  have p0000 := @gPw1eq A B
  have p0001 := @gPw1eq (synCpw1 A) (synCpw1 B)
  have p0002 :=
    @gSyl (.classEq A B) (.classEq (synCpw1 A) (synCpw1 B))
      (.classEq (synCpw1 (synCpw1 A)) (synCpw1 (synCpw1 B))) p0000 p0001
  have p0003 :=
    @gImakeq2d (.classEq A B) (synCpw1 (synCpw1 A)) (synCpw1 (synCpw1 B))
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0002
  have p0004 :=
    @gImakeq1d (.classEq A B)
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 A)))
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
      C p0003
  have p0005 := @gDfaddc2 C A
  have p0006 := @gDfaddc2 C B
  have p0007 :=
    @gN3eqtr4g (.classEq A B)
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 A)))
        C)
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
        C)
      (synCplc C A) (synCplc C B) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_addceq12`. -/
@[expose]
noncomputable def gAddceq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A C) (.classEq B D)) (.classEq (synCplc A B) (synCplc C D))) :=
  by
  have p0000 := @gAddceq1 A C B
  have p0001 := @gAddceq2 B D C
  have p0002 :=
    @gSylan9eq (.classEq A C) (.classEq B D) (synCplc A B) (synCplc C B) (synCplc C D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_addceq1i`. -/
@[expose]
noncomputable def gAddceq1i (A : Class) (B : Class) (C : Class)
    (hyp_addceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCplc A C) (synCplc B C)) :=
  by
  have p0000 := @gAddceq1 A B C
  have p0001 := Nominal.mp hyp_addceqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_addceq2i`. -/
@[expose]
noncomputable def gAddceq2i (A : Class) (B : Class) (C : Class)
    (hyp_addceqi_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCplc C A) (synCplc C B)) :=
  by
  have p0000 := @gAddceq2 A B C
  have p0001 := Nominal.mp hyp_addceqi_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_addceq12i`. -/
@[expose]
noncomputable def gAddceq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_addceqi_1 : Nominal.NPrf (.classEq A B))
    (hyp_addceqi_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (synCplc A C) (synCplc B D)) :=
  by
  have p0000 := @gAddceq12 A C B D
  have p0001 :=
    @gMp2an (.classEq A B) (.classEq C D) (.classEq (synCplc A C) (synCplc B D))
      hyp_addceqi_1 hyp_addceqi_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_addceq1d`. -/
@[expose]
noncomputable def gAddceq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_addceqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCplc A C) (synCplc B C))) :=
  by
  have p0000 := @gAddceq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCplc A C) (synCplc B C)) hyp_addceqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_addceq2d`. -/
@[expose]
noncomputable def gAddceq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_addceqd_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCplc C A) (synCplc C B))) :=
  by
  have p0000 := @gAddceq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCplc C A) (synCplc C B)) hyp_addceqd_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_addceq12d`. -/
@[expose]
noncomputable def gAddceq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_addceqd_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_addceqd_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (synCplc A C) (synCplc B D))) :=
  by
  have p0000 := @gAddceq12 A C B D
  have p0001 :=
    @gSyl2anc ph (.classEq A B) (.classEq C D) (.classEq (synCplc A C) (synCplc B D))
      hyp_addceqd_1 hyp_addceqd_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_n_0cex`. -/
@[expose]
noncomputable def gN0cex : Nominal.NPrf (.classMem (synC0c) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synC0c))
  have p0001 := @gSnex (synC0)
  have p0002 := @gEqeltri (synC0c) (synCsn (synC0)) (synCvv) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_addcexg`. -/
@[expose]
noncomputable def gAddcexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCplc A B) (synCvv))) :=
  by
  have p0000 := @gDfaddc2 A B
  have p0001 := @gPw1exg B W
  have p0002 := @gPw1exg (synCpw1 B) (synCvv)
  have p0003 := @gAddcexlem
  have p0004 :=
    @gImakexg
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 B)) (synCvv) (synCvv)
  have p0005 :=
    @gMpan
      (.classMem (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCvv))
      (.classMem (synCpw1 (synCpw1 B)) (synCvv))
      (.classMem (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
        (synCvv))
      p0003 p0004
  have p0006 :=
    @gN3syl (.classMem B W) (.classMem (synCpw1 B) (synCvv))
      (.classMem (synCpw1 (synCpw1 B)) (synCvv))
      (.classMem (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
        (synCvv))
      p0001 p0002 p0005
  have p0007 :=
    @gImakexg
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
      A (synCvv) V
  have p0008 :=
    @gSylan (.classMem B W)
      (.classMem (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
        (synCvv))
      (.classMem A V)
      (.classMem (synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
          A) (synCvv))
      p0006 p0007
  have p0009 :=
    @gAncoms (.classMem B W) (.classMem A V)
      (.classMem (synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
          A) (synCvv))
      p0008
  have p0010 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCplc A B)
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 B)))
        A)
      (synCvv) p0000 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_addcex`. -/
@[expose]
noncomputable def gAddcex (A : Class) (B : Class)
    (hyp_addcex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_addcex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCplc A B) (synCvv)) :=
  by
  have p0000 := @gAddcexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCplc A B) (synCvv)) hyp_addcex_1 hyp_addcex_2 p0000
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

/-- Checked nominal proof certificate identified upstream as `g_dfnnc2`. -/
@[expose]
noncomputable def gDfnnc2 (x : Var) :
    Nominal.NPrf
      (.classEq (synCnnc) (synCint (synCdif (.cab x (.classMem (synC0c) (.cv x))) (synCimak
              (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak
                        (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synC1c))))) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfNnc z y
      (show y ≠ z from (by exact fresh_y_ne_z))
  have p0001 :=
    @gEldif (.cv y) (.cab x (.classMem (synC0c) (.cv x)))
      (synCimak (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek
                (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))) (synC1c))
  have p0002 := @gVex y
  have p0003 := @gEleq2 (.cv x) (.cv y) (synC0c)
  have freeVariableCertificate0 : x ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_x_ne_y, not_false_eq_true]
  have freeVariableCertificate1 : x ∉ ((Wff.classMem (synC0c) (.cv y))).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
      NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_singleton,
      Finset.notMem_empty, fresh_x_ne_y, or_false, not_false_eq_true]
  have p0004 :=
    @gElab (.classMem (synC0c) (.cv x)) (.classMem (synC0c) (.cv y)) x (.cv y)
      freeVariableCertificate0 freeVariableCertificate1 p0002 p0003
  have p0005 := @gSnex (.cv z)
  have p0006 := @gOpkeq1 (.cv t) (synCsn (.cv z)) (.cv y)
  have p0007 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv z))) (synCopk (.cv t) (.cv y))
      (synCopk (synCsn (.cv z)) (.cv y))
      (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif
                  (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      p0006
  have freeVariableCertificate2 : t ∉ ((synCsn (.cv z))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_z,
      not_false_eq_true]
  have freeVariableCertificate3 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCdif (synCssetk)
            (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif (synCins3k
                        (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))))).fv :=
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
    @gCeqsexv
      (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
            (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCdif (synCssetk)
          (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      t (synCsn (.cv z)) freeVariableCertificate2 freeVariableCertificate3 p0005 p0007
  have p0009 :=
    @gEldif (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk)
      (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif (synCins3k
                  (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))))
  have p0010 := @gVex z
  have p0011 := @gElssetk (.cv z) (.cv y) p0010 p0002
  have p0012 := @gSnex (.cv w)
  have p0013 := @gOpkeq2 (.cv t) (synCsn (.cv w)) (synCsn (.cv z))
  have p0014 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv w))) (synCopk (synCsn (.cv z)) (.cv t))
      (synCopk (synCsn (.cv z)) (synCsn (.cv w)))
      (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0013
  have p0015 := @gVex w
  have p0016 :=
    @gOpksnelsik (.cv z) (.cv w)
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0010 p0015
  have p0017 :=
    @gSyl6bb (.classEq (.cv t) (synCsn (.cv w)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
              (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv w))) (synCsik (synCimagek
            (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (.cv z) (.cv w)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0014 p0016
  have p0018 := @gOpkeq1 (.cv t) (synCsn (.cv w)) (.cv y)
  have p0019 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv w))) (synCopk (.cv t) (.cv y))
      (synCopk (synCsn (.cv w)) (.cv y)) (synCssetk) p0018
  have p0020 :=
    @gAnbi12d (.classEq (.cv t) (synCsn (.cv w)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
              (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (.cv z) (.cv w)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))
      (.classMem (synCopk (synCsn (.cv w)) (.cv y)) (synCssetk)) p0017 p0019
  have freeVariableCertificate4 : t ∉ ((synCsn (.cv w))).fv := by
    simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
      NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_w,
      not_false_eq_true]
  have freeVariableCertificate5 :
    t ∉
      ((synWa (.classMem (synCopk (.cv z) (.cv w)) (synCimagek (synCimak (synCdif
                  (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))))
          (.classMem (synCopk (synCsn (.cv w)) (.cv y)) (synCssetk)))).fv :=
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
    @gCeqsexv
      (synWa (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c)))))))
        (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)))
      (synWa (.classMem (synCopk (.cv z) (.cv w)) (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))))
        (.classMem (synCopk (synCsn (.cv w)) (.cv y)) (synCssetk)))
      t (synCsn (.cv w)) freeVariableCertificate4 freeVariableCertificate5 p0012 p0020
  have p0022 :=
    @gOpkelimagekg (.cv z) (.cv w)
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))
      (synCvv) (synCvv)
  have p0023 :=
    @gMp2an (.classMem (.cv z) (synCvv)) (.classMem (.cv w) (synCvv))
      (synWb (.classMem (synCopk (.cv z) (.cv w)) (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))) (.classEq (.cv w) (synCimak (synCimak
              (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))) (.cv z))))
      p0010 p0015 p0022
  have p0024 := @gDfaddc2 (.cv z) (synC1c)
  have p0025 :=
    @gEqeq2i (synCplc (.cv z) (synC1c))
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))) (.cv z))
      (.cv w) p0024
  have p0026 :=
    @gBitr4i
      (.classMem (synCopk (.cv z) (.cv w)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (.cv w) (synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c)))) (.cv z)))
      (.classEq (.cv w) (synCplc (.cv z) (synC1c))) p0023 p0025
  have p0027 := @gElssetk (.cv w) (.cv y) p0015 p0002
  have p0028_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv w)) (.cv y)) (synCssetk)) (.objMem w y)) :=
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
      p0027
  have p0028 :=
    @gAnbi12i
      (.classMem (synCopk (.cv z) (.cv w)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (.cv w) (synCplc (.cv z) (synC1c)))
      (.classMem (synCopk (synCsn (.cv w)) (.cv y)) (synCssetk)) (.objMem w y) p0026
      p0028_e01_recanon
  have p0029 :=
    @gBitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv w))) (synWa
            (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))
            (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)))))
      (synWa (.classMem (synCopk (.cv z) (.cv w)) (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))))
        (.classMem (synCopk (synCsn (.cv w)) (.cv y)) (synCssetk)))
      (synWa (.classEq (.cv w) (synCplc (.cv z) (synC1c))) (.objMem w y)) p0021 p0028
  have p0030 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv w))) (synWa
            (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))
            (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)))))
      (synWa (.classEq (.cv w) (synCplc (.cv z) (synC1c))) (.objMem w y)) w p0029
  have freeVariableCertificate6 : t ∉ ((Class.cv y)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_t_ne_y, not_false_eq_true]
  have freeVariableCertificate7 :
    t ∉
      ((synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))))).fv :=
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
    @gOpkelcok t (synCsn (.cv z)) (.cv y) (synCssetk)
      (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      freeVariableCertificate2 freeVariableCertificate6
      (by
        exact
          (show t ∉ ((synCssetk)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate7 p0005 p0002
  have freeVariableCertificate8 : w ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_w_ne_t, not_false_eq_true]
  have p0032 := @gEl1c w (.cv t) freeVariableCertificate8
  have p0033 :=
    @gAnbi1i (.classMem (.cv t) (synC1c))
      (synWex w (.classEq (.cv t) (synCsn (.cv w))))
      (synWa (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c)))))))
        (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)))
      p0032
  have freeVariableCertificate9 :
    w ∉
      ((synWa (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                  (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))
          (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)))).fv :=
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
    @gN1941v (.classEq (.cv t) (synCsn (.cv w)))
      (synWa (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c)))))))
        (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)))
      w freeVariableCertificate9
  have p0035 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synC1c)) (synWa
          (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                  (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))
          (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))))
      (synWa (synWex w (.classEq (.cv t) (synCsn (.cv w)))) (synWa
          (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                  (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))
          (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))))
      (synWex w (synWa (.classEq (.cv t) (synCsn (.cv w))) (synWa
            (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))
            (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)))))
      p0033 p0034
  have p0036 :=
    @gExbii
      (synWa (.classMem (.cv t) (synC1c)) (synWa
          (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                  (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))
          (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))))
      (synWex w (synWa (.classEq (.cv t) (synCsn (.cv w))) (synWa
            (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))
            (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)))))
      t p0035
  have p0037 :=
    @gSikss1c1c
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))))
  have p0038 :=
    @gSseli
      (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      (synCxpk (synC1c) (synC1c)) (synCopk (synCsn (.cv z)) (.cv t)) p0037
  have p0039 := @gVex t
  have p0040 := @gOpkelxpk (synCsn (.cv z)) (.cv t) (synC1c) (synC1c) p0005 p0039
  have p0041 :=
    @gSimprbi
      (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCxpk (synC1c) (synC1c)))
      (.classMem (synCsn (.cv z)) (synC1c)) (.classMem (.cv t) (synC1c)) p0040
  have p0042 :=
    @gSyl
      (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
              (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCxpk (synC1c) (synC1c)))
      (.classMem (.cv t) (synC1c)) p0038 p0041
  have p0043 :=
    @gPm471ri
      (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
              (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (.cv t) (synC1c)) p0042
  have p0044 :=
    @gAnbi1i
      (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
              (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (synCsn (.cv z)) (.cv t))
          (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)) p0043
  have p0045 :=
    @gAnass (.classMem (.cv t) (synC1c))
      (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
              (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))
  have p0046 :=
    @gBitri
      (synWa (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c)))))))
        (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)))
      (synWa (synWa (.classMem (.cv t) (synC1c))
          (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                  (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))))))
        (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)))
      (synWa (.classMem (.cv t) (synC1c)) (synWa
          (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                  (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))
          (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))))
      p0044 p0045
  have p0047 :=
    @gExbii
      (synWa (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c)))))))
        (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)))
      (synWa (.classMem (.cv t) (synC1c)) (synWa
          (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                  (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))
          (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))))
      t p0046
  have p0048 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (.cv w))) (synWa
          (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                  (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))
          (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))))
      w t
  have p0049 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synC1c)) (synWa
            (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))
            (.classMem (synCopk (.cv t) (.cv y)) (synCssetk)))))
      (synWex t (synWex w (synWa (.classEq (.cv t) (synCsn (.cv w))) (synWa
              (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))
              (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))))))
      (synWex t (synWa (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek
                (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))
          (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))))
      (synWex w (synWex t (synWa (.classEq (.cv t) (synCsn (.cv w))) (synWa
              (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))
              (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))))))
      p0036 p0047 p0048
  have p0050 :=
    @gBitri
      (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCcomk (synCssetk) (synCsik
            (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWex t (synWa (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek
                (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))
          (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))))
      (synWex w (synWex t (synWa (.classEq (.cv t) (synCsn (.cv w))) (synWa
              (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))
              (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))))))
      p0031 p0049
  have freeVariableCertificate10 : w ∉ ((synCplc (.cv z) (synC1c))).fv := by
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
      (synCplc (.cv z) (synC1c)) (.cv y) freeVariableCertificate10 freeVariableCertificate11)
  have p0052_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCplc (.cv z) (synC1c)) (.cv y)) (synWex w
          (synWa (.classEq (.cv w) (synCplc (.cv z) (synC1c))) (.objMem w y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa synC1c
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
    @gN3bitr4i
      (synWex w (synWex t (synWa (.classEq (.cv t) (synCsn (.cv w))) (synWa
              (.classMem (synCopk (synCsn (.cv z)) (.cv t)) (synCsik (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))
              (.classMem (synCopk (.cv t) (.cv y)) (synCssetk))))))
      (synWex w (synWa (.classEq (.cv w) (synCplc (.cv z) (synC1c))) (.objMem w y)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCcomk (synCssetk) (synCsik
            (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCplc (.cv z) (synC1c)) (.cv y)) p0030 p0050 p0052_e02_recanon
  have p0053 :=
    @gNotbii
      (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCcomk (synCssetk) (synCsik
            (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCplc (.cv z) (synC1c)) (.cv y)) p0052
  have p0054_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk)) (.objMem z y)) :=
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
      p0011
  have p0054 :=
    @gAnbi12i (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk)) (.objMem z y)
      (.neg (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCcomk (synCssetk) (synCsik
              (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (.neg (.classMem (synCplc (.cv z) (synC1c)) (.cv y))) p0054_e00_recanon p0053
  have p0055 :=
    @gBitri
      (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCdif (synCssetk)
          (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk)) (.neg
          (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCcomk (synCssetk) (synCsik
                (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWa (.objMem z y) (.neg (.classMem (synCplc (.cv z) (synC1c)) (.cv y)))) p0009
      p0054
  have p0056 :=
    @gBitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv z)))
          (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
                (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCdif (synCssetk)
          (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (.objMem z y) (.neg (.classMem (synCplc (.cv z) (synC1c)) (.cv y)))) p0008
      p0055
  have p0057 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv z)))
          (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
                (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWa (.objMem z y) (.neg (.classMem (synCplc (.cv z) (synC1c)) (.cv y)))) z
      p0056
  have freeVariableCertificate12 :
    t ∉
      ((synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak
                  (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
    @gElimak t
      (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif
                  (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synC1c) (.cv y) freeVariableCertificate12
      (by
        exact
          (show t ∉ ((synC1c)).fv from
            (by
              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c];
              exact (show t ∉ (∅ : Finset Var) from (fun hmem => by cases hmem)))))
      freeVariableCertificate6 p0002
  have freeVariableCertificate13 : z ∉ ((Class.cv t)).fv := by
    simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
      fresh_z_ne_t, not_false_eq_true]
  have p0059 := @gEl1c z (.cv t) freeVariableCertificate13
  have p0060 :=
    @gAnbi1i (.classMem (.cv t) (synC1c))
      (synWex z (.classEq (.cv t) (synCsn (.cv z))))
      (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
            (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      p0059
  have freeVariableCertificate14 :
    z ∉
      ((Wff.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
              (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))))).fv :=
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
    @gN1941v (.classEq (.cv t) (synCsn (.cv z)))
      (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
            (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      z freeVariableCertificate14
  have p0062 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv y))
          (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWa (synWex z (.classEq (.cv t) (synCsn (.cv z))))
        (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
              (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (.cv z)))
          (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
                (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      p0060 p0061
  have p0063 :=
    @gExbii
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv y))
          (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (.cv z)))
          (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
                (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      t p0062
  have p0064 :=
    (Nominal.biimpRefl (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv y))
          (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))))))
  have p0065 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (.cv z))) (.classMem (synCopk (.cv t) (.cv y))
          (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      z t
  have p0066 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv y))
            (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWex t (synWex z (synWa (.classEq (.cv t) (synCsn (.cv z)))
            (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
                  (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk)
            (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif (synCins3k
                        (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (.cv z)))
            (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
                  (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      p0063 p0064 p0065
  have p0067 :=
    @gBitri
      (.classMem (.cv y) (synCimak (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik
                (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synC1c)))
      (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk)
            (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif (synCins3k
                        (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (.cv z)))
            (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
                  (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      p0058 p0066
  have p0068 :=
    (Nominal.biimpRefl
      (synWrex z (.cv y) (.neg (.classMem (synCplc (.cv z) (synC1c)) (.cv y)))))
  have p0069_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex z (.cv y) (.neg (.classMem (synCplc (.cv z) (synC1c)) (.cv y))))
        (synWex z (synWa (.objMem z y)
            (.neg (.classMem (synCplc (.cv z) (synC1c)) (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCplc, synC1c]
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
    @gN3bitr4i
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (.cv z)))
            (.classMem (synCopk (.cv t) (.cv y)) (synCdif (synCssetk) (synCcomk (synCssetk)
                  (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      (synWex z (synWa (.objMem z y) (.neg (.classMem (synCplc (.cv z) (synC1c)) (.cv y)))))
      (.classMem (.cv y) (synCimak (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik
                (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synC1c)))
      (synWrex z (.cv y) (.neg (.classMem (synCplc (.cv z) (synC1c)) (.cv y)))) p0057
      p0067 p0069_e02_recanon
  have p0070 := @gRexnal (.classMem (synCplc (.cv z) (synC1c)) (.cv y)) z (.cv y)
  have p0071 :=
    @gBitr2i
      (.classMem (.cv y) (synCimak (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik
                (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synC1c)))
      (synWrex z (.cv y) (.neg (.classMem (synCplc (.cv z) (synC1c)) (.cv y))))
      (.neg (synWral z (.cv y) (.classMem (synCplc (.cv z) (synC1c)) (.cv y)))) p0069
      p0070
  have p0072 :=
    @gCon1bii (synWral z (.cv y) (.classMem (synCplc (.cv z) (synC1c)) (.cv y)))
      (.classMem (.cv y) (synCimak (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik
                (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synC1c)))
      p0071
  have p0073 :=
    @gAnbi12i (.classMem (.cv y) (.cab x (.classMem (synC0c) (.cv x))))
      (.classMem (synC0c) (.cv y))
      (.neg (.classMem (.cv y) (synCimak (synCdif (synCssetk) (synCcomk (synCssetk)
                (synCsik (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synC1c))))
      (synWral z (.cv y) (.classMem (synCplc (.cv z) (synC1c)) (.cv y))) p0004 p0072
  have p0074 :=
    @gBitri
      (.classMem (.cv y) (synCdif (.cab x (.classMem (synC0c) (.cv x))) (synCimak
            (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synC1c))))
      (synWa (.classMem (.cv y) (.cab x (.classMem (synC0c) (.cv x)))) (.neg
          (.classMem (.cv y) (synCimak (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik
                    (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synC1c)))))
      (synWa (.classMem (synC0c) (.cv y))
        (synWral z (.cv y) (.classMem (synCplc (.cv z) (synC1c)) (.cv y))))
      p0001 p0073
  have freeVariableCertificate15 :
    y ∉
      ((synCdif (.cab x (.classMem (synC0c) (.cv x))) (synCimak (synCdif (synCssetk)
              (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif (synCins3k
                          (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synC1c)))).fv :=
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
    @gEqabi
      (synWa (.classMem (synC0c) (.cv y))
        (synWral z (.cv y) (.classMem (synCplc (.cv z) (synC1c)) (.cv y))))
      y
      (synCdif (.cab x (.classMem (synC0c) (.cv x))) (synCimak (synCdif (synCssetk)
            (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif (synCins3k
                        (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synC1c)))
      freeVariableCertificate15 p0074
  have p0076 :=
    @gInteqi
      (synCdif (.cab x (.classMem (synC0c) (.cv x))) (synCimak (synCdif (synCssetk)
            (synCcomk (synCssetk) (synCsik (synCimagek (synCimak (synCdif (synCins3k
                        (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synC1c)))
      (.cab y (synWa (.classMem (synC0c) (.cv y))
          (synWral z (.cv y) (.classMem (synCplc (.cv z) (synC1c)) (.cv y)))))
      p0075
  have p0077 :=
    @gEqtr4i (synCnnc)
      (synCint (.cab y (synWa (.classMem (synC0c) (.cv y))
            (synWral z (.cv y) (.classMem (synCplc (.cv z) (synC1c)) (.cv y))))))
      (synCint (synCdif (.cab x (.classMem (synC0c) (.cv x))) (synCimak
            (synCdif (synCssetk) (synCcomk (synCssetk) (synCsik (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synC1c))))
      p0000 p0076
  exact p0077


end NFChoice.DirectNominalPrf.WPPReplay

end
