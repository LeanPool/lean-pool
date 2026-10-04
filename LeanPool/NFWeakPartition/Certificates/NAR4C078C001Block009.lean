/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NAR4C078C001Block008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NAR4C078C001Part030`. -/


section

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

theorem nb078_support_mem_1165 (h : Var) :
    (nb078AlphaDummy1112 h) ∈
      (((Class.cv (nb078AlphaDummy1112 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1112 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1166 :
    (nb078AlphaDummy1051) ∈
      (((Class.cv (nb078AlphaDummy1049))).fv ∪ ((Class.cv (nb078AlphaDummy1051))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1167 :
    (nb078AlphaDummy1051) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1093)
              (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1049))
                (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                  (synCphi (Class.cv (nb078AlphaDummy1094)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1093)
              (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
                (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1093) from (by
          unfold nb078AlphaDummy1093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1166) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1094) from (by
            unfold nb078AlphaDummy1094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1166) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1168 (h : Var) :
    (nb078AlphaDummy1054 h) ∈
      (((Class.cv (nb078AlphaDummy1052 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1054 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1169 (h : Var) :
    (nb078AlphaDummy1054 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1095 h)
              (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1052 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                  (synCphi (Class.cv (nb078AlphaDummy1096 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1095 h)
              (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1095 h) from (by
          unfold nb078AlphaDummy1095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1168 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1096 h) from (by
            unfold nb078AlphaDummy1096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1168 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1170 :
    (nb078AlphaDummy1051) ∈
      (((Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1093)
            (synWrex (nb078AlphaDummy1094) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1093))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1094)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1093) from (by
          unfold nb078AlphaDummy1093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1166) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1094) from (by
            unfold nb078AlphaDummy1094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1166) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1171 (h : Var) :
    (nb078AlphaDummy1054 h) ∈
      (((Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1095 h)
            (synWrex (nb078AlphaDummy1096 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1095 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1096 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1095 h) from (by
          unfold nb078AlphaDummy1095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1168 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1096 h) from (by
            unfold nb078AlphaDummy1096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1168 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1172 :
    (nb078AlphaDummy1094) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1094))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1173 (h : Var) :
    (nb078AlphaDummy1096 h) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1096 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1174 :
    (nb078AlphaDummy1094) ∈
      (((synCphi (Class.cv (nb078AlphaDummy1094)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1175 (h : Var) :
    (nb078AlphaDummy1096 h) ∈
      (((synCphi (Class.cv (nb078AlphaDummy1096 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1096 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1176 :
    (nb078AlphaDummy1129) ∈
      (({(nb078AlphaDummy1129)} : Finset Var) ∪ ({(nb078AlphaDummy1130)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy1130))
            (synCcnv (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy1129)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1177 (h : Var) :
    (nb078AlphaDummy1131 h) ∈
      (({(nb078AlphaDummy1131 h)} : Finset Var) ∪
          ({(nb078AlphaDummy1132 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy1132 h)) (synCcnv (Class.cv h))
            (Class.cv (nb078AlphaDummy1131 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1178 :
    (nb078AlphaDummy1130) ∈
      (({(nb078AlphaDummy1129)} : Finset Var) ∪ ({(nb078AlphaDummy1130)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy1130))
            (synCcnv (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy1129)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1179 (h : Var) :
    (nb078AlphaDummy1132 h) ∈
      (({(nb078AlphaDummy1131 h)} : Finset Var) ∪
          ({(nb078AlphaDummy1132 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy1132 h)) (synCcnv (Class.cv h))
            (Class.cv (nb078AlphaDummy1131 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1180 :
    (nb078AlphaDummy1129) ∈
      (((Class.cv (nb078AlphaDummy1129))).fv ∪ ((Class.cv (nb078AlphaDummy1130))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1181 :
    (nb078AlphaDummy1129) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1135)
              (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
                (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                  (synCphi (Class.cv (nb078AlphaDummy1136)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1135)
              (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
                (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1135) from (by
          unfold nb078AlphaDummy1135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1136) from (by
            unfold nb078AlphaDummy1136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1182 (h : Var) :
    (nb078AlphaDummy1131 h) ∈
      (((Class.cv (nb078AlphaDummy1131 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1132 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1183 (h : Var) :
    (nb078AlphaDummy1131 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1137 h)
              (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                  (synCphi (Class.cv (nb078AlphaDummy1138 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1137 h)
              (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1137 h) from (by
          unfold nb078AlphaDummy1137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1182 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1138 h) from (by
            unfold nb078AlphaDummy1138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1182 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1184 :
    (nb078AlphaDummy1129) ∈
      (((Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCphi (Class.cv (nb078AlphaDummy1136))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCphi (Class.cv (nb078AlphaDummy1136))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1135) from (by
          unfold nb078AlphaDummy1135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1136) from (by
            unfold nb078AlphaDummy1136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1185 (h : Var) :
    (nb078AlphaDummy1131 h) ∈
      (((Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCphi (Class.cv (nb078AlphaDummy1138 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCphi (Class.cv (nb078AlphaDummy1138 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1137 h) from (by
          unfold nb078AlphaDummy1137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1182 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1138 h) from (by
            unfold nb078AlphaDummy1138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1182 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1186 :
    (nb078AlphaDummy1136) ∈ (((Class.cv (nb078AlphaDummy1136))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1187 (h : Var) :
    (nb078AlphaDummy1138 h) ∈ (((Class.cv (nb078AlphaDummy1138 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1188 :
    (nb078AlphaDummy1143) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy1143)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1143)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1143))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1189 (h : Var) :
    (nb078AlphaDummy1145 h) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy1145 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1145 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1145 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1190 :
    (nb078AlphaDummy1143) ∈
      (((Class.cv (nb078AlphaDummy1143))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1191 (h : Var) :
    (nb078AlphaDummy1145 h) ∈
      (((Class.cv (nb078AlphaDummy1145 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1192 :
    (nb078AlphaDummy1150) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1150)) (Class.cv (nb078AlphaDummy1151)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1150))
            (Class.cv (nb078AlphaDummy1151)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1193 (h : Var) :
    (nb078AlphaDummy1153 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1153 h))
            (Class.cv (nb078AlphaDummy1154 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1153 h))
            (Class.cv (nb078AlphaDummy1154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1194 :
    (nb078AlphaDummy1150) ∈
      (((Class.cv (nb078AlphaDummy1150))).fv ∪ ((Class.cv (nb078AlphaDummy1151))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1195 (h : Var) :
    (nb078AlphaDummy1153 h) ∈
      (((Class.cv (nb078AlphaDummy1153 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1154 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1196 :
    (nb078AlphaDummy1151) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1150)) (Class.cv (nb078AlphaDummy1151)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1150))
            (Class.cv (nb078AlphaDummy1151)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1197 (h : Var) :
    (nb078AlphaDummy1154 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1153 h))
            (Class.cv (nb078AlphaDummy1154 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1153 h))
            (Class.cv (nb078AlphaDummy1154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1198 :
    (nb078AlphaDummy1151) ∈
      (((Class.cv (nb078AlphaDummy1150))).fv ∪ ((Class.cv (nb078AlphaDummy1151))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1199 (h : Var) :
    (nb078AlphaDummy1154 h) ∈
      (((Class.cv (nb078AlphaDummy1153 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1154 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1200 :
    (nb078AlphaDummy1150) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1150)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1151)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1201 (h : Var) :
    (nb078AlphaDummy1153 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1153 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1202 :
    (nb078AlphaDummy1150) ∈
      (((Class.cv (nb078AlphaDummy1150))).fv ∪ ((Class.cv (nb078AlphaDummy1150))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1203 (h : Var) :
    (nb078AlphaDummy1153 h) ∈
      (((Class.cv (nb078AlphaDummy1153 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1153 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1204 :
    (nb078AlphaDummy1151) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1150)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1151)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1205 (h : Var) :
    (nb078AlphaDummy1154 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1153 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1206 :
    (nb078AlphaDummy1151) ∈
      (((Class.cv (nb078AlphaDummy1151))).fv ∪ ((Class.cv (nb078AlphaDummy1151))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1207 (h : Var) :
    (nb078AlphaDummy1154 h) ∈
      (((Class.cv (nb078AlphaDummy1154 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1154 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1208 :
    (nb078AlphaDummy1130) ∈
      (((Class.cv (nb078AlphaDummy1129))).fv ∪ ((Class.cv (nb078AlphaDummy1130))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1209 :
    (nb078AlphaDummy1130) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1135)
              (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1129))
                (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                  (synCphi (Class.cv (nb078AlphaDummy1136)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1135)
              (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
                (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1135) from (by
          unfold nb078AlphaDummy1135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1208) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1136) from (by
            unfold nb078AlphaDummy1136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1208) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1210 (h : Var) :
    (nb078AlphaDummy1132 h) ∈
      (((Class.cv (nb078AlphaDummy1131 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1132 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1211 (h : Var) :
    (nb078AlphaDummy1132 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1137 h)
              (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1131 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                  (synCphi (Class.cv (nb078AlphaDummy1138 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1137 h)
              (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1137 h) from (by
          unfold nb078AlphaDummy1137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1210 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1138 h) from (by
            unfold nb078AlphaDummy1138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1210 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1212 :
    (nb078AlphaDummy1130) ∈
      (((Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1135)
            (synWrex (nb078AlphaDummy1136) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1135))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1136)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1135) from (by
          unfold nb078AlphaDummy1135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1208) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1136) from (by
            unfold nb078AlphaDummy1136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1208) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1213 (h : Var) :
    (nb078AlphaDummy1132 h) ∈
      (((Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1137 h)
            (synWrex (nb078AlphaDummy1138 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1137 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1138 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1137 h) from (by
          unfold nb078AlphaDummy1137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1210 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1138 h) from (by
            unfold nb078AlphaDummy1138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1210 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1214 :
    (nb078AlphaDummy1136) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1136))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1215 (h : Var) :
    (nb078AlphaDummy1138 h) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1138 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1216 :
    (nb078AlphaDummy1136) ∈
      (((synCphi (Class.cv (nb078AlphaDummy1136)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1136)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1217 (h : Var) :
    (nb078AlphaDummy1138 h) ∈
      (((synCphi (Class.cv (nb078AlphaDummy1138 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1138 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1218 :
    (nb078AlphaDummy1130) ∈
      (((Class.cv (nb078AlphaDummy1130))).fv ∪ ((Class.cv (nb078AlphaDummy1129))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1219 :
    (nb078AlphaDummy1130) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1171)
              (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
                (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                  (synCphi (Class.cv (nb078AlphaDummy1172)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1171)
              (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
                (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1171) from (by
          unfold nb078AlphaDummy1171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1172) from (by
            unfold nb078AlphaDummy1172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1220 (h : Var) :
    (nb078AlphaDummy1132 h) ∈
      (((Class.cv (nb078AlphaDummy1132 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1131 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1221 (h : Var) :
    (nb078AlphaDummy1132 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1173 h)
              (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                  (synCphi (Class.cv (nb078AlphaDummy1174 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1173 h)
              (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1173 h) from (by
          unfold nb078AlphaDummy1173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1220 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1174 h) from (by
            unfold nb078AlphaDummy1174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1220 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1222 :
    (nb078AlphaDummy1130) ∈
      (((Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCphi (Class.cv (nb078AlphaDummy1172))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCphi (Class.cv (nb078AlphaDummy1172))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1171) from (by
          unfold nb078AlphaDummy1171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1130) ≠ (nb078AlphaDummy1172) from (by
            unfold nb078AlphaDummy1172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1223 (h : Var) :
    (nb078AlphaDummy1132 h) ∈
      (((Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCphi (Class.cv (nb078AlphaDummy1174 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCphi (Class.cv (nb078AlphaDummy1174 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1173 h) from (by
          unfold nb078AlphaDummy1173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1220 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1132 h) ≠ (nb078AlphaDummy1174 h) from (by
            unfold nb078AlphaDummy1174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1220 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1224 :
    (nb078AlphaDummy1172) ∈ (((Class.cv (nb078AlphaDummy1172))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1225 (h : Var) :
    (nb078AlphaDummy1174 h) ∈ (((Class.cv (nb078AlphaDummy1174 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1226 :
    (nb078AlphaDummy1179) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy1179)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1179)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1179))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1227 (h : Var) :
    (nb078AlphaDummy1181 h) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy1181 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1181 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1181 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1228 :
    (nb078AlphaDummy1179) ∈
      (((Class.cv (nb078AlphaDummy1179))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1229 (h : Var) :
    (nb078AlphaDummy1181 h) ∈
      (((Class.cv (nb078AlphaDummy1181 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1230 :
    (nb078AlphaDummy1186) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1186)) (Class.cv (nb078AlphaDummy1187)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1186))
            (Class.cv (nb078AlphaDummy1187)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1231 (h : Var) :
    (nb078AlphaDummy1189 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1189 h))
            (Class.cv (nb078AlphaDummy1190 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1189 h))
            (Class.cv (nb078AlphaDummy1190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1232 :
    (nb078AlphaDummy1186) ∈
      (((Class.cv (nb078AlphaDummy1186))).fv ∪ ((Class.cv (nb078AlphaDummy1187))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1233 (h : Var) :
    (nb078AlphaDummy1189 h) ∈
      (((Class.cv (nb078AlphaDummy1189 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1190 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1234 :
    (nb078AlphaDummy1187) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1186)) (Class.cv (nb078AlphaDummy1187)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1186))
            (Class.cv (nb078AlphaDummy1187)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1235 (h : Var) :
    (nb078AlphaDummy1190 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1189 h))
            (Class.cv (nb078AlphaDummy1190 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1189 h))
            (Class.cv (nb078AlphaDummy1190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1236 :
    (nb078AlphaDummy1187) ∈
      (((Class.cv (nb078AlphaDummy1186))).fv ∪ ((Class.cv (nb078AlphaDummy1187))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1237 (h : Var) :
    (nb078AlphaDummy1190 h) ∈
      (((Class.cv (nb078AlphaDummy1189 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1190 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1238 :
    (nb078AlphaDummy1186) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1186)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1187)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1239 (h : Var) :
    (nb078AlphaDummy1189 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1189 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1240 :
    (nb078AlphaDummy1186) ∈
      (((Class.cv (nb078AlphaDummy1186))).fv ∪ ((Class.cv (nb078AlphaDummy1186))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1241 (h : Var) :
    (nb078AlphaDummy1189 h) ∈
      (((Class.cv (nb078AlphaDummy1189 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1189 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1242 :
    (nb078AlphaDummy1187) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1186)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1187)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1243 (h : Var) :
    (nb078AlphaDummy1190 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1189 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1244 :
    (nb078AlphaDummy1187) ∈
      (((Class.cv (nb078AlphaDummy1187))).fv ∪ ((Class.cv (nb078AlphaDummy1187))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1245 (h : Var) :
    (nb078AlphaDummy1190 h) ∈
      (((Class.cv (nb078AlphaDummy1190 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1190 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1246 :
    (nb078AlphaDummy1129) ∈
      (((Class.cv (nb078AlphaDummy1130))).fv ∪ ((Class.cv (nb078AlphaDummy1129))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1247 :
    (nb078AlphaDummy1129) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1171)
              (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1130))
                (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                  (synCphi (Class.cv (nb078AlphaDummy1172)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1171)
              (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
                (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1171) from (by
          unfold nb078AlphaDummy1171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1246) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1172) from (by
            unfold nb078AlphaDummy1172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1246) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1248 (h : Var) :
    (nb078AlphaDummy1131 h) ∈
      (((Class.cv (nb078AlphaDummy1132 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1131 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1249 (h : Var) :
    (nb078AlphaDummy1131 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1173 h)
              (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1132 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                  (synCphi (Class.cv (nb078AlphaDummy1174 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1173 h)
              (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1173 h) from (by
          unfold nb078AlphaDummy1173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1248 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1174 h) from (by
            unfold nb078AlphaDummy1174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1248 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1250 :
    (nb078AlphaDummy1129) ∈
      (((Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1171)
            (synWrex (nb078AlphaDummy1172) (Class.cv (nb078AlphaDummy1129))
              (Wff.classEq (Class.cv (nb078AlphaDummy1171))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1172)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1171) from (by
          unfold nb078AlphaDummy1171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1246) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1129) ≠ (nb078AlphaDummy1172) from (by
            unfold nb078AlphaDummy1172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1246) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1251 (h : Var) :
    (nb078AlphaDummy1131 h) ∈
      (((Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1173 h)
            (synWrex (nb078AlphaDummy1174 h) (Class.cv (nb078AlphaDummy1131 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1173 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1174 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1173 h) from (by
          unfold nb078AlphaDummy1173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1248 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1131 h) ≠ (nb078AlphaDummy1174 h) from (by
            unfold nb078AlphaDummy1174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1248 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1252 :
    (nb078AlphaDummy1172) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1172))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1253 (h : Var) :
    (nb078AlphaDummy1174 h) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1174 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1254 :
    (nb078AlphaDummy1172) ∈
      (((synCphi (Class.cv (nb078AlphaDummy1172)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1172)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1255 (h : Var) :
    (nb078AlphaDummy1174 h) ∈
      (((synCphi (Class.cv (nb078AlphaDummy1174 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1174 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1256 :
    (nb078AlphaDummy002) ∈
      (((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy002)))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))) (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv (nb078AlphaDummy002)))
              (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))) (synCid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1257 (h : Var) :
    h ∈
      (((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
            (synCid))).fv ∪
        ((synCnin (synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))
            (synCid))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1258 :
    (nb078AlphaDummy002) ∈
      (((synCcom (synCcnv (Class.cv (nb078AlphaDummy002)))
            (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002)))))).fv ∪ ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1259 (h : Var) :
    h ∈
      (((synCcom (synCcnv (Class.cv h)) (synCcnv (synCcnv (Class.cv h))))).fv ∪
        ((synCid)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccom]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1260 :
    (nb078AlphaDummy002) ∈
      (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv ∪
        ((synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1261 :
    (nb078AlphaDummy002) ∈
      (({(nb078AlphaDummy1049)} : Finset Var) ∪ ({(nb078AlphaDummy1050)} : Finset Var) ∪
        ((synWex (nb078AlphaDummy1051) (synWa (synWbr (Class.cv (nb078AlphaDummy1049))
                (synCcnv (synCcnv (Class.cv (nb078AlphaDummy002))))
                (Class.cv (nb078AlphaDummy1051)))
              (synWbr (Class.cv (nb078AlphaDummy1051))
                (synCcnv (Class.cv (nb078AlphaDummy002)))
                (Class.cv (nb078AlphaDummy1050)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy002) ≠ (nb078AlphaDummy1051) from (by
          unfold nb078AlphaDummy1051;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1260) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_1262 (h : Var) :
    h ∈ (((synCcnv (Class.cv h))).fv ∪ ((synCcnv (synCcnv (Class.cv h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1263 (h : Var) :
    h ∈
      (({(nb078AlphaDummy1052 h)} : Finset Var) ∪
          ({(nb078AlphaDummy1053 h)} : Finset Var) ∪ ((synWex (nb078AlphaDummy1054 h)
            (synWa (synWbr (Class.cv (nb078AlphaDummy1052 h))
                (synCcnv (synCcnv (Class.cv h))) (Class.cv (nb078AlphaDummy1054 h)))
              (synWbr (Class.cv (nb078AlphaDummy1054 h)) (synCcnv (Class.cv h))
                (Class.cv (nb078AlphaDummy1053 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb078AlphaDummy1054 h) from (by
          unfold nb078AlphaDummy1054;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1262 h) 2))))
  · rw [fv_syn_wa]
    with_reducible rw [Finset.mem_union]
    left
    rw [fv_syn_wbr]
    with_reducible rw [Finset.mem_union]
    right
    rw [fv_syn_ccnv]
    rw [fv_syn_ccnv]
    rw [fv_class_cv]
    exact Finset.mem_singleton_self _

theorem nb078_support_mem_1264 :
    (nb078AlphaDummy002) ∈
      (({(nb078AlphaDummy1129)} : Finset Var) ∪ ({(nb078AlphaDummy1130)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy1130))
            (synCcnv (Class.cv (nb078AlphaDummy002)))
            (Class.cv (nb078AlphaDummy1129)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1265 (h : Var) :
    h ∈
      (({(nb078AlphaDummy1131 h)} : Finset Var) ∪
          ({(nb078AlphaDummy1132 h)} : Finset Var) ∪
        ((synWbr (Class.cv (nb078AlphaDummy1132 h)) (synCcnv (Class.cv h))
            (Class.cv (nb078AlphaDummy1131 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wbr]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1266 :
    (nb078AlphaDummy002) ∈ (((synCcnv (Class.cv (nb078AlphaDummy002)))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1267 (h : Var) : h ∈ (((synCcnv (Class.cv h))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1268 :
    (nb078AlphaDummy1051) ∈
      (((Class.cv (nb078AlphaDummy1051))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1269 :
    (nb078AlphaDummy1051) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1207)
              (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
                (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                  (synCphi (Class.cv (nb078AlphaDummy1208)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1207)
              (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
                (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1207) from (by
          unfold nb078AlphaDummy1207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1208) from (by
            unfold nb078AlphaDummy1208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1270 (h : Var) :
    (nb078AlphaDummy1054 h) ∈
      (((Class.cv (nb078AlphaDummy1054 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1271 (h : Var) :
    (nb078AlphaDummy1054 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1209 h)
              (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                  (synCphi (Class.cv (nb078AlphaDummy1210 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1209 h)
              (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1209 h) from (by
          unfold nb078AlphaDummy1209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1210 h) from (by
            unfold nb078AlphaDummy1210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1272 :
    (nb078AlphaDummy1051) ∈
      (((Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCphi (Class.cv (nb078AlphaDummy1208))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCphi (Class.cv (nb078AlphaDummy1208))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1207) from (by
          unfold nb078AlphaDummy1207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1051) ≠ (nb078AlphaDummy1208) from (by
            unfold nb078AlphaDummy1208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1273 (h : Var) :
    (nb078AlphaDummy1054 h) ∈
      (((Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCphi (Class.cv (nb078AlphaDummy1210 h))))))).fv ∪
        ((Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCphi (Class.cv (nb078AlphaDummy1210 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1209 h) from (by
          unfold nb078AlphaDummy1209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1054 h) ≠ (nb078AlphaDummy1210 h) from (by
            unfold nb078AlphaDummy1210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1274 :
    (nb078AlphaDummy1208) ∈ (((Class.cv (nb078AlphaDummy1208))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1275 (h : Var) :
    (nb078AlphaDummy1210 h) ∈ (((Class.cv (nb078AlphaDummy1210 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1276 :
    (nb078AlphaDummy1215) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy1215)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1215)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1215))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1277 (h : Var) :
    (nb078AlphaDummy1217 h) ∈
      (((Wff.classMem (Class.cv (nb078AlphaDummy1217 h)) (synCnnc))).fv ∪
          ((synCplc (Class.cv (nb078AlphaDummy1217 h)) (synC1c))).fv ∪
        ((Class.cv (nb078AlphaDummy1217 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_wff_classMem]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1278 :
    (nb078AlphaDummy1215) ∈
      (((Class.cv (nb078AlphaDummy1215))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1279 (h : Var) :
    (nb078AlphaDummy1217 h) ∈
      (((Class.cv (nb078AlphaDummy1217 h))).fv ∪ ((synC1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1280 :
    (nb078AlphaDummy1222) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1222)) (Class.cv (nb078AlphaDummy1223)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1222))
            (Class.cv (nb078AlphaDummy1223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1281 (h : Var) :
    (nb078AlphaDummy1225 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1225 h))
            (Class.cv (nb078AlphaDummy1226 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1225 h))
            (Class.cv (nb078AlphaDummy1226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1282 :
    (nb078AlphaDummy1222) ∈
      (((Class.cv (nb078AlphaDummy1222))).fv ∪ ((Class.cv (nb078AlphaDummy1223))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1283 (h : Var) :
    (nb078AlphaDummy1225 h) ∈
      (((Class.cv (nb078AlphaDummy1225 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1226 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1284 :
    (nb078AlphaDummy1223) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1222)) (Class.cv (nb078AlphaDummy1223)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1222))
            (Class.cv (nb078AlphaDummy1223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1285 (h : Var) :
    (nb078AlphaDummy1226 h) ∈
      (((synCnin (Class.cv (nb078AlphaDummy1225 h))
            (Class.cv (nb078AlphaDummy1226 h)))).fv ∪
        ((synCnin (Class.cv (nb078AlphaDummy1225 h))
            (Class.cv (nb078AlphaDummy1226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1286 :
    (nb078AlphaDummy1223) ∈
      (((Class.cv (nb078AlphaDummy1222))).fv ∪ ((Class.cv (nb078AlphaDummy1223))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1287 (h : Var) :
    (nb078AlphaDummy1226 h) ∈
      (((Class.cv (nb078AlphaDummy1225 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1226 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1288 :
    (nb078AlphaDummy1222) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1222)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1289 (h : Var) :
    (nb078AlphaDummy1225 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1225 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1290 :
    (nb078AlphaDummy1222) ∈
      (((Class.cv (nb078AlphaDummy1222))).fv ∪ ((Class.cv (nb078AlphaDummy1222))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1291 (h : Var) :
    (nb078AlphaDummy1225 h) ∈
      (((Class.cv (nb078AlphaDummy1225 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1225 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1292 :
    (nb078AlphaDummy1223) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1222)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1293 (h : Var) :
    (nb078AlphaDummy1226 h) ∈
      (((synCcompl (Class.cv (nb078AlphaDummy1225 h)))).fv ∪
        ((synCcompl (Class.cv (nb078AlphaDummy1226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1294 :
    (nb078AlphaDummy1223) ∈
      (((Class.cv (nb078AlphaDummy1223))).fv ∪ ((Class.cv (nb078AlphaDummy1223))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1295 (h : Var) :
    (nb078AlphaDummy1226 h) ∈
      (((Class.cv (nb078AlphaDummy1226 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1226 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1296 :
    (nb078AlphaDummy1050) ∈
      (((Class.cv (nb078AlphaDummy1051))).fv ∪ ((Class.cv (nb078AlphaDummy1050))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1297 :
    (nb078AlphaDummy1050) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1207)
              (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1051))
                (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                  (synCphi (Class.cv (nb078AlphaDummy1208)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1207)
              (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
                (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1207) from (by
          unfold nb078AlphaDummy1207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1296) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1208) from (by
            unfold nb078AlphaDummy1208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1296) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1298 (h : Var) :
    (nb078AlphaDummy1053 h) ∈
      (((Class.cv (nb078AlphaDummy1054 h))).fv ∪
        ((Class.cv (nb078AlphaDummy1053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1299 (h : Var) :
    (nb078AlphaDummy1053 h) ∈
      (((synCcompl (Class.cab (nb078AlphaDummy1209 h)
              (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1054 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                  (synCphi (Class.cv (nb078AlphaDummy1210 h)))))))).fv ∪ ((synCcompl
            (Class.cab (nb078AlphaDummy1209 h)
              (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
                (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                  (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                    (synCsn (synC0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1053 h) ≠ (nb078AlphaDummy1209 h) from (by
          unfold nb078AlphaDummy1209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1298 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1053 h) ≠ (nb078AlphaDummy1210 h) from (by
            unfold nb078AlphaDummy1210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1298 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1300 :
    (nb078AlphaDummy1050) ∈
      (((Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1207)
            (synWrex (nb078AlphaDummy1208) (Class.cv (nb078AlphaDummy1050))
              (Wff.classEq (Class.cv (nb078AlphaDummy1207))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1208)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1207) from (by
          unfold nb078AlphaDummy1207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1296) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1050) ≠ (nb078AlphaDummy1208) from (by
            unfold nb078AlphaDummy1208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1296) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end

/-! Certificates from `NAR4C078C001Part031`. -/


section

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

theorem nb078_support_mem_1301 (h : Var) :
    (nb078AlphaDummy1053 h) ∈
      (((Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                  (synCsn (synC0c))))))).fv ∪ ((Class.cab (nb078AlphaDummy1209 h)
            (synWrex (nb078AlphaDummy1210 h) (Class.cv (nb078AlphaDummy1053 h))
              (Wff.classEq (Class.cv (nb078AlphaDummy1209 h))
                (synCun (synCphi (Class.cv (nb078AlphaDummy1210 h)))
                  (synCsn (synC0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078AlphaDummy1053 h) ≠ (nb078AlphaDummy1209 h) from (by
          unfold nb078AlphaDummy1209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1298 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078AlphaDummy1053 h) ≠ (nb078AlphaDummy1210 h) from (by
            unfold nb078AlphaDummy1210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1298 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1302 :
    (nb078AlphaDummy1208) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1208))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1303 (h : Var) :
    (nb078AlphaDummy1210 h) ∈
      (((synCcompl (synCphi (Class.cv (nb078AlphaDummy1210 h))))).fv ∪
        ((synCcompl (synCsn (synC0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1304 :
    (nb078AlphaDummy1208) ∈
      (((synCphi (Class.cv (nb078AlphaDummy1208)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1208)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1305 (h : Var) :
    (nb078AlphaDummy1210 h) ∈
      (((synCphi (Class.cv (nb078AlphaDummy1210 h)))).fv ∪
        ((synCphi (Class.cv (nb078AlphaDummy1210 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_compact_fv_empty_0026 : (nb078AlphaDummy007) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0027 (f : Var) :
    (nb078AlphaDummy008 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0028 : (nb078AlphaDummy005) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0029 (f : Var) :
    (nb078AlphaDummy006 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0030 : (nb078AlphaDummy000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0031 (f : Var) : f ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0032 : (nb078AlphaDummy004) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0033 (y : Var) : y ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0034 : (nb078AlphaDummy003) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0035 (x : Var) : x ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
