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
    (nb078_alpha_dummy_1112 h) ∈
      (((Class.cv (nb078_alpha_dummy_1112 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1112 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1166 :
    (nb078_alpha_dummy_1051) ∈
      (((Class.cv (nb078_alpha_dummy_1049))).fv ∪ ((Class.cv (nb078_alpha_dummy_1051))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1167 :
    (nb078_alpha_dummy_1051) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1093)
              (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1049))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1093)
              (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1093) from (by
          unfold nb078_alpha_dummy_1093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1166) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1094) from (by
            unfold nb078_alpha_dummy_1094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1166) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1168 (h : Var) :
    (nb078_alpha_dummy_1054 h) ∈
      (((Class.cv (nb078_alpha_dummy_1052 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1054 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1169 (h : Var) :
    (nb078_alpha_dummy_1054 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1095 h)
              (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1052 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1095 h)
              (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1095 h) from (by
          unfold nb078_alpha_dummy_1095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1168 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1096 h) from (by
            unfold nb078_alpha_dummy_1096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1168 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1170 :
    (nb078_alpha_dummy_1051) ∈
      (((Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1093)
            (syn_wrex (nb078_alpha_dummy_1094) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1093))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1094)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1093) from (by
          unfold nb078_alpha_dummy_1093;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1166) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1094) from (by
            unfold nb078_alpha_dummy_1094;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1166) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1171 (h : Var) :
    (nb078_alpha_dummy_1054 h) ∈
      (((Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1095 h)
            (syn_wrex (nb078_alpha_dummy_1096 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1095 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1095 h) from (by
          unfold nb078_alpha_dummy_1095;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1168 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1096 h) from (by
            unfold nb078_alpha_dummy_1096;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1168 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1172 :
    (nb078_alpha_dummy_1094) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1094))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1173 (h : Var) :
    (nb078_alpha_dummy_1096 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1096 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1174 :
    (nb078_alpha_dummy_1094) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1094)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1175 (h : Var) :
    (nb078_alpha_dummy_1096 h) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1096 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1176 :
    (nb078_alpha_dummy_1129) ∈
      (({(nb078_alpha_dummy_1129)} : Finset Var) ∪ ({(nb078_alpha_dummy_1130)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_1130))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_1129)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1177 (h : Var) :
    (nb078_alpha_dummy_1131 h) ∈
      (({(nb078_alpha_dummy_1131 h)} : Finset Var) ∪
          ({(nb078_alpha_dummy_1132 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_1132 h)) (syn_ccnv (Class.cv h))
            (Class.cv (nb078_alpha_dummy_1131 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  left
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1178 :
    (nb078_alpha_dummy_1130) ∈
      (({(nb078_alpha_dummy_1129)} : Finset Var) ∪ ({(nb078_alpha_dummy_1130)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_1130))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_1129)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1179 (h : Var) :
    (nb078_alpha_dummy_1132 h) ∈
      (({(nb078_alpha_dummy_1131 h)} : Finset Var) ∪
          ({(nb078_alpha_dummy_1132 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_1132 h)) (syn_ccnv (Class.cv h))
            (Class.cv (nb078_alpha_dummy_1131 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  with_reducible rw [Finset.mem_union]
  right
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1180 :
    (nb078_alpha_dummy_1129) ∈
      (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1181 :
    (nb078_alpha_dummy_1129) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1135)
              (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1135)
              (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1135) from (by
          unfold nb078_alpha_dummy_1135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1136) from (by
            unfold nb078_alpha_dummy_1136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1182 (h : Var) :
    (nb078_alpha_dummy_1131 h) ∈
      (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1132 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1183 (h : Var) :
    (nb078_alpha_dummy_1131 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1137 h)
              (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1137 h)
              (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1137 h) from (by
          unfold nb078_alpha_dummy_1137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1182 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1138 h) from (by
            unfold nb078_alpha_dummy_1138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1182 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1184 :
    (nb078_alpha_dummy_1129) ∈
      (((Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1135) from (by
          unfold nb078_alpha_dummy_1135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1136) from (by
            unfold nb078_alpha_dummy_1136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1180) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1185 (h : Var) :
    (nb078_alpha_dummy_1131 h) ∈
      (((Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1137 h) from (by
          unfold nb078_alpha_dummy_1137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1182 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1138 h) from (by
            unfold nb078_alpha_dummy_1138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1182 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1186 :
    (nb078_alpha_dummy_1136) ∈ (((Class.cv (nb078_alpha_dummy_1136))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1187 (h : Var) :
    (nb078_alpha_dummy_1138 h) ∈ (((Class.cv (nb078_alpha_dummy_1138 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1188 :
    (nb078_alpha_dummy_1143) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1143)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1143)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1143))).fv) :=
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
    (nb078_alpha_dummy_1145 h) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1145 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1145 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1145 h))).fv) :=
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
    (nb078_alpha_dummy_1143) ∈
      (((Class.cv (nb078_alpha_dummy_1143))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1191 (h : Var) :
    (nb078_alpha_dummy_1145 h) ∈
      (((Class.cv (nb078_alpha_dummy_1145 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1192 :
    (nb078_alpha_dummy_1150) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1150)) (Class.cv (nb078_alpha_dummy_1151)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1150))
            (Class.cv (nb078_alpha_dummy_1151)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1193 (h : Var) :
    (nb078_alpha_dummy_1153 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h))
            (Class.cv (nb078_alpha_dummy_1154 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h))
            (Class.cv (nb078_alpha_dummy_1154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1194 :
    (nb078_alpha_dummy_1150) ∈
      (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1195 (h : Var) :
    (nb078_alpha_dummy_1153 h) ∈
      (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1154 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1196 :
    (nb078_alpha_dummy_1151) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1150)) (Class.cv (nb078_alpha_dummy_1151)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1150))
            (Class.cv (nb078_alpha_dummy_1151)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1197 (h : Var) :
    (nb078_alpha_dummy_1154 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h))
            (Class.cv (nb078_alpha_dummy_1154 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1153 h))
            (Class.cv (nb078_alpha_dummy_1154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1198 :
    (nb078_alpha_dummy_1151) ∈
      (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1199 (h : Var) :
    (nb078_alpha_dummy_1154 h) ∈
      (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1154 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1200 :
    (nb078_alpha_dummy_1150) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1150)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1151)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1201 (h : Var) :
    (nb078_alpha_dummy_1153 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1153 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1202 :
    (nb078_alpha_dummy_1150) ∈
      (((Class.cv (nb078_alpha_dummy_1150))).fv ∪ ((Class.cv (nb078_alpha_dummy_1150))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1203 (h : Var) :
    (nb078_alpha_dummy_1153 h) ∈
      (((Class.cv (nb078_alpha_dummy_1153 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1153 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1204 :
    (nb078_alpha_dummy_1151) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1150)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1151)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1205 (h : Var) :
    (nb078_alpha_dummy_1154 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1153 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1154 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1206 :
    (nb078_alpha_dummy_1151) ∈
      (((Class.cv (nb078_alpha_dummy_1151))).fv ∪ ((Class.cv (nb078_alpha_dummy_1151))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1207 (h : Var) :
    (nb078_alpha_dummy_1154 h) ∈
      (((Class.cv (nb078_alpha_dummy_1154 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1154 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1208 :
    (nb078_alpha_dummy_1130) ∈
      (((Class.cv (nb078_alpha_dummy_1129))).fv ∪ ((Class.cv (nb078_alpha_dummy_1130))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1209 :
    (nb078_alpha_dummy_1130) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1135)
              (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1129))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1135)
              (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1135) from (by
          unfold nb078_alpha_dummy_1135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1208) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1136) from (by
            unfold nb078_alpha_dummy_1136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1208) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1210 (h : Var) :
    (nb078_alpha_dummy_1132 h) ∈
      (((Class.cv (nb078_alpha_dummy_1131 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1132 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1211 (h : Var) :
    (nb078_alpha_dummy_1132 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1137 h)
              (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1131 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1137 h)
              (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1137 h) from (by
          unfold nb078_alpha_dummy_1137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1210 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1138 h) from (by
            unfold nb078_alpha_dummy_1138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1210 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1212 :
    (nb078_alpha_dummy_1130) ∈
      (((Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1135)
            (syn_wrex (nb078_alpha_dummy_1136) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1135))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1136)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1135) from (by
          unfold nb078_alpha_dummy_1135;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1208) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1136) from (by
            unfold nb078_alpha_dummy_1136;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1208) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1213 (h : Var) :
    (nb078_alpha_dummy_1132 h) ∈
      (((Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1137 h)
            (syn_wrex (nb078_alpha_dummy_1138 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1137 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1137 h) from (by
          unfold nb078_alpha_dummy_1137;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1210 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1138 h) from (by
            unfold nb078_alpha_dummy_1138;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1210 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1214 :
    (nb078_alpha_dummy_1136) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1136))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1215 (h : Var) :
    (nb078_alpha_dummy_1138 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1138 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1216 :
    (nb078_alpha_dummy_1136) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1136)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1217 (h : Var) :
    (nb078_alpha_dummy_1138 h) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1138 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1218 :
    (nb078_alpha_dummy_1130) ∈
      (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1219 :
    (nb078_alpha_dummy_1130) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1171)
              (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1171)
              (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1171) from (by
          unfold nb078_alpha_dummy_1171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1172) from (by
            unfold nb078_alpha_dummy_1172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1220 (h : Var) :
    (nb078_alpha_dummy_1132 h) ∈
      (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1131 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1221 (h : Var) :
    (nb078_alpha_dummy_1132 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1173 h)
              (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1173 h)
              (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1173 h) from (by
          unfold nb078_alpha_dummy_1173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1220 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1174 h) from (by
            unfold nb078_alpha_dummy_1174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1220 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1222 :
    (nb078_alpha_dummy_1130) ∈
      (((Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1171) from (by
          unfold nb078_alpha_dummy_1171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1130) ≠ (nb078_alpha_dummy_1172) from (by
            unfold nb078_alpha_dummy_1172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1218) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1223 (h : Var) :
    (nb078_alpha_dummy_1132 h) ∈
      (((Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1173 h) from (by
          unfold nb078_alpha_dummy_1173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1220 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1132 h) ≠ (nb078_alpha_dummy_1174 h) from (by
            unfold nb078_alpha_dummy_1174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1220 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1224 :
    (nb078_alpha_dummy_1172) ∈ (((Class.cv (nb078_alpha_dummy_1172))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1225 (h : Var) :
    (nb078_alpha_dummy_1174 h) ∈ (((Class.cv (nb078_alpha_dummy_1174 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1226 :
    (nb078_alpha_dummy_1179) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1179)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1179)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1179))).fv) :=
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
    (nb078_alpha_dummy_1181 h) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1181 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1181 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1181 h))).fv) :=
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
    (nb078_alpha_dummy_1179) ∈
      (((Class.cv (nb078_alpha_dummy_1179))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1229 (h : Var) :
    (nb078_alpha_dummy_1181 h) ∈
      (((Class.cv (nb078_alpha_dummy_1181 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1230 :
    (nb078_alpha_dummy_1186) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1186)) (Class.cv (nb078_alpha_dummy_1187)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1186))
            (Class.cv (nb078_alpha_dummy_1187)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1231 (h : Var) :
    (nb078_alpha_dummy_1189 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h))
            (Class.cv (nb078_alpha_dummy_1190 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h))
            (Class.cv (nb078_alpha_dummy_1190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1232 :
    (nb078_alpha_dummy_1186) ∈
      (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1233 (h : Var) :
    (nb078_alpha_dummy_1189 h) ∈
      (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1190 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1234 :
    (nb078_alpha_dummy_1187) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1186)) (Class.cv (nb078_alpha_dummy_1187)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1186))
            (Class.cv (nb078_alpha_dummy_1187)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1235 (h : Var) :
    (nb078_alpha_dummy_1190 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h))
            (Class.cv (nb078_alpha_dummy_1190 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1189 h))
            (Class.cv (nb078_alpha_dummy_1190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1236 :
    (nb078_alpha_dummy_1187) ∈
      (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1237 (h : Var) :
    (nb078_alpha_dummy_1190 h) ∈
      (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1190 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1238 :
    (nb078_alpha_dummy_1186) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1186)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1187)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1239 (h : Var) :
    (nb078_alpha_dummy_1189 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1189 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1240 :
    (nb078_alpha_dummy_1186) ∈
      (((Class.cv (nb078_alpha_dummy_1186))).fv ∪ ((Class.cv (nb078_alpha_dummy_1186))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1241 (h : Var) :
    (nb078_alpha_dummy_1189 h) ∈
      (((Class.cv (nb078_alpha_dummy_1189 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1189 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1242 :
    (nb078_alpha_dummy_1187) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1186)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1187)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1243 (h : Var) :
    (nb078_alpha_dummy_1190 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1189 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1190 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1244 :
    (nb078_alpha_dummy_1187) ∈
      (((Class.cv (nb078_alpha_dummy_1187))).fv ∪ ((Class.cv (nb078_alpha_dummy_1187))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1245 (h : Var) :
    (nb078_alpha_dummy_1190 h) ∈
      (((Class.cv (nb078_alpha_dummy_1190 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1190 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1246 :
    (nb078_alpha_dummy_1129) ∈
      (((Class.cv (nb078_alpha_dummy_1130))).fv ∪ ((Class.cv (nb078_alpha_dummy_1129))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1247 :
    (nb078_alpha_dummy_1129) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1171)
              (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1130))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1171)
              (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1171) from (by
          unfold nb078_alpha_dummy_1171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1246) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1172) from (by
            unfold nb078_alpha_dummy_1172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1246) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1248 (h : Var) :
    (nb078_alpha_dummy_1131 h) ∈
      (((Class.cv (nb078_alpha_dummy_1132 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1131 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1249 (h : Var) :
    (nb078_alpha_dummy_1131 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1173 h)
              (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1132 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1173 h)
              (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1173 h) from (by
          unfold nb078_alpha_dummy_1173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1248 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1174 h) from (by
            unfold nb078_alpha_dummy_1174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1248 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1250 :
    (nb078_alpha_dummy_1129) ∈
      (((Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1171)
            (syn_wrex (nb078_alpha_dummy_1172) (Class.cv (nb078_alpha_dummy_1129))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1171))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1172)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1171) from (by
          unfold nb078_alpha_dummy_1171;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1246) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1129) ≠ (nb078_alpha_dummy_1172) from (by
            unfold nb078_alpha_dummy_1172;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1246) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1251 (h : Var) :
    (nb078_alpha_dummy_1131 h) ∈
      (((Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1173 h)
            (syn_wrex (nb078_alpha_dummy_1174 h) (Class.cv (nb078_alpha_dummy_1131 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1173 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1173 h) from (by
          unfold nb078_alpha_dummy_1173;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1248 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1131 h) ≠ (nb078_alpha_dummy_1174 h) from (by
            unfold nb078_alpha_dummy_1174;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1248 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1252 :
    (nb078_alpha_dummy_1172) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1172))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1253 (h : Var) :
    (nb078_alpha_dummy_1174 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1174 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1254 :
    (nb078_alpha_dummy_1172) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1172)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1172)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1255 (h : Var) :
    (nb078_alpha_dummy_1174 h) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1174 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1256 :
    (nb078_alpha_dummy_002) ∈
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
              (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))) (syn_cid))).fv) :=
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
      (((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
            (syn_cid))).fv ∪
        ((syn_cnin (syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))
            (syn_cid))).fv) :=
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
    (nb078_alpha_dummy_002) ∈
      (((syn_ccom (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
            (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))))).fv ∪ ((syn_cid)).fv) :=
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
      (((syn_ccom (syn_ccnv (Class.cv h)) (syn_ccnv (syn_ccnv (Class.cv h))))).fv ∪
        ((syn_cid)).fv) :=
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
    (nb078_alpha_dummy_002) ∈
      (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv ∪
        ((syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1261 :
    (nb078_alpha_dummy_002) ∈
      (({(nb078_alpha_dummy_1049)} : Finset Var) ∪ ({(nb078_alpha_dummy_1050)} : Finset Var) ∪
        ((syn_wex (nb078_alpha_dummy_1051) (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1049))
                (syn_ccnv (syn_ccnv (Class.cv (nb078_alpha_dummy_002))))
                (Class.cv (nb078_alpha_dummy_1051)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_1051))
                (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
                (Class.cv (nb078_alpha_dummy_1050)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_002) ≠ (nb078_alpha_dummy_1051) from (by
          unfold nb078_alpha_dummy_1051;
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
    h ∈ (((syn_ccnv (Class.cv h))).fv ∪ ((syn_ccnv (syn_ccnv (Class.cv h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1263 (h : Var) :
    h ∈
      (({(nb078_alpha_dummy_1052 h)} : Finset Var) ∪
          ({(nb078_alpha_dummy_1053 h)} : Finset Var) ∪ ((syn_wex (nb078_alpha_dummy_1054 h)
            (syn_wa (syn_wbr (Class.cv (nb078_alpha_dummy_1052 h))
                (syn_ccnv (syn_ccnv (Class.cv h))) (Class.cv (nb078_alpha_dummy_1054 h)))
              (syn_wbr (Class.cv (nb078_alpha_dummy_1054 h)) (syn_ccnv (Class.cv h))
                (Class.cv (nb078_alpha_dummy_1053 h)))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_wex]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show h ≠ (nb078_alpha_dummy_1054 h) from (by
          unfold nb078_alpha_dummy_1054;
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
    (nb078_alpha_dummy_002) ∈
      (({(nb078_alpha_dummy_1129)} : Finset Var) ∪ ({(nb078_alpha_dummy_1130)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_1130))
            (syn_ccnv (Class.cv (nb078_alpha_dummy_002)))
            (Class.cv (nb078_alpha_dummy_1129)))).fv) :=
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
      (({(nb078_alpha_dummy_1131 h)} : Finset Var) ∪
          ({(nb078_alpha_dummy_1132 h)} : Finset Var) ∪
        ((syn_wbr (Class.cv (nb078_alpha_dummy_1132 h)) (syn_ccnv (Class.cv h))
            (Class.cv (nb078_alpha_dummy_1131 h)))).fv) :=
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
    (nb078_alpha_dummy_002) ∈ (((syn_ccnv (Class.cv (nb078_alpha_dummy_002)))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1267 (h : Var) : h ∈ (((syn_ccnv (Class.cv h))).fv) :=
  by
  rw [fv_syn_ccnv]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1268 :
    (nb078_alpha_dummy_1051) ∈
      (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1269 :
    (nb078_alpha_dummy_1051) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1207)
              (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1207)
              (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1207) from (by
          unfold nb078_alpha_dummy_1207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1208) from (by
            unfold nb078_alpha_dummy_1208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1270 (h : Var) :
    (nb078_alpha_dummy_1054 h) ∈
      (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1271 (h : Var) :
    (nb078_alpha_dummy_1054 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1209 h)
              (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1209 h)
              (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1209 h) from (by
          unfold nb078_alpha_dummy_1209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1210 h) from (by
            unfold nb078_alpha_dummy_1210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1272 :
    (nb078_alpha_dummy_1051) ∈
      (((Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1207) from (by
          unfold nb078_alpha_dummy_1207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1051) ≠ (nb078_alpha_dummy_1208) from (by
            unfold nb078_alpha_dummy_1208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1268) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1273 (h : Var) :
    (nb078_alpha_dummy_1054 h) ∈
      (((Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))))).fv ∪
        ((Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1209 h) from (by
          unfold nb078_alpha_dummy_1209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1054 h) ≠ (nb078_alpha_dummy_1210 h) from (by
            unfold nb078_alpha_dummy_1210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1270 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1274 :
    (nb078_alpha_dummy_1208) ∈ (((Class.cv (nb078_alpha_dummy_1208))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1275 (h : Var) :
    (nb078_alpha_dummy_1210 h) ∈ (((Class.cv (nb078_alpha_dummy_1210 h))).fv) :=
  by
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1276 :
    (nb078_alpha_dummy_1215) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1215)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1215)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1215))).fv) :=
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
    (nb078_alpha_dummy_1217 h) ∈
      (((Wff.classMem (Class.cv (nb078_alpha_dummy_1217 h)) (syn_cnnc))).fv ∪
          ((syn_cplc (Class.cv (nb078_alpha_dummy_1217 h)) (syn_c1c))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1217 h))).fv) :=
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
    (nb078_alpha_dummy_1215) ∈
      (((Class.cv (nb078_alpha_dummy_1215))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1279 (h : Var) :
    (nb078_alpha_dummy_1217 h) ∈
      (((Class.cv (nb078_alpha_dummy_1217 h))).fv ∪ ((syn_c1c)).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1280 :
    (nb078_alpha_dummy_1222) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1222)) (Class.cv (nb078_alpha_dummy_1223)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1222))
            (Class.cv (nb078_alpha_dummy_1223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1281 (h : Var) :
    (nb078_alpha_dummy_1225 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h))
            (Class.cv (nb078_alpha_dummy_1226 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h))
            (Class.cv (nb078_alpha_dummy_1226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1282 :
    (nb078_alpha_dummy_1222) ∈
      (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1283 (h : Var) :
    (nb078_alpha_dummy_1225 h) ∈
      (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1226 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1284 :
    (nb078_alpha_dummy_1223) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1222)) (Class.cv (nb078_alpha_dummy_1223)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1222))
            (Class.cv (nb078_alpha_dummy_1223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1285 (h : Var) :
    (nb078_alpha_dummy_1226 h) ∈
      (((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h))
            (Class.cv (nb078_alpha_dummy_1226 h)))).fv ∪
        ((syn_cnin (Class.cv (nb078_alpha_dummy_1225 h))
            (Class.cv (nb078_alpha_dummy_1226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cnin]
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1286 :
    (nb078_alpha_dummy_1223) ∈
      (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1287 (h : Var) :
    (nb078_alpha_dummy_1226 h) ∈
      (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1226 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1288 :
    (nb078_alpha_dummy_1222) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1222)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1289 (h : Var) :
    (nb078_alpha_dummy_1225 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1225 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1290 :
    (nb078_alpha_dummy_1222) ∈
      (((Class.cv (nb078_alpha_dummy_1222))).fv ∪ ((Class.cv (nb078_alpha_dummy_1222))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1291 (h : Var) :
    (nb078_alpha_dummy_1225 h) ∈
      (((Class.cv (nb078_alpha_dummy_1225 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1225 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1292 :
    (nb078_alpha_dummy_1223) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1222)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1223)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1293 (h : Var) :
    (nb078_alpha_dummy_1226 h) ∈
      (((syn_ccompl (Class.cv (nb078_alpha_dummy_1225 h)))).fv ∪
        ((syn_ccompl (Class.cv (nb078_alpha_dummy_1226 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1294 :
    (nb078_alpha_dummy_1223) ∈
      (((Class.cv (nb078_alpha_dummy_1223))).fv ∪ ((Class.cv (nb078_alpha_dummy_1223))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1295 (h : Var) :
    (nb078_alpha_dummy_1226 h) ∈
      (((Class.cv (nb078_alpha_dummy_1226 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1226 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1296 :
    (nb078_alpha_dummy_1050) ∈
      (((Class.cv (nb078_alpha_dummy_1051))).fv ∪ ((Class.cv (nb078_alpha_dummy_1050))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1297 :
    (nb078_alpha_dummy_1050) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1207)
              (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1051))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1207)
              (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1207) from (by
          unfold nb078_alpha_dummy_1207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1296) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1208) from (by
            unfold nb078_alpha_dummy_1208;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1296) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1298 (h : Var) :
    (nb078_alpha_dummy_1053 h) ∈
      (((Class.cv (nb078_alpha_dummy_1054 h))).fv ∪
        ((Class.cv (nb078_alpha_dummy_1053 h))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1299 (h : Var) :
    (nb078_alpha_dummy_1053 h) ∈
      (((syn_ccompl (Class.cab (nb078_alpha_dummy_1209 h)
              (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1054 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                  (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))))))).fv ∪ ((syn_ccompl
            (Class.cab (nb078_alpha_dummy_1209 h)
              (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
                (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                  (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                    (syn_csn (syn_c0c)))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  right
  rw [fv_syn_ccompl]
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1209 h) from (by
          unfold nb078_alpha_dummy_1209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1298 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1210 h) from (by
            unfold nb078_alpha_dummy_1210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1298 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1300 :
    (nb078_alpha_dummy_1050) ∈
      (((Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1207)
            (syn_wrex (nb078_alpha_dummy_1208) (Class.cv (nb078_alpha_dummy_1050))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1207))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1208)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1207) from (by
          unfold nb078_alpha_dummy_1207;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1296) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1050) ≠ (nb078_alpha_dummy_1208) from (by
            unfold nb078_alpha_dummy_1208;
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
    (nb078_alpha_dummy_1053 h) ∈
      (((Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                  (syn_csn (syn_c0c))))))).fv ∪ ((Class.cab (nb078_alpha_dummy_1209 h)
            (syn_wrex (nb078_alpha_dummy_1210 h) (Class.cv (nb078_alpha_dummy_1053 h))
              (Wff.classEq (Class.cv (nb078_alpha_dummy_1209 h))
                (syn_cun (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))
                  (syn_csn (syn_c0c))))))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_class_cab]
  with_reducible rw [Finset.mem_erase]
  constructor
  · exact
      (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1209 h) from (by
          unfold nb078_alpha_dummy_1209;
          with_reducible
            exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1298 h) 0))))
  · rw [fv_syn_wrex]
    with_reducible rw [Finset.mem_union]
    left
    with_reducible rw [Finset.mem_erase]
    constructor
    · exact
        (show (nb078_alpha_dummy_1053 h) ≠ (nb078_alpha_dummy_1210 h) from (by
            unfold nb078_alpha_dummy_1210;
            with_reducible
              exact (Nat.ne_of_lt (mem_lt_freshVar (nb078_support_mem_1298 h) 1))))
    · rw [fv_class_cv]
      exact Finset.mem_singleton_self _

theorem nb078_support_mem_1302 :
    (nb078_alpha_dummy_1208) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1208))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1303 (h : Var) :
    (nb078_alpha_dummy_1210 h) ∈
      (((syn_ccompl (syn_cphi (Class.cv (nb078_alpha_dummy_1210 h))))).fv ∪
        ((syn_ccompl (syn_csn (syn_c0c)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_ccompl]
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1304 :
    (nb078_alpha_dummy_1208) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1208)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_support_mem_1305 (h : Var) :
    (nb078_alpha_dummy_1210 h) ∈
      (((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv ∪
        ((syn_cphi (Class.cv (nb078_alpha_dummy_1210 h)))).fv) :=
  by
  with_reducible rw [Finset.mem_union]
  left
  rw [fv_syn_cphi]
  rw [fv_class_cv]
  exact Finset.mem_singleton_self _

theorem nb078_compact_fv_empty_0026 : (nb078_alpha_dummy_007) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0027 (f : Var) :
    (nb078_alpha_dummy_008 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0028 : (nb078_alpha_dummy_005) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0029 (f : Var) :
    (nb078_alpha_dummy_006 f) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0030 : (nb078_alpha_dummy_000) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0031 (f : Var) : f ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0032 : (nb078_alpha_dummy_004) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0033 (y : Var) : y ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0034 : (nb078_alpha_dummy_003) ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem

theorem nb078_compact_fv_empty_0035 (x : Var) : x ∉ (∅ : Finset Var) :=
  by
  intro hmem
  cases hmem


end NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired

end
