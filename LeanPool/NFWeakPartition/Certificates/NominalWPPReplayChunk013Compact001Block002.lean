/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block001

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part006`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_brpprod (x : Var) (y : Var) (z : Var) (w : Var) (A : Class)
    (B : Class) (R : Class) (S : Class) (dv_A_w : w ∉ A.fv) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_A_z : z ∉ A.fv) (dv_B_w : w ∉ B.fv) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_R_w : w ∉ R.fv) (dv_R_x : x ∉ R.fv)
    (dv_R_y : y ∉ R.fv) (dv_R_z : z ∉ R.fv) (dv_S_w : w ∉ S.fv) (dv_S_x : x ∉ S.fv)
    (dv_S_y : y ∉ S.fv) (dv_S_z : z ∉ S.fv) (dv_w_x : w ≠ x) (dv_w_y : w ≠ y)
    (dv_w_z : w ≠ z) (dv_x_y : x ≠ y) (dv_x_z : x ≠ z) (dv_y_z : y ≠ z) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cpprod R S) B) (syn_wex x (syn_wex y (syn_wex z (syn_wex w
                (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y)))
                  (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wa (syn_wbr (.cv x) R (.cv z))
                    (syn_wbr (.cv y) S (.cv w))))))))) :=
  by
  have dv_cache_0001 : z ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_z, not_false_eq_true])
  have dv_cache_0002 : w ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_w, not_false_eq_true])
  have dv_cache_0003 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_z, not_false_eq_true])
  have dv_cache_0004 : w ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_w, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_ccom R (syn_c1st))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, dv_R_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : w ∉ ((syn_ccom R (syn_c1st))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union, dv_R_w,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : z ∉ ((syn_ccom S (syn_c2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, dv_S_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((syn_ccom S (syn_c2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union, dv_S_w,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show z ≠ w from (by exact Ne.symm dv_w_z))
  have dv_cache_0010 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_z,
          not_false_eq_true])
  have dv_cache_0012 : x ∉ (R).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_R_x, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_c1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0014 : x ∉ ((syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, (Ne.symm dv_w_x), dv_S_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0016 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_x_y), not_false_eq_true])
  have dv_cache_0017 : y ∉ ((syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, (Ne.symm dv_w_y), dv_S_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((syn_wbr (.cv x) R (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_y), dv_y_z, dv_R_y, or_false,
          not_false_eq_true])
  have dv_cache_0019 : x ∉ ((Wff.classEq B (syn_cop (.cv z) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_B_x, dv_x_z, (Ne.symm dv_w_x), or_false,
          not_false_eq_true])
  have dv_cache_0020 : y ∉ ((Wff.classEq B (syn_cop (.cv z) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_B_y, dv_y_z, (Ne.symm dv_w_y), or_false,
          not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (syn_cpprod R S))
  have p0001 :=
    @g_breqi A B (syn_cpprod R S)
      (syn_ctxp (syn_ccom R (syn_c1st)) (syn_ccom S (syn_c2nd))) p0000
  have p0002 :=
    @g_brtxp z w A B (syn_ccom R (syn_c1st)) (syn_ccom S (syn_c2nd)) dv_cache_0001
      dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0008 dv_cache_0009
  have p0003 :=
    @g_brco x A (.cv z) R (syn_c1st) dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013
  have p0004 :=
    @g_anbi1i (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z))
      (syn_wex x (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z))))
      (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)) p0003
  have p0005 :=
    @g_n_19_41v (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z)))
      (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)) x dv_cache_0014
  have p0006 :=
    @g_an32 (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z))
      (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))
  have p0007 := @g_vex x
  have p0008 := @g_br1st y A (.cv x) dv_cache_0015 dv_cache_0016 p0007
  have p0009 :=
    @g_anbi1i (syn_wbr A (syn_c1st) (.cv x))
      (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y))))
      (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)) p0008
  have p0010 :=
    @g_n_19_41v (.classEq A (syn_cop (.cv x) (.cv y)))
      (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)) y dv_cache_0017
  have p0011 := @g_breq1 A (syn_cop (.cv x) (.cv y)) (.cv w) (syn_ccom S (syn_c2nd))
  have p0012 := @g_vex y
  have p0013 := @g_brco2nd (.cv x) (.cv y) (.cv w) S p0007 p0012
  have p0014 :=
    @g_syl6bb (.classEq A (syn_cop (.cv x) (.cv y)))
      (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))
      (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_ccom S (syn_c2nd)) (.cv w))
      (syn_wbr (.cv y) S (.cv w)) p0011 p0013
  have p0015 :=
    @g_pm5_32i (.classEq A (syn_cop (.cv x) (.cv y)))
      (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)) (syn_wbr (.cv y) S (.cv w)) p0014
  have p0016 :=
    @g_exbii
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
        (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w))) y p0015
  have p0017 :=
    @g_n_3bitr2i
      (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))
      (syn_wa (syn_wex y (.classEq A (syn_cop (.cv x) (.cv y))))
        (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))
      (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
          (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))))
      (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w))))
      p0009 p0010 p0016
  have p0018 :=
    @g_anbi1i
      (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))
      (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w))))
      (syn_wbr (.cv x) R (.cv z)) p0017
  have p0019 :=
    @g_anass (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv z))
      (syn_wbr (.cv y) S (.cv w))
  have p0020 :=
    @g_an32 (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv z))
      (syn_wbr (.cv y) S (.cv w))
  have p0021 :=
    @g_bitr3i
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
        (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))
      (syn_wa (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv x) R (.cv z)))
        (syn_wbr (.cv y) S (.cv w)))
      (syn_wa (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w)))
        (syn_wbr (.cv x) R (.cv z)))
      p0019 p0020
  have p0022 :=
    @g_exbii
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
        (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))
      (syn_wa (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w)))
        (syn_wbr (.cv x) R (.cv z)))
      y p0021
  have p0023 :=
    @g_n_19_41v
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w)))
      (syn_wbr (.cv x) R (.cv z)) y dv_cache_0018
  have p0024 :=
    @g_bitr2i
      (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
          (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))
      (syn_wex y (syn_wa
          (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w)))
          (syn_wbr (.cv x) R (.cv z))))
      (syn_wa (syn_wex y
          (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w))))
        (syn_wbr (.cv x) R (.cv z)))
      p0022 p0023
  have p0025 :=
    @g_n_3bitri
      (syn_wa (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z)))
        (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))
      (syn_wa (syn_wa (syn_wbr A (syn_c1st) (.cv x))
          (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))) (syn_wbr (.cv x) R (.cv z)))
      (syn_wa (syn_wex y
          (syn_wa (.classEq A (syn_cop (.cv x) (.cv y))) (syn_wbr (.cv y) S (.cv w))))
        (syn_wbr (.cv x) R (.cv z)))
      (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
          (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))
      p0006 p0018 p0024
  have p0026 :=
    @g_exbii
      (syn_wa (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z)))
        (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))
      (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
          (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))
      x p0025
  have p0027 :=
    @g_n_3bitr2i
      (syn_wa (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z))
        (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))
      (syn_wa (syn_wex x (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z))))
        (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))
      (syn_wex x (syn_wa (syn_wa (syn_wbr A (syn_c1st) (.cv x)) (syn_wbr (.cv x) R (.cv z)))
          (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
            (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))))
      p0004 p0005 p0026
  have p0028 :=
    @g_anbi2i
      (syn_wa (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z))
        (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
            (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))))
      (.classEq B (syn_cop (.cv z) (.cv w))) p0027
  have p0029 :=
    @g_n_3anass (.classEq B (syn_cop (.cv z) (.cv w)))
      (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z))
      (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))
  have p0030 :=
    @g_n_3ancoma (.classEq A (syn_cop (.cv x) (.cv y)))
      (.classEq B (syn_cop (.cv z) (.cv w)))
      (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))
  have p0031 :=
    @g_n_3anass (.classEq B (syn_cop (.cv z) (.cv w)))
      (.classEq A (syn_cop (.cv x) (.cv y)))
      (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))
  have p0032 :=
    @g_bitri
      (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w)))
        (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))
      (syn_w3a (.classEq B (syn_cop (.cv z) (.cv w))) (.classEq A (syn_cop (.cv x) (.cv y)))
        (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))
      (syn_wa (.classEq B (syn_cop (.cv z) (.cv w)))
        (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
          (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))
      p0030 p0031
  have p0033 :=
    @g_n_2exbii
      (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w)))
        (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))
      (syn_wa (.classEq B (syn_cop (.cv z) (.cv w)))
        (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
          (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))
      x y p0032
  have p0034 :=
    @g_n_19_42vv (.classEq B (syn_cop (.cv z) (.cv w)))
      (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
        (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))
      x y dv_cache_0019 dv_cache_0020
  have p0035 :=
    @g_bitri
      (syn_wex x (syn_wex y (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y)))
            (.classEq B (syn_cop (.cv z) (.cv w)))
            (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))))
      (syn_wex x (syn_wex y (syn_wa (.classEq B (syn_cop (.cv z) (.cv w)))
            (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
              (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))))
      (syn_wa (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wex x (syn_wex y
            (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
              (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))))
      p0033 p0034
  have p0036 :=
    @g_n_3bitr4i
      (syn_wa (.classEq B (syn_cop (.cv z) (.cv w)))
        (syn_wa (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z))
          (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w))))
      (syn_wa (.classEq B (syn_cop (.cv z) (.cv w))) (syn_wex x (syn_wex y
            (syn_wa (.classEq A (syn_cop (.cv x) (.cv y)))
              (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w)))))))
      (syn_w3a (.classEq B (syn_cop (.cv z) (.cv w)))
        (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))
      (syn_wex x (syn_wex y (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y)))
            (.classEq B (syn_cop (.cv z) (.cv w)))
            (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))))
      p0028 p0029 p0035
  have p0037 :=
    @g_n_2exbii
      (syn_w3a (.classEq B (syn_cop (.cv z) (.cv w)))
        (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z)) (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))
      (syn_wex x (syn_wex y (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y)))
            (.classEq B (syn_cop (.cv z) (.cv w)))
            (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))))
      z w p0036
  have p0038 :=
    @g_exrot4
      (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y))) (.classEq B (syn_cop (.cv z) (.cv w)))
        (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))
      z w x y
  have p0039 :=
    @g_bitri
      (syn_wex z (syn_wex w (syn_w3a (.classEq B (syn_cop (.cv z) (.cv w)))
            (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z))
            (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))))
      (syn_wex z (syn_wex w (syn_wex x (syn_wex y
              (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y)))
                (.classEq B (syn_cop (.cv z) (.cv w)))
                (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))))))
      (syn_wex x (syn_wex y (syn_wex z (syn_wex w
              (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y)))
                (.classEq B (syn_cop (.cv z) (.cv w)))
                (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))))))
      p0037 p0038
  have p0040 :=
    @g_n_3bitri (syn_wbr A (syn_cpprod R S) B)
      (syn_wbr A (syn_ctxp (syn_ccom R (syn_c1st)) (syn_ccom S (syn_c2nd))) B)
      (syn_wex z (syn_wex w (syn_w3a (.classEq B (syn_cop (.cv z) (.cv w)))
            (syn_wbr A (syn_ccom R (syn_c1st)) (.cv z))
            (syn_wbr A (syn_ccom S (syn_c2nd)) (.cv w)))))
      (syn_wex x (syn_wex y (syn_wex z (syn_wex w
              (syn_w3a (.classEq A (syn_cop (.cv x) (.cv y)))
                (.classEq B (syn_cop (.cv z) (.cv w)))
                (syn_wa (syn_wbr (.cv x) R (.cv z)) (syn_wbr (.cv y) S (.cv w))))))))
      p0001 p0002 p0039
  exact p0040


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part007`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_dmpprod (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_cdm (syn_cpprod A B)) (syn_cxp (syn_cdm A) (syn_cdm B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let c : Var := freshVar proofSupport 3
  let d : Var := freshVar proofSupport 4
  let t : Var := freshVar proofSupport 5
  let u : Var := freshVar proofSupport 6
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
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
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_c_not_A : c ∉ A.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (h))
  have fresh_c_not_B : c ∉ B.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_d_not_A : d ∉ A.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_B : d ∉ B.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_u : u ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_u_not_A : u ∉ A.fv := by
    intro h
    exact fresh_u (Finset.mem_union_left _ (h))
  have fresh_u_not_B : u ∉ B.fv := by
    intro h
    exact fresh_u (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_a_ne_u : a ≠ u :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_u_ne_a : u ≠ a := Ne.symm fresh_a_ne_u
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_b_ne_t : b ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_t_ne_b : t ≠ b := Ne.symm fresh_b_ne_t
  have fresh_b_ne_u : b ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_u_ne_b : u ≠ b := Ne.symm fresh_b_ne_u
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_x_ne_d : x ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_d_ne_x : d ≠ x := Ne.symm fresh_x_ne_d
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_u : x ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_u_ne_x : u ≠ x := Ne.symm fresh_x_ne_u
  have fresh_c_ne_d : c ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
  have fresh_c_ne_t : c ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_t_ne_c : t ≠ c := Ne.symm fresh_c_ne_t
  have fresh_c_ne_u : c ≠ u :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_u_ne_c : u ≠ c := Ne.symm fresh_c_ne_u
  have fresh_d_ne_t : d ≠ t :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_t_ne_d : t ≠ d := Ne.symm fresh_d_ne_t
  have fresh_d_ne_u : d ≠ u :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_u_ne_d : u ≠ d := Ne.symm fresh_d_ne_u
  have fresh_t_ne_u : t ≠ u :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have dv_cache_0001 : x ∉ ((syn_cop (.cv c) (.cv d))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_c, fresh_x_ne_d, or_false, not_false_eq_true])
  have dv_cache_0002 :
    x ∉ ((syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_c, fresh_x_not_A, fresh_x_ne_b,
          fresh_x_ne_d, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cop (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_b, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cpprod A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          Finset.mem_union, fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0005 : d ∉ ((syn_cop (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_b, or_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_cop (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_b, or_false, not_false_eq_true])
  have dv_cache_0007 : u ∉ ((syn_cop (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_u_ne_a, fresh_u_ne_b, or_false, not_false_eq_true])
  have dv_cache_0008 : c ∉ ((syn_cop (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_b, or_false, not_false_eq_true])
  have dv_cache_0009 : d ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_x, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_x, not_false_eq_true])
  have dv_cache_0011 : u ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_x, not_false_eq_true])
  have dv_cache_0012 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0013 : d ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_A, not_false_eq_true])
  have dv_cache_0014 : t ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_A, not_false_eq_true])
  have dv_cache_0015 : u ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_A, not_false_eq_true])
  have dv_cache_0016 : c ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_A, not_false_eq_true])
  have dv_cache_0017 : d ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_B, not_false_eq_true])
  have dv_cache_0018 : t ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_B, not_false_eq_true])
  have dv_cache_0019 : u ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_u_not_B, not_false_eq_true])
  have dv_cache_0020 : c ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_B, not_false_eq_true])
  have dv_cache_0021 : d ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show d ≠ t from (by exact fresh_d_ne_t))
  have dv_cache_0022 : d ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show d ≠ u from (by exact fresh_d_ne_u))
  have dv_cache_0023 : d ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0024 : t ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show t ≠ u from (by exact fresh_t_ne_u))
  have dv_cache_0025 : t ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show t ≠ c from (by exact fresh_t_ne_c))
  have dv_cache_0026 : u ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show u ≠ c from (by exact fresh_u_ne_c))
  have dv_cache_0027 : c ∉ ((syn_wa (.objEq t a) (.objEq u b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_c_ne_t, fresh_c_ne_a, fresh_c_ne_u, fresh_c_ne_b,
          or_false, not_false_eq_true])
  have dv_cache_0028 : d ∉ ((syn_wa (.objEq t a) (.objEq u b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_d_ne_t, fresh_d_ne_a, fresh_d_ne_u, fresh_d_ne_b,
          or_false, not_false_eq_true])
  have dv_cache_0029 : c ∉ ((Wff.objEq t a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_c_ne_t, fresh_c_ne_a, or_false, not_false_eq_true])
  have dv_cache_0030 : d ∉ ((Wff.objEq t a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_d_ne_t, fresh_d_ne_a, or_false, not_false_eq_true])
  have dv_cache_0031 : c ∉ ((Wff.objEq u b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_c_ne_u, fresh_c_ne_b, or_false, not_false_eq_true])
  have dv_cache_0032 : d ∉ ((Wff.objEq u b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_d_ne_u, fresh_d_ne_b, or_false, not_false_eq_true])
  have dv_cache_0033 : t ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_a, not_false_eq_true])
  have dv_cache_0034 : u ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_a, not_false_eq_true])
  have dv_cache_0035 : t ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_b, not_false_eq_true])
  have dv_cache_0036 : u ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_b, not_false_eq_true])
  have dv_cache_0037 :
    u ∉
      ((syn_wex c (syn_wex d (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_c,
          fresh_u_ne_d, fresh_u_ne_a, fresh_u_not_A, fresh_u_ne_b, fresh_u_not_B,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0038 :
    t ∉
      ((syn_wex c (syn_wex d (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_c,
          fresh_t_ne_d, fresh_t_ne_a, fresh_t_not_A, fresh_t_ne_u, fresh_t_not_B,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0039 : c ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_a, not_false_eq_true])
  have dv_cache_0040 : d ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_b, not_false_eq_true])
  have dv_cache_0041 : d ∉ ((syn_wbr (.cv a) A (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_c, fresh_d_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0042 : c ∉ ((syn_wbr (.cv b) B (.cv d))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_b, fresh_c_ne_d, fresh_c_not_B, or_false,
          not_false_eq_true])
  have dv_cache_0043 : a ∉ ((syn_cdm (syn_cpprod A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, Finset.mem_union,
          fresh_a_not_A, fresh_a_not_B, or_false, not_false_eq_true])
  have dv_cache_0044 : b ∉ ((syn_cdm (syn_cpprod A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod, Finset.mem_union,
          fresh_b_not_A, fresh_b_not_B, or_false, not_false_eq_true])
  have dv_cache_0045 : a ∉ ((syn_cxp (syn_cdm A) (syn_cdm B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_a_not_A, fresh_a_not_B, or_false, not_false_eq_true])
  have dv_cache_0046 : b ∉ ((syn_cxp (syn_cdm A) (syn_cdm B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          fresh_b_not_A, fresh_b_not_B, or_false, not_false_eq_true])
  have dv_cache_0047 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have p0000 := @g_vex c
  have p0001 := @g_vex d
  have p0002 := @g_opex (.cv c) (.cv d) p0000 p0001
  have p0003 := @g_isseti x (syn_cop (.cv c) (.cv d)) dv_cache_0001 p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
      (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d))) x dv_cache_0002
  have p0005 :=
    @g_mpbiran
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
          (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d)))))
      (syn_wex x (.classEq (.cv x) (syn_cop (.cv c) (.cv d))))
      (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d))) p0003 p0004
  have p0006 :=
    @g_n_2exbii
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
          (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d)))))
      (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d))) c d p0005
  have p0007 := (Nominal.biimpRefl (syn_wbr (.cv a) (syn_cdm (syn_cpprod A B)) (.cv b)))
  have p0008 :=
    @g_eldm x (syn_cop (.cv a) (.cv b)) (syn_cpprod A B) dv_cache_0003 dv_cache_0004
  have p0009 :=
    @g_brpprod t u c d (syn_cop (.cv a) (.cv b)) (.cv x) A B dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024
      dv_cache_0025 dv_cache_0026
  have p0010 :=
    @g_n_19_42vv (syn_wa (.objEq t a) (.objEq u b))
      (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
        (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))
      c d dv_cache_0027 dv_cache_0028
  have p0011 :=
    @g_n_3anass (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv t) (.cv u)))
      (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
      (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))
  have p0012 := @g_eqcom (syn_cop (.cv a) (.cv b)) (syn_cop (.cv t) (.cv u))
  have p0013 := @g_opth (.cv t) (.cv u) (.cv a) (.cv b)
  have p0014_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cop (.cv t) (.cv u)) (syn_cop (.cv a) (.cv b)))
        (syn_wa (.objEq t a) (.objEq u b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0014 :=
    @g_bitri (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv t) (.cv u)))
      (.classEq (syn_cop (.cv t) (.cv u)) (syn_cop (.cv a) (.cv b)))
      (syn_wa (.objEq t a) (.objEq u b)) p0012 p0014_e01_recanon
  have p0015 :=
    @g_anbi1i (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv t) (.cv u)))
      (syn_wa (.objEq t a) (.objEq u b))
      (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
        (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))
      p0014
  have p0016 :=
    @g_bitri
      (syn_w3a (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv t) (.cv u)))
        (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
        (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))
      (syn_wa (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv t) (.cv u)))
        (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
          (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))))
      (syn_wa (syn_wa (.objEq t a) (.objEq u b))
        (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
          (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))))
      p0011 p0015
  have p0017 :=
    @g_n_2exbii
      (syn_w3a (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv t) (.cv u)))
        (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
        (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))
      (syn_wa (syn_wa (.objEq t a) (.objEq u b))
        (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
          (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))))
      c d p0016
  have p0018 :=
    (Nominal.biimpRefl (syn_w3a (.objEq t a) (.objEq u b) (syn_wex c (syn_wex d
            (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))))))
  have p0019 :=
    @g_n_3bitr4i
      (syn_wex c (syn_wex d (syn_wa (syn_wa (.objEq t a) (.objEq u b))
            (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))))))
      (syn_wa (syn_wa (.objEq t a) (.objEq u b)) (syn_wex c (syn_wex d
            (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))))))
      (syn_wex c (syn_wex d
          (syn_w3a (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv t) (.cv u)))
            (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
            (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))))
      (syn_w3a (.objEq t a) (.objEq u b) (syn_wex c (syn_wex d
            (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))))))
      p0010 p0017 p0018
  have p0020 :=
    @g_n_2exbii
      (syn_wex c (syn_wex d
          (syn_w3a (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv t) (.cv u)))
            (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
            (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))))
      (syn_w3a (.objEq t a) (.objEq u b) (syn_wex c (syn_wex d
            (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))))))
      t u p0019
  have p0021 := @g_vex a
  have p0022 := @g_vex b
  have p0023 := @g_breq1 (.cv t) (.cv a) (.cv c) A
  have p0024_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq t a) (syn_wb (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv a) A (.cv c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0023
  have p0024 :=
    @g_anbi1d (.objEq t a) (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv a) A (.cv c))
      (syn_wbr (.cv u) B (.cv d)) p0024_e00_recanon
  have p0025 :=
    @g_anbi2d (.objEq t a)
      (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))
      (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))
      (.classEq (.cv x) (syn_cop (.cv c) (.cv d))) p0024
  have p0026 :=
    @g_n_2exbidv (.objEq t a)
      (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
        (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))
      (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
        (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))
      c d dv_cache_0029 dv_cache_0030 p0025
  have p0027 := @g_breq1 (.cv u) (.cv b) (.cv d) B
  have p0028_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq u b) (syn_wb (syn_wbr (.cv u) B (.cv d)) (syn_wbr (.cv b) B (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0027
  have p0028 :=
    @g_anbi2d (.objEq u b) (syn_wbr (.cv u) B (.cv d)) (syn_wbr (.cv b) B (.cv d))
      (syn_wbr (.cv a) A (.cv c)) p0028_e00_recanon
  have p0029 :=
    @g_anbi2d (.objEq u b)
      (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))
      (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d)))
      (.classEq (.cv x) (syn_cop (.cv c) (.cv d))) p0028
  have p0030 :=
    @g_n_2exbidv (.objEq u b)
      (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
        (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))
      (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
        (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d))))
      c d dv_cache_0031 dv_cache_0032 p0029
  have p0031_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv t) (.cv a)) (syn_wb (syn_wex c (syn_wex d
              (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
                (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))))) (syn_wex c
            (syn_wex d (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
                (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0031_e03_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv u) (.cv b)) (syn_wb (syn_wex c (syn_wex d
              (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
                (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))))) (syn_wex c
            (syn_wex d (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
                (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0030
  have p0031 :=
    @g_ceqsex2v
      (syn_wex c (syn_wex d (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
            (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))))
      (syn_wex c (syn_wex d (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
            (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))))
      (syn_wex c (syn_wex d (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
            (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d))))))
      t u (.cv a) (.cv b) dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
      dv_cache_0037 dv_cache_0038 dv_cache_0024 p0021 p0022 p0031_e02_recanon
      p0031_e03_recanon
  have p0032_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex t (syn_wex u (syn_w3a (.objEq t a) (.objEq u b) (syn_wex c (syn_wex d
                  (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
                    (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))))))))
        (syn_wex c (syn_wex d (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0032 :=
    @g_n_3bitri (syn_wbr (syn_cop (.cv a) (.cv b)) (syn_cpprod A B) (.cv x))
      (syn_wex t (syn_wex u (syn_wex c (syn_wex d
              (syn_w3a (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv t) (.cv u)))
                (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
                (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d))))))))
      (syn_wex t (syn_wex u (syn_w3a (.objEq t a) (.objEq u b) (syn_wex c (syn_wex d
                (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
                  (syn_wa (syn_wbr (.cv t) A (.cv c)) (syn_wbr (.cv u) B (.cv d)))))))))
      (syn_wex c (syn_wex d (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
            (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d))))))
      p0009 p0020 p0032_e02_recanon
  have p0033 :=
    @g_exbii (syn_wbr (syn_cop (.cv a) (.cv b)) (syn_cpprod A B) (.cv x))
      (syn_wex c (syn_wex d (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
            (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d))))))
      x p0032
  have p0034 :=
    @g_exrot3
      (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
        (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d))))
      x c d
  have p0035 :=
    @g_bitri (syn_wex x (syn_wbr (syn_cop (.cv a) (.cv b)) (syn_cpprod A B) (.cv x)))
      (syn_wex x (syn_wex c (syn_wex d (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d)))))))
      (syn_wex c (syn_wex d (syn_wex x (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d)))))))
      p0033 p0034
  have p0036 :=
    @g_n_3bitri (syn_wbr (.cv a) (syn_cdm (syn_cpprod A B)) (.cv b))
      (.classMem (syn_cop (.cv a) (.cv b)) (syn_cdm (syn_cpprod A B)))
      (syn_wex x (syn_wbr (syn_cop (.cv a) (.cv b)) (syn_cpprod A B) (.cv x)))
      (syn_wex c (syn_wex d (syn_wex x (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d)))))))
      p0007 p0008 p0035
  have p0037 := @g_eldm c (.cv a) A dv_cache_0039 dv_cache_0016
  have p0038 := @g_eldm d (.cv b) B dv_cache_0040 dv_cache_0017
  have p0039 :=
    @g_anbi12i (.classMem (.cv a) (syn_cdm A)) (syn_wex c (syn_wbr (.cv a) A (.cv c)))
      (.classMem (.cv b) (syn_cdm B)) (syn_wex d (syn_wbr (.cv b) B (.cv d))) p0037 p0038
  have p0040 := @g_brxp (.cv a) (.cv b) (syn_cdm A) (syn_cdm B)
  have p0041 :=
    @g_eeanv (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d)) c d dv_cache_0041
      dv_cache_0042
  have p0042 :=
    @g_n_3bitr4i (syn_wa (.classMem (.cv a) (syn_cdm A)) (.classMem (.cv b) (syn_cdm B)))
      (syn_wa (syn_wex c (syn_wbr (.cv a) A (.cv c))) (syn_wex d (syn_wbr (.cv b) B (.cv d))))
      (syn_wbr (.cv a) (syn_cxp (syn_cdm A) (syn_cdm B)) (.cv b))
      (syn_wex c (syn_wex d (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d)))))
      p0039 p0040 p0041
  have p0043 :=
    @g_n_3bitr4i
      (syn_wex c (syn_wex d (syn_wex x (syn_wa (.classEq (.cv x) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d)))))))
      (syn_wex c (syn_wex d (syn_wa (syn_wbr (.cv a) A (.cv c)) (syn_wbr (.cv b) B (.cv d)))))
      (syn_wbr (.cv a) (syn_cdm (syn_cpprod A B)) (.cv b))
      (syn_wbr (.cv a) (syn_cxp (syn_cdm A) (syn_cdm B)) (.cv b)) p0006 p0036 p0042
  have p0044 :=
    @g_eqbrriv a b (syn_cdm (syn_cpprod A B)) (syn_cxp (syn_cdm A) (syn_cdm B))
      dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 p0043
  exact p0044


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part008`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cnvpprod (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_ccnv (syn_cpprod A B)) (syn_cpprod (syn_ccnv A) (syn_ccnv B))) :=
  by
  have p0000 :=
    @g_cnvin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st)))
      (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd)))
  have p0001 := @g_cnvco (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st))
  have p0002 := @g_cnvco A (syn_c1st)
  have p0003 := @g_cnvcnv (syn_c1st)
  have p0004 :=
    @g_coeq12i (syn_ccnv (syn_ccom A (syn_c1st)))
      (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccnv A)) (syn_ccnv (syn_ccnv (syn_c1st)))
      (syn_c1st) p0002 p0003
  have p0005 := @g_coass (syn_ccnv (syn_c1st)) (syn_ccnv A) (syn_c1st)
  have p0006 :=
    @g_n_3eqtri (syn_ccnv (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st))))
      (syn_ccom (syn_ccnv (syn_ccom A (syn_c1st))) (syn_ccnv (syn_ccnv (syn_c1st))))
      (syn_ccom (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccnv A)) (syn_c1st))
      (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_ccnv A) (syn_c1st))) p0001 p0004
      p0005
  have p0007 := @g_cnvco (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd))
  have p0008 := @g_cnvco B (syn_c2nd)
  have p0009 := @g_cnvcnv (syn_c2nd)
  have p0010 :=
    @g_coeq12i (syn_ccnv (syn_ccom B (syn_c2nd)))
      (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccnv B)) (syn_ccnv (syn_ccnv (syn_c2nd)))
      (syn_c2nd) p0008 p0009
  have p0011 := @g_coass (syn_ccnv (syn_c2nd)) (syn_ccnv B) (syn_c2nd)
  have p0012 :=
    @g_n_3eqtri (syn_ccnv (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd))))
      (syn_ccom (syn_ccnv (syn_ccom B (syn_c2nd))) (syn_ccnv (syn_ccnv (syn_c2nd))))
      (syn_ccom (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccnv B)) (syn_c2nd))
      (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom (syn_ccnv B) (syn_c2nd))) p0007 p0010
      p0011
  have p0013 :=
    @g_ineq12i (syn_ccnv (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st))))
      (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_ccnv A) (syn_c1st)))
      (syn_ccnv (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd))))
      (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom (syn_ccnv B) (syn_c2nd))) p0006 p0012
  have p0014 :=
    @g_eqtri
      (syn_ccnv (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st)))
          (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd)))))
      (syn_cin (syn_ccnv (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st))))
        (syn_ccnv (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd)))))
      (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_ccnv A) (syn_c1st)))
        (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom (syn_ccnv B) (syn_c2nd))))
      p0000 p0013
  have p0015 := (Nominal.classEqRefl (syn_cpprod A B))
  have p0016 :=
    (Nominal.classEqRefl (syn_ctxp (syn_ccom A (syn_c1st)) (syn_ccom B (syn_c2nd))))
  have p0017 :=
    @g_eqtri (syn_cpprod A B) (syn_ctxp (syn_ccom A (syn_c1st)) (syn_ccom B (syn_c2nd)))
      (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st)))
        (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd))))
      p0015 p0016
  have p0018 :=
    @g_cnveqi (syn_cpprod A B)
      (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st)))
        (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd))))
      p0017
  have p0019 := (Nominal.classEqRefl (syn_cpprod (syn_ccnv A) (syn_ccnv B)))
  have p0020 :=
    (Nominal.classEqRefl
      (syn_ctxp (syn_ccom (syn_ccnv A) (syn_c1st)) (syn_ccom (syn_ccnv B) (syn_c2nd))))
  have p0021 :=
    @g_eqtri (syn_cpprod (syn_ccnv A) (syn_ccnv B))
      (syn_ctxp (syn_ccom (syn_ccnv A) (syn_c1st)) (syn_ccom (syn_ccnv B) (syn_c2nd)))
      (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_ccnv A) (syn_c1st)))
        (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom (syn_ccnv B) (syn_c2nd))))
      p0019 p0020
  have p0022 :=
    @g_n_3eqtr4i
      (syn_ccnv (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom A (syn_c1st)))
          (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom B (syn_c2nd)))))
      (syn_cin (syn_ccom (syn_ccnv (syn_c1st)) (syn_ccom (syn_ccnv A) (syn_c1st)))
        (syn_ccom (syn_ccnv (syn_c2nd)) (syn_ccom (syn_ccnv B) (syn_c2nd))))
      (syn_ccnv (syn_cpprod A B)) (syn_cpprod (syn_ccnv A) (syn_ccnv B)) p0014 p0018 p0021
  exact p0022

@[expose]
noncomputable def g_rnpprod (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (syn_crn (syn_cpprod A B)) (syn_cxp (syn_crn A) (syn_crn B))) :=
  by
  have p0000 := @g_cnvpprod A B
  have p0001 :=
    @g_dmeqi (syn_ccnv (syn_cpprod A B)) (syn_cpprod (syn_ccnv A) (syn_ccnv B)) p0000
  have p0002 := @g_dmpprod (syn_ccnv A) (syn_ccnv B)
  have p0003 :=
    @g_eqtri (syn_cdm (syn_ccnv (syn_cpprod A B)))
      (syn_cdm (syn_cpprod (syn_ccnv A) (syn_ccnv B)))
      (syn_cxp (syn_cdm (syn_ccnv A)) (syn_cdm (syn_ccnv B))) p0001 p0002
  have p0004 := @g_dfrn4 (syn_cpprod A B)
  have p0005 := @g_dfrn4 A
  have p0006 := @g_dfrn4 B
  have p0007 :=
    @g_xpeq12i (syn_crn A) (syn_cdm (syn_ccnv A)) (syn_crn B) (syn_cdm (syn_ccnv B)) p0005
      p0006
  have p0008 :=
    @g_n_3eqtr4i (syn_cdm (syn_ccnv (syn_cpprod A B)))
      (syn_cxp (syn_cdm (syn_ccnv A)) (syn_cdm (syn_ccnv B))) (syn_crn (syn_cpprod A B))
      (syn_cxp (syn_crn A) (syn_crn B)) p0003 p0004 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part009`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_fnpprod (A : Class) (B : Class) (F : Class) (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wfn F A) (syn_wfn G B)) (syn_wfn (syn_cpprod F G) (syn_cxp A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ F.fv ∪ G.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  let c : Var := freshVar proofSupport 5
  let d : Var := freshVar proofSupport 6
  let e : Var := freshVar proofSupport 7
  let f : Var := freshVar proofSupport 8
  let g : Var := freshVar proofSupport 9
  let h : Var := freshVar proofSupport 10
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_G : y ∉ G.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_F : z ∉ F.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z_not_G : z ∉ G.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_not_G : a ∉ G.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_b_not_F : b ∉ F.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_G : b ∉ G.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 5 ∉ proofSupport
    exact freshVar_not_mem proofSupport 5
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_G : c ∉ G.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 6 ∉ proofSupport
    exact freshVar_not_mem proofSupport 6
  have fresh_d_not_F : d ∉ F.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_d_not_G : d ∉ G.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 7 ∉ proofSupport
    exact freshVar_not_mem proofSupport 7
  have fresh_e_not_F : e ∉ F.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_e_not_G : e ∉ G.fv := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (h))
  have fresh_f : f ∉ proofSupport :=
    by
    change freshVar proofSupport 8 ∉ proofSupport
    exact freshVar_not_mem proofSupport 8
  have fresh_f_not_F : f ∉ F.fv := by
    intro h
    exact fresh_f (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_f_not_G : f ∉ G.fv := by
    intro h
    exact fresh_f (Finset.mem_union_right _ (h))
  have fresh_g : g ∉ proofSupport :=
    by
    change freshVar proofSupport 9 ∉ proofSupport
    exact freshVar_not_mem proofSupport 9
  have fresh_g_not_F : g ∉ F.fv := by
    intro h
    exact fresh_g (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_g_not_G : g ∉ G.fv := by
    intro h
    exact fresh_g (Finset.mem_union_right _ (h))
  have fresh_h : h ∉ proofSupport :=
    by
    change freshVar proofSupport 10 ∉ proofSupport
    exact freshVar_not_mem proofSupport 10
  have fresh_h_not_F : h ∉ F.fv := by
    intro h
    exact fresh_h (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_h_not_G : h ∉ G.fv := by
    intro h
    exact fresh_h (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
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
  have fresh_x_ne_c : x ≠ c :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_c_ne_x : c ≠ x := Ne.symm fresh_x_ne_c
  have fresh_x_ne_d : x ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_d_ne_x : d ≠ x := Ne.symm fresh_x_ne_d
  have fresh_x_ne_e : x ≠ e :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_e_ne_x : e ≠ x := Ne.symm fresh_x_ne_e
  have fresh_x_ne_f : x ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 0) (j := 8) (by decide)
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_x_ne_g : x ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 0) (j := 9) (by decide)
  have fresh_g_ne_x : g ≠ x := Ne.symm fresh_x_ne_g
  have fresh_x_ne_h : x ≠ h :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 0) (j := 10) (by decide)
  have fresh_h_ne_x : h ≠ x := Ne.symm fresh_x_ne_h
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_c : y ≠ c :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_c_ne_y : c ≠ y := Ne.symm fresh_y_ne_c
  have fresh_y_ne_d : y ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_d_ne_y : d ≠ y := Ne.symm fresh_y_ne_d
  have fresh_y_ne_e : y ≠ e :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_e_ne_y : e ≠ y := Ne.symm fresh_y_ne_e
  have fresh_y_ne_f : y ≠ f :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_y_ne_g : y ≠ g :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 1) (j := 9) (by decide)
  have fresh_g_ne_y : g ≠ y := Ne.symm fresh_y_ne_g
  have fresh_y_ne_h : y ≠ h :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 1) (j := 10) (by decide)
  have fresh_h_ne_y : h ≠ y := Ne.symm fresh_y_ne_h
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_z_ne_c : z ≠ c :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_c_ne_z : c ≠ z := Ne.symm fresh_z_ne_c
  have fresh_z_ne_d : z ≠ d :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_d_ne_z : d ≠ z := Ne.symm fresh_z_ne_d
  have fresh_z_ne_e : z ≠ e :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
  have fresh_e_ne_z : e ≠ z := Ne.symm fresh_z_ne_e
  have fresh_z_ne_f : z ≠ f :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 2) (j := 8) (by decide)
  have fresh_f_ne_z : f ≠ z := Ne.symm fresh_z_ne_f
  have fresh_z_ne_g : z ≠ g :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 2) (j := 9) (by decide)
  have fresh_g_ne_z : g ≠ z := Ne.symm fresh_z_ne_g
  have fresh_z_ne_h : z ≠ h :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 2) (j := 10) (by decide)
  have fresh_h_ne_z : h ≠ z := Ne.symm fresh_z_ne_h
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_c : a ≠ c :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_a_ne_e : a ≠ e :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_e_ne_a : e ≠ a := Ne.symm fresh_a_ne_e
  have fresh_a_ne_f : a ≠ f :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 3) (j := 8) (by decide)
  have fresh_f_ne_a : f ≠ a := Ne.symm fresh_a_ne_f
  have fresh_a_ne_g : a ≠ g :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 3) (j := 9) (by decide)
  have fresh_g_ne_a : g ≠ a := Ne.symm fresh_a_ne_g
  have fresh_a_ne_h : a ≠ h :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 3) (j := 10) (by decide)
  have fresh_h_ne_a : h ≠ a := Ne.symm fresh_a_ne_h
  have fresh_b_ne_c : b ≠ c :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_b_ne_d : b ≠ d :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
  have fresh_b_ne_e : b ≠ e :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_e_ne_b : e ≠ b := Ne.symm fresh_b_ne_e
  have fresh_b_ne_f : b ≠ f :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 4) (j := 8) (by decide)
  have fresh_f_ne_b : f ≠ b := Ne.symm fresh_b_ne_f
  have fresh_b_ne_g : b ≠ g :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 4) (j := 9) (by decide)
  have fresh_g_ne_b : g ≠ b := Ne.symm fresh_b_ne_g
  have fresh_b_ne_h : b ≠ h :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 4) (j := 10) (by decide)
  have fresh_h_ne_b : h ≠ b := Ne.symm fresh_b_ne_h
  have fresh_c_ne_d : c ≠ d :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
  have fresh_c_ne_e : c ≠ e :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_e_ne_c : e ≠ c := Ne.symm fresh_c_ne_e
  have fresh_c_ne_f : c ≠ f :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
  have fresh_f_ne_c : f ≠ c := Ne.symm fresh_c_ne_f
  have fresh_c_ne_g : c ≠ g :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 5) (j := 9) (by decide)
  have fresh_g_ne_c : g ≠ c := Ne.symm fresh_c_ne_g
  have fresh_c_ne_h : c ≠ h :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 5) (j := 10) (by decide)
  have fresh_h_ne_c : h ≠ c := Ne.symm fresh_c_ne_h
  have fresh_d_ne_e : d ≠ e :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_e_ne_d : e ≠ d := Ne.symm fresh_d_ne_e
  have fresh_d_ne_f : d ≠ f :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 6) (j := 8) (by decide)
  have fresh_f_ne_d : f ≠ d := Ne.symm fresh_d_ne_f
  have fresh_d_ne_g : d ≠ g :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 6) (j := 9) (by decide)
  have fresh_g_ne_d : g ≠ d := Ne.symm fresh_d_ne_g
  have fresh_d_ne_h : d ≠ h :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 6) (j := 10) (by decide)
  have fresh_h_ne_d : h ≠ d := Ne.symm fresh_d_ne_h
  have fresh_e_ne_f : e ≠ f :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 8
    exact freshVar_injective proofSupport (i := 7) (j := 8) (by decide)
  have fresh_e_ne_g : e ≠ g :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 7) (j := 9) (by decide)
  have fresh_e_ne_h : e ≠ h :=
    by
    change freshVar proofSupport 7 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 7) (j := 10) (by decide)
  have fresh_h_ne_e : h ≠ e := Ne.symm fresh_e_ne_h
  have fresh_f_ne_g : f ≠ g :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 9
    exact freshVar_injective proofSupport (i := 8) (j := 9) (by decide)
  have fresh_f_ne_h : f ≠ h :=
    by
    change freshVar proofSupport 8 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 8) (j := 10) (by decide)
  have fresh_h_ne_f : h ≠ f := Ne.symm fresh_f_ne_h
  have fresh_g_ne_h : g ≠ h :=
    by
    change freshVar proofSupport 9 ≠ freshVar proofSupport 10
    exact freshVar_injective proofSupport (i := 9) (j := 10) (by decide)
  have fresh_h_ne_g : h ≠ g := Ne.symm fresh_g_ne_h
  have dv_cache_0001 :
    f ∉
      ((syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
              (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_f_ne_a, fresh_f_ne_c,
          fresh_f_not_F, fresh_f_ne_b, fresh_f_ne_d, fresh_f_not_G, fresh_f_ne_x,
          fresh_f_ne_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0002 :
    e ∉
      ((syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
              (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_e_ne_a, fresh_e_ne_c,
          fresh_e_not_F, fresh_e_ne_b, fresh_e_ne_d, fresh_e_not_G, fresh_e_ne_x,
          fresh_e_ne_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0003 :
    a ∉
      ((syn_wex g (syn_wex h (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
              (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
              (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_e, fresh_a_ne_g,
          fresh_a_not_F, fresh_a_ne_f, fresh_a_ne_h, fresh_a_not_G, fresh_a_ne_x,
          fresh_a_ne_z, or_false, and_false, not_false_eq_true])
  have dv_cache_0004 :
    b ∉
      ((syn_wex g (syn_wex h (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
              (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
              (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_e, fresh_b_ne_g,
          fresh_b_not_F, fresh_b_ne_f, fresh_b_ne_h, fresh_b_not_G, fresh_b_ne_x,
          fresh_b_ne_z, or_false, and_false, not_false_eq_true])
  have dv_cache_0005 : f ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show f ≠ a from (by exact fresh_f_ne_a))
  have dv_cache_0006 : b ≠ e :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show b ≠ e from (by exact fresh_b_ne_e))
  have dv_cache_0007 :
    h ∉
      ((syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
          (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
          (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_h_ne_a, fresh_h_ne_c, fresh_h_not_F, fresh_h_ne_b,
          fresh_h_ne_d, fresh_h_not_G, fresh_h_ne_x, fresh_h_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    g ∉
      ((syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
          (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
          (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_a, fresh_g_ne_c, fresh_g_not_F, fresh_g_ne_b,
          fresh_g_ne_d, fresh_g_not_G, fresh_g_ne_x, fresh_g_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    c ∉
      ((syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
          (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
          (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_e, fresh_c_ne_g, fresh_c_not_F, fresh_c_ne_f,
          fresh_c_ne_h, fresh_c_not_G, fresh_c_ne_x, fresh_c_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    d ∉
      ((syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
          (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
          (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_e, fresh_d_ne_g, fresh_d_not_F, fresh_d_ne_f,
          fresh_d_ne_h, fresh_d_not_G, fresh_d_ne_x, fresh_d_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0011 : h ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show h ≠ c from (by exact fresh_h_ne_c))
  have dv_cache_0012 : d ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show d ≠ g from (by exact fresh_d_ne_g))
  have dv_cache_0013 : d ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_x, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0015 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0016 : c ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_x, not_false_eq_true])
  have dv_cache_0017 : d ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_y, not_false_eq_true])
  have dv_cache_0018 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0019 : b ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0020 : c ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_c_ne_y, not_false_eq_true])
  have dv_cache_0021 : d ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_F, not_false_eq_true])
  have dv_cache_0022 : a ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_F, not_false_eq_true])
  have dv_cache_0023 : b ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_F, not_false_eq_true])
  have dv_cache_0024 : c ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_F, not_false_eq_true])
  have dv_cache_0025 : d ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_G, not_false_eq_true])
  have dv_cache_0026 : a ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_G, not_false_eq_true])
  have dv_cache_0027 : b ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_G, not_false_eq_true])
  have dv_cache_0028 : c ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_G, not_false_eq_true])
  have dv_cache_0029 : d ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show d ≠ a from (by exact fresh_d_ne_a))
  have dv_cache_0030 : d ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show d ≠ b from (by exact fresh_d_ne_b))
  have dv_cache_0031 : d ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show d ≠ c from (by exact fresh_d_ne_c))
  have dv_cache_0032 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0033 : a ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show a ≠ c from (by exact fresh_a_ne_c))
  have dv_cache_0034 : b ≠ c :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show b ≠ c from (by exact fresh_b_ne_c))
  have dv_cache_0035 : h ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_h_ne_x, not_false_eq_true])
  have dv_cache_0036 : e ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_e_ne_x, not_false_eq_true])
  have dv_cache_0037 : f ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_x, not_false_eq_true])
  have dv_cache_0038 : g ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_g_ne_x, not_false_eq_true])
  have dv_cache_0039 : h ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_h_ne_z, not_false_eq_true])
  have dv_cache_0040 : e ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_e_ne_z, not_false_eq_true])
  have dv_cache_0041 : f ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_z, not_false_eq_true])
  have dv_cache_0042 : g ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_g_ne_z, not_false_eq_true])
  have dv_cache_0043 : h ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_F, not_false_eq_true])
  have dv_cache_0044 : e ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_F, not_false_eq_true])
  have dv_cache_0045 : f ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_F, not_false_eq_true])
  have dv_cache_0046 : g ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_F, not_false_eq_true])
  have dv_cache_0047 : h ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_h_not_G, not_false_eq_true])
  have dv_cache_0048 : e ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_G, not_false_eq_true])
  have dv_cache_0049 : f ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_f_not_G, not_false_eq_true])
  have dv_cache_0050 : g ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_g_not_G, not_false_eq_true])
  have dv_cache_0051 : h ≠ e :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050
    exact (show h ≠ e from (by exact fresh_h_ne_e))
  have dv_cache_0052 : h ≠ f :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact (show h ≠ f from (by exact fresh_h_ne_f))
  have dv_cache_0053 : h ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
    exact (show h ≠ g from (by exact fresh_h_ne_g))
  have dv_cache_0054 : e ≠ f :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
    exact (show e ≠ f from (by exact fresh_e_ne_f))
  have dv_cache_0055 : e ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054
    exact (show e ≠ g from (by exact fresh_e_ne_g))
  have dv_cache_0056 : f ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055
    exact (show f ≠ g from (by exact fresh_f_ne_g))
  have dv_cache_0057 : g ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_g_ne_y, fresh_g_ne_z, or_false, not_false_eq_true])
  have dv_cache_0058 : h ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_h_ne_y, fresh_h_ne_z, or_false, not_false_eq_true])
  have dv_cache_0059 : g ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_g_not_F, fresh_g_not_G, or_false, not_false_eq_true])
  have dv_cache_0060 : h ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
    exact
      (by
        have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_h_not_F, fresh_h_not_G, or_false, not_false_eq_true])
  have dv_cache_0061 : c ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_c_ne_y, fresh_c_ne_z, or_false, not_false_eq_true])
  have dv_cache_0062 : d ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_d_ne_y, fresh_d_ne_z, or_false, not_false_eq_true])
  have dv_cache_0063 : c ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_c_not_F, fresh_c_not_G, or_false, not_false_eq_true])
  have dv_cache_0064 : d ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_d_not_F, fresh_d_not_G, or_false, not_false_eq_true])
  have dv_cache_0065 : e ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_e_ne_y, fresh_e_ne_z, or_false, not_false_eq_true])
  have dv_cache_0066 : f ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_f_ne_y, fresh_f_ne_z, or_false, not_false_eq_true])
  have dv_cache_0067 : e ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_e_not_F, fresh_e_not_G, or_false, not_false_eq_true])
  have dv_cache_0068 : f ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_f_not_F, fresh_f_not_G, or_false, not_false_eq_true])
  have dv_cache_0069 : a ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_a_ne_y, fresh_a_ne_z, or_false, not_false_eq_true])
  have dv_cache_0070 : b ∉ ((Wff.objEq y z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_b_ne_y, fresh_b_ne_z, or_false, not_false_eq_true])
  have dv_cache_0071 : a ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_a_not_F, fresh_a_not_G, or_false, not_false_eq_true])
  have dv_cache_0072 : b ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_b_not_F, fresh_b_not_G, or_false, not_false_eq_true])
  have dv_cache_0073 : z ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_z_not_F, fresh_z_not_G, or_false, not_false_eq_true])
  have dv_cache_0074 : x ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_x_not_F, fresh_x_not_G, or_false, not_false_eq_true])
  have dv_cache_0075 : y ∉ ((syn_wa (syn_wfun F) (syn_wfun G))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun, Finset.mem_union,
          fresh_y_not_F, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0076 : x ∉ ((syn_cpprod F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          Finset.mem_union, fresh_x_not_F, fresh_x_not_G, or_false, not_false_eq_true])
  have dv_cache_0077 : y ∉ ((syn_cpprod F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          Finset.mem_union, fresh_y_not_F, fresh_y_not_G, or_false, not_false_eq_true])
  have dv_cache_0078 : z ∉ ((syn_cpprod F G)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpprod,
          Finset.mem_union, fresh_z_not_F, fresh_z_not_G, or_false, not_false_eq_true])
  have dv_cache_0079 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0080 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0081 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @g_ee4anv
      (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
            (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
            (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))))
      (syn_wex g (syn_wex h (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
            (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
            (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))))
      a b e f dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
  have p0001 :=
    @g_ee4anv
      (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
        (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))
      (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
        (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
        (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))
      c d g h dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
  have p0002 :=
    @g_n_2exbii
      (syn_wex c (syn_wex d (syn_wex g (syn_wex h (syn_wa
                (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
                  (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
                  (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))
                (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
                  (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
                  (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))))))))
      (syn_wa (syn_wex c (syn_wex d (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
              (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))))) (syn_wex g
          (syn_wex h (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
              (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
              (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))))))
      e f p0001
  have p0003 :=
    @g_n_2exbii
      (syn_wex e (syn_wex f (syn_wex c (syn_wex d (syn_wex g (syn_wex h (syn_wa
                    (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
                      (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
                      (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))
                    (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
                      (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
                      (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))))))))))
      (syn_wex e (syn_wex f (syn_wa (syn_wex c (syn_wex d
                (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
                  (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
                  (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))))) (syn_wex g
              (syn_wex h (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
                  (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
                  (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))))))))
      a b p0002
  have p0004 :=
    @g_brpprod a b c d (.cv x) (.cv y) F G dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
      dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0034
  have p0005 :=
    @g_brpprod e f g h (.cv x) (.cv z) F G dv_cache_0035 dv_cache_0036 dv_cache_0037
      dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041 dv_cache_0042 dv_cache_0043
      dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049
      dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053 dv_cache_0054 dv_cache_0055
      dv_cache_0056
  have p0006 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_cpprod F G) (.cv y))
      (syn_wex a (syn_wex b (syn_wex c (syn_wex d
              (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
                (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
                (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))))))
      (syn_wbr (.cv x) (syn_cpprod F G) (.cv z))
      (syn_wex e (syn_wex f (syn_wex g (syn_wex h
              (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
                (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
                (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))))))
      p0004 p0005
  have p0007 :=
    @g_n_3bitr4ri
      (syn_wex a (syn_wex b (syn_wex e (syn_wex f (syn_wa (syn_wex c (syn_wex d
                    (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
                      (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
                      (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))))
                (syn_wex g (syn_wex h (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
                      (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
                      (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))))))))))
      (syn_wa (syn_wex a (syn_wex b (syn_wex c (syn_wex d
                (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
                  (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
                  (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))))))
        (syn_wex e (syn_wex f (syn_wex g (syn_wex h
                (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
                  (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
                  (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))))))))
      (syn_wex a (syn_wex b (syn_wex e (syn_wex f (syn_wex c (syn_wex d (syn_wex g (syn_wex h
                      (syn_wa (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
                          (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
                          (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))
                        (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
                          (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
                          (syn_wa (syn_wbr (.cv e) F (.cv g))
                            (syn_wbr (.cv f) G (.cv h)))))))))))))
      (syn_wa (syn_wbr (.cv x) (syn_cpprod F G) (.cv y))
        (syn_wbr (.cv x) (syn_cpprod F G) (.cv z)))
      p0000 p0003 p0006
  have p0008 :=
    @g_an42 (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))
      (syn_wbr (.cv a) F (.cv g)) (syn_wbr (.cv b) G (.cv h))
  have p0009 := @g_fununiq (.cv a) (.cv c) (.cv g) F
  have p0010_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wfun F) (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv a) F (.cv g)))
        (.objEq c g)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
          syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_wbr syn_cop syn_cun syn_wrex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0009
  have p0010 :=
    @g_n_3expib (syn_wfun F) (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv a) F (.cv g))
      (.objEq c g) p0010_e00_recanon
  have p0011 := @g_fununiq (.cv b) (.cv h) (.cv d) G
  have p0012 :=
    @g_eqcomd
      (syn_w3a (syn_wfun G) (syn_wbr (.cv b) G (.cv h)) (syn_wbr (.cv b) G (.cv d)))
      (.cv h) (.cv d) p0011
  have p0013_e00_recanon :
    Nominal.NPrf
      (.imp (syn_w3a (syn_wfun G) (syn_wbr (.cv b) G (.cv h)) (syn_wbr (.cv b) G (.cv d)))
        (.objEq d h)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_w3a syn_wa syn_wfun syn_wss syn_cin syn_ccompl syn_cnin syn_wnan
          syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_wbr syn_cop syn_cun syn_wrex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0012
  have p0013 :=
    @g_n_3expib (syn_wfun G) (syn_wbr (.cv b) G (.cv h)) (syn_wbr (.cv b) G (.cv d))
      (.objEq d h) p0013_e00_recanon
  have p0014 :=
    @g_im2anan9 (syn_wfun F)
      (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv a) F (.cv g))) (.objEq c g)
      (syn_wfun G) (syn_wa (syn_wbr (.cv b) G (.cv h)) (syn_wbr (.cv b) G (.cv d)))
      (.objEq d h) p0010 p0013
  have p0015 :=
    @g_syl5bi
      (syn_wa (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))
        (syn_wa (syn_wbr (.cv a) F (.cv g)) (syn_wbr (.cv b) G (.cv h))))
      (syn_wa (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv a) F (.cv g)))
        (syn_wa (syn_wbr (.cv b) G (.cv h)) (syn_wbr (.cv b) G (.cv d))))
      (syn_wa (syn_wfun F) (syn_wfun G)) (syn_wa (.objEq c g) (.objEq d h)) p0008 p0014
  have p0016 :=
    @g_exp3acom23 (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))
      (syn_wa (syn_wbr (.cv a) F (.cv g)) (syn_wbr (.cv b) G (.cv h)))
      (syn_wa (.objEq c g) (.objEq d h)) p0015
  have p0017 := @g_breq1 (.cv e) (.cv a) (.cv g) F
  have p0018 := @g_breq1 (.cv f) (.cv b) (.cv h) G
  have p0019_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq e a) (syn_wb (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv a) F (.cv g)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0017
  have p0019_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq f b) (syn_wb (syn_wbr (.cv f) G (.cv h)) (syn_wbr (.cv b) G (.cv h)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0019 :=
    @g_bi2anan9 (.objEq e a) (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv a) F (.cv g))
      (.objEq f b) (syn_wbr (.cv f) G (.cv h)) (syn_wbr (.cv b) G (.cv h))
      p0019_e00_recanon p0019_e01_recanon
  have p0020 :=
    @g_adantr (syn_wa (.objEq e a) (.objEq f b))
      (syn_wb (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))
        (syn_wa (syn_wbr (.cv a) F (.cv g)) (syn_wbr (.cv b) G (.cv h))))
      (.classEq (.cv z) (syn_cop (.cv g) (.cv h))) p0019
  have p0021 := @g_eqeq2 (.cv z) (syn_cop (.cv g) (.cv h)) (syn_cop (.cv c) (.cv d))
  have p0022 := @g_opth (.cv c) (.cv d) (.cv g) (.cv h)
  have p0023_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cop (.cv c) (.cv d)) (syn_cop (.cv g) (.cv h)))
        (syn_wa (.objEq c g) (.objEq d h))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0022
  have p0023 :=
    @g_syl6bb (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
      (.classEq (syn_cop (.cv c) (.cv d)) (.cv z))
      (.classEq (syn_cop (.cv c) (.cv d)) (syn_cop (.cv g) (.cv h)))
      (syn_wa (.objEq c g) (.objEq d h)) p0021 p0023_e01_recanon
  have p0024 :=
    @g_imbi2d (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
      (.classEq (syn_cop (.cv c) (.cv d)) (.cv z)) (syn_wa (.objEq c g) (.objEq d h))
      (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))) p0023
  have p0025 :=
    @g_adantl (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
      (syn_wb (.imp (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))
          (.classEq (syn_cop (.cv c) (.cv d)) (.cv z)))
        (.imp (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))
          (syn_wa (.objEq c g) (.objEq d h))))
      (syn_wa (.objEq e a) (.objEq f b)) p0024
  have p0026 :=
    @g_imbi12d
      (syn_wa (syn_wa (.objEq e a) (.objEq f b)) (.classEq (.cv z) (syn_cop (.cv g) (.cv h))))
      (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))
      (syn_wa (syn_wbr (.cv a) F (.cv g)) (syn_wbr (.cv b) G (.cv h)))
      (.imp (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))
        (.classEq (syn_cop (.cv c) (.cv d)) (.cv z)))
      (.imp (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))
        (syn_wa (.objEq c g) (.objEq d h)))
      p0020 p0025
  have p0027 :=
    @g_syl5ibrcom (syn_wa (syn_wfun F) (syn_wfun G))
      (.imp (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))
        (.imp (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))
          (.classEq (syn_cop (.cv c) (.cv d)) (.cv z))))
      (syn_wa (syn_wa (.objEq e a) (.objEq f b)) (.classEq (.cv z) (syn_cop (.cv g) (.cv h))))
      (.imp (syn_wa (syn_wbr (.cv a) F (.cv g)) (syn_wbr (.cv b) G (.cv h)))
        (.imp (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))
          (syn_wa (.objEq c g) (.objEq d h))))
      p0016 p0026
  have p0028 :=
    @g_exp3a (syn_wa (syn_wfun F) (syn_wfun G)) (syn_wa (.objEq e a) (.objEq f b))
      (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
      (.imp (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))
        (.imp (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))
          (.classEq (syn_cop (.cv c) (.cv d)) (.cv z))))
      p0027
  have p0029 :=
    @g_n_3impd (syn_wa (syn_wfun F) (syn_wfun G)) (syn_wa (.objEq e a) (.objEq f b))
      (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
      (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))
      (.imp (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))
        (.classEq (syn_cop (.cv c) (.cv d)) (.cv z)))
      p0028
  have p0030 :=
    @g_com23 (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_w3a (syn_wa (.objEq e a) (.objEq f b)) (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
        (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))
      (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))
      (.classEq (syn_cop (.cv c) (.cv d)) (.cv z)) p0029
  have p0031 := @g_eqeq1 (.cv x) (syn_cop (.cv a) (.cv b)) (syn_cop (.cv e) (.cv f))
  have p0032 := @g_eqcom (syn_cop (.cv a) (.cv b)) (syn_cop (.cv e) (.cv f))
  have p0033 := @g_opth (.cv e) (.cv f) (.cv a) (.cv b)
  have p0034_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cop (.cv e) (.cv f)) (syn_cop (.cv a) (.cv b)))
        (syn_wa (.objEq e a) (.objEq f b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0033
  have p0034 :=
    @g_bitri (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv e) (.cv f)))
      (.classEq (syn_cop (.cv e) (.cv f)) (syn_cop (.cv a) (.cv b)))
      (syn_wa (.objEq e a) (.objEq f b)) p0032 p0034_e01_recanon
  have p0035 :=
    @g_syl6bb (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
      (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
      (.classEq (syn_cop (.cv a) (.cv b)) (syn_cop (.cv e) (.cv f)))
      (syn_wa (.objEq e a) (.objEq f b)) p0031 p0034
  have p0036 :=
    @g_n_3anbi1d (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
      (.classEq (.cv x) (syn_cop (.cv e) (.cv f))) (syn_wa (.objEq e a) (.objEq f b))
      (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
      (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))) p0035
  have p0037 :=
    @g_adantr (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
      (syn_wb (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
          (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
          (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))
        (syn_w3a (syn_wa (.objEq e a) (.objEq f b)) (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
          (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))))
      (.classEq (.cv y) (syn_cop (.cv c) (.cv d))) p0036
  have p0038 := @g_eqeq1 (.cv y) (syn_cop (.cv c) (.cv d)) (.cv z)
  have p0039_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
        (syn_wb (.objEq y z) (.classEq (syn_cop (.cv c) (.cv d)) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_wb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
      p0038
  have p0039 :=
    @g_adantl (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
      (syn_wb (.objEq y z) (.classEq (syn_cop (.cv c) (.cv d)) (.cv z)))
      (.classEq (.cv x) (syn_cop (.cv a) (.cv b))) p0039_e00_recanon
  have p0040 :=
    @g_imbi12d
      (syn_wa (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv y) (syn_cop (.cv c) (.cv d))))
      (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
        (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
        (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))
      (syn_w3a (syn_wa (.objEq e a) (.objEq f b)) (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
        (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))
      (.objEq y z) (.classEq (syn_cop (.cv c) (.cv d)) (.cv z)) p0037 p0039
  have p0041 :=
    @g_imbi2d
      (syn_wa (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv y) (syn_cop (.cv c) (.cv d))))
      (.imp (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
          (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
          (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))) (.objEq y z))
      (.imp (syn_w3a (syn_wa (.objEq e a) (.objEq f b))
          (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
          (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))
        (.classEq (syn_cop (.cv c) (.cv d)) (.cv z)))
      (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))) p0040
  have p0042 :=
    @g_syl5ibrcom (syn_wa (syn_wfun F) (syn_wfun G))
      (.imp (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))) (.imp
          (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
            (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
            (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))) (.objEq y z)))
      (syn_wa (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv y) (syn_cop (.cv c) (.cv d))))
      (.imp (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))) (.imp
          (syn_w3a (syn_wa (.objEq e a) (.objEq f b))
            (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
            (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))
          (.classEq (syn_cop (.cv c) (.cv d)) (.cv z))))
      p0030 p0041
  have p0043 :=
    @g_exp3a (syn_wa (syn_wfun F) (syn_wfun G))
      (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
      (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
      (.imp (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))) (.imp
          (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
            (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
            (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))) (.objEq y z)))
      p0042
  have p0044 :=
    @g_n_3impd (syn_wa (syn_wfun F) (syn_wfun G))
      (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
      (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
      (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d)))
      (.imp (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
          (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
          (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))) (.objEq y z))
      p0043
  have p0045 :=
    @g_imp3a (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
        (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
        (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))
      (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
        (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
        (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h))))
      (.objEq y z) p0044
  have p0046 :=
    @g_exlimdvv (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_wa (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
          (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
          (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))
        (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
          (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
          (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))))
      (.objEq y z) g h dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 p0045
  have p0047 :=
    @g_exlimdvv (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_wex g (syn_wex h (syn_wa (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
              (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
              (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))
            (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
              (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
              (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))))))
      (.objEq y z) c d dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 p0046
  have p0048 :=
    @g_exlimdvv (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_wex c (syn_wex d (syn_wex g (syn_wex h (syn_wa
                (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
                  (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
                  (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))
                (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
                  (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
                  (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))))))))
      (.objEq y z) e f dv_cache_0065 dv_cache_0066 dv_cache_0067 dv_cache_0068 p0047
  have p0049 :=
    @g_exlimdvv (syn_wa (syn_wfun F) (syn_wfun G))
      (syn_wex e (syn_wex f (syn_wex c (syn_wex d (syn_wex g (syn_wex h (syn_wa
                    (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
                      (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
                      (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))
                    (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
                      (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
                      (syn_wa (syn_wbr (.cv e) F (.cv g)) (syn_wbr (.cv f) G (.cv h)))))))))))
      (.objEq y z) a b dv_cache_0069 dv_cache_0070 dv_cache_0071 dv_cache_0072 p0048
  have p0050 :=
    @g_syl5bi
      (syn_wa (syn_wbr (.cv x) (syn_cpprod F G) (.cv y))
        (syn_wbr (.cv x) (syn_cpprod F G) (.cv z)))
      (syn_wex a (syn_wex b (syn_wex e (syn_wex f (syn_wex c (syn_wex d (syn_wex g (syn_wex h
                      (syn_wa (syn_w3a (.classEq (.cv x) (syn_cop (.cv a) (.cv b)))
                          (.classEq (.cv y) (syn_cop (.cv c) (.cv d)))
                          (syn_wa (syn_wbr (.cv a) F (.cv c)) (syn_wbr (.cv b) G (.cv d))))
                        (syn_w3a (.classEq (.cv x) (syn_cop (.cv e) (.cv f)))
                          (.classEq (.cv z) (syn_cop (.cv g) (.cv h)))
                          (syn_wa (syn_wbr (.cv e) F (.cv g))
                            (syn_wbr (.cv f) G (.cv h)))))))))))))
      (syn_wa (syn_wfun F) (syn_wfun G)) (.objEq y z) p0007 p0049
  have p0051 :=
    @g_alrimiv (syn_wa (syn_wfun F) (syn_wfun G))
      (.imp (syn_wa (syn_wbr (.cv x) (syn_cpprod F G) (.cv y))
          (syn_wbr (.cv x) (syn_cpprod F G) (.cv z))) (.objEq y z))
      z dv_cache_0073 p0050
  have p0052 :=
    @g_alrimivv (syn_wa (syn_wfun F) (syn_wfun G))
      (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_cpprod F G) (.cv y))
            (syn_wbr (.cv x) (syn_cpprod F G) (.cv z))) (.objEq y z)))
      x y dv_cache_0074 dv_cache_0075 p0051
  have p0053 :=
    @g_dffun2 x y z (syn_cpprod F G) dv_cache_0076 dv_cache_0077 dv_cache_0078
      dv_cache_0079 dv_cache_0080 dv_cache_0081
  have p0054 :=
    @g_sylibr (syn_wa (syn_wfun F) (syn_wfun G))
      (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_cpprod F G) (.cv y))
                (syn_wbr (.cv x) (syn_cpprod F G) (.cv z))) (.objEq y z)))))
      (syn_wfun (syn_cpprod F G)) p0052 p0053
  have p0055 := @g_dmpprod F G
  have p0056 := @g_xpeq12 (syn_cdm F) A (syn_cdm G) B
  have p0057 :=
    @g_syl5eq (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B))
      (syn_cdm (syn_cpprod F G)) (syn_cxp (syn_cdm F) (syn_cdm G)) (syn_cxp A B) p0055
      p0056
  have p0058 :=
    @g_anim12i (syn_wa (syn_wfun F) (syn_wfun G)) (syn_wfun (syn_cpprod F G))
      (syn_wa (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B))
      (.classEq (syn_cdm (syn_cpprod F G)) (syn_cxp A B)) p0054 p0057
  have p0059 :=
    @g_an4s (syn_wfun F) (syn_wfun G) (.classEq (syn_cdm F) A) (.classEq (syn_cdm G) B)
      (syn_wa (syn_wfun (syn_cpprod F G)) (.classEq (syn_cdm (syn_cpprod F G)) (syn_cxp A B)))
      p0058
  have p0060 := (Nominal.biimpRefl (syn_wfn F A))
  have p0061 := (Nominal.biimpRefl (syn_wfn G B))
  have p0062 :=
    @g_anbi12i (syn_wfn F A) (syn_wa (syn_wfun F) (.classEq (syn_cdm F) A)) (syn_wfn G B)
      (syn_wa (syn_wfun G) (.classEq (syn_cdm G) B)) p0060 p0061
  have p0063 := (Nominal.biimpRefl (syn_wfn (syn_cpprod F G) (syn_cxp A B)))
  have p0064 :=
    @g_n_3imtr4i
      (syn_wa (syn_wa (syn_wfun F) (.classEq (syn_cdm F) A))
        (syn_wa (syn_wfun G) (.classEq (syn_cdm G) B)))
      (syn_wa (syn_wfun (syn_cpprod F G)) (.classEq (syn_cdm (syn_cpprod F G)) (syn_cxp A B)))
      (syn_wa (syn_wfn F A) (syn_wfn G B)) (syn_wfn (syn_cpprod F G) (syn_cxp A B)) p0059
      p0062 p0063
  exact p0064


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part010`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_f1opprod (A : Class) (B : Class) (C : Class) (D : Class) (F : Class)
    (G : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wf1o F A C) (syn_wf1o G B D))
        (syn_wf1o (syn_cpprod F G) (syn_cxp A B) (syn_cxp C D))) :=
  by
  have p0000 := @g_fnpprod A B F G
  have p0001 := @g_fnpprod C D (syn_ccnv F) (syn_ccnv G)
  have p0002 := @g_cnvpprod F G
  have p0003 :=
    @g_fneq1i (syn_cxp C D) (syn_ccnv (syn_cpprod F G))
      (syn_cpprod (syn_ccnv F) (syn_ccnv G)) p0002
  have p0004 :=
    @g_sylibr (syn_wa (syn_wfn (syn_ccnv F) C) (syn_wfn (syn_ccnv G) D))
      (syn_wfn (syn_cpprod (syn_ccnv F) (syn_ccnv G)) (syn_cxp C D))
      (syn_wfn (syn_ccnv (syn_cpprod F G)) (syn_cxp C D)) p0001 p0003
  have p0005 :=
    @g_anim12i (syn_wa (syn_wfn F A) (syn_wfn G B))
      (syn_wfn (syn_cpprod F G) (syn_cxp A B))
      (syn_wa (syn_wfn (syn_ccnv F) C) (syn_wfn (syn_ccnv G) D))
      (syn_wfn (syn_ccnv (syn_cpprod F G)) (syn_cxp C D)) p0000 p0004
  have p0006 :=
    @g_an4s (syn_wfn F A) (syn_wfn G B) (syn_wfn (syn_ccnv F) C) (syn_wfn (syn_ccnv G) D)
      (syn_wa (syn_wfn (syn_cpprod F G) (syn_cxp A B))
        (syn_wfn (syn_ccnv (syn_cpprod F G)) (syn_cxp C D)))
      p0005
  have p0007 := @g_dff1o4 A C F
  have p0008 := @g_dff1o4 B D G
  have p0009 :=
    @g_anbi12i (syn_wf1o F A C) (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) C))
      (syn_wf1o G B D) (syn_wa (syn_wfn G B) (syn_wfn (syn_ccnv G) D)) p0007 p0008
  have p0010 := @g_dff1o4 (syn_cxp A B) (syn_cxp C D) (syn_cpprod F G)
  have p0011 :=
    @g_n_3imtr4i
      (syn_wa (syn_wa (syn_wfn F A) (syn_wfn (syn_ccnv F) C))
        (syn_wa (syn_wfn G B) (syn_wfn (syn_ccnv G) D)))
      (syn_wa (syn_wfn (syn_cpprod F G) (syn_cxp A B))
        (syn_wfn (syn_ccnv (syn_cpprod F G)) (syn_cxp C D)))
      (syn_wa (syn_wf1o F A C) (syn_wf1o G B D))
      (syn_wf1o (syn_cpprod F G) (syn_cxp A B) (syn_cxp C D)) p0006 p0009 p0010
  exact p0011

@[expose]
noncomputable def g_ovcross (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (.classEq (syn_co A (syn_ccross) B) (syn_cxp A B))) :=
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
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0005 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cxp A (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cxp A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((syn_cxp A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 := @g_elex A V
  have p0001 := @g_elex B W
  have p0002 := @g_xpexg A B (syn_cvv) (syn_cvv)
  have p0003 := @g_xpeq1 (.cv x) A (.cv y)
  have p0004 := @g_xpeq2 (.cv y) B A
  have p0005 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cross x y
      dv_cache_0001
  have p0006 :=
    @g_ovmpt2g x y A B (syn_cvv) (syn_cvv) (syn_cxp (.cv x) (.cv y)) (syn_cxp A B)
      (syn_ccross) (syn_cxp A (.cv y)) (syn_cvv) dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0001 p0003 p0004 p0005
  have p0007 :=
    @g_mpd3an3 (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classMem (syn_cxp A B) (syn_cvv))
      (.classEq (syn_co A (syn_ccross) B) (syn_cxp A B)) p0002 p0006
  have p0008 :=
    @g_syl2an (.classMem A V) (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (.classEq (syn_co A (syn_ccross) B) (syn_cxp A B)) (.classMem B W) p0000 p0001 p0007
  exact p0008

@[expose]
noncomputable def g_fncross : Nominal.NPrf (syn_wfn (syn_ccross) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cross x y
      dv_cache_0001
  have p0001 := @g_vex x
  have p0002 := @g_vex y
  have p0003 := @g_xpex (.cv x) (.cv y) p0001 p0002
  have p0004 :=
    @g_fnmpt2i x y (syn_cvv) (syn_cvv) (syn_cxp (.cv x) (.cv y)) (syn_ccross)
      dv_cache_0002 dv_cache_0003 dv_cache_0002 dv_cache_0003 dv_cache_0001 p0000 p0003
  have p0005 := @g_xpvv
  have p0006 := @g_fneq2i (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv) (syn_ccross) p0005
  have p0007 :=
    @g_mpbi (syn_wfn (syn_ccross) (syn_cxp (syn_cvv) (syn_cvv)))
      (syn_wfn (syn_ccross) (syn_cvv)) p0004 p0006
  exact p0007

@[expose]
noncomputable def g_brcrossg (A : Class) (B : Class) (C : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (.classMem B W))
        (syn_wb (syn_wbr (syn_cop A B) (syn_ccross) C) (.classEq C (syn_cxp A B)))) :=
  by
  have p0000 := @g_eqcom C (syn_co A (syn_ccross) B)
  have p0001 := (Nominal.classEqRefl (syn_co A (syn_ccross) B))
  have p0002 :=
    @g_eqeq1i (syn_co A (syn_ccross) B) (syn_cfv (syn_ccross) (syn_cop A B)) C p0001
  have p0003 :=
    @g_bitri (.classEq C (syn_co A (syn_ccross) B)) (.classEq (syn_co A (syn_ccross) B) C)
      (.classEq (syn_cfv (syn_ccross) (syn_cop A B)) C) p0000 p0002
  have p0004 := @g_fncross
  have p0005 := @g_opexg A B V W
  have p0006 := @g_fnbrfvb (syn_cvv) (syn_cop A B) C (syn_ccross)
  have p0007 :=
    @g_sylancr (syn_wa (.classMem A V) (.classMem B W)) (syn_wfn (syn_ccross) (syn_cvv))
      (.classMem (syn_cop A B) (syn_cvv))
      (syn_wb (.classEq (syn_cfv (syn_ccross) (syn_cop A B)) C)
        (syn_wbr (syn_cop A B) (syn_ccross) C))
      p0004 p0005 p0006
  have p0008 :=
    @g_syl5bb (.classEq C (syn_co A (syn_ccross) B))
      (.classEq (syn_cfv (syn_ccross) (syn_cop A B)) C)
      (syn_wa (.classMem A V) (.classMem B W)) (syn_wbr (syn_cop A B) (syn_ccross) C)
      p0003 p0007
  have p0009 := @g_ovcross A B V W
  have p0010 :=
    @g_eqeq2d (syn_wa (.classMem A V) (.classMem B W)) (syn_co A (syn_ccross) B)
      (syn_cxp A B) C p0009
  have p0011 :=
    @g_bitr3d (syn_wa (.classMem A V) (.classMem B W))
      (.classEq C (syn_co A (syn_ccross) B)) (syn_wbr (syn_cop A B) (syn_ccross) C)
      (.classEq C (syn_cxp A B)) p0008 p0010
  exact p0011

@[expose]
noncomputable def g_brcross (A : Class) (B : Class) (C : Class)
    (hyp_brcross_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_brcross_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop A B) (syn_ccross) C) (.classEq C (syn_cxp A B))) :=
  by
  have p0000 := @g_brcrossg A B C (syn_cvv) (syn_cvv)
  have p0001 :=
    @g_mp2an (.classMem A (syn_cvv)) (.classMem B (syn_cvv))
      (syn_wb (syn_wbr (syn_cop A B) (syn_ccross) C) (.classEq C (syn_cxp A B)))
      hyp_brcross_1 hyp_brcross_2 p0000
  exact p0001

@[expose]
noncomputable def g_crossex : Nominal.NPrf (.classMem (syn_ccross) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let b : Var := freshVar proofSupport 4
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
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
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_b : z ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_b_ne_z : b ≠ z := Ne.symm fresh_z_ne_b
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have dv_cache_0001 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0002 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_y, not_false_eq_true])
  have dv_cache_0004 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0005 : a ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_z, not_false_eq_true])
  have dv_cache_0006 : b ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_z, not_false_eq_true])
  have dv_cache_0007 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0009 :
    a ∉ ((syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_z, fresh_a_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    a ∉
      ((syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
              (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : b ∉ ((syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_x, fresh_b_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    b ∉
      ((syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                    (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                      (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0014 : y ∉ ((syn_cvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0015 :
    x ∉
      ((syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                      (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                        (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))
          (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 :
    y ∉
      ((syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                      (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                        (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))
          (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 :
    z ∉
      ((syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                      (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                        (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))
          (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : z ∉ ((syn_cxp (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0019 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0020 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_cross x y
      dv_cache_0001
  have p0001 :=
    @g_rexcom (.classEq (.cv z) (syn_cop (.cv a) (.cv b))) a b (.cv x) (.cv y)
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0002 :=
    @g_elxp2 a b (.cv z) (.cv x) (.cv y) dv_cache_0005 dv_cache_0006 dv_cache_0007
      dv_cache_0002 dv_cache_0003 dv_cache_0008 dv_cache_0004
  have p0003 :=
    @g_elin
      (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
      (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                  (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))
  have p0004 := @g_snex (.cv z)
  have p0005 :=
    @g_otelins2 (syn_csn (.cv b)) (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))
      (syn_cins2 (syn_csset)) p0004
  have p0006 := @g_vex x
  have p0007 := @g_otelins2 (syn_csn (.cv b)) (.cv x) (.cv y) (syn_csset) p0006
  have p0008 := @g_vex b
  have p0009 := @g_vex y
  have p0010 := @g_opelssetsn (.cv b) (.cv y) p0008 p0009
  have p0011_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv b)) (.cv y)) (syn_csset)) (.objMem b y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
      p0010
  have p0011 :=
    @g_n_3bitri
      (.classMem
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (.cv x) (.cv y))) (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv b)) (.cv y)) (syn_csset)) (.objMem b y) p0005
      p0007 p0011_e02_recanon
  have p0012 :=
    @g_oqelins4 (syn_csn (.cv b)) (syn_csn (.cv z)) (.cv x) (.cv y)
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
              (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))
      p0009
  have p0013 :=
    @g_elin
      (syn_cop (syn_csn (.cv a))
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
      (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
            (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))
  have p0014 := @g_snex (.cv b)
  have p0015 :=
    @g_otelins2 (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))
      (syn_cins2 (syn_csset)) p0014
  have p0016 := @g_otelins2 (syn_csn (.cv a)) (syn_csn (.cv z)) (.cv x) (syn_csset) p0004
  have p0017 := @g_vex a
  have p0018 := @g_opelssetsn (.cv a) (.cv x) p0017 p0006
  have p0019_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv a)) (.cv x)) (syn_csset)) (.objMem a x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
      p0018
  have p0019 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv a))
          (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv z)) (.cv x)))
        (syn_cins2 (syn_csset)))
      (.classMem (syn_cop (syn_csn (.cv a)) (.cv x)) (syn_csset)) (.objMem a x) p0015
      p0016 p0019_e02_recanon
  have p0020 :=
    @g_oqelins4 (syn_csn (.cv a)) (syn_csn (.cv b)) (syn_csn (.cv z)) (.cv x)
      (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
          (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))
      p0006
  have p0021 := @g_vex z
  have p0022 :=
    @g_otsnelsi3 (.cv a) (.cv b) (.cv z)
      (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))
      p0017 p0008 p0021
  have p0023 :=
    @g_elin (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins2 (syn_ccnv (syn_c1st)))
      (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))
  have p0024 := @g_otelins2 (.cv a) (.cv b) (.cv z) (syn_ccnv (syn_c1st)) p0008
  have p0025 := (Nominal.biimpRefl (syn_wbr (.cv a) (syn_ccnv (syn_c1st)) (.cv z)))
  have p0026 := @g_brcnv (.cv a) (.cv z) (syn_c1st)
  have p0027 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins2 (syn_ccnv (syn_c1st))))
      (.classMem (syn_cop (.cv a) (.cv z)) (syn_ccnv (syn_c1st)))
      (syn_wbr (.cv a) (syn_ccnv (syn_c1st)) (.cv z)) (syn_wbr (.cv z) (syn_c1st) (.cv a))
      p0024 p0025 p0026
  have p0028 :=
    @g_opelxp (.cv a) (syn_cop (.cv b) (.cv z)) (syn_cvv) (syn_ccnv (syn_c2nd))
  have p0029 :=
    @g_mpbiran
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))
        (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))
      (.classMem (.cv a) (syn_cvv))
      (.classMem (syn_cop (.cv b) (.cv z)) (syn_ccnv (syn_c2nd))) p0017 p0028
  have p0030 := (Nominal.biimpRefl (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (.cv z)))
  have p0031 := @g_brcnv (.cv b) (.cv z) (syn_c2nd)
  have p0032 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))
        (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))
      (.classMem (syn_cop (.cv b) (.cv z)) (syn_ccnv (syn_c2nd)))
      (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (.cv z)) (syn_wbr (.cv z) (syn_c2nd) (.cv b))
      p0029 p0030 p0031
  have p0033 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z))) (syn_cins2 (syn_ccnv (syn_c1st))))
      (syn_wbr (.cv z) (syn_c1st) (.cv a))
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))
        (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))
      (syn_wbr (.cv z) (syn_c2nd) (.cv b)) p0027 p0032
  have p0034 := @g_op1st2nd (.cv a) (.cv b) (.cv z) p0017 p0008
  have p0035 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))
        (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))
      (syn_wa (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))
          (syn_cins2 (syn_ccnv (syn_c1st))))
        (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))
          (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))
      (syn_wa (syn_wbr (.cv z) (syn_c1st) (.cv a)) (syn_wbr (.cv z) (syn_c2nd) (.cv b)))
      (.classEq (.cv z) (syn_cop (.cv a) (.cv b))) p0023 p0033 p0034
  have p0036 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv a))
          (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins4 (syn_csi3
            (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
              (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))))
      (.classMem (syn_cop (syn_csn (.cv a)) (syn_cop (syn_csn (.cv b)) (syn_csn (.cv z))))
        (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
            (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))
      (.classMem (syn_cop (.cv a) (syn_cop (.cv b) (.cv z)))
        (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))
      (.classEq (.cv z) (syn_cop (.cv a) (.cv b))) p0020 p0022 p0035
  have p0037 :=
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv a))
          (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem a x)
      (.classMem (syn_cop (syn_csn (.cv a))
          (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins4 (syn_csi3
            (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
              (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))))
      (.classEq (.cv z) (syn_cop (.cv a) (.cv b))) p0019 p0036
  have p0038 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv a))
          (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
              (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv a))
            (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
          (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv a))
            (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))) (syn_cins4
            (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))))
      (syn_wa (.objMem a x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))) p0013 p0037
  have p0039 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv a))
          (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
              (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))))
      (syn_wa (.objMem a x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))) a p0038
  have p0040 :=
    @g_elima1c a (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x)))
      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
            (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
              (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))))
      dv_cache_0009 dv_cache_0010
  have p0041 :=
    (Nominal.biimpRefl (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))))
  have p0042_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))) (syn_wex a
          (syn_wa (.objMem a x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_cop, syn_cun, syn_cnin,
          syn_wnan, syn_ccompl]
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
      p0041
  have p0042 :=
    @g_n_3bitr4i
      (syn_wex a (.classMem (syn_cop (syn_csn (.cv a))
            (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))))
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                  (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))))))
      (syn_wex a (syn_wa (.objMem a x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))))
      (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                  (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))
      (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))) p0039 p0040
      p0042_e02_recanon
  have p0043 :=
    @g_bitri
      (.classMem
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                  (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                    (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))
      (.classMem (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (.cv x))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                  (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))
      (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))) p0012 p0042
  have p0044 :=
    @g_anbi12i
      (.classMem
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cins2 (syn_cins2 (syn_csset))))
      (.objMem b y)
      (.classMem
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                  (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                    (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))
      (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))) p0011 p0043
  have p0045 :=
    @g_bitri
      (.classMem
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                    (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                      (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv b))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
          (syn_cins2 (syn_cins2 (syn_csset)))) (.classMem (syn_cop (syn_csn (.cv b))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))) (syn_cins4 (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                    (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                      (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))))
      (syn_wa (.objMem b y) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))))
      p0003 p0044
  have p0046 :=
    @g_exbii
      (.classMem
        (syn_cop (syn_csn (.cv b)) (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
        (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                    (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                      (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))))
      (syn_wa (.objMem b y) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))))
      b p0045
  have p0047 :=
    @g_elima1c b (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y)))
      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                  (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                    (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))
      dv_cache_0011 dv_cache_0012
  have p0048 :=
    (Nominal.biimpRefl (syn_wrex b (.cv y)
        (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))))
  have p0049_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex b (.cv y)
          (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))) (syn_wex b
          (syn_wa (.objMem b y)
            (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))))) :=
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
      p0048
  have p0049 :=
    @g_n_3bitr4i
      (syn_wex b (.classMem (syn_cop (syn_csn (.cv b))
            (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))))
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                      (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                        (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))))
      (syn_wex b (syn_wa (.objMem b y)
          (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b))))))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                      (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                        (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c)))
      (syn_wrex b (.cv y) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))))
      p0046 p0047 p0049_e02_recanon
  have p0050 :=
    @g_n_3bitr4ri
      (syn_wrex a (.cv x) (syn_wrex b (.cv y) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))))
      (syn_wrex b (.cv y) (syn_wrex a (.cv x) (.classEq (.cv z) (syn_cop (.cv a) (.cv b)))))
      (.classMem (.cv z) (syn_cxp (.cv x) (.cv y)))
      (.classMem (syn_cop (syn_csn (.cv z)) (syn_cop (.cv x) (.cv y))) (syn_cima
          (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                      (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                        (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c)))
      p0001 p0002 p0049
  have p0051 :=
    @g_releqmpt2 x y z (syn_cvv) (syn_cvv)
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                    (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                      (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c))
      (syn_cxp (.cv x) (.cv y)) dv_cache_0013 dv_cache_0014 dv_cache_0013 dv_cache_0014
      dv_cache_0015 dv_cache_0016 dv_cache_0017 dv_cache_0018 dv_cache_0001 dv_cache_0019
      dv_cache_0020 p0050
  have p0052 :=
    @g_eqtr4i (syn_ccross) (syn_cmpt2 x (syn_cvv) y (syn_cvv) (syn_cxp (.cv x) (.cv y)))
      (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima
          (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                            (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                              (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))
                (syn_c1c)))) (syn_c1c)))
      p0000 p0051
  have p0053 := @g_vvex
  have p0055 := @g_ssetex
  have p0056 := @g_ins2ex (syn_csset) p0055
  have p0057 := @g_ins2ex (syn_cins2 (syn_csset)) p0056
  have p0058 := @g_n_1stex
  have p0059 := @g_cnvex (syn_c1st) p0058
  have p0060 := @g_ins2ex (syn_ccnv (syn_c1st)) p0059
  have p0062 := @g_n_2ndex
  have p0063 := @g_cnvex (syn_c2nd) p0062
  have p0064 := @g_xpex (syn_cvv) (syn_ccnv (syn_c2nd)) p0053 p0063
  have p0065 :=
    @g_inex (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))
      p0060 p0064
  have p0066 :=
    @g_si3ex
      (syn_cin (syn_cins2 (syn_ccnv (syn_c1st))) (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))
      p0065
  have p0067 :=
    @g_ins4ex
      (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
          (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))
      p0066
  have p0068 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cins4 (syn_csi3 (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
            (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))
      p0057 p0067
  have p0069 := @g_n_1cex
  have p0070 :=
    @g_imaex
      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
            (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
              (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd)))))))
      (syn_c1c) p0068 p0069
  have p0071 :=
    @g_ins4ex
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
              (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))
      p0070
  have p0072 :=
    @g_inex (syn_cins2 (syn_cins2 (syn_csset)))
      (syn_cins4 (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                  (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))
      p0057 p0071
  have p0074 :=
    @g_imaex
      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
            (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                  (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                    (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))
      (syn_c1c) p0072 p0069
  have p0075 :=
    @g_mpt2exlem (syn_cvv) (syn_cvv)
      (syn_cima (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
              (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                    (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                      (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c)))) (syn_c1c))
      p0053 p0053 p0074
  have p0076 :=
    @g_eqeltri (syn_ccross)
      (syn_cdif (syn_cxp (syn_cxp (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_cima
          (syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_cima
                (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_cima
                      (syn_cin (syn_cins2 (syn_cins2 (syn_csset))) (syn_cins4 (syn_csi3
                            (syn_cin (syn_cins2 (syn_ccnv (syn_c1st)))
                              (syn_cxp (syn_cvv) (syn_ccnv (syn_c2nd))))))) (syn_c1c))))
                (syn_c1c)))) (syn_c1c)))
      (syn_cvv) p0052 p0075
  exact p0076

@[expose]
noncomputable def g_pw1fnval (A : Class)
    (hyp_pw1fnval_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_cfv (syn_cpw1fn) (syn_csn A)) (syn_cpw1 A)) :=
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
  have dv_cache_0001 : x ∉ ((syn_csn A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cpw1 A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_c1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_snel1c A hyp_pw1fnval_1
  have p0001 := @g_unieq (.cv x) (syn_csn A)
  have p0002 := @g_unisn A hyp_pw1fnval_1
  have p0003 :=
    @g_syl6eq (.classEq (.cv x) (syn_csn A)) (syn_cuni (.cv x)) (syn_cuni (syn_csn A)) A
      p0001 p0002
  have p0004 := @g_pw1eq (syn_cuni (.cv x)) A
  have p0005 :=
    @g_syl (.classEq (.cv x) (syn_csn A)) (.classEq (syn_cuni (.cv x)) A)
      (.classEq (syn_cpw1 (syn_cuni (.cv x))) (syn_cpw1 A)) p0003 p0004
  have p0006 := NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw1fn x
  have p0007 := @g_pw1ex A hyp_pw1fnval_1
  have p0008 :=
    @g_fvmpt x (syn_csn A) (syn_cpw1 (syn_cuni (.cv x))) (syn_cpw1 A) (syn_c1c)
      (syn_cpw1fn) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0005 p0006 p0007
  have p0009 := Nominal.mp p0000 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end
